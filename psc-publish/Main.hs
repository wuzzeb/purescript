{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import Prelude hiding (userError)

import Data.Maybe
import Data.Char (isSpace)
import Data.String (fromString)
import Data.List (stripPrefix, isSuffixOf, (\\), nubBy)
import Data.List.Split (splitOn)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Version
import Data.Function (on)
import Safe (headMay)

import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.Text as T

import qualified Data.Aeson as A
import Data.Aeson.BetterErrors

import Control.Applicative
import Control.Category ((>>>))
import Control.Arrow ((***))
import Control.Exception (catch, try)
import Control.Monad.Trans.Except
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.Writer

import System.Directory (doesFileExist)
import System.Process (readProcess)
import System.Exit (exitFailure)
import qualified System.FilePath.Glob as Glob

import Web.Bower.PackageMeta (PackageMeta(..), BowerError(..), PackageName,
                              runPackageName, parsePackageName, Repository(..))
import qualified Web.Bower.PackageMeta as Bower

import qualified Language.PureScript as P (version)
import qualified Language.PureScript.Docs as D
import Utils
import ErrorsWarnings

main :: IO ()
main = do
  pkg <- preparePackage
  BL.putStrLn (A.encode pkg)

-- | Attempt to retrieve package metadata from the current directory.
-- Calls exitFailure if no package metadata could be retrieved.
preparePackage :: IO D.UploadedPackage
preparePackage =
  runPrepareM preparePackage'
    >>= either (\e -> printError e >> exitFailure)
               handleWarnings
  where
  handleWarnings (result, warns) = do
    printWarnings warns
    return result

newtype PrepareM a =
  PrepareM { unPrepareM :: WriterT [PackageWarning] (ExceptT PackageError IO) a }
  deriving (Functor, Applicative, Monad,
            MonadWriter [PackageWarning],
            MonadError PackageError)

-- This MonadIO instance ensures that IO errors don't crash the program.
instance MonadIO PrepareM where
  liftIO act =
    lift' (try act) >>= either (otherError . IOExceptionThrown) return
    where
    lift' :: IO a -> PrepareM a
    lift' = PrepareM . lift . lift

runPrepareM :: PrepareM a -> IO (Either PackageError (a, [PackageWarning]))
runPrepareM = runExceptT . runWriterT . unPrepareM

warn :: PackageWarning -> PrepareM ()
warn w = tell [w]

userError :: UserError -> PrepareM a
userError = throwError . UserError

internalError :: InternalError -> PrepareM a
internalError = throwError . InternalError

otherError :: OtherError -> PrepareM a
otherError = throwError . OtherError

catchLeft :: Applicative f => Either a b -> (a -> f b) -> f b
catchLeft a f = either f pure a

preparePackage' :: PrepareM D.UploadedPackage
preparePackage' = do
  exists <- liftIO (doesFileExist "bower.json")
  unless exists (userError BowerJSONNotFound)

  pkgMeta <- liftIO (Bower.decodeFile "bower.json")
                    >>= flip catchLeft (userError . CouldntParseBowerJSON)
  (pkgVersionTag, pkgVersion) <- getVersionFromGitTag
  pkgGithub                   <- getBowerInfo pkgMeta
  (pkgBookmarks, pkgModules)  <- getModulesAndBookmarks

  let declaredDeps = map fst (bowerDependencies pkgMeta ++
                              bowerDevDependencies pkgMeta)
  pkgResolvedDependencies     <- getResolvedDependencies declaredDeps

  let pkgUploader = D.NotYetKnown
  let pkgCompilerVersion = P.version

  return D.Package{..}

getModulesAndBookmarks :: PrepareM ([D.Bookmark], [D.Module])
getModulesAndBookmarks = do
  (inputFiles, depsFiles) <- liftIO getInputAndDepsFiles
  liftIO (D.parseAndDesugar inputFiles depsFiles renderModules)
    >>= either (userError . ParseAndDesugarError) return
  where
  renderModules bookmarks modules =
    return (bookmarks, map D.convertModule modules)

getVersionFromGitTag :: PrepareM (String, Version)
getVersionFromGitTag = do
  out <- readProcess' "git" ["tag", "--list", "--points-at", "HEAD"] ""
  let vs = map trimWhitespace (lines out)
  case mapMaybe parseMay vs of
    []  -> userError TagMustBeCheckedOut
    [x] -> return x
    xs  -> userError (AmbiguousVersions (map snd xs))
  where
  trimWhitespace =
    dropWhile isSpace >>> reverse >>> dropWhile isSpace >>> reverse
  parseMay str =
    (str,) <$> D.parseVersion' (dropPrefix "v" str)
  dropPrefix prefix str =
    fromMaybe str (stripPrefix prefix str)

getBowerInfo :: PackageMeta -> PrepareM (D.GithubUser, D.GithubRepo)
getBowerInfo = either (userError . BadRepositoryField) return . tryExtract
  where
  tryExtract pkgMeta =
    case bowerRepository pkgMeta of
      Nothing -> Left RepositoryFieldMissing
      Just Repository{..} -> do
        unless (repositoryType == "git")
          (Left (BadRepositoryType repositoryType))
        maybe (Left NotOnGithub) Right (extractGithub repositoryUrl)

extractGithub :: String -> Maybe (D.GithubUser, D.GithubRepo)
extractGithub =
  stripPrefix "git://github.com/"
   >>> fmap (splitOn "/")
   >=> takeTwo
   >>> fmap (D.GithubUser *** (D.GithubRepo . dropDotGit))

  where
  takeTwo :: [a] -> Maybe (a, a)
  takeTwo [x, y] = Just (x, y)
  takeTwo _ = Nothing

  dropDotGit :: String -> String
  dropDotGit str
    | ".git" `isSuffixOf` str = take (length str - 4) str
    | otherwise = str

readProcess' :: String -> [String] -> String -> PrepareM String
readProcess' prog args stdin = do
  out <- liftIO (catch (Right <$> readProcess prog args stdin)
                       (return . Left))
  either (otherError . ProcessFailed prog args) return out

data DependencyStatus
  = Missing
    -- ^ Listed in bower.json, but not installed.
  | NoResolution
    -- ^ In the output of `bower list --json --offline`, there was no
    -- _resolution key. This can be caused by adding the dependency using
    -- `bower link`, or simply copying it into bower_components instead of
    -- installing it normally.
  | ResolvedOther String
    -- ^ Resolved, but to something other than a version. The String argument
    -- is the resolution type. The values it can take that I'm aware of are
    -- "commit" and "branch".
  | ResolvedVersion String
    -- ^ Resolved to a version. The String argument is the resolution tag (eg,
    -- "v0.1.0").
  deriving (Show, Eq)

-- Go through all bower dependencies which contain purescript code, and
-- extract their versions.
--
-- In the case where a bower dependency is taken from a particular version,
-- that's easy; take that version. In any other case (eg, a branch, or a commit
-- sha) we print a warning that documentation links will not work, and avoid
-- linking to documentation for any types from that package.
--
-- The rationale for this is: people will prefer to use a released version
-- where possible. If they are not using a released version, then this is
-- probably for a reason. However, docs are only ever available for released
-- versions. Therefore there will probably be no version of the docs which is
-- appropriate to link to, and we should omit links.
getResolvedDependencies :: [PackageName] -> PrepareM [(PackageName, Version)]
getResolvedDependencies declaredDeps = do
  depsBS <- fromString <$> readProcess' "bower" ["list", "--json", "--offline"] ""

  -- Check for undeclared dependencies
  toplevels <- catchJSON (parse asToplevelDependencies depsBS)
  warnUndeclared declaredDeps toplevels

  deps <- catchJSON (parse asResolvedDependencies depsBS)
  handleDeps deps

  where
  catchJSON = flip catchLeft (internalError . JSONError FromBowerList)

-- | Extracts all dependencies and their versions from
--   `bower list --json --offline`
asResolvedDependencies :: Parse BowerError [(PackageName, DependencyStatus)]
asResolvedDependencies = nubBy ((==) `on` fst) <$> go
  where
  go =
    fmap (fromMaybe []) $
      keyMay "dependencies" $
        (++) <$> eachInObjectWithKey (parsePackageName . T.unpack)
                                     asDependencyStatus
             <*> (concatMap snd <$> eachInObject asResolvedDependencies)

-- | Extracts only the top level dependency names from the output of
--   `bower list --json --offline`
asToplevelDependencies :: Parse BowerError [PackageName]
asToplevelDependencies =
  fmap (map fst) $
    key "dependencies" $
      eachInObjectWithKey (parsePackageName . T.unpack) (return ())

asDependencyStatus :: Parse e DependencyStatus
asDependencyStatus = do
  isMissing <- keyOrDefault "missing" False asBool
  if isMissing
    then
      return Missing
    else
      key "pkgMeta" $
        keyOrDefault "_resolution" NoResolution $ do
          type_ <- key "type" asString
          case type_ of
            "version" -> ResolvedVersion <$> key "tag" asString
            other -> return (ResolvedOther other)

warnUndeclared :: [PackageName] -> [PackageName] -> PrepareM ()
warnUndeclared declared actual =
  mapM_ (warn . UndeclaredDependency) (actual \\ declared)

handleDeps ::
  [(PackageName, DependencyStatus)] -> PrepareM [(PackageName, Version)]
handleDeps deps = do
  let (missing, noVersion, installed) = partitionDeps deps
  case missing of
    (x:xs) ->
      userError (MissingDependencies (x :| xs))
    [] -> do
      mapM_ (warn . NoResolvedVersion) noVersion
      withVersions <- catMaybes <$> mapM tryExtractVersion' installed
      filterM (liftIO . isPureScript . bowerDir . fst) withVersions

  where
  partitionDeps = foldr go ([], [], [])
  go (pkgName, d) (ms, os, is) =
    case d of
      Missing           -> (pkgName : ms, os, is)
      NoResolution      -> (ms, pkgName : os, is)
      ResolvedOther _   -> (ms, pkgName : os, is)
      ResolvedVersion v -> (ms, os, (pkgName, v) : is)

  bowerDir pkgName = "bower_components/" ++ runPackageName pkgName

  -- Try to extract a version, and warn if unsuccessful.
  tryExtractVersion' pair =
    maybe (warn (UnacceptableVersion pair) >> return Nothing)
          (return . Just)
          (tryExtractVersion pair)

tryExtractVersion :: (PackageName, String) -> Maybe (PackageName, Version)
tryExtractVersion (pkgName, tag) =
  let tag' = fromMaybe tag (stripPrefix "v" tag)
  in  (pkgName,) <$> D.parseVersion' tag'

-- | Returns whether it looks like there is a purescript package checked out
-- in the given directory.
isPureScript :: FilePath -> IO Bool
isPureScript dir = do
  files <- Glob.globDir1 purescriptSourceFiles dir
  return (not (null files))

getInputAndDepsFiles :: IO ([FilePath], [(PackageName, FilePath)])
getInputAndDepsFiles = do
  inputFiles <- globRelative purescriptSourceFiles
  depsFiles' <- globRelative purescriptDepsFiles
  return (inputFiles, mapMaybe withPackageName depsFiles')

withPackageName :: FilePath -> Maybe (PackageName, FilePath)
withPackageName fp = (,fp) <$> getPackageName fp

getPackageName :: FilePath -> Maybe PackageName
getPackageName fp = do
  let xs = splitOn "/" fp
  ys <- stripPrefix ["bower_components"] xs
  y <- headMay ys
  case Bower.mkPackageName y of
    Right name -> Just name
    Left _ -> Nothing
