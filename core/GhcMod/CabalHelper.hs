-- ghc-mod: Happy Haskell Hacking
-- Copyright (C) 2015  Daniel Gröber <dxld ÄT darkboxed DOT org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU Affero General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU Affero General Public License for more details.
--
-- You should have received a copy of the GNU Affero General Public License
-- along with this program.  If not, see <http://www.gnu.org/licenses/>.

{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module GhcMod.CabalHelper
  (
    getComponents
  , getGhcMergedPkgOptions
  , getCabalPackageDbStack
  , withAutogen
  , withProjSetup
  ) where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Category ((.))
import Data.Dynamic (toDyn, fromDynamic, Dynamic)
import Data.List.NonEmpty ( NonEmpty(..), toList)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Typeable (Typeable)
import Data.Version
import Data.Binary (Binary)
import Data.Traversable
import Distribution.Helper hiding (Programs(..))
import qualified Distribution.Helper as CH
import GhcMod.Cradle
import qualified GhcMod.Types as T
import GhcMod.Caching
import GhcMod.Types
import GhcMod.Monad.Types
import GhcMod.Utils
import GhcMod.PathsAndFiles
import GhcMod.Logging
import GhcMod.Output
import GhcMod.CustomPackageDb
import GhcMod.Stack
import GhcMod.Error
import System.FilePath
import System.Process
import System.Exit
import GhcProject.Types
import Prelude hiding ((.))

import Paths_ghc_mod_core as GhcMod

-- | Only package related GHC options, sufficient for things that don't need to
-- access home modules
getGhcMergedPkgOptions :: (Applicative m, IOish m, Gm m)
  => m [GHCOption]
getGhcMergedPkgOptions = undefined
-- getGhcMergedPkgOptions = chCached $ \distdir -> Cached {
--   cacheLens = Just (lGmcMergedPkgOptions . lGmCaches),
--   cacheFile = mergedPkgOptsCacheFile distdir,
--   cachedAction = \_tcf (_progs, _projdir, _ver) _ma -> do
--     opts <- runCHQuery ghcMergedPkgOptions
--     return ([setupConfigPath distdir], opts)
--  }

getCabalPackageDbStack :: (IOish m, Gm m) => m [GhcPkgDb]
getCabalPackageDbStack = undefined
-- getCabalPackageDbStack = chCached $ \distdir -> Cached {
--   cacheLens = Just (lGmcPackageDbStack . lGmCaches),
--   cacheFile = pkgDbStackCacheFile distdir,
--   cachedAction = \_tcf (_progs, _projdir, _ver) _ma -> do
--     crdl <- cradle
--     dbs <- map chPkgToGhcPkg <$>
--              runCHQuery packageDbStack
--     return ([setupConfigFile crdl, sandboxConfigFile crdl], dbs)
--  }

chPkgToGhcPkg :: ChPkgDb -> GhcPkgDb
chPkgToGhcPkg ChPkgGlobal = GlobalDb
chPkgToGhcPkg ChPkgUser = UserDb
chPkgToGhcPkg (ChPkgSpecific f) = PackageDb f

-- | Primary interface to cabal-helper and intended single entrypoint to
-- constructing 'GmComponent's
--
-- The Component\'s 'gmcHomeModuleGraph' will be empty and has to be resolved by
-- 'resolveGmComponents'.
getComponents :: (Applicative m, IOish m, Gm m, Typeable pt)
              => ProjSetup pt -> m [GmComponent 'GMCRaw ChEntrypoint]
getComponents ps = do
  let
    doComp :: (ChComponentName, ChComponentInfo) -> GmComponent 'GMCRaw ChEntrypoint
    doComp (cn,ci) =
      GmComponent
       { gmcHomeModuleGraph = mempty
       , gmcGhcOpts         = ciGhcOptions     ci
       , gmcGhcPkgOpts      = ciGhcPkgOptions  ci
       , gmcGhcSrcOpts      = ciGhcSrcOptions  ci
       , gmcGhcLangOpts     = ciGhcLangOptions ci
       , gmcRawEntrypoints  = ciEntrypoints    ci
       , gmcEntrypoints     = ciEntrypoints    ci
       , gmcSourceDirs      = ciSourceDirs     ci
       , gmcName            = ciComponentName  ci
       , gmcNeedsBuildOutput = ciNeedsBuildOutput ci
       }
    foo :: UnitInfo -> [GmComponent 'GMCRaw ChEntrypoint]
    foo ui = map doComp $ Map.toList $ uiComponents ui

  ff <- runCHQuery ps $ allUnits foo
  let cs = concat $ toList ff
  return cs

-- getComponents = chCached $ \distdir -> Cached {
--     cacheLens = Just (lGmcComponents . lGmCaches),
--     cacheFile = cabalHelperCacheFile distdir,
--     cachedAction = \ _tcf (_progs, _projdir, _ver) _ma -> do
--       cs <- runCHQuery $ components $
--              GmComponent mempty
--                CH.<$> ghcOptions
--                CH.<.> ghcPkgOptions
--                CH.<.> ghcSrcOptions
--                CH.<.> ghcLangOptions
--                CH.<.> entrypoints
--                CH.<.> entrypoints
--                CH.<.> sourceDirs
--       return ([setupConfigPath distdir], cs)
--   }

-- getQueryEnv :: forall m pt. (IOish m, GmOut m, GmEnv m) => m (Maybe ( QueryEnv pt))
getQueryEnv :: (IOish m, GmOut m, GmEnv m) => m (QueryEnv pt)
getQueryEnv = undefined
  {-
getQueryEnv = do
  crdl <- cradle
  progs <- patchStackPrograms crdl =<< (optPrograms <$> options)
  readProc <- gmReadProcess
  case cradleCabalFile crdl of
    Nothing -> return Nothing
    Just cabalFile -> do
      let
        distdirCradle = cradleDistDir crdl
        (projdir,distdir) = case cradleProject crdl of
          CabalProject     -> (ProjLocCabalFile cabalFile,DistDirV1 distdirCradle)
          CabalNewProject  -> (ProjLocCabalFile cabalFile,DistDirV2 distdirCradle)
          SandboxProject   -> (ProjLocCabalFile cabalFile,DistDirV1 distdirCradle)
          PlainProject     -> (ProjLocCabalFile cabalFile,DistDirV1 distdirCradle)
          StackProject env -> (ProjLocCabalFile cabalFile,DistDirStack distdirCradle)
      qe <- liftIO $ mkQueryEnv projdir distdir
      return (Just qe)
  -- let
  --   (projdir,distdir) = case cradleProject crdl of
  --     CabalProject     -> (ProjLocCabalFile cabalFile,DisDirV1 distdir)
  --     CabalNewProject  -> (ProjLocCabalFile cabalFile,DisDirV1 distdir)
  --     SandboxProject   -> (ProjLocCabalFile cabalFile,DisDirV1 distdir)
  --     PlainProject     -> (ProjLocCabalFile cabalFile,DisDirV1 distdir)
  --     StackProject env -> (ProjLocCabalFile cabalFile,DisDirV1 distdir)
  -- return (mkQueryEnv projdir distdir) {
  --                 qeReadProcess = readProc
  --               , qePrograms = helperProgs progs
  --               }
  {-
    let projdir = takeDirectory cabal_file
    qe <- mkQueryEnv
            (psProjDir cabal_file)
            (psDistDir projdir)

-}
-- getQueryEnv = do
--   crdl <- cradle
--   progs <- patchStackPrograms crdl =<< (optPrograms <$> options)
--   readProc <- gmReadProcess
--   let projdir = cradleRootDir crdl
--       distdir = projdir </> cradleDistDir crdl
--   return (mkQueryEnv projdir distdir) {
--                   qeReadProcess = readProc
--                 , qePrograms = helperProgs progs
--                 }
-}

runCHQuery :: (IOish m, GmOut m, GmEnv m, Typeable pt)
           => ProjSetup (pt :: ProjType) -> Query (pt :: ProjType) b -> m b
runCHQuery ps a = do
  crdl <- cradle
  progs <- patchStackPrograms crdl =<< (optPrograms <$> options)
  readProc <- gmReadProcess
  case cradleCabalFile crdl of
    Nothing -> error "runCHQuery 1"
    Just cabalFile -> runProjSetup ps cabalFile (\qe -> runQuery a qe)

-- ---------------------------------------------------------------------

runProjSetup :: (IOish m, GmOut m, GmEnv m, Typeable pt)
             => ProjSetup (pt :: ProjType) -> FilePath -> (QueryEnv (pt :: ProjType) -> IO a) -> m a
runProjSetup ps cabalFile f = do
  let projdir = takeDirectory cabalFile
  crdl <- cradle
  -- progs <- patchStackPrograms crdl =<< (optPrograms <$> options)
  -- readProc <- gmReadProcess
  -- qeBare <- liftIO $ mkQueryEnv
  --             (psProjDir ps $ cabalFile)
  --             (psDistDir ps $ projdir)
  -- let qe = qeBare
  --            -- { qeReadProcess = \_ -> readProc
  --            -- , qePrograms = helperProgs progs
  --            -- }
  -- r <- liftIO $ f qe
  -- return r
  r <- case cradleCabalFile crdl of
    Nothing -> error "runProjSetup:Nothing"
    Just cabalFile -> do
      runF ps (cradleQueryEnv crdl) f
      -- case cradleProject crdl of
      --   CabalProject      -> runF ps (cradleQueryEnv crdl) f
      --   CabalNewProject   -> liftIO $ f (fromJust $ cradleQueryEnvV2 crdl)
      --   SandboxProject    -> liftIO $ f (fromJust $ cradleQueryEnvV1 crdl)
      --   StackProject _env -> liftIO $ f (fromJust $ cradleQueryEnvSt crdl)
      --   PlainProject      -> error $ "runProjSetup:PlainProject"
  return r

runF :: (MonadIO m, Typeable pt) => ProjSetup (pt :: ProjType) -> (Maybe Dynamic) -> (QueryEnv (pt :: ProjType) -> IO a) -> m a
runF _ Nothing _   = error "CabalHelper.runF"
runF _ (Just dqe) f = liftIO $ f qe
  where
    qe = case fromDynamic dqe of
      Nothing -> error "CabalHelper.runF 2"
      Just qe -> qe

-- ---------------------------------------------------------------------

withProjSetup :: (IOish m, GmOut m, GmEnv m) => (forall pt . Typeable pt => ProjSetup pt -> m a) -> m (Maybe a)
withProjSetup f = do
  crdl <- cradle
  progs <- patchStackPrograms crdl =<< (optPrograms <$> options)
  readProc <- gmReadProcess
  case cradleCabalFile crdl of
    Nothing -> return Nothing
    Just cabalFile -> do
      -- liftIO $ putStrLn $ "withProjSetup:project=" ++ show (cradleProject crdl)
      case cradleProject crdl of
        CabalProject      -> Just <$> f oldBuild
        CabalNewProject   -> Just <$> f newBuild
        SandboxProject    -> Just <$> f oldBuild
        StackProject _env -> Just <$> f stackBuild
        PlainProject      -> return Nothing

-- ---------------------------------------------------------------------

-- prepareCabalHelper :: (IOish m, GmEnv m, GmOut m, GmLog m, Typeable pt) => ProjSetup (pt :: ProjType) -> m ()
-- prepareCabalHelper ps = do
--   crdl <- cradle
--   when (isCabalHelperProject $ cradleProject crdl) $ do
--        qe <- getQueryEnv
--        withCabal ps $ liftIO (prepare qe)

getUnit :: (IOish m, GmEnv m, GmOut m, Typeable pt) => ProjSetup pt -> m (Unit pt)
getUnit ps = do
  crdl <- cradle
  let cabalFile = cradleCabalFile crdl
      filterUnit u
        | Just ccf <- cabalFile
        , CabalFile ucf <- uCabalFile u = ucf == ccf
        | otherwise = True
  allUnits <- runCHQuery ps projectUnits
  case NE.filter filterUnit allUnits of
    x:_ -> return x
    _ -> throw $ GMEString "getUnit: no units found matching the cabal file!"

withAutogen :: (IOish m, GmEnv m, GmOut m, GmLog m, Typeable pt) => ProjSetup pt -> m a -> m a
withAutogen ps action = do
    gmLog GmDebug "" $ strDoc "making sure autogen files exist"
    crdl <- cradle
    let projdir = cradleRootDir crdl
        distdir = projdir </> cradleDistDir crdl

    unit <- getUnit ps
    unitInfo <- runCHQuery ps $ unitInfo unit
    let (pkgName',_) = uiPackageId unitInfo

    mCabalFile          <- liftIO $ timeFile `traverse` cradleCabalFile crdl
    mCabalMacroHeader   <- liftIO $ timeMaybe (distdir </> macrosHeaderPath)
    mCabalPathsModule   <- liftIO $ timeMaybe (distdir </> autogenModulePath pkgName')

    when (mCabalMacroHeader < mCabalFile || mCabalPathsModule < mCabalFile) $ do
      gmLog GmDebug "" $ strDoc $ "autogen files out of sync"
      writeAutogen unit

    action

 where
   writeAutogen unit = do
     gmLog GmDebug "" $ strDoc "writing Cabal autogen files"
     runCHQuery ps $ writeAutogenFiles unit

-- ---------------------------------------------------------------------

withCabal :: (IOish m, GmEnv m, GmOut m, GmLog m, Typeable pt) => ProjSetup (pt :: ProjType) -> m a -> m a
withCabal ps action = do
    crdl <- cradle
    mCabalFile          <- liftIO $ timeFile `traverse` cradleCabalFile crdl
    mCabalConfig        <- liftIO $ timeMaybe (setupConfigFile crdl)
    mCabalSandboxConfig <- liftIO $ timeMaybe (sandboxConfigFile crdl)

    let haveSetupConfig = isJust mCabalConfig

    cusPkgDb <- getCustomPkgDbStack
    (flgs, pkgDbStackOutOfSync) <- do
      if haveSetupConfig
        then getUnit ps >>= \unit -> runCHQuery ps $ do
          ui <- unitInfo unit
          -- flgs <- nonDefaultConfigFlags
          let flgs = uiNonDefaultConfigFlags ui
          -- pkgDb <- map chPkgToGhcPkg <$> packageDbStack
          let pkgDb = map chPkgToGhcPkg (uiPackageDbStack ui)
          return (flgs, fromMaybe False $ (pkgDb /=) <$> cusPkgDb)
        else return ([], False)

    when (isSetupConfigOutOfDate mCabalFile mCabalConfig) $
      gmLog GmDebug "" $ strDoc $ "setup configuration is out of date"

    when (isSetupConfigOutOfDate mCabalSandboxConfig mCabalConfig) $
      gmLog GmDebug "" $ strDoc $ "sandbox configuration is out of date"

    when pkgDbStackOutOfSync $
      gmLog GmDebug "" $ strDoc $ "package-db stack out of sync with ghc-mod.package-db-stack"

    when ( isSetupConfigOutOfDate mCabalFile mCabalConfig
        || pkgDbStackOutOfSync
        || isSetupConfigOutOfDate mCabalSandboxConfig mCabalConfig) $ do
          proj <- cradleProject <$> cradle
          opts <- options
          case proj of
            CabalProject -> do
                gmLog GmDebug "" $ strDoc "reconfiguring Cabal project"
                cabalReconfigure "configure" (optPrograms opts) crdl flgs
            CabalNewProject -> do
                gmLog GmDebug "" $ strDoc "reconfiguring Cabal new-build project"
                cabalReconfigure "new-configure" (optPrograms opts) crdl flgs
            StackProject {} -> do
                gmLog GmDebug "" $ strDoc "reconfiguring Stack project"
                -- TODO: we could support flags for stack too, but it seems
                -- you're supposed to put those in stack.yaml so detecting which
                -- flags to pass down would be more difficult

                -- "--flag PACKAGE:[-]FLAG Override flags set in stack.yaml
                -- (applies to local packages and extra-deps)"

                stackReconfigure (optStackBuildDeps opts) crdl (optPrograms opts)
            _ ->
                error $ "withCabal: unsupported project type: " ++ show proj

    action

 where
   cabalReconfigure cmd progs crdl flgs = do
     readProc <- gmReadProcess
     withDirectory_ (cradleRootDir crdl) $ do
        cusPkgStack <- maybe [] ((PackageDb "clear"):) <$> getCustomPkgDbStack
        let progOpts =
                [ "--with-ghc=" ++ T.ghcProgram progs ]
                -- Only pass ghc-pkg if it was actually set otherwise we
                -- might break cabal's guessing logic
                ++ if T.ghcPkgProgram progs /= T.ghcPkgProgram (optPrograms defaultOptions)
                     then [ "--with-ghc-pkg=" ++ T.ghcPkgProgram progs ]
                     else []
                ++ map pkgDbArg cusPkgStack
                ++ flagOpt

            toFlag (f, True) = f
            toFlag (f, False) = '-':f
            flagOpt = ["--flags", unwords $ map toFlag flgs]

        liftIO $ void $ readProc (T.cabalProgram progs) (cmd:progOpts) ""
   stackReconfigure deps crdl progs = do
     withDirectory_ (cradleRootDir crdl) $ do
       supported <- haveStackSupport
       if supported
          then do
            when deps $
              spawn [T.stackProgram progs, "build", "--only-dependencies", "."]
            spawn [T.stackProgram progs, "build", "--only-configure", "."]
          else
            gmLog GmWarning "" $ strDoc $ "Stack project configuration is out of date, please reconfigure manually using 'stack build' as your stack version is too old (need at least 0.1.4.0)"

   spawn [] = return ()
   spawn (exe:args) = do
     readProc <- gmReadProcess
     liftIO $ void $ readProc exe args ""

   haveStackSupport = do
     (rv, _, _) <-
         liftIO $ readProcessWithExitCode "stack" ["--numeric-version"] ""
     case rv of
       ExitSuccess -> return True
       ExitFailure _ -> return False



pkgDbArg :: GhcPkgDb -> String
pkgDbArg GlobalDb      = "--package-db=global"
pkgDbArg UserDb        = "--package-db=user"
pkgDbArg (PackageDb p) = "--package-db=" ++ p

-- * Neither file exists -> should return False:
--   @Nothing < Nothing = False@
--   (since we don't need to @cabal configure@ when no cabal file exists.)
--
-- * Cabal file doesn't exist (impossible since cabal-helper is only used with
-- cabal projects) -> should return False
--   @Just cc < Nothing = False@
--
-- * dist/setup-config doesn't exist yet -> should return True:
--   @Nothing < Just cf = True@
--
-- * Both files exist
--   @Just cc < Just cf = cc < cf = cc `olderThan` cf@
isSetupConfigOutOfDate :: Maybe TimedFile -> Maybe TimedFile -> Bool
isSetupConfigOutOfDate worldCabalFile worldCabalConfig = do
  worldCabalConfig < worldCabalFile

helperProgs :: Programs -> CH.Programs
helperProgs = undefined
-- helperProgs progs = CH.Programs {
--     cabalProgram  = T.cabalProgram progs,
--     ghcProgram    = T.ghcProgram progs,
--     ghcPkgProgram = T.ghcPkgProgram progs
--   }

chCached :: (Applicative m, IOish m, Gm m, Binary a, Typeable pt)
  => ProjSetup pt -> (FilePath -> Cached m GhcModState ChCacheData a) -> m a
chCached ps c = do
  projdir <- cradleRootDir <$> cradle
  distdir <- (projdir </>) . cradleDistDir <$> cradle
  d <- cacheInputData projdir
  withCabal ps $ cached projdir (c distdir) d
 where
   -- we don't need to include the distdir in the cache input because when it
   -- changes the cache files will be gone anyways ;)
   cacheInputData projdir = do
               opts <- options
               crdl <- cradle
               progs' <- patchStackPrograms crdl (optPrograms opts)
               return $ ( helperProgs progs'
                        , projdir
                        , (showVersion gmVer, chVer)
                        )

   gmVer = GhcMod.version
   chVer = VERSION_cabal_helper
