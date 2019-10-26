{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | This module has been extracted from ghc-mod-core GhcMod.Types, to
-- provide a basis of types that can be shared between various
-- alternative backends for the hie-bios.
module GhcProject.Types
  (
    GmModuleGraph(..)
  , ModulePath(..)
  , GmComponent(..)
  , GmComponentType(..)
  ) where

-- ---------------------------------------------------------------------

import Control.Applicative
import Control.Monad
import Data.Binary
import Data.Binary.Generic
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Data.Maybe
import Data.Typeable (Typeable)
import Distribution.Helper hiding (Programs(..))
import qualified Distribution.Helper as CabalHelper
#if __GLASGOW_HASKELL__ < 708
import qualified MonadUtils as GHC (MonadIO(..))
#endif
import GHC (ModuleName, moduleNameString, mkModuleName)
import GHC.Generics
import Prelude

-- ---------------------------------------------------------------------

data GmModuleGraph = GmModuleGraph {
    gmgGraph :: Map ModulePath (Set ModulePath)
  } deriving (Eq, Ord, Show, Read, Generic, Typeable)

instance Binary GmModuleGraph where
  put GmModuleGraph {..} = put (mpim, graph)
    where
      mpim :: Map ModulePath Integer
      mpim = Map.fromList $ Map.keys gmgGraph `zip` [0..]
      graph :: Map Integer (Set Integer)
      graph = Map.map (Set.map mpToInt) $ Map.mapKeys mpToInt gmgGraph
      mpToInt :: ModulePath -> Integer
      mpToInt mp = fromJust $ Map.lookup mp mpim

  get = do
    (mpim :: Map ModulePath Integer, graph :: Map Integer (Set Integer)) <- get
    let impm = swapMap mpim
        intToMp i = fromJust $ Map.lookup i impm
        mpGraph :: Map ModulePath (Set ModulePath)
        mpGraph = Map.map (Set.map intToMp) $ Map.mapKeys intToMp graph
    return $ GmModuleGraph mpGraph
    where
      swapMap :: Ord v => Map k v -> Map v k
      swapMap = Map.fromList . map (\(x, y) -> (y, x)) . Map.toList

#if __GLASGOW_HASKELL__ >= 804
instance Semigroup GmModuleGraph where
  (<>) = mappend
#endif

instance Monoid GmModuleGraph where
  mempty  = GmModuleGraph mempty
  mappend (GmModuleGraph a) (GmModuleGraph a') =
    GmModuleGraph (Map.unionWith Set.union a a')

-- ---------------------------------------------------------------------

data GmComponentType = GMCRaw
                     | GMCResolved
data GmComponent (t :: GmComponentType) eps = GmComponent {
    gmcHomeModuleGraph :: GmModuleGraph
  , gmcGhcOpts         :: [GHCOption]
  , gmcGhcPkgOpts      :: [GHCOption]
  , gmcGhcSrcOpts      :: [GHCOption]
  , gmcGhcLangOpts     :: [GHCOption]
  , gmcRawEntrypoints  :: ChEntrypoint
  , gmcEntrypoints     :: eps
  , gmcSourceDirs      :: [FilePath]
  , gmcName            :: ChComponentName
  } deriving (Eq, Ord, Show, Read, Generic, Functor)

instance Binary eps => Binary (GmComponent t eps) where
    put = ggput . from
    get = to `fmap` ggget

data ModulePath = ModulePath { mpModule :: ModuleName, mpPath :: FilePath }
  deriving (Eq, Ord, Show, Read, Generic, Typeable)
instance Binary ModulePath where
    put = ggput . from
    get = to `fmap` ggget

instance Binary ModuleName where
  get = mkModuleName <$> get
  put mn = put (moduleNameString mn)

instance Show ModuleName where
  show mn = "ModuleName " ++ show (moduleNameString mn)

instance Read ModuleName where
  readsPrec d =
    readParen
      (d > app_prec)
      (\r' -> [ (mkModuleName m, t)
              | ("ModuleName", s) <- lex r'
              , (m, t)            <- readsPrec (app_prec + 1) s
              ])
    where
      app_prec = 10

-- ---------------------------------------------------------------------

-- | A single GHC command line option.
type GHCOption = String

-- ---------------------------------------------------------------------

instance Binary CabalHelper.Programs where
    put = ggput . from
    get = to `fmap` ggget
instance Binary ChModuleName where
    put = ggput . from
    get = to `fmap` ggget
instance Binary ChComponentName where
    put = ggput . from
    get = to `fmap` ggget
instance Binary ChEntrypoint where
    put = ggput . from
    get = to `fmap` ggget
instance Binary ChLibraryName where
    put = ggput . from
    get = to `fmap` ggget
instance Binary EnvOverride where
    put = ggput . from
    get = to `fmap` ggget

-- ---------------------------------------------------------------------
