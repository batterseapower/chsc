module Termination.Statics (
    embedStatics
  ) where

import Termination.Generaliser
import Termination.Terminate

import Supercompile.Split (StaticSort(..), Statics(..))

import Core.Renaming (Out)
import Core.Syntax (Var)
import Evaluator.Syntax (annedTag)

import Utilities

import qualified Data.IntMap as IM
import qualified Data.Map as M


embedStatics :: WQO Statics StaticGeneraliser
embedStatics = precomp (staticsTags . staticVars) $ postcomp generaliserFromGrowing $ refineCollection (\discard -> postcomp discard $ zippable nat)
  where
    staticsTags :: M.Map (Out Var) StaticSort -> TagMap Nat
    staticsTags fvs = IM.unionsWith (+) [IM.singleton tg 1 | LocalVariable tg <- M.elems fvs] -- FIXME: make InputVariable eligible for generalisation
    
    generaliserFromGrowing :: TagMap Bool -> StaticGeneraliser
    generaliserFromGrowing growing = StaticGeneraliser $ \x -> fromMaybe False $ IM.lookup (annedTag x) growing
