module Termination.Statics (
    embedStatics
  ) where

import Termination.Generaliser
import Termination.Terminate

import Supercompile.Split (Statics(..))

import Core.FreeVars
import Evaluator.Syntax (annedTag)

import Utilities

import qualified Data.IntMap as IM
import qualified Data.Map as M


embedStatics :: WQO Statics StaticGeneraliser
embedStatics = precomp (freeVarsTags . staticVars) $ postcomp generaliserFromGrowing $ wqo_foo
  where
    wqo_foo :: WQO (TagMap Nat) (TagMap Bool)
    wqo_foo = refineCollection (\discard -> postcomp discard $ zippable nat)
      
    freeVarsTags :: FreeVars -> TagMap Nat
    freeVarsTags fvs = IM.unionsWith (+) [IM.singleton (tag ann) 1 | anns <- M.elems fvs, ann <- anns]
    
    generaliserFromGrowing :: TagMap Bool -> StaticGeneraliser
    generaliserFromGrowing growing = StaticGeneraliser $ \x -> fromMaybe False $ IM.lookup (annedTag x) growing
