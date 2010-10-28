{-# LANGUAGE FlexibleContexts #-}
module Termination.Statics (
    embedStatics
  ) where

import Termination.Generaliser
import Termination.Terminate

import Core.Renaming (Out)
import Core.Syntax (Var)
import Core.Statics (StaticSort(..), Statics(..))

import Utilities

import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable


-- | A wrapper for variables that were free in the initial program (of which there are guaranteed to be a finite number)
newtype InputVar = UnsafeCertifyInputVar (Out Var)
                 deriving (Eq, Ord)
instance Finite InputVar


embedStatics :: WQO Statics StaticGeneraliser
embedStatics = precomp (staticsTags . staticVars) $ postcomp generaliserFromGrowing (bag `prod` bag)
  where
    bag :: (HasDomain f, Finite (Domain f),                 -- Only works for things with finite domains
            Foldable.Foldable f, Traversable.Traversable f) -- We insist that the things are Traversable (and hence Functor) so we can actually do some structure-preserving operations on the versions with domain equality evidence
        => WQO (f Nat) (f Bool)
    bag = refineCollection (\discard -> postcomp discard $ zippable nat)
    
    staticsTags :: M.Map (Out Var) StaticSort -> (TagMap Nat, M.Map InputVar Nat)
    staticsTags statics = (IM.unionsWith (+) [IM.singleton tg 1 | LocalVariable tg <- M.elems statics],
                           M.unionsWith (+) [M.singleton (UnsafeCertifyInputVar x) 1 | (x, InputVariable) <- M.toList statics])
    
    generaliserFromGrowing :: (TagMap Bool, M.Map InputVar Bool) -> StaticGeneraliser
    generaliserFromGrowing (growing_locals, growing_inputs)
      = StaticGeneraliser $ \x' sort -> fromMaybe False $ do { LocalVariable tg <- return sort; IM.lookup tg growing_locals } `mplus`
                                                          do { InputVariable <- return sort; M.lookup (UnsafeCertifyInputVar x') growing_inputs }
