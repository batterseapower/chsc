module Evaluator.Syntax where

import Size.Deeds

import Core.Renaming
import Core.Syntax

import Utilities

import qualified Data.Map as M


type State = (Heap, Stack, In TaggedTerm)

type PureHeap = M.Map (Out Var) (In TaggedTerm)
data Heap = Heap PureHeap IdSupply
          deriving (Show)

type Stack = [StackFrame]
data StackFrame = Apply (Out (Tagged Var))
                | Scrutinise (In [TaggedAlt])
                | PrimApply PrimOp [Tagged (In TaggedValue)] [In TaggedTerm]
                | Update (Out (Tagged Var))
                deriving (Show)

instance Pretty StackFrame where
    pPrintPrec level prec kf = case kf of
        Apply x'                  -> pPrintPrecApp level prec (text "[_]") x'
        Scrutinise in_alts        -> pPrintPrecCase level prec (text "[_]") (renameIn renameTaggedAlts prettyIdSupply in_alts)
        PrimApply pop in_vs in_es -> pPrintPrecPrimOp level prec pop (map SomePretty in_vs ++ map SomePretty in_es)
        Update x'                 -> pPrintPrecApp level prec (text "update") x'


stackFrameTags :: StackFrame -> [Tag]
stackFrameTags kf = case kf of
    Apply x'                -> [tag x']
    Scrutinise in_alts      -> map (tag . snd) (snd in_alts)
    PrimApply _ in_vs in_es -> map tag in_vs ++ map (tag . snd) in_es
    Update x'               -> [tag x']

releaseStateDeed :: Deeds -> State -> Deeds
releaseStateDeed deeds (Heap h _, k, (_, e))
  = foldl' (\deeds kf -> foldl' releaseDeedDeep deeds (stackFrameTags kf))
           (foldl' (\deeds (_, e) -> releaseDeedDeep deeds (tag e))
                   (releaseDeedDeep deeds (tag e))
                   (M.elems h))
           k
