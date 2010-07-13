module Evaluator.Syntax where

import Core.Renaming
import Core.Syntax

import Utilities

import qualified Data.Map as M


type State = (Heap, Stack, In TaggedTerm)

type PureHeap = M.Map (Out Var) (In TaggedTerm)
data Heap = Heap PureHeap IdSupply
          deriving (Show)

type Stack = [Tagged StackFrame]
data StackFrame = Apply (Out Var)
                | Scrutinise (In [TaggedAlt])
                | PrimApply PrimOp [Tagged (In TaggedValue)] [In TaggedTerm]
                | Update (Out Var)
                deriving (Show)

instance Pretty StackFrame where
    pPrintPrec level prec kf = case kf of
        Apply x'                  -> pPrintPrecApp level prec (text "[_]") x'
        Scrutinise in_alts        -> pPrintPrecCase level prec (text "[_]") (renameIn renameTaggedAlts prettyIdSupply in_alts)
        PrimApply pop in_vs in_es -> pPrintPrecPrimOp level prec pop (map SomePretty in_vs ++ map SomePretty in_es)
        Update x'                 -> pPrintPrecApp level prec (text "update") x'
