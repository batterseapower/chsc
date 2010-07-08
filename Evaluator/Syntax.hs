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
                | PrimApply PrimOp [In TaggedValue] [In TaggedTerm]
                | Update (Out Var)
                deriving (Show)
