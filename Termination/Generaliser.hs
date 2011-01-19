module Termination.Generaliser where

import Core.Syntax   (Var)
import Core.Renaming (Out)

import Evaluator.Syntax

import Utilities (Tagged)


data Generaliser = Generaliser {
    generaliseStackFrame  :: Tagged StackFrame -> Bool,
    generaliseHeapBinding :: Out Var -> HeapBinding -> Bool
  }

generaliseNothing :: Generaliser
generaliseNothing = Generaliser (\_ -> False) (\_ _ -> False)
