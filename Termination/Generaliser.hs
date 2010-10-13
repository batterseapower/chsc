module Termination.Generaliser where

import Core.Syntax   (Var)
import Core.Renaming (In, Out)

import Evaluator.Syntax


data Generaliser = Generaliser {
    generaliseStackFrame  :: StackFrame -> Bool,
    generaliseHeapBinding :: Out Var -> In AnnedTerm -> Bool
  }

generaliseNothing :: Generaliser
generaliseNothing = Generaliser (\_ -> False) (\_ _ -> False)
