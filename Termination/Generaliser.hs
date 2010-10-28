module Termination.Generaliser where

import Core.Syntax   (Var)
import Core.Renaming (In, Out)
import Core.Statics  (StaticSort)

import Evaluator.Syntax


type Generaliser = (StaticGeneraliser, StateGeneraliser)

newtype StaticGeneraliser = StaticGeneraliser {
    generaliseStaticVar :: Out Var -> StaticSort -> Bool
  }

staticGeneraliseNothing :: StaticGeneraliser
staticGeneraliseNothing = StaticGeneraliser (\_ _ -> False)

data StateGeneraliser = StateGeneraliser {
    generaliseStackFrame  :: StackFrame -> Bool,
    generaliseHeapBinding :: Out Var -> In AnnedTerm -> Bool
  }

stateGeneraliseNothing :: StateGeneraliser
stateGeneraliseNothing = StateGeneraliser (\_ -> False) (\_ _ -> False)

generaliseNothing :: Generaliser
generaliseNothing = (staticGeneraliseNothing, stateGeneraliseNothing)
