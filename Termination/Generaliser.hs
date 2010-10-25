module Termination.Generaliser where

import Core.Syntax   (Var)
import Core.Renaming (In, Out)

import Evaluator.Syntax


type Generaliser = (StaticGeneraliser, StateGeneraliser)

newtype StaticGeneraliser = StaticGeneraliser {
    generaliseStaticVar :: Out (Anned Var) -> Bool
  }

staticGeneraliseNothing :: StaticGeneraliser
staticGeneraliseNothing = StaticGeneraliser (\_ -> False)

data StateGeneraliser = StateGeneraliser {
    generaliseStackFrame  :: StackFrame -> Bool,
    generaliseHeapBinding :: Out Var -> In AnnedTerm -> Bool
  }

stateGeneraliseNothing :: StateGeneraliser
stateGeneraliseNothing = StateGeneraliser (\_ -> False) (\_ _ -> False)

generaliseNothing :: Generaliser
generaliseNothing = (staticGeneraliseNothing, stateGeneraliseNothing)
