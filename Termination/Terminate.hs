{-# LANGUAGE PatternGuards #-}
module Termination.Terminate (
        -- * The tag collection interface
        Generaliser(..), generaliseNothing, TagCollection(..),
        
        -- * The termination criterion
        History, emptyHistory, TermRes(..), isContinue, terminate,
        
        -- * History combination for rollback
        forgetFutureHistory
    ) where

import Core.Syntax   (Var)
import Core.Renaming (In, Out)

import Evaluator.Syntax

import Utilities


class TagCollection tc where
    (<|) :: tc -> tc -> Maybe Generaliser
    stateTags :: State -> tc


data Generaliser = Generaliser {
    generaliseStackFrame  :: StackFrame -> Bool,
    generaliseHeapBinding :: Out Var -> In AnnedTerm -> Bool
  }

generaliseNothing :: Generaliser
generaliseNothing = Generaliser (\_ -> False) (\_ _ -> False)


newtype History tc a = History { unHistory :: [(tc, a)] }

instance Functor (History tc) where
    fmap f hist = History $ map (second f) (unHistory hist)

emptyHistory :: History tc a
emptyHistory = History []

data TermRes tc a = Stop Generaliser a | Continue (a -> History tc a)

isContinue :: TermRes tc a -> Bool
isContinue (Continue _) = True
isContinue _ = False

terminate :: TagCollection tc => History tc a -> tc -> TermRes tc a
terminate hist here
  -- | traceRender (length hist, tagBag here) && False = undefined
  | (gen, prev_extra):_ <- [(gen, prev_extra) | (prev, prev_extra) <- unHistory hist, Just gen <- [prev <| here]]
  = Stop gen prev_extra
  | otherwise
  = Continue (\here_extra -> History $ (here, here_extra) : unHistory hist)

-- FIXME: make less ugly
forgetFutureHistory :: History tc (Maybe a) -> History tc (Maybe a) -> History tc (Maybe a)
forgetFutureHistory (History short) (History long) = History $ short ++ fmap (second (const Nothing)) (short `dropBy` long)
