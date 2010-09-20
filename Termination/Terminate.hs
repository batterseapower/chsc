{-# LANGUAGE PatternGuards #-}
module Termination.Terminate (
        -- * The tag collection interface
        TagCollection(..),
        
        -- * Testing for growing bags
        GrowingTags, isTagGrowing,

        -- * The termination criterion
        History, emptyHistory, TermRes(..), isContinue, terminate,
        
        -- * History combination for rollback
        forgetFutureHistory
    ) where

import Evaluator.Syntax

import Utilities

import qualified Data.IntSet as IS


class TagCollection tc where
    (<|) :: tc -> tc -> Bool
    growingTags :: tc -> tc -> GrowingTags
    stateTags :: State -> tc


type GrowingTags = IS.IntSet

isTagGrowing :: GrowingTags -> Tag -> Bool
isTagGrowing gts tg = tg `IS.member` gts


newtype History tc a = History { unHistory :: [(tc, a)] }

instance Functor (History tc) where
    fmap f hist = History $ map (second f) (unHistory hist)

emptyHistory :: History tc a
emptyHistory = History []

data TermRes tc a = Stop GrowingTags a | Continue (a -> History tc a)

isContinue :: TermRes tc a -> Bool
isContinue (Continue _) = True
isContinue _ = False

terminate :: TagCollection tc => History tc a -> tc -> TermRes tc a
terminate hist here
  -- | traceRender (length hist, tagBag here) && False = undefined
  | (prev, prev_extra):_ <- [(prev, prev_extra) | (prev, prev_extra) <- unHistory hist, if prev <| here then {- traceRender (hang (text "terminate") 2 (pPrint hist $$ pPrint here)) -} True else False]
  = Stop (prev `growingTags` here) prev_extra
  | otherwise
  = Continue (\here_extra -> History $ (here, here_extra) : unHistory hist)

-- FIXME: make less ugly
forgetFutureHistory :: History tc (Maybe a) -> History tc (Maybe a) -> History tc (Maybe a)
forgetFutureHistory (History short) (History long) = History $ short ++ fmap (second (const Nothing)) (short `dropBy` long)
