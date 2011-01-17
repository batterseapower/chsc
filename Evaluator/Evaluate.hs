{-# LANGUAGE TupleSections, PatternGuards, ViewPatterns #-}
module Evaluator.Evaluate (Losers, emptyLosers, normalise, step) where

import Evaluator.Residualise
import Evaluator.Syntax

import Core.FreeVars
import Core.Renaming
import Core.Syntax
import Core.Prelude (trueDataCon, falseDataCon)

import Size.Deeds

import Renaming
import StaticFlags
import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M


type Losers = IS.IntSet

emptyLosers :: Losers
emptyLosers = IS.empty


-- | Non-expansive simplification we can do everywhere safely
--
-- This function only ever returns deeds to the deed pool, but may add them.
-- TODO: tag stack frames so we can lose the deeds argument altogether
normalise :: (Deeds, UnnormalisedState) -> (Deeds, State)
normalise (deeds, _state@(h, k, (rn, e))) =
  (\(deeds', state') -> assertRender (hang (text "normalise: deeds lost or gained:") 2 (pPrintFullUnnormalisedState _state))
                                     (not dEEDS || noChange (releaseUnnormalisedStateDeed deeds _state) (releaseStateDeed deeds' state')) (deeds', state')) $
  case annee e of
    Var x             -> (deeds, (h, k, (rn, fmap (const (Question x)) e)))
    Value v           -> (deeds, (h, k, (rn, fmap (const (Answer v)) e)))
    App e1 x2         -> normalise (deeds', (h, Apply (renameAnnedVar rn x2)    : k, (rn, e1)))
    PrimOp pop (e:es) -> normalise (deeds', (h, PrimApply pop [] (map (rn,) es) : k, (rn, e)))
    Case e alts       -> normalise (deeds', (h, Scrutinise (rn, alts)           : k, (rn, e)))
    LetRec xes e      -> normalise (allocate deeds' h k (rn, (xes, e)))
  where
    tg = annedTag e
    deeds' = releaseDeedDescend_ deeds tg

    allocate :: Deeds -> Heap -> Stack -> In ([(Var, AnnedTerm)], AnnedTerm) -> (Deeds, UnnormalisedState)
    allocate deeds (Heap h ids) k (rn, (xes, e)) = (deeds, (Heap (h `M.union` M.map Concrete (M.fromList xes')) ids', k, (rn', e)))
      where (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes

step :: (Deeds, State) -> Maybe (Deeds, State)
step (deeds, _state@(h, k, (rn, qa))) =
  (\mb_res -> assertRender (hang (text "step: deeds lost or gained:") 2 (pPrintFullState _state))
                           (not dEEDS || maybe True (\(deeds', state') -> noChange (releaseStateDeed deeds _state) (releaseStateDeed deeds' state')) mb_res) mb_res) $
  fmap normalise $ case annee qa of
    Question x -> force  deeds h k tg (rename rn x)
    Answer   v -> unwind deeds h k tg (rn, v)
  where
    tg = annedTag qa
      
    force :: Deeds -> Heap -> Stack -> Tag -> Out Var -> Maybe (Deeds, UnnormalisedState)
    force deeds (Heap h ids) k tg x' = do { Concrete in_e <- M.lookup x' h; return (deeds, (Heap (M.delete x' h) ids, Update (annedVar tg x') : k, in_e)) }

    unwind :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> Maybe (Deeds, UnnormalisedState)
    unwind deeds h k tg_v in_v = uncons k >>= \(kf, k) -> case kf of
        Apply x2'                 -> return $ apply      deeds h k tg_v in_v x2'
        Scrutinise in_alts        ->          scrutinise deeds h k tg_v in_v in_alts
        PrimApply pop in_vs in_es -> return $ primop     deeds h k tg_v pop in_vs in_v in_es
        Update x'                 ->          update     deeds h k tg_v x' in_v

    apply :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> Out (Anned Var) -> (Deeds, UnnormalisedState)
    apply deeds h k tg_v (rn, Lambda x e_body) x2' = (deeds', (h, k, (insertRenaming x (annee x2') rn, e_body)))
      where deeds' = releaseDeedDescend_ (releaseDeedDeep deeds (annedTag x2')) tg_v
    apply _     _ _ _    (_,  v)               _   = panic "apply" (pPrint v)

    scrutinise :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> In [AnnedAlt] -> Maybe (Deeds, UnnormalisedState)
    scrutinise deeds h            k tg_v (_,    Literal l)  (rn_alts, alts)
      | (alt_e, rest):_ <- [((rn_alts, alt_e), rest) | ((LiteralAlt alt_l, alt_e), rest) <- bagContexts alts, alt_l == l] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (h, k, alt_e))
    scrutinise deeds h            k tg_v (rn_v, Data dc xs) (rn_alts, alts)
      | (alt_e, rest):_ <- [((insertRenamings (alt_xs `zip` map (rename rn_v) xs) rn_alts, alt_e), rest) | ((DataAlt alt_dc alt_xs, alt_e), rest) <- bagContexts alts, alt_dc == dc] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (h, k, alt_e))
    scrutinise deeds (Heap h ids) k tg_v (rn_v, v)          (rn_alts, alts)
      | ((alt_x, alt_e), rest):_ <- [((alt_x, alt_e), rest) | ((DefaultAlt (Just alt_x), alt_e), rest) <- bagContexts alts]
      , (ids', rn_alts', alt_x') <- renameBinder ids rn_alts alt_x
      = Just (releaseAltDeeds rest deeds, (Heap (M.insert alt_x' (Concrete (rn_v, annedTerm tg_v $ Value v)) h) ids', k, (rn_alts', alt_e)))
      | otherwise
      = Nothing -- This can legitimately occur, e.g. when supercompiling (if x then (case x of False -> 1) else 2)

    releaseAltDeeds :: [(a, AnnedTerm)] -> Deeds -> Deeds
    releaseAltDeeds alts deeds = foldl' (\deeds (_, in_e) -> releaseDeedDeep deeds (annedTag in_e)) deeds alts

    primop :: Deeds -> Heap -> Stack -> Tag -> PrimOp -> [In (Anned AnnedValue)] -> In AnnedValue -> [In AnnedTerm] -> (Deeds, UnnormalisedState)
    primop deeds h k tg_v2 pop [(_, Comp (Tagged tg_v1 (FVed _ (Literal (Int l1)))))] (_, Literal (Int l2)) [] = (releaseDeedDeep deeds tg_v1, (h, k, (emptyRenaming, annedTerm tg_v2 (Value (f pop l1 l2)))))
      where f pop = case pop of Add -> retInt (+); Subtract -> retInt (-);
                                Multiply -> retInt (*); Divide -> retInt div; Modulo -> retInt mod;
                                Equal -> retBool (==); LessThan -> retBool (<); LessThanEqual -> retBool (<=)
            retInt  pop l1 l2 = Literal (Int (pop l1 l2))
            retBool pop l1 l2 = if pop l1 l2 then Data trueDataCon [] else Data falseDataCon []
    primop deeds h k tg_v  pop in_vs (rn, v) (in_e:in_es) = (deeds, (h, PrimApply pop (in_vs ++ [(rn, annedValue tg_v v)]) in_es : k, in_e))

    update :: Deeds -> Heap -> Stack -> Tag -> Anned (Out Var) -> In AnnedValue -> Maybe (Deeds, UnnormalisedState)
    update deeds (Heap h ids) k tg_v x' (rn, v) = case claimDeed deeds' tg_v of
        Nothing      -> traceRender ("update: deed claim FAILURE", annee x') Nothing
        Just deeds'' -> Just (deeds'', (Heap (M.insert (annee x') (Concrete (rn, annedTerm tg_v (Value v))) h) ids, k, (rn, annedTerm tg_v (Value v))))
      where
        -- Unconditionally release the tag associated with the update frame
        deeds' = releaseDeedDeep deeds (annedTag x')
