{-# LANGUAGE TupleSections, PatternGuards, ViewPatterns #-}
module Evaluator.Evaluate (Losers, emptyLosers, step) where

import Evaluator.Residualise
import Evaluator.Syntax

import Core.FreeVars
import Core.Renaming
import Core.Syntax
import Core.Prelude (trueDataCon, falseDataCon)

import Size.Deeds

import Renaming
import Name
import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M


type Losers = IS.IntSet

emptyLosers :: Losers
emptyLosers = IS.empty


step :: (Deeds, State) -> Maybe (Deeds, State)
step (deeds, _state@(h, k, (rn, e))) =
  (\mb_res -> assertRender (hang (text "step: deeds lost or gained when stepping:") 2 (pPrint (residualiseState _state)))
                           (maybe True (\(deeds', state') -> noChange (releaseStateDeed deeds _state) (releaseStateDeed deeds' state')) mb_res) mb_res) $
  case annee e of
    Var x             -> force  deeds h k tg (rename rn x)
    Value x v         -> unwind deeds h k tg (rn, (x, v))
    App e1 x2         -> Just (deeds', (h, Apply (renameAnnedVar rn x2)    : k, (rn, e1)))
    PrimOp pop (e:es) -> Just (deeds', (h, PrimApply pop [] (map (rn,) es) : k, (rn, e)))
    Case e alts       -> Just (deeds', (h, Scrutinise (rn, alts)           : k, (rn, e)))
    LetRec xes e      -> Just (allocate deeds' h k (rn, (xes, e)))
  where
    tg = annedTag e
    deeds' = releaseDeedDescend_ deeds tg

    force :: Deeds -> Heap -> Stack -> Tag -> Out Var -> Maybe (Deeds, State)
    force deeds (Heap h ids) k tg x' = do { Concrete in_e <- M.lookup x' h; return (deeds, (Heap (M.delete x' h) ids, Update (annedVar tg x') : k, in_e)) }

    unwind :: Deeds -> Heap -> Stack -> Tag -> In (Maybe Var, AnnedValue) -> Maybe (Deeds, State)
    unwind deeds h k tg_v in_v = uncons k >>= \(kf, k) -> case kf of
        Apply x2'                 -> return $ apply      deeds h k tg_v in_v x2'
        Scrutinise in_alts        ->          scrutinise deeds h k tg_v in_v in_alts
        PrimApply pop in_vs in_es -> return $ primop     deeds h k tg_v pop in_vs in_v in_es
        Update x'                 ->          update     deeds h k tg_v x' in_v

    apply :: Deeds -> Heap -> Stack -> Tag -> In (Maybe Var, AnnedValue) -> Out (Anned Var) -> (Deeds, State)
    apply deeds h k tg_v (rn, (_, Lambda x e_body)) x2' = (deeds', (h, k, (insertRenaming x (annee x2') rn, e_body)))
      where deeds' = releaseDeedDescend_ (releaseDeedDeep deeds (annedTag x2')) tg_v
    apply _     _ _ _    (_,  (_, v))               _   = panic "apply" (pPrint v)

    scrutinise :: Deeds -> Heap -> Stack -> Tag -> In (Maybe Var, AnnedValue) -> In [AnnedAlt] -> Maybe (Deeds, State)
    scrutinise deeds h            k tg_v (_,    (_, Literal l))  (rn_alts, alts)
      | (alt_e, rest):_ <- [((rn_alts, alt_e), rest) | ((LiteralAlt alt_l, alt_e), rest) <- bagContexts alts, alt_l == l] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (h, k, alt_e))
    scrutinise deeds h            k tg_v (rn_v, (_, Data dc xs)) (rn_alts, alts)
      | (alt_e, rest):_ <- [((insertRenamings (alt_xs `zip` map (rename rn_v) xs) rn_alts, alt_e), rest) | ((DataAlt alt_dc alt_xs, alt_e), rest) <- bagContexts alts, alt_dc == dc] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (h, k, alt_e))
    scrutinise deeds (Heap h ids) k tg_v (rn_v, (x_v, v))        (rn_alts, alts)
      | ((alt_x, alt_e), rest):_ <- [((alt_x, alt_e), rest) | ((DefaultAlt (Just alt_x), alt_e), rest) <- bagContexts alts]
      , (h', ids', rn_alts') <- case x_v of
          Nothing  -> (M.insert alt_x' (Concrete (rn_v, annedTerm tg_v $ Value Nothing v)) h, ids', rn_alts')
            where (ids', rn_alts', alt_x') = renameBinder ids rn_alts alt_x
          Just x_v -> (h, ids, insertRenaming alt_x x_v rn_alts)
      = Just (releaseAltDeeds rest deeds, (Heap h' ids', k, (rn_alts', alt_e)))
      | otherwise
      = Nothing -- This can legitimately occur, e.g. when supercompiling (if x then (case x of False -> 1) else 2)

    releaseAltDeeds :: [(a, AnnedTerm)] -> Deeds -> Deeds
    releaseAltDeeds alts deeds = foldl' (\deeds (_, in_e) -> releaseDeedDeep deeds (annedTag in_e)) deeds alts

    primop :: Deeds -> Heap -> Stack -> Tag -> PrimOp -> [In (Maybe Var, Anned AnnedValue)] -> In (Maybe Var, AnnedValue) -> [In AnnedTerm] -> (Deeds, State)
    primop deeds h k tg_v2 pop [(_, (_, Comp (Tagged tg_v1 (FVed _ (Literal (Int l1))))))] (_, (_, Literal (Int l2))) [] = (releaseDeedDeep deeds tg_v1, (h, k, (emptyRenaming, annedTerm tg_v2 (Value Nothing (f pop l1 l2)))))
      where f pop = case pop of Add -> retInt (+); Subtract -> retInt (-);
                                Multiply -> retInt (*); Divide -> retInt div; Modulo -> retInt mod;
                                Equal -> retBool (==); LessThan -> retBool (<); LessThanEqual -> retBool (<=)
            retInt  pop l1 l2 = Literal (Int (pop l1 l2))
            retBool pop l1 l2 = if pop l1 l2 then Data trueDataCon [] else Data falseDataCon []
    primop deeds h k tg_v  pop in_vs (rn, (x_v, v)) (in_e:in_es) = (deeds, (h, PrimApply pop (in_vs ++ [(rn, (x_v, annedValue tg_v v))]) in_es : k, in_e))

    update :: Deeds -> Heap -> Stack -> Tag -> Anned (Out Var) -> In (Maybe Var, AnnedValue) -> Maybe (Deeds, State)
    update deeds (Heap h ids) k tg_v x' (rn, (x_v, v)) = case claimDeed (releaseDeedDeep deeds (annedTag x')) tg_v of -- Unconditionally release the tag associated with the update frame
        Nothing      -> traceRender ("update: deed claim FAILURE", annee x') Nothing
        Just deeds'' -> Just (deeds'', (Heap (M.insert (annee x') (Concrete (rn, annedTerm tg_v (Value x_v v))) h) ids', k, (insertRenaming x'' (annee x') rn, annedTerm tg_v (Value (Just x'') v))))
          where (ids', x'') = freshName ids (name_string (annee x'))

    allocate :: Deeds -> Heap -> Stack -> In ([(Var, AnnedTerm)], AnnedTerm) -> (Deeds, State)
    allocate deeds (Heap h ids) k (rn, (xes, e)) = (deeds, (Heap (h `M.union` M.map Concrete (M.fromList xes')) ids', k, (rn', e)))
      where (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes
