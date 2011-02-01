{-# LANGUAGE TupleSections, PatternGuards, ViewPatterns #-}
module Evaluator.Evaluate (normalise, step) where

import Evaluator.FreeVars
import Evaluator.Residualise
import Evaluator.Syntax

import Core.Renaming
import Core.Syntax
import Core.Prelude (trueDataCon, falseDataCon)

import Size.Deeds

import Renaming
import StaticFlags
import Utilities

import qualified Data.Map as M


-- | Non-expansive simplification we can do everywhere safely
--
-- This function only ever returns deeds to the deed pool, but may add them.
-- TODO: tag stack frames so we can lose the deeds argument altogether
normalise :: (Deeds, UnnormalisedState) -> (Deeds, State)
normalise (deeds, state) =
    (\(deeds', state') -> assertRender (hang (text "normalise: deeds lost or gained:") 2 (pPrintFullUnnormalisedState state $$ pPrint deeds $$ pPrintFullState state' $$ pPrint deeds'))
                                       (True || not dEEDS || noChange (releaseStateDeed deeds state) (releaseStateDeed deeds' state')) $ -- TODO: fix deeds checks (tagged stack frames bugger us)
                          assertRender (text "normalise: FVs") (stateFreeVars state == stateFreeVars state') $
                          -- traceRender (text "normalising" $$ nest 2 (pPrintFullUnnormalisedState state) $$ text "to" $$ nest 2 (pPrintFullState state')) $
                          (deeds', state')) $
    go (deeds, state)
  where
    go (deeds, (h, k, (rn, e))) = case annee e of
        Var x             -> (deeds, (h, k, (rn, fmap (const (Question x)) e)))
        Value v           -> maybe (deeds, (h, k, (rn, fmap (const (Answer v)) e))) normalise $ unwind False deeds h k tg (rn, v)
        App e1 x2         -> normalise (deeds, (h, Tagged tg (Apply (rename rn x2))            : k, (rn, e1)))
        PrimOp pop (e:es) -> normalise (deeds, (h, Tagged tg (PrimApply pop [] (map (rn,) es)) : k, (rn, e)))
        Case e alts       -> normalise (deeds, (h, Tagged tg (Scrutinise (rn, alts))           : k, (rn, e)))
        LetRec xes e      -> normalise (allocate deeds' h k (rn, (xes, e)))
          where deeds' = releaseDeedDescend_ deeds tg
      where tg = annedTag e

    allocate :: Deeds -> Heap -> Stack -> In ([(Var, AnnedTerm)], AnnedTerm) -> (Deeds, UnnormalisedState)
    allocate deeds (Heap h ids) k (rn, (xes, e)) = (deeds, (Heap (h `M.union` M.map Concrete (M.fromList xes')) ids', k, (rn', e)))
      where (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes

step :: (Deeds, State) -> Maybe (Deeds, State)
step (deeds, _state@(h, k, (rn, qa))) =
  (\mb_res -> assertRender (hang (text "step: deeds lost or gained:") 2 (pPrintFullState _state))
                           (True || not dEEDS || maybe True (\(deeds', state') -> noChange (releaseStateDeed deeds _state) (releaseStateDeed deeds' state')) mb_res) $ -- TODO: fix deeds checks (tagged stack frames bugger us)
              -- (case mb_res of Nothing -> traceRender ("Evaluation stuck on", pPrint (annee qa)); _ -> id) $
              mb_res) $
  fmap normalise $ case annee qa of
    Question x -> force  deeds h k tg (rename rn x)
    Answer   v -> unwind True deeds h k tg (rn, v)
  where
    tg = annedTag qa
      
    force :: Deeds -> Heap -> Stack -> Tag -> Out Var -> Maybe (Deeds, UnnormalisedState)
    force deeds (Heap h ids) k tg x'
            = do { _ <- lookupValue (Heap h ids) x'; unwind True deeds (Heap h ids) k tg (mkIdentityRenaming [x'], Indirect x') }
      `mplus` do { Concrete in_e <- M.lookup x' h; return (deeds, (Heap (M.delete x' h) ids, Tagged tg (Update x') : k, in_e)) }

lookupValue :: Heap -> Out Var -> Maybe (In AnnedValue)
lookupValue (Heap h _) x' = do
    hb <- M.lookup x' h
    case hb of
      Concrete  (rn, anned_e) -> fmap ((rn,) . annee) $ termToValue anned_e
      Unfolding (rn, anned_v) -> Just (rn, annee anned_v)
      _                       -> Nothing

unwind :: Bool -> Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> Maybe (Deeds, UnnormalisedState)
unwind do_updates deeds h k tg_v in_v = uncons k >>= \(kf, k) -> let deeds' = releaseDeedDescend_ deeds (tag kf) in case tagee kf of
    Apply x2'                 -> apply      deeds'         h k tg_v in_v x2'
    Scrutinise in_alts        -> scrutinise deeds'         h k tg_v in_v in_alts
    PrimApply pop in_vs in_es -> primop     deeds (tag kf) h k tg_v pop in_vs in_v in_es
    Update x' | do_updates    -> update     deeds'         h k tg_v x' in_v
              | otherwise     -> Nothing
  where
    -- When derereferencing an indirection, it is important that the resulting value is not stored anywhere. The reasons are:
    --  1) That would cause allocation to be duplicated if we residualised immediately afterwards, because the value would still be in the heap
    --  2) It would cause a violation of the deeds invariant because *syntax* would be duplicate
    --  3) It feels a bit weird because it might turn phantom stuff into real stuff
    --
    -- Indirections do not change the deeds story much (at all). You have to pay a deed per indirection, which is released
    -- whenever the indirection dies in the process of evaluation (e.g. in the function position of an application). The deeds
    -- that the indirection "points to" are not affected by any of this. The exception is if we *retain* any subcomponent
    -- of the dereferenced thing - in this case we have to be sure to claim some deeds for that subcomponent. For example, if we
    -- dereference to get a lambda in our function application we had better claim deeds for the body.
    dereference :: Heap -> In AnnedValue -> In AnnedValue
    dereference h (rn, Indirect x) | Just (rn', anned_v') <- lookupValue h (safeRename "dereference" rn x) = dereference h (rn', anned_v')
    dereference _ in_v = in_v
    
    apply :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> Out Var -> Maybe (Deeds, UnnormalisedState)
    apply deeds h k tg_v (dereference h -> (rn, Lambda x e_body)) x2' = fmap (\deeds'' -> (deeds'', (h, k, (insertRenaming x x2' rn, e_body)))) $ claimDeed deeds' (annedTag e_body)
      where
        -- You might wonder why I don't just releaseDeedDescend_ the tg_v here rather than releasing it all and
        -- then claiming a little bit back. The answer is that the tg_v might be the tag of an indirection, so I have
        -- no guarantee that releaseDeedDescend_ will leave me with any deeds for the lambda body!
        deeds' = releaseDeedDeep deeds tg_v
    apply _     _ _ _    _                                        _   = Nothing -- Might happen theoretically if we have an unresovable indirection

    scrutinise :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> In [AnnedAlt] -> Maybe (Deeds, UnnormalisedState)
    scrutinise deeds (Heap h ids) k tg_v (rn_v, v)  (rn_alts, alts)
      | Literal l <- v_deref
      , (alt_e, rest):_ <- [((rn_alts, alt_e), rest) | ((LiteralAlt alt_l, alt_e), rest) <- bagContexts alts, alt_l == l] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (Heap h ids, k, alt_e))
      | Data dc xs <- v_deref
      , (alt_e, rest):_ <- [((insertRenamings (alt_xs `zip` map (rename rn_v_deref) xs) rn_alts, alt_e), rest) | ((DataAlt alt_dc alt_xs, alt_e), rest) <- bagContexts alts, alt_dc == dc] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (Heap h ids, k, alt_e))
      | ((mb_alt_x, alt_e), rest):_ <- [((mb_alt_x, alt_e), rest) | ((DefaultAlt mb_alt_x, alt_e), rest) <- bagContexts alts]
      = Just $ case mb_alt_x of
                 Nothing    -> (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (Heap h                                                               ids,  k, (rn_alts,  alt_e)))
                 Just alt_x -> (releaseAltDeeds rest deeds,                        (Heap (M.insert alt_x' (Concrete (rn_v, annedTerm tg_v $ Value v)) h) ids', k, (rn_alts', alt_e)))
                   where (ids', rn_alts', alt_x') = renameBinder ids rn_alts alt_x
                         -- NB: we add the *non-dereferenced* value to the heap in a default branch with variable, because anything else may duplicate allocation
      | otherwise
      = Nothing -- This can legitimately occur, e.g. when supercompiling (if x then (case x of False -> 1) else 2)
      where (rn_v_deref, v_deref) = dereference (Heap h ids) (rn_v, v)

    releaseAltDeeds :: [(a, AnnedTerm)] -> Deeds -> Deeds
    releaseAltDeeds alts deeds = foldl' (\deeds (_, in_e) -> releaseDeedDeep deeds (annedTag in_e)) deeds alts

    primop :: Deeds -> Tag -> Heap -> Stack -> Tag -> PrimOp -> [In (Anned AnnedValue)] -> In AnnedValue -> [In AnnedTerm] -> Maybe (Deeds, UnnormalisedState)
    primop deeds tg_kf h k tg_v2 pop [(rn_v1, anned_v1)] (rn_v2, v2) []
      | (_, Literal (Int l1)) <- dereference h (rn_v1, annee anned_v1)
      , (_, Literal (Int l2)) <- dereference h (rn_v2, v2)
      = Just (releaseDeedDeep (releaseDeedDeep deeds tg_v2) (annedTag anned_v1), (h, k, (emptyRenaming, annedTerm tg_kf (Value (f pop l1 l2)))))
      | otherwise
      = Nothing -- Can occur legitimately if some of the arguments of the primop are just indirections
      where f pop = case pop of Add -> retInt (+); Subtract -> retInt (-);
                                Multiply -> retInt (*); Divide -> retInt div; Modulo -> retInt mod;
                                Equal -> retBool (==); LessThan -> retBool (<); LessThanEqual -> retBool (<=)
            retInt  pop l1 l2 = Literal (Int (pop l1 l2))
            retBool pop l1 l2 = if pop l1 l2 then Data trueDataCon [] else Data falseDataCon []
    primop deeds tg_kf h k tg_v pop in_vs (rn, v) (in_e:in_es) = Just (deeds, (h, Tagged tg_kf (PrimApply pop (in_vs ++ [(rn, annedValue tg_v v)]) in_es) : k, in_e))
    primop _     _     _ _ _    _   _     _       _            = Nothing -- I don't think this can occur legitimately

    update :: Deeds -> Heap -> Stack -> Tag -> Out Var -> In AnnedValue -> Maybe (Deeds, UnnormalisedState)
    update deeds (Heap h ids) k tg_v x' (rn, v) = case claimDeed deeds tg_v of
        Nothing      -> trace (render (text "update-deeds:" <+> pPrint x')) Nothing
        Just deeds'' ->                                                     Just (deeds'', (Heap (M.insert x' (Concrete (rn, annedTerm tg_v (Value v))) h) ids, k, in_e))
          where in_e | dUPLICATE_VALUES_EVALUATOR = (rn,                      annedTerm tg_v (Value v))
                     | otherwise                  = (mkIdentityRenaming [x'], annedTerm tg_v (Value (Indirect x'))) -- FIXME: this is claiming too many deeds in the case that v is a lambda. Ideally we would just reuse the deed gained from stack frame release
