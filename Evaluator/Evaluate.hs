{-# LANGUAGE TupleSections, PatternGuards, ViewPatterns #-}
module Evaluator.Evaluate (normalise, step) where

import Evaluator.Deeds
import Evaluator.FreeVars
import Evaluator.Residualise
import Evaluator.Syntax

import Core.Renaming
import Core.Syntax
import Core.Prelude (trueDataCon, falseDataCon)

import Renaming
import StaticFlags
import Utilities

import qualified Data.Map as M


-- | Non-expansive simplification we can do everywhere safely
--
-- This function only ever returns deeds to the deed pool, but may add them.
normalise :: (Deeds, UnnormalisedState) -> (Deeds, State)
normalise (deeds, state) =
    (\(deeds', state') -> assertRender (hang (text "normalise: deeds lost or gained:") 2 (pPrint state $$ pPrint (deeds, releaseStateDeed 0 state) $$ pPrint state' $$ pPrint (deeds', releaseStateDeed 0 state')))
                                       (noChange (releaseStateDeed deeds state) (releaseStateDeed deeds' state')) $
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
        LetRec xes e      -> normalise (deeds + 1, allocate h k (rn, (xes, e)))
      where tg = annedTag e

    allocate :: Heap -> Stack -> In ([(Var, AnnedTerm)], AnnedTerm) -> UnnormalisedState
    allocate (Heap h ids) k (rn, (xes, e)) = (Heap (h `M.union` M.map Concrete (M.fromList xes')) ids', k, (rn', e))
      where (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes

step :: (Deeds, State) -> Maybe (Deeds, State)
step (deeds, _state@(h, k, (rn, qa))) =
  (\mb_res -> assertRender (hang (text "step: deeds lost or gained:") 2 (pPrintFullState _state))
                           (maybe True (\(deeds', state') -> noChange (releaseStateDeed deeds _state) (releaseStateDeed deeds' state')) mb_res) $
              -- (case mb_res of Nothing -> traceRender ("Evaluation stuck on", pPrint (annee qa)); _ -> id) $
              mb_res) $
  fmap normalise $ case annee qa of
    Question x -> force  deeds h k tg (rename rn x)
    Answer   v -> unwind True deeds h k tg (rn, v)
  where
    tg = annedTag qa
      
    force :: Deeds -> Heap -> Stack -> Tag -> Out Var -> Maybe (Deeds, UnnormalisedState)
    force deeds (Heap h ids) k tg x'
      | Just in_v <- lookupValue (Heap h ids) x'
      = do { (deeds, in_v) <- prepareValue deeds x' in_v; unwind True deeds (Heap h ids) k tg in_v }
      | otherwise
      = do { Concrete in_e <- M.lookup x' h; return (deeds, (Heap (M.delete x' h) ids, Tagged tg (Update x') : k, in_e)) }

prepareValue :: Deeds
             -> Out Var       -- ^ Name to which the value is bound
             -> In AnnedValue -- ^ Bound value, which we have *exactly* 1 deed for already that is not recorded in the Deeds itself
             -> Maybe (Deeds, In AnnedValue) -- Outgoing deeds have that 1 latent deed included in them, and we have claimed deeds for the outgoing value
prepareValue deeds x' in_v@(_, v)
  | dUPLICATE_VALUES_EVALUATOR = fmap (,in_v) $ claimDeeds (deeds + 1) (annedValueSize' v)
  | otherwise                  = return (deeds, (mkIdentityRenaming [x'], Indirect x'))

-- We have not yet claimed deeds for the result of this function
lookupValue :: Heap -> Out Var -> Maybe (In AnnedValue)
lookupValue (Heap h _) x' = do
    hb <- M.lookup x' h
    case hb of
      Concrete  (rn, anned_e) -> fmap ((rn,) . annee) $ termToValue anned_e
      Unfolding (rn, anned_v) -> Just (rn, annee anned_v)
      _                       -> Nothing

unwind :: Bool -> Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> Maybe (Deeds, UnnormalisedState)
unwind do_updates deeds h k tg_v in_v = uncons k >>= \(kf, k) -> case tagee kf of
    Apply x2'                 -> apply      (deeds + 1)          h k      in_v x2'
    Scrutinise in_alts        -> scrutinise (deeds + 1)          h k tg_v in_v in_alts
    PrimApply pop in_vs in_es -> primop     deeds       (tag kf) h k tg_v pop in_vs in_v in_es
    Update x' | do_updates    -> update     deeds                h k tg_v x' in_v
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
    
    apply :: Deeds -> Heap -> Stack -> In AnnedValue -> Out Var -> Maybe (Deeds, UnnormalisedState)
    apply deeds h k in_v@(_, v) x2'
      | (rn, Lambda x e_body) <- dereference h in_v = fmap (,(h, k, (insertRenaming x x2' rn, e_body))) $ claimDeeds (deeds + annedValueSize' v) (annedSize e_body)
      | otherwise                                   = Nothing -- Might happen theoretically if we have an unresovable indirection

    scrutinise :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> In [AnnedAlt] -> Maybe (Deeds, UnnormalisedState)
    scrutinise deeds (Heap h ids) k tg_v (rn_v, v)  (rn_alts, alts)
      | Literal l <- v_deref
      , (alt_e, rest):_ <- [((rn_alts, alt_e), rest) | ((LiteralAlt alt_l, alt_e), rest) <- bagContexts alts, alt_l == l]
      = Just (deeds + annedValueSize' v + annedAltsSize rest, (Heap h ids, k, alt_e))
      | Data dc xs <- v_deref
      , (alt_e, rest):_ <- [((insertRenamings (alt_xs `zip` map (rename rn_v_deref) xs) rn_alts, alt_e), rest) | ((DataAlt alt_dc alt_xs, alt_e), rest) <- bagContexts alts, alt_dc == dc]
      = Just (deeds + annedValueSize' v + annedAltsSize rest, (Heap h ids, k, alt_e))
      | ((mb_alt_x, alt_e), rest):_ <- [((mb_alt_x, alt_e), rest) | ((DefaultAlt mb_alt_x, alt_e), rest) <- bagContexts alts]
      = Just $ case mb_alt_x of
                 Nothing    -> (deeds + annedValueSize' v + annedAltsSize rest, (Heap h                                                               ids,  k, (rn_alts,  alt_e)))
                 Just alt_x -> (deeds +                     annedAltsSize rest, (Heap (M.insert alt_x' (Concrete (rn_v, annedTerm tg_v $ Value v)) h) ids', k, (rn_alts', alt_e)))
                   where (ids', rn_alts', alt_x') = renameBinder ids rn_alts alt_x
                         -- NB: we add the *non-dereferenced* value to the heap in a default branch with variable, because anything else may duplicate allocation
      | otherwise
      = Nothing -- This can legitimately occur, e.g. when supercompiling (if x then (case x of False -> 1) else 2)
      where (rn_v_deref, v_deref) = dereference (Heap h ids) (rn_v, v)

    primop :: Deeds -> Tag -> Heap -> Stack -> Tag -> PrimOp -> [In (Anned AnnedValue)] -> In AnnedValue -> [In AnnedTerm] -> Maybe (Deeds, UnnormalisedState)
    primop deeds tg_kf h k _tg_v2 pop [(rn_v1, anned_v1)] (rn_v2, v2) []
      | (_, Literal (Int l1)) <- dereference h (rn_v1, annee anned_v1)
      , (_, Literal (Int l2)) <- dereference h (rn_v2, v2)
      , let e' = annedTerm tg_kf (Value (f pop l1 l2))
      , Just deeds <- claimDeeds (deeds + annedSize anned_v1 + annedValueSize' v2 + 1) (annedSize e') -- I don't think this can ever fail
      = Just (deeds, (h, k, (emptyRenaming, e')))
      | otherwise
      = Nothing -- Can occur legitimately if some of the arguments of the primop are just indirections to nothing
      where f pop = case pop of Add -> retInt (+); Subtract -> retInt (-);
                                Multiply -> retInt (*); Divide -> retInt div; Modulo -> retInt mod;
                                Equal -> retBool (==); LessThan -> retBool (<); LessThanEqual -> retBool (<=)
            retInt  pop l1 l2 = Literal (Int (pop l1 l2))
            retBool pop l1 l2 = if pop l1 l2 then Data trueDataCon [] else Data falseDataCon []
    primop deeds tg_kf h k tg_v pop in_vs (rn, v) (in_e:in_es) = Just (deeds, (h, Tagged tg_kf (PrimApply pop (in_vs ++ [(rn, annedValue tg_v v)]) in_es) : k, in_e))
    primop _     _     _ _ _    _   _     _       _            = Nothing -- I don't think this can occur legitimately

    update :: Deeds -> Heap -> Stack -> Tag -> Out Var -> In AnnedValue -> Maybe (Deeds, UnnormalisedState)
    update deeds (Heap h ids) k tg_v x' (rn, v) = case prepareValue deeds x' in_v of
        Nothing             -> trace (render (text "update-deeds:" <+> pPrint x')) Nothing
        Just (deeds', in_v) ->                                                     Just (deeds', (Heap (M.insert x' (Concrete (rn, annedTerm tg_v (Value v))) h) ids, k, second (annedTerm tg_v . Value) in_v))
