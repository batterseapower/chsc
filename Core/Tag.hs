{-# LANGUAGE RankNTypes #-}
module Core.Tag where

import Utilities

import Core.FreeVars
import Core.Syntax


tagTerm :: Term -> TaggedTerm
tagTerm = mkTag (\i f (I e) -> Tagged (hashedId i) (f e))

tagFVedTerm :: FVedTerm -> TaggedFVedTerm
tagFVedTerm = mkTag (\i f (FVed fvs e) -> Comp (Tagged (hashedId i) (FVed fvs (f e))))


{-# INLINE mkTag #-}
mkTag :: (forall a b. Id -> (a -> b) -> ann a -> ann' b)
      -> ann (TermF ann) -> ann' (TermF ann')
mkTag rec = term tagIdSupply
  where
    var ids = rec (idFromSupply ids) var'
    var' x = x
    
    term ids = rec i (term' ids')
      where (ids', i) = stepIdSupply ids
    term' ids e = case e of
        Var x         -> Var x
        Value x v     -> Value x (value ids v)
        App e x       -> App (term ids0' e) (var ids1' x)
          where (ids0', ids1') = splitIdSupply ids
        PrimOp pop es -> PrimOp pop (zipWith term idss' es)
          where idss' = splitIdSupplyL ids
        Case e alts   -> Case (term ids0' e) (alternatives ids1' alts)
          where (ids0', ids1') = splitIdSupply ids
        LetRec xes e  -> LetRec (zipWith (\ids'' (x, e) -> (x, term ids'' e)) idss' xes) (term ids1' e)
          where (ids0', ids1') = splitIdSupply ids
                idss' = splitIdSupplyL ids0'

    value ids v = case v of
        Lambda x e -> Lambda x (term ids e)
        Data dc xs -> Data dc xs
        Literal l  -> Literal l

    alternatives = zipWith alternative . splitIdSupplyL
    
    alternative ids (con, e) = (con, term ids e)


(taggedVarToVar,         taggedTermToTerm,         taggedAltsToAlts,         taggedValueToValue,         taggedValue'ToValue')         = mkDetag (\f e -> I (f (tagee e)))
(fVedVarToVar,           fVedTermToTerm,           fVedAltsToAlts,           fVedValueToValue,           fVedValue'ToValue')           = mkDetag (\f e -> I (f (fvee e)))
(taggedFVedVarToVar,     taggedFVedTermToTerm,     taggedFVedAltsToAlts,     taggedFVedValueToValue,     taggedFVedValue'ToValue')     = mkDetag (\f e -> I (f (fvee (tagee (unComp e)))))
(taggedFVedVarToFVedVar, taggedFVedTermToFVedTerm, taggedFVedAltsToFVedAlts, taggedFVedValueToFVedValue, taggedFVedValue'ToFVedValue') = mkDetag (\f e -> FVed (freeVars (tagee (unComp e))) (f (fvee (tagee (unComp e)))))


{-# INLINE mkDetag #-}
mkDetag :: (forall a b. (a -> b) -> ann a -> ann' b)
        -> (ann Var          -> ann' Var,
            ann (TermF ann)  -> ann' (TermF ann'),
            [AltF ann]       -> [AltF ann'],
            ann (ValueF ann) -> ann' (ValueF ann'),
            ValueF ann       -> ValueF ann')
mkDetag rec = (var, term, alternatives, value, value')
  where
    var = rec var'
    var' x = x
    
    term = rec term'
    term' e = case e of
        Var x         -> Var x
        Value x v     -> Value x (value' v)
        App e x       -> App (term e) (var x)
        PrimOp pop es -> PrimOp pop (map term es)
        Case e alts   -> Case (term e) (alternatives alts)
        LetRec xes e  -> LetRec (map (second term) xes) (term e)

    value = rec value'
    value' (Lambda x e) = Lambda x (term e)
    value' (Data dc xs) = Data dc xs
    value' (Literal l)  = Literal l

    alternatives = map (second term)
