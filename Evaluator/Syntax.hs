{-# LANGUAGE TypeOperators #-}
module Evaluator.Syntax where

import Size.Deeds

import Core.FreeVars
import Core.Renaming
import Core.Syntax
import Core.Tag

import Renaming
import Utilities

import qualified Data.Map as M


type Anned = Tagged :.: FVed
type AnnedTerm = Anned (TermF Anned)
type AnnedValue = ValueF Anned
type AnnedAlt = AltF Anned

annee :: Anned a -> a
annee = fvee . tagee . unComp

annedFreeVars :: Anned a -> FreeVars
annedFreeVars = freeVars . tagee . unComp

annedTags :: Anned a -> [Tag]
annedTags = tags . unComp


annedVarFreeVars' = taggedFVedVarFreeVars'
annedTermFreeVars = taggedFVedTermFreeVars
annedTermFreeVars' = taggedFVedTermFreeVars'
annedValueFreeVars = taggedFVedValueFreeVars
annedValueFreeVars' = taggedFVedValueFreeVars'
annedAltsFreeVars = taggedFVedAltsFreeVars

renameAnnedVar = renameTaggedFVedVar
renameAnnedTerm = renameTaggedFVedTerm :: IdSupply -> Renaming -> AnnedTerm -> AnnedTerm
renameAnnedValue = renameTaggedFVedValue
renameAnnedValue' = renameTaggedFVedValue'
renameAnnedAlts = renameTaggedFVedAlts

detagAnnedVar = taggedFVedVarToFVedVar
detagAnnedTerm = taggedFVedTermToFVedTerm
detagAnnedValue = taggedFVedValueToFVedValue
detagAnnedValue' = taggedFVedValue'ToFVedValue'
detagAnnedAlts = taggedFVedAltsToFVedAlts


annedVar :: [Tag] -> Var -> Anned Var
annedVar   tgs x = Comp (Tagged tgs (FVed (annedVarFreeVars' x)  x))

annedTerm :: [Tag] -> TermF Anned -> AnnedTerm
annedTerm  tgs e = Comp (Tagged tgs (FVed (annedTermFreeVars' e)  e))

annedValue :: [Tag] -> ValueF Anned -> Anned AnnedValue
annedValue tgs v = Comp (Tagged tgs (FVed (annedValueFreeVars' v) v))


toAnnedTerm :: Term -> AnnedTerm
toAnnedTerm = tagFVedTerm . reflect


type State = (Heap, Stack, In AnnedTerm)

type PureHeap = M.Map (Out Var) (In AnnedTerm)
data Heap = Heap PureHeap IdSupply
          deriving (Show)

instance NFData Heap where
    rnf (Heap a b) = rnf a `seq` rnf b

type Stack = [StackFrame]
data StackFrame = Apply (Out (Anned Var))
                | Scrutinise (In [AnnedAlt])
                | PrimApply PrimOp [In (Anned AnnedValue)] [In AnnedTerm]
                | Update (Out (Anned Var))
                deriving (Show)

instance NFData StackFrame where
    rnf (Apply a)         = rnf a
    rnf (Scrutinise a)    = rnf a
    rnf (PrimApply a b c) = rnf a `seq` rnf b `seq` rnf c
    rnf (Update a)        = rnf a

instance Pretty StackFrame where
    pPrintPrec level prec kf = case kf of
        Apply x'                  -> pPrintPrecApp level prec (text "[_]") x'
        Scrutinise in_alts        -> pPrintPrecCase level prec (text "[_]") (renameIn renameAnnedAlts prettyIdSupply in_alts)
        PrimApply pop in_vs in_es -> pPrintPrecPrimOp level prec pop (map SomePretty in_vs ++ map SomePretty in_es)
        Update x'                 -> pPrintPrecApp level prec (text "update") x'


stackFrameTags :: StackFrame -> [Tag]
stackFrameTags kf = case kf of
    Apply x'                -> annedTags x'
    Scrutinise in_alts      -> concatMap (annedTags . snd) (snd in_alts)
    PrimApply _ in_vs in_es -> concatMap (annedTags . snd) in_vs ++ concatMap (annedTags . snd) in_es
    Update x'               -> annedTags x'

releaseStateDeed :: Deeds -> State -> Deeds
releaseStateDeed deeds (Heap h _, k, (_, e))
  = foldl' (\deeds kf -> foldl' releaseDeedDeep deeds (stackFrameTags kf))
           (foldl' (\deeds (_, e) -> foldl' releaseDeedDeep deeds (annedTags e))
                   (foldl' releaseDeedDeep deeds (annedTags e))
                   (M.elems h))
           k
