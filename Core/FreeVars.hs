{-# LANGUAGE Rank2Types, TypeOperators, FlexibleInstances, TypeSynonymInstances, DeriveFunctor, DeriveFoldable #-}
module Core.FreeVars where

import Core.Syntax

import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.Set as S
import qualified Data.Map as M


type BoundVars = S.Set Var


type FreeVarsF ann = M.Map Var [ann ()]
type FreeVars = FreeVarsF Tagged

emptyFreeVars :: FreeVarsF ann
emptyFreeVars = M.empty

isFreeVar :: Var -> FreeVarsF ann -> Bool
isFreeVar = M.member

unionFreeVars :: FreeVarsF ann -> FreeVarsF ann -> FreeVarsF ann
unionFreeVars = M.unionWith (++)

unionsFreeVars :: [FreeVarsF ann] -> FreeVarsF ann
unionsFreeVars = M.unionsWith (++)

singletonFreeVar :: Copointed ann => ann Var -> FreeVarsF ann
singletonFreeVar x = M.singleton (extract x) [fmap (const ()) x]


(termVarFreeVars,       termFreeVars,           termFreeVars',           altsFreeVars,           valueFreeVars,           valueFreeVars')           = mkFreeVars id                                              (\f (I e) -> f e)
(fvedTermVarFreeVars,   fvedTermFreeVars,       fvedTermFreeVars',       fvedAltsFreeVars,       fvedValueFreeVars,       fvedValueFreeVars')       = mkFreeVars (\(FVed _ e) -> I e)                            (\_ (FVed fvs _) -> fvs)
(taggedTermVarFreeVars, taggedTermFreeVars,     taggedTermFreeVars',     taggedAltsFreeVars,     taggedValueFreeVars,     taggedValueFreeVars')     = mkFreeVars id                                              (\f (Tagged _ e) -> f e)
(taggedFVedVarFreeVars, taggedFVedTermFreeVars, taggedFVedTermFreeVars', taggedFVedAltsFreeVars, taggedFVedValueFreeVars, taggedFVedValueFreeVars') = mkFreeVars (\(Comp (Tagged tg (FVed _ e))) -> Tagged tg e) (\_ (Comp (Tagged _ (FVed fvs _))) -> fvs)

{-# INLINE mkFreeVars #-}
mkFreeVars :: Copointed ann
           => (forall a. ann a -> ann' a)
           -> (forall a. (a -> FreeVarsF ann') -> ann a -> FreeVarsF ann')
           -> (ann Var          -> FreeVarsF ann',
               ann (TermF ann)  -> FreeVarsF ann',
               TermF ann        -> FreeVarsF ann',
               [AltF ann]       -> FreeVarsF ann',
               ann (ValueF ann) -> FreeVarsF ann',
               ValueF ann       -> FreeVarsF ann')
mkFreeVars forget rec = (var, term, term', alternatives, value, value')
  where
    var x = fmap (map forget) $ singletonFreeVar x
    
    term = rec term'
    term' (Var x)        = var x
    term' (Value v)      = value' v
    term' (App e x)      = term e `unionFreeVars` var x
    term' (PrimOp _ es)  = unionsFreeVars $ map term es
    term' (Case e alts)  = term e `unionFreeVars` alternatives alts
    term' (LetRec xes e) = deleteListMap xs $ unionsFreeVars (map term es) `unionFreeVars` term e
      where (xs, es) = unzip xes
    
    value = rec value'
    value' (Lambda x e) = M.delete x $ term e
    value' (Data _ xs)  = unionsFreeVars $ map var xs
    value' (Literal _)  = emptyFreeVars
    
    alternatives = unionsFreeVars . map alternative
    
    alternative (altcon, e) = altConFreeVars altcon $ term e

annFreeVars :: Copointed ann
            => SyntaxHom ann (ann :.: FVedF ann)
annFreeVars = hom
  where hom = mkSyntaxHom (lift varFVs id) (lift termFVs (termHom' hom)) (lift valueFVs (valueHom' hom))
        
        lift :: Functor ann => (ann a -> FreeVarsF ann) -> (a -> b) -> ann a -> (ann :.: FVedF ann) b
        lift fvs inside anned_x = Comp $ fmap (\x -> FVed (fvs anned_x) (inside x)) anned_x
  
        (varFVs, termFVs, _termFVs', _alternativesFVs, valueFVs, _valueFVs') = mkFreeVars id (\f -> f . extract)

altConOpenFreeVars :: AltCon -> (BoundVars, FreeVarsF ann) -> (BoundVars, FreeVarsF ann)
altConOpenFreeVars (DataAlt _ xs)    (bvs, fvs) = (bvs `S.union` S.fromList xs, fvs)
altConOpenFreeVars (LiteralAlt _)    (bvs, fvs) = (bvs, fvs)
altConOpenFreeVars (DefaultAlt mb_x) (bvs, fvs) = (maybe id S.insert mb_x bvs, fvs)

altConFreeVars :: AltCon -> FreeVarsF ann -> FreeVarsF ann
altConFreeVars (DataAlt _ xs)    = deleteListMap xs
altConFreeVars (LiteralAlt _)    = id
altConFreeVars (DefaultAlt mb_x) = maybe id M.delete mb_x


data FVedF ann a = FVed { freeVars :: !(FreeVarsF ann), fvee :: !a }
            deriving (Functor, Foldable.Foldable)

instance Functor ann => Copointed (FVedF ann) where
    extract = fvee

instance Show1 ann => Show1 (FVedF ann) where
    showsPrec1 prec (FVed fvs x) = showParen (prec >= appPrec) (showString "FVed" . showsPrec appPrec fvs . showsPrec appPrec x)

instance Eq1 ann => Eq1 (FVedF ann) where
    eq1 (FVed fvs1 x1) (FVed fvs2 x2) = fvs1 == fvs2 && x1 == x2

instance Ord1 ann => Ord1 (FVedF ann) where
    compare1 (FVed fvs1 x1) (FVed fvs2 x2) = (x1, fvs1) `compare` (x2, fvs2)

instance NFData1 ann => NFData1 (FVedF ann) where
    rnf1 (FVed a b) = rnf a `seq` rnf b

instance Pretty1 ann => Pretty1 (FVedF ann) where
    pPrintPrec1 level prec (FVed _ x) = pPrintPrec level prec x


type FVed = FVedF Identity
type FVedTerm = FVed (TermF FVed)
type FVedAlt = AltF FVed
type FVedValue = ValueF FVed


instance Symantics FVed where
    var = fvedTerm . Var . fvedVar
    value = fvedTerm . Value
    app e = fvedTerm . App e . fvedVar
    primOp pop = fvedTerm . PrimOp pop
    case_ e = fvedTerm . Case e
    letRec xes = fvedTerm . LetRec xes
    
    lambdaV = Lambda
    dataV dc = Data dc . map fvedVar
    literalV = Literal

fvedVar :: Var -> FVed Var
fvedVar x = FVed (termVarFreeVars (I x)) x

fvedTermFreeVars' :: TermF FVed -> FreeVarsF Identity

fvedTerm :: TermF FVed -> FVedTerm
fvedTerm e = FVed (fvedTermFreeVars' e) e


type TaggedFVed = Tagged :.: FVedF Tagged
type TaggedFVedTerm = TaggedFVed (TermF TaggedFVed)
type TaggedFVedAlt = AltF TaggedFVed
type TaggedFVedValue = ValueF TaggedFVed
