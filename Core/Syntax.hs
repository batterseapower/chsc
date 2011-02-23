{-# LANGUAGE PatternGuards, ViewPatterns, TypeSynonymInstances, FlexibleInstances, Rank2Types #-}
module Core.Syntax where

import Core.Data (DataCon)

import Name
import Utilities
import StaticFlags


type Var = Name

data PrimOp = Add | Subtract | Multiply | Divide | Modulo | Equal | LessThan | LessThanEqual
            deriving (Eq, Ord, Show)

data AltCon = DataAlt DataCon [Var] | LiteralAlt Literal | DefaultAlt (Maybe Var)
            deriving (Eq, Show)

-- Note [Case wildcards]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- Simon thought that I should use the variable in the DefaultAlt to agressively rewrite occurences of a scrutinised variable.
-- The motivation is that this lets us do more inlining above the case. For example, take this code fragment from foldl':
--
--   let n' = c n y
--   in case n' of wild -> foldl' c n' ys
--
-- If we rewrite, n' becomes linear:
--
--   let n' = c n y
--   in case n' of wild -> foldl c wild ys
--
-- This lets us potentially inline n' directly into the scrutinee position (operationally, this prevent creation of a thunk for n').
-- However, I don't think that this particular form of improving linearity helps the supercompiler. We only want to inline n' in
-- somewhere if it meets some interesting context, with which it can cancel. But if we are creating an update frame for n' at all,
-- it is *probably* because we had no information about what it evaluated to.
--
-- An interesting exception is when n' binds a case expression:
--
--   let n' = case unk of T -> F; F -> T
--   in case (case n' of T -> F; F -> T) of
--        wild -> e[n']
--
-- You might think that we want n' to be linear so we can inline it into the case on it. However, the splitter will save us and produce:
--
--   case unk of
--     T -> let n' = F
--          in case (case n' of T -> F; F -> T) of wild -> e[n']
--     F -> let n' = T
--          in case (case n' of T -> F; F -> T) of wild -> e[n']
--
-- Since we now know the form of n', everything works out nicely.
--
-- Conclusion: I don't think rewriting to use the case wildcard buys us anything at all.

data Literal = Int Integer | Char Char
             deriving (Eq, Show)

type Term = Identity (TermF Identity)
type TaggedTerm = Tagged (TermF Tagged)
type CountedTerm = Counted (TermF Counted)
data TermF ann = Var Var | Value (ValueF ann) | App (ann (TermF ann)) Var | PrimOp PrimOp [ann (TermF ann)] | Case (ann (TermF ann)) [AltF ann] | LetRec [(Var, ann (TermF ann))] (ann (TermF ann))
               deriving (Eq, Show)

type Alt = AltF Identity
type TaggedAlt = AltF Tagged
type CountedAlt = AltF Counted
type AltF ann = (AltCon, ann (TermF ann))

type Value = ValueF Identity
type TaggedValue = ValueF Tagged
type CountedValue = ValueF Counted
data ValueF ann = Indirect Var | Lambda Var (ann (TermF ann)) | Data DataCon [Var] | Literal Literal -- TODO: add PAPs as well? Would avoid duplicating function bodies too eagerly.
                deriving (Eq, Show)

instance NFData PrimOp

instance NFData AltCon where
    rnf (DataAlt a b) = rnf a `seq` rnf b
    rnf (LiteralAlt a) = rnf a
    rnf (DefaultAlt a) = rnf a

instance NFData Literal where
    rnf (Int a) = rnf a
    rnf (Char a) = rnf a

instance NFData1 ann => NFData (TermF ann) where
    rnf (Var a) = rnf a
    rnf (Value a) = rnf a
    rnf (App a b) = rnf a `seq` rnf b
    rnf (PrimOp a b) = rnf a `seq` rnf b
    rnf (Case a b) = rnf a `seq` rnf b
    rnf (LetRec a b) = rnf a `seq` rnf b

instance NFData1 ann => NFData (ValueF ann) where
    rnf (Indirect a) = rnf a
    rnf (Lambda a b) = rnf a `seq` rnf b
    rnf (Data a b) = rnf a `seq` rnf b
    rnf (Literal a) = rnf a

instance Pretty PrimOp where
    pPrint Add           = text "(+)"
    pPrint Subtract      = text "(-)"
    pPrint Multiply      = text "(*)"
    pPrint Divide        = text "div"
    pPrint Modulo        = text "mod"
    pPrint Equal         = text "(==)"
    pPrint LessThan      = text "(<)"
    pPrint LessThanEqual = text "(<=)"

instance Pretty AltCon where
    pPrintPrec level prec altcon = case altcon of
        DataAlt dc xs   -> prettyParen (prec >= appPrec) $ text dc <+> hsep (map (pPrintPrec level appPrec) xs)
        LiteralAlt l    -> pPrint l
        DefaultAlt mb_x -> maybe (text "_") (pPrintPrec level prec) mb_x

instance Pretty Literal where
    pPrintPrec level prec (Int i) | level == haskellLevel = prettyParen (prec >= appPrec) $ pPrintPrec level appPrec i <+> text ":: Int"
                                  | otherwise             = pPrintPrec level prec i
    pPrintPrec _     _    (Char c) = text $ show c

instance Pretty1 ann => Pretty (TermF ann) where
    pPrintPrec level prec e = case e of
        LetRec xes e  -> pPrintPrecLetRec level prec xes e
        Var x         -> pPrintPrec level prec x
        Value v       -> pPrintPrec level prec v
        App e1 x2     -> pPrintPrecApp level prec e1 x2
        PrimOp pop xs -> pPrintPrecPrimOp level prec pop xs
        Case e alts | level == haskellLevel, null alts                              -> pPrintPrecSeq level prec e (text "undefined")
                    | level == haskellLevel, [(DefaultAlt Nothing, e_alt)]  <- alts -> pPrintPrecSeq level prec e e_alt
                    | level == haskellLevel, [(DefaultAlt (Just x), e_alt)] <- alts -> pPrintPrecLetRec level prec [(x, e)] (pPrintPrecSeq level prec x e_alt)
                    | otherwise                                                     -> pPrintPrecCase level prec e alts

pPrintPrecSeq :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> b -> Doc
pPrintPrecSeq level prec e1 e2 = pPrintPrecApp level prec (PrettyFunction $ \level prec -> pPrintPrecApp level prec (name "seq") e1) e2

pPrintPrecApp :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> b -> Doc
pPrintPrecApp level prec e1 e2 = prettyParen (prec >= appPrec) $ pPrintPrec level opPrec e1 <+> pPrintPrec level appPrec e2

pPrintPrecPrimOp :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> [b] -> Doc
pPrintPrecPrimOp level prec pop xs = pPrintPrecApps level prec pop xs

pPrintPrecCase :: (Pretty a, Pretty b, Pretty c) => PrettyLevel -> Rational -> a -> [(b, c)] -> Doc
pPrintPrecCase level prec e alts = prettyParen (prec > noPrec) $ hang (text "case" <+> pPrintPrec level noPrec e <+> text "of") 2 $ vcat (map (pPrintPrecAlt level noPrec) alts)

pPrintPrecAlt :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> (a, b) -> Doc
pPrintPrecAlt level _ (alt_con, alt_e) = hang (pPrintPrec level noPrec alt_con <+> text "->") 2 (pPrintPrec level noPrec alt_e)

pPrintPrecLetRec :: (Pretty a, Pretty b, Pretty c) => PrettyLevel -> Rational -> [(a, b)] -> c -> Doc
pPrintPrecLetRec level prec xes e_body
  | [] <- xes = pPrintPrec level prec e_body
  | otherwise = prettyParen (prec > noPrec) $ hang (if level == haskellLevel then text "let" else text "letrec") 2 (vcat [pPrintPrec level noPrec x <+> text "=" <+> pPrintPrec level noPrec e | (x, e) <- xes]) $$ text "in" <+> pPrintPrec level noPrec e_body

instance Pretty1 ann => Pretty (ValueF ann) where
    pPrintPrec level prec v = case v of
        Indirect x    -> pPrintPrec level prec x
        -- Unfortunately, this nicer pretty-printing doesn't work for general (TermF ann):
        --Lambda x e    -> pPrintPrecLam level prec (x:xs) e'
        --  where (xs, e') = collectLambdas e
        Lambda x e    -> pPrintPrecLam level prec [x] e
        Data dc xs    -> pPrintPrecApps level prec (PrettyFunction $ \_ _ -> text dc) xs
        Literal l     -> pPrintPrec level prec l

pPrintPrecLam :: Pretty a => PrettyLevel -> Rational -> [Var] -> a -> Doc
pPrintPrecLam level prec xs e = prettyParen (prec > noPrec) $ text "\\" <> hsep [pPrintPrec level appPrec y | y <- xs] <+> text "->" <+> pPrintPrec level noPrec e

pPrintPrecApps :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> [b] -> Doc
pPrintPrecApps level prec e1 es2 = prettyParen (not (null es2) && prec >= appPrec) $ pPrintPrec level opPrec e1 <+> hsep (map (pPrintPrec level appPrec) es2)


altConBinders :: AltCon -> [Var]
altConBinders (DataAlt _ xs)    = xs
altConBinders (LiteralAlt _)    = []
altConBinders (DefaultAlt mb_x) = maybeToList mb_x

termToValue :: Copointed ann => ann (TermF ann) -> Maybe (ann (ValueF ann))
termToValue e = case extract e of Value v -> Just (fmap (const v) e); _ -> Nothing

termIsValue :: Copointed ann => ann (TermF ann) -> Bool
termIsValue = isValue . extract

isValue :: TermF ann -> Bool
isValue (Value _) = True
isValue _         = False

termIsCheap :: Copointed ann => ann (TermF ann) -> Bool
termIsCheap = isCheap . extract

isCheap :: Copointed ann => TermF ann -> Bool
isCheap _ | cALL_BY_NAME = True -- A cunning hack. I think this is all that should be required...
isCheap (Var _)     = True
isCheap (Value _)   = True
isCheap (Case e []) = isCheap (extract e) -- NB: important for pushing down let-bound applications of ``error''
isCheap _           = False

termToVar :: Copointed ann => ann (TermF ann) -> Maybe Var
termToVar e = case extract e of
    Value (Indirect x) -> Just x
    Var x              -> Just x
    _                  -> Nothing


class Symantics ann where
    var    :: Var -> ann (TermF ann)
    value  :: ValueF ann -> ann (TermF ann)
    app    :: ann (TermF ann) -> Var -> ann (TermF ann)
    primOp :: PrimOp -> [ann (TermF ann)] -> ann (TermF ann)
    case_  :: ann (TermF ann) -> [AltF ann] -> ann (TermF ann)
    letRec :: [(Var, ann (TermF ann))] -> ann (TermF ann) -> ann (TermF ann)

instance Symantics Identity where
    var = I . Var
    value = I . Value
    app e = I . App e
    primOp pop es = I (PrimOp pop es)
    case_ e = I . Case e
    letRec xes e = I $ LetRec xes e


reify :: (forall ann. Symantics ann => ann (TermF ann)) -> Term
reify x = x

reflect :: Term -> (forall ann. Symantics ann => ann (TermF ann))
reflect (I e) = case e of
    Var x              -> var x
    Value (Indirect x) -> value (Indirect x)
    Value (Lambda x e) -> value (Lambda x (reflect e))
    Value (Data dc xs) -> value (Data dc xs)
    Value (Literal l)  -> value (Literal l)
    App e1 x2          -> app (reflect e1) x2
    PrimOp pop es      -> primOp pop (map reflect es)
    Case e alts        -> case_ (reflect e) (map (second reflect) alts)
    LetRec xes e       -> letRec (map (second reflect) xes) (reflect e)


literal :: Symantics ann => Literal -> ann (TermF ann)
literal = value . Literal

lambda :: Symantics ann => Var -> ann (TermF ann) -> ann (TermF ann)
lambda x = value . Lambda x

lambdas :: Symantics ann => [Var] -> ann (TermF ann) -> ann (TermF ann)
lambdas = flip $ foldr lambda

data_ :: Symantics ann => DataCon -> [Var] -> ann (TermF ann)
data_ dc = value . Data dc

apps :: Symantics ann => ann (TermF ann) -> [Var] -> ann (TermF ann)
apps = foldl app

varApps :: Symantics ann => Var -> [Var] -> ann (TermF ann)
varApps h xs = var h `apps` xs

letRecSmart :: Symantics ann => [(Var, ann (TermF ann))] -> ann (TermF ann) -> ann (TermF ann)
letRecSmart []  = id
letRecSmart xes = letRec xes

strictLet :: Symantics ann => Var -> ann (TermF ann) -> ann (TermF ann) -> ann (TermF ann)
strictLet x e1 e2 = case_ e1 [(DefaultAlt (Just x), e2)]

collectLambdas :: Term -> ([Var], Term)
collectLambdas (I (Value (Lambda x e))) = first (x:) $ collectLambdas e
collectLambdas e                        = ([], e)

freshFloatVar :: IdSupply -> String -> Term -> (IdSupply, Maybe (Name, Term), Name)
freshFloatVar ids _ (I (Var x)) = (ids,  Nothing,     x)
freshFloatVar ids s e           = (ids', Just (y, e), y)
  where (ids', y) = freshName ids s

freshFloatVars :: IdSupply -> String -> [Term] -> (IdSupply, [(Name, Term)], [Name])
freshFloatVars ids s es = reassociate $ mapAccumL (\ids -> associate . freshFloatVar ids s) ids es
  where reassociate (ids, unzip -> (mb_floats, xs)) = (ids, catMaybes mb_floats, xs)
        associate (ids, mb_float, x) = (ids, (mb_float, x))