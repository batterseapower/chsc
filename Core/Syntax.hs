{-# LANGUAGE PatternGuards, ViewPatterns, TypeSynonymInstances, FlexibleInstances #-}
module Core.Syntax where

import Name
import Utilities


type Var = Name

type DataCon = String

data PrimOp = Add | Subtract | Multiply | Divide | Modulo | Equal | LessThanEqual
            deriving (Eq, Ord, Show)

data AltCon = DataAlt DataCon [Var] | LiteralAlt Literal | DefaultAlt (Maybe Var)
            deriving (Eq, Show)

data Literal = Int Integer | Char Char
             deriving (Eq, Show)

newtype Term = Term { unTerm :: TermF Term }
             deriving (Eq, Show)
data TaggedTerm = TaggedTerm { unTaggedTerm :: Tagged (TermF TaggedTerm) }
                deriving (Eq, Show)
data TermF term = Var Var | Value (ValueF term) | App term Var | PrimOp PrimOp [term] | Case term [AltF term] | LetRec [(Var, term)] term
                deriving (Eq, Show)

type Alt = AltF Term
type TaggedAlt = AltF TaggedTerm
type AltF term = (AltCon, term)

type Value = ValueF Term
type TaggedValue = ValueF TaggedTerm
data ValueF term = Lambda Var term | Data DataCon [Var] | Literal Literal
                 deriving (Eq, Show)

instance NFData PrimOp

instance NFData AltCon where
    rnf (DataAlt a b) = rnf a `seq` rnf b
    rnf (LiteralAlt a) = rnf a
    rnf (DefaultAlt a) = rnf a

instance NFData Literal where
    rnf (Int a) = rnf a
    rnf (Char a) = rnf a

instance NFData Term where
    rnf (Term a) = rnf a

instance NFData TaggedTerm where
    rnf (TaggedTerm a) = rnf a

instance NFData term => NFData (TermF term) where
    rnf (Var a) = rnf a
    rnf (Value a) = rnf a
    rnf (App a b) = rnf a `seq` rnf b
    rnf (PrimOp a b) = rnf a `seq` rnf b
    rnf (Case a b) = rnf a `seq` rnf b
    rnf (LetRec a b) = rnf a `seq` rnf b

instance NFData term => NFData (ValueF term) where
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

instance Pretty Term where
    pPrintPrec level prec (Term e) = pPrintPrec level prec e

instance Pretty TaggedTerm where
    pPrintPrec level prec (TaggedTerm e) = pPrintPrec level prec e

instance Pretty term => Pretty (TermF term) where
    pPrintPrec level prec e = case e of
        LetRec xes e  -> pPrintPrecLetRec level prec xes e
        Var x         -> pPrintPrec level prec x
        Value v       -> pPrintPrec level prec v
        App e1 x2     -> pPrintPrecApp level prec e1 x2
        PrimOp pop xs -> pPrintPrecPrimOp level prec pop xs
        Case e alts | level == haskellLevel, null alts                              -> pPrintPrecSeq level prec e (text "undefined")
                    | level == haskellLevel, [(DefaultAlt Nothing, e_alt)]  <- alts -> pPrintPrecSeq level prec e e_alt
                    | level == haskellLevel, [(DefaultAlt (Just x), e_alt)] <- alts -> pPrintPrecLetRec level prec [(x, e)] e_alt
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

instance Pretty term => Pretty (ValueF term) where
    pPrintPrec level prec v = case v of
        -- Unfortunately, this nicer pretty-printing doesn't work for general (TermF term):
        --Lambda x e    -> pPrintPrecLam level prec (x:xs) e'
        --  where (xs, e') = collectLambdas e
        Lambda x e    -> pPrintPrecLam level prec [x] e
        Data dc xs    -> pPrintPrecApps level prec (PrettyFunction $ \_ _ -> text dc) xs
        Literal l     -> pPrintPrec level prec l

pPrintPrecLam :: Pretty a => PrettyLevel -> Rational -> [Var] -> a -> Doc
pPrintPrecLam level prec xs e = prettyParen (prec > noPrec) $ text "\\" <> hsep [pPrintPrec level appPrec y | y <- xs] <+> text "->" <+> pPrintPrec level noPrec e

pPrintPrecApps :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> [b] -> Doc
pPrintPrecApps level prec e1 es2 = prettyParen (not (null es2) && prec >= appPrec) $ pPrintPrec level opPrec e1 <+> hsep (map (pPrintPrec level appPrec) es2)


tagTerm :: IdSupply -> Term -> TaggedTerm
tagTerm ids (Term e) = TaggedTerm $ Tagged (hashedId i) $ case e of
    Var x         -> Var x
    Value v       -> Value (tagValue ids' v)
    App e x       -> App (tagTerm ids' e) x
    PrimOp pop es -> PrimOp pop (zipWith tagTerm idss' es)
    Case e alts   -> Case (tagTerm ids' e) (tagAlts (head idss') alts)
    LetRec xes e  -> LetRec (zipWith (\ids'' (x, e) -> (x, tagTerm ids'' e)) idss' xes) (tagTerm ids' e)
  where
    (ids', i) = stepIdSupply ids
    idss' = splitIdSupplyL ids'

tagValue :: IdSupply -> Value -> TaggedValue
tagValue ids v = case v of
    Lambda x e -> Lambda x (tagTerm ids e)
    Data dc xs -> Data dc xs
    Literal l  -> Literal l

tagAlt :: IdSupply -> Alt -> TaggedAlt
tagAlt ids (con, e) = (con, tagTerm ids e)

tagAlts :: IdSupply -> [Alt] -> [TaggedAlt]
tagAlts = zipWith tagAlt . splitIdSupplyL

detagTerm :: TaggedTerm -> Term
detagTerm (TaggedTerm (Tagged _ e)) = case e of
    Var x         -> var x
    Value v       -> value (detagValue v)
    App e x       -> app (detagTerm e) x
    PrimOp pop es -> primOp pop (map detagTerm es)
    Case e alts   -> case_ (detagTerm e) (detagAlts alts)
    LetRec xes e  -> letRec (map (second detagTerm) xes) (detagTerm e)

detagValue :: TaggedValue -> Value
detagValue (Lambda x e) = Lambda x (detagTerm e)
detagValue (Data dc xs) = Data dc xs
detagValue (Literal l)  = Literal l

detagAlts :: [TaggedAlt] -> [Alt]
detagAlts = map (second detagTerm)


isValue :: TermF term -> Bool
isValue (Value _) = True
isValue _         = False

termIsValue :: Term -> Bool
termIsValue = isValue . unTerm

isCheap :: TermF term -> Bool
isCheap (Var _)   = True
isCheap (Value _) = True
isCheap _         = False

termIsCheap :: Term -> Bool
termIsCheap = isCheap . unTerm

taggedTermIsCheap :: TaggedTerm -> Bool
taggedTermIsCheap = isCheap . tagee . unTaggedTerm

letRec :: [(Var, Term)] -> Term -> Term
letRec []  e = e
letRec xes e = Term $ LetRec xes e

var :: Var -> Term
var = Term . Var

value :: Value -> Term
value = Term . Value

literal :: Literal -> Term
literal = value . Literal

lambda :: Var -> Term -> Term
lambda x = value . Lambda x

lambdas :: [Var] -> Term -> Term
lambdas = flip $ foldr lambda

data_ :: DataCon -> [Var] -> Term
data_ dc = value . Data dc

primOp :: PrimOp -> [Term] -> Term
primOp pop es = Term (PrimOp pop es)

app :: Term -> Var -> Term
app e x = Term (App e x)

apps :: Term -> [Var] -> Term
apps = foldl app

varApps :: Var -> [Var] -> Term
varApps h xs = var h `apps` xs

case_ :: Term -> [Alt] -> Term
case_ e = Term . Case e

collectLambdas :: Term -> ([Var], Term)
collectLambdas (Term (Value (Lambda x e))) = first (x:) $ collectLambdas e
collectLambdas e                           = ([], e)

freshFloatVar :: IdSupply -> String -> Term -> (IdSupply, Maybe (Name, Term), Name)
freshFloatVar ids _ (Term (Var x)) = (ids,  Nothing,     x)
freshFloatVar ids s e              = (ids', Just (y, e), y)
  where (ids', y) = freshName ids s

freshFloatVars :: IdSupply -> String -> [Term] -> (IdSupply, [(Name, Term)], [Name])
freshFloatVars ids s es = reassociate $ mapAccumL (\ids -> associate . freshFloatVar ids s) ids es
  where reassociate (ids, unzip -> (mb_floats, xs)) = (ids, catMaybes mb_floats, xs)
        associate (ids, mb_float, x) = (ids, (mb_float, x))