{-# LANGUAGE PatternGuards, TupleSections, ViewPatterns #-}
module Core.Parser (parse) where

import Core.Syntax
import Core.Prelude

import Name hiding (freshName)
import qualified Name
import StaticFlags
import Utilities

import qualified Data.Map as M

import qualified Language.Haskell.Exts as LHE
import Language.Preprocessor.Cpphs

import System.Directory
import System.FilePath (replaceExtension)


parse :: FilePath -> IO (String, [(Var, Term)])
parse path = do
    -- Read and pre-process .core file
    contents <- readFile path >>= cpp
    unless qUIET $ putStrLn contents
    
    -- Read and pre-process corresponding .hs file (if any)
    let wrapper_path = replaceExtension path ".hs"
    has_wrapper <- doesFileExist wrapper_path
    wrapper <- if has_wrapper then readFile wrapper_path >>= cpp else return ""
    
    -- Return parsed .core file
    return (wrapper, moduleCore . LHE.fromParseResult . LHE.parseFileContentsWithMode (LHE.defaultParseMode { LHE.parseFilename = path, LHE.extensions = [LHE.CPP, LHE.MagicHash] }) $ contents)
  where cpp = runCpphs (defaultCpphsOptions { boolopts = (boolopts defaultCpphsOptions) { locations = False }, defines = ("SUPERCOMPILE", "1") : defines defaultCpphsOptions }) path


data ParseState = ParseState {
    ids :: IdSupply,
    dcWrappers :: M.Map DataCon Var,
    intWrappers :: M.Map Integer Var,
    charWrappers :: M.Map Char Var,
    primWrappers :: M.Map PrimOp Var
  }

initParseState :: ParseState
initParseState = ParseState {
    ids = parseIdSupply,
    dcWrappers = M.empty,
    intWrappers = M.empty,
    charWrappers = M.empty,
    primWrappers = M.empty
  }

buildWrappers :: ParseState -> [(Var, Term)]
buildWrappers ps
  = [ (f, lambdas xs $ data_ dc xs)
    | (dc, f) <- M.toList (dcWrappers ps)
    , let arity = dataConArity dc; xs = map (\i -> name $ 'x' : show i) [1..arity] ] ++
    [ (f, int i)
    | (i, f) <- M.toList (intWrappers ps) ] ++
    [ (f, char c)
    | (c, f) <- M.toList (charWrappers ps) ] ++
    [ (f, lam (name "x1") $ lam (name "x2") $ primOp pop [var (name "x1"), var (name "x2")])
    | (pop, f) <- M.toList (primWrappers ps) ] ++
    [ (name "error", lam (name "msg") $ case_ (var (name "prelude_error") `app` name "msg") []) ]
  where
    dataConArity :: String -> Int
    dataConArity "()"      = 0
    dataConArity "(,)"     = 2
    dataConArity "(,,)"    = 3
    dataConArity "(,,,)"   = 4
    dataConArity "[]"      = 0
    dataConArity "(:)"     = 2
    dataConArity "Left"    = 1
    dataConArity "Right"   = 1
    dataConArity "True"    = 0
    dataConArity "False"   = 0
    dataConArity "Just"    = 1
    dataConArity "Nothing" = 0
    dataConArity "MkU"     = 1 -- GHCBug
    dataConArity "Z"       = 0 -- Exp3_8
    dataConArity "S"       = 1 -- Exp3_8
    dataConArity "Leaf"    = 1 -- SumTree
    dataConArity "Branch"  = 2 -- SumTree
    dataConArity "Empty"   = 0 -- ZipTreeMaps
    dataConArity "Node"    = 3 -- ZipTreeMaps
    dataConArity "Wheel1"  = 2 -- Wheel-Sieve1
    dataConArity "Wheel2"  = 3 -- Wheel-Sieve2
    dataConArity "A"       = 0 -- KMP
    dataConArity "B"       = 0 -- KMP
    dataConArity "H"       = 0 -- Paraffins
    dataConArity "C"       = 3 -- Paraffins
    dataConArity "BCP"     = 2 -- Paraffins
    dataConArity "CCP"     = 4 -- Paraffins
    dataConArity s = panic "dataConArity" (text s)

newtype ParseM a = ParseM { unParseM :: ParseState -> (ParseState, a) }

instance Functor ParseM where
    fmap = liftM

instance Monad ParseM where
    return x = ParseM $ \s -> (s, x)
    mx >>= fxmy = ParseM $ \s -> case unParseM mx s of (s, x) -> unParseM (fxmy x) s

freshName :: String -> ParseM Name
freshName n = ParseM $ \s -> let (ids', x) = Name.freshName (ids s) n in (s { ids = ids' }, x)

freshFloatName :: String -> Term -> ParseM (Maybe (Var, Term), Name)
freshFloatName _ (I (Var x)) = return (Nothing, x)
freshFloatName n e           = freshName n >>= \x -> return (Just (x, e), x)

nameIt :: Term -> (Var -> ParseM Term) -> ParseM Term
nameIt e f = freshFloatName "a" e >>= \(mb_float, x) -> fmap (bind (maybeToList mb_float)) $ f x

nameThem :: [Term] -> ([Var] -> ParseM Term) -> ParseM Term
nameThem es f = mapM (freshFloatName "a") es >>= \(unzip -> (mb_es, xs)) -> fmap (bind (catMaybes mb_es)) $ f xs

list :: [Term] -> ParseM Term
list es = nameThem es $ \es_xs -> replicateM (length es) (freshName "list") >>= \cons_xs -> return $ uncurry bind $ foldr (\(cons_x, e_x) (floats, tl) -> ((cons_x, tl) : floats, cons e_x cons_x)) ([], nil) (cons_xs `zip` es_xs)

appE :: Term -> Term -> ParseM Term
appE e1 e2 = e2 `nameIt` \x2 -> return (e1 `app` x2)

dataConWrapper :: DataCon -> ParseM Var
dataConWrapper = grabWrapper dcWrappers (\s x -> s { dcWrappers = x })

intWrapper :: Integer -> ParseM Var
intWrapper = grabWrapper intWrappers (\s x -> s { intWrappers = x })

charWrapper :: Char -> ParseM Var
charWrapper = grabWrapper charWrappers (\s x -> s { charWrappers = x })

primWrapper :: PrimOp -> ParseM Var
primWrapper = grabWrapper primWrappers (\s x -> s { primWrappers = x })

grabWrapper :: Ord a
            => (ParseState -> M.Map a Var) -> (ParseState -> M.Map a Var -> ParseState)
            -> a -> ParseM Var
grabWrapper get set what = do
    mb_x <- ParseM $ \s -> (s, M.lookup what (get s))
    case mb_x of Just x -> return x
                 Nothing -> freshName "wrap" >>= \x -> ParseM $ \s -> (set s (M.insert what x (get s)), x)

runParseM :: ParseM a -> ([(Var, Term)], a)
runParseM = first buildWrappers . flip unParseM initParseState


moduleCore :: LHE.Module -> [(Var, Term)]
moduleCore (LHE.Module _loc _name _ops _warntxt _mbexports _imports decls) = wrap_xes ++ xes
  where (wrap_xes, xes) = runParseM $ declsCore decls


declsCore :: [LHE.Decl] -> ParseM [(Name, Term)]
declsCore = fmap concat . mapM declCore

declCore :: LHE.Decl -> ParseM [(Name, Term)]
declCore (LHE.FunBind [LHE.Match _loc n pats _mb_type@Nothing (LHE.UnGuardedRhs e) _binds@(LHE.BDecls where_decls)]) = do
    let x = name (nameString n)
    (ys, _bound_ns, build) <- patCores pats
    xes <- declsCore where_decls
    e <- expCore e
    return [(x, lambdas ys $ build $ bind xes e)]
declCore (LHE.PatBind _loc pat _mb_ty@Nothing (LHE.UnGuardedRhs e) _binds@(LHE.BDecls where_decls)) = do
    (x, bound_ns, build) <- patCore pat
    xes <- declsCore where_decls
    e <- expCore e
    return $ (x, bind xes e) : [(n, build (var n)) | n <- bound_ns, n /= x]
declCore d = panic "declCore" (text $ show d)

expCore :: LHE.Exp -> ParseM Term
expCore (LHE.Var qname) = qNameCore qname
expCore (LHE.Con qname) = fmap var $ dataConWrapper $ qNameDataCon qname
expCore (LHE.Lit lit) = literalCore lit
expCore (LHE.NegApp e) = expCore $ LHE.App (LHE.Var (LHE.UnQual (LHE.Ident "negate"))) e
expCore (LHE.App e1 e2) = expCore e1 >>= \e1 -> expCore e2 >>= appE e1
expCore (LHE.InfixApp e1 eop e2) = expCore e1 >>= \e1 -> e1 `nameIt` \x1 -> expCore e2 >>= \e2 -> e2 `nameIt` \x2 -> qopCore eop >>= \eop -> return $ apps eop [x1, x2]
expCore (LHE.Let (LHE.BDecls binds) e) = do
    xes <- declsCore binds
    fmap (bind xes) $ expCore e
expCore (LHE.If e1 e2 e3) = expCore e1 >>= \e1 -> liftM2 (if_ e1) (expCore e2) (expCore e3)
expCore (LHE.Case e alts) = expCore e >>= \e -> fmap (case_ e) (mapM altCore alts)
expCore (LHE.Tuple es) = mapM expCore es >>= flip nameThem (return . tuple)
expCore (LHE.Paren e) = expCore e
expCore (LHE.List es) = mapM expCore es >>= list
expCore (LHE.Lambda _ ps e) = patCores ps >>= \(xs, _bound_xs, build) -> expCore e >>= \e -> return $ lambdas xs $ build e
expCore (LHE.LeftSection e1 eop) = expCore e1 >>= \e1 -> e1 `nameIt` \x1 -> qopCore eop >>= \eop -> return (eop `app` x1)
expCore (LHE.RightSection eop e2) = expCore e2 >>= \e2 -> e2 `nameIt` \x2 -> qopCore eop >>= \eop -> eop `nameIt` \xop -> freshName "rsect" >>= \x1 -> return $ lambda x1 $ (var xop `app` x1) `app` x2  -- NB: careful about sharing!
expCore (LHE.EnumFromTo e1 e2) = expCore $ LHE.Var (LHE.UnQual (LHE.Ident "enumFromTo")) `LHE.App` e1 `LHE.App` e2
expCore (LHE.EnumFromThen e1 e2) = expCore $ LHE.Var (LHE.UnQual (LHE.Ident "enumFromThen")) `LHE.App` e1 `LHE.App` e2
expCore (LHE.EnumFromThenTo e1 e2 e3) = expCore $ LHE.Var (LHE.UnQual (LHE.Ident "enumFromThenTo")) `LHE.App` e1 `LHE.App` e2 `LHE.App` e3
expCore (LHE.ListComp e quals) = listCompCore e [case qual of LHE.QualStmt stmt -> stmt | qual <- quals]
expCore e = panic "expCore" (text $ show e)

qopCore :: LHE.QOp -> ParseM Term
qopCore (LHE.QVarOp qn) = qNameCore qn
qopCore (LHE.QConOp qn) = qNameCore qn

literalCore :: LHE.Literal -> ParseM Term
literalCore (LHE.Int i) = fmap var $ intWrapper i
literalCore (LHE.Char c) = fmap var $ charWrapper c
literalCore (LHE.String s) = mapM (literalCore . LHE.Char) s >>= list

altCore :: LHE.Alt -> ParseM Alt
altCore (LHE.Alt _loc pat (LHE.UnGuardedAlt e) (LHE.BDecls binds)) = do
    (altcon, build) <- altPatCore pat
    xes <- declsCore binds
    e <- expCore e
    return (altcon, build (bind xes e))

-- | For irrefutible pattern matches a single level deep, where we need to make a choice based on the outer constructor *only*:
altPatCore :: LHE.Pat -> ParseM (AltCon, Term -> Term)
altPatCore (LHE.PApp qname pats)           = liftM (dataAlt (qNameDataCon qname)) (patCores pats)
altPatCore (LHE.PInfixApp pat1 qname pat2) = liftM (dataAlt (qNameDataCon qname)) (patCores [pat1, pat2])
altPatCore (LHE.PTuple [pat1, pat2])       = liftM (dataAlt pairDataCon) (patCores [pat1, pat2])
altPatCore (LHE.PParen pat)                = altPatCore pat
altPatCore (LHE.PList [])                  = return $ dataAlt nilDataCon ([], [], id)
altPatCore (LHE.PLit (LHE.Int i))          = return (LiteralAlt (Int i), id)
altPatCore (LHE.PLit (LHE.Char c))         = return (LiteralAlt (Char c), id)
altPatCore LHE.PWildCard                   = return (DefaultAlt Nothing, id)
altPatCore p = panic "altPatCore" (text $ show p)

dataAlt :: DataCon -> ([Var], [Var], Term -> Term) -> (AltCon, Term -> Term)
dataAlt dcon (names, _bound_ns, build) = (DataAlt dcon names, build)

listCompCore :: LHE.Exp -> [LHE.Stmt] -> ParseM Term
listCompCore e_inner stmts = go stmts
  where
    go [] = expCore e_inner >>= \e_inner -> list [e_inner]
    go (stmt:stmts) = case stmt of
        -- concatMap (\pat -> [[go stmts]]) e
        LHE.Generator _loc pat e -> do
            (x, _bound_xs, build) <- patCore pat
            arg1 <- liftM (lambda x . build) (go stmts)
            arg2 <- expCore e
            var (name "concatMap") `appE` arg1 >>= (`appE` arg2)
        -- if e then [[go stmts]] else []
        LHE.Qualifier e -> liftM3 if_ (expCore e) (go stmts) (list [])
        -- let [[binds]] in [[go stmts]]
        LHE.LetStmt (LHE.BDecls binds) -> liftM2 bind (declsCore binds) (go stmts)


specialConDataCon :: LHE.SpecialCon -> DataCon
specialConDataCon LHE.UnitCon = unitDataCon
specialConDataCon LHE.ListCon = nilDataCon
specialConDataCon (LHE.TupleCon LHE.Boxed 2) = pairDataCon
specialConDataCon LHE.Cons = consDataCon

nameString :: LHE.Name -> String
nameString (LHE.Ident s)  = s
nameString (LHE.Symbol s) = s

qNameCore :: LHE.QName -> ParseM Term
qNameCore (LHE.UnQual n) = fmap var $ case nameString n of
    "+"   -> primWrapper Add
    "-"   -> primWrapper Subtract
    "*"   -> primWrapper Multiply
    "div" -> primWrapper Divide
    "mod" -> primWrapper Modulo
    "=="  -> primWrapper Equal
    "<"   -> primWrapper LessThan
    "<="  -> primWrapper LessThanEqual
    s -> return (name s)
qNameCore (LHE.Special sc) = fmap var $ dataConWrapper $ specialConDataCon sc
qNameCore qn = panic "qNameCore" (text $ show qn)

qNameDataCon :: LHE.QName -> DataCon
qNameDataCon (LHE.UnQual n)   = nameString n
qNameDataCon (LHE.Special sc) = specialConDataCon sc

patCores :: [LHE.Pat] -> ParseM ([Var], [Var], Term -> Term)
patCores []     = return ([], [], id)
patCores (p:ps) = do
    (n', bound_ns', build) <- patCore p
    (ns', bound_nss', build') <- patCores ps
    return (n':ns', bound_ns' ++ bound_nss', build . build')

-- | For refutable and irrefutable pattern matches where there is only a single alternative so constructors can be nested
patCore :: LHE.Pat               -- Pattern
        -> ParseM (Var,          -- Name consumed by the pattern
                   [Var],        -- Names bound by the pattern
                   Term -> Term) -- How to build the (strict) consuming context around the thing inside the pattern
patCore (LHE.PVar n)    = return (x, [x], id)
  where x = name (nameString n)
patCore LHE.PWildCard   = fmap (\x -> (x, [x], id)) $ freshName "_"
patCore (LHE.PParen p)  = patCore p
patCore (LHE.PTuple ps) = case tupleDataCon (length ps) of
    Nothing | [p] <- ps -> patCore p
    Just dc -> tuplePatCore dc ps
patCore (LHE.PApp (LHE.Special LHE.UnitCon) []) = tuplePatCore unitDataCon []
patCore (LHE.PInfixApp p1 qinfix p2) = do
    n' <- freshName "infx"
    (n1', bound_ns1, build1) <- patCore p1
    (n2', bound_ns2, build2) <- patCore p2
    return (n', bound_ns1 ++ bound_ns2, \e -> case_ (var n') [(DataAlt (qNameDataCon qinfix) [n1', n2'], build1 (build2 e))])
patCore p = panic "patCore" (text $ show p)

tuplePatCore :: DataCon -> [LHE.Pat] -> ParseM (Var, [Var], Term -> Term)
tuplePatCore dc ps = do
    (ns', bound_ns', build) <- patCores ps
    freshName "tup" >>= \n' -> return (n', bound_ns', \e -> case_ (var n') [(DataAlt dc ns', build e)])

bind :: [(Var, Term)] -> Term -> Term
bind = letRecSmart
