{-# LANGUAGE RecursiveDo #-}

module SystemUBox.Compiler where

import qualified SystemUBox.AST as AST
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative
import Control.Monad.Error
import Control.Monad.Writer
import qualified Data.Set as Set
import Data.List (intercalate)

newtype Ref = Ref Integer
    deriving (Eq,Ord)

data Type
    = TType
    | TPartial Value
    | TPi Value (Value -> Value)
    | TFinite Int

data Value
    = VCanon Canon
    | VNeutral Neutral

data Canon
    = CType Type
    | CFun (Value -> Value)
    | CBox [(Ref,Value)] Value  -- holds an explicit closure
    | CLabel Int

data Neutral
    = NRef Ref
    | NApp Neutral Value
    | NUnbox Neutral
    | NCase Neutral [Value]


-- Mega Hax!!
-- We use negative neutrals when showing to keep from interfering
-- with the main substitution mechanic.
type ShowM = WriterT (Set.Set Ref) (State Integer)

newRefShow :: ShowM Ref
newRefShow = do
    c <- get
    put $! (c-1)
    return (Ref c)

valToName :: Integer -> String
valToName z | z < 0     = "@" ++ show (-z)
            | z < 26    = (:[]) $ ['a'..'z'] !! fromIntegral z
            | otherwise = valToName (z `mod` 26) ++ show (z `div` 26)

showRef (Ref c) = valToName (-c)

parens :: Int -> Int -> String -> String
parens p prec s =
    case compare p prec of
        LT -> "(" ++ s ++ ")"
        GT -> s
        EQ -> "(" ++ s ++ ")"

showVal :: Int -> Value -> ShowM String
showVal prec (VCanon (CType TType)) = return "Type"
showVal prec (VCanon (CType (TPi dom f))) = do
    n <- newRefShow
    (rng',s) <- listen (showVal 1 (f (VNeutral (NRef n))))
    case n `Set.member` s of
        True -> do
            dom' <- showVal 2 dom
            return $ parens 2 prec ("(" ++ showRef n ++ " : " ++ dom' ++ ") -> " ++ rng')
        False -> do
            dom' <- showVal 2 dom
            return $ parens 2 prec (dom' ++ " -> " ++ rng')
showVal prec (VCanon (CType (TPartial t))) = do
    t' <- showVal 3 t
    return $ "$" ++ t'
showVal prec (VCanon (CType (TFinite n))) = do
    return $ show n
showVal prec (VCanon (CBox _ v)) = do
    v' <- showVal 0 v
    return $ "[" ++ v' ++ "]"
showVal prec (VCanon (CFun f)) = do
    n <- newRefShow
    let n' = showRef n
    body <- showVal 0 (f (VNeutral (NRef n)))
    return $ parens 0 prec ("\\" ++ n' ++ ". " ++ body ++ "")
showVal prec (VCanon (CLabel l)) = do
    return $ "'" ++ show l
showVal prec (VNeutral n) = showNeutral prec n

showNeutral :: Int -> Neutral -> ShowM String
showNeutral prec (NRef r) = do
    tell (Set.singleton r)
    return $ showRef r
showNeutral prec (NApp n v) = do
    n' <- showNeutral 1 n
    v' <- showVal 2 v
    return $ parens 2 prec (n' ++ " " ++ v')
showNeutral prec (NUnbox n) = do
    n' <- showNeutral 3 n
    return $ "!" ++ n'
showNeutral prec (NCase n cs) = do
    n' <- showNeutral 0 n
    cs' <- mapM (showVal 0) cs
    return $ "case " ++ n' ++ " of { " ++ intercalate "; " cs' ++ " }"

instance Show Value where
    show v = evalState (fmap fst . runWriterT $ showVal 0 v) (-1)

-- envNames is a set of alternate values for the environment.
-- we copy this to envDefs when we go under a box
data Env = Env { envTypes :: [Value], envDefs :: [Value], envNames :: [Ref] }

getType,getDef :: Int -> Env -> Value
getType x e = envTypes e !! x
getDef  x e = envDefs  e !! x

type Typecheck = ErrorT String (ReaderT Env (State Integer))

runTypecheck :: Typecheck a -> Either String a
runTypecheck m = evalState (runReaderT (runErrorT m) (Env [] [] [])) 0


newRef :: Typecheck Ref
newRef = do
    c <- get
    put $! c+1
    return (Ref c)

newNeutral :: Typecheck Value
newNeutral = VNeutral . NRef <$> newRef

makeSubenv :: Typecheck (Value -> Value -> Env -> Env)
makeSubenv = do
    name <- newRef
    return $ \t v e -> Env { envTypes = t:envTypes e, envDefs = v:envDefs e, envNames = name:envNames e}

subenv :: Value -> Value -> Typecheck a -> Typecheck a
subenv t v m = do
    s <- makeSubenv
    local (s t v) m

assertEq :: Value -> Value -> Typecheck ()
assertEq (VCanon (CType TType)) (VCanon (CType TType)) = return ()
assertEq (VCanon (CType (TPi t f))) (VCanon (CType (TPi t' f'))) = do
    assertEq t t'
    r <- newNeutral
    assertEq (f r) (f' r)
assertEq (VCanon (CType (TPartial t))) (VCanon (CType (TPartial t'))) = do
    assertEq t t'
assertEq (VCanon (CType (TFinite n))) (VCanon (CType (TFinite n'))) 
    | n == n' = return ()
assertEq (VCanon (CFun f)) (VCanon (CFun f')) = do
    r <- newNeutral
    assertEq (f r) (f' r)
assertEq (VCanon (CBox cl v)) (VCanon (CBox cl' v')) = do
    assertEq v v'    -- XXX probably should do more sophisticated closure analysis
assertEq (VCanon (CLabel l)) (VCanon (CLabel l'))
    | l == l' = return ()
assertEq (VNeutral (NRef r)) (VNeutral (NRef r')) 
    | r == r' = return ()
assertEq (VNeutral (NApp n x)) (VNeutral (NApp n' x')) = do
    assertEq (VNeutral n) (VNeutral n')
    assertEq x x'
assertEq (VNeutral (NUnbox n)) (VNeutral (NUnbox n')) = do
    assertEq (VNeutral n) (VNeutral n')
assertEq (VNeutral (NCase n cs)) (VNeutral (NCase n' cs')) = do
    assertEq (VNeutral n) (VNeutral n')
    mapM_ (uncurry assertEq) (zip cs cs')
assertEq v v' = fail $ "Cannot unify: " ++ show v ++ " with " ++ show v'

vType = VCanon . CType

typecheck :: AST.AST -> Typecheck Value
typecheck (AST.Var ix) = asks (getType ix)
typecheck AST.Type     = return $ vType TType

typecheck (AST.Pi ty body) = do
    domt <- typecheck ty
    assertEq domt (vType TType)
    
    dom <- eval ty
    r <- newNeutral
    rng <- subenv dom r $ typecheck body
    assertEq rng (vType TType)
    
    return (vType TType)

typecheck (AST.Lam dom ast) = do
    domt <- typecheck dom
    assertEq domt (vType TType)

    dom' <- eval dom

    r <- newRef
    let n = VNeutral (NRef r)
    rng <- subenv dom' n $ typecheck ast
    return (VCanon (CType (TPi dom' (\v -> subst r v rng))))

typecheck (AST.App a b) = do
    fun <- typecheck a
    arg <- typecheck b
    case fun of
        VCanon (CType (TPi dom rng)) -> do
            assertEq arg dom
            val <- eval b
            return (rng val)
        _ -> fail $ "Application of non-Pi: " ++ show fun ++ " applied to " ++ show arg

typecheck (AST.Finite n) = return (vType TType)

typecheck (AST.Label ss n) = do
    unless (ss >= 0 && ss < n) . fail $ "Illegal label (" ++ show ss ++ ":" ++ show n ++ ")"
    return (vType (TFinite n))

typecheck (AST.Case scrutinee ret cases) = do
    fin <- typecheck scrutinee
    n <- case fin of
            VCanon (CType (TFinite n)) -> return n
            _ -> fail $ "Case on non-finite type: " ++ show fin

    scrutinee' <- eval scrutinee

    retft <- typecheck ret
    assertEq retft (vType (TPi fin (\_ -> vType TType)))
    retf <- eval ret
    
    forM_ (zip [0..] cases) $ \(label,body) -> do
        caset <- typecheck body
        assertEq caset (applyVal retf (VCanon (CLabel label)))
    return $ applyVal retf scrutinee'

typecheck (AST.LetRec defs body) = go defs
    where
    go [] = typecheck body
    go ((typ,def):defs) = mdo
        -- check that the type is a type
        assertEq (vType TType) =<< typecheck typ
        -- compile the type
        typv <- eval typ
        -- check the type of the body under that assumption
        r <- newRef
        typvInfer <- subenv typv (VNeutral (NRef r)) $ typecheck def
        assertEq typv typvInfer   -- hmm.. what happened to r?  should we subst it for body?

        sub <- makeSubenv
        body <- local (sub typv body) $ eval def
        local (sub typv body) $ go defs
            

typecheck (AST.Partial sub) = do
    t <- typecheck sub
    assertEq t (vType TType)
    return (vType TType)

typecheck (AST.Box sub) = do
    -- I don't think definitions are hidden when typechecking
    -- a box, just evaluating it.
    t <- typecheck sub
    return (vType (TPartial t))

typecheck (AST.Unbox sub) = do
    t <- typecheck sub
    case t of
        VCanon (CType (TPartial t)) -> return t
        _ -> fail $ "Type error when checking unbox: " ++ show sub
    

eval :: AST.AST -> Typecheck Value
eval (AST.Var ix) = asks (getDef ix)
eval AST.Type = return (VCanon (CType TType))
eval (AST.Pi domast fast) = do
    dom <- eval domast
    r <- newRef
    f <- subenv dom (VNeutral (NRef r)) $ eval fast
    return (VCanon (CType (TPi dom (\v -> subst r v f))))
eval (AST.Lam ty body) = do
    ty' <- eval ty
    r <- newRef
    body' <- subenv ty' (VNeutral (NRef r)) $ eval body
    return (VCanon (CFun (\v -> subst r v body')))
eval (AST.App fun arg) = do
    fun' <- eval fun
    arg' <- eval arg
    return $ applyVal fun' arg'
eval (AST.Finite n) = return $ vType (TFinite n)
eval (AST.Label l n) = return $ VCanon (CLabel l)
eval (AST.Case scrutinee _ cases) = do
    scrutinee' <- eval scrutinee
    cases' <- mapM eval cases
    return $ caseVal scrutinee' cases'
eval (AST.LetRec defs body) = go defs
    where
    go [] = eval body
    go ((typ,def):defs) = mdo
        typ' <- eval typ
        ~(ret, def') <- subenv typ' def' $ do
            def' <- eval def
            ret <- go defs
            return (ret,def')
        return ret
eval (AST.Partial sub) = do
    t <- eval sub
    return (vType (TPartial t))
eval (AST.Box sub) = do
    defs <- asks envDefs
    names <- asks envNames
    let restore = zip names defs
    let newDefs = map (VNeutral . NRef) names
    t <- local (\e -> e { envDefs = newDefs }) $ eval sub
    return (VCanon (CBox restore t))
eval (AST.Unbox sub) = do
    t <- eval sub
    return $ unboxVal t
    

applyVal :: Value -> Value -> Value
applyVal f x =
    case f of
        VNeutral n -> VNeutral (NApp n x)
        VCanon (CFun f) -> f x
        _ -> error "Cannot apply non-function"

caseVal :: Value -> [Value] -> Value
caseVal s cs = 
    case s of
        VNeutral n -> VNeutral (NCase n cs)
        VCanon (CLabel l) -> cs !! l
        _ -> error "Cannot scrutinize a non-label"

unboxVal :: Value -> Value
unboxVal val =
    case val of
        VNeutral n -> VNeutral (NUnbox n)
        VCanon (CBox restore v') -> foldr (.) id [subst r def | (r,def) <- restore] v'
        _ -> error "Cannot unbox a non-box"

subst :: Ref -> Value -> Value -> Value
subst r for t@(VCanon (CType TType)) = t
subst r for (VCanon (CType (TPi dom f))) = VCanon (CType (TPi dom' f'))
    where
    dom' = subst r for dom
    f' = subst r for . f . subst r for
subst r for (VCanon (CType (TPartial v))) = VCanon (CType (TPartial (subst r for v)))
subst r for (VCanon (CType (TFinite n))) = VCanon (CType (TFinite n))
subst r for (VCanon (CFun f)) = VCanon (CFun f')
    where
    f' = subst r for . f . subst r for
subst r for (VCanon (CBox cl v)) = VCanon (CBox (cl ++ [(r,for)]) v)
subst r for (VCanon (CLabel l)) = VCanon (CLabel l)
subst r for (VNeutral n) = substN r for n

substN :: Ref -> Value -> Neutral -> Value
substN r for (NRef r') =
    if r == r' then for else VNeutral (NRef r')
substN r for (NApp n v) = applyVal (substN r for n) (subst r for v)
substN r for (NUnbox n) = unboxVal (substN r for n)
substN r for (NCase s cs) = caseVal (substN r for s) (map (subst r for) cs)
