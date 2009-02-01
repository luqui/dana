{-# LANGUAGE RecursiveDo #-}

module SystemU.Compiler where

import qualified SystemU.AST as AST
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative
import Control.Monad.Error

newtype Ref = Ref Integer
    deriving (Eq,Ord)

data Type
    = TType
    | TPartial Value
    | TPi Value (Value -> Value)

data Value
    = VCanon Canon
    | VNeutral Neutral

data Canon
    = CType Type
    | CFun (Value -> Value)
    | CBox [(Ref,Value)] Value  -- holds an explicit closure

data Neutral
    = NRef Ref
    | NApp Neutral Value
    | NUnbox Neutral


-- Mega Hax!!
-- We use negative neutrals when showing to keep from interfering
-- with the main substitution mechanic.
type ShowM = State Integer

newNeutralShow :: ShowM Value
newNeutralShow = do
    c <- get
    put $! (c-1)
    return (VNeutral (NRef (Ref c)))

showVal :: Value -> ShowM String
showVal (VCanon (CType TType)) = return "Type"
showVal (VCanon (CType (TPi dom f))) = do
    n <- newNeutralShow
    dom' <- showVal dom
    rng' <- showVal (f n)
    n' <- showVal n
    return $ "(/\\" ++ n' ++ " : " ++ dom' ++ ". " ++ rng' ++ ")"
showVal (VCanon (CType (TPartial t))) = do
    t' <- showVal t
    return $ "$" ++ t'
showVal (VCanon (CBox _ v)) = do
    v' <- showVal v
    return $ "[" ++ v' ++ "]"
showVal (VCanon (CFun f)) = do
    n <- newNeutralShow
    n' <- showVal n
    body <- showVal (f n)
    return $ "(\\" ++ n' ++ ". " ++ body ++ ")"
showVal (VNeutral n) = showNeutral n

showNeutral :: Neutral -> ShowM String
showNeutral (NRef (Ref r)) = return $ "@" ++ show (-r)
showNeutral (NApp n v) = do
    n' <- showNeutral n
    v' <- showVal v
    return $ "(" ++ n' ++ " " ++ v' ++ ")"
showNeutral (NUnbox n) = do
    n' <- showNeutral n
    return $ "!" ++ n'

instance Show Value where
    show v = evalState (showVal v) (-1)

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
assertEq (VCanon (CFun f)) (VCanon (CFun f')) = do
    r <- newNeutral
    assertEq (f r) (f' r)
assertEq (VCanon (CBox cl v)) (VCanon (CBox cl' v')) = do
    assertEq v v'    -- XXX probably should do more sophisticated closure analysis
assertEq (VNeutral (NRef r)) (VNeutral (NRef r')) 
    | r == r' = return ()
assertEq (VNeutral (NApp n x)) (VNeutral (NApp n' x')) = do
    assertEq (VNeutral n) (VNeutral n')
    assertEq x x'
assertEq (VNeutral (NUnbox n)) (VNeutral (NUnbox n')) = do
    assertEq (VNeutral n) (VNeutral n')
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
    return $ case fun' of
        VNeutral n -> VNeutral (NApp n arg')
        VCanon (CFun f) -> f arg'
        _ -> error $ "Impossible, function type not a function: " ++ show fun'
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
    case t of
        VCanon (CBox restore v') -> return $ 
            foldr (.) id [ subst r def | (r,def) <- restore ] v'
        VNeutral n -> return $ VNeutral (NUnbox n)
        _ -> fail $ "Unboxing a nonbox: " ++ show sub
    

zipWithSpine :: [a] -> (b -> c -> d) -> [b] -> [c] -> [d]
zipWithSpine [] _ _ _ = []
zipWithSpine (_:ss) f ~(b:bs) ~(c:cs) = f b c : zipWithSpine ss f bs cs

subst :: Ref -> Value -> Value -> Value
subst r for t@(VCanon (CType TType)) = t
subst r for (VCanon (CType (TPi dom f))) = VCanon (CType (TPi dom' f'))
    where
    dom' = subst r for dom
    f' = subst r for . f
subst r for (VCanon (CType (TPartial v))) = VCanon (CType (TPartial (subst r for v)))
subst r for (VCanon (CFun f)) = VCanon (CFun f')
    where
    f' = subst r for . f
subst r for (VCanon (CBox cl v)) = VCanon (CBox (cl ++ [(r,for)]) v)
subst r for (VNeutral n) = substN r for n

substN :: Ref -> Value -> Neutral -> Value
substN r for (NRef r') =
    if r == r' then for else VNeutral (NRef r')
substN r for (NApp n v) = 
    case substN r for n of
        VNeutral n' -> VNeutral (NApp n' (subst r for v))
        VCanon (CFun f) -> subst r for (f v)
        _ -> error "Impossible!"
substN r for (NUnbox n) = 
    case substN r for n of
        VNeutral n' -> VNeutral (NUnbox n')
        VCanon (CBox restore v) -> foldr (.) id [subst r def | (r,def) <- restore ] v
        _ -> error "Bullshit!"
