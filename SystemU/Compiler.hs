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
    | TPi Value (Value -> Value)

data Value
    = VCanon Canon
    | VNeutral Neutral

data Canon
    = CType Type
    | CFun (Value -> Value)

data Neutral
    = NRef Ref
    | NApp Neutral Value


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

instance Show Value where
    show v = evalState (showVal v) (-1)


data Env = Env { envTypes :: [Value], envDefs :: [Value] }

getType,getDef :: Int -> Env -> Value
getType x e = envTypes e !! x
getDef  x e = envDefs  e !! x

type Typecheck = ErrorT String (ReaderT Env (State Integer))

runTypecheck :: Typecheck a -> Either String a
runTypecheck m = evalState (runReaderT (runErrorT m) (Env [] [])) 0

newRef :: Typecheck Ref
newRef = do
    c <- get
    put $! c+1
    return (Ref c)

newNeutral :: Typecheck Value
newNeutral = VNeutral . NRef <$> newRef

subenv :: Value -> Value -> Env -> Env
subenv t v e = Env { envTypes = t:envTypes e, envDefs = v:envDefs e }

assertEq :: Value -> Value -> Typecheck ()
assertEq (VCanon (CType TType)) (VCanon (CType TType)) = return ()
assertEq (VCanon (CType (TPi t f))) (VCanon (CType (TPi t' f'))) = do
    assertEq t t'
    r <- newNeutral
    assertEq (f r) (f' r)
assertEq (VCanon (CFun f)) (VCanon (CFun f')) = do
    r <- newNeutral
    assertEq (f r) (f' r)
assertEq (VNeutral (NRef r)) (VNeutral (NRef r')) 
    | r == r' = return ()
assertEq (VNeutral (NApp n x)) (VNeutral (NApp n' x')) = do
    assertEq (VNeutral n) (VNeutral n')
    assertEq x x'
assertEq _ _ = fail "Unification error!"

vType = VCanon . CType

typecheck :: AST.AST -> Typecheck Value
typecheck (AST.Var ix) = asks (getType ix)
typecheck AST.Type     = return $ vType TType

typecheck (AST.Pi ty body) = do
    dom <- typecheck ty
    assertEq dom (vType TType)
    
    r <- newNeutral
    rng <- local (subenv dom r) $ typecheck body
    assertEq rng (vType TType)
    
    return (vType TType)

typecheck (AST.Lam dom ast) = do
    domt <- typecheck dom
    assertEq domt (vType TType)

    dom' <- eval dom

    r <- newRef
    let n = VNeutral (NRef r)
    rng <- local (subenv dom' n) $ typecheck ast
    return (VCanon (CType (TPi dom' (\v -> subst r v rng))))

typecheck (AST.App a b) = do
    fun <- typecheck a
    arg <- typecheck b
    case fun of
        VCanon (CType (TPi dom rng)) -> do
            assertEq arg dom
            val <- eval b
            return (rng val)
        _ -> fail $ "Application of non-Pi: " ++ show fun


eval :: AST.AST -> Typecheck Value
eval (AST.Var ix) = asks (getDef ix)
eval AST.Type = return (VCanon (CType TType))
eval (AST.Pi domast fast) = do
    dom <- eval domast
    r <- newRef
    f <- local (subenv dom (VNeutral (NRef r))) $ eval fast
    return (VCanon (CType (TPi dom (\v -> subst r v f))))
eval (AST.Lam ty body) = do
    ty' <- eval ty
    r <- newRef
    body' <- local (subenv ty' (VNeutral (NRef r))) $ eval body
    return (VCanon (CFun (\v -> subst r v body')))
eval (AST.App fun arg) = do
    fun' <- eval fun
    arg' <- eval arg
    return $ case fun' of
        VNeutral n -> VNeutral (NApp n arg')
        VCanon (CFun f) -> f arg'
        _ -> error $ "Impossible, function type not a function: " ++ show fun'


subst :: Ref -> Value -> Value -> Value
subst r for t@(VCanon (CType TType)) = t
subst r for (VCanon (CType (TPi dom f))) = VCanon (CType (TPi dom' f'))
    where
    dom' = subst r for dom
    f' = subst r for . f
subst r for (VCanon (CFun f)) = VCanon (CFun f')
    where
    f' = subst r for . f
subst r for (VNeutral n) = substN r for n

substN :: Ref -> Value -> Neutral -> Value
substN r for (NRef r') =
    if r == r' then for else VNeutral (NRef r')
substN r for (NApp n v) = 
    case substN r for n of
        VNeutral n' -> VNeutral (NApp n' (subst r for v))
        VCanon (CFun f) -> subst r for (f v)
        _ -> error "Impossible!"
