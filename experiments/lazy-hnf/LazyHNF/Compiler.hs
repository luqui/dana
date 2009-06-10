module LazyHNF.Compiler 
    (Exp(..), Eval, Val, Value(..), eval, makePrim, compile, runEval, (%%)) 
where

import Control.Monad.State
import Control.Monad.Instances
import Control.Applicative

type Name = Integer

infixl 9 :%
data Exp a
    = Exp a :% Exp a
    | Lam (Exp a)
    | Var Int
    | Lit a
    deriving (Show)

newtype Eval a = Eval { unEval :: State Name a }
    deriving (Functor, Monad)

data Val a
    = VNeutral (Name -> Val a -> Eval (Val a))
    | VFun (Val a -> Eval (Val a))
    | VPrim a

class Value v where
    applyValue :: v -> Val v -> Eval (Val v)

eval :: Val a -> Eval (Either a (Val a -> Eval (Val a)))
eval (VNeutral _) = error "Neutral encountered in eval"
eval (VFun f) = return (Right f)
eval (VPrim a) = return (Left a)

makePrim :: a -> Val a
makePrim = VPrim


newName :: (Name -> Eval a) -> Eval a
newName f = Eval $ do
    z <- get
    put $! z+1
    unEval (f z)

infixl 9 %%
(%%) :: (Value a) => Val a -> Val a -> Eval (Val a)
(%%) (VFun f) x = f x
(%%) (VNeutral f) x = return . VNeutral $ \from to -> f from to >>= (%% x)
(%%) (VPrim a) (VNeutral f) = return . VNeutral $ \name val -> (VPrim a %%) =<< f name val
(%%) (VPrim a) b = applyValue a b

showt (VFun _) = "fun"
showt (VNeutral _) = "neutral"
showt (VPrim _) = "prim"

-- does this destroy necessary sharing?
subst :: Name -> Val a -> Val a -> Eval (Val a)
subst from to (VNeutral n) = n from to
subst from to (VFun f) = newName $ \name -> do
    f' <- f (neutral name) 
    f'' <- subst from to f'
    return . VFun $ \x -> subst name x f''
subst from to (VPrim x) = return $ VPrim x

compile' :: (Value a) => [Name] -> Exp a -> Eval (Val a)
compile' env (t :% u) = do
    t' <- compile' env t 
    u' <- compile' env u
    t' %% u'
compile' env (Lam t) = newName $ \n -> do
    t' <- compile' (n:env) t
    return . VFun $ \v -> subst n v t'
compile' env (Var z) = 
    let name = env !! z
    in return (neutral name)
compile' env (Lit l) = return (VPrim l)

compile :: (Value a) => Exp a -> Eval (Val a)
compile = compile' []

neutral :: Name -> Val a
neutral name = r
    where
    r = VNeutral (\from -> if from == name then return else const (return r))

runEval :: Eval a -> a
runEval e = evalState (unEval e) 0
