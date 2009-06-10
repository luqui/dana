module LazyHNF.Compiler where

import qualified Data.Map as Map
import Data.Supply
import Control.Monad.Instances
import Debug.Trace
import GHC.Prim (Any)
import Unsafe.Coerce

type Name = Integer
type Sup = Supply Name


infixl 9 :%
data Exp
    = Exp :% Exp
    | Lam Exp
    | Var Int
    | Trace String Exp

type Eval = (->) Sup

data Val
    = VNeutral (Name -> Val -> Eval Val)
    | VFun (Val -> Eval Val)

newName :: (Name -> Eval a) -> Eval a
newName f s = let (s1,s2) = split2 s in 
              f (supplyValue s1) s2

infixl 9 %%
(%%) :: Val -> Val -> Eval Val
(%%) (VFun f) x = f x
(%%) (VNeutral f) x = return . VNeutral $ \from to -> f from to >>= (%% x)

-- does this destroy necessary sharing?
subst :: Name -> Val -> Val -> Eval Val
subst from to (VNeutral n) = n from to
subst from to (VFun f) = newName $ \name -> do
    f' <- f (neutral name) 
    f'' <- subst from to f'
    return . VFun $ \x -> subst name x f''

compile :: [Name] -> Exp -> Eval Val
compile env (t :% u) = do 
    t' <- compile env t 
    u' <- compile env u
    t' %% u'
compile env (Lam t) = newName $ \n -> do
    t' <- compile (n:env) t
    return . VFun $ \v -> subst n v t'
compile env (Var z) = 
    let name = env !! z
    in return (neutral name)
compile env (Trace s exp) = do
    t' <- compile env exp
    return $ case t' of
        VNeutral f -> VNeutral $ \from to -> trace ("Neutral (" ++ s ++ ")") $ f from to
        VFun f -> VFun $ \x -> trace s (f x)

neutral :: Name -> Val
neutral name = r
    where
    r = VNeutral (\from -> if from == name then return else const (return r))


