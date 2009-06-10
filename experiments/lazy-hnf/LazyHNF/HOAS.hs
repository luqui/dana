module LazyHNF.HOAS (Term, (%), fun, lit, buildExp) where

import qualified LazyHNF.Exp as C
import Control.Monad.State
import qualified Data.Map as Map

data Term a
    = App (Term a) (Term a)
    | Lam (Term a -> Term a)
    | Lit a
    | VarID Integer

infixl 9 %
(%) :: Term a -> Term a -> Term a
(%) = App

fun :: (Term a -> Term a) -> Term a
fun = Lam

lit :: a -> Term a
lit = Lit

buildExp :: Term a -> C.Exp a
buildExp t = evalState (go Map.empty t) 0
    where
    go m (App x y) = liftM2 (C.:%) (go m x) (go m y)
    go m (Lam f) = do
        i <- get
        put $! i+1
        fmap C.Lam $ go (Map.insert i 0 . Map.map succ $ m) (f (VarID i))
    go m (Lit a) = return $ C.Lit a
    go m (VarID z) = return $ C.Var (m Map.! z)
