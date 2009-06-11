module IXi.HOAS 
    ( Exp, fun, (%), _Xi, _H, name, hoas) 
where

import qualified Data.Map as Map
import Control.Monad.Trans.State
import qualified IXi.Term as Term
import Control.Applicative
import Control.Monad (liftM2)

type Name = Integer

data Exp 
    = Lambda (Exp -> Exp)
    | Exp :% Exp
    | Var Name
    | NameVar Term.Name
    | Xi | H

infixl 9 %
fun = Lambda
(%) = (:%)
_Xi = Xi
_H  = H
name = NameVar


allocName :: State Name Name
allocName = do
    n <- get
    put $! n+1
    return n

hoas :: Exp -> Term.Term
hoas e = evalState (go Map.empty e) 0
    where
    go m (Lambda f) = do
        name <- allocName
        Term.Lambda <$> go (Map.insert name 0 . Map.map (+1) $ m) (f (Var name))
    go m (t :% u) = liftM2 (Term.:%) (go m t) (go m u)
    go m (Var n) = return $ Term.Var (m Map.! n)
    go m (NameVar n) = return $ Term.NameVar n
    go m Xi = return Term.Xi
    go m H = return Term.H


    
