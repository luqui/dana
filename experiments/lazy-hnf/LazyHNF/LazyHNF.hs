module LazyHNF.LazyHNF 
    ( Val, Value(..), eval )
where

import LazyHNF.Exp

data Val a 
    = VLam (Val a)
    | VApp (Val a) (Val a)
    | VVar Int
    | VPrim a
    deriving (Show)

class Value v where
    applyValue :: v -> v -> v

quote :: Val a -> Val a
quote = go 0
    where
    go n (VLam a) = VLam (go (n+1) a)
    go n (VApp a b) = VApp (go n a) (go n b)
    go n (VVar z) | n <= z = VVar (z+1)
                 | otherwise = VVar z
    go n (VPrim p) = VPrim p

subst :: (Value a) => Val a -> Val a -> Val a
subst = go 0
    where
    go n to (VLam body) = VLam (go (n+1) (quote to) body)
    go n to (VApp a b) = go n to a %% go n to b
    go n to (VVar z) =
        case compare n z of
            LT -> VVar (z-1)
            EQ -> to
            GT -> VVar z
    go n to (VPrim p) = VPrim p

(%%) :: (Value a) => Val a -> Val a -> Val a
VLam body %% arg = subst arg body
VPrim p %% VPrim q = VPrim (applyValue p q)
VPrim p %% VLam body = error "Cannot apply a primitive to a lambda"
VPrim p %% t = VApp (VPrim p) t
exp %% arg = VApp exp arg



eval :: (Value a) => Exp a -> Val a
eval (a :% b) = eval a %% eval b
eval (Lam body) = VLam (eval body)
eval (Var z) = VVar z
eval (Lit p) = VPrim p
