module LazyHNF.LazyNF 
    ( lazyNFInterp )
where

import LazyHNF.Exp

data Val a 
    = VLam (Val a)
    | VApp (Val a) (Val a)
    | VVar Int
    | VPrim a
    deriving (Show)

quote :: Int -> Val a -> Val a
quote by = go 0
    where
    go n (VLam a) = VLam (go (n+1) a)
    go n (VApp a b) = VApp (go n a) (go n b)
    go n (VVar z) | n <= z = VVar (z+by)
                  | otherwise = VVar z
    go n (VPrim p) = VPrim p

subst :: (Value a) => Val a -> Val a -> Val a
subst = go 0 0
    where
    go n q to (VLam body) = VLam (go (n+1) (q+1) to body)
    go n q to (VApp a b) = go n q to a %% go n q to b
    go n q to (VVar z) =
        case compare n z of
            LT -> VVar (z-1)
            EQ -> quote q to
            GT -> VVar z
    go n q to (VPrim p) = VPrim p

(%%) :: (Value a) => Val a -> Val a -> Val a
VLam body %% arg = subst arg body
VPrim p %% VPrim q = VPrim (applyValue p q)
VPrim p %% VLam body = error "Cannot apply a primitive to a lambda"
VPrim p %% t = VApp (VPrim p) t
exp %% arg = VApp exp arg

lazyNFInterp = Interp {
    eval = getValNF . evalNF
}

getValNF (VPrim a) = Just a
getValNF _ = Nothing

evalNF (a :% b) = evalNF a %% evalNF b
evalNF (Lam body) = VLam (evalNF body)
evalNF (Var z) = VVar z
evalNF (Lit p) = VPrim p
