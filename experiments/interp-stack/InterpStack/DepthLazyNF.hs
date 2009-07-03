module InterpStack.DepthLazyNF (depthLazyNFInterp, compile, Val) where

import InterpStack.Exp

infix 9 :@
data Val a = Int :@ Node a
    deriving (Show)

data Node a
    = VLam (Val a)
    | VApp (Val a) (Val a)
    | VVar
    | VPrim a
    deriving (Show)

infixl 8 %%
(%%) :: (Value a) => Val a -> Val a -> Val a
δf :@ VLam body %%  arg           = subst (δf+1) arg body
_ :@ VPrim p    %%  _ :@ VPrim q  = 0 :@ VPrim (applyValue p q)
_ :@ VPrim p    %%  _ :@ VLam _   = error "Can't apply a primitive to a lambda"
_ :@ VPrim p    %%  δz :@ z       = δz :@ VApp (0 :@ VPrim p) (δz :@ z)
δexp :@ exp     %%  δarg :@ arg   = max δexp δarg :@ VApp (δexp :@ exp) (δarg :@ arg)

subst :: (Value a) => Int -> Val a -> Val a -> Val a
subst δ arg@(δarg :@ argnode) (δbody :@ body) 
    | δbody < δ = δbody :@ body
    | otherwise =
        case body of
            VLam b -> δnew :@ VLam (subst δ arg b)
            VApp l r -> clamp δnew (subst δ arg l %% subst δ arg r)
            VVar -> case compare δbody δ of
                        EQ -> arg
                        GT -> (δbody-1) :@ VVar
                        LT -> δbody :@ VVar
            VPrim a -> 0 :@ VPrim a
    where
    δnew = max (δbody-1) δarg

clamp :: Int -> Val a -> Val a
clamp c ~(x :@ v) = c :@ v

minFree n (t :% u) = plusWith min (minFree n t) (minFree n u)
minFree n (Lam t) = minFree (n+1) t
minFree n (Var z) | n <= z    = Just (z-n)
                  | otherwise = Nothing
minFree n (Lit l) = Nothing

plusWith f Nothing Nothing = Nothing
plusWith f (Just x) Nothing = Just x
plusWith f Nothing (Just y) = Just y
plusWith f (Just x) (Just y) = Just (f x y)

compile :: (Value a) => Exp a -> Val a
compile = go []
    where
    go depths (t :% u) = go depths t %% go depths u
    go depths (Lam t) = δnew :@ VLam (go (δnew : depths) t)
        where
        δnew = case minFree 0 (Lam t) of
                    Nothing -> 0
                    Just n -> (depths !! n) + 1
    go depths (Var z) = let δ = (depths !! z) + 1 in δ :@ VVar
    go depths (Lit l) = 0 :@ VPrim l

depthLazyNFInterp = Interp {
    eval = getValNF . compile
}

getValNF (_ :@ VPrim v) = Just v
getValNF _ = Nothing
