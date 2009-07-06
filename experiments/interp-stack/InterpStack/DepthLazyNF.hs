{-# LANGUAGE PatternGuards #-}

module InterpStack.DepthLazyNF (depthLazyNFInterp, compile, Val) where

import InterpStack.Exp

type Depth = Int

infix 9 :@
data Val a = Depth :@ Node a
    deriving (Show)

data Node a
    = VLam (Val a)
    | VApp (Val a) (Val a)
    | VVar
    | VPrim a
    deriving (Show)

app :: (Value a) => Depth -> Val a -> Val a -> Val a
app δ (δλ :@ VLam λ) arg = subst δλ (δ - δλ - 1) arg λ
app _ (_ :@ VPrim a) (_ :@ VPrim b) = 0 :@ VPrim (applyValue a b)
app _ (_ :@ VPrim _) (_ :@ VLam _) = error "Apply primitive to lambda not supported"
app δ l r = δ :@ VApp l r

subst :: (Value a) => Depth -> Depth -> Val a -> Val a -> Val a
subst δs shiftδ arg (δbody :@ body)
    | δbody <= δs = δbody :@ body
    | VLam λ   <- body = δnew :@ VLam (subst δs shiftδ arg λ)
    | VApp l r <- body = app δnew (subst δs shiftδ arg l) (subst δs shiftδ arg r)
    | VVar     <- body = if δs+1 == δbody then arg else δnew :@ VVar
    | VPrim v  <- body = 0 :@ VPrim v
    where
    δnew = δbody + shiftδ

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
    go depths (t :% u) = app (max δt δu) (δt :@ t') (δu :@ u')
        where
        δt :@ t' = go depths t
        δu :@ u' = go depths u
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
