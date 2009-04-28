{-# LANGUAGE TemplateHaskell #-}

module IXi.Term where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Applicative
import Data.DeriveTH
import Data.Derive.Binary
import Data.Binary
import Control.Monad

type Var = String

infixl 9 :%
data Term
    = Lam String Term
    | Var String
    | Term :% Term
    | H | Xi
    deriving (Eq, Ord)

$( derive makeBinary ''Term )

freeVars :: Term -> Set.Set Var
freeVars (Lam v t) = Set.delete v (freeVars t)
freeVars (Var x) = Set.singleton x
freeVars (t :% u) = freeVars t `Set.union` freeVars u
freeVars _ = Set.empty

substitute :: Var -> Term -> Term -> Maybe Term
substitute v with = go Set.empty
    where
    withFree = freeVars with
    go bound (Lam v' t) = Lam v' <$> go (Set.insert v' bound) t
    go bound (Var v') | v == v' = 
        if v' `Set.member` bound then Nothing else Just with
    go bound (t :% u) = liftA2 (:%) (go bound t) (go bound u)
    go bound x = Just x

alphaRename :: Var -> Term -> Maybe Term
alphaRename v' (Lam v t) = Lam v' <$> substitute v (Var v') t
alphaRename _ _ = Nothing

betaExpand :: Term -> Maybe Term
betaExpand (Lam v t :% u) = substitute v u t
betaExpand _ = Nothing

etaContract :: Term -> Maybe Term
etaContract (Lam v (t :% Var v')) 
    | v == v' && not (v `Set.member` freeVars t) = Just t
etaContract _ = Nothing

alphaEquiv :: Term -> Term -> Bool
alphaEquiv = go Map.empty Map.empty 0
    where
    go m m' count (Lam v t) (Lam v' t') = go (Map.insert v newv m) (Map.insert v' newv m') (count+1) t t'
        where newv = "@" ++ show count
    go m m' count (Var x) (Var y) = (not (x `Map.member` m) && not (y `Map.member` m'))
                                 || (liftM2 (==) (Map.lookup x m) (Map.lookup y m') == Just True)
    go m m' count (x :% y) (x' :% y') = go m m' count x y && go m m' count x' y'
    go m m' count H H = True
    go m m' count Xi Xi = True
    go m m' count _ _ = False
