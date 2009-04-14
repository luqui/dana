module IXi.Term where

import qualified Data.Set as Set
import Control.Applicative

type Var = String

infixl 9 :%
data Term
    = Lam String Term
    | Var String
    | Term :% Term
    | H | Xi
    deriving (Eq)

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

etaContract :: Term -> Maybe Term
etaContract (Lam v (t :% Var v')) 
    | v == v' && not (v `Set.member` freeVars t) = Just t
etaContract _ = Nothing



