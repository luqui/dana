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
substitute v with = go
    where
    withFree = freeVars with
    go (Lam v' t) | v' `Set.member` withFree = Nothing
                  | otherwise = Lam v' <$> go t
    go (Var v') | v == v' = Just with
    go (t :% u) = liftA2 (:%) (go t) (go u)
    go x = Just x

alphaRename :: Var -> Term -> Maybe Term
alphaRename v' (Lam v t) = Lam v' <$> substitute v (Var v') t
alphaRename _ _ = Nothing

betaExpand :: Term -> Maybe Term
betaExpand (Lam v t :% u) = substitute v u t

etaContract :: Term -> Maybe Term
etaContract (Lam v (t :% Var v')) 
    | v == v' && not (v `Set.member` freeVars t) = Just t
etaContract _ = Nothing


