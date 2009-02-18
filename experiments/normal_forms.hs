{-# LANGUAGE PatternGuards #-}

import Control.Monad (liftM2, MonadPlus(..), (<=<))

data Combi
    = CS | CK | CI

infixl 9 :%
data Term
    = Combi Combi
    | Lam Term
    | Var Int
    | Term :% Term

s = Combi CS
k = Combi CK
i = Combi CI

showTerm :: Term -> String
showTerm = go False False
    where
    go _ _  (Combi CS) = "S"
    go _ _  (Combi CK) = "K"
    go _ _  (Combi CI) = "I"
    go _ lp (Lam t)    = parens lp $ "\\." ++ go False False t
    go _ _  (Var z)    = show z
    go ap _ (t :% u)   = parens ap $ go False True t ++ " " ++ go True True u
    
    parens True s  = "(" ++ s ++ ")"
    parens False s = s

instance Show Term where
    show = showTerm


unfree :: Int -> Term -> Maybe Term
unfree z (Var x) =
    case compare z x of
        EQ -> Nothing
        LT -> Just (Var (x-1))
        GT -> Just (Var x)
unfree z (Lam f) = fmap Lam (unfree (z+1) f)
unfree z (f :% x) = liftM2 (:%) (unfree z f) (unfree z x)
unfree z (Combi c) = Just (Combi c)

tr :: Term -> Term
tr (Combi c) = Combi c
tr (Var z) = Var z
tr (a :% b) = tr a :% tr b
tr (Lam t) | Just t' <- unfree 0 t = Combi CK :% tr t'
tr (Lam (Var 0)) = Combi CI
tr (Lam (Lam t)) | Nothing <- unfree 1 t = tr (Lam (tr (Lam t)))
tr (Lam (t :% Var 0)) | Just t' <- unfree 0 t = t'
tr (Lam (t :% u)) = Combi CS :% tr (Lam t) :% tr (Lam u)


reduce :: Term -> Maybe Term
reduce (Lam t) = fmap Lam (reduce t)
reduce (Combi CS :% x :% y :% z) = Just $ x :% z :% (y :% z)
reduce (Combi CK :% x :% y)      = Just x
reduce (Combi CI :% x)           = Just x
reduce (Lam f :% x) = Just $ subst 0 x f
reduce (Var z :% t) = fmap (Var z :%) (reduce t)
reduce (t :% u :% v) = fmap (:% v) (reduce (t :% u))
               `mplus` fmap (t :% u :%) (reduce v)
reduce _ = Nothing

flatten :: Term -> [Term]
flatten (t :% u) = flatten t ++ [u]
flatten x = [x]


shiftUp :: Int -> Term -> Term
shiftUp z (Lam t) = Lam (shiftUp (z+1) t)
shiftUp z (Var z') | z' < z = Var z'
                   | otherwise = Var (z'+1)
shiftUp z (t :% u) = shiftUp z t :% shiftUp z u
shiftUp z (Combi c) = Combi c

subst :: Int -> Term -> Term -> Term
subst z for (Combi c) = Combi c
subst z for (Lam t)   = Lam (subst (z+1) (shiftUp 0 for) t)
subst z for (Var z') | z == z' = for
                     | otherwise = Var z'
subst z for (t :% u) = subst z for t :% subst z for u

reduceNF :: Term -> Term
reduceNF = multiReduce reduce

multiReduce :: (a -> Maybe a) -> a -> a
multiReduce f t = maybe t (multiReduce f) (f t)

rept :: Int -> (a -> a) -> (a -> a)
rept n f = (!! n) . iterate f

etaExpand :: Int -> Term -> Term
etaExpand n t = rept n Lam $ rept n (\t' -> shiftUp 0 t' :% Var 0) t

rephrase :: Int -> Term -> Term
rephrase n = tr . reduceNF . etaExpand n

