module IXi.Helpers where

import IXi.Term
import Control.Monad.Writer
import Control.Applicative

convNF :: (Eq n) => Term n -> (Term n, Conversion n')
convNF = runWriter . go
    where
    go (Lambda t) = Lambda <$> censor convInLambda (go t)
    go (t :% u) = do
        t' <- censor convInAppL (go t)
        case t' of
            Lambda body -> tell convBetaReduce >> go (subst 0 u body)
            _ -> (t :%) <$> censor convInAppR (go u)
    go x = return x

convInverseNF :: (Eq n, Eq n') => Term n -> (Term n, Conversion n')
convInverseNF = second getDual . runWriter . go
    where
    go (Lambda t) = Lambda <$> censor (inDual convInLambda) (go t)
    go (t :% u) = do
        t' <- censor (inDual convInAppL) (go t)
        case t' of
            Lambda (Var 0) -> tell (Dual convExpandId) >> go u
            Lambda t | Just t' <- unfree 0 t 
                     , Just t'' <- rebrand t'   -- << name-dependency here
                -> tell (Dual (convExpandConst t'')) >> go t'
            Lambda (a :% b)
                | Just a' <- unfree 0 a -> tell (Dual convExpandRight) >> go (a' :% (Lambda b :% u))
                | Just b' <- unfree 0 b -> tell (Dual convExpandLeft)  >> go ((Lambda a :% u) :% b')
                | otherwise -> tell (Dual convExpandProj) >> go ((Lambda a :% u) :% (Lambda b :% u))
            Lambda (Lambda a) -> tell (Dual convExpandLambda) >> go (Lambda (Lambda (subst 0 (Var 1) a) :% u))
            Lambda _ -> error $ "Normal form not invertible in a name-independent way: " ++ showTerm (const "*") t'
            _ -> (t' :%) <$> censor (inDual convInAppR) (go u)
    go x = return x
    
    inDual f (Dual x) = Dual (f x)
    second f (a,b) = (a, f b)

convEquiv :: (Eq n, Eq n') => Term n -> Term n -> Maybe (Conversion n')
convEquiv t t' = 
    let (nf1, conv1) = convNF t
        (nf2, conv2) = convInverseNF t'
    in 
        if nf1 == nf2 then Just (conv1 `mappend` conv2) else Nothing

-- X -> (\x. x) X -> (\y. (\x. x) X) Y -> (\x. \y. x) X Y
convExpandK y = mconcat [
    convExpandId,
    convExpandConst y,
    convInAppL convExpandLambda ]

rebrand :: Term a -> Maybe (Term b)
rebrand (Lambda t) = Lambda <$> rebrand t
rebrand (t :% u) = liftA2 (:%) (rebrand t) (rebrand u)
rebrand (Var n) = Just (Var n)
rebrand (NameVar n) = Nothing
rebrand Xi = Just Xi
rebrand H = Just H
