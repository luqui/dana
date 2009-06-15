module IXi.Helpers where

import IXi.Term
import IXi.Conversion
import Control.Monad.Trans.Writer
import Control.Applicative
import Data.Monoid
import Data.Maybe (fromJust)

convNF :: Term -> (Term, Conversion)
convNF = runWriter . go
    where
    go (Lambda t) = Lambda <$> censor convInLambda (go t)
    go (t :% u) = do
        t' <- censor convInAppL (go t)
        case t' of
            Lambda body -> tell convBetaReduce >> go (subst 0 u body)
            _ -> (t :%) <$> censor convInAppR (go u)
    go x = return x

convInverseNF :: Term -> (Term, Conversion)
convInverseNF = second getDual . runWriter . go
    where
    go (Lambda t) = Lambda <$> censor' convInLambda (go t)
    go (t :% u) = do
        t' <- censor' convInAppL (go t)
        case t' of
            Lambda (Var 0) -> tell' convExpandId >> go u
            Lambda t | not (free 0 t)
                -> tell' (convExpandConst (decr t)) >> go (decr t)
            Lambda (a :% b)
                | not (free 0 a) -> tell' convExpandRight >> go (decr a :% (Lambda b :% u))
                | not (free 0 b) -> tell' convExpandLeft  >> go ((Lambda a :% u) :% decr b)
                | otherwise -> tell' convExpandProj >> go ((Lambda a :% u) :% (Lambda b :% u))
            Lambda (Lambda a) -> tell' convExpandLambda >> go (Lambda (Lambda (subst 0 (Var 1) a) :% u))
            _ -> (t' :%) <$> censor' convInAppR (go u)
    go x = return x
    
    inDual f (Dual x) = Dual (f x)
    second f (a,b) = (a, f b)
    tell' = tell . Dual
    censor' = censor . inDual
    decr = fromJust . unfree 0

convEquiv :: Term -> Term -> Maybe Conversion
convEquiv t t' = 
    let (nf1, conv1) = convNF t
        (nf2, conv2) = convInverseNF t'
    in 
        if nf1 == nf2 then Just (conv1 `mappend` conv2) else Nothing
