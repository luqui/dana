module IXi.Helpers 
    ( convNF, convInverseNF, convEquiv, convInverseBeta
    , unfoldn, foldn )
where

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
            Lambda (Lambda a) -> tell' convExpandLambda >> go (Lambda (Lambda (swapVars a) :% u))
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

convInverseBeta :: Term -> Conversion
convInverseBeta (Lambda t) = go t
    where
    go (Var 0) = convExpandId
    go t | not (free 0 t) = convExpandConst (decr t)
    go (a :% b)
        | not (free 0 a) =
            convInAppR (go b) `mappend` convExpandRight
        | not (free 0 b) =
            convInAppL (go a) `mappend` convExpandLeft
        | otherwise =
            convInAppL (go a) `mappend` convInAppR (go b) `mappend` convExpandProj
    go (Lambda t) =
        convInLambda (go (swapVars t)) `mappend` convExpandLambda
convInverseBeta _ = error "convInverseBeta not given a lambda argument"

unfoldn :: Int -> Conversion
unfoldn n = mconcat . reverse . take n $ iterate convInAppL convBetaReduce

-- It seems that ignored parts of terms become free variables in the output.
-- This may be distressing, as it means you can convert a closed term into
-- one with free variables.  I don't see a good reason to disallow it though --
-- any choice for that variable yields a correct conversion.
--
-- However, there is still a grossness about it; you would like it to be
-- maximal: you get exactly the number of free variables out as you have
-- choices, so you can characterize all such conversions by filling in the
-- variables.  This is not so currently, as can be seen from the 3-fold of 
-- the term \xyz. yy, which expands to the most hideous and perplexing
-- (\xyz. yy) (\xy. xx) ?0 (xx) on input (?0 ?0).
foldn :: Int -> Term -> Conversion
foldn n = mconcat . zipWith ($) appLs . reverse . bodies n
    where
    appLs = iterate (convInAppL .) convInverseBeta
    
    bodies 0 _ = []
    bodies n t@(Lambda t') = t : bodies (n-1) t'
    bodies n _ = error "foldn not given n nested lambdas"
