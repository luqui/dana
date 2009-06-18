module IXi.Tactics where

import IXi.Tactic
import IXi.HOAS
import IXi.Term
import IXi.Helpers
import IXi.Conversion
import qualified IXi.Sequent as Sequent
import Data.Monoid (mconcat, mappend)

_K = fun (\x -> fun (\y -> x))
-- x -> Kxy
fold_K y = convInverseBeta . hoas . fun $ \x -> y
-- Kxy -> x
unfold_K = mconcat [convInAppL convBetaReduce, convBetaReduce]


_I = fun (\x -> x)
-- x -> Ix
fold_I = convInverseBeta (hoas _I)
-- Ix -> x
unfold_I = convBetaReduce


p ==> q = _Xi % (_K % p) % (_K % q)


-- |- Q
--  |- KQI
--   |- Ξ(KP)(KQ)
--    |- P ==> Q
--   |- KPI
--    |- P
modusPonens :: Exp -> Tactic -> Tactic -> Tactic
modusPonens p pqPf pPf = 
    conversion (fold_K _I) $
    implRule (hoas (_K % p % _I)) (conversion unfold_K pPf) pqPf

-- |- P ==> Q
--  |- Ξ(KP)(KQ)
--   |- H(KPx)
--    |- HP
--   KPx |- KQx
--    P |- Q
implAbstract :: Tactic -> (Hypothesis -> Tactic) -> Tactic
implAbstract hpPf pqPf = 
    newName $ \n -> 
    xiRule n (conversion (convInAppR unfold_K) hpPf)
                (\kpx -> conversion unfold_K (pqPf (conversion (fold_K (name n)) kpx)))


-- |- ΞA(\x. B)
--  |- H(Ax)
--  Ax |- (\x. B)x
--   Ax |- B
lambdaXiRule :: Name -> Tactic -> (Hypothesis -> Tactic) -> Tactic
lambdaXiRule x haPf abPf =
    xiRule x haPf (\ax -> conversion convBetaReduce (abPf ax))

-- |- ΞH(\P. P ==> P)
--  |- H(Hx)
--  HP |- P ==> P
--   HP |- HP
--   HP, P |- P
thm_impl_refl = prove (hoas (_Xi % _H % fun (\p -> p ==> p))) $
    newName $ \pvar ->
    lambdaXiRule pvar hhRule $ \hp ->
    implAbstract hp (\p -> p)

_True = _Xi % _H % _H

-- |- ΞHH
--  |- H(Hx)
--  Hx |- Hx
thm_true_true = prove (hoas (_Xi % _H % _H)) $
    newName $ \x ->
    xiRule x hhRule id

-- |- H True
--  |- H(ΞHH)
--   |- H(Hx)
--   Hx |- H(Hx)
thm_h_true = prove (hoas (_H % _True)) $
    newName $ \x ->
    hxiRule x hhRule (\_ -> hhRule)

_U = _K % _True

-- |- U x
--  |- K True x
--   |- True
u_everything = conversion unfold_K (theorem thm_true_true)

f ° g = fun (\x -> f % (g % x))
-- (f ° g) x -> f (g x)
unfold_compose = convBetaReduce
-- f (g x) -> (f ° g) x
-- A(Bx) -> A(B((\x.x)x)) -> A((\x. Bx)x) -> (\x. A(Bx))x
fold_compose = mconcat [
    convInAppR (convInAppR convExpandId),
    convInAppR (convExpandRight),
    convExpandRight ]

a --> b = fun (\f -> _Xi % a % (b ° f))

-- ΞA(B°f) -> (A --> B)f
Just fold_arrow = convEquiv (hoas (_Xi % a % (b ° f))) (hoas ((a --> b) % f))
    where
    a = name (toEnum 0)
    b = name (toEnum 1)
    f = name (toEnum 2)
-- (A --> B)f -> ΞA(B°f)
unfold_arrow = convBetaReduce

_L = _U --> _H

-- LA |- H(Ax)
--  LA |- (H°A)x
--   LA |- Ux
--   LA |- ΞU(H°A)
--    LA |- (U-->H)A
--     LA |- LA
la_hax la = 
    conversion fold_compose $
    implRule (hoas _U) u_everything $
    conversion fold_arrow la

-- |- LA
--  |- (U-->H)A
--   |- ΞU(H°A)
--    |- H(Ux)
--     |- H True
--    Ux |- (H°A)x
--     Ux |- H(Ax)
hax_la x hax = 
    conversion unfold_arrow $
    xiRule x (conversion (convInAppR unfold_K) (theorem thm_h_true)) $
    (\_ -> conversion unfold_compose hax)

-- |- LH
--  |- H(Hx)
thm_lh = prove (hoas (_L % _H)) $
    newName $ \x -> 
    hax_la x hhRule


-- |- LU
--  |- H(Ux)
--   |- H True
thm_lu = prove (hoas (_L % _U)) $
    newName $ \x ->
    hax_la x (conversion (convInAppR unfold_K) (theorem thm_h_true))


-- LA, LB |- L(A --> B)
--  LA, LB |- H((A-->B)x)
--   LA, LB |- H(ΞA(B°x))
--    LA, LB |- H(Ay)
--     LA, LB |- LA
--    LA, LB, Ay |- H((B°x)y)
--     LA, LB, Ay |- H(B(xy))
arrowTypeHelper la lb = 
    newName $ \x ->
    hax_la x $
    conversion (convInAppR unfold_arrow) $
    newName $ \y ->
    hxiRule y (la_hax la)
              (\_ -> conversion (convInAppR unfold_compose) (la_hax lb))

-- |- LL
--  |- L(U --> H)
--   |- LU
--   |- LH
thm_ll = prove (hoas (_L % _L)) $ arrowTypeHelper (theorem thm_lu) (theorem thm_lh)

-- |- ΞL(\A. ΞL(\B. L(A --> B)))
--  |- H(LA)
--   |- LL
--  LA |- ΞL(\B. L(A --> B))
--   LA |- H(LB)
--    LA |- LL
--   LA,LB |- L(A --> B)
--    LA,LB |- LA
--    LA,LB |- LB
thm_arrow_type = prove (hoas (_Xi % _L % fun (\a -> _Xi % _L % fun (\b -> _L % (a --> b))))) $
    newName $ \a ->
    lambdaXiRule a (la_hax (theorem thm_ll)) $ \la ->
    newName $ \b ->
    lambdaXiRule b (la_hax (theorem thm_ll)) $ \lb ->
    arrowTypeHelper la lb


