module IXi.Tactics where

import IXi.Tactic
import IXi.HOAS
import IXi.Term
import IXi.Helpers
import IXi.Conversion
import qualified IXi.Sequent as Sequent
import Data.Monoid (mconcat, mappend)

_K = fun (\x -> fun (\y -> x))
fold_K y = mconcat [ convExpandConst (hoas y)                -- (\y.X)Y
                   , convInAppL (convInLambda convExpandId)  -- (\y.(\x.x)X)Y
                   , convInAppL (convExpandLambda)           -- (\xy.X)Y
                   ]
-- Kxy -> x
unfold_K = unfoldn 2


_I = fun (\x -> x)
-- x -> Ix
fold_I = foldn 1 (hoas _I)
-- Ix -> x
unfold_I = unfoldn 1


_Impl = fun (\p -> fun (\q -> _Xi % (_K % p) % (_K % q)))
p ==> q = _Impl % p % q

fold_Impl = foldn 2 (hoas _Impl)
unfold_Impl = unfoldn 2


-- |- Q
--  |- KQI
--   |- Ξ(KP)(KQ)
--    |- P ==> Q
--   |- KPI
--    |- P
modusPonens :: Exp -> Tactic -> Tactic -> Tactic
modusPonens p pqPf pPf = 
    conversion (fold_K _I) $
    implRule (hoas (_K % p % _I)) (conversion unfold_K pPf) 
                                  (conversion fold_Impl pqPf)

-- |- P ==> Q
--  |- Ξ(KP)(KQ)
--   |- H(KPx)
--    |- HP
--   KPx |- KQx
--    P |- Q
implAbstract :: Tactic -> (Hypothesis -> Tactic) -> Tactic
implAbstract hpPf pqPf = 
    newName $ \n -> 
    conversion unfold_Impl $
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

_Compose = fun (\f -> fun (\g -> fun (\x -> f % (g % x))))
f ° g = _Compose % f % g

fold_Compose = foldn 3 (hoas _Compose)
unfold_Compose = unfoldn 3

_Arrow = fun (\a -> fun (\b -> fun (\f -> _Xi % a % (b ° f))))
a --> b = _Arrow % a % b

fold_arrow = foldn 3 (hoas _Arrow)
unfold_arrow = unfoldn 3

_L = _U --> _H

-- LA |- H(Ax)
--  LA |- (H°A)x
--   LA |- Ux
--   LA |- ΞU(H°A)
--    LA |- (U-->H)A
--     LA |- LA
la_hax la = 
    conversion fold_Compose $
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
    (\_ -> conversion unfold_Compose hax)

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
              (\_ -> conversion (convInAppR unfold_Compose) (la_hax lb))

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
