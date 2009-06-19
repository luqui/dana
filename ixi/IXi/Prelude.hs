module IXi.Prelude where

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
--   |- KPI
--    |- P
--   |- Ξ(KP)(KQ)
--    |- P ==> Q
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

fold_Arrow = foldn 3 (hoas _Arrow)
unfold_Arrow = unfoldn 3

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
    conversion fold_Arrow la

-- |- LA
--  |- (U-->H)A
--   |- ΞU(H°A)
--    |- H(Ux)
--     |- H True
--    Ux |- (H°A)x
--     Ux |- H(Ax)
hax_la x hax = 
    conversion unfold_Arrow $
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
    conversion (convInAppR unfold_Arrow) $
    newName $ \y ->
    hxiRule y (la_hax la)
              (\_ -> conversion (convInAppR unfold_Compose) (la_hax lb))

-- |- LL
--  |- L(U --> H)
--   |- LU
--   |- LH
thm_ll = prove (hoas (_L % _L)) $ 
    arrowTypeHelper (theorem thm_lu) (theorem thm_lh)

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


-- (A-->B)f, Ax |- B(fx)
--  (A-->B)f, Ax |- (B°f)x
--   (A-->B)f, Ax |- Ax
--   (A-->B)f, Ax |- ΞA(B°f)
--    (A-->B)f, Ax |- (A-->B)f
arrowApplyHelper a pfABf pfAx = 
    conversion fold_Compose $
    implRule (hoas a) pfAx (conversion fold_Arrow pfABf)

pullName name rest = inspect (\seq -> conversion (convAbstract name (Sequent.goal seq)) rest)

-- |- ΞL(\A. ΞL(\B. Ξ(A-->B)(\f. ΞA(\x. B(fx)))))
--  |- LL
--  LA |- ΞL(\B. Ξ(A-->B)(\f. ΞA(\x. B(fx))))
--   LA |- LL
--   LA, LB |- Ξ(A-->B)(\f. ΞA(\x. B(fx)))
--    LA, LB |- L(A-->B)
--     LA, LB |- (\B. L(A-->B))B
--      LA, LB |- LB
--      LA, LB |- ΞL(\B. L(A --> B))
--       LA, LB |- (\A. ΞL(\B. L(A --> B))A
--        LA, LB |- LA
--        LA, LB |- ΞL(\A. ΞL(\B. L(A --> B)))
--    LA, LB, (A-->B)f |- ΞA(\x. B(fx))
--     LA, LB, (A-->B)f |- LA
--     LA, LB, (A-->B)f, Ax |- B(fx)
--      {arrowApplyHelper}
thm_arrow_apply = prove (hoas $
        _Xi % _L % fun (\a -> _Xi % _L % fun (\b -> 
        _Xi % (a --> b) % fun (\f -> _Xi % a % fun (\x ->
        b % (f % x)))))) $
    newName $ \a ->
    lambdaXiRule a (la_hax (theorem thm_ll)) $ \la ->
    newName $ \b ->
    lambdaXiRule b (la_hax (theorem thm_ll)) $ \lb ->
    newName $ \f ->
    lambdaXiRule f (la_hax $
        pullName b $ implRule (hoas _L) lb $
        pullName a $ implRule (hoas _L) la $
        theorem thm_arrow_type) $ \abf ->
    newName $ \x ->
    lambdaXiRule x (la_hax la) $ \ax ->
    arrowApplyHelper (name a) abf ax
