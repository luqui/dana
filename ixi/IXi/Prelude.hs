module IXi.Tactics where

import IXi.Tactic
import IXi.HOAS
import IXi.Term
import IXi.Helpers
import IXi.Conversion
import qualified IXi.Sequent as Sequent
import Data.Monoid (mconcat, mappend)

_K = fun (\x -> fun (\y -> x))
_I = fun (\x -> x)

-- X -> (\x. x) X -> (\y. (\x. x) X) Y -> (\x. \y. x) X Y
convExpandK y = mconcat [
    convExpandId,
    convExpandConst y,
    convInAppL convExpandLambda ]

convReduceK = mconcat [convInAppL convBetaReduce, convBetaReduce]

p ==> q = _Xi % (_K % p) % (_K % q)

-- |- Q
--  |- KQI
--   |- Ξ(KP)(KQ)
--    |- P ==> Q
--   |- KPI
--    |- P
modusPonens :: Exp -> Tactic -> Tactic -> Tactic
modusPonens p pqPf pPf = 
    conversion (convExpandK (hoas _I)) $
    implRule (hoas (_K % p % _I)) (conversion convReduceK pPf) pqPf

-- |- P ==> Q
--  |- Ξ(KP)(KQ)
--   |- H(KPx)
--    |- HP
--   KPx |- KQx
--    P |- Q
implAbstract :: Tactic -> (Hypothesis -> Tactic) -> Tactic
implAbstract hpPf pqPf = 
    newName $ \name -> 
    xiRule name (conversion (convInAppR convReduceK) hpPf)
                (\kpx -> conversion convReduceK (pqPf (conversion (convExpandK (NameVar name)) kpx)))


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
impl_refl = prove (hoas (_Xi % _H % fun (\p -> p ==> p))) $
    newName $ \pvar ->
    lambdaXiRule pvar hhRule $ \hp ->
    implAbstract hp (\p -> p)

_True = _Xi % _H % _H

-- |- ΞHH
--  |- H(Hx)
--  Hx |- Hx
true_true = prove (hoas (_Xi % _H % _H)) $
    newName $ \x ->
    xiRule x hhRule id

-- |- H True
--  |- H(ΞHH)
--   |- H(Hx)
--   Hx |- H(Hx)
h_true = prove (hoas (_H % _True)) $
    newName $ \x ->
    hxiRule x hhRule (\_ -> hhRule)

_U = _K % _True

-- |- U x
--  |- K True x
--   |- True
u_everything = conversion convReduceK (theorem true_true)

f ° g = fun (\x -> f % (g % x))

-- A(Bx) -> A(B((\x.x)x)) -> A((\x. Bx)x) -> (\x. A(Bx))x
convExpandCompose = mconcat [
    convInAppR (convInAppR convExpandId),
    convInAppR (convExpandRight),
    convExpandRight ]

a --> b = fun (\f -> _Xi % a % (b ° f))

-- ΞA(B°f) -> (A --> B)f
Just convExpandArrow = convEquiv (hoas (_Xi % a % (b ° f))) (hoas ((a --> b) % f))
    where
    a = name (toEnum 0)
    b = name (toEnum 1)
    f = name (toEnum 2)

_L = _U --> _H

-- LA |- H(Ax)
--  LA |- (H°A)x
--   LA |- Ux
--   LA |- ΞU(H°A)
--    LA |- (U-->H)A
--     LA |- LA
la_hax la = 
    conversion convExpandCompose $
    implRule (hoas _U) u_everything $
    conversion convExpandArrow la

-- |- LA
--  |- (U-->H)A
--   |- ΞU(H°A)
--    |- H(Ux)
--     |- H True
--    Ux |- (H°A)x
--     Ux |- H(Ax)
hax_la x hax = 
    conversion convBetaReduce $
    xiRule x (conversion (convInAppR convReduceK) (theorem h_true)) $
    (\_ -> conversion convBetaReduce hax)

-- |- LH
--  |- H(Hx)
lh = prove (hoas (_L % _H)) $
    newName $ \x -> 
    hax_la x hhRule


-- |- LU
--  |- H(Ux)
--   |- H True
lu = prove (hoas (_L % _U)) $
    newName $ \x ->
    hax_la x (conversion (convInAppR convReduceK) (theorem h_true))


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
    conversion (convInAppR convBetaReduce) $
    newName $ \y ->
    hxiRule y (la_hax la)
              (\_ -> conversion (convInAppR convBetaReduce) (la_hax lb))

-- |- LL
--  |- L(U --> H)
--   |- LU
--   |- LH
ll = prove (hoas (_L % _L)) $ arrowTypeHelper (theorem lu) (theorem lh)

-- |- ΞL(\A. ΞL(\B. L(A --> B)))
--  |- H(LA)
--   |- LL
--  LA |- ΞL(\B. L(A --> B))
--   LA |- H(LB)
--    LA |- LL
--   LA,LB |- L(A --> B)
--    LA,LB |- LA
--    LA,LB |- LB
arrow_type = prove (hoas (_Xi % _L % fun (\a -> _Xi % _L % fun (\b -> _L % (a --> b))))) $
    newName $ \a ->
    lambdaXiRule a (la_hax (theorem ll)) $ \la ->
    newName $ \b ->
    lambdaXiRule b (la_hax (theorem ll)) $ \lb ->
    arrowTypeHelper la lb


