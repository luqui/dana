module IXi.Tactics where

import IXi.Tactic
import IXi.HOAS
import IXi.Term
import IXi.Helpers
import IXi.Conversion
import Data.Monoid (mconcat)

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
u_everything x = conversion convReduceK (theorem true_true)

f ° g = fun (\x -> f % (g % x))

-- A(Bx) -> A(B((\x.x)x)) -> A((\x. Bx)x) -> (\x. A(Bx))x
convExpandCompose = mconcat [
    convInAppR (convInAppR convExpandId),
    convInAppR (convExpandRight),
    convExpandRight ]

a --> b = fun (\f -> _Xi % a % (b ° f))

_L = _U --> _H

-- |- ΞAB
--  |- H(Ax)
--   |- (H°A)x
--    |- Ux
--    |- ΞU(H°A)
--     |- LA
--  Ax |- Bx
xiLRule x lPf abPf = 
    xiRule x 
        (conversion convExpandCompose 
            (implRule (hoas _U) (u_everything (name x)) lPf)) 
        abPf

-- |- LH
--  |- (U --> H)H
--   |- ΞU(H°H)
--    |- H(Ux)
--     |- H True
--    Ux |- (H°H)x
--     Ux |- H(Hx)
lh = prove (hoas (_L % _H)) $
    conversion convBetaReduce $
    newName $ \x ->
    xiRule x (conversion (convInAppR convReduceK) (theorem h_true))
             (\h -> conversion convBetaReduce hhRule)
