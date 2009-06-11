module IXi.Tactics where

import IXi.Tactic
import IXi.HOAS
import IXi.Term
import IXi.Helpers
import IXi.Conversion

_K = fun (\x -> fun (\y -> x))
_I = fun (\x -> x)

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
