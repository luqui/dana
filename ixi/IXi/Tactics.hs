module IXi.Tactics where

import IXi.Tactic
import IXi.Term
import IXi.Conversion
import IXi.Helpers (convExpandK, convReduceK)
import Control.Applicative

_K = Lambda (Lambda (Var 1))

-- |- R
--  |- KRx
--   |- KGx
--    |- G        -- goalproof
--   |- Ξ(KG)(KR)
--    |- H(KGx)
--     |- HG      -- hproof
--    KGx |- KRx
--     G |- KRx
--      G |- R    -- rest
--
assert :: (Alternative f) => Term -> Tactic f -> Tactic f -> (Hypothesis -> Tactic f) -> Tactic f
assert goal hproof goalproof rest = withFreshName $ \xname -> 
    let x = NameVar xname in

    conversion (convExpandK x) $
    implRule (_K :% goal)
        (conversion convReduceK goalproof)
        (xiRule xname (conversion (convInAppR convReduceK) hproof)
                      (\hyp -> hypConversion hyp convReduceK 
                               (conversion convReduceK (rest hyp))))
