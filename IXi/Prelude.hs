module IXi.Prelude where

import IXi.Term
import IXi.Proof
import Data.Monoid (Monoid(..))

_K = Lambda (Lambda (Var 1))
_I = Lambda (Var 0)

-- (\x. \y. x) A B -> (\y. A) B -> A
reduceK = convInAppL convBetaReduce `mappend` convBetaReduce

a --> b = Xi :% (_K :% a) :% (_K :% b)

proveImpl :: Proof n -> Proof n -> Proof n
-- |- Ξ(KA)(KB)
--  |- H(KAx)
--   |- HA    -- pfH
--  KAx |- KBx
--   A |- KBx
--    A |- B  -- pfB
proveImpl pfH pfB = 
    xiRule (\_ -> conversion (convInAppR reduceK) pfH)
           (\_ -> hypConversion 0 reduceK (conversion reduceK pfB))
