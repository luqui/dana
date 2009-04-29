module IXi.Prelude where

import IXi.Term
import IXi.Proof
import Data.Monoid (Monoid(..))

-- Naming conventions:
--   _ : definition (must be closed)
--   prove_ : inference rule
--   convert_ : conversion
--   prop_ : theorem

-- K, the constant function.  Kxy = x
_K = Lambda (Lambda (Var 1))
-- (\x. \y. x) A B -> (\y. A) B -> A
convert_redK = convInAppL convBetaReduce `mappend` convBetaReduce
-- A -> (\x. \y. x) A B
convert_expK = convExpandK

-- I, the identity function.  Ix = x
_I = Lambda (Var 0)

-- Material implication.
a --> b = Xi :% (_K :% a) :% (_K :% b)

prove_impl_abs :: Proof n -> Proof n -> Proof n
-- |- Ξ(KA)(KB)
--  |- H(KAx)
--   |- HA    -- pfH
--  KAx |- KBx
--   A |- KBx
--    A |- B  -- pfB
prove_impl_abs pfH pfB = 
    xiRule (\_ -> conversion (convInAppR convert_redK) pfH)
           (\_ -> hypConversion 0 convert_redK (conversion convert_redK pfB))

-- |- B
--  |- KBI
--   |- KAI
--    |- A        -- pfA
--   |- Ξ(KA)(KB) -- pfImpl
prove_impl_mp a pfA pfImpl =
    conversion (convert_expK _I) $
        implRule (_K :% a) (conversion convert_redK pfA) pfImpl

-- True, the true proposition.
_True = Xi :% H :% H

-- |- H(ΞHH)
--  |- H(Hx)
--  Hx |- H(Hx)
Right prop_HTrue = prove (H :% _True) (hxiRule (\_ -> hhRule) (\_ -> hhRule))

Right prop_True = prove _True (xiRule (\_ -> hhRule) (\_ -> hypothesis 0))

-- U, the type of all objects.
_U = _K :% _True

-- L, the type of types.
_L = Lambda (Xi :% _U :% Lambda (H :% (Var 1 :% Var 0)))

-- |- LU  =  (\x. ΞU(\y. H(xy))) U
--  |- ΞU(\y. H(Uy))
--   |- H(Uy)
--    |- H True   -- prop_HTrue
--   Uy |- (\y. H(Uy))y
--    Uy |- H(Uy)
--     Uy |- H True   -- prop_HTrue
Right prop_LU = prove (_L :% _U) $
    conversion convBetaReduce $
        xiRule (\_ -> conversion (convInAppR convert_redK) (theorem prop_HTrue))
               (\_ -> conversion (convBetaReduce `mappend` convInAppR convert_redK) (theorem prop_HTrue))

-- |- LL  =  (\x. ΞU(\y. H(xy))) L
--  |- ΞU(\y. H(Ly))
--   |- H(Uy)
--    |- H True    -- prop_HTrue
--   Uy |- (\y. H(Ly))y
--    Uy |- H(Ly)   =  H((\x. ΞU(\y. H(xy)))y)
--     Uy |- H(ΞU(\z. H(yz)))
--      Uy |- H(Uz)
--       Uy |- H True  -- prop_HTrue
--      Uy, Uz |- H((\z. H(yz)) z)
--       Uy, Uz |- H(H(yz))
Right prop_LL = prove (_L :% _L) $
    conversion convBetaReduce $
        xiRule (\_ -> conversion (convInAppR convert_redK) (theorem prop_HTrue))
               (\_ -> conversion (convBetaReduce `mappend` convInAppR convBetaReduce) $
                    hxiRule (\_ -> conversion (convInAppR convert_redK) (theorem prop_HTrue))
                            (\_ -> conversion (convInAppR convBetaReduce) hhRule))

--  |- H(Ax)
--   |- (\y. H(Ay))x
--    |- Ux
--     |- True              -- prop_True
--    |- ΞU(\y. H(Ay))
--     |- (\x. ΞU(\y. H(xy))) A  =  LA   -- pfLA
