module IXi.Prelude where

import IXi.Term
import IXi.Proof
import IXi.Helpers
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
a ==> b = Xi :% (_K :% a) :% (_K :% b)

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
prove_HAx_from_LA pfLA = 
    conversion conv1 $
        implRule _U (conversion convert_redK (theorem prop_True))
                    (conversion conv2 pfLA)

    where
    Just conv1 = convEquiv (H :% (nA :% nx))
                           (Lambda (H :% (nA :% Var 0)) :% nx)
    Just conv2 = convEquiv (Xi :% nU :% Lambda (H :% (nA :% Var 0)))
                           (Lambda (Xi :% nU :% Lambda (H :% (Var 1 :% Var 0))) :% nA)
    [nA,nx,nU] = map (NameVar . toEnum) [0,1,2]

-- |- ΞAB
--  |- H(Ax)     -- prove_HAx_from_LA pfLA
--  Ax |- Bx     -- pfB x
prove_Xi_with_L pfLA pfB = xiRule (\_ -> prove_HAx_from_LA pfLA) pfB


-- Function type  (A -> B = \f. ΞA(\x. B (f x)))
_F = Lambda (Lambda (Lambda (Xi :% Var 0 :% Lambda (Var 2 :% (Var 1 :% Var 0)))))

-- |- ΞL(\A. ΞL(\B. L(FAB)))
--  |- LL             -- prop_LL
--  LA |- ΞL(\B. L(FAB))
--   LA |- LL         -- prop_LL
--   LA, LB |- L(FAB)      =  L((\A. \B. \f. ΞA(\x. B (f x))) A B)
--    LA, LB |- L((\B. \f. ΞA(\x. B (f x))) B)
--     LA, LB |- L(\f. ΞA(\x. B (f x)))  = (\z. ΞU(\x. H(zx))) (\f. ΞA(\x. B (f x)))
--      LA, LB |- ΞU(\x. H((\f. ΞA(\y. B (f y)))x))
--       LA, LB |- ΞU(\x. H(ΞA(\y. B (x y))))
--        LA, LB |- H(Uz)
--         LA, LB |- H True   -- prop_True
--        LA, LB, Uz |- (\x. H(ΞA(\y. B (x y)))) z
--         LA, LB, Uz |- H(ΞA(\y. B (z y)))
--          LA, LB, Uz |- LA
--          LA, LB, Uz, Ay |- H((\y. B (z y)) y)
--           LA, LB, Uz, Ay |- H (B (z y))
--            LA, LB, Uz, Ay |- LB
