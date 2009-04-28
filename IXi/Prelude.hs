module IXi.Prelude where

import IXi.Term
import IXi.Helpers
import IXi.Proof
import Data.Maybe (fromJust)
import Debug.Trace

_K = Lambda (Lambda (Var 1))
_I = Lambda (Var 0)

a --> b = Xi :% (_K :% a) :% (_K :% b)

traced x = trace (show x) x

kxy_conv_x x y = fromJust
               $ redAppL convBeta >~> convBeta 
               $ _K :% x :% y
