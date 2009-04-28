module IXi.Prelude where

import IXi.Term
import IXi.Proof

_K = Lambda (Lambda (Var 1))
_I = Lambda (Var 0)

a --> b = Xi :% (_K :% a) :% (_K :% b)
