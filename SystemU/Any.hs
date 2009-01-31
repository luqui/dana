module SystemU.Any (Any, toAny, fromAny) where

import qualified GHC.Prim
import Unsafe.Coerce (unsafeCoerce)

newtype Any = Any GHC.Prim.Any

toAny :: a -> Any
toAny = unsafeCoerce

fromAny :: Any -> a
fromAny = unsafeCoerce
