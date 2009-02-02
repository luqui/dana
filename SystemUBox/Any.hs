module SystemUBox.Any (Any, toAny, fromAny) where

import qualified GHC.Prim
import Unsafe.Coerce (unsafeCoerce)

newtype Any = Any GHC.Prim.Any

toAny :: a -> Any
toAny = Any . unsafeCoerce

fromAny :: Any -> a
fromAny (Any x) = unsafeCoerce x
