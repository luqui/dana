module IXi.Helpers where

import IXi.Term
import Data.Monoid (Monoid(..))

-- X
-- -> (\x. \y. x) X Y
-- -> (\y. X) Y
convExpandConst y = mconcat [
    convExpandK y,
    convInAppL convBetaReduce ]

-- X (Y Z) 
-- -> (\x. X) Z (Y Z) 
-- -> (\z. (\x. X) z (Y z)) Z 
-- -> (\z. X (Y z)) Z
convExpandB :: (Eq n) => Conversion n
convExpandB = convDep $ \t ->
    case t of
        x :% (y :% z) -> Just $ mconcat [
            (convInAppL . convExpandConst) z,
            convExpandS,
            (convInAppL . convInLambda . convInAppL) convBetaReduce ]
        _ -> Nothing

-- X Z Y
-- -> X Z ((\x. Y) Z)
-- -> (\z. X z ((\x. Y) z)) Z
-- -> (\z. X z (Y z)) Z
convExpandC :: (Eq n) => Conversion n
convExpandC = convDep $ \t ->
    case t of
        x :% z :% y -> Just $ mconcat [
            (convInAppR . convExpandConst) z,
            convExpandS,
            (convInAppL . convInLambda . convInAppR) convBetaReduce ]
        _ -> Nothing
