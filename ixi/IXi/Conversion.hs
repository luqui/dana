module IXi.Conversion 
    ( Conversion, convert
    , convId, convTrans
    , convInLambda, convInAppL, convInAppR
    , convEtaContract, convEtaExpand
    , convBetaReduce

    , convExpandId, convExpandConst
    , convExpandProj, convExpandLeft, convExpandRight
    , convExpandLambda
    )
where

import IXi.Term
import Control.Monad ((>=>))
import Control.Applicative
import Data.Monoid

data Conversion
    = ConvId
    | Conversion :=>: Conversion
    | ConvInLambda Conversion
    | ConvInAppL Conversion
    | ConvInAppR Conversion

    | ConvEtaContract
    | ConvEtaExpand
    | ConvBetaReduce

    | ConvExpandId
    | ConvExpandConst Term

    | ConvExpandProj
    | ConvExpandLeft
    | ConvExpandRight
    | ConvExpandLambda
    deriving (Show)

instance Monoid Conversion where
    mempty = convId
    mappend = convTrans

convId = ConvId
convTrans = (:=>:)
convInLambda = ConvInLambda
convInAppL = ConvInAppL
convInAppR = ConvInAppR
convEtaContract = ConvEtaContract
convEtaExpand = ConvEtaExpand
convBetaReduce = ConvBetaReduce
convExpandId = ConvExpandId
convExpandConst = ConvExpandConst
convExpandProj = ConvExpandProj
convExpandLeft = ConvExpandLeft
convExpandRight = ConvExpandRight
convExpandLambda = ConvExpandLambda

convert :: Conversion -> Term -> Maybe Term
-- X -> X
convert ConvId t = Just t
-- (X -> Y) (Y -> Z) -> (X -> Z)
convert (c :=>: c') t = (convert c >=> convert c') t
-- (X -> Y) -> (\x. X -> \x. y)
convert (ConvInLambda c) (Lambda t) = Lambda <$> convert c t
-- (X -> Y) -> (X Z -> Y Z)
convert (ConvInAppL c) (t :% u) = (:% u) <$> convert c t
-- (X -> Y) -> (Z X -> Z Y)
convert (ConvInAppR c) (t :% u) = (t :%) <$> convert c u

-- \x. X x -> X    (x not free in X)
convert ConvEtaContract (Lambda (t :% Var 0)) = unfree 0 t
-- X -> \x. X x    (x not free in X)
convert ConvEtaExpand t = Just (Lambda (quote 0 t :% Var 0))
-- (\x. X) Y -> X[Y/x]
convert ConvBetaReduce (Lambda t :% u) = Just (subst 0 u t)

-- X -> (\x. x) X
convert ConvExpandId t = Just (Lambda (Var 0) :% t)
-- X -> (\x. X) Y
convert (ConvExpandConst c) t = Just (Lambda (quote 0 t) :% c)

-- (\x. A) Z ((\x. B) Z) -> (\x. A B) Z
convert ConvExpandProj (Lambda a :% z :% (Lambda b :% z'))
    | z == z' = Just (Lambda (a :% b) :% z)
-- (\x. A) C B -> (\x. A B) C      (x not free in B)
convert ConvExpandLeft (Lambda a :% c :% b) 
    = Just (Lambda (a :% quote 0 b) :% c)
-- A ((\x. B) C) -> (\x. A B) C    (x not free in A)
convert ConvExpandRight (a :% (Lambda b :% c))
    = Just (Lambda (quote 0 a :% b) :% c)
-- \y. (\x. A) C -> (\x. \y. A) C  (y not free in C)
convert ConvExpandLambda (Lambda (Lambda a :% c))
    = (Lambda (Lambda (swapVars a)) :%) <$> unfree 0 c
convert _ _ = Nothing
