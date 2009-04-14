module IXi.TermZipper where

import IXi.Term
import qualified Data.Set as Set

data DTerm
    = DTop
    | DLam String DTerm
    | DAppL DTerm Term
    | DAppR Term DTerm

data TermZipper = TermZipper { tzFocus :: Term, tzContext :: DTerm }

type Motion = TermZipper -> Maybe TermZipper

goLambda :: Motion
goLambda (TermZipper (Lam v t) cx) = Just (TermZipper t (DLam v cx))
goLambda _ = Nothing

goLeftApp :: Motion
goLeftApp (TermZipper (x :% y) cx) = Just (TermZipper x (DAppL cx y))
goLeftApp _ = Nothing

goRightApp :: Motion
goRightApp (TermZipper (x :% y) cx) = Just (TermZipper y (DAppR x cx))
goRightApp _ = Nothing

goUp :: Motion
goUp (TermZipper t DTop) = Nothing
goUp (TermZipper t (DLam v cx)) = Just (TermZipper (Lam v t) cx)
goUp (TermZipper t (DAppL cx y)) = Just (TermZipper (t :% y) cx)
goUp (TermZipper t (DAppR x cx)) = Just (TermZipper (x :% t) cx)

termUnzip :: TermZipper -> Term
termUnzip tz = maybe (tzFocus tz) termUnzip (goUp tz)

inZipper :: (Term -> Term) -> TermZipper -> TermZipper
inZipper f (TermZipper t cx) = TermZipper (f t) cx

inZipperM :: (Term -> Maybe Term) -> Motion
inZipperM f (TermZipper t cx) = fmap (\r -> TermZipper r cx) (f t)

boundVars :: DTerm -> Set.Set Var
boundVars DTop = Set.empty
boundVars (DLam v t) = Set.insert v (boundVars t)
boundVars (DAppL cx t) = boundVars cx
boundVars (DAppR t cx) = boundVars cx
