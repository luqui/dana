module IXi.Helpers where

import IXi.Term
import Control.Applicative
import Data.Maybe (fromJust)
import Control.Monad.Writer
import Data.List (foldl')

betaNFsteps :: (Eq n) => Term n -> [Conversion n]
betaNFsteps = execWriter . go
    where
    go (Lambda t) = Lambda <$> censor' convLambda (go t)
    go (t :% u) = do
        t' <- censor' (`convAppL` u) (go t)
        case t' of
            Lambda {} -> do
                let conv = fromJust (convBeta (t' :% u))
                tell [conv]
                go (convTo conv)
            _ -> ((t' :%) <$> censor' (t' `convAppR`) (go u))
    go x = return x

    censor' = censor . map

betaNF :: (Eq n) => Term n -> Conversion n
betaNF term = foldl' safeTrans (convId term) (betaNFsteps term)

etaNF :: (Eq n) => Term n -> Conversion n
etaNF (Lambda (t :% Var 0)) | Just t' <- unfree 0 t = convSym (convEta t') `safeTrans` etaNF t'
etaNF (Lambda t) = convLambda (etaNF t)
etaNF (t :% u) = let conv = etaNF t in
                 convAppL conv u `safeTrans` convAppR (convTo conv) (etaNF u)
etaNF x = convId x

infixr 5 >~>
(>~>) :: (Eq n) => (Term n -> Conversion n) -> (Term n -> Conversion n) -> (Term n -> Conversion n)
(f >~> g) t = let conv = f t in conv `safeTrans` g (convTo conv)

safeTrans a b =
    case convTrans a b of
        Just c -> c
        Nothing -> error $ "Failed to unify: " ++ showConv a ++ " and " ++ showConv b

showConv c = showTerm (const "*") (convFrom c) ++ " <-> " ++ showTerm (const "*") (convTo c)
