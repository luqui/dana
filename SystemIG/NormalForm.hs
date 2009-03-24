module SystemIG.NormalForm where

import SystemIG.Calculus
import Data.Maybe (fromJust)

rwhnf :: Term -> Conversion
rwhnf src@(t :* u) = fromJust $ do
    let conv = rwhnf t
    case snd (convTerms conv) of
        Lam z -> do
            redlam <- convBeta (Lam z :* u)
            let next = rwhnf (snd (convTerms redlam))
            convChain [convAppL conv u, redlam, next]
        t' -> return $ convAppL conv u
rwhnf t = convId t
