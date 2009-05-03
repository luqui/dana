import Control.Monad.CC
import Control.Monad.State

callCC f = reset (\p -> f (shift p . const . return))

easy :: (Monad m) => (CCT r m a -> CCT r m b) -> (CCT r m a -> CCT r m c) -> (CCT r m a -> CCT r m (b,c))
easy f g z = callCC $ \cont -> do
    a <- reset (\m -> f (shift m (\del -> do
            z' <- z
            a <- del (return z')
            b <- g (return z')
            cont (a,b))))
    b <- g z
    return (a,b)

-- Should return 1
test = execState (runCCT (easy f g (modify (+1)))) 0
    where
    f x = x >> return ()
    g x = x >> return ()
