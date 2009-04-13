module IXi.Interface where

import IXi.Term
import IXi.Parser
import IXi.Sequent
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Data.List (isPrefixOf)
import qualified System.Console.Editline as EL
import System.Exit (exitSuccess)

dispSequent :: Sequent -> IO ()
dispSequent (cx :|- goal) = do
    mapM_ (putStrLn . showTerm) cx
    putStrLn "----"
    putStrLn . showTerm $ goal

showSequent :: Sequent -> String
showSequent (cx :|- goal) = "... |- " ++ showTerm goal

type InterfaceM = ReaderT EL.EditLine (StateT [Sequent] IO)

askLine :: InterfaceM String
askLine = do
    l <- liftIO . EL.elGets =<< ask
    case l of
        Nothing -> liftIO exitSuccess
        Just r -> return (init r)

chomp :: String -> String
chomp = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ')

cmd1 :: String -> String -> Maybe String
cmd1 name inp | name `isPrefixOf` inp = Just $ chomp (drop (length name) inp)
              | otherwise = Nothing

cmds :: a -> [(String, String -> a)] -> String -> a
cmds def [] _ = def
cmds def ((name, f):rest) inp = maybe (cmds def rest inp) f $ cmd1 name inp

loop :: InterfaceM ()
loop = do
    seqs <- get
    case seqs of
        [] -> return ()
        (s:ss) -> do
            mapM_ (liftIO . putStrLn . showSequent) ss
            liftIO $ putStrLn ""
            liftIO $ dispSequent s
            askLine >>= cmds invalid [
                "rotate" --> \_ -> put (ss ++ [s]),
                "assumption" --> \_ -> tactic assumption,
                "mp" --> \t -> maybe invalid (tactic . modusPonens) (parseTerm t),
                "abstract" --> \v -> tactic (abstract v),
                "abswf" --> \v -> tactic (univWF v),
                "wf" --> \_ -> tactic wfwf
              ]
            loop
    where
    (-->) = (,)
    invalid = liftIO $ putStrLn "Invalid input"

main = do
    el <- EL.elInit "ixi"
    evalStateT (runReaderT loop el) [ [] :|- Xi :% H :% H ]

tactic :: Tactic -> InterfaceM ()
tactic tac = do
    (s:ss) <- get
    case tac s of
        Right new -> put (new ++ ss)
        Left err -> liftIO $ putStrLn err  
