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
import qualified Data.Map as Map

dispSequent :: Sequent -> IO ()
dispSequent (cx :|- goal) = do
    mapM_ (putStrLn . showTerm) cx
    putStrLn "----"
    putStrLn . showTerm $ goal

showSequent :: Sequent -> String
showSequent (cx :|- goal) = "... |- " ++ showTerm goal

showDef :: (Var,Term) -> String
showDef (v,t) = v ++ " = " ++ showTerm t

type InterfaceM = ReaderT EL.EditLine (StateT Context IO)

data Context = Context { cxSeqs :: [Sequent], cxDefs :: Map.Map Var Term }

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
    cx  <- get
    case cxSeqs cx of
        [] -> return ()
        (s:ss) -> do
            mapM_ (const (liftIO (putStrLn ""))) [1..5]
            mapM_ (liftIO . putStrLn . showDef) (Map.assocs (cxDefs cx))
            liftIO $ putStrLn ""
            mapM_ (liftIO . putStrLn . showSequent) ss
            liftIO $ putStrLn ""
            liftIO $ dispSequent s
            askLine >>= cmds invalid [
                "rotate" --> \_ -> put (cx { cxSeqs = ss ++ [s] }),
                "assumption" --> \_ -> tactic assumption,
                "mp" --> \t -> maybe invalid (tactic . modusPonens) (parseTerm t),
                "abstract" --> \v -> tactic (abstract v),
                "abswf" --> \v -> tactic (univWF v),
                "wf" --> \_ -> tactic wfwf,
                "define" --> define,
                "unfold" --> unfold,
                "pose" --> pose
              ]
            loop
    where
    (-->) = (,)
    invalid = liftIO $ putStrLn "Invalid input"

main = do
    el <- EL.elInit "ixi"
    evalStateT (runReaderT loop el) (Context { cxSeqs = [ [] :|- Xi :% H :% H ], cxDefs = Map.empty })

tactic :: Tactic -> InterfaceM ()
tactic tac = do
    cx <- get
    let (s:ss) = cxSeqs cx
    case tac s of
        Right new -> put (cx { cxSeqs = new ++ ss })
        Left err -> liftIO $ putStrLn err  

define :: String -> InterfaceM ()
define s = do
    let varname = takeWhile (/= ' ') s
    case dropWhile (/= ' ') s of
        (' ':'=':def) -> do
            cx <- get
            if varname `Map.member` cxDefs cx
                then liftIO $ putStrLn "Already defined"
                else case parseTerm (chomp def) of
                        Nothing -> liftIO $ putStrLn "Parse error"
                        Just term -> put (cx { cxDefs = Map.insert varname term (cxDefs cx) })
        _ -> liftIO $ putStrLn "Parse error"

unfold :: String -> InterfaceM ()
unfold s = do
    cx <- get
    let ((hyps :|- goal) : ss) = cxSeqs cx
    case Map.lookup s (cxDefs cx) of
        Nothing -> liftIO $ putStrLn "No such definition"
        Just def -> case substitute s def goal of
                        Nothing -> liftIO $ putStrLn "Substitute failed"
                        Just t' -> put (cx { cxSeqs = (hyps :|- t'):ss })

pose :: String -> InterfaceM ()
pose s = do
    case parseTerm s of
        Nothing -> liftIO $ putStrLn "Parse error"
        Just goal -> do
            cx <- get
            let ((hyps :|- g) : ss) = cxSeqs cx
            put (cx { cxSeqs = (hyps :|- goal) : ((goal : hyps) :|- g) : ss })
