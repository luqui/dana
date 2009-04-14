module IXi.Interface where

import IXi.Term
import IXi.Parser
import IXi.Sequent
import IXi.TermZipper
import IXi.Undo
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

type InterfaceM = ReaderT EL.EditLine (UndoT Context IO)

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
    lift save
    cx  <- lift get
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
                "rotate" --> \_ -> lift (put (cx { cxSeqs = ss ++ [s] })),
                "assumption" --> \_ -> tactic assumption,
                "mp" --> \t -> maybe invalid (tactic . modusPonens) (parseTerm t),
                "abstract" --> \v -> tactic (abstract v),
                "abswf" --> \v -> tactic (univWF v),
                "wf" --> \_ -> tactic wfwf,
                "define" --> define,
                "unfold" --> unfold,
                "pose" --> pose,
                "edit" --> \_ -> 
                    let hyps :|- goal = s in do
                         goal' <- editTerm goal
                         lift (put (cx { cxSeqs = (hyps :|- goal'):ss })),
                "undo" --> \_ -> lift (undo >> undo)
              ]
            loop
    where
    (-->) = (,)
    invalid = liftIO $ putStrLn "Invalid input"

main = do
    el <- EL.elInit "ixi"
    EL.setEditor el EL.Emacs
    evalUndoT (runReaderT loop el) (Context { cxSeqs = [ [] :|- Xi :% H :% H ], cxDefs = Map.empty })

tactic :: Tactic -> InterfaceM ()
tactic tac = do
    cx <- lift get
    let (s:ss) = cxSeqs cx
    case tac s of
        Right new -> lift (put (cx { cxSeqs = new ++ ss }))
        Left err -> liftIO $ putStrLn err  

define :: String -> InterfaceM ()
define s = do
    let varname = takeWhile (/= ' ') s
    case dropWhile (/= ' ') s of
        (' ':'=':def) -> do
            cx <- lift get
            if varname `Map.member` cxDefs cx
                then liftIO $ putStrLn "Already defined"
                else case parseTerm (chomp def) of
                        Nothing -> liftIO $ putStrLn "Parse error"
                        Just term -> lift (put (cx { cxDefs = Map.insert varname term (cxDefs cx) }))
        _ -> liftIO $ putStrLn "Parse error"

unfold :: String -> InterfaceM ()
unfold s = do
    cx <- lift get
    let ((hyps :|- goal) : ss) = cxSeqs cx
    case Map.lookup s (cxDefs cx) of
        Nothing -> liftIO $ putStrLn "No such definition"
        Just def -> case substitute s def goal of
                        Nothing -> liftIO $ putStrLn "Substitute failed"
                        Just t' -> lift (put (cx { cxSeqs = (hyps :|- t'):ss }))

pose :: String -> InterfaceM ()
pose s = do
    case parseTerm s of
        Nothing -> liftIO $ putStrLn "Parse error"
        Just goal -> do
            cx <- lift get
            let ((hyps :|- g) : ss) = cxSeqs cx
            lift (put (cx { cxSeqs = (hyps :|- goal) : ((goal : hyps) :|- g) : ss }))

edit :: TermZipper -> InterfaceM TermZipper
edit tz@(TermZipper t cx) = do
    liftIO . putStrLn $ showDTerm cx ("[" ++ showTerm t ++ "]")
    askLine >>= cmds invalid [
        "h" --> \_ -> subedit goLeftApp,
        "l" --> \_ -> subedit goRightApp,
        "j" --> \_ -> subedit goLambda,
        "k" --> \_ -> subedit goUp,
        "q" --> \_ -> return tz,
        "beta" --> \_ -> subedit (inZipperM betaExpand),
        "alpha" --> \v -> subedit (inZipperM (alphaRename v)),
        "eta" --> \_ -> subedit (inZipperM etaContract)
      ]
    where
    subedit motion =
        case motion tz of
            Just newz -> edit newz
            Nothing -> liftIO (putStrLn "Invalid motion") >> edit tz
    invalid = liftIO (putStrLn "Invalid command") >> edit tz
    (-->) = (,)

editTerm :: Term -> InterfaceM Term
editTerm t = termUnzip <$> edit (TermZipper t DTop)
