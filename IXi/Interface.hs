{-# LANGUAGE TemplateHaskell #-}

module IXi.Interface where

import IXi.Term
import IXi.Parser
import IXi.Sequent
import IXi.TermZipper
import qualified IXi.Undo as U
import Control.Monad.Reader
import Control.Applicative
import Data.List (isPrefixOf)
import qualified System.Console.Editline as EL
import System.Exit (exitSuccess)
import qualified Data.Map as Map
import Data.Binary
import Data.DeriveTH
import Data.Derive.Binary
import qualified Data.ByteString.Lazy as Str
import System.Environment
import Data.Function
import Control.Exception (handle)
import qualified Data.Char as Char

dispSequent :: Sequent -> IO ()
dispSequent (cx :|- goal) = do
    mapM_ (putStrLn . showTerm) cx
    putStrLn "----"
    putStrLn . showTerm $ goal

showSequent :: Sequent -> String
showSequent (cx :|- goal) = "... |- " ++ showTerm goal

showDef :: (Var,Term) -> String
showDef (v,t) = v ++ " = " ++ showTerm t

type InterfaceM = ReaderT EL.EditLine (U.UndoT Context IO)

data Context = Context { cxSeqs :: [Sequent], cxDefs :: Map.Map Var Term }

$(derive makeBinary ''Context)

askLine :: InterfaceM String
askLine = liftIO . askLine' =<< ask

clAskLine = do
    l <- askLine
    liftIO $ putStr clearScreen
    return l

askLine' :: EL.EditLine -> IO String
askLine' el = do
    l <- EL.elGets el
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

save :: FilePath -> InterfaceM ()
save path = do
    cx <- lift U.get
    liftIO . handle (\x -> print (x :: IOError)) $ do
        Str.writeFile path (encode cx)
        putStrLn $ "Saved to " ++ path

loop :: InterfaceM ()
loop = do
    lift U.save
    cx  <- lift U.get
    case cxSeqs cx of
        [] -> return ()
        (s:ss) -> do
            mapM_ (liftIO . putStrLn . showDef) (Map.assocs (cxDefs cx))
            liftIO $ putStrLn ""
            mapM_ (liftIO . putStrLn . showSequent) ss
            liftIO $ putStrLn ""
            liftIO $ dispSequent s
            clAskLine >>= cmds invalid [
                "rotate" --> \_ -> lift (U.put (cx { cxSeqs = ss ++ [s] })),
                "assumption" --> \_ -> tactic assumption,
                "mp" --> \t -> maybe invalid (tactic . modusPonens) (parseTerm t),
                "abstract" --> ident (tactic . abstract),
                "abswf" --> ident (tactic . univWF),
                "wf" --> \_ -> tactic wfwf,
                "define" --> define,
                "unfold" --> unfold,
                "pose" --> pose,
                "edit" --> \_ -> 
                    let hyps :|- goal = s in do
                         goal' <- editTerm goal
                         lift (U.put (cx { cxSeqs = (hyps :|- goal'):ss })),
                "undo" --> \_ -> lift (U.undo >> U.undo),
                "save" --> save
              ]
            loop
    where
    (-->) = (,)
    invalid = liftIO $ putStrLn "Invalid input"
    ident c v | all Char.isAlphaNum v && not (null v) = c v
              | otherwise = liftIO $ putStrLn "Not a valid identifier"

main = do
    el <- EL.elInit "ixi"
    EL.setEditor el EL.Emacs

    cx <- do
        args <- getArgs
        case args of
            [] -> fix $ \self -> do
                putStrLn "Enter Goal"
                s <- askLine' el
                case parseTerm s of
                    Just t -> return $ Context { cxSeqs = [ [] :|- t ], cxDefs = Map.empty }
                    Nothing -> putStrLn "Parse error" >> self
            [file] -> decode <$> Str.readFile file
                
    putStr clearScreen
    U.evalUndoT (runReaderT loop el) cx
    putStrLn "No more goals.  Success!"

tactic :: Tactic -> InterfaceM ()
tactic tac = do
    cx <- lift U.get
    let (s:ss) = cxSeqs cx
    case tac s of
        Right new -> lift (U.put (cx { cxSeqs = new ++ ss }))
        Left err -> liftIO $ putStrLn err  

define :: String -> InterfaceM ()
define s = do
    let varname = takeWhile (/= ' ') s
    case dropWhile (/= ' ') s of
        (' ':'=':def) -> do
            cx <- lift U.get
            if varname `Map.member` cxDefs cx
                then liftIO $ putStrLn "Already defined"
                else case parseTerm (chomp def) of
                        Nothing -> liftIO $ putStrLn "Parse error"
                        Just term -> lift (U.put (cx { cxDefs = Map.insert varname term (cxDefs cx) }))
        _ -> liftIO $ putStrLn "Parse error"

unfold :: String -> InterfaceM ()
unfold s = do
    cx <- lift U.get
    let ((hyps :|- goal) : ss) = cxSeqs cx
    case Map.lookup s (cxDefs cx) of
        Nothing -> liftIO $ putStrLn "No such definition"
        Just def -> case substitute s def goal of
                        Nothing -> liftIO $ putStrLn "Substitute failed"
                        Just t' -> lift (U.put (cx { cxSeqs = (hyps :|- t'):ss }))

pose :: String -> InterfaceM ()
pose s = do
    case parseTerm s of
        Nothing -> liftIO $ putStrLn "Parse error"
        Just goal -> do
            cx <- lift U.get
            let ((hyps :|- g) : ss) = cxSeqs cx
            lift (U.put (cx { cxSeqs = (hyps :|- goal) : ((goal : hyps) :|- g) : ss }))

showZipper (TermZipper t cx) = showDTerm cx subterm
    where
    subterm | needsParens cx t = "(" ++ bold (showTerm t) ++ ")"
            | otherwise        = bold (showTerm t)

edit :: TermZipper -> InterfaceM TermZipper
edit tz = do
    liftIO . putStr $ clearScreen
    liftIO . putStrLn $ showZipper tz
    clAskLine >>= cmds invalid [
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


bold :: String -> String
bold s = "\27[1;31m" ++ s ++ "\27[0m"

clearScreen :: String
clearScreen = "\27[2J\27[0;0H"
