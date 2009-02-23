import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Writer

type Var = String

data Prim
    = B | C | I | Defn Int

infixl 9 :%
data AST
    = Lam Var AST
    | AST :% AST
    | Var Var
    | Prim Prim

free :: String -> AST -> Bool
free v (Lam x e) | v == x    = False
                 | otherwise = free x e
free v (f :% x) = free v f || free v x
free v (Var x) = v == x
free v (Prim _) = False

tr :: (?env :: Map.Map String AST) => AST -> AST
tr (f :% x) = tr f :% tr x
tr (Lam v e) | not (free v e) = error $ "Nonlinear occurrence of " ++ show v
tr (Lam v (Var v')) | v == v' = Prim I
tr (Lam v (Lam v' e)) | free v e = tr (Lam v (tr (Lam v' e)))
tr (Lam v (f :% Var v')) | v == v' && not (free v f) = f
tr (Lam v (f :% x)) =
    case (free v f, free v x) of
        (True,False) -> Prim C :% tr (Lam v f) :% x
        (False,True) -> Prim B :% f :% tr (Lam v x)
        _            -> error $ "Nonlinear occurrence of " ++ show v
tr (Var v) | Just i <- Map.lookup v ?env = i
tr x = x

factor :: [(String,AST)] -> [AST]
factor defs = let ?env = defids in map (tr . snd) defs
    where
    defids = Map.fromList (zip (map fst defs) (map (Prim . Defn) [0..]))

makeMaker :: Int -> AST -> String
makeMaker ident ast = execWriter (runStateT main 0) 
    where
    main = do
        tell $ "struct Node* defn" ++ show ident ++ "(struct Pool* pool) {\n"
        make ast
        tell $ "}\n"
    makePrim prim = do
        varid <- alloc
        tell $ "struct Node* " ++ varid ++ "; " 
             ++ varid ++ "->tag = " ++ tag ++ "; " 
             ++ varid ++ "->head = " ++ varid ++ "->tail = 0;\n"
        return varid
        where
        tag = case prim of { B -> "B"; C -> "C"; I -> "I"; Defn i -> show i }
    make (f :% x) = do
        fv <- make f
        xv <- make x
        return $ "apply(" ++ fv ++ ", " ++ xv ++ ", alloc_Link(pool))"
    make (Prim p) = makePrim p
    alloc = do
        x <- get
        put (x+1)
        return $ "v" ++ show x
