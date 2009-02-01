import qualified SystemU.AST as U
import qualified SystemU.Compiler as U
import qualified SystemU.Parser as U
import SystemU.UnsafeCompile

parse :: String -> U.AST
parse = head . U.parses

fromTypecheck :: U.Typecheck a -> a
fromTypecheck m = case U.runTypecheck m of
                      Left err -> error err
                      Right x -> x

typecheck :: U.AST -> U.Value
typecheck = fromTypecheck . U.typecheck

eval :: U.AST -> U.Value
eval = fromTypecheck . U.eval

compile :: U.AST -> Any
compile = unsafeCompile

showType :: Type -> String
showType Type = "Type"
showType (Pi t f) = "(Pi " ++ showType t ++ " ?)"
