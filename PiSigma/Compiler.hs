module PiSigma.Compiler where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified GHC.Prim
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Fix
import Unsafe.Coerce (unsafeCoerce)
import Data.Typeable

newtype Label v = Label String
    deriving (Eq,Ord)

class (Typeable1 v) => ValueType v

data Type v
    = TType
    | TFinite (Set.Set (Label v))
    | TPi     v v   -- Pi    : (A : Type) -> (A -> Type) -> Type
    | TSigma  v v   -- Sigma : (A : Type) -> (A -> Type) -> Type
    deriving (Typeable)

newtype Ref = Ref Integer
    deriving (Eq,Ord)

data Pair v = Pair v v
    deriving (Typeable)

newtype Fun v = Fun (v -> v)
    deriving (Typeable)

newtype Dyn v = Dyn GHC.Prim.Any
    deriving (Typeable)

instance ValueType Type
instance ValueType Pair
instance ValueType Fun
instance ValueType Dyn


class (Functor m, MonadFix m) => Compiler m where
    data Value m :: *
    lam :: Value m -> (forall m. Compiler m => Value m -> m (Value m)) -> m (Value m)


data Env = Env {
    envTypes :: Map.Map Ref IValue,
    envDefs  :: Map.Map Ref IValue
  }

insertType :: Ref -> IValue -> Env -> Env
insertType ref val env = env { envTypes = Map.insert ref val (envTypes env) }

insertDef :: Ref -> IValue -> Env -> Env
insertDef ref val env = env { envDefs = Map.insert ref val (envDefs env) }

data IValue 
    = forall a. ValueType a => IVCanonical (a IValue)
    | IVNeutral Neutral

data Neutral
    = NVar   Ref
    | NApp   Neutral IValue
    | NSplit Neutral (IValue -> IValue -> IValue)
    | NCase  Neutral (Map.Map (Label IValue) IValue)
    | NUnbox Neutral


type EnvI = StateT [Ref] (Reader Env)

newtype TypeCheck a = TypeCheck { runTypeCheck :: EnvI a }
    deriving (Functor, Monad, MonadFix)

allocate :: (MonadState [Ref] m) => m Ref
allocate = do
    (r:rs) <- get
    put rs
    return r

lookupRef :: Ref -> Env -> IValue
lookupRef ref env = 
    case Map.lookup ref (envDefs env) of
        Nothing -> IVNeutral (NVar ref)
        Just v  -> v

instance Compiler TypeCheck where
    newtype Value TypeCheck = TCVal { typecheck :: Env -> IValue }
    lam dom body = TypeCheck $ do
        env <- ask
        ref <- allocate
        cod <- local (insertType ref (typecheck dom env)) $
            runTypeCheck . body . TCVal . lookupRef $ ref
        return . TCVal $ \env -> IVCanonical $
            TPi (typecheck dom env) 
                (IVCanonical . Fun $ \x -> 
                     let env' = insertDef ref x env in typecheck cod env')


newtype Interpret a = Interpret { runInterpret :: Reader Env a }
    deriving (Functor, Monad, MonadFix)

instance Compiler Interpret where
    newtype Value Interpret = IVal { interpret :: Env -> IValue }
    lam dom body = Interpret $ do
        -- we know the lambda is well-typed
        return . IVal $ \env ->
            -- should one of these envs be the closure from outside?
            IVCanonical . Fun $ \x -> interpret (runReader (runInterpret (body (IVal (const x)))) env) env
