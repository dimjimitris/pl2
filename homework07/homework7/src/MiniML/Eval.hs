module MiniML.Eval where

import qualified Data.Map as M
import Control.Monad.State

import MiniML.Syntax
import MiniML.Error
import MiniML.Values


-- MiniML evaluation

-- Make sure to look at Values.hs for the associated data types.

-- The evaluation state.
type EvalState = ( Env     -- An environment mapping variables to their values.
                 , Store   -- A store mapping memory locations to values.
                 , Loc     -- The next available memory location. Needed when allocation new references.
                 )

-- The type of the evaluation computation.
type Eval = StateT EvalState (Either (Posn,String))

-- `StateT` is the monad transformer for the State monad. It allows you to put
-- an arbitrary monad inside the State. Here, we put an Error monad inside the
-- result of the state, composing the State monad with the Error monad.

-- The resulting monad, `Eval`, manages both mutable state and error propagation
-- within a single monad.

-- Essentially, the type `Eval a` represents a computation of type `EvalState -> (EvalState, Error a)`

-- Note 1: In the definition of `Eval`, we use `Either (Posn, String)` directly
-- instead of the type synonym `Error` (defined in Error.hs) because Haskell
-- does not allow partially applied type synonyms.

-- Note 2: Technically, we could have used a reader monad for Env, but it makes
-- our definitions simpler to put it in the state and avoid composing too many
-- monads.

-- Useful functions for handling the state.

-- Get the environment
getEnv :: Eval Env
getEnv = do
  (env, _, _) <- get
  return env

-- Update the environment
putEnv :: Env -> Eval ()
putEnv env = do
  (_, store, l) <- get
  put (env, store, l)

-- Get the store
getStore :: Eval Store
getStore = do
  (_, store, _) <- get
  return store

-- Update the store
putStore :: Store -> Eval ()
putStore store = do
  (env, _, l) <- get
  put (env, store, l)

-- Run a computation in the provided environment
localEnv :: Env -> Eval a -> Eval a
localEnv env m = do
  env' <- getEnv
  putEnv env
  x <- m
  putEnv env'
  return x

-- Update the store using the given function and run a computation
withStore :: (Store -> Store) -> Eval a -> Eval a
withStore f m = do
  store <- getStore
  putStore (f store)
  m

-- Return a fresh location and increase the location counter
freshLoc :: Eval Loc
freshLoc = do
  (store, env, l) <- get
  let l' = l + 1
  put (store, env, l')
  return l'

-- Throw an error.
throwErr :: Posn -> String -> Eval a
throwErr p str = lift (throw (p,str))

-- Main evaluation function.

-- TODO 2: Fill in the definition for the evaluation function.

-- Make sure to correctly propagate the types to closure values. This should be
-- available as type annotations in the input program (Do not use the
-- typechecking function in te evaluation function!). You can assume that the
-- input programs will never have the form `Abs p x t Nothing e` (i.e., return
-- type annotations will be filled).

eval :: Exp -> Eval Value
-- Application
eval (App _ e1 e2) = do
    v1 <- eval e1
    case v1 of
        VClo env' _ x _ _ b -> do
            v2 <- eval e2
            localEnv (M.insert x v2 env') $ eval b
        _ -> throwErr (getPosn e1) "Expected a function closure"
-- Let
eval (Let _ x _ e1 e2) = do
    v1 <- eval e1
    env <- getEnv
    localEnv (M.insert x v1 env) $ eval e2
-- If
eval (ITE _ e1 e2 e3) = do
    v1 <- eval e1
    case v1 of
        VBool True -> eval e2
        VBool False -> eval e3
        _ -> throwErr (getPosn e1) "Expected a boolean expression"
-- Bop
eval (Bop p b e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    case (v1, v2) of
        (VNum n1, VNum n2) ->
            case b of
                Plus -> return $ VNum (n1 + n2)
                Minus -> return $ VNum (n1 - n2)
                Mult -> return $ VNum (n1 * n2)
                Div -> return $ VNum (n1 `div` n2)
                Lt -> return $ VBool (n1 < n2)
                Gt -> return $ VBool (n1 > n2)
                Le -> return $ VBool (n1 <= n2)
                Ge -> return $ VBool (n1 >= n2)
                Eq -> return $ VBool (n1 == n2)
                _ -> throwErr p "Expected integer operator and integer operands"
        (VBool b1, VBool b2) ->
            case b of
                And -> return $ VBool (b1 && b2)
                Or -> return $ VBool (b1 || b2)
                Eq -> return $ VBool (b1 == b2)
                _ -> throwErr p "Expected boolean operator and boolean operands"
        _ -> throwErr p "Expected numeric or boolean operands"
-- Uop
eval (Uop _ u e) = do
    v <- eval e
    case (u, v) of
        (Not, VBool b) -> return $ VBool (not b)
        _ -> throwErr (getPosn e) "Expected boolean operand"
-- Pair
eval (Pair _ e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    return $ VPair v1 v2
-- Fst
eval (Fst _ e) = do
    v <- eval e
    case v of
        VPair v1 _ -> return v1
        _ -> throwErr (getPosn e) "Expected a pair"
-- Snd
eval (Snd _ e) = do
    v <- eval e
    case v of
        VPair _ v2 -> return v2
        _ -> throwErr (getPosn e) "Expected a pair"
-- Left injection
eval (Inl _ t e) = do
    v <- eval e
    return $ VInl t v
-- Right injection
eval (Inr _ t e) = do
    v <- eval e
    return $ VInr t v
-- Case
eval (Case _ e y1 e1 y2 e2) = do
    v <- eval e
    env <- getEnv
    case v of
        VInl _ v' -> localEnv (M.insert y1 v' env) $ eval e1
        VInr _ v' -> localEnv (M.insert y2 v' env) $ eval e2
        _ -> throwErr (getPosn e) "Expected a sum value"
-- Let rec
eval (LetRec _ f x t r b rest) = do
    env <- getEnv
    localEnv (M.insert f (VClo env f x t r b) env) $ eval rest
-- Assignment to Reference
eval (Asgn _ e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    case v1 of
        Memloc l -> do
            store <- getStore
            putStore (M.insert l v2 store)
            return VUnit
        _ -> throwErr (getPosn e1) "Expected a reference"
-- Dereference
eval (Deref _ e) = do
    v <- eval e
    case v of
        Memloc l -> do
            store <- getStore
            case M.lookup l store of
                Just v' -> return v'
                Nothing -> throwErr (getPosn e) "Dereferencing an uninitialized reference"
        _ -> throwErr (getPosn e) "Expected a reference"
-- Reference
eval (Ref _ e) = do
    v <- eval e
    l <- freshLoc
    store <- getStore
    putStore (M.insert l v store)
    return $ Memloc l
-- Values
eval (Abs _ x t mret e) = do
    env <- getEnv
    ret <- case mret of
        Just ret -> return ret
        Nothing -> throwErr (getPosn e) "Expected a return type annotation"
    return $ VClo env x x t ret e
eval (Unit _) = return VUnit
eval (NumLit _ n) = return $ VNum n
eval (BoolLit _ b) = return $ VBool b
eval (Var p x) = do
    env <- getEnv
    case M.lookup x env of
        Just v -> return v
        Nothing -> throwErr p ("Unbound variable: " ++ x)

-- Top-level evaluation function. Runs the main evaluation function on an empty
-- state and extracts the value and the store. Note that the store is needed as
-- the value may contain memory locations.
evalTop :: Exp -> Error (Value,Store)
evalTop e = do
  let initState = (M.empty, M.empty, 0)
  (val, (_, store, _)) <- runStateT (eval e) initState
  return (val, store)