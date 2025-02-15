module MiniML.Typeinf where

import qualified Data.Map as M
import Control.Monad.State
import Data.List (nub) -- nub removes duplicates from a list. You may find it helpful.

import MiniML.Syntax
import MiniML.Error
import MiniML.Print -- For better error messages
import Debug.Trace -- Debug.Trace is your friend

import Data.Maybe (fromMaybe)

-- A Typing context
type Ctx = M.Map String TypeScheme

-- Typing constraints.
-- You may want to change the representation of constraints to use a more
-- efficient data structure.
type Constraints = [(Type, Type, Posn)]

-- Substitution
type Substitution = M.Map String Type

-- The state for the type inference monad. You may want to add extend the record
-- with more information (e.g., constraints), depending on your implementation
-- of constraint generation.
newtype TypeInfState = MkTIState { fresh :: Int }

-- The monad for type inference.
type TypeInf = StateT TypeInfState (Either (Posn,String))

-- Generate a fresh type variable
freshTVar :: TypeInf String
freshTVar = do
  MkTIState nextVar <- get
  put $ MkTIState (nextVar+1)
  return $ "a" <> show nextVar


-- Raise a type error
typeError :: Posn -> String -> Error a
typeError p msg = Left (p, msg)


-- Constraint unification
unify :: Constraints -> Error Substitution
unify [] = return M.empty
unify ((t1, t2, pos):c) = case (t1, t2) of
  -- cases described in README.md
  (TVar a, TVar b) | a == b -> unify c
  (TVar a, t) | not $ occursFreeType a t -> do
    s <- unify $ applySubstCnstr c $ M.singleton a t
    return $ extendSubst s a t
  (t, TVar a) -> unify $ (TVar a, t, pos):c -- just flip it, the previous case will handle it
  (TArrow t11 t12, TArrow t21 t22) ->
    unify $ (t11, t21, pos):(t12, t22, pos):c
  -- rest of the cases...
  (TUnit, TUnit) -> unify c
  (TInt, TInt) -> unify c
  (TBool, TBool) -> unify c
  (TProd t11 t12, TProd t21 t22) ->
    unify $ (t11, t21, pos):(t12, t22, pos):c
  (TSum t11 t12, TSum t21 t22) ->
    unify $ (t11, t21, pos):(t12, t22, pos):c
  (TList t1', TList t2') -> unify $ (t1', t2', pos):c
  _ -> typeError pos $ "Cannot unify " <> showType t1 <> " with " <> showType t2


-- Constraint and type generation
inferType :: Ctx -> Exp -> TypeInf (Type, Constraints)
inferType = error "Implement me!"

-- Top-level type inference function with an empty context
inferTypeTop :: Exp -> Error TypeScheme
inferTypeTop = error "Implement me!"

-- Various helper functions

-- Apply a substitution to a type
applySubst :: Type -> Substitution -> Type
applySubst TUnit _ = TUnit
applySubst TInt _ = TInt
applySubst TBool _ = TBool
applySubst (TArrow t1 t2) subst = TArrow (applySubst t1 subst) (applySubst t2 subst)
applySubst (TProd t1 t2) subst = TProd (applySubst t1 subst) (applySubst t2 subst)
applySubst (TSum t1 t2) subst = TSum (applySubst t1 subst) (applySubst t2 subst)
applySubst (TList t) subst = TList (applySubst t subst)
applySubst (TVar a) subst = case M.lookup a subst of
  Just ty -> ty
  Nothing -> TVar a

-- Apply a substitution to a set of constraints
applySubstCnstr :: Constraints -> Substitution -> Constraints
applySubstCnstr cnstr subst =
  (\(t1, t2, pos) -> (applySubst t1 subst, applySubst t2 subst, pos)) <$> cnstr

-- Apply a substitution to a type scheme
applySubstTypeScheme :: TypeScheme -> Substitution -> TypeScheme
applySubstTypeScheme (Type t) subst = Type $ applySubst t subst
applySubstTypeScheme (Forall xs t) subst = Forall xs $ applySubst t (foldr M.delete subst xs)

-- Apply a substitution to a typing environment
applySubstEnv :: Ctx -> Substitution -> Ctx
applySubstEnv ctx subst = M.map (`applySubstTypeScheme` subst) ctx


-- Extend a substitution. Essentially the composition of a substitution subst
-- with a singleton substitution [x -> typ].
extendSubst :: Substitution -> String -> Type -> Substitution
extendSubst s x typ = M.map (`applySubst` s) (M.singleton x typ) `M.union` s

-- Instantiate universal type variables with fresh ones
instantiate :: TypeScheme -> TypeInf Type
instantiate (Type t) = return t
instantiate (Forall vars t) = do
  freshVars <- mapM (const freshTVar) vars
  let subst = M.fromList $ zip vars (map TVar freshVars)
  return $ applySubst t subst

-- Generalize a the free type variables in a type
generalize :: Ctx -> Type -> TypeScheme
generalize ctx t =
  let vars = nub [v | v <- freeTypeVars t, not $ occursFreeCtx v ctx]
  in Forall vars t
  where
    freeTypeVars :: Type -> [String]
    freeTypeVars (TVar a) = [a]
    freeTypeVars TUnit = []
    freeTypeVars TInt = []
    freeTypeVars TBool = []
    freeTypeVars (TSum t1 t2) = freeTypeVars t1 ++ freeTypeVars t2
    freeTypeVars (TProd t1 t2) = freeTypeVars t1 ++ freeTypeVars t2
    freeTypeVars (TArrow t1 t2) = freeTypeVars t1 ++ freeTypeVars t2
    freeTypeVars (TList t') = freeTypeVars t'



-- Rename a free type variable in a type
rename :: (String, String) -> Type -> Type
rename _ TUnit = TUnit
rename _ TInt = TInt
rename _ TBool = TBool
rename subst (TArrow t1 t2) = TArrow (rename subst t1) (rename subst t2)
rename subst (TProd t1 t2) = TProd (rename subst t1) (rename subst t2)
rename subst (TSum t1 t2) = TSum (rename subst t1) (rename subst t2)
rename subst (TList t) = TList (rename subst t)
rename (x, y) (TVar a) = if x == a then TVar y else TVar a

-- Check if a type variable occurs free in a type
occursFreeType :: String -> Type -> Bool
occursFreeType x (TVar a) = x == a
occursFreeType _ TUnit = False
occursFreeType _ TInt = False
occursFreeType _ TBool = False
occursFreeType x (TSum t1 t2) = occursFreeType x t1 || occursFreeType x t2
occursFreeType x (TProd t1 t2) = occursFreeType x t1 || occursFreeType x t2
occursFreeType x (TArrow t1 t2) = occursFreeType x t1 || occursFreeType x t2
occursFreeType x (TList t) = occursFreeType x t

-- Check if a type variable occurs free in a type scheme
occursFreeTypeScheme :: String -> TypeScheme -> Bool
occursFreeTypeScheme x (Type ty) = occursFreeType x ty
occursFreeTypeScheme x (Forall ys ty) = notElem x ys && occursFreeType x ty

-- Check if a type variable occurs free in a typing environment
occursFreeCtx :: String -> Ctx -> Bool
occursFreeCtx x = M.foldr ((||) . occursFreeTypeScheme x) False
