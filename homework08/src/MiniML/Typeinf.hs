module MiniML.Typeinf where

import qualified Data.Map as M
import Control.Monad.State
import Data.List (nub) -- nub removes duplicates from a list. You may find it helpful.

import MiniML.Syntax
import MiniML.Error
import MiniML.Print -- For better error messages

-- import Debug.Trace -- Debug.Trace is your friend

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

-- literals
inferType _ (Unit _) = return (TUnit, [])
inferType _ (NumLit _ _) = return (TInt, [])
inferType _ (BoolLit _ _) = return (TBool, [])

-- rest of cases...
{-
        x : s ∈ Γ
        t = instantiate(s)
    ---------------------------CT-Var
         Γ ⊢ x : t | {} 
-}
inferType ctx (Var pos x) = case M.lookup x ctx of
  Nothing -> lift $ typeError pos $ "Unbound variable " <> x
  Just scheme -> do
    t <- instantiate scheme
    return (t, [])

{-
        Γ, x : t1 ⊢ e : t2 | C
---------------------------------------------CT-AbsAnnot
    Γ ⊢ (fun x : t1 -> e) : t1 -> t2 | C


        Γ, x : α ⊢ e : t2 | C
---------------------------------------CT-Abs             α is fresh
    Γ ⊢ (fun x -> e) : α -> t2 | C
-}
-- (fun (x : t1) : t2 -> e) t2 will always be missing in the AST
-- based on my understanding of the code
inferType ctx (Abs pos x mt1 mt2 e) = do
  t1 <- maybe (TVar <$> freshTVar) return mt1
  let ctx' = M.insert x (Type t1) ctx
  (t2, c2) <- inferType ctx' e
  let c0 = case mt2 of
        Nothing -> []
        Just t2Aux -> [(t2, t2Aux, pos)]
  return (TArrow t1 t2, c0 ++ c2)

{-
             Γ ⊢ e1 : t1 | C1
             Γ ⊢ e2 : t2 | C2        
-------------------------------------------------CT-App   α is fresh
    Γ ⊢ e1 e2 : α | {t1 = t2 -> α} ∪ C1 ∪ C2
-}
inferType ctx (App pos e1 e2) = do
  (t1, c1) <- inferType ctx e1
  (t2, c2) <- inferType ctx e2
  a <- TVar <$> freshTVar
  return (a, nub ([(t1, TArrow t2 a, pos)] ++ c1 ++ c2))

{-
        Γ ⊢ e1 : t1 | C1       Γ ⊢ e2 : t2 | C2       Γ ⊢ e3 : t3 | C3
-------------------------------------------------------------------------------CT-ITE
   Γ ⊢ if e1 then e2 else e3 : t2 | { t1 = bool, t2 = t3 } ∪ C1 ∪ C2 ∪ C3
-}
inferType ctx (ITE pos e1 e2 e3) = do
  (t1, c1) <- inferType ctx e1
  (t2, c2) <- inferType ctx e2
  (t3, c3) <- inferType ctx e3
  return (t2, nub ([(t1, TBool, pos), (t2, t3, pos)] ++ c1 ++ c2 ++ c3))

inferType ctx (Bop pos op e1 e2) = do
  (t1, c1) <- inferType ctx e1
  (t2, c2) <- inferType ctx e2
  let (rett, c0) = case op of
        Plus -> (TInt, [(t1, TInt, pos), (t2, TInt, pos)])
        Minus -> (TInt, [(t1, TInt, pos), (t2, TInt, pos)])
        Mult -> (TInt, [(t1, TInt, pos), (t2, TInt, pos)])
        Div -> (TInt, [(t1, TInt, pos), (t2, TInt, pos)])
        And -> (TBool, [(t1, TBool, pos), (t2, TBool, pos)])
        Or -> (TBool, [(t1, TBool, pos), (t2, TBool, pos)])
        Lt -> (TBool, [(t1, TInt, pos), (t2, TInt, pos)])
        Gt -> (TBool, [(t1, TInt, pos), (t2, TInt, pos)])
        Le -> (TBool, [(t1, TInt, pos), (t2, TInt, pos)])
        Ge -> (TBool, [(t1, TInt, pos), (t2, TInt, pos)])
        Eq -> (TBool, [(t1, t2, pos)])
  return (rett, nub (c0 ++ c1 ++ c2))

inferType ctx (Uop pos op e) = do
  (t1, c1) <- inferType ctx e
  let (rett, c0) = case op of
        Not -> (TBool, [(t1, TBool, pos)])
  return (rett, nub (c0 ++ c1))

{-
         Γ ⊢ e1 : t1 | C1      Γ ⊢ e2 : t2 | C2
----------------------------------------------------------CT-Pair
             Γ ⊢ (e1, e2) : t1 * t2 | C1 ∪ C2
-}
inferType ctx (Pair _ e1 e2) = do
  (t1, c1) <- inferType ctx e1
  (t2, c2) <- inferType ctx e2
  return (TProd t1 t2, nub (c1 ++ c2))

{-
         Γ ⊢ e : t | C
--------------------------------CT-Fst          α, β are fresh
    Γ ⊢ fst e : α | { t = α * β } ∪ C
-}
inferType ctx (Fst pos e) = do
  (t, c) <- inferType ctx e
  a <- TVar <$> freshTVar
  b <- TVar <$> freshTVar
  let c0 = [(t, TProd a b, pos)]
  return (a, nub (c0 ++ c))

{-
         Γ ⊢ e : t | C
--------------------------------CT-Snd          α, β are fresh
    Γ ⊢ snd e : β | { t = α * β } ∪ C
-}
inferType ctx (Snd pos e) = do
  (t, c) <- inferType ctx e
  a <- TVar <$> freshTVar
  b <- TVar <$> freshTVar
  let c0 = [(t, TProd a b, pos)]
  return (b, nub (c0 ++ c))

inferType _ (Nil _) = do
  a <- TVar <$> freshTVar
  return (TList a, [])

inferType ctx (Cons pos e1 e2) = do
  (t1, c1) <- inferType ctx e1
  (t2, c2) <- inferType ctx e2
  return (TList t1, nub ([(t2, TList t1, pos)] ++ c1 ++ c2))

{-
Implemented following a rule similar to what we do for CT-Case (see bellow)
-}
-- case e1 of | [] -> e2 | hd::tl -> e3
inferType ctx (CaseL pos e1 e2 hd tl e3) = do
  (t1, c1) <- inferType ctx e1
  (t2, c2) <- inferType ctx e2
  a <- TVar <$> freshTVar
  let ctx' = M.insert hd (Type a) ctx
  let ctx'' = M.insert tl (Type $ TList a) ctx'
  (t3, c3) <- inferType ctx'' e3
  return (t2, nub ([(t1, TList a, pos), (t2, t3, pos)] ++ c1 ++ c2 ++ c3))

{-
         Γ ⊢ e : t | C
-----------------------------------CT-Inl            α is fresh
      Γ ⊢ inl e : t + α | C 
-}
inferType ctx (Inl _ e) = do
  a <- TVar <$> freshTVar
  (t, c) <- inferType ctx e
  return (TSum t a, c)

{-
         Γ ⊢ e : t | C
----------------------------CT-Inr              α is fresh
    Γ ⊢ inr e : α + t | C 
-}
inferType ctx (Inr _ e) = do
  a <- TVar <$> freshTVar
  (t, c) <- inferType ctx e
  return (TSum a t, c)

{-
      Γ ⊢ e1 : t1 | C1       Γ, x : α ⊢ e2 : t2 | C2       Γ, y : β ⊢ e3 : t3 | C3
---------------------------------------------------------------------------------------------CT-Case    α, β are fresh
    Γ ⊢ case e1 of | inl x -> e2  | inr y -> e3 : t2 | {t1 = α + β, t2 = t3} ∪ C1 ∪ C2 ∪ C3
-}
inferType ctx (Case pos e1 x e2 y e3) = do
  (t1, c1) <- inferType ctx e1
  a <- TVar <$> freshTVar
  let ctx' = M.insert x (Type a) ctx
  (t2, c2) <- inferType ctx' e2
  b <- TVar <$> freshTVar
  let ctx'' = M.insert y (Type b) ctx
  (t3, c3) <- inferType ctx'' e3
  return (t2, nub ([(t1, TSum a b, pos), (t2, t3, pos)] ++ c1 ++ c2 ++ c3))

{-
      Γ ⊢ [x ↦ e1]e2 : t2 | C2        Γ ⊢ e1 : t1 | C1
----------------------------------------------------------------CT-LetPoly
            Γ ⊢ let x = e1 in e2 : t2 | C1 ∪ C2
( adapted from 'Types and Programming' by Benjamin C. Pierce : Chapter 22.7 Let-Polymorphism )
-}
-- let x : t = e1 in e2
inferType ctx (Let pos x mt e1 e2) = do
  (t1Aux, c1Aux) <- inferType ctx e1
  let c0 = case mt of
        Nothing -> []
        Just t -> [(t1Aux, t, pos)]
  let c1 = c0 ++ c1Aux
  s1 <- lift $ unify c1
  let t1 = applySubst t1Aux s1
  let ctx' = applySubstEnv ctx s1
  let ts1 = generalize ctx' t1
  let ctx'' = M.insert x ts1 ctx
  (t2, c2) <- inferType ctx'' e2
  return (t2, nub (c1 ++ c2))

{-
   Γ, f : α ⊢ (fun x -> e1) : t1 | C1         Γ, f : Γ^-(t1) ⊢ e2 : t2 | C2
-------------------------------------------------------------------------------CT-LetRec   α is fresh, Γ^-(τ) = generalize Γ τ
          Γ ⊢ let rec f x = e1 in e2 : t2 | { t1 = α } ∪ C1 ∪ C2   
( adapted from https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Typing_rule )
-}
-- let rec f (x : tx) : tr = e1Aux in e2
-- e1 = (fun x : tx -> e1Aux)
-- t1 = TArrow tx tr
-- model it as let f = e1 in e2 (but use different context for type inference than usual)
inferType ctx (LetRec pos f x mtx mtr e1Aux e2) = do
  let e1 = Abs pos x mtx mtr e1Aux
  a <- TVar <$> freshTVar
  let ctx' = M.insert f (Type a) ctx
  (t1Aux, c1) <- inferType ctx' e1
  s1 <- lift $ unify c1
  let t1 = applySubst t1Aux s1
  let ctx'' = applySubstEnv ctx s1
  let ts1 = generalize ctx'' t1
  let ctx''' = M.insert f ts1 ctx
  (t2, c2) <- inferType ctx''' e2
  return (t2, nub ([(t1, a, pos)] ++ c1 ++ c2))


-- Top-level type inference function with an empty context
inferTypeTop :: Exp -> Error TypeScheme
inferTypeTop exp' = do
  case runStateT (inferType M.empty exp') (MkTIState 0) of
    Left err -> Left err
    Right ((t, c), _) -> do
      s <- unify c
      return $ generalize M.empty $ applySubst t s

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

-- compose two substitutions
-- suppose s1 models σ1 and s2 models σ2
-- composeSubst s1 s2 models σ2(σ1)
-- s2 is a Map String Type, s1 is a Map String Type
-- s2 contains things of the form [x -> σ2(x)], where σ2(x) is a Type
-- M.map (`applySubst` s1) s2 will do σ2(χ) `applySubst` s1 for each χ in s2
-- so we get σ1(σ2(χ)) for each x in s2
-- M.map (`applySubst` s1) s2 contains things of the form [x -> σ1(σ2(x))] for each x in s2
-- if there is an x in s1 that is not in s2, then σ1(σ2(χ)) = σ1(x) and we need to add it to the result
-- thus we do the final union with s1
-- a `M.union` b prefers the values in a if there is a key that is in both a and b
-- that is why we put M.map (`applySubst` s1) s2 first
composeSubst :: Substitution -> Substitution -> Substitution
composeSubst s1 s2 = M.map (`applySubst` s1) s2 `M.union` s1

-- Extend a substitution. Essentially the composition of a substitution subst
-- with a singleton substitution [x -> typ].
extendSubst :: Substitution -> String -> Type -> Substitution
extendSubst s x typ = composeSubst s $ M.singleton x typ

-- Instantiate universal type variables with fresh ones
instantiate :: TypeScheme -> TypeInf Type
instantiate (Type t) = return t
instantiate (Forall vars t) = do
  freshVars <- mapM (const freshTVar) vars
  return $ foldl (flip rename) t (zip vars freshVars)

-- Generalize a the free type variables in a type
generalize :: Ctx -> Type -> TypeScheme
generalize ctx t =
  let vars = nub [v | v <- freeTypeVars t, not $ occursFreeCtx v ctx] in
  Forall vars t
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
rename (x, y) = flip applySubst $ M.singleton x (TVar y)

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
