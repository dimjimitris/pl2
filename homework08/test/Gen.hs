module Gen where

import Test.QuickCheck
import Control.Monad
import qualified Data.Map as M

import MiniML.Syntax

-- Generators for random programs

-- Simple random generators of types and terms. No well-formedness invariant.
-- Useful for testing the parser

genTypeSize :: Int -> Gen Type
genTypeSize 0 =
    elements [ TInt, TBool, TUnit ]
genTypeSize s =
    frequency [ (2, elements [ TInt, TBool, TUnit ])
              , (1, liftM2 TArrow genTypeS genTypeS)
              , (1, liftM2 TSum genTypeS genTypeS)
              , (1, liftM2 TProd genTypeS genTypeS) ]
    where
        genTypeS = genTypeSize (s-1)

genType :: Gen Type
genType = scale (min 10) $ sized genTypeSize

genBop :: Gen Bop
genBop = elements [Plus, Minus, Mult, Div, And, Or, Lt, Gt, Le, Ge, Eq]

genVar :: Gen String
genVar = do
  n <- chooseInt (1, 200)
  x <- elements [ "x", "y", "z", "test_42", "foo_", "_bar", "z21", "f", "g", "lala"]
  return (x ++ show n)

-- Generate an expression of a given size
genExpSize :: Int -> Gen Exp
genExpSize s = case s of
    0 -> baseCases
    _ -> frequency [ (2, baseCases)
                   , (1, liftM2 (App nowhere) genExpS genExpS)
                   , (1, liftM4 (Abs nowhere) genVar genOptTypeS (return Nothing) genExpS)
                   , (1, liftM3 (ITE nowhere) genExpS genExpS genExpS)
                   , (1, liftM3 (Bop nowhere) genBop genExpS genExpS)
                   , (1, liftM  (Uop nowhere Not) genExpS)
                   , (1, liftM2 (Pair nowhere) genExpS genExpS)
                   , (1, liftM  (Fst nowhere) genExpS)
                   , (1, liftM  (Snd nowhere) genExpS)
                   , (1, liftM (Inl nowhere) genExpS)
                   , (1, liftM (Inr nowhere) genExpS)
                   , (1, liftM5 (Case nowhere) genExpS genVar genExpS genVar genExpS)
                   , (1, liftM4 (Let nowhere) genVar (Just <$> genTypeS) genExpS genExpS)
                   , (1, do
                           x <- genVar
                           liftM5 (LetRec nowhere x) genVar genOptTypeS genOptTypeS genExpS genExpS)
                   , (1, return (Nil nowhere))
                   , (1, liftM2 (Cons nowhere) genExpS genExpS)
                   , (1, liftM5 (CaseL nowhere) genExpS genExpS genVar genVar genExpS)
                   ]
  where
    genExpS = genExpSize (s-1)
    genTypeS = genTypeSize (s-1)
    baseCases = oneof [ return (Unit nowhere)
                      , liftM (NumLit nowhere) arbitrary
                      , liftM (BoolLit nowhere) arbitrary ]
  
    genOptTypeS = oneof [ Just <$> genTypeS
                        , return Nothing ]

-- Generate an expression of an arbitrary
genExp :: Gen Exp
genExp = scale (min 20) $ sized genExpSize



-- A generator for well-typed terms. You may use the generator for STLC programs
-- provided in the course notes as a reference:
-- https://github.com/zoep/PL2/blob/main/lectures/Haskell/src/QuickCheck.hs

genTExpSize :: M.Map Type [String]  -- a map from types to variables with the corresponding types
            -> Int                  -- counter for generating fresh names
            -> Type                 -- the type of the generated terms
            -> Int                  -- The size of the term.
            -> Gen Exp
genTExpSize env next t sz =
  case t of
    TUnit ->
      frequency $ (6, genLit) : if sz <= 0 then [] else [
                  (2, genApp),
                  (2, genFst),
                  (2, genSnd),
                  (2, genCase),
                  (2, genCaseL),
                  (2, genLet),
                  (2, genITE),
                  (1, genLetRec)
                ]
                ++ zip [1..] genVar'

    TInt ->
      frequency $ (6, genLit) : if sz <= 0 then [] else [
                  (4, genBop'),
                  (3, genApp),
                  (3, genCase),
                  (3, genCaseL),
                  (3, genLet),
                  (2, genITE),
                  (2, genFst),
                  (2, genSnd),
                  (1, genLetRec)
                ]
                ++ zip [1..] genVar'

    TBool ->
      frequency $ (6, genLit) : if sz <= 0 then [] else [
                  (4, genBop'),
                  (4, genUop),
                  (3, genApp),
                  (3, genCase),
                  (3, genCaseL),
                  (3, genLet),
                  (2, genFst),
                  (2, genSnd),
                  (2, genITE),
                  (1, genLetRec)
                ]
                ++ zip [1..] genVar'

    TArrow t1 t2 ->
      frequency $ (6, genAbs t1 t2) : if sz <= 0 then [] else [
                  (3, genLet),
                  (3, genApp),
                  (2, genFst),
                  (2, genSnd),
                  (2, genITE),
                  (2, genCase),
                  (2, genCaseL),
                  (1, genLetRec)
                ]
                ++ zip [1..] genVar'

    TProd t1 t2 ->
      frequency $ (6, genPair t1 t2) : if sz <= 0 then [] else [
                  (3, genLet),
                  (3, genApp),
                  (3, genITE),
                  (3, genCase),
                  (3, genCaseL),
                  (2, genFst),
                  (2, genSnd),
                  (1, genLetRec)
                ]
                ++ zip [1..] genVar'

    TSum t1 t2 ->
      frequency $ [ (6, genInl t1),
                    (6, genInr t2) ] ++ if sz <= 0 then [] else [
                    (3, genLet),
                    (3, genApp),
                    (3, genITE),
                    (3, genCase),
                    (3, genCaseL),
                    (2, genFst),
                    (2, genSnd),
                    (1, genLetRec)
                  ]
                  ++ zip [1..] genVar'

    TList t' ->
      frequency $ (6, genNil) : if sz <= 0 then [] else [
                  (4, genCons t'),
                  (3, genLet),
                  (3, genApp),
                  (3, genITE),
                  (3, genCase),
                  (3, genCaseL),
                  (2, genFst),
                  (2, genSnd),
                  (1, genLetRec)
                ]
                ++ zip [1..] genVar'

    TVar _ -> error "genTExpSize: encountered type variable"
  where
    -- var
    genVar' = case M.lookup t env of
      Just xs -> [elements (fmap (Var nowhere) xs)]
      Nothing -> []

    -- application
    genApp = do
      t1 <- genType
      e1 <- genTExpSize env next (TArrow t1 t) (sz - 1)
      e2 <- genTExpSize env next t1 (sz - 1)
      return $ App nowhere e1 e2

    -- abstraction
    genAbs t1 t2 = do
      let name = "x_" ++ show next
      let env' = addVar name t1 env
      body <- genTExpSize env' (next + 1) t2 (sz - 1)
      -- ! maybe just
      return $ Abs nowhere name Nothing Nothing body

    -- unit, integers, booleans
    genLit =
      case t of
        TUnit -> return (Unit nowhere) -- consider units to be literals for simplicity
        TInt -> liftM (NumLit nowhere) arbitrary
        TBool -> liftM (BoolLit nowhere) arbitrary
        _ -> error $ "genLit: invalid literal type: " ++ show t

    -- if-then-else
    genITE = do
      e1 <- genTExpSize env next TBool (sz - 1)
      e2 <- genTExpSize env next t (sz - 1)
      e3 <- genTExpSize env next t (sz - 1)
      return $ ITE nowhere e1 e2 e3

    -- arithmetic bops, logical bops, comparison bops
    genBop' =
      case t of
        TInt -> do
          op <- intIntBop
          e1 <- genTExpS TInt
          e2 <- if op == Div then genNonZeroTInt else genTExpS TInt
          return $ Bop nowhere op e1 e2
        TBool -> oneof [liftM3 (Bop nowhere) boolBoolBop (genTExpS TBool) (genTExpS TBool),
                        liftM3 (Bop nowhere) intBoolBop (genTExpS TInt) (genTExpS TInt)]
        _ -> error $ "genBop': invalid binary operator type: " ++ show t
      where
        intIntBop = elements [Plus, Minus, Mult, Div]
        boolBoolBop = elements [And, Or]
        intBoolBop = elements [Lt, Gt, Le, Ge, Eq]
        -- second expression in division will always an int literal, but that's fine
        genNonZeroTInt = do
          n <- arbitrary
          if n == 0 then genNonZeroTInt else return $ NumLit nowhere n

    -- boolean uops
    genUop = liftM (Uop nowhere Not) (genTExpS TBool)

    -- pair
    genPair t1 t2 = liftM2 (Pair nowhere) (genTExpS t1) (genTExpS t2)

    -- fst
    genFst = do
      t2 <- genType
      e <- genTExpS (TProd t t2)
      return $ Fst nowhere e

    -- snd
    genSnd = do
      t1 <- genType
      e <- genTExpS (TProd t1 t)
      return $ Snd nowhere e

    -- inl
    genInl t' = liftM (Inl nowhere) (genTExpS t')

    -- inr
    genInr t' = liftM (Inr nowhere) (genTExpS t')

    -- case
    genCase = do
      t1 <- genType
      t2 <- genType
      e <- genTExpS (TSum t1 t2)
      let name1 = "y1_" ++ show next
      let name2 = "y2_" ++ show next
      let env1 = addVar name1 t1 env
      let env2 = addVar name2 t2 env
      e1 <- genTExpSize env1 (next + 1) t (sz - 1)
      e2 <- genTExpSize env2 (next + 1) t (sz - 1)
      return $ Case nowhere e name1 e1 name2 e2

    -- caseL (case e of Nil -> e1 | Cons x xs -> e2)
    genCaseL = do
      t' <- genType
      e <- genTExpS (TList t')
      let name_hd = "y1_" ++ show next
      let name_tl = "y2_" ++ show next
      let env' = addVar name_tl (TList t') (addVar name_hd t' env)
      e1 <- genTExpSize env (next + 1) t (sz - 1)
      e2 <- genTExpSize env' (next + 1) t (sz - 1)
      return $ CaseL nowhere e e1 name_hd name_tl e2

    -- let
    genLet = do
      let name = "x_" ++ show next
      t' <- genType
      e <- genTExpS t'
      let env' = addVar name t' env
      rest <- genTExpSize env' (next + 1) t (sz - 1)
      return $ Let nowhere name Nothing e rest

    -- let rec
    genLetRec = do
      let xname = "x_" ++ show next
      xt <- genType
      let fname = "f_" ++ show next
      let env' = addVar fname (TArrow xt t) env
      body <- genTExpSize (addVar xname xt env') (next + 1) t (sz - 1)
      rest <- genTExpSize env' (next + 1) t (sz - 1)
      return $ LetRec nowhere fname xname Nothing Nothing body rest

    genNil = return $ Nil nowhere

    genCons t' = do
      e1 <- genTExpS t'
      e2 <- genTExpS (TList t')
      return $ Cons nowhere e1 e2

    -- helper functions
    genTExpS t' = genTExpSize env next t' (sz - 1)
    addVar x typ = M.insertWith (++) typ [x] -- (returns a function that takes an environment and adds a variable to it)
  

-- Top-level function for generating well-typed expressions. You may tweak them
-- if you wish, but do not change their types.

-- Generate a well-type term
genWTExp :: Gen Exp
genWTExp = do
  size <- arbitrary
  t <- genType
  genTExpSize M.empty 1 t size

-- Generate a well-type term of a certain type
genExpOfType :: Type -> Gen Exp
genExpOfType t = genTExpSize M.empty 1 t 3

-- Generate a well-type term with its type
genExpType :: Gen (Exp,Type)
genExpType = do
  t <- scale (min 10) $ sized genTypeSize
  e <- scale (min 10) $ sized $ genTExpSize M.empty 1 t
  return (e,t)
