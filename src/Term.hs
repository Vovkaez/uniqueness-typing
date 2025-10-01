{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

module Term
  ( Term (..),
    TypeT (..),
    Type (..),
    BuiltIn (..),
    reconstructType,
    annotateSharing,
  )
where

import Boolean (BoolVariableID, Boolean (BoolFalse, BoolVariable), mkOr)
import qualified Boolean (substitute, unify, variables)
import Data.Bifunctor (bimap)
import Substitution (subOne)

data Term
  = TermVariable Bool Int -- De Brujin indexing
  | TermApplication Term Term
  | TermAbstraction Term
  | TermBuiltIn BuiltIn
  deriving (Show)

data BuiltIn
  = BuiltInInt Int
  | BuiltInSum Term Term
  | BuiltInSub Term Term
  | BuiltInMul Term Term
  | BuiltInDiv Term Term
  | BuiltInBool Bool
  | BuiltInOr Term Term
  | BuiltInAnd Term Term
  | BuiltInNot Term
  deriving (Show)

annotateSharing :: Term -> Term
annotateSharing (TermAbstraction t) =
  let cnt d = \case
        TermVariable _ i | i == d -> 1 :: Int
        TermVariable _ _ | otherwise -> 0
        TermAbstraction m -> cnt (d + 1) m
        TermApplication a b -> cnt d a + cnt d b
        TermBuiltIn (BuiltInSum a b) -> cnt d a + cnt d b
        TermBuiltIn (BuiltInSub a b) -> cnt d a + cnt d b
        TermBuiltIn (BuiltInMul a b) -> cnt d a + cnt d b
        TermBuiltIn (BuiltInDiv a b) -> cnt d a + cnt d b
        TermBuiltIn (BuiltInOr a b) -> cnt d a + cnt d b
        TermBuiltIn (BuiltInAnd a b) -> cnt d a + cnt d b
        TermBuiltIn (BuiltInNot a) -> cnt d a
        _ -> 0
      subU u d =
        let s = subU u
         in \case
              TermVariable _ i | i == d -> TermVariable u i
              var@(TermVariable _ _) | otherwise -> var
              TermAbstraction m -> TermAbstraction $ s (d + 1) m
              TermApplication a b -> TermApplication (s d a) (s d b)
              TermBuiltIn (BuiltInSum a b) -> TermBuiltIn (BuiltInSum (s d a) (s d b))
              TermBuiltIn (BuiltInSub a b) -> TermBuiltIn (BuiltInSub (s d a) (s d b))
              TermBuiltIn (BuiltInMul a b) -> TermBuiltIn (BuiltInMul (s d a) (s d b))
              TermBuiltIn (BuiltInDiv a b) -> TermBuiltIn (BuiltInDiv (s d a) (s d b))
              TermBuiltIn (BuiltInOr a b) -> TermBuiltIn (BuiltInOr (s d a) (s d b))
              TermBuiltIn (BuiltInAnd a b) -> TermBuiltIn (BuiltInAnd (s d a) (s d b))
              TermBuiltIn (BuiltInNot a) -> TermBuiltIn $ BuiltInNot $ s d a
              term -> term
   in TermAbstraction $ subU (cnt 0 t == 1) 0 t
annotateSharing term = term

type TypeVariableID = Int

data TypeT
  = TypeArrow Type Type
  | TypeInt
  | TypeBool
  | TypeVariable TypeVariableID
  deriving (Eq, Show)

data Type
  = Attr TypeT Boolean
  deriving (Eq, Show)

getUniqueness :: Type -> Boolean
getUniqueness (Attr _ u) = u

data SomeType
  = A Type
  | T TypeT
  | U Boolean
  deriving (Eq, Show)

substituteT :: (TypeVariableID -> TypeT) -> SomeType -> SomeType
substituteT s =
  let sA = \case
        Attr t u -> Attr (sT t) u
      sT = \case
        TypeArrow l r -> TypeArrow (sA l) (sA r)
        TypeVariable x -> s x
        term -> term
   in \case
        A a -> A $ sA a
        T t -> T $ sT t
        u@(U _) -> u

substituteU :: (BoolVariableID -> Boolean) -> SomeType -> SomeType
substituteU s =
  let sU = Boolean.substitute s
      sA = \case
        Attr t u -> Attr (sT t) (sU u)
      sT = \case
        TypeArrow l r -> TypeArrow (sA l) (sA r)
        term -> term
   in \case
        U u -> U $ sU u
        T t -> T $ sT t
        A a -> A $ sA a

isTvar :: TypeT -> Bool
isTvar (TypeVariable _) = True
isTvar _ = False

isUvar :: Boolean -> Bool
isUvar (BoolVariable _) = True
isUvar _ = False

variables :: TypeT -> [TypeVariableID]
variables TypeInt = []
variables TypeBool = []
variables (TypeVariable v) = [v]
variables (TypeArrow (Attr a _) (Attr b _)) = variables a ++ variables b

type Equations = [(SomeType, SomeType)]

unifyOnce :: Equations -> Equations -> Maybe Equations
unifyOnce prev next = case next of
  [] -> Just $ reverse prev
  (l, r) : eqs | l == r -> unifyOnce prev eqs
  (t@(T term), var@(T (TypeVariable _))) : eqs | not $ isTvar term -> unifyOnce ((var, t) : prev) eqs
  (u@(U term), var@(U (BoolVariable _))) : eqs | not $ isUvar term -> unifyOnce ((var, u) : prev) eqs
  (A (Attr lt lu), A (Attr rt ru)) : eqs -> unifyOnce prev $ (T lt, T rt) : (U lu, U ru) : eqs
  (T (TypeArrow a b), T (TypeArrow c d)) : eqs -> unifyOnce prev $ (A a, A c) : (A b, A d) : eqs
  -- TODO: unify these branches
  eq@(T (TypeVariable v), T term) : eqs
    | v `elem` variables term -> Nothing
    | otherwise ->
        let s = substituteT (subOne term TypeVariable v)
            substEqs = map $ bimap s s
         in unifyOnce (eq : substEqs prev) (substEqs eqs)
  eq@(U (BoolVariable v), U term) : eqs ->
    let s = substituteU (subOne term BoolVariable v)
        substEqs = map $ bimap s s
     in unifyOnce (eq : substEqs prev) (substEqs eqs)
  (U a, U b) : eqs -> do
    s <- Boolean.unify a b
    let newEqs = map (\v -> (U $ BoolVariable v, U $ s v)) (Boolean.variables a ++ Boolean.variables b)
     in unifyOnce prev $ newEqs ++ eqs
  _ -> Nothing -- something unresolvable in current equation

subTFromEqs :: Equations -> TypeVariableID -> TypeT
subTFromEqs [] = TypeVariable
subTFromEqs ((T (TypeVariable x), T sub) : eqs) = subOne sub (subTFromEqs eqs) x
subTFromEqs (_ : eqs) = subTFromEqs eqs

subUFromEqs :: Equations -> BoolVariableID -> Boolean
subUFromEqs [] = BoolVariable
subUFromEqs ((U (BoolVariable x), U sub) : eqs) = subOne sub (subUFromEqs eqs) x
subUFromEqs (_ : eqs) = subUFromEqs eqs

unify :: Equations -> Maybe (TypeVariableID -> TypeT, BoolVariableID -> Boolean)
unify eqs = do
  newEqs <- unifyOnce [] eqs
  if newEqs == eqs then return (subTFromEqs eqs, subUFromEqs eqs) else unify newEqs

builtinUnaryOpEquations :: [Type] -> TypeVariableID -> BoolVariableID -> Term -> TypeT -> (Equations, Type, TypeVariableID, BoolVariableID)
builtinUnaryOpEquations varTypes nextTypeIdx nextUniqIdx a resType =
  let (aEqs, aType, aNextTypeIdx, aNextUniqIdx) = mkTypeEquations varTypes nextTypeIdx nextUniqIdx a
      resT = Attr resType $ BoolVariable aNextUniqIdx
   in ((A aType, A resT) : aEqs, resT, aNextTypeIdx, aNextUniqIdx + 1)

builtinBinaryOpEquations :: [Type] -> TypeVariableID -> BoolVariableID -> Term -> Term -> TypeT -> (Equations, Type, TypeVariableID, BoolVariableID)
builtinBinaryOpEquations varTypes nextTypeIdx nextUniqIdx a b resType =
  let (aEqs, aType, aNextTypeIdx, aNextUniqIdx) = mkTypeEquations varTypes nextTypeIdx nextUniqIdx a
      (bEqs, bType, bNextTypeIdx, bNextUniqIdx) = mkTypeEquations varTypes aNextTypeIdx aNextUniqIdx b
      resT = Attr resType $ BoolVariable bNextUniqIdx
   in ((A aType, A resT) : (A bType, A resT) : (aEqs ++ bEqs), resT, bNextTypeIdx, bNextUniqIdx + 1)

-- TODO: pass idx via state monad
mkTypeEquations :: [Type] -> TypeVariableID -> BoolVariableID -> Term -> (Equations, Type, TypeVariableID, BoolVariableID)
mkTypeEquations varTypes nextTypeIdx nextUniqIdx = \case
  TermVariable True idx -> ([], varTypes !! idx, nextTypeIdx, nextUniqIdx) -- TODO: free variables
  TermVariable False idx -> let t = varTypes !! idx in ([(U $ getUniqueness t, U BoolFalse)], t, nextTypeIdx, nextUniqIdx)
  TermAbstraction term ->
    let varType = Attr (TypeVariable nextTypeIdx) (BoolVariable nextUniqIdx)
        (eqs, t, retNextTypeIdx, retNextUniqIdx) = mkTypeEquations (varType : varTypes) (nextTypeIdx + 1) (nextUniqIdx + 1) term
     in (eqs, Attr (TypeArrow varType t) (foldl (\b -> mkOr b . getUniqueness) BoolFalse varTypes), retNextTypeIdx, retNextUniqIdx)
  TermApplication a b ->
    let (aEqs, aType, aNextTypeIdx, aNextUniqIdx) = mkTypeEquations varTypes nextTypeIdx nextUniqIdx a
        (bEqs, bType, bNextTypeIdx, bNextUniqIdx) = mkTypeEquations varTypes aNextTypeIdx aNextUniqIdx b
        varType = Attr (TypeVariable bNextTypeIdx) (BoolVariable bNextUniqIdx)
     in ((A aType, A $ Attr (TypeArrow bType varType) (BoolVariable $ bNextUniqIdx + 1)) : (aEqs ++ bEqs), varType, bNextTypeIdx + 1, bNextUniqIdx + 2)
  TermBuiltIn b ->
    let binOpInt = \l r -> builtinBinaryOpEquations varTypes nextTypeIdx nextUniqIdx l r TypeInt
        binOpBool = \l r -> builtinBinaryOpEquations varTypes nextTypeIdx nextUniqIdx l r TypeBool
     in case b of
          BuiltInInt _ -> ([], Attr TypeInt (BoolVariable nextUniqIdx), nextTypeIdx, nextUniqIdx + 1)
          BuiltInSum l r -> binOpInt l r
          BuiltInSub l r -> binOpInt l r
          BuiltInMul l r -> binOpInt l r
          BuiltInDiv l r -> binOpInt l r
          BuiltInBool _ -> ([], Attr TypeBool (BoolVariable nextUniqIdx), nextTypeIdx, nextUniqIdx + 1)
          BuiltInAnd l r -> binOpBool l r
          BuiltInOr l r -> binOpBool l r
          BuiltInNot a -> builtinUnaryOpEquations varTypes nextTypeIdx nextUniqIdx a TypeBool

reconstructType :: Term -> Maybe Type
reconstructType term =
  let (eqs, t, _, _) = mkTypeEquations [] 0 0 term
   in do
        (subT, subU) <- unify eqs
        case substituteU subU $ substituteT subT (A t) of
          A a -> Just a
          _ -> Nothing
