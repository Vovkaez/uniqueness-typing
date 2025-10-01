{-# LANGUAGE LambdaCase #-}

module Boolean
  ( Boolean (..),
    BoolVariableID,
    mkAnd,
    mkOr,
    mkNot,
    mkXor,
    substitute,
    variables,
    unify,
  )
where

import Substitution (subOne)

type BoolVariableID = Int

data Boolean
  = BoolTrue
  | BoolFalse
  | BoolVariable BoolVariableID
  | BoolAnd Boolean Boolean
  | BoolOr Boolean Boolean
  | BoolNot Boolean
  deriving (Eq, Show)

-- mk* constructors are strict, substitute uses them to minimize result size
mkAnd :: Boolean -> Boolean -> Boolean
mkAnd BoolFalse _ = BoolFalse
mkAnd _ BoolFalse = BoolFalse
mkAnd BoolTrue BoolTrue = BoolTrue
mkAnd BoolTrue a = a
mkAnd a BoolTrue = a
mkAnd a b = BoolAnd a b

mkOr :: Boolean -> Boolean -> Boolean
mkOr BoolTrue _ = BoolTrue
mkOr _ BoolTrue = BoolTrue
mkOr BoolFalse BoolFalse = BoolFalse
mkOr BoolFalse a = a
mkOr a BoolFalse = a
mkOr a b = BoolOr a b

mkNot :: Boolean -> Boolean
mkNot BoolTrue = BoolFalse
mkNot BoolFalse = BoolTrue
mkNot a = BoolNot a

mkXor :: Boolean -> Boolean -> Boolean
mkXor a b = mkOr (mkAnd a (mkNot b)) (mkAnd (mkNot a) b)

substitute :: (BoolVariableID -> Boolean) -> Boolean -> Boolean
substitute s =
  let sub = substitute s
   in \case
        BoolTrue -> BoolTrue
        BoolFalse -> BoolFalse
        BoolVariable v -> s v
        BoolAnd a b -> mkAnd (sub a) (sub b)
        BoolOr a b -> mkOr (sub a) (sub b)
        BoolNot a -> mkNot (sub a)

-- free variables contained in term
-- repetitions are possible
variables :: Boolean -> [BoolVariableID]
variables BoolTrue = []
variables BoolFalse = []
variables (BoolVariable v) = [v]
variables (BoolAnd a b) = variables a ++ variables b
variables (BoolOr a b) = variables a ++ variables b
variables (BoolNot a) = variables a

unify :: Boolean -> Boolean -> Maybe (BoolVariableID -> Boolean)
unify a b = unify0 $ mkXor a b

-- unify a = 0 using successive variable elimination
unify0 :: Boolean -> Maybe (BoolVariableID -> Boolean)
unify0 a = case variables a of
  [] -> case a of
    BoolFalse -> Just BoolVariable
    _ -> Nothing
  x : _ ->
    let a0 = substitute (subOne BoolFalse BoolVariable x) a
        a1 = substitute (subOne BoolTrue BoolVariable x) a
        unifier = unify0 $ mkAnd a0 a1
     in do
          u <- unifier
          let subX = mkOr (substitute u a0) (mkAnd (BoolVariable x) (mkNot $ substitute u a1))
          return $ subOne subX u x
