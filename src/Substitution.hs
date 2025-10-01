module Substitution (subOne) where

subOne :: (Eq v) => a -> (v -> a) -> v -> v -> a
subOne sub base x y
  | x == y = sub
  | otherwise = base y
