{-# LANGUAGE InstanceSigs #-}

module Pretty (prettyType) where

import Boolean (Boolean (..))
import Prettyprinter (pretty, (<+>))
import qualified Prettyprinter as PP
import Prettyprinter.Render.Terminal (AnsiStyle)
import Term (Type (..), TypeT (..))

newtype PrettyBoolean = PB Boolean deriving (Show)

instance PP.Pretty PrettyBoolean where
  pretty :: PrettyBoolean -> PP.Doc ann
  pretty (PB b) = case b of
    BoolTrue -> pretty "•"
    BoolFalse -> pretty "×"
    BoolVariable x -> pretty "u" <> pretty x
    BoolAnd x y -> binOp x y "∧"
    BoolOr x y -> binOp x y "∨"
    BoolNot x -> pretty "¬" <> recurse x
    where
      recurse = PP.parens . pretty . PB
      binOp l r sep = recurse l <+> pretty sep <+> recurse r

newtype PrettyType = PT Type deriving (Show)

instance PP.Pretty PrettyType where
  pretty :: PrettyType -> PP.Doc ann
  pretty (PT (Attr (TypeArrow x y) u)) = recurse x <+> pretty "-" <> pretty (PB u) <> pretty ">" <+> recurse y
    where
      recurse = PP.parens . pretty . PT
  pretty (PT (Attr t u)) =
    let pt = case t of
          TypeBool -> pretty "bool"
          TypeInt -> pretty "int"
          TypeVariable x -> pretty "t" <> pretty x
     in pt <> (PP.braces $ pretty $ PB u)

prettyType :: Type -> PP.Doc AnsiStyle
prettyType t = pretty $ PT $ t
