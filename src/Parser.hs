module Parser (parse) where

import Control.Applicative (many, (<|>))
import Control.Monad (msum, void)
import Data.Char (isAlpha)
import Data.Void (Void)
import Term (Term (..), annotateSharing)
import Text.Megaparsec (Parsec, eof, runParser, satisfy, try)
import Text.Megaparsec.Char (char, space, string)
import Text.Megaparsec.Error (ParseErrorBundle)

type Parser = Parsec Void String

spaced :: Parser a -> Parser a
spaced p = space *> p <* space

parenthesized :: Parser a -> Parser a
parenthesized p = do
  void $ char '('
  a <- p
  void $ char ')'
  return a

variable :: Parser String
variable = many $ satisfy isAlpha

boundVariable :: [String] -> Parser Int
boundVariable xs =
  let parsers = zipWith (\s idx -> (string s >> return idx)) xs ([0 ..] :: [Int])
   in msum parsers

abstraction :: [String] -> Parser Term
abstraction xs = do
  void $ string "\\"
  x <- variable
  space
  void $ string "."
  t <- term (x : xs)
  return $ annotateSharing $ TermAbstraction t

application :: [String] -> Parser Term
application xs =
  let oneTerm = (try $ parenthesized $ term xs) <|> (TermVariable False <$> boundVariable xs)
   in do
        a <- oneTerm
        space
        b <- oneTerm
        space
        return $ TermApplication a b

term :: [String] -> Parser Term
term xs =
  spaced $
    msum
      [ try $ application xs,
        TermVariable False <$> boundVariable xs,
        abstraction xs
      ]

parse :: String -> Either (ParseErrorBundle String Void) Term
parse = runParser (liftA2 const (term []) eof) mempty
