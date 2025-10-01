module Main (main) where

import Parser (parse)
import Pretty (prettyType)
import Term (reconstructType)
import Text.Megaparsec.Error (errorBundlePretty)

main :: IO ()
main = do
  input <- getLine
  if input == "q" || input == "quit"
    then putStrLn "Exiting"
    else do
      case parse input of
        Left err -> putStrLn $ errorBundlePretty err
        Right term -> case reconstructType term of
          Nothing -> (putStrLn "failed to reconstruct type")
          Just tp -> print $ prettyType tp
      main
