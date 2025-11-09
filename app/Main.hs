{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Environment (getArgs)
import Compiler.Compiler (compile)
import qualified Data.Text as T

main :: IO ()
main = do
  args <- getArgs
  case args of
    [target, filename] ->
      case target of
        "noname" -> runCompile target filename
        "sapic" -> runCompile target filename
        _  -> putStrLn "Error: target must be 'noname' or 'sapic'"
    _ -> putStrLn "Usage: runhaskell Main.hs (noname|sapic) <filename>.choreo"

runCompile :: String -> FilePath -> IO ()
runCompile target filename =
  case ".choreo" `T.stripSuffix` T.pack filename of
    Just baseName -> do
      let baseName' = T.unpack baseName
      input <- readFile filename
      let res = compile target baseName' input
      case res of
        Left err -> do
          putStrLn "Translation has failed!"
          case target of
            "sapic" -> do 
              writeFile (baseName' ++ ".spthy") ("Error: " ++ show err)
              putStrLn "Hello, world!"
            "noname" -> writeFile (baseName' ++ ".nn") ("Error: " ++ show err)
        Right output -> do
          putStrLn "Translation succeeded!"
          case target of
            "sapic" -> writeFile (baseName' ++ ".spthy") output
            "noname" -> writeFile (baseName' ++ ".nn") output
    Nothing -> putStrLn "Error: File must have .choreo extension"