-- automatically generated by BNF Converter
module Main where


import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs )
import System.Exit ( exitFailure, exitSuccess )

import Control.Monad.Except

import Parser.LexSimpleCalc
import Parser.ParSimpleCalc
-- import Parser.SkelSimpleCalc
import Parser.PrintSimpleCalc
-- import Parser.AbsSimpleCalc
import Parser.ErrM
import TypeChecker.CheckMonad
import TypeChecker.ProgramChecker()

type ParseFun a = [Token] -> Err a

myLLexer :: String -> [Token]
myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: (Print a, Show a, Checkable a) => Verbosity -> ParseFun a -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: (Print a, Show a, Checkable a) => Verbosity -> ParseFun a -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad e    -> do putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          putStrLn e
                          exitFailure
           Ok  tree -> do putStrLn "\nParse Successful!"
                          showTree v tree
                          checkTree tree
                          exitSuccess


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

checkTree :: (Checkable a) => a -> IO ()
checkTree p =
  let (r, warnings) = runCheck (check p)
  in do
    when (not (null warnings))
        (putStrLn "Warnings:" >> mapM_ (putStrLn . show) warnings)
    case r of
      Left e -> putStrLn "Type error: " >> (putStrLn $ show e)
      Right _ -> putStrLn "Type check successful."

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> hGetContents stdin >>= run 2 pProgram
    "-s":fs -> mapM_ (runFile 0 pProgram) fs
    fs -> mapM_ (runFile 2 pProgram) fs