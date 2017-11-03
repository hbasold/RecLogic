{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
-- This file comes with NO WARRANTY and may be used FOR ANY PURPOSE.
module TypeChecker.TyErr where

import Control.Monad.Except
import GHC.Stack

import Parser.AbsSimpleCalc
import Parser.PrintSimpleCalc

data TyErr
  = Bad String
  | UnknownVariable Identifier
  | TypeCheckError (Term ()) String
  | FormulaCheckError (Formula ()) String
  | ProofCheckError (Proof ()) String
  deriving (Eq, Ord)

instance Show TyErr where
  show (Bad e) = e
  show (UnknownVariable (Identifier (p, x))) =
    "Unknown identifier " ++ x ++ " at position " ++ show p
  show (TypeCheckError t e) = e ++ " while typechecking " ++ printTree t
  show (FormulaCheckError t e) = e ++ " while checking formula " ++ printTree t
  show (ProofCheckError t e) = e ++ " while checking proof " ++ printTree t

data TyWarning
  = Shadowing Identifier Identifier
  | UnfilledHole (Formula Type)
  | GenericWarning String

instance Show TyWarning where
  show (Shadowing (Identifier (px, x)) (Identifier (py, y))) =
    "Variable " ++ show x ++ " at " ++ show px ++ " shadows "
    ++ show y ++ " from " ++ show py
  show (UnfilledHole f) =
    "Unfilled hole when checking proof for " ++ printTree f
  show (GenericWarning w) = w

type TyWarnings = [TyWarning]

failure :: (?loc :: CallStack, MonadError TyErr m, Print a) => a -> m b
failure x = throwError $ Bad $ "Undefined case: " ++ printTree x ++ "\n" ++ prettyCallStack ?loc

ignore :: (Monad m) => a -> m ()
ignore _ = return ()
