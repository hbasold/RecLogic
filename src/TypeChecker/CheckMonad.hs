{-# LANGUAGE FlexibleContexts #-}
module TypeChecker.CheckMonad where

import Data.Map as Map

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer

import Parser.AbsSimpleCalc

import TypeChecker.TyErr

data CheckS =
  CheckS
  { typeDecls :: Map Identifier Type
  , decls :: Map Identifier (Type, TTerm)
  , thms :: Map Identifier (ThmDecls, TFormula)
  , defs :: Map Identifier (ThmDecls, TFormula)
  , varCounter :: Int
  }

initialCheckState :: CheckS
initialCheckState = CheckS Map.empty Map.empty Map.empty Map.empty 1

type CheckRes = (Either TyErr (), TyWarnings)
type CheckM = StateT CheckS (ExceptT TyErr (Writer TyWarnings))

type Env = Map Identifier Type

class Checkable a where
  check :: a -> CheckM ()

runCheck :: CheckM () -> CheckRes
runCheck m = runWriter $ runExceptT $ evalStateT m initialCheckState

uniqueDecl :: (CheckS -> Map Identifier a) ->
              (Map Identifier a -> CheckS -> CheckS) ->
              Identifier -> a -> String -> CheckM ()
uniqueDecl getter setter x v t = do
  s <- get
  let m = getter s
  s' <- if member x m
        then throwError $ Bad $ t ++ " " ++ show x ++ " already declared"
        else return $ setter (insert x v m) s
  put s'

getDecl :: (MonadState CheckS m) => Identifier -> m (Maybe (Type,TTerm))
getDecl x = gets (Map.lookup x . decls)

getDeclType :: (MonadState CheckS m, MonadError TyErr m) =>
               Identifier -> m Type
getDeclType x = do
  r <- getDecl x
  case r of
   Just (a,t) -> return a
   Nothing -> throwError $ Bad $ show x ++ " not declared."

-- | If the variable x is in the environment e, then
-- getDeclPosition x e returns an identifier with the position, where
-- x has been delared.
-- Unfortunately, this map requires two lookups, thus is rather inefficient
-- for now.
getDeclPosition :: Identifier -> Env -> Maybe Identifier
getDeclPosition x e = case Map.lookupIndex x e of
  Nothing -> Nothing
  Just i -> Just $ fst $ elemAt i e

issueWarning :: (MonadWriter TyWarnings m) => TyWarning -> m ()
issueWarning w = tell [w]

fresh :: (MonadState CheckS m) => Identifier -> m Identifier
fresh i = state (genName i)
  where
    genName (Identifier (p, x)) s =
      let c = varCounter s
      in (Identifier (p, x ++ "_" ++ show c), s { varCounter = c + 1 })
