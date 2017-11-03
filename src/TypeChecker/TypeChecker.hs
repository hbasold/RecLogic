{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TypeChecker.TypeChecker where

import Data.Map as Map
import Data.Maybe as Data.Maybe

import Control.Applicative
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer

import Data.Generics.Twins
import Data.Generics.Aliases
import Data.Data

import Parser.AbsSimpleCalc
import Parser.PrintSimpleCalc

import TypeChecker.TyErr
import TypeChecker.Substitution
import TypeChecker.CheckMonad

type TyCheckM = ReaderT Env CheckM

noType :: Type
noType = undefined

safeTypeDecl :: Identifier -> Type -> CheckM ()
safeTypeDecl x t = do
  check t
  s <- get
  s' <- if member x (typeDecls s)
        then throwError $ Bad $ "Type " ++ show x ++ " already declared"
        else return s { typeDecls = insert x t (typeDecls s) }
  put s'

isTyVar :: (MonadReader Env m, MonadState CheckS m, MonadError TyErr m) =>
          Identifier -> m Bool
isTyVar x = reader (Map.member x)

isDeclaredType :: (MonadState CheckS m, MonadError TyErr m) =>
                  Identifier -> m (Maybe Identifier)
isDeclaredType x = do
  d <- gets typeDecls
  case Map.lookupIndex x d of
    Nothing -> return Nothing
    Just i -> return $ Just $ fst $ Map.elemAt i d

resolveTypeHead :: (MonadState CheckS m, MonadError TyErr m) => Type -> m Type
resolveTypeHead (VarT (TypeVar x)) = do
  s <- get
  case Map.lookup x (typeDecls s) of
   Nothing -> throwError $ Bad $ "Undeclared type " ++ show x
   Just t -> resolveTypeHead t
resolveTypeHead t = return t

instance Checkable Type where
  check x1 = runReaderT (checkType x1) Map.empty
    where
      checkType :: Type -> TyCheckM ()
      checkType x = case x of
        ArrowT a b -> local (\_ -> Map.empty) (checkType a)
                      >> checkType b
        PlusT a b -> checkType a >> checkType b
        TimesT a b -> checkType a >> checkType b
        LfpT y b -> do
          isDeclTy <- isDeclaredType y
          maybe (return ()) (\y' -> tell [Shadowing y y']) isDeclTy
          local (Map.alter (\_ -> Just noType) y) $ checkType b
        GfpT y b -> do
          isDeclTy <- isDeclaredType y
          maybe (return ()) (\y' -> tell [Shadowing y y']) isDeclTy
          local (Map.alter (\_ -> Just noType) y) $ checkType b
        OneT -> return ()
        VarT (TypeVar i) -> do
          isTV <- isTyVar i
          isDeclTy <- fmap isJust $ isDeclaredType i
          if isTV || isDeclTy
            then return ()
            else throwError $ Bad $ show i ++ " not a type variable or a declared type"

typeEq :: forall m. (Functor m, MonadState CheckS m, MonadError TyErr m) =>
          Type -> Type -> m Bool
typeEq (VarT (TypeVar x)) (VarT (TypeVar y)) =
  if x == y
  then return True
  else do
    s <- get
    case Map.lookup x (typeDecls s) of
     Nothing -> throwError $ Bad $ "Undeclared type " ++ show x
     Just a -> case Map.lookup y (typeDecls s) of
       Nothing -> throwError $ Bad $ "Undeclared type " ++ show y
       Just b -> typeEq a b
typeEq (VarT (TypeVar x)) b = do
  s <- get
  case Map.lookup x (typeDecls s) of
   Nothing -> throwError $ Bad $ "Undeclared type " ++ show x
   Just a -> typeEq a b
typeEq a (VarT (TypeVar y)) = do
  s <- get
  case Map.lookup y (typeDecls s) of
   Nothing -> throwError $ Bad $ "Undeclared type " ++ show y
   Just b -> typeEq a b
typeEq a b =
  if toConstr a == toConstr b
  then fmap and $ sequence $ gzipWithQ ((return True) `mkQ2` typeEq) a b
  else return False

isType :: (Functor m, MonadState CheckS m, MonadError TyErr m) =>
          Term () -> Type -> Type -> m ()
isType x a b = do
  r <- typeEq a b
  if r
    then return ()
    else throwError $ TypeCheckError x $
         "Types "
         ++ printTree a
         ++ " and "
         ++ printTree b
         ++ " do not match"

-- isType x a b = do
--   a' <- resolveTypeHead a
--   b' <- resolveTypeHead b
--   if a' == b'
--     then return ()
--     else throwError $ TypeCheckError x $
--          "Types "
--          ++ printTree a
--          ++ " and "
--          ++ printTree b
--          ++ " do not match."
