{-# LANGUAGE FlexibleContexts #-}
module TypeChecker.TypedConstr where

import Data.Map as Map

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State

import Parser.AbsSimpleCalc
import Parser.PrintSimpleCalc

import TypeChecker.TyErr
import TypeChecker.CheckMonad
import TypeChecker.Substitution
import TypeChecker.TypeChecker

tAbs :: (MonadError TyErr m) => Lambda -> Identifier -> Type -> TTerm -> m TTerm
tAbs l x a t = return $ Abs (ArrowT a (getType t)) l x t

tApp :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
        TTerm -> TTerm -> m TTerm
tApp s t = do
  a <- resolveTypeHead (getType s)
  case a of
    ArrowT c d -> do
      isType (forgetType t) c (getType t)
      return $ App d s t
    _ -> throwError $ Bad $
      "Internal error: Applying term " ++ printTree s
      ++ " of non-function type " ++ printTree a

tInl :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
       Type -> TTerm -> m TTerm
tInl a t = do
  a' <- resolveTypeHead a
  let b = getType t
  case a' of
    PlusT b' _ -> do
      isType (fmap (\_ -> ()) t) b b'
      return $ Inl a t
    _ -> throwError $ Bad $
      "Internal error: Requesting non-sum type " ++ printTree a'
      ++ " in application of inl to " ++ printTree t

tInr :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
       Type -> TTerm -> m TTerm
tInr a t = do
  a' <- resolveTypeHead a
  let c = getType t
  case a' of
    PlusT _ c' -> do
      isType (fmap (\_ -> ()) t) c c'
      return $ Inr a t
    _ -> throwError $ Bad $
      "Internal error: Requesting non-sum type " ++ printTree a'
      ++ " in application of inl to " ++ printTree t

tIn :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
       Type -> TTerm -> m TTerm
tIn a t = do
  a' <- resolveTypeHead a
  let c = getType t
  case a' of
    LfpT y b -> do
      a'_in_b <- subst (Map.singleton y a') b
      isType (fmap (\_ -> ()) t) c a'_in_b
      return $ In a t
    _ -> throwError $ Bad $
      "Internal error: Requesting non-lfp type " ++ printTree a'
      ++ " in application of in to " ++ printTree t

tFst :: (MonadState CheckS m, MonadError TyErr m) => TTerm -> m TTerm
tFst t = do
  a <- resolveTypeHead (getType t)
  case a of
    TimesT b _ -> return $ Fst b t
    _ -> throwError $ Bad $
      "Internal error: Applying fst to non-product term " ++ printTree t

tSnd :: (MonadState CheckS m, MonadError TyErr m) => TTerm -> m TTerm
tSnd t = do
  a <- resolveTypeHead (getType t)
  case a of
    TimesT _ c -> return $ Snd c t
    _ -> throwError $ Bad $
      "Internal error: Applying snd to non-product term " ++ printTree t

tPair :: (MonadState CheckS m, MonadError TyErr m) => TTerm -> TTerm -> m TTerm
tPair s t = return $ Pair (TimesT (getType s) (getType t)) s t

tOut :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
        TTerm -> m TTerm
tOut t = do
  a <- resolveTypeHead (getType t)
  case a of
    GfpT x b -> do
      a_in_b <- subst (Map.singleton x a) b
      return $ Out a_in_b t
    _ -> throwError $ Bad $
      "Internal error: Applying out to term " ++ printTree t
      ++ " of non-gfp type " ++ printTree a

tRec :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
        TTerm -> TTerm -> m TTerm
tRec s t = do
  a <- resolveTypeHead (getType s)
  b <- resolveTypeHead (getType t)
  case a of
    ArrowT u v -> case b of
      LfpT x b -> do
        return $ Rec v s t
      _ -> throwError $ Bad $
        "Internal error: Applying rec to term " ++ printTree t
        ++ " of non-lfp type " ++ printTree b
    _ -> throwError $ Bad $
      "Internal error: Applying rec to term " ++ printTree s
      ++ " of non-function type " ++ printTree a

tCorec :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
        Type -> TTerm -> TTerm -> m TTerm
tCorec a s t = do
  tyS <- resolveTypeHead (getType s)
  tyT <- resolveTypeHead (getType t)
  case tyS of
    ArrowT u v -> do
      isType (forgetType t) u tyT
      case a of
        GfpT x b -> do
          u_in_b <- subst (Map.singleton x u) b
          isType (forgetType s) u_in_b v
          return $ Corec a s t
        _ -> throwError $ Bad $
          "Internal error: Requesting non-gfp type " ++ printTree a
          ++ " for " ++ printTree (Corec undefined s t)
    _ -> throwError $ Bad $
      "Internal error: Applying corec to term " ++ printTree s
      ++ " of non-function type " ++ printTree a
