{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
module TypeChecker.TypeCheck where

-- Haskell module generated by the BNF converter

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
import TypeChecker.TypeChecker

safeDecl :: Identifier -> Type -> Term () -> CheckM ()
safeDecl x a t = do
  check a
  t' <- runReaderT (typeCheck t a) Map.empty
  s <- get
  s' <- if member x (decls s)
        then throwError $ Bad $ "Object " ++ show x ++ " already declared"
        else return s { decls = insert x (a,t') (decls s) }
  put s'

getVar :: (MonadReader Env m, MonadState CheckS m, MonadError TyErr m) =>
          Identifier -> m Type
getVar x = do
  e <- ask
  case Map.lookup x e of
   Nothing -> getDeclType x
   Just t -> return t

isVar :: (MonadReader Env m, MonadState CheckS m, MonadError TyErr m) =>
         Identifier -> m (Maybe Identifier)
isVar x = do
  e <- ask
  case Map.lookupIndex x e of
    Nothing -> do
      d <- gets decls
      case Map.lookupIndex x e of
        Nothing -> return Nothing
        Just i -> return $ Just $ fst $ Map.elemAt i d
    Just i -> return $ Just $ fst $ Map.elemAt i e

-- transIdentifier :: Identifier -> Result
-- transIdentifier x = case x of
--   Identifier string -> failure x
-- transLambda :: Lambda -> Result
-- transLambda x = case x of
--   Lambda string -> failure x

typeCheck :: (Applicative m, MonadReader Env m, MonadState CheckS m,
              MonadError TyErr m, MonadWriter TyWarnings m) =>
             Term () -> Type -> m TTerm
typeCheck x a = case x of
   Var _ identifier -> do
     a' <- getVar identifier
     isType x a a'
     return $ Var a' identifier
   Unit _ -> isType x a OneT >> return (Unit OneT)
   Inl _ term -> do
     a' <- resolveTypeHead a
     case a' of
      PlusT b _ -> Inl a <$> typeCheck term b
      _ -> throwError $ TypeCheckError x $ printTree a' ++ " is not a sum type"
   Inr _ term -> do
     a' <- resolveTypeHead a
     case a' of
      PlusT _ c -> Inr a <$> typeCheck term c
      _ -> throwError $ TypeCheckError x $ printTree a' ++ " is not a sum type"
   Pair _ term1 term2 -> do
     a' <- resolveTypeHead a
     case a' of
      TimesT b c -> Pair a <$> typeCheck term1 b <*> typeCheck term2 c
      _ -> throwError $ TypeCheckError x $ printTree a' ++ " is not a product type"
   Abs _ l i t -> do
     a' <- resolveTypeHead a
     case a' of
      ArrowT b c -> do
          varExists <- isVar i
          maybe (return ()) (\y' -> tell [Shadowing i y']) varExists
          t' <- local (Map.alter (\_ -> Just b) i) $ typeCheck t c
          return $ Abs a l i t'
      _ -> throwError $ TypeCheckError x $ printTree a' ++ " is not a function type"
   In _ t -> do
     a' <- resolveTypeHead a
     case a' of
      LfpT y b -> do
        a'_in_b <- subst (Map.singleton y a') b
        t' <- typeCheck t a'_in_b
        return $ In a t'
      _ -> throwError $ TypeCheckError x $ printTree a' ++ " is not a lfp type"
   -- App term1 term2 -> do
   --   a1 <- typeInfer term1
   --   case a1 of
   --    ArrowT b c -> isType c a >> typeCheck term2 b
   --    _ -> throwError $ TypeCheckError x $ printTree a1 ++ " is not a function type"
   App _ t1 t2 -> do
     t2' <- typeInfer t2
     App a <$> typeCheck t1 (ArrowT (getType t2') a) <*> pure t2'
   Fst _ t -> do
     t' <- typeInfer t
     a' <- resolveTypeHead $ getType t'
     case a' of
      TimesT b _ -> isType t b a >> return (Fst a t')
                    -- then return ()
                    -- else throwError $ TypeCheckError x $
                    --      "Result type " ++ printTree a
                    --      ++ " of " ++ printTree x
                    --      ++ " does not match expected type " ++ printTree t
      _ -> throwError $ TypeCheckError x $ printTree a' ++ " is not a product type"
   Snd _ t -> do
     t' <- typeInfer t
     a' <- resolveTypeHead $ getType t'
     case a' of
      TimesT _ c -> isType t c a >> return (Snd a t')
                    -- then return ()
                    -- else throwError $ TypeCheckError x $
                    --      "Result type " ++ printTree b
                    --      ++ " of " ++ printTree x
                    --      ++ " does not match expected type " ++ printTree t
      _ -> throwError $ TypeCheckError x $ printTree a' ++ " is not a product type"
   Out _ t -> do
     t' <- typeInfer t
     a' <- resolveTypeHead $ getType t'
     case a' of
      GfpT y b -> do
        a'_in_b <- subst (Map.singleton y a') b
        isType t a a'_in_b
        return $ Out a t'
                    -- then return ()
                    -- else throwError $ TypeCheckError x $
                    --      "Result type " ++ printTree b
                    --      ++ " of " ++ printTree x
                    --      ++ " does not match expected type " ++ printTree t
      _ -> throwError $ TypeCheckError x $ printTree a' ++ " is not a gfp type"
   Match _ i1 t1 i2 t2 s -> do
     s' <- typeInfer s
     a' <- resolveTypeHead $ getType s'
     case a' of
      PlusT b c -> do
        t1' <- local (Map.alter (\_ -> Just b) i1) $ typeCheck t1 a
        t2' <- local (Map.alter (\_ -> Just c) i2) $ typeCheck t2 a
        return $ Match a i1 t1' i2 t2' s'
      _ -> throwError $ TypeCheckError s $ printTree a' ++ " is not a sum type"
   Rec _ t1 t2 -> do
     t2' <- typeInfer t2
     a1 <- resolveTypeHead $ getType t2'
     case a1 of
      LfpT y b -> do
        ba_to_a <- ArrowT <$> subst (Map.singleton y a) b <*> pure a
        Rec a <$> typeCheck t1 ba_to_a <*> pure t2'
      _ -> throwError $ TypeCheckError t2 $ printTree a1 ++ " is not a lfp type"
   Corec _ t1 t2 -> do
     a' <- resolveTypeHead a
     t2' <- typeInfer t2
     let a2 = getType t2'
     case a' of
      GfpT y b -> do
        a2_to_ba2 <- ArrowT a2 <$> subst (Map.singleton y a2) b
        Corec a <$> typeCheck t1 a2_to_ba2 <*> pure t2'
      _ -> throwError $ TypeCheckError x $ printTree a' ++ " is not a gfp type"

getAndResolve :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
                 TTerm -> m (TTerm, Type)
getAndResolve t = (t,) <$> resolveTypeHead (getType t)

typeInfer ::  (Applicative m, MonadReader Env m, MonadState CheckS m,
               MonadError TyErr m, MonadWriter TyWarnings m) =>
              Term () -> m TTerm
typeInfer x = case x of
   Var _ identifier -> Var <$> getVar identifier <*> pure identifier
   Unit _ -> return $ Unit OneT
   Inl _ _t -> failure x
   Inr _ _t -> failure x
   Pair _ t1 t2 -> do
     t1' <- typeInfer t1
     t2' <- typeInfer t2
     return $ Pair (TimesT (getType t1') (getType t2')) t1' t2'
   Abs _ _ _i _t -> failure x
   In _ _t -> failure x
   App _ t1 t2 -> do
     t1' <- typeInfer t1
     a <- resolveTypeHead $ getType t1'
     t2' <- typeInfer t2
     case a of
      ArrowT c d -> isType t2 c (getType t2') >> return (App d t1' t2')
      _ -> throwError $ TypeCheckError t1 $ printTree a ++ " is not a function type"
   Fst _ t -> do
     (t', a) <- typeInfer t >>= getAndResolve
     case a of
      TimesT b _ -> return $ Fst b t'
      _ -> throwError $ TypeCheckError t $ printTree a ++ " is not a product type"
   Snd _ t -> do
     (t', a) <- typeInfer t >>= getAndResolve
     case a of
      TimesT _ c -> return $ Snd c t'
      _ -> throwError $ TypeCheckError t $ printTree a ++ " is not a product type"
   Out _ t -> do
     (t', a) <- typeInfer t >>= getAndResolve
     case a of
      GfpT y b -> Out <$> subst (Map.singleton y a) b <*> pure t'
      _ -> throwError $ TypeCheckError t $ printTree a ++ " is not a gfp type"
   Match _ i1 t1 i2 t2 s -> do
     (s', a) <- typeInfer s >>= getAndResolve
     case a of
      PlusT b c -> do
        t1' <- local (Map.alter (\_ -> Just b) i1) $ typeInfer t1
        t2' <- local (Map.alter (\_ -> Just c) i2) $ typeInfer t2
        let a1 = getType t1'
        isType t2 a1 (getType t2')
        return $ Match a1 i1 t1' i2 t2' s'
      _ -> throwError $ TypeCheckError s $ printTree a ++ " is not a sum type"
   Rec _ _t1 t2 -> do
     (t2', a) <- typeInfer t2 >>= getAndResolve
     case a of
      LfpT _y _b -> failure x -- This requires unification
      _ -> throwError $ TypeCheckError t2 $ printTree a ++ " is not a lfp type"
   Corec _ _t1 _t2 -> throwError $ TypeCheckError x $
                      "Cannot infer type for corec"

-- Just for debugging
checkTyped :: (Applicative m, MonadReader Env m, MonadState CheckS m,
               MonadError TyErr m, MonadWriter TyWarnings m) =>
              TTerm -> m ()
checkTyped t = do
  _ <- typeCheck (fmap (\_ -> ()) t) (getType t)
  sequence_ $ gmapQ ((return ()) `mkQ` checkTyped) t
