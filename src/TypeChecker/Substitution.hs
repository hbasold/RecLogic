{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module TypeChecker.Substitution where

import Data.Map as Map

import Control.Applicative
import Control.Monad.State
import Control.Monad.Except

import Parser.AbsSimpleCalc
import Parser.PrintSimpleCalc

import TypeChecker.TyErr
import TypeChecker.CheckMonad

-- | Assumption: All terms we substitute are closed, so that we do not need
-- to worry about α-renaming.
class Substitute a b where
  subst :: (Applicative m, MonadState CheckS m) => Map Identifier b -> a -> m a

instance Substitute Type Type where
  subst m a1 = case a1 of
    ArrowT a b -> ArrowT <$> (subst m a) <*> (subst m b)
    PlusT a b -> PlusT <$> (subst m a) <*> (subst m b)
    TimesT a b -> TimesT <$> (subst m a) <*> (subst m b)
    LfpT x a -> LfpT x <$> subst (delete x m) a
    GfpT x a -> GfpT x <$> subst (delete x m) a
    OneT -> return OneT
    VarT (TypeVar x) ->
      case Map.lookup x m of
        Nothing -> return a1
        Just t -> return t

instance Substitute (Term a) (Term a) where
  subst m t = case t of
    Var _ x ->
      case Map.lookup x m of
        Nothing -> return t
        Just s -> return s
    Unit _ -> return t
    Inl u s -> Inl u <$> subst m s
    Inr u s -> Inr u <$> subst m s
    Pair u s1 s2 -> Pair u <$> (subst m s1) <*> (subst m s2)
    Abs u lam x s -> Abs u lam x <$> subst m s
    In u s -> In u <$> subst m s
    App u s1 s2 -> App u <$> (subst m s1) <*> (subst m s2)
    Fst u s -> Fst u <$> subst m s
    Snd u s -> Snd u <$> subst m s
    Out u s -> Out u <$> subst m s
    Match u x s1 y s2 s3 ->
      (\v -> Match u x v y) <$> (subst m s1) <*> (subst m s2) <*> (subst m s3)
    Rec u s1 s2 -> Rec u <$> (subst m s1) <*> (subst m s2)
    Corec u s1 s2 -> Corec u <$> (subst m s1) <*> (subst m s2)

instance Substitute TFormula (TFormula, PropDecls) where
  subst m f = case f of
    Bottom -> return Bottom
    PropVar x propargs ->
      case Map.lookup x m of
        Nothing -> return f
        Just (g, ds) -> substTerm (mkSubst propargs ds) g
    Implies g h -> Implies <$> (subst m g) <*> (subst m h)
    Or g h -> Or <$> (subst m g) <*> (subst m h)
    And g h -> And <$> (subst m g) <*> (subst m h)
    Forall x a g -> Forall x a <$> subst m g
    Exists x a g -> Exists x a <$> subst m g
    EqForm (Equality s t) -> return f
    Later g -> Later <$> subst m g
    LfpF x propdecls g -> error "Substitution in fixed point formulas not supported, yet"
    GfpF x propdecls g -> error "Substitution in fixed point formulas not supported, yet"

    where
      mkSubst' :: [PropArg a] -> [PropDecl] -> Map Identifier (Term a)
      mkSubst' [] [] = Map.empty
      mkSubst' [] _  = error "Too little argument for proposition"
      mkSubst' _ []  = error "Too many argument for proposition"
      mkSubst' (PropArg t : args) (PropDecl x _ : ds) =
        Map.insert x t $ mkSubst' args ds
      mkSubst :: PropArgs a -> PropDecls -> Map Identifier (Term a)
      mkSubst NoPropArgs NoPropDecls = Map.empty
      mkSubst NoPropArgs _ = error "Too little argument for proposition"
      mkSubst _ NoPropDecls = error "Too many argument for proposition"
      mkSubst (PropArgs args) (PropDecls decls) = mkSubst' args decls

class TermSubstitution a b where
  substTerm :: (Applicative m, MonadState CheckS m) =>
               Map Identifier (Term a) -> b -> m b

instance TermSubstitution a (PropArg a) where
  substTerm m (PropArg t) = PropArg <$> subst m t

instance TermSubstitution a (PropArgs a) where
  substTerm m NoPropArgs = return NoPropArgs
  substTerm m (PropArgs args) = PropArgs <$> mapM (substTerm m) args

renameTo :: (Applicative m, MonadState CheckS m, TermSubstitution a b) =>
            Identifier -> Identifier -> a -> b -> m b
renameTo x z u f = substTerm (Map.singleton x (Var u z)) f

instance TermSubstitution Type TFormula where
  substTerm m f = case f of
   Bottom -> return Bottom
   PropVar x propargs -> PropVar x <$> substTerm m propargs
   Implies g h -> Implies <$> (substTerm m g) <*> (substTerm m h)
   Or g h -> Or <$> (substTerm m g) <*> (substTerm m h)
   And g h -> And <$> (substTerm m g) <*> (substTerm m h)
   Forall x a g -> do
     x' <- fresh x
     g' <- renameTo x x' a g
     Forall x' a <$> substTerm m g'
   Exists x a g -> do
     x' <- fresh x
     g' <- renameTo x x' a g
     Exists x' a <$> substTerm m g'
   EqForm (Equality s t) -> EqForm <$> (Equality <$> (subst m s) <*> (subst m t))
   Later g -> Later <$> substTerm m g
   LfpF x propdecls g -> LfpF x propdecls <$> substTerm m g
   GfpF x propdecls g -> GfpF x propdecls <$> substTerm m g
