{-# LANGUAGE FlexibleContexts #-}
module TypeChecker.Reductions where

import Data.Map as Map
import Data.Function
import Data.Generics (Data, Typeable, mkQ, everything)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative

import Parser.AbsSimpleCalc
import Parser.PrintSimpleCalc

import TypeChecker.TyErr
import TypeChecker.CheckMonad
import TypeChecker.Substitution
import TypeChecker.TypedConstr
import TypeChecker.TypeChecker
import TypeChecker.TypeCheck

lam :: Lambda
lam = Lambda "\\"

fresh' :: (MonadState CheckS m) => String -> m Identifier
fresh' x = fresh $ Identifier ((0,0), x)

-- | identity map id : A -> A
idTerm :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
          Type -> m TTerm
idTerm a = do
  x <- fresh' "x"
  tAbs lam x a $ Var a x
  -- return $ Abs (ArrowT a a) lam x $ Var a x

-- | Maps s : A -> B and t : B -> C to t o s : B -> C
comp :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
        TTerm -> TTerm -> m TTerm
comp t s = case (getType s, getType t) of
  (ArrowT a b, ArrowT b' c) -> do
    x <- fresh' "x"
    tAbs lam x a =<< tApp t =<< tApp s (Var a x)
--    return $ Abs (ArrowT a c) lam x $ App c t $ App b s $ Var a x
  _ -> error "Composition of non-function terms"

-- | Maps s : A -> B and t : C -> D to s + t : A * C -> B * D
timesTerm :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
             TTerm -> TTerm -> m TTerm
timesTerm s t = case (getType s, getType t) of
  (ArrowT a c, ArrowT b d) -> do
    x <- fresh' "x"
    let tx = Var (TimesT a b) x
    s_tx_fst <- tApp s =<< tFst tx
    t_tx_snd <- tApp t =<< tSnd tx
    tAbs lam x (TimesT a b) =<< tPair s_tx_fst t_tx_snd
    -- return $ Abs (ArrowT (TimesT a c) (TimesT b d)) lam x $
    --   Pair (TimesT b d) (App b s $ Fst a tx) (App d t $ Snd b tx)
  _ -> error "Product of non-function terms"

-- | Maps s : A -> B and t : C -> D to s + t : A + C -> B + D
plusTerm :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
            TTerm -> TTerm -> m TTerm
plusTerm s t = case (getType s, getType t) of
  (ArrowT a c, ArrowT b d) -> do
    x <- fresh' "x"
    y <- fresh' "y"
    z <- fresh' "z"
    let tx = Var (PlusT a b) x
        ty = Var a y
        tz = Var b z
    s_ty <- tApp s ty
    t_tz <- tApp t tz
    tAbs lam x (PlusT a b) =<<
      Match (PlusT c d)
      y <$> tInl (PlusT c d) s_ty <*>
      pure z <*> tInr (PlusT c d) t_tz <*>
      pure tx

isClosed :: Type -> Bool
isClosed = isClosed'
  where
    isClosed' :: Data d => d -> Bool
    isClosed' = everything (&&) (mkQ True (\(TypeVar _) -> False))

tyActDom :: (Applicative m, MonadState CheckS m) =>
            Type -> Map Identifier TTerm -> m Type
tyActDom a m = subst (fmap getDom m) a
  where
    getDom :: TTerm -> Type
    getDom t = case getType t of
      ArrowT a _ -> a
      _ -> error $ "Extracting domain from non-function term: " ++ printTree t

tyActCodom :: (Applicative m, MonadState CheckS m) =>
              Type -> Map Identifier TTerm -> m Type
tyActCodom a m = subst (fmap getCodom m) a
  where
    getCodom :: TTerm -> Type
    getCodom t = case getType t of
      ArrowT _ b -> b
      _ -> error $ "Extracting codomain from non-function term: " ++ printTree t

-- | Maps a type T with free variables Xi and terms ti : Ai -> Bi for each Xi to
-- a term T(ts) : T[Ai/Xi] -> T[Bi/Xi].
tyAct :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
         Type -> Map Identifier TTerm -> m TTerm
tyAct a m =
  if isClosed a
  then idTerm a
  else do
    dom <- tyActDom a m
    cod <- tyActCodom a m
    tyAct' a m dom cod
  where
    -- The last two type arguments are the domain/codomain of the resulting map.
    tyAct' :: (Applicative m, MonadState CheckS m, MonadError TyErr m) =>
              Type -> Map Identifier TTerm -> Type -> Type -> m TTerm
    tyAct' a ts dom cod = case (a, dom, cod) of
      (ArrowT b c, ArrowT b1 c1, ArrowT b2 c2) -> do
        f <- fresh' "f"
        t <- tyAct' c ts c1 c2
        c <- comp t (Var (ArrowT b1 c1) f)
        return $ Abs (ArrowT dom cod) lam f c
      (PlusT b c, PlusT b1 c1, PlusT b2 c2) -> do
        s <- tyAct' b ts b1 b2
        t <- tyAct' c ts c1 c2
        plusTerm s t
      (TimesT b c, TimesT b1 c1, TimesT b2 c2) -> do
        s <- tyAct' b ts b1 b2
        t <- tyAct' c ts c1 c2
        timesTerm s t
      (LfpT x b, LfpT x1 bDom, LfpT x2 bCod) -> do
        y <- fresh' "y"
        z <- fresh' "z"
        bDom' <- subst (Map.singleton x1 cod) bDom
        bCod' <- subst (Map.singleton x2 cod) bCod
        id <- idTerm cod
        t <- tyAct b (Map.alter (\_ -> Just id) x ts)
        s <- tAbs lam z bDom' =<< tIn cod =<< tApp t (Var bDom' z)
        tAbs lam y dom =<< tRec s (Var dom y)
--        let s = Abs (ArrowT bDom' cod) lam z $ In cod $ App bCod' t $ Var bDom' z
--        return $ Abs (ArrowT dom cod) lam y $ Rec cod s $ Var dom y
      (GfpT x b, GfpT x1 bDom, GfpT x2 bCod) -> do
        y <- fresh' "y"
        z <- fresh' "z"
        bDom' <- subst (Map.singleton x1 dom) bDom
        bCod' <- subst (Map.singleton x2 dom) bCod
        id <- idTerm dom
        t <- tyAct b $ Map.alter (\_ -> Just id) x ts
        let s = Abs (ArrowT dom bCod') lam z $ App bCod' t $ Out bDom' $ Var dom z
        return $ Abs (ArrowT dom cod) lam y $ Corec cod s $ Var dom y
      (OneT, _, _) -> idTerm OneT
      (VarT (TypeVar x), _, _) -> case Map.lookup x ts of
        Nothing -> do
          r <- isDeclaredType x
          case r of
            Nothing -> throwError $ Bad $
              "Internal error in tyAct: Variable " ++ show x ++ " undefined"
            Just _ -> idTerm a
        Just t -> return t

-- | Problem: reduce only works on typed terms! Or we need to annotate (co)rec.

reduce :: (Applicative m, MonadState CheckS m, MonadError TyErr m
          , MonadWriter TyWarnings m) =>
          TTerm -> m TTerm
reduce t1 = do
  -- issueWarning $ GenericWarning $
  --   "Reducing " ++ printTree t1
  t1' <- reduce' t1
  -- issueWarning $ GenericWarning $
  --   "Obtained " ++ printTree t1'
  return t1'

reduce' :: (Applicative m, MonadState CheckS m, MonadError TyErr m
          , MonadWriter TyWarnings m) =>
          TTerm -> m TTerm
reduce' t1 = case t1 of
  Var _ x -> do
    d <- getDecl x
    case d of
     Just (_, t) -> reduce t
     Nothing -> return t1
  Unit _ -> return t1
  Inl a t -> Inl a <$> reduce t
  Inr a t -> Inr a <$> reduce t
  Pair a s t -> Pair a <$> reduce s <*> reduce t
  Abs a l x t -> Abs a l x <$> reduce t
  In a t -> In a <$> reduce t
  App a s t -> do
    s' <- reduce s
    case s' of
     Abs _ _ x u -> subst (Map.singleton x t) u >>= reduce
     _ -> App a s' <$> reduce t
  Fst a t -> do
    t' <- reduce t
    case t' of
     Pair _ s _ -> return s
     _ -> return $ Fst a t'
  Snd a t -> do
    t' <- reduce t
    case t' of
     Pair _ _ s -> return s
     _ -> return $ Snd a t'
  Out a u -> do
    u' <- reduce u
    x <- fresh' "x"
    case u' of
     Corec gfp' s t -> do
       gfp <- resolveTypeHead gfp'
       case gfp of
         GfpT y b -> do
           corec_s <- tAbs lam x (getType t) =<< tCorec gfp s (Var (getType t)  x)
           b_corec_s <- tyAct b (Map.singleton y corec_s)
           reduce =<< tApp b_corec_s =<< tApp s t
     _ -> return $ Out a u'
  Match a x s y t u -> do
    u' <- reduce u
    case u' of
     Inl _ v -> reduce =<< subst (Map.singleton x v) s
     Inr _ v -> reduce =<< subst (Map.singleton y v) t
     _ -> return $ Match a x s y t u'
  Rec a s t -> do
    t' <- reduce t
    x <- fresh' "x"
    case t' of
     In lfp' u -> do
       lfp <- resolveTypeHead lfp'
       case lfp of
         LfpT y b -> do
           rec_s <- tAbs lam x lfp =<< tRec s (Var lfp x)
           b_rec_s <- tyAct b (Map.singleton y rec_s)
           b_rec_s_u <- tApp b_rec_s u
           reduce =<< tApp s b_rec_s_u
         _ -> throwError $ Bad $ "Internal error: When reducing "
           ++ printTree t1 ++ ", the type " ++ printTree lfp' ++ " of "
           ++ printTree t' ++ " is not an lfp-type."
     _ -> return $ Rec a s t'
  Corec a s t -> Corec a s <$> reduce t

convertibleTo :: (Applicative m, MonadState CheckS m, MonadError TyErr m,
                  MonadWriter TyWarnings m, MonadReader Env m) =>
                 TTerm -> TTerm -> m Bool
convertibleTo s t = do
  -- issueWarning $ GenericWarning $
  --   "Reducing " ++ printTree s ++ " for comparison"
  s' <- reduce s
  -- issueWarning $ GenericWarning $
  --   "Reducing " ++ printTree t ++ " for comparison"
  t' <- reduce t
  -- issueWarning $ GenericWarning $
  --   "Comparing normal forms " ++ printTree s' ++ " and " ++ printTree t'
  -- issueWarning $ GenericWarning $
  --   "Comparing normal forms " ++ show s' ++ " and " ++ show t'
  --   ++ " of " ++ printTree s ++ " and " ++ printTree t
  --   ++ " -> " ++ show (s' == t')
  -- checkTyped s'
  -- checkTyped t'
  return $ s' == t'
