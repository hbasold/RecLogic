{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
module TypeChecker.ProofChecker where

import Data.Map as Map hiding (foldl)
import Data.Data (Data, cast, toConstr)
import Data.Generics.Twins

import Control.Applicative
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer

import Parser.AbsSimpleCalc
import Parser.PrintSimpleCalc

import TypeChecker.TyErr
import TypeChecker.Substitution
import TypeChecker.CheckMonad
import TypeChecker.TypedConstr
import TypeChecker.TypeChecker
import TypeChecker.TypeCheck
import TypeChecker.Reductions

type PropEnv = Map Identifier PropDecls
type ProofEnv = Map Identifier TFormula
data ProofCheckEnv =
  ProofCheckEnv
  { varEnv :: Env
  , propEnv :: PropEnv
  , proofEnv :: ProofEnv
  }
initialProofCheckEnv :: ProofCheckEnv
initialProofCheckEnv = ProofCheckEnv Map.empty Map.empty Map.empty
newtype ProofCheckM a
  = ProofCheckM (ReaderT ProofCheckEnv CheckM a)
  deriving (Functor, Applicative, Monad, MonadState CheckS
           , MonadError TyErr, MonadWriter TyWarnings)

instance MonadReader Env ProofCheckM where
  ask = ProofCheckM $ reader varEnv
  local f (ProofCheckM r) =
    ProofCheckM (local (\e -> e { varEnv = f (varEnv e) }) r)

askPr :: ProofCheckM ProofCheckEnv
askPr = ProofCheckM ask

readerPr :: (ProofCheckEnv -> a) -> ProofCheckM a
readerPr f = ProofCheckM (reader f)

localPr :: (ProofCheckEnv -> ProofCheckEnv) -> ProofCheckM a -> ProofCheckM a
localPr f (ProofCheckM m) = ProofCheckM (local f m)

askProofEnv :: ProofCheckM ProofEnv
askProofEnv = ProofCheckM $ reader proofEnv

localProofEnv :: (ProofEnv -> ProofEnv) -> ProofCheckM a -> ProofCheckM a
localProofEnv f (ProofCheckM r) =
  ProofCheckM (local (\e -> e { proofEnv = f (proofEnv e) }) r)

localPropEnv :: (PropEnv -> PropEnv) -> ProofCheckM a -> ProofCheckM a
localPropEnv f (ProofCheckM r) =
  ProofCheckM (local (\e -> e { propEnv = f (propEnv e) }) r)

getPropDecl :: Identifier -> ProofCheckM PropDecls
getPropDecl p = do
  props <- readerPr propEnv
  case Map.lookup p props of
    Nothing -> throwError $ UnknownVariable p
    Just d -> return d

runProofCheckM :: ProofCheckM a -> ProofCheckEnv -> CheckM a
runProofCheckM (ProofCheckM r) = runReaderT r

liftPr :: CheckM a -> ProofCheckM a
liftPr m = ProofCheckM $ lift m

checkPropDecl :: PropDecl -> ProofCheckM ()
checkPropDecl d = case d of
  PropDecl _ a -> liftPr $ check a
checkPropDecls :: PropDecls -> ProofCheckM ()
checkPropDecls ds = case ds of
  NoPropDecls -> return ()
  PropDecls propdecls -> foldM (\_ -> checkPropDecl) () propdecls

checkPropArg :: (PropDecl, PropArg ()) -> ProofCheckM TPropArg
checkPropArg u = case u of
  (PropDecl _ a, PropArg t) -> PropArg <$> typeCheck t a

checkPropArgs :: Identifier -> PropArgs () -> ProofCheckM TPropArgs
checkPropArgs x args = do
  d <- getPropDecl x
  case d of
    NoPropDecls -> case args of
      NoPropArgs -> return NoPropArgs
      PropArgs _ ->
        throwError $ FormulaCheckError (PropVar x args) $
        "Too many arguments provided"
    PropDecls propdecls -> case args of
      NoPropArgs -> throwError $ FormulaCheckError (PropVar x args) $
        "Too little arguments provided"
      PropArgs propargs ->
        PropArgs <$> mapM checkPropArg (zip propdecls propargs)

checkFormula :: Formula () -> ProofCheckM TFormula
checkFormula f = case f of
  Bottom -> return Bottom
  PropVar x propargs -> PropVar x <$> checkPropArgs x propargs
  Implies g h -> Implies <$> checkFormula g <*> checkFormula h
  Or g h -> Or <$> checkFormula g <*> checkFormula h
  And g h -> And <$> checkFormula g <*> checkFormula h
  Forall x a g -> do
    liftPr (check a)
    Forall x a <$> local (Map.alter (\_ -> Just a) x) (checkFormula g)
  Exists x a g -> do
    liftPr (check a)
    Exists x a <$> local (Map.alter (\_ -> Just a) x) (checkFormula g)
  EqForm (Equality t s) -> do
    t' <- typeInfer t
    s' <- typeCheck s (getType t')
    return $ EqForm $ Equality t' s'
  Later g -> Later <$> checkFormula g
  LfpF p propdecls g -> do
    checkPropDecls propdecls
    LfpF p propdecls <$>
      localPropEnv (Map.alter (\_ -> Just propdecls) p) (checkFormula g)
  GfpF p propdecls g -> do
    checkPropDecls propdecls
    GfpF p propdecls <$>
      localPropEnv (Map.alter (\_ -> Just propdecls) p) (checkFormula g)

-- | Assumption: Given formulas have already been checked.
-- FIXME: Implement check for fixed points.
alphaEquiv :: (Applicative m, MonadState CheckS m, MonadError TyErr m,
                  MonadWriter TyWarnings m, MonadReader Env m) =>
              TFormula -> TFormula -> m Bool
alphaEquiv = alphaCmp
  where
    cmpPropArgs :: (Applicative m, MonadState CheckS m, MonadError TyErr m,
                    MonadWriter TyWarnings m, MonadReader Env m) =>
                   TPropArgs -> TPropArgs -> m Bool
    cmpPropArgs NoPropArgs NoPropArgs = return True
    cmpPropArgs NoPropArgs (PropArgs _) = return False
    cmpPropArgs (PropArgs _) NoPropArgs = return True
    cmpPropArgs (PropArgs args1) (PropArgs args2) =
      fmap and $ sequence [s `convertibleTo` t | PropArg s <- args1, PropArg t <- args2]

    alphaCmp :: (Applicative m, MonadState CheckS m, MonadError TyErr m,
                 MonadWriter TyWarnings m, MonadReader Env m,
                 Data d1, Data d2) =>
                d1 -> d2 -> m Bool
    alphaCmp u v = case (tFormCast u, tFormCast v) of
      (Just (PropVar x args1), Just (PropVar y args2)) ->
        if x == y then cmpPropArgs args1 args2 else return False
      -- This case is necessary to ignore the position in identifiers
      (Just (EqForm (Equality s1 t1)), Just (EqForm (Equality s2 t2))) ->
        liftM2 (&&) (s1 `convertibleTo` s2) (t1 `convertibleTo` t2)
--        return $ s1 == s2 && t1 == t2
      -- Case for α-renaming variables
      (Just (Forall x a f), Just (Forall y b g)) -> do
        z <- fresh x
        f' <- renameTo x z a f
        g' <- renameTo y z b g
        alphaCmp f' g'
      (Just (Exists x a f), Just (Exists y b g)) -> do
        z <- fresh x
        f' <- renameTo x z a f
        g' <- renameTo y z b g
        alphaCmp f' g'
      _ -> if toConstr u == toConstr v
           then (and <$> (sequence $ gzipWithQ alphaCmp u v))
           else return False
      where
        tFormCast :: Data a => a -> Maybe TFormula
        tFormCast = cast

formulasEqual :: Proof () -> TFormula -> TFormula -> ProofCheckM ()
formulasEqual p f g = do
  -- issueWarning $ GenericWarning $
  --   "Checking equivalence of " ++ printTree f ++
  --   " and " ++ printTree g
  alphaEq <- f `alphaEquiv` g
  when (not $ alphaEq) $
    (throwError $ ProofCheckError p $
     "Expected proof for " ++ printTree f ++ " but have " ++ printTree g)

checkThmArg :: ThmArg () -> CheckM TThmArg
checkThmArg x = case x of
  ThmArg formula -> failure x
checkThmArgs :: ThmArgs () -> CheckM TThmArgs
checkThmArgs x = case x of
  NoArgs -> failure x
  Args thmargs -> failure x

checkFormulaUnderPropDecls :: PropDecls -> Formula () -> ProofCheckM TFormula
checkFormulaUnderPropDecls d = local (mkEnv d) . checkFormula
  where
    mkEnv :: PropDecls -> Env -> Env
    mkEnv NoPropDecls e = e
    mkEnv (PropDecls decls) e =
      foldl (\e' (PropDecl x a) -> Map.alter (\_ -> Just a) x e')
      e decls

instThm :: Proof () -> ThmDecls -> ThmArgs () -> TFormula -> ProofCheckM TFormula
instThm p NoDeclArgs NoArgs g = return g
instThm p NoDeclArgs (Args _) _ =
  throwError $ ProofCheckError p $
  "Too many arguments provided to theorem"
instThm p (DeclArgs _) NoArgs _ =
  throwError $ ProofCheckError p $
  "Too little arguments provided to theorem"
instThm p (DeclArgs decls) (Args thmargs) g = do
  s <- mkSubst decls thmargs
  subst s g
  where
    mkSubst :: [ThmDecl] -> [ThmArg ()] -> ProofCheckM (Map Identifier (TFormula,PropDecls))
    mkSubst [] [] = return Map.empty
    mkSubst [] (_ : _) =
      throwError $ ProofCheckError p $
      "Too many arguments provided to theorem"
    mkSubst (_:_) [] =
      throwError $ ProofCheckError p $
      "Too little arguments provided to theorem"
    mkSubst (ThmDecl x d : ds) (ThmArg f : a) = do
      f' <- checkFormulaUnderPropDecls d f
      Map.insert x (f', d) <$> mkSubst ds a

  -- case (hintL, hintR) of
  --   (Nothing, Nothing) -> _
  --   (Just l, Nothing) -> _
  --   (Nothing, Just r) -> _
  --   (Just l, Just r) -> _

strip :: (MonadError TyErr m) =>
         String -> (TTerm -> Maybe TTerm) -> Proof () -> Maybe TTerm -> m (Maybe TTerm)
strip _     _       _  Nothing = return Nothing
strip shape matcher p (Just t) =
  case matcher t of
   Nothing -> throwError $ ProofCheckError p $
              "The term " ++ printTree t ++
              " is not of the form (" ++ shape ++ ")"
   Just s -> return $ Just s

stripInl, stripInr, stripIn, stripOut, stripFst, stripSnd
  :: (MonadError TyErr m) => Proof () -> Maybe TTerm -> m (Maybe TTerm)
stripInl = strip "inl s" m
  where
    m (Inl _ s) = Just s
    m _         = Nothing

stripInr = strip "inr s" m
  where
    m (Inr _ s) = Just s
    m _         = Nothing

stripIn = strip "in s" m
  where
    m (In _ s) = Just s
    m _         = Nothing

stripOut = strip "s.out" m
  where
    m (Out _ s) = Just s
    m _         = Nothing

stripFst = strip "s.fst" m
  where
    m (Fst _ s) = Just s
    m _         = Nothing

stripSnd = strip "s.snd" m
  where
    m (Snd _ s) = Just s
    m _         = Nothing

-- | Infer formula for an equality proof with possible hints for left and
-- right side of the equality.
eqProofInfer :: Proof () -> Maybe TTerm -> Maybe TTerm -> ProofCheckM TFormula
eqProofInfer p1 hintL hintR = case p1 of
  PrHole -> case (hintL, hintR) of
    (Nothing, Nothing) -> throwError $ ProofCheckError p1 $
      "Cannot infer terms for equality."
    (Just l, Nothing) -> throwError $ ProofCheckError p1 $
      "Cannot infer right term for equality " ++ printTree l ++ " ~ ??"
    (Nothing, Just r) -> throwError $ ProofCheckError p1 $
      "Cannot infer left term for equality ?? ~ " ++ printTree r
    (Just l, Just r) -> return $ (EqForm $ Equality l r)
  PrVar _ -> proofInfer p1
  PrBotElim _ -> proofInfer p1
  PrThmInst _ _ -> proofInfer p1
  PrImplIntro _ _ _ -> proofInfer p1
  PrImplElim _ _ -> proofInfer p1
  PrAndIntro _ _ -> proofInfer p1
  PrAndElimFst _ -> proofInfer p1
  PrAndElimSnd _ -> proofInfer p1
  PrOrIntroLeft _ -> proofInfer p1
  PrOrIntroRight _ -> proofInfer p1
  PrOrElim _ _ -> proofInfer p1
  PrNec _ -> proofInfer p1
  PrFP _ _ -> proofInfer p1
  PrAllIntro _ _ -> proofInfer p1
  PrAllElim _ _ -> proofInfer p1
  PrExIntro _ _ -> proofInfer p1
  PrExElim _ _ _ -> proofInfer p1
  PrRefl s t -> do
    (s', t') <- case (hintL, hintR) of
      (Nothing, Nothing) -> do
        s' <- typeInfer s
        t' <- typeCheck t (getType s')
        return (s', t')
      (Just l, _) ->
        (,) <$> typeCheck s (getType l) <*> typeCheck t (getType l)
      (Nothing, Just r) ->
        (,) <$> typeCheck s (getType r) <*> typeCheck t (getType r)
    conv <- s' `convertibleTo` t'
    when (not conv)
      (throwError $ ProofCheckError p1 $
       printTree s ++ " not convertible to " ++ printTree t)
    return $ EqForm $ Equality s' t'
  PrSym p -> do
      f <- eqProofInfer p hintR hintL
      case f of
        EqForm (Equality t s) -> return $ (EqForm $ Equality s t)
        _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not an equality"

  PrTrans p q -> case (hintL, hintR) of
    (Nothing, Nothing) -> do
      f <- eqProofInfer p hintL Nothing
      case f of
        EqForm (Equality s t) -> do
          -- We have now p : s ~ t, thus we know q : t ~ ?
          g <- eqProofInfer q (Just t) Nothing
          case g of
            EqForm (Equality t' u) ->
              if t == t'
              then return $ EqForm $ Equality s u
              else throwError $ ProofCheckError p1 $
                   "Terms " ++ printTree t ++ " and " ++ printTree t'
                   ++ " do not match"
            _ -> throwError $ ProofCheckError p $
              printTree g ++ " is not an equality"
        _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not an equality"
    (Just l, Nothing) -> do
      f <- eqProofInfer p hintL Nothing
      case f of
        EqForm (Equality s t) -> do
          -- We have now p : s ~ t, thus we know q : t ~ ?
          g <- eqProofInfer q (Just t) Nothing
          case g of
            EqForm (Equality t' u) ->
              if t == t'
              then return $ EqForm $ Equality s u
              else throwError $ ProofCheckError p1 $
                   "Terms " ++ printTree t ++ " and " ++ printTree t'
                   ++ " do not match"
            _ -> throwError $ ProofCheckError p $
              printTree g ++ " is not an equality"
        _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not an equality"
    (Nothing, Just r) -> do
      -- We know q : ? ~ r
      g <- eqProofInfer q Nothing hintR
      case g of
        EqForm (Equality s t) -> do
          -- Now we must have t = r and p : ? ~ s
          f <- eqProofInfer p Nothing (Just s)
          case f of
            EqForm (Equality u s') ->
              if s == s'
              then return $ EqForm $ Equality u t
              else throwError $ ProofCheckError p1 $
                   "Terms " ++ printTree s ++ " and " ++ printTree s'
                   ++ " do not match"
            _ -> throwError $ ProofCheckError p $
              printTree f ++ " is not an equality"
        _ -> throwError $ ProofCheckError p1 $
          printTree g ++ " is not an equality"
    (Just l, Just r) -> do
      -- We know q : ? ~ r
      g <- eqProofInfer q Nothing hintR
      case g of
        EqForm (Equality s t) -> do
          -- Now we must have t = r and p : l ~ s
          f <- eqProofInfer p hintL (Just s)
          case f of
            EqForm (Equality u s') ->
              if s == s'
              then return $ EqForm $ Equality u t
              else throwError $ ProofCheckError p1 $
                   "Terms " ++ printTree s ++ " and " ++ printTree s'
                   ++ " do not match"
            _ -> throwError $ ProofCheckError p $
              printTree f ++ " is not an equality"
        _ -> throwError $ ProofCheckError p1 $
          printTree g ++ " is not an equality"
  PrExt identifier proof -> failure p1
  PrFunEq proof term -> failure p1
  PrUnit term -> failure p1
  PrFst p -> do
    hintL' <- stripFst p1 hintL
    hintR' <- stripFst p1 hintR
    f <- eqProofInfer p hintL' hintR'
    case f of
     EqForm (Equality t s) -> EqForm <$> (Equality <$> tFst t <*> tFst s)
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not an equality"
  PrSnd p -> do
    hintL' <- stripSnd p1 hintL
    hintR' <- stripSnd p1 hintR
    f <- eqProofInfer p hintL' hintR'
    case f of
     EqForm (Equality t s) -> EqForm <$> (Equality <$> tSnd t <*> tSnd s)
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not an equality"
  PrPair proof1 proof2 -> failure p1
  PrOut p -> do
    hintL' <- stripOut p1 hintL
    hintR' <- stripOut p1 hintR
    f <- eqProofInfer p hintL' hintR'
    case f of
     EqForm (Equality t s) -> (Later . EqForm) <$> (Equality <$> tOut t <*> tOut s)
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not an equality"
  PrCoind proof -> failure p1
  PrInl p -> do
    a <- case (hintL, hintR) of
      (Nothing, Nothing) -> throwError $ ProofCheckError p1 $
                            "Cannot infer type in proof of lfp constructor"
      (Just l, _) -> return $ getType l
      (Nothing, Just r) -> return $ getType r
    hintL' <- stripInl p1 hintL
    hintR' <- stripInl p1 hintR
    f <- eqProofInfer p hintL' hintR'
    case f of
      EqForm (Equality t s) -> EqForm <$> (Equality <$> tInl a t <*> tInl a s)
      _ -> throwError $ ProofCheckError p1 $
           printTree f ++ " is not an equality"
  PrInr p -> do
    a <- case (hintL, hintR) of
      (Nothing, Nothing) -> throwError $ ProofCheckError p1 $
        "Cannot infer type in proof for lfp constructor"
      (Just l, _) -> return $ getType l
      (Nothing, Just r) -> return $ getType r
    hintL' <- stripInr p1 hintL
    hintR' <- stripInr p1 hintR
    f <- eqProofInfer p hintL' hintR'
    case f of
      EqForm (Equality t s) -> EqForm <$> (Equality <$> tInr a t <*> tInr a s)
      _ -> throwError $ ProofCheckError p1 $
        printTree f ++ " is not an equality"
  PrSumInd identifier1 proof1 identifier2 proof2 identifier3 -> failure p1
  PrIn p -> do
    a <- case (hintL, hintR) of
      (Nothing, Nothing) -> throwError $ ProofCheckError p1 $
        "Cannot infer type in proof of lfp constructor"
      (Just l, _) -> return $ getType l
      (Nothing, Just r) -> return $ getType r
    hintL' <- stripIn p1 hintL
    hintR' <- stripIn p1 hintR
    f <- eqProofInfer p hintL' hintR'
    case f of
      Later (EqForm (Equality t s)) ->
        EqForm <$> (Equality <$> tIn a t <*> tIn a s)
      _ -> throwError $ ProofCheckError p1 $
        printTree f ++ " is not a delayed equality"
  PrLfpInd identifier1 proof identifier2 -> failure p1


proofInfer :: Proof () -> ProofCheckM TFormula
proofInfer p1 = case p1 of
  PrHole -> throwError $ ProofCheckError p1 $ "Cannot infer formula for a hole"
  PrVar x -> do
     u <- askProofEnv >>= return . Map.lookup x
     case u of
       Nothing -> throwError $ ProofCheckError p1 $ "Variable " ++ show x ++ " undefined"
       Just g -> return g
  PrBotElim proof -> failure p1
  PrThmInst thm thmargs -> do
     thms <- gets thms
     case Map.lookup thm thms of
       Nothing -> throwError $ ProofCheckError p1 $
                  "Theorem " ++ show thm ++ " not in scope"
       Just (decls, g) -> instThm p1 decls thmargs g
  PrImplIntro lambda identifier proof -> failure p1
  PrImplElim p q -> do
    f <- proofInfer p
    case f of
     Implies g h -> checkProof q g >> return h
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not an implication"
  PrAndIntro p q -> do
    f <- proofInfer p
    g <- proofInfer q
    return $ And f g
  PrAndElimFst p -> do
    f <- proofInfer p
    case f of
      And g _ -> return g
      _ -> throwError $ ProofCheckError p1 $ printTree f ++ " is not a conjunction"
  PrAndElimSnd p ->  do
    f <- proofInfer p
    case f of
      And _ h -> return h
      _ -> throwError $ ProofCheckError p1 $ printTree f ++ " is not a conjunction"
  PrOrIntroLeft proof -> failure p1
  PrOrIntroRight proof -> failure p1
  PrOrElim proof1 proof2 -> failure p1
  PrNec p -> Later <$> proofInfer p
  PrAppl p q -> do
    f <- proofInfer p
    case f of
     Later (Implies g h) -> checkProof q (Later g) >> return (Later h)
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not a delayed implication"
  PrFP identifier proof -> failure p1
  PrAllIntro identifier proof -> failure p1
  PrAllElim p t -> do
    f <- proofInfer p
    case f of
      Forall x a h -> do
        a' <- resolveTypeHead a
        t' <- typeCheck t a'
        substTerm (Map.singleton x t') h
      _ -> throwError $ ProofCheckError p $
         printTree f ++ " is not a forall formula"
  PrExIntro term proof -> failure p1
  PrExElim identifier proof1 proof2 -> failure p1
  PrRefl _ _ -> eqProofInfer p1 Nothing Nothing
    -- do
    -- -- e <- ask :: ProofCheckM Env
    -- -- issueWarning $ GenericWarning $
    -- --   "Infering formula for " ++ printTree p1 ++ " in context " ++ show e
    -- s' <- typeInfer s
    -- t' <- typeCheck t (getType s')
    -- -- issueWarning $ GenericWarning $
    -- --   "Checking convertibility in " ++ printTree p1
    -- conv <- s' `convertibleTo` t'
    -- when (not conv)
    --   (throwError $ ProofCheckError p1 $
    --    printTree s ++ " not convertible to " ++ printTree t)
    -- return $ EqForm $ Equality s' t'
  PrSym _ -> eqProofInfer p1 Nothing Nothing
  PrTrans _ _ -> eqProofInfer p1 Nothing Nothing
  PrExt _ _ -> eqProofInfer p1 Nothing Nothing
  PrFunEq _ _ -> eqProofInfer p1 Nothing Nothing
  PrUnit _ -> eqProofInfer p1 Nothing Nothing
  PrFst _ -> eqProofInfer p1 Nothing Nothing
  PrSnd _ -> eqProofInfer p1 Nothing Nothing
  PrPair _ _ -> eqProofInfer p1 Nothing Nothing
  PrOut _ -> eqProofInfer p1 Nothing Nothing
  PrCoind _ -> eqProofInfer p1 Nothing Nothing
  PrInl _ -> eqProofInfer p1 Nothing Nothing
  PrInr _ -> eqProofInfer p1 Nothing Nothing
  PrSumInd _ _ _ _ _ -> eqProofInfer p1 Nothing Nothing
  PrIn _ -> eqProofInfer p1 Nothing Nothing
  PrLfpInd _ _ _ -> eqProofInfer p1 Nothing Nothing

checkProof :: Proof () -> TFormula -> ProofCheckM ()
checkProof p1 f = case p1 of
  PrHole -> issueWarning (UnfilledHole f)
  PrVar x -> do
     u <- askProofEnv >>= return . Map.lookup x
     case u of
       Nothing -> throwError $ ProofCheckError p1 $
                  "Variable " ++ show x ++ " undefined"
       Just g -> formulasEqual p1 f g
  PrBotElim proof -> failure p1
  PrThmInst thm thmargs -> do
     thms <- gets thms
     case Map.lookup thm thms of
       Nothing -> throwError $ ProofCheckError p1 $
                  "Theorem " ++ show thm ++ " not in scope"
       Just (decls, g) -> instThm p1 decls thmargs g >>= formulasEqual p1 f
  PrImplIntro _ x p -> case f of
     Implies g h -> do
--       varExists <- isVar identifier
--       maybe (return ()) (\y' -> tell [Shadowing identifier y']) varExists
       localProofEnv (Map.alter (\_ -> Just g) x) $ checkProof p h
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not an implication"
  PrImplElim p q -> do
     g <- proofInfer q
     checkProof p (Implies g f)
  PrAndIntro p q -> case f of
     And g h -> checkProof p g >> checkProof q h
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not a conjunction"
  PrAndElimFst p -> do
    g <- proofInfer p
    case g of
     And f' _ -> formulasEqual p1 f f'
  PrAndElimSnd p -> do
    g <- proofInfer p
    case g of
     And _ f' -> formulasEqual p1 f f'
  PrOrIntroLeft proof -> failure p1
  PrOrIntroRight proof -> failure p1
  PrOrElim proof1 proof2 -> failure p1
  PrNec p -> case f of
     Later f' -> checkProof p f'
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not a delayed formula"
  PrAppl p q -> case f of
     Later f' -> do
       g <- proofInfer q
       case g of
         Later g' -> checkProof p (Later $ Implies g' f')
         _ -> throwError $ ProofCheckError q $
              printTree g ++ " is not a delayed formula"
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not a delayed formula"
  PrFP x p -> localProofEnv (Map.alter (\_ -> Just (Later f)) x) $
              checkProof p f
  PrAllIntro x p -> case f of
    Forall y a g -> do
      when (x /= y) (throwError $ ProofCheckError p1 $
                     "Change of variable names not supported")
      --       varExists <- isVar identifier
      --       maybe (return ()) (\y' -> tell [Shadowing identifier y']) varExists
      local (Map.alter (\_ -> Just a) x) $ checkProof p g
    _ -> throwError $ ProofCheckError p1 $
         printTree f ++ " is not a forall formula"
  PrAllElim p t -> do
    g <- proofInfer p
    case g of
      Forall x a h -> do
        a' <- resolveTypeHead a
        t' <- typeCheck t a'
        h' <- substTerm (Map.singleton x t') h
        formulasEqual p1 f h'
      _ -> throwError $ ProofCheckError p $
         printTree g ++ " is not a forall formula"
  PrExIntro term proof -> failure p1
  PrExElim identifier proof1 proof2 -> failure p1
  -- | FIXME: The comparison of untyped and typed terms is probably inefficient
  PrRefl s t -> case f of
    EqForm (Equality s' t') -> do
      conv <- s' `convertibleTo` t'
      when (not conv)
        (throwError $ ProofCheckError p1 $
         printTree s ++ " not convertible to " ++ printTree t)
      when (s /= (forgetType s'))
        (throwError $ ProofCheckError p1 $
         printTree s ++ " does not match expected " ++ printTree s')
      when (t /= (forgetType t'))
        (throwError $ ProofCheckError p1 $
         printTree t ++ " does not match expected " ++ printTree t')
    _ -> throwError $ ProofCheckError p1 $
         printTree f ++ " is not an equality"
  PrSym p -> case f of
    EqForm (Equality t s) -> checkProof p $ (EqForm $ Equality s t)
    _ -> throwError $ ProofCheckError p1 $
         printTree f ++ " is not an equality"
  PrTrans p q -> case f of
    EqForm (Equality t s) -> do
      g <- eqProofInfer p (Just t) Nothing
      case g of
       EqForm (Equality t' u) ->
         if t == t'
         then checkProof q (EqForm $ Equality u s)
         else throwError $ ProofCheckError p1 $
              "Terms " ++ printTree t ++ " and " ++ printTree t' ++ " do not match"
       _ -> throwError $ ProofCheckError p $
            printTree g ++ " is not an equality"
    _ -> throwError $ ProofCheckError p1 $
         printTree f ++ " is not an equality"
  PrExt identifier proof -> failure p1
  PrFunEq proof term -> failure p1
  PrUnit term -> failure p1
  PrFst p -> case f of
     EqForm (Equality (Fst _ t) (Fst _ s)) ->
       checkProof p (EqForm (Equality t s))
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not of the form (t.fst ~ s.fst)"
  PrSnd p -> case f of
     EqForm (Equality (Fst _ t) (Fst _ s)) ->
       checkProof p (EqForm (Equality t s))
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not of the form (t.snd ~ s.snd)"
  PrPair p q -> case f of
    EqForm (Equality t s) -> do
      t_fst <- tFst t
      t_snd <- tSnd t
      s_fst <- tFst s
      s_snd <- tSnd s
      checkProof p (EqForm $ Equality t_fst s_fst)
      checkProof q (EqForm $ Equality t_snd s_snd)
    _ -> throwError $ ProofCheckError p1 $
         printTree f ++ " is not an equality"
  PrOut p -> case f of
     Later (EqForm (Equality (Out _ t) (Out _ s))) ->
       checkProof p (EqForm (Equality t s))
     _ -> throwError $ ProofCheckError p1 $
          printTree f ++ " is not of the form #(t.out ~ s.out)"
  PrCoind p -> case f of
    EqForm (Equality t s) -> do
      ot <- tOut t
      os <- tOut s
      checkProof p (Later $ EqForm $ Equality ot os)
    _ -> throwError $ ProofCheckError p1 $
         printTree f ++ " is not an equality"
  PrUnitInd p x -> do
    a <- getVar x >>= resolveTypeHead
    case a of
     OneT -> do
       f1 <- substTerm (Map.singleton x (Unit a)) f
       -- h2 <- substTerm (Map.singleton x (Inr a $ Var b2 y2)) f
       -- FIXME: We need to replace x in the assumptions and and remove it!
       checkProof p f1
       -- local (Map.alter (\_ -> Just b2) y2) $ checkProof p2 h2
     _ -> throwError $ ProofCheckError p1 $
          "Cannot refine variable" ++ show x ++ " to <>"
          ++ " because " ++ printTree a ++ " is not the unit type"
  PrInl p -> case f of
    EqForm (Equality u v) ->
      do u' <- reduce u
         v' <- reduce v
         case (u', v') of
           ((Inl _ t), (Inl _ s)) ->
             checkProof p (EqForm $ Equality t s)
           _ -> throwError $ ProofCheckError p1 $
                printTree f ++ " is not an equality between terms of the form (inl t)"
    _ -> throwError $ ProofCheckError p1 $
         printTree f ++ " is not an equality between terms of the form (inl t)"
  PrInr p -> case f of
    EqForm (Equality u v) ->
      do u' <- reduce u
         v' <- reduce v
         case (u', v') of
           ((Inr _ t), (Inr _ s)) ->
             checkProof p (EqForm $ Equality t s)
           _ -> throwError $ ProofCheckError p1 $
                printTree f ++ " is not an equality between terms of the form (inr t)"
    _ -> throwError $ ProofCheckError p1 $
         printTree f ++ " is not an equality between terms of the form (inr t)"
  PrSumInd y1 p1 y2 p2 x -> do
    a <- getVar x >>= resolveTypeHead
    case a of
     PlusT b1 b2 -> do
       h1 <- substTerm (Map.singleton x (Inl a $ Var b1 y1)) f
       h2 <- substTerm (Map.singleton x (Inr a $ Var b2 y2)) f
       -- FIXME: We need to replace x in the assumptions and and remove it!
       local (Map.alter (\_ -> Just b1) y1) $ checkProof p1 h1
       local (Map.alter (\_ -> Just b2) y2) $ checkProof p2 h2
     _ -> throwError $ ProofCheckError p1 $
          "Cannot refine variable" ++ show x ++ " to (inl " ++  show y1 ++ ")"
          ++ " because " ++ printTree a ++ " is not an sum type"
  PrIn p -> case f of
    EqForm (Equality u v) ->
      do u' <- reduce u
         v' <- reduce v
         case (u', v') of
           ((In _ t), (In _ s)) ->
             checkProof p (Later $ EqForm $ Equality t s)
           _ -> throwError $ ProofCheckError p1 $
                printTree f ++ " is not an equality between terms of the form (in t)"
    _ -> throwError $ ProofCheckError p1 $
         printTree f ++ " is not an equality between terms of the form (in t)"
  PrLfpInd y p x -> do
    a <- getVar x >>= resolveTypeHead
    case a of
     LfpT z b -> do
       a_in_b <- subst (Map.singleton z a) b
       h <- substTerm (Map.singleton x (In a $ Var a_in_b y)) f
       -- FIXME: We need to replace x in the assumptions and and remove it!
       local (Map.alter (\_ -> Just a_in_b) y) $ checkProof p h
     _ -> throwError $ ProofCheckError p1 $
          "Cannot refine variable" ++ show x ++ " to (in " ++  show y ++ ")"
          ++ " because " ++ printTree a ++ " is not an lfp type"

checkThmDecl :: ThmDecl -> ProofCheckM ()
checkThmDecl (ThmDecl _ propdecls) = checkPropDecls propdecls

checkThmDecls :: ThmDecls -> ProofCheckM ()
checkThmDecls d = case d of
  NoDeclArgs -> return ()
  DeclArgs thmdecls -> foldM (\_ -> checkThmDecl) () thmdecls

localThmDecls :: ThmDecls -> ProofCheckM a -> ProofCheckM a
localThmDecls d m = case d of
  NoDeclArgs -> m
  DeclArgs thmdecls ->
    localPropEnv
    (\e -> foldl (\e' (ThmDecl p propdecls) -> Map.alter (\_ -> Just propdecls) p e')
           e thmdecls)
    m

safeThmDecl :: Identifier -> ThmDecls -> Formula () -> Proof () -> CheckM ()
safeThmDecl thmName thmdecls f p = do
  f' <- runProofCheckM (
    checkThmDecls thmdecls >>
    localThmDecls thmdecls (
        checkFormula f >>= \f' ->
          checkProof p f' >>
          return f'
        )
    )
    initialProofCheckEnv
  uniqueDecl thms (\e s -> s {thms = e}) thmName (thmdecls, f') "Theorem"

safeDef :: Identifier -> ThmDecls -> Formula () -> CheckM ()
safeDef p thmdecls f = do
  f' <- runProofCheckM
    (checkThmDecls thmdecls >>
     localThmDecls thmdecls (checkFormula f))
    initialProofCheckEnv
  uniqueDecl defs (\e s -> s {defs = e}) p (thmdecls, f') "Definition"
