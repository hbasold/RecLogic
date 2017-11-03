type Nat = lfp X . Unit + X ;
type StrN = gfp Y . Nat * Y ;

0 : Nat
  = in (inl <>) ;

pre-suc : Nat -> Unit + Nat
    = \n. inr n ;

suc : Nat -> Nat
    = \n. in (inr n) ;

1 : Nat
  = suc 0 ;

plus-aux : Unit + (Nat -> Nat) -> (Nat -> Nat)
         = \x. \m. {inl _ -> m ; inr f -> suc (f m)} x ;

plus : Nat -> Nat -> Nat
     = \n. \m. rec plus-aux n m ;

hd : StrN -> Nat
   = \s. (s.out).fst ;

tl : StrN -> StrN
   = \s. (s.out).snd ;

inj : Nat -> StrN
    = \n. corec (\x. <n, x>) <> ;

splus-aux : StrN * StrN -> Nat * (StrN * StrN)
          = \x. <plus (hd (x.fst)) (hd (x.snd)), <tl (x.fst), tl (x.snd)>> ;

splus : StrN -> StrN -> StrN
      = \s. \t. corec splus-aux <s, t> ;

thm andI [P,Q] : P -> Q -> P & Q =
  \p. \q. <p & q>
;

thm prod-coind : forall x:Nat*StrN. forall y:Nat*StrN.
                 (x.fst ~ y.fst) & (x.snd ~ y.snd) -> x ~ y =
  \\x. \\y. \p. <p.&fst, p.&snd>
;

thm later-distr-conj [P,Q] : #P & #Q -> #(P & Q) =
  \lplq. (nec (inst andI [P,Q]))
         <*> (lplq.&fst)
         <*> (lplq.&snd)
;

thm later-dist-forall-Nat [P(x : Nat)]
  : #(forall x:Nat.P(x)) -> forall y:Nat. #P(y)
  = \p. \\y. (nec (\q. q @ y)) <*> p
;

thm later-dist-forall-StrN [P(x : StrN)]
  : #(forall x:StrN.P(x)) -> forall y:StrN. #P(y)
  = \p. \\y. (nec (\q. q @ y)) <*> p
;

thm later-distr-pair : forall x:Nat*StrN. forall y:Nat*StrN.
                       #(x.fst ~ y.fst) & #(x.snd ~ y.snd) -> #(x ~ y) =
  \\x. \\y. \p. (nec ((inst prod-coind) @ x @ y))
                <*> ((inst later-distr-conj [x.fst ~ y.fst, x.snd ~ y.snd]) p)
;

thm later-trans-Nat : forall x:Nat. forall y:Nat. forall z:Nat.
                  #(x ~ y) -> #(y ~ z) -> #(x ~ z)
  = \\x. \\y. \\z. \p. \q. (nec (\r. \s. trans r s)) <*> p <*> q
;

thm later-fst : forall x:Nat*StrN. forall y:Nat*StrN. #(x ~ y) -> #(x.fst ~ y.fst)
    = \\x. \\y. \p. (nec (\q. q.fst)) <*> p
;

thm cong-hd : forall s:StrN. forall t:StrN.
              s ~ t -> #(Eq hd s ~ hd t)
    = \\s. \\t. \p.
      ((inst later-trans-Nat) @ (hd s) @ (t.out.fst) @ (hd t))
             (((inst later-trans-Nat) @ (hd s) @ (s.out.fst) @ (t.out.fst))
                     (nec (refl (hd s) (s.out.fst)))
                     (((inst later-fst) @ (s.out) @ (t.out)) (p.out)))
             (nec (refl (t.out.fst) (hd t)))
;

thm conv-hd : forall s:StrN. forall t:StrN.
              (hd s ~ hd t) -> (s.out.fst ~ t.out.fst) =
  \\s. \\t. \p. trans (trans (refl (s.out.fst) (hd s)) p)
                      (refl (hd t) (t.out.fst))
;

thm conv-tl : forall s:StrN. forall t:StrN.
              (tl s ~ tl t) -> (s.out.snd ~ t.out.snd) =
  \\s. \\t. \p. trans (trans (refl (s.out.snd) (tl s)) p)
                      (refl (tl t) (t.out.snd))
;

thm str-coind : forall s:StrN. forall t:StrN.
                #(hd s ~ hd t) -> #(tl s ~ tl t) -> s ~ t =
  \\s. \\t. \p. \q. coind (((inst later-distr-pair) @ (s.out) @ (t.out))
                                  < (nec ((inst conv-hd) @ s @ t)) <*> p
                                  & (nec ((inst conv-tl) @ s @ t)) <*> q>)
;

-- Proved in StreamPlusComm.cp
thm splus-comm : forall s:StrN. forall t:StrN. splus s t ~ splus t s = ?? ;

nat1-coalg : Nat -> Nat * Nat
           = \n. <n , suc n> ;

nat1-aux : Nat -> StrN
         = \n. corec nat1-coalg n ;

nat1 : StrN
     = nat1-aux 0 ;

nat2-coalg : StrN -> Nat * StrN
           = \s. <hd s, splus s (inj 1)> ;

nat2-aux : StrN -> StrN
         = \s. corec nat2-coalg s ;

nat2 : StrN
     = nat2-aux (inj 0) ;

thm nat-aux-hd : forall n:Nat. Eq hd (nat1-aux n) ~ hd (nat2-aux (inj n)) =
  \\n. refl (hd (nat1-aux n)) (hd (nat2-aux (inj n)))
;

thm nat1-aux-tl-lem : forall n:Nat. Eq tl (nat1-aux n) ~ nat1-aux (suc n)
    = \\n. refl (tl (nat1-aux n)) (nat1-aux (suc n))
;

thm later-trans-Str : forall x:StrN. forall y:StrN. forall z:StrN.
                  #(x ~ y) -> #(y ~ z) -> #(x ~ z)
  = \\x. \\y. \\z. \p. \q. (nec (\r. \s. trans r s)) <*> p <*> q
;

thm splus-suc-lem1 : forall n:Nat. Eq splus (inj 1) (inj n) ~ inj (suc n)
    = \\n. fix p.
      ((inst str-coind) @ (splus (inj 1) (inj n)) @ (inj (suc n)))
       (nec (refl (hd (splus (inj 1) (inj n))) (hd (inj (suc n)))))
       (((inst later-trans-Str) @ (tl (splus (inj 1) (inj n))) @ (splus (inj 1) (inj n)) @ (tl (inj (suc n))))
          (nec (refl (tl (splus (inj 1) (inj n))) (splus (inj 1) (inj n))))
          (((inst later-trans-Str) @ (splus (inj 1) (inj n)) @ (tl (inj (suc n))) @ (inj (suc n)))
                  p
                  (nec (refl (tl (inj (suc n))) (inj (suc n))))
          )
       )
;


thm splus-suc-lem : forall n:Nat. Eq splus (inj n) (inj 1) ~ inj (suc n)
    = \\n. trans ((inst splus-comm) @ (inj n) @ (inj 1))
                 ((inst splus-suc-lem1) @ n)
;

thm nat2-cong-hd : forall s:StrN. forall t:StrN.
                   s ~ t -> # (Eq hd (nat2-aux s) ~ hd (nat2-aux t))
    = \\s. \\t. \p. ((inst later-trans-Nat) @ (hd (nat2-aux s)) @ (hd s) @ (hd (nat2-aux t)))
                           (nec (refl (hd (nat2-aux s)) (hd s)))
                           (((inst later-trans-Nat) @ (hd s) @ (hd t) @ (hd (nat2-aux t)))
                                   (((inst cong-hd) @ s @ t) p)
                                   (nec (refl (hd t) (hd (nat2-aux t)))))
;

thm nat2-cong-tl :
    #(forall s:StrN. forall t:StrN. s ~ t -> nat2-aux s ~ nat2-aux t) ->
    forall s:StrN. forall t:StrN. s ~ t -> # (Eq tl (nat2-aux s) ~ tl (nat2-aux t))
    = \p. \\s. \\t. \q. ??
;

thm nat2-cong : forall s:StrN. forall t:StrN. s ~ t -> nat2-aux s ~ nat2-aux t
    = fix p. \\s. \\t. \q.
      ((inst str-coind) @ (nat2-aux s) @ (nat2-aux t))
      (((inst nat2-cong-hd) @ s @ t) q)
      (((inst nat2-cong-tl) p @ s @ t) q)
;

thm nat2-aux-tl-lem : forall n:Nat. Eq tl (nat2-aux (inj n)) ~ nat2-aux (inj (suc n))
    = \\n. trans (refl (tl (nat2-aux (inj n))) (nat2-aux (splus (inj n) (inj 1))))
                 (((inst nat2-cong) @ (splus (inj n) (inj 1)) @ (inj (suc n)))
                         ((inst splus-suc-lem) @ n))
;

thm nat-aux-tl : #(forall n:Nat. nat1-aux n ~ nat2-aux (inj n)) ->
                 forall n:Nat. #(Eq tl (nat1-aux n) ~ tl (nat2-aux (inj n))) =
  \p. \\n. ??
;

thm nat-aux-equiv : forall n:Nat. nat1-aux n ~ nat2-aux (inj n) =
  fix p. \\n. ((inst str-coind) @ (nat1-aux n) @ (nat2-aux (inj n)))
              (nec ((inst nat-aux-hd) @ n))
              ((inst nat-aux-tl) p @ n)
;

thm nat1-nat2-equiv : nat1 ~ nat2 =
  trans (trans (refl nat1 (nat1-aux 0))
               ((inst nat-aux-equiv) @ 0))
        (refl (nat2-aux (inj 2)) nat2)
;