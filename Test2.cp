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

thm curry [P,Q,R] : (P & Q -> R) -> (P -> Q -> R) =
  \f. \p. \q. f <p & q>
;

thm uncurry [P,Q,R] : (P -> Q -> R) -> (P & Q -> R) =
  \i. \pq. i (pq.&fst) (pq.&snd)
;

thm later-mono [P,Q] : (P -> Q) -> #P -> #Q =
  \i. \lp. (nec i) <*> lp
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

thm trans2-Nat : forall x:Nat. forall x1:Nat. forall y:Nat. forall y1:Nat.
                 x ~ x1 -> y ~ y1 -> x1 ~ y1 -> x ~ y =
  \\x. \\x1. \\y. \\y1. \p. \q. \r. trans p (trans q (sym r))
;

thm later-trans-Nat : forall x:Nat. forall y:Nat. forall z:Nat.
                  #(x ~ y) -> #(y ~ z) -> #(x ~ z)
  = \\x. \\y. \\z. \p. \q. (nec (\r. \s. trans r s)) <*> p <*> q
;

thm Nat-ind [P(n : Nat)]
    : P(0)
      -> (forall n:Nat. #P(n) -> P(suc n))
      -> forall n:Nat. P(n)
    = \b. \s. fix p. \\n.
      {in x ->
      { inl u -> { <> -> b } u
      ; inr m -> (s @ m) (((inst later-dist-forall-Nat [P(n)]) p) @ m)
      } x
      } n
;

-- thm Nat-ind [P(n : Nat)]
--     : P(0) -> (forall n:Nat. P(n) -> P(suc n)) -> forall n:Nat. P(n)
--     = ??
-- ;

thm plus-0-neutral-l : forall n:Nat. plus 0 n ~ n =
  \\n. refl (plus 0 n) n
;

thm plus-suc-distr-l
    : forall n:Nat. forall m:Nat. Eq plus (suc n) m ~ suc (plus n m)
    = \\n. \\m. refl (plus (suc n) m) (suc (plus n m))
;

thm inr-cong : forall n:Nat. forall m:Nat. n ~ m -> pre-suc n ~ pre-suc m =
  \\n. \\m. \p. inr p
;

thm suc-cong : forall n:Nat. forall m:Nat. #(n ~ m) -> suc n ~ suc m =
  \\n. \\m. \p. in ((nec ((inst inr-cong) @ n @ m)) <*> p)
;

thm plus-0-neutral-r : forall n:Nat. plus n 0 ~ n =
  \\n. (inst Nat-ind [plus n 0 ~ n])
       ((inst plus-0-neutral-l) @ 0)
              (\\n. \p. trans ((inst plus-suc-distr-l) @ n @ 0)
                                     (((inst suc-cong) @ (plus n 0) @ n) p)
              )
       @ n
;

thm plus-suc-distr-r
    : forall n:Nat. forall m:Nat. Eq plus n (suc m) ~ suc (plus n m)
    = \\n. \\m. (inst Nat-ind [plus n (suc m) ~ suc (plus n m)])
                (refl (plus 0 (suc m)) (suc (plus 0 m)))
                (\\n. \p.
                  ((inst trans2-Nat)
                         @ (plus (suc n) (suc m)) @ (suc (plus n (suc m)))
                         @ (suc (plus (suc n) m)) @ (suc (suc (plus n m))))
                         (refl (plus (suc n) (suc m)) (suc (plus n (suc m))))
                         (refl (suc (plus (suc n) m)) (suc (suc (plus n m))))
                         (((inst suc-cong) @ (plus n (suc m)) @ (suc (plus n m))) p)
                )
                @ n
;

thm plus-comm-IS : forall m:Nat.
    forall n:Nat. #(plus n m ~ plus m n) -> Eq plus (suc n) m ~ plus m (suc n) =
  \\m. \\n. \p.
    trans (refl (plus (suc n) m) (suc (plus n m)))
          (trans (((inst suc-cong) @ (plus n m) @ (plus m n)) p)
                 (sym ((inst plus-suc-distr-r) @ m @ n)))
;

thm plus-comm : forall n:Nat. forall m:Nat. plus n m ~ plus m n =
  \\n. \\m. (inst Nat-ind [plus n m ~ plus m n])
                  (trans ((inst plus-0-neutral-l) @ m)
                         (sym ((inst plus-0-neutral-r) @ m)))
                  ((inst plus-comm-IS) @ m)
                  @ n
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

thm splus-comm-lem1 : #(forall s:StrN. forall t:StrN. splus s t ~ splus t s) ->
                      forall s:StrN. forall t:StrN. #(splus s t ~ splus t s) =
  \p. \\s. \\t.
      ((inst later-dist-forall-StrN [splus s x ~ splus x s])
      ((inst later-dist-forall-StrN [forall t:StrN. splus x t ~ splus t x]) p
             @ s)) @ t
;

thm splus-hd : forall s:StrN. forall t:StrN.
               Eq hd (splus s t) ~ plus (hd s) (hd t)
  = \\s. \\t. refl (hd (splus s t)) (plus (hd s) (hd t))
;

thm splus-tl : forall s:StrN. forall t:StrN.
               Eq tl (splus s t) ~ splus (tl s) (tl t)
  = \\s. \\t. refl (tl (splus s t)) (splus (tl s) (tl t))
;

thm later-trans-StrN : forall x:StrN. forall y:StrN. forall z:StrN.
                  #(x ~ y) -> #(y ~ z) -> #(x ~ z)
  = \\x. \\y. \\z. \p. \q. (nec (\r. \s. trans r s)) <*> p <*> q
;

thm splus-comm : forall s:StrN. forall t:StrN. splus s t ~ splus t s =
  fix p. \\s. \\t. ((inst str-coind) @ (splus s t) @ (splus t s))
                   (nec (trans (trans ((inst splus-hd) @ s @ t)
                                      ((inst plus-comm) @ (hd s) @ (hd t)))
                               (sym ((inst splus-hd) @ t @ s))))
                   ((((inst later-trans-StrN)
                            @ (tl (splus s t)) @ (splus (tl t)(tl s))) @ (tl (splus t s)))
                            (((inst later-trans-StrN)
                                    @ (tl (splus s t)) @ (splus (tl s)(tl t)) @ (splus (tl t)(tl s)))
                                    ((nec (inst splus-tl) @ s @ t))
                                    ((inst splus-comm-lem1) p @ (tl s) @ (tl t)))
                            (nec (sym ((inst splus-tl) @ t @ s))))
;

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



-- thm inj-hom : / / |- forall n : Nat. splus (inj n) (inj 1) ~ (inj (plus n 1)) by {
--   ??
-- };

def IsBism [P(x : StrN, y : StrN)] =
  forall u : StrN. forall v : StrN.
  P(u,v) -> (hd u ~ hd v) & P(tl u, tl v) ;