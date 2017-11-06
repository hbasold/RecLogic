---------- Preliminaries ---------------
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

hd : StrN -> Nat
   = \s. (s.out).fst ;

tl : StrN -> StrN
   = \s. (s.out).snd ;

thm later-dist-forall-Nat [P(n : Nat)]
  : #(forall n:Nat. P(n)) -> forall n:Nat. #P(n)
  = \p. \\n. (nec (\q. q @ n)) <*> p
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

thm andI [P,Q] : P -> Q -> P & Q =
  \p. \q. <p & q>
;

thm later-distr-conj [P,Q] : #P & #Q -> #(P & Q) =
  \lplq. (nec (inst andI [P,Q]))
         <*> (lplq.&fst)
         <*> (lplq.&snd)
;

thm prod-coind : forall x:Nat*StrN. forall y:Nat*StrN.
                 (x.fst ~ y.fst) & (x.snd ~ y.snd) -> x ~ y =
  \\x. \\y. \p. <p.&fst, p.&snd>
;

thm later-distr-pair : forall x:Nat*StrN. forall y:Nat*StrN.
                       #(x.fst ~ y.fst) & #(x.snd ~ y.snd) -> #(x ~ y) =
  \\x. \\y. \p. (nec ((inst prod-coind) @ x @ y))
                <*> ((inst later-distr-conj [x.fst ~ y.fst, x.snd ~ y.snd]) p)
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

--------------- Actual Content -------------

d-aux : Unit + (StrN -> StrN) -> (StrN -> StrN)
      = \x. \s. {inl _ -> s ; inr f -> tl (f s)} x ;

d : Nat -> StrN -> StrN
  = \n. \s. rec d-aux n s ;

-- Not provable with currently encodable induction
thm tl-d : forall n:Nat. forall s:StrN. Eq tl (d n s) ~ d n (tl s) =
  \\n. \\s. ((inst Nat-ind [forall s:StrN. Eq tl (d n s) ~ d n (tl s)])
         (\\t. refl (tl (d 0 t)) (d 0 (tl t)))
         (\\m. \p. \\t. ??)) @ n @ s
;