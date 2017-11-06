type Nat = lfp X . Unit + X ;
type StrN = gfp Y . Nat * Y ;

0 : Nat
  = in (inl <>) ;

suc : Nat -> Nat
    = \n. in (inr n) ;

1 : Nat
  = suc 0 ;


thm later-dist-forall-Nat [P(n : Nat)]
  : #(forall n:Nat.P(n)) -> forall n:Nat. #P(n)
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