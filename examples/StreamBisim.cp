type Nat = lfp X . Unit + X ;
type StrN = gfp Y . Nat * Y ;

hd : StrN -> Nat
   = \s. (s.out).fst ;

tl : StrN -> StrN
   = \s. (s.out).snd ;

def IsBism [P(x : StrN, y : StrN)] =
  forall u : StrN. forall v : StrN.
  P(u,v) -> (hd u ~ hd v) & P(tl u, tl v) ;