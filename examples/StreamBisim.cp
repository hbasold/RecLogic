def IsBism [P(x : StrN, y : StrN)] =
  forall u : StrN. forall v : StrN.
  P(u,v) -> (hd u ~ hd v) & P(tl u, tl v) ;