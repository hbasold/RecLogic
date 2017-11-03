--------------------------------------------------------------------------
------ Trees
--------------------------------------------------------------------------

type Nat = lfp X . Unit + X ;
-- Non-empty, finitely branching, Nat-labelled, potentially infinite trees
type Tr = gfp X . lfp Y . Nat * (Unit + X * Y) ;
-- Branching-type of Tr
type Br = lfp Y . Nat * (Unit + Tr * Y) ;

root-aux : Nat * (Unit + Tr * Nat) -> Nat
         = \x. x.fst ;

root : Tr -> Nat
     = \x. rec root-aux (x.out) ;

-- Non-empty, finitely branching, Nat-labelled, potentially infinite trees
type Tr2 = gfp X . lfp Y . Unit + (Nat * X * Y) ;
-- Branching-type of Tr
type Br2 = lfp Y . Unit + (Nat * Tr2 * Y) ;

root2-aux : Unit + (Nat * Tr2 * (Unit + Nat)) -> Unit + Nat
         = \x. {inl x -> inl x ; inr x -> inr (x.fst.fst)} x ;

root2 : Tr2 -> Unit + Nat
     = \x. rec root2-aux (x.out) ;
