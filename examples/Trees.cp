--------------------------------------------------------------------------
------ Trees
--------------------------------------------------------------------------

type Nat = lfp X . Unit + X ;
-- Non-empty, finitely branching, Nat-labelled, potentially infinite trees
type Tr = gfp X . Nat * (lfp Y . (Unit + X * Y)) ;
-- Branching-type of Tr
type Br = (lfp Y . (Unit + Tr * Y)) ;

root : Tr -> Nat
     = \x. x.out.fst ;

-- Non-empty, finitely branching, Nat-labelled, potentially infinite trees
type Tr2 = gfp X . lfp Y . Unit + (Nat * X * Y) ;
-- Branching-type of Tr
type Br2 = lfp Y . Unit + (Nat * Tr2 * Y) ;

root2-aux : Unit + (Nat * Tr2 * (Unit + Nat)) -> Unit + Nat
         = \x. {inl x -> inl x ; inr x -> inr (x.fst.fst)} x ;

root2 : Tr2 -> Unit + Nat
     = \x. rec root2-aux (x.out) ;
