type Nat = lfp X . Unit + X ;

-- This should succeed
thm test1 : forall x:Nat. forall y:Nat. x ~ x
    = \\y. \\x. refl y y -- Note the reversed names
;

-- This should fail
thm test2 : forall x:Nat. forall y:Nat. x ~ y
    = \\x. \\y. refl x x
;

-- -- This should fail, too
-- thm test3 : forall x:Nat. forall y:Nat. x ~ y
--     = \\x. \\x. refl x x
-- ;