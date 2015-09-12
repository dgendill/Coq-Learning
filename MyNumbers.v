Require Import Coq.QArith.QArith_base.

Module MyNumbers.

(*Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.*)

Definition add2 (n:nat) : nat :=
match n with
    | O => S(S(O))
    | (S n') => S(S(S n'))
end.

Eval compute in ((add2 O) = 2).


Eval compute in (sqrt 1).


End MyNumbers.