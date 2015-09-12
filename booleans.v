Require Import Coq.Init.Datatypes.

Definition isTrue (b:bool) := andb b true.

(*
The assertion we've just made can be
proved by observing that both sides
of the equality evaluate to the same
thing, after some simplification.*)

Example testIsTrue: (
   (isTrue true) = true
). Proof. reflexivity. Qed.

Eval compute in (isTrue true).
Eval compute in (isTrue false).
Eval compute in (isTrue (negb false)).

Definition nandb (b1:bool) (b2:bool) : bool :=
    match (andb b1 b2) with
    | true => false
    | false => true
    end.

Example nanddb_tt: (
nandb true true = false
). Proof. reflexivity. Qed.
Example nanddb_ff: (
nandb false false = true
). Proof. reflexivity. Qed.
Example nanddb_ft: (
nandb false true = true
). Proof. reflexivity. Qed.
Example nanddb_tf: (
nandb true false = true
). Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
andb (andb b1 b2) b3.

Example andb3_ttt: (andb3 true true true) = true.
Proof. reflexivity. Qed.
