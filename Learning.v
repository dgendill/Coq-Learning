Require Import Coq.Setoids.Setoid.
Require Import Coq.Bool.Bool.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
intros n.
reflexivity. Qed.

(* intro, simpl, reflexivity are tactics.  Tells
coq how it should test the correctness of the claim.
Tactics go between Proof. and Qed. *)

Theorem plus_n_0 : forall n : nat, n + 0 = n.
Proof.
intros n.
auto.
Qed.



(* "On the left" _l *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) -> 
  forall (b : bool), f (f b) = b.
Proof.
intros f.
intros H.
intros b.
rewrite H.
rewrite H.
reflexivity.

(* negb = negative boolean *)

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) -> 
  forall (b : bool), f (f b) = b.
Proof.
intros.
rewrite H.
rewrite H.
destruct b.
simpl. reflexivity.
simpl. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (b = c) -> (andb b c = orb b c).
Proof.
intros.
inversion H.
destruct c.
simpl. reflexivity.
simpl. reflexivity.
Qed.

inversion H.
reflexivity.

(*
Theorem dom_t :
  forall (b c : bool),
  (b <> c) -> (orb b c = false).
Proof.
intros.
destruct b.
rewrite H.*)

Theorem andb_eq_orb :
  forall (b c : bool),
  (b = c) -> (andb b c = orb b c).
Proof.
intros.
simpl.
rewrite H.
destruct c.
reflexivity.
reflexivity.
Qed.

Theorem andb_eq_orb_rev :
  forall (b c : bool),
  (andb b c = orb b c) -> (b = c).
Proof.
intros b c.
induction c.
rewrite andb_true_r.
rewrite orb_true_r.
induction b. auto.
intro.
rewrite H.
reflexivity.
rewrite andb_false_r.
rewrite orb_false_r.
induction b; auto.

Theorem andb_eq_orb_2 :
  forall (b c : bool),
  (andb b c = orb b c) -> (b = c).
Proof.
intros b c.
induction c.
destruct b.
reflexivity.
simpl.
intro.
rewrite H.
reflexivity.
destruct b. simpl.



reflexivity.
intro.
auto.
intro.
auto.
rewrite andb_false_r.

destruct b.
reflexivity.
simpl.
intro.
reflexivity.
simpl.
reflexivity.*)

(*intros b c.
induction c.
destruct b.
reflexivity.
reflexivity.
simpl.
reflexivity.*)


rewrite H.
destruct c.
reflexivity.
reflexivity.



simpl. intros.
induction c.




destruct b as [b|c].

(*
The annotation "as [| n']" is called an
intro pattern. It tells Coq what variable
names to introduce in each subgoal. *)

(* left of -> arrow is the the hypothesis.
   arrow is read "implies"  intros H moves
   hypothesis into context.

destruct generates two subgoals *)

