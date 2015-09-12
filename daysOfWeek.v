Inductive day : Set :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday tuesday).
Eval simpl in (next_weekday saturday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.


(* One is the successor to 0*)
(* Definition one := (S 0) *)

(*
Definition one : nat := (S 0)
Definition two : nat := (S one)

gt one two

Definition double (m:nat) := plus m m

eq (double 1) (plus 1 1) *)

