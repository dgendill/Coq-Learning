Require Import Coq.QArith.QArith_base.
Require Import Coq.Numbers.NatInt.NZSqrt.
Require Import NZAxioms NZMulOrder.
Require Import Coq.Numbers.Natural.Abstract.NSqrt.

Require Import Coq.ZArith.BinInt.

Local Open Scope Z_scope.

(*
Reals cannot be computed
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Rfunctions.
Require Import Rbase.
*)


(* point is the constructor *)
(* Point is the type *)
(* There is one way to construct a Point - by using
the point constructor *)

Inductive Point : Type :=
  point : nat -> nat -> Point.

(*Eval compute in (pair 3 5).
Check (pair 3 5).*)

Notation "( x , y )" := (pair x y).

(* coq pair already exists *)


Inductive Line : Type :=
  line : Point -> Point -> Line.

Definition line_fst (l:Line) :=
  match l with
  | line x y => x
  end.

Definition line_snd (l:Line) :=
  match l with
  | line x y => y
  end.

Definition point_fst (p:Point) :=
  match p with
  | point x y => x
  end.

Definition point_snd (p:Point) :=
  match p with
  | point x y => y
  end.

(* The reference sqrt was not found in the current environment. *)

Definition line_length (l:Line) :=
  sqrt(
        (minus (point_snd(line_fst l)) (point_fst(line_fst l)))^2 
+
        (minus (point_snd(line_snd l)) (point_fst(line_snd l)))^2
  ).

Example line_example : (
line_length (line (point 1 1) (point 2 2)) = 2
).

Eval compute in line_length (line (point 0 0 ) (point 1 123)).
Check line_length (line (point 1 1) (point 2 2)).


Theorem line_length :
  forall (a b : Point),
  forall (c : Line),
  



Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday ⇒ tuesday
  | tuesday ⇒ wednesday
  | wednesday ⇒ thursday
  | thursday ⇒ friday
  | friday ⇒ monday
  | saturday ⇒ monday
  | sunday ⇒ monday
  end.