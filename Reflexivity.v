Require Import Coq.Setoids.Setoid.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof. intros. auto. Qed.

Theorem plus_id_example : forall n m:nat,
n = m ->
n + n = m + m.

Proof.
intros n m.
intros H.
rewrite -> H.
reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
intros n m o.
intros H1 H2.
rewrite -> H1.
rewrite -> H2.
reflexivity.
Qed.

Print plus_id_exercise.

(* induction *)

Theorem test1 : ~ 1 = 2.
Proof.
unfold not.
intro H. (* Assume 1 = 2.  Assume the hypothesis *)
inversion H. (* Switch the sides and see if they match *)
Qed.

Print True.
Print False.
Print no.