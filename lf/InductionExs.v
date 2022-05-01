From LF Require Import Induction.
From LF Require Import Basics.

(******************************************************************************)

(* Exercise 1 *)

Theorem plus_0_r : forall n : nat,
  n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  (* Since `n` is arbitrary, we must use induction. *)
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl mult. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite -> plus_0_r. reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.
    induction m as [| m' IHm'].
    + simpl. rewrite -> plus_0_r. reflexivity.
    + simpl.
      induction p as [| p' IHp'].
      * repeat rewrite -> plus_0_r. reflexivity.
      * rewrite <- IHn'. reflexivity.
Qed.

(******************************************************************************)

(* Exercise 2 *)

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n,
  double n = n + n.
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

(******************************************************************************)

(* Exercise 3 *)

Theorem double_negb : forall b : bool,
  negb (negb b) = b.
Proof.
  intros n.
  destruct n as [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'.
    rewrite -> double_negb.
    simpl. reflexivity.
Qed.
