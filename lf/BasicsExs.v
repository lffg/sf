From LF Require Import Basics.

(******************************************************************************)

(* Exercise 1 *)

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(******************************************************************************)

(* Exercise 2 *)

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  andb b1 (andb b2 b3).

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(******************************************************************************)

(* Exercise 3 *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: factorial 3 = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: factorial 5 = mult 10 12.
Proof. simpl. reflexivity. Qed.

(******************************************************************************)

(* Exercise 4 *)

(* Checks if the first argument is less than the second. *)
Definition ltb (m n : nat) : bool :=
  if eqb m n
    then false
    else leb m n.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(******************************************************************************)

(* Exercise 5 *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite <- H2.
  rewrite -> H1.
  reflexivity.
Qed.

Check plus_id_exercise.

(******************************************************************************)

(* Exercise 6 *)

(* Provided by the standard library: *)
Check mult_n_O:
  forall n : nat, 0 = n * 0.
Check mult_n_Sm:
  forall n m : nat, n * m + n = n * S m.

(* Use those two lemmas about multiplication that we just checked to prove the
  * following theorem. Hint: recall that 1 is S O. *)
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

(******************************************************************************)

(* Exercise 7 *)

(* Prove the following claim, marking cases (and subcases) with bullets when
 * you use destruct. Hint: delay introducing the hypothesis until after you
 * have an opportunity to simplify it. *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct c eqn:EqnC.
  - reflexivity.
  - intros H. rewrite <- H. destruct b eqn:EqnB.
    + reflexivity.
    + reflexivity.
Qed.

(******************************************************************************)

(* Exercise 8 *)

Theorem zero_nbeq_plus_1 : forall n : nat,
  eqb 0 (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

(******************************************************************************)

(* Exercise 9 *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool),
  f (f b) = b.
Proof.
  intros hyp1 hyp2 b.
  rewrite -> hyp2. rewrite -> hyp2.
  reflexivity.
Qed.

(******************************************************************************)

(* Exercise 10 *)

Definition manual_grade_for_negation_fn_applied_twice :
  option (nat * string) := None.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool),
  f (f b) = b.
Proof.
  intros hyp1 hyp2 b.
  rewrite -> hyp2. rewrite -> hyp2.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(******************************************************************************)

(* Exercise 11 *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  - simpl. intros hyp. rewrite <- hyp. reflexivity.
  - simpl. intros hyp. rewrite <- hyp. reflexivity.
Qed.

(******************************************************************************)

(* Exercise 12 *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint decr (m : bin) : bin :=
  match m with
  | Z => Z
  | B0 m' => B1 (decr m')
  | B1 Z => Z
  | B1 m' => B0 m'
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => 0
  | B1 Z => 1
  | B0 m' => 2 * (bin_to_nat m')
  | B1 m' => 1 + 2 * (bin_to_nat m')
  end.

Example test_bin_decr1 : (decr Z) = Z.
Proof. simpl. reflexivity. Qed.
Example test_bin_decr2 : (decr (B1 Z)) = Z.
Proof. simpl. reflexivity. Qed.
Example test_bin_decr3 : (decr (B0 (B1 Z))) = B1 Z.
Proof. simpl. reflexivity. Qed.
Example test_bin_decr4 : (decr (B1 (B1 Z))) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_decr5 : (decr (B0 (B0 (B1 Z)))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl incr. simpl bin_to_nat. simpl. reflexivity. Qed.