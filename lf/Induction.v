From LF Require Export Basics.

(*
 * PROOF BY INDUCTION
 *)

(* One may trivially prove that `0` is the neutral addition element when it is
 * on the left of `+`.
 *)

 Theorem add_0_r' : forall n : nat, 0 + n = n.
 Proof. reflexivity. Qed.
 
 (* But that wouldn't work when the `0` is on the right.
  *)
 
 Theorem add_0_r'' : forall n : nat, n + 0 = n.
 Proof. intros n. simpl. (* simpl does nothing. *) Abort.
 
 Theorem add_0_r''' : forall n : nat, n + 0 = n.
 Proof.
     destruct n as [| n'] eqn:E.
     - reflexivity. (* In the 0 case, ok. Simplification is trivial. *)
     - simpl. (* `S n'` has `n' : nat`, which is arbitrary; can't simplify. *)
 Abort.
 
 (* To understand why, let's recall the definition of `add`.
  *)
 
 Fixpoint my_add' (m n : nat) : nat :=
     match m with
     | O => n
     | S m' => S (my_add' m' n)
     end.
 
 (* Notice the first argument, `m` is being used in a match expression.
  * Thus, since `n` in `n + 0` is an arbitrary unknown number, it can't be
  * further simplified using `simpl`. Using `destruct` would also not work since
  * the `n'` in `S n'` may be also arbitrary. How many times `destruct` must be
  * called? We don't know.
  *)
 
 (* Thus, the simple techniques we've learned so far aren't enough to prove
  * arbitrary definitions, such as numbers, list and other inductively defined
  * sets. Induction must also be used to prove it.
  *
  * If `P(n)` is some proposition involving a natural number `n`, one may use
  * induction to prove such proposition for all natural numbers if:
  *
  *     - Show that `P(0)` holds.
  *     - If, for any `n'` in `P(n')` holds, then so does `P(S n')`.
  *     - Hence `P(n)` holds for all `n`.
  *
  * In Coq, such induction principles are almost the same.
  *
  * One begin with the goal of proving some `P(n)` for all `n` and break it down
  * into two separate sub goals; the first, which proves `P(0)`; and the second,
  * which shows `P(n') -> P(S n')`. The `induction` tactic is used.
  *)
 
 Theorem add_0_r : forall n : nat,
     n + 0 = n.
 Proof.
     intros n.
     induction n as [| n' IHn'].
     - reflexivity.
     - simpl plus. rewrite -> IHn'. reflexivity.
 Qed.
 
 (* The `induction` tactic replaces the variable with its type's constructors.
  * In the first sub goal, `n` is replaced with `0`.
  * In the second sub goal, `n` is replaced by `S n'` and the assumption
  * `n' + 0 = n'` is added to the context as `IHn'`, which stands for induction
  * hypothesis for `n'`.
  *)

Theorem plus_0_r : forall n : nat,
  n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Exercise 1 *)

Theorem mul_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  (* Since `n` is arbitrary, we must use induction. *)
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
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
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

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

(* Exercise 3 *)

Theorem double_negb : forall b : bool,
  negb (negb b) = b.
Proof.
  intros [].
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
