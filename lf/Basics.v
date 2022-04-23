(*
 * DATA AND FUNCTIONS
 *)

(* Introduce a new type. *)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Define a function. *)
Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(* `Compute` evaluates the expression and prints the result. *)
Compute (next_weekday friday).
Compute (next_weekday monday).

(* Makes an assertion and gives it a name. *)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(* Verify the last assertion.
 *
 * Notice that `Example` does not verify if the assertion is valid, it only
 * names it. To verify it, one must use `Proof`.
 *)
Proof. simpl. reflexivity. Qed.

(******************************************************************************)

From Coq Require Export String.

(*
 * BOOLEANS
 *)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Example test_negb1: (negb true) = false.
Proof. simpl. reflexivity. Qed.
Example test_negb2: (negb false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Example test_andb1: (andb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb2: (andb true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb3: (andb false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb4: (andb false false) = false.
Proof. simpl. reflexivity. Qed.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "a && b" := (andb a b).
Notation "a || b" := (orb a b).

Example test_andb_notation: true && false = false.
Proof. simpl. reflexivity. Qed.

Example test_orb_notation: false || true = true.
Proof. simpl. reflexivity. Qed.

(******************************************************************************)

(*
 * TYPES
 *)

(* `Check` prints the given expression's type. *)
Check true.

(* `Check` may also be used to check the type. *)
Check andb: bool -> bool -> bool.
Check negb: bool -> bool.
Check (negb true) : bool.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  (* Constructors may take arguments. Here we say the `color` constructor
   * `primary` takes an argument of type `rgb`.
   *)
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary _ => false
  end.

(******************************************************************************)

(*
 * MODULES
 *)

Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b :bool := true.

Check Playground.b : rgb.
Check b : bool.

(******************************************************************************)

(*
 * TUPLES
 *)

Module TuplePlayground.

  Inductive bit : Type :=
    | B0
    | B1.

  (* One may declare a tuple-like structure by using an inductively-defined type
   * with only one variant.
   *)
  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).

  Check (bits B1 B0 B1 B0) : nybble.

  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.

  Example test_all_zero1: all_zero (bits B1 B0 B1 B0) = false.
  Proof. simpl. reflexivity. Qed.
  Example test_all_zero2: all_zero (bits B0 B0 B0 B0) = true.
  Proof. simpl. reflexivity. Qed.

End TuplePlayground.

(******************************************************************************)

(*
 * NUMBERS
 *)

Module NatPlayground1.

  (* Up until this point, all types defined here compose a finite set. Natural
   * numbers, however, comprehend an infinite set. Hence, how one might
   * represent them?
   *
   * Just like computers use a binary representation to facilitate circuitry, a
   * person who's trying to prove something must pick a representation that
   * eases such proofs.
   *
   * Unary representation?
   *)
  Inductive nat : Type :=
    | O                    (* zero *)
    | S (n : nat).         (* successor of another nat *)

  (* That's indeed a powerful definition.
   *
   * The constructor `O` belongs to the set `nat`.
   * For all `n` that belongs to `nat`, `S n` will also belong to `nat`.
   *
   * So:
   *     - Zero may be encoded as `O`,
   *     - One as `S O`,
   *     - Two as `S (S O)`,
   *     - (...)
   *)

  Check O: nat.
  Check S: nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

  Example test_pred1: pred O = O.
  Proof. simpl. reflexivity. Qed.
  Example test_pred2: pred (S O) = O.
  Proof. simpl. reflexivity. Qed.
  Example test_pred3: pred (S (S O)) = S O.
  Proof. simpl. reflexivity. Qed.

  (* Notice that, since the previous `nat` definition is inside a module, all
   * other scopes do not use it. Rather, they use `nat` defined in the std lib.
   *)

End NatPlayground1.

Check (S (S (S (O)))). (* Will print 3, built-in Coq magic notation. *)

Example coq_nat_magic: (S (S (S (O)))) = 3.
Proof. simpl. reflexivity. Qed.

  Definition suc (n : nat) : nat := S (n).

  Example test_suc1: suc O = 1.
  Proof. simpl. reflexivity. Qed.
  Example test_suc2: suc (S O) = 2.
  Proof. simpl. reflexivity. Qed.

Definition minustwo (n : nat) :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Example test_minustwo1: minustwo O = 0.
Proof. simpl. reflexivity. Qed.
Example test_minustwo2: minustwo (S O) = 0.
Proof. simpl. reflexivity. Qed.
Example test_minustwo3: minustwo (S (S O)) = 0.
Proof. simpl. reflexivity. Qed.
Example test_minustwo4: minustwo (S (S (S O))) = 1.
Proof. simpl. reflexivity. Qed.

(* Notice that, while the terms `S` and `pred` have the same type, they do not
 * represent the same concept.
 *
 * `S` is a constructor. It just creates a value an does nothing with it.
 * `pred` is a _computation_ rule (i.e., a function). It takes a value and
 * does something with it.
 *)
Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

(* Use `Fixpoint` to define a recursive function. *)
Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Example test_odd1: odd 0 = false.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd3: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (m n : nat) : nat :=
  match m with
  | O => n
  | S m' => S (plus m' n)
  end.

  Example test_plus1: plus 2 3 = 5.
  Proof. simpl. reflexivity. Qed.

  (* What's even happening above??
   * 
   *   plus [(S (S O)) (S (S (S O)))] = plus [2 3]
   *                   ^^^^^^^^^^^^^
   *
   * = S (plus [(S (S O)) (S (S O))])
   *   ^                  ^^^^^^^^^
   *
   * = S (S (plus [(S (S O)) (S O)]))
   *   ^  ^                  ^^^^^
   *
   * = S (S (S (plus [(S (S O)) O])))
   *   ^  ^  ^        ----2---- *
   *
   * = S (S (S (S (S O))))
   *   ^  ^  ^  ---2---
   *
   * = 5
   *)

  Fixpoint minus (m n : nat) : nat :=
    match m, n with
    | O, _ => O
    | m, O => m
    | S m', S n' => minus m' n'
    end.

  Example test_minus1: minus 2 0 = 2.
  Proof. simpl. reflexivity. Qed.
  Example test_minus2: minus 0 2 = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_minus3: minus 5 3 = 2.
  Proof. simpl. reflexivity. Qed.
  Example test_minus4: minus 3 5 = 0.
  Proof. simpl. reflexivity. Qed.

  Fixpoint mult (m n : nat) : nat :=
    match n with 
    | O => O
    | S n' => plus m (mult m n')
    end.

  Example test_mult1: mult 3 0 = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_mult2: mult 3 1 = 3.
  Proof. simpl. reflexivity. Qed.
  Example test_mult3: mult 3 2 = 6.
  Proof. simpl. reflexivity. Qed.

End NatPlayground2.

Fixpoint pow (base exp : nat) : nat :=
  match exp with
  | O => S O
  | S exp' => mult base (pow base exp')
  end.

Example test_pow1: pow 3 0 = 1.
Proof. simpl. reflexivity. Qed.
Example test_pow2: pow 3 1 = 3.
Proof. simpl. reflexivity. Qed.
Example test_pow3: pow 3 2 = 9.
Proof. simpl. reflexivity. Qed.

(* Common notation *)
Notation "x + y" := (plus x y)
  (at level 50, left associativity)
  : nat_scope.
Notation "x - y" := (minus x y)
  (at level 50, left associativity)
  : nat_scope.
Notation "x * y" := (mult x y)
  (at level 40, left associativity)
  : nat_scope.

Check ((0 + 1) + 1) : nat.

(* Checks if both arguments are equal. *)
Fixpoint eqb (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | O, _ => false
  | _, O => false
  | S m', S n' => eqb m' n'
  end.

Example test_eqb1: eqb 0 5 = false.
Proof. simpl. reflexivity. Qed.
Example test_eqb2: eqb 5 0 = false.
Proof. simpl. reflexivity. Qed.
Example test_eqb3: eqb 4 5 = false.
Proof. simpl. reflexivity. Qed.
Example test_eqb4: eqb 5 4 = false.
Proof. simpl. reflexivity. Qed.
Example test_eqb5: eqb 5 5 = true.
Proof. simpl. reflexivity. Qed.

(* Checks if the first argument is less than or equal to the first. *)
Fixpoint leb (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | O, n => true
  | m, O => false
  | S m', S n' => leb m' n'
  end.

Example test_leb1: leb 4 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 3 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 3 = false.
Proof. simpl. reflexivity. Qed.

(* Common notation. *)
Notation "x =? y" := (eqb x y)
  (at level 70)
  : nat_scope.
Notation "x <=? y" := (leb x y)
  (at level 70)
  : nat_scope.

Example test_leb4: (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Notice the difference between `=` and `=?`.
 *
 * The former, built into Coq, is used to define a proposition (i.e. a logical
 * claim which may be proved later). The latter, however, may be seen as a
 * simple function (a notation for `eqb`), which may be used to compute a
 * value.
 *)

(******************************************************************************)

(*
 * PROOF BY SIMPLIFICATION
 *)

(* Notice that the previous proofs used `simpl` to simplify both sides of the
 * equation while `reflexivity` was used to check that both sides contain
 * identical values.
 *
 * In such examples, however, `simpl` was not needed at all since `reflexivity`
 * can perform simplifications when checking that two sides are equal.
 * Indeed, `reflexivity` is a little bit more powerful since it can also
 * _unfold_ defined terms.
 *)

(* `intros`, `simpl` and `reflexivity` are called tactics. A tactic is a command
 * used between `Prof` and `Qed` to guide the process of checking some claim.
 *
 * `Theorem`, `Example`, `Lemma`, `Fact` and `Remark` are almost analogous.
 *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(* Theorem plus 1 on the left. *)
Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

(* Theorem mult 0 on the left. *)
Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

(******************************************************************************)

(*
 * PROOF BY REWRITING
 *)

Theorem plus_id_example : forall m n : nat,
  m = n ->
  m + m = n + n.
Proof.
  (* Move both quantifiers, `m` and `n`, into the context. *)
  intros m n.
  (* Move the hypothesis, `m = n`, into the context. *)
  intros Hyp.
  (* Rewrite the goal, `m + m = n + n`, using the hypothesis,
   * so we get `n + n = n + n`.
   *
   * The arrow below tells Coq to rewrite from left to right. *)
  rewrite -> Hyp.
  reflexivity.
Qed.

(* The `rewrite` tactic may be used with a previously proved theorem instead
 * of an hypothesis from the context.
 *)

(* Provided by the standard library: *)
Check mult_n_O:
  forall n : nat, 0 = n * 0.
Check mult_n_Sm:
  forall n m : nat, n * m + n = n * S m.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  (* Notice the `<-`. I want to go from `n * 0` to `0`,
   * and not from `0` to `n * 0`. *)
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

(******************************************************************************)

(*
 * PROOF BY CASE ANALYSIS
 *)

(* Not everything can be proved by simple calculation and rewriting.
 * In general, unknown and hypothetical values can block simplification.
 *)

Theorem plus_1_neq_0_first_try : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.
Abort.

(* The `simpl` tactic cannot do anything meaningful above since both `+` and
 * `=?` perform a `match` in the first argument (here, `n` and `n + 1`,
 * respectively). Since those are expressions with unknown values,
 * simplification becomes impossible.
 *
 * To make progress, one must consider the possible forms of the given unknown
 * value separately. Given `n: nat`, we must consider the constructors `O` and
 * `S`. The tactic `destruct` can be used here.
 *)

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - simpl plus. (* May be elided. `reflexivity` already does that. *)
    simpl eqb.  (* May be elided. *)
    reflexivity.
  - simpl plus. (* `simpl` again won't do anything since `n'` is unknown. *)
    simpl eqb.  (* See `eqb` definition. *)
    reflexivity.
Qed.

(* The tactic `destruct` will generate two sub goals from the original goal.
 * Each of then will have to be proven separately.
 *
 * ` as [| n'] ` is an **intro pattern**. It tells what variable names should be
 * introduced in each sub goal. In general, it is a list of list of names,
 * separated by `|`.
 * In this case, the first element is empty since the `O` constructor is
 * nullary. The second element gives a single name, ` n' ` to `S`'s element.
 *
 * `eqn:E` tells `destruct` to give the name `E` to the equation. Since the
 * sub goal's equation is named, their assumptions (e.g. `n: nat`, introduced by
 * `intros n`) are not elided (the default behavior without `eqn:E`).
 *
 * `-` signs a bullet. For each sub goal generated by `destruct`, one must
 * handle the respective bullet. Other allowed signals are `-`, `+`, `*`, or a
 * repetition of them, such as `--` or `***`. Useful in nested `destruct`s.
 *)

(* Involutive means that negation is its own inverse. *)
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c : bool,
  andb b c = andb c b.
Proof.
  intros b c.
  destruct b eqn:EqnB.
  - destruct c eqn:EqnC.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:EqnC.
    + reflexivity.
    + reflexivity.
Qed.

(* The pattern `intros n. destruct n as [| n'] eqn:E.` is so common that
 * exists a shorthand for it. One may perform case analysis on a variable
 * when introducing it by using an intro pattern instead of a variable name.
 *)
Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

(* If there aren't any constructors that need names, `[]` may be used. *)
Theorem andb_commutative' : forall b c : bool,
  andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.