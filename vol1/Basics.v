Module EnumeratedTypes1.

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

End EnumeratedTypes1.

(******************************************************************************)

Module Bool.

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

  (* Declare a notation to extend the Coq syntax. *)
  Notation "! a" := (negb a) (at level 65, right associativity).

  Example test_negb_notation: !true = false.
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

  Notation "a && b" := (andb a b).

  Example test_andb_notation: true && false = false.
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

  Notation "a || b" := (orb a b).

  Example test_orb_notation: false || true = true.
  Proof. simpl. reflexivity. Qed.

End Bool.

(******************************************************************************)

Module CheckingTypes.

  (* `Check` prints the given expression's type. *)
  Check true.

  (* `Check` may also be used to check the type. *)
  Check andb: bool -> bool -> bool.
  Check negb: bool -> bool.
  Check (negb true) : bool.

End CheckingTypes.

(******************************************************************************)

Module EnumeratedTypes2.

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

End EnumeratedTypes2.

(******************************************************************************)

Module Modules.

  Include EnumeratedTypes2.

  Module Playground.
    Definition b : rgb := blue.
  End Playground.

  Definition b :bool := true.

  Check Playground.b : rgb.
  Check b: bool.

End Modules.

(******************************************************************************)

(* Tuples *)

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

  (* Notice that, since the previous `nat` definition is inside a module, all
   * other scopes do not use it. Rather, they use `nat` defined in the std lib.
   *)

End NatPlayground1.

Module NatPlayground2.

  Check (S (S (S (O)))). (* Will print 3, built-in Coq magic notation. *)
  Example coq_nat_magic: (S (S (S (O)))) = 3.
  Proof. simpl. reflexivity. Qed.

  Definition suc (n : nat) : nat := S (n).

  Example test_suc1: suc O = 1.
  Proof. simpl. reflexivity. Qed.
  Example test_suc2: suc (S O) = 2.
  Proof. simpl. reflexivity. Qed.

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

  Example test_pred1: pred O = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_pred2: pred (S O) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_pred3: pred (S (S O)) = 1.
  Proof. simpl. reflexivity. Qed.

  Definition minus_two (n : nat) :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

  Example test_minus_two1: minus_two O = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_minus_two2: minus_two (S O) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_minus_two3: minus_two (S (S O)) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_minus_two4: minus_two (S (S (S O))) = 1.
  Proof. simpl. reflexivity. Qed.

  (* Notice that, while the terms `S` and `suc` have the same type, they do not
   * represent the same concept.
   *
   * `S` is a constructor. It just creates a value an does nothing with it.
   * `suc` is a _computation_ rule (i.e., a function). It takes a value and does
   * something with it.
   *)
  Check S: nat -> nat.
  Check suc: nat -> nat.

  (* Use `Fixpoint` to define a recursive function. *)
  Fixpoint even (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

  Definition odd (n : nat) : bool := negb (even n).

  Example test_odd1: odd 0 = false.
  Proof. simpl. reflexivity. Qed.
  Example test_odd2: odd 1 = true.
  Proof. simpl. reflexivity. Qed.
  Example test_odd3: odd 4 = false.
  Proof. simpl. reflexivity. Qed.

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
  Notation "x + y" := (plus x y)
    (at level 50, left associativity)
    : nat_scope.
  Notation "x - y" := (minus x y)
    (at level 50, left associativity)
    : nat_scope.
  Notation "x * y" := (mult x y)
    (at level 40, left associativity)
    : nat_scope.
  Notation "x =? y" := (eqb x y)
    (at level 70)
    : nat_scope.
  Notation "x <=? y" := (leb x y)
    (at level 70)
    : nat_scope.

  (* Notice the difference between `=` and `=?`.
   *
   * The former, built into Coq, is used to define a proposition (i.e. a logical
   * claim which may be proved later). The latter, however, may be seen as a
   * simple function (a notation for `eqb`), which may be used to compute a
   * value.
   *)

End NatPlayground2.