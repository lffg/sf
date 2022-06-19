From LF Require Export Tactics.

(* Equality propositions `x1 = x2`, implications `P -> Q` and quantified
 * propositions `forall x, P`.
 *
 * In Coq, propositions have the type `Prop`. They should only be syntactically
 * valid. The `Prop` type says nothing about the proposition's truthfulness.
 * Hence, not all propositions are provable.
 *)

Check (3 = 3): Prop.
Check (forall m n : nat, n + m = m + n): Prop.

(* Propositions are normal values, and, as such, first class citizens.
 *
 * A function that return a proposition is said to define properties on their
 * argument.
 *
 * The `=` operator is itself a function that returns `Prop`.
 *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

(* One now may prove that the `S` constructor is injective. *)
Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as goal. apply goal.
Qed.

Check @eq: forall A : Type, A -> A -> Prop.

(******************************************************************************)

(*
 * LOGICAL CONNECTIVES
 *)

(* Conjunction (and).
 *
 * To prove a conjunction, one should use the `split` tactic.
 *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

(* For any propositions `A` and `B`, if `A` is true and `B` is true, one
 * can conclude that `A /\ B` is also true.
 *)

Lemma and_intro : forall A B : Prop,
  A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

(* `and_intro` has the same effect as `split`, as applying `and_intro` will
 * generate two new sub-goals, one for each of its hypotheses.
 *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  -  reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

Example and_exercise : forall n m : nat,
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct n.
    + reflexivity.
    + discriminate.
  - destruct m.
    + reflexivity.
    + rewrite <- plus_n_Sm in H. discriminate.
Qed.

(******************************************************************************)

(* In order to use a conjunctive hypothesis to prove something else, the
 * `destruct` tactic may be used.
 *)

Lemma and_example2 : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm]. (* Or simply `intros n m [Hn Hm]`. *)
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(* Conjunction hypothesis often arise from intermediate steps. E.g.: *)
Lemma and_example3 : forall n m : nat,
  n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  (* Notice that, since `Hm` isn't needed here, it was discarded using `_`. *)
  destruct H as [Hn _].
  rewrite Hn.
  reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q [HP _].
  apply HP.
Qed.

(******************************************************************************)

(* Exercise *)

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
  intros P Q [_ HQ].
  apply HQ.
Qed.

(******************************************************************************)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  apply HQ. apply HP.
Qed.

(* Exercise *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split.
  apply HP. apply HQ. apply HR.
Qed.

(******************************************************************************)

Check and: Prop -> Prop -> Prop.
Check or: Prop -> Prop -> Prop.

(* Disjunction (or).
 *
 * To use a disjunctive hypothesis, one proceed by case analysis, one for each
 * possible truthful argument (either left or right).
 *
 * To show the truthfulness of a disjunction, it suffices to show that one of it
 * sides holds. To do that, one may use the `left` or `right` tactics.
 *)

Lemma factor_is_O : forall n m : nat,
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - (* `n = 0` *)
    rewrite Hn. reflexivity.
  - (* `m = 0` *)
    rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ : forall n : nat,
  n = 0 \/ n = S (pred n).
Proof.
  intros [| n'].
  - (* n = 0 *)
    left. reflexivity.
  - (* n = S n' *)
    right. simpl. reflexivity.
Qed.

(* Negation (falsehood; not).
 *
 * To show that some proposition is not true, one may use the `~` (not)
 * operator.
 *
 * The principle of explosion asserts that, given an assumed contradiction,
 * any other proposition can be derived.
 *
 * From that intuition, `~P` can be defined as `forall Q, P -> Q`.
 *
 *     In this case, since `Q` can be anything (including an absurd statement),
 *     it's only reasonable to assume that `P` is also absurd, as, from the
 *     principle of explosion, anything can arise from an absurd hypothesis.
 *     Hence, P being an absurd justifies the case where Q is also absurd.
 *
 *
 *
 * In Coq, `~P` is defined as `P -> False`, where False is a contradictory
 * proposition. `P -> False` is equivalent to `forall Q, P -> Q`.
 *
 *     In this case, the only way to get to an absurd proposition (the `False`)
 *     is having an absurd hypothesis. In such a case, `P` must also be absurd.
 *)

Module MyNot.

  (* False is a contradictory proposition, defined in the stdlib. *)
  Check False: Prop.

  (* From the principle of explosion, a way to show `False` (an absurd
   * proposition) is to assume that the hypothesis (`P`) is also absurd.
   *)
  Definition not (P : Prop) := P -> False.

  Notation "~ x" := (not x) : type_scope.

  Check not: Prop -> Prop.

End MyNot.

(* If one gets `False` into the proof context, one can `destruct` on it to
 * complete any goal.
 *)

(* “From falsehood follows whatever one would like.”, another typical phrasing
 * to refer to the principle of explosion.
 *)
Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros p contra.
  destruct contra.
Qed.

(******************************************************************************)

(* Exercise *)

(* Show that Coq's definition of negation implies the intuitive one mentioned
 * above:
 *)

Fact not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P NP Q HP.
  destruct NP.
  apply HP.
Qed.

(******************************************************************************)

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  (* `0 <> 1` is the same as `~ (0 = 1)` and `not (0 = 1)`.
   * Which, from the definition of `not`, unfolds to `(0 = 1) -> False`.
   *
   * Since the only way to construct an absurd is to already have an absurd,
   * `0 = 1` must be absurd.
   *)
  unfold not.
  intros contra.
  discriminate contra.
Qed.

(******************************************************************************)

Theorem not_False : ~ False.
Proof.
  unfold not.
  intros madness.
  destruct madness.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP].
  unfold not in HNP.
  (* Search `apply L in H` in the previous chapter.
   *
   * When using `apply L in H`, where `L : X -> Y`, if `H` matches `Y`, `L` is
   * substituted with `Y`.
   * Hence, `apply `P -> False` in `P` tries to match `P` with `P`. Since this
   * match is successful, the “apply target” is rewritten as `False`.
   *)
  apply HNP in HP.
  (* `HP` is false. We have an absurd statement in the context.
   * This may be destructed.
   *)
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P.
  intros HP.
  (* `~~P` = `(P -> False) -> False` = `~P -> False` *)
  intros HNP.
  unfold not in HNP.
  (* See the explanation immediately above. The following gets `False` in the
   * proof context.
   *)
  apply HNP in HP.
  destruct HP.
Qed.

(* Another way (from the book). *)
Theorem double_neg' : forall P : Prop,
  P -> ~~P.
Proof.
  intros P HP.
  unfold not.
  intros HNP.
  (* Applies `P -> False` in the goal (`False`). Since the implication
   * conclusion matches the goal, one gets the implication premises as
   * sub-goals. In this case, the only premise is `P`.
   *)
  apply HNP.
  (* `apply P` in the goal (`P`) finishes it. Trivial. *)
  apply HP.
Qed.
