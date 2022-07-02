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
  apply HNP in HP as contra.
  destruct contra.
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

(* Exercise *)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ.
  unfold not.
  intros HNQ HP.
  (* Apply `P -> Q` in `P`, which will turn it in `Q`. *)
  apply HPQ in HP as HQ.
  (* Apply `Q -> False` in `Q`, which will turn it in `False`. *)
  apply HNQ in HQ as contra.
  (* `False` in the context, just `destruct` it. *)
  destruct contra.
Qed.

(* Exercise *)

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros [HP HNP].
  apply HNP in HP as contra.
  destruct contra.
Qed.

(******************************************************************************)

Check ex_falso_quodlibet: forall (P : Prop), False -> P.

(* A useful trick when trying to prove an absurd goal is to apply
 * `ex_falso_quodlibet` to change the goal to `False`.
 *
 * This makes it easier to use assumptions of the form `~P` that might be
 * available in the context. In particular, assumptions of the form `x <> y`.
 *
 * Since using `ex_falso_quodlibet`, Coq provides the built-in tactic `exfalso`.
 *)

Theorem not_true_is_false : forall (b : bool),
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso. (* Or `apply ex_falso_quodlibet.` *)
    apply H. reflexivity.
  - reflexivity.
Qed.

(* Truth.
 *
 * Besides `False`, Coq also provides `True`, a proposition which is trivially
 * true. To prove it, one may use the constant `I: True`.
 *
 * It is rarely used, though.
 *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(* As an example of its use, let's demonstrate how to achieve the same effect
 * as the `discriminate` without using it.
 *)

Definition disc_fn (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc : forall n, ~ (O = S n).
Proof.
  intros n H1.
  assert (H2: disc_fn O). { simpl. apply I. }
  rewrite H1 in H2. simpl in H2. apply H2.
Qed.

(* Logical Equivalence (“if and only if”).
 *)

Module MyIff.

  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

  Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HPQ HQP].
  split.
  - apply HQP.
  - apply HPQ.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H.
    rewrite H.
    intros contra. discriminate contra.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem or_distributes_over_and : forall (P Q R : Prop),
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [hP | [hQ hR]].
    + split.
      * left. apply hP.
      * left. apply hP.
    + split.
      * right. apply hQ.
      * right. apply hR.
  - intros [[hP1 | hQ] [hP2 | hR]].
    + left. apply hP1.
    + left. apply hP1.
    + left. apply hP2.
    + right. split. apply hQ. apply hR.
Qed.

(* ================================================================= *)
(** ** Setoids and Logical Equivalence *)

(** Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  In
    particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we have
    to import the Coq library that supports it: *)

From Coq Require Import Setoids.Setoid.

(** A "setoid" is a set equipped with an equivalence relation,
    that is, a relation that is reflexive, symmetric, and transitive.
    When two elements of a set are equivalent according to the
    relation, [rewrite] can be used to replace one element with the
    other. We've seen that already with the equality relation [=] in
    Coq: when [x = y], we can use [rewrite] to replace [x] with [y],
    or vice-versa.

    NOTE:
        Equivalence relations:
          - Reflexive relation: all elements of a set are related to itself, i.e.
            `x R x`.
          - Symmetric relation: if `a R b`, then `b R a`;
          - Transitive relation: if `a R b` and `b R c`, then `a R c`.

        A setoid is a set with equivalence relation. `rewrite` and `reflexivity`
        can be used in setoids.

    Similarly, the logical equivalence relation [<->] is reflexive,
    symmetric, and transitive, so we can use it to replace one part of
    a proposition with another: if [P <-> Q], then we can use
    [rewrite] to replace [P] with [Q], or vice-versa. *)

(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's prove a couple of basic iff equivalences. *)

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  unfold iff.
  split.
  - apply Coq.Arith.Mult.mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity]
    to give smooth proofs of statements involving equivalences.  For
    example, here is a ternary version of the previous [mult_0]
    result: *)

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  Check mul_eq_0.
  (* Apply `forall n m : nat, n * m = 0 <-> n = 0 \/ m = 0` in:
   *
   *      n *  m * p = 0     <-> ...
   *      n * (m * p = 0)    <-> ...
   *
   * Yields:
   *
   *      n * m = 0 \/ p = 0 <-> ...
   *)
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

(** The [apply] tactic can also be used with [<->]. When given an
    equivalence as its argument, [apply] tries to guess which
    direction of the equivalence will be useful. *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mul_eq_0. apply H.
Qed.

Lemma apply_iff_example' :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m.
  apply mul_eq_0.
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

(** Another important logical connective is _existential
    quantification_.  To say that there is some [x] of type [T] such
    that some property [P] holds of [x], we write [exists x : T,
    P]. As with [forall], the type annotation [: T] can be omitted if
    Coq is able to infer from the context what the type of [x] should
    be. *)

(** NOTE:
    forall x : T, P.
    exists x : T, P.

    forall x, P.    (infer)
    exists x, P.    (infer) *)

(** To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t].  Then we prove that [P] holds after
    all occurrences of [x] are replaced by [t]. *)

Definition Even x := exists (n : nat), x = double n.

Check Even: nat -> Prop.

Lemma four_is_even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(** **** Exercise: 1 star, standard, especially useful (dist_not_exists)

    Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold."  (Hint: [destruct H as [x E]] works on
    existential assumptions!)  *)

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P U [x not_Px].
  unfold not in not_Px.
  apply not_Px.
  apply U.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (dist_exists_or)

    Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [nx [H | H]].
    + left. exists nx. apply H.
    + right. exists nx. apply H.
  - intros [[nx H] | [nx H]].
    + exists nx. left. apply H.
    + exists nx. right. apply H.
Qed.

(** [] *)

(* ################################################################# *)
(** * Programming with Propositions *)

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:

       - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if either it is equal to [x'] or it occurs in
         [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning a proposition (!): *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2__MY : forall (n : nat),
  In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl. intros n [H | [H | contra]].
  - exists 1. symmetry. apply H.
  - exists 2. symmetry. apply H.
  - destruct contra.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also prove more generic, higher-level lemmas about [In].

    (Note how [In] starts out applied to a variable and only gets
    expanded when we do case analysis on this variable.) *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + (* `=` binds tighter. (a = b) \/ (c) *)
      right.
      apply IHl'. apply H.
Qed.

(** This way of defining propositions recursively, though convenient
    in some cases, also has some drawbacks.  In particular, it is
    subject to Coq's usual restrictions regarding the definition of
    recursive functions, e.g., the requirement that they be "obviously
    terminating."  In the next chapter, we will see how to define
    propositions _inductively_, a different technique with its own set
    of strengths and limitations. *)

(** **** Exercise: 3 stars, standard (In_map_iff) *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x, (f x = y) /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [| h' t' IHt'].
    + intros [].
    + simpl. intros [H | H].
      * exists h'. split.
        -- apply H.
        -- left. reflexivity.
      * apply IHt' in H as [x []].
        exists x. split.
        -- assumption.
        -- right. assumption.
  - intros [x []]. subst. apply In_map. assumption.
Qed.

(** [] *)

Search Coq.Init.Logic.or_assoc.

(** **** Exercise: 2 stars, standard (In_app_iff) *)
Theorem In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [| hl tl IHtl].
  - unfold iff. simpl. split.
    + intros. right. assumption.
    + intros [[] | H]. assumption.
  - unfold iff. split.
    + intros [H1 | H2].
      * left. left. assumption.
      * simpl. rewrite <- or_assoc. right. apply IHtl. assumption.
    + intros [[H1 | H2] | H3].
      * left. assumption.
      * simpl. right. apply IHtl. left. assumption.
      * simpl. right. apply IHtl. right. assumption.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (All)

    Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h' :: t' => P h' /\ All P t'
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T prop_fn l. induction l as [| lh lt IHlt].
  - simpl. split; intros.
    + apply I.
    + contradiction.
  - split.
    + intros H. simpl. split.
      * apply H. left. reflexivity.
      * apply IHlt. intros. apply H. simpl. right. assumption.
    + simpl. intros [] x [H' | H'].
      * rewrite <- H'. assumption.
      * apply IHlt; assumption.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (combine_odd_even)

    Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) (n : nat) : Prop :=
  if odd n then Podd n else Peven n.

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n Hodd Heven.
  unfold combine_odd_even. destruct (odd n).
  - apply Hodd. reflexivity.
  - apply Heven. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even. destruct (odd n); intros.
  - assumption.
  - discriminate.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even. destruct (odd n); intros.
  - discriminate.
  - assumption.
Qed.

(** [] *)

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** One feature that distinguishes Coq from some other popular
    proof assistants (e.g., ACL2 and Isabelle) is that it treats
    _proofs_ as first-class objects.

    There is a great deal to be said about this, but it is not
    necessary to understand it all in detail in order to use Coq.
    This section gives just a taste, while a deeper exploration can be
    found in the optional chapters [ProofObjects] and
    [IndPrinciples]. *)

(** We have seen that we can use [Check] to ask Coq to print the type
    of an expression.  We can also use it to ask what theorem a
    particular identifier refers to. *)

Check plus     : nat -> nat -> nat.
Check add_comm : forall n m : nat, n + m = m + n.

(** Coq checks the _statement_ of the [add_comm] theorem (or prints
    it for us, if we leave off the part beginning with the colon) in
    the same way that it checks the _type_ of any term (e.g., plus)
    that we ask it to [Check]. Why? *)

(** The reason is that the identifier [add_comm] actually refers to a
    _proof object_, which represents a logical derivation establishing
    of the truth of the statement [forall n m : nat, n + m = m + n].  The
    type of this object is the proposition which it is a proof of. *)

(** Intuitively, this makes sense because the statement of a
    theorem tells us what we can use that theorem for. *)

(** Operationally, this analogy goes even further: by applying a
    theorem as if it were a function, i.e., applying it to values and
    hypotheses with matching types, we can specialize its result
    without having to resort to intermediate assertions.  For example,
    suppose we wanted to prove the following result: *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this
    by rewriting with [add_comm] twice to make the two sides match.
    The problem, however, is that the second [rewrite] will undo the
    effect of the first. *)

Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

(** We saw similar problems back in Chapter [Induction], and saw one
    way to work around them by using [assert] to derive a specialized
    version of [add_comm] that can be used to rewrite exactly where
    we want. *)

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
  { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [add_comm] directly
    to the arguments we want to instantiate it with, in much the same
    way as we apply a polymorphic function to a type argument. *)

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** Let's see another example of using a theorem like a function.

    The following theorem says: any list [l] containing some element
    must be nonempty. *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(** What makes this interesting is that one quantified variable
    ([x]) does not appear in the conclusion ([l <> []]). *)

(** We should be able to use this theorem to prove the special case
    where [x] is [42]. However, naively, the tactic [apply in_not_nil]
    will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** There are several ways to work around this: *)

(** Use [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Use [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(** You can "use theorems as functions" in this way with almost all
    tactics that take a theorem name as an argument.  Note also that
    theorem application uses the same inference mechanisms as function
    application; thus, it is possible, for example, to supply
    wildcards as arguments to be inferred, or to declare some
    hypotheses to a theorem as implicit by default.  These features
    are illustrated in the proof below. (The details of how this proof
    works are not critical -- the goal here is just to illustrate what
    can be done.) *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples in later chapters. *)

(* ################################################################# *)
(** * Coq vs. Set Theory *)

(** Coq's logical core, the _Calculus of Inductive
    Constructions_, differs in some important ways from other formal
    systems that are used by mathematicians to write down precise and
    rigorous definitions and proofs.  For example, in the most popular
    foundation for paper-and-pencil mathematics, Zermelo-Fraenkel Set
    Theory (ZFC), a mathematical object can potentially be a member of
    many different sets; a term in Coq's logic, on the other hand, is
    a member of at most one type.  This difference often leads to
    slightly different ways of capturing informal mathematical
    concepts, but these are, by and large, about equally natural and
    easy to work with.  For example, instead of saying that a natural
    number [n] belongs to the set of even numbers, we would say in Coq
    that [Even n] holds, where [Even : nat -> Prop] is a property
    describing even numbers.

    We conclude this chapter with a brief discussion of some of the
    most significant differences between the two worlds. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** Coq's logic is intentionally quite minimal.  This means that there
    are occasionally some cases where translating standard
    mathematical reasoning into Coq can be cumbersome or sometimes
    even impossible, unless we enrich the core logic with additional
    axioms. *)

(** The equality assertions that we have seen so far mostly have
    concerned elements of inductive types ([nat], [bool], etc.).  But,
    since Coq's equality operator is polymorphic, we can use it at
    _any_ type -- in particular, we can write propositions claiming
    that two _functions_ are equal to each other: *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. simpl. reflexivity. Qed.

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same output on every input:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** Informally, an "extensional property" is one that pertains to an
    object's observable behavior.  Thus, functional extensionality
    simply means that a function's identity is completely determined
    by what we can observe from it -- i.e., the results we obtain
    after applying it. *)

(** However, functional extensionality is not part of Coq's built-in
    logic.  This means that some apparently "obvious" propositions are
    not provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

(** However, we can add functional extensionality to Coq's core using
    the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

(** Defining something as an [Axiom] has the same effect as stating a
    theorem and skipping its proof using [Admitted], but it alerts the
    reader that this isn't just something we're going to come back and
    fill in later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(** Naturally, we must be careful when adding new axioms into Coq's
    logic, as this can render it _inconsistent_ -- that is, it may
    become possible to prove every proposition, including [False],
    [2+2=5], etc.!

    Unfortunately, there is no simple way of telling whether an axiom
    is safe to add: hard work by highly trained mathematicians is
    often required to establish the consistency of any particular
    combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command:
    [Print Assumptions function_equality_ex2]. *)

(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g

    (You may also see [add_comm] listed as an assumption, depending
    on whether the copy of [Tactics.v] in the local directory has the
    proof of [add_comm] filled in.) *)

(** **** Exercise: 4 stars, standard (tr_rev_correct)

    One problem with the definition of the list-reversing function
    [rev] that we have is that it performs a call to [app] on each
    step; running [app] takes time asymptotically linear in the size
    of the list, which means that [rev] is asymptotically quadratic.
    We can improve this with the following definitions: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version of [rev] is said to be _tail-recursive_, because the
    recursive call to the function is the last operation that needs to
    be performed (i.e., we don't have to execute [++] after the
    recursive call); a decent compiler will generate very efficient
    code in this case.

    Prove that the two definitions are indeed equivalent. *)

Lemma rev_append_app : forall X (l acc : list X),
  rev_append l acc = rev_append l [] ++ acc.
Proof.
  intros X l. induction l as [| lh lt IHlt].
  - reflexivity.
  - intros acc.
    simpl.
    rewrite -> IHlt.
    rewrite -> IHlt with (acc := [lh]).
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  unfold tr_rev. intros X. apply functional_extensionality.
  intros l. induction l as [| h t IHt].
  - reflexivity.
  - simpl. rewrite <- IHt.
    apply rev_append_app.
Qed.

(** [] *)

(* ================================================================= *)
(** ** Propositions vs. Booleans

    We've seen two different ways of expressing logical claims in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    Here are the key differences between [bool] and [Prop]:

                                           bool     Prop
                                           ====     ====
           decidable?                      yes       no
           useable with match?             yes       no
           equalities rewritable?          no        yes
*)

(** The most essential difference between the two worlds is
    _decidability_.  Every Coq expression of type [bool] can be
    simplified in a finite number of steps to either [true] or
    [false] -- i.e., there is a terminating mechanical procedure for
    deciding whether or not it is [true].  This means that, for
    example, the type [nat -> bool] is inhabited only by functions
    that, given a [nat], always return either [true] or [false]; and
    this, in turn, means that there is no function in [nat -> bool]
    that checks whether a given number is the code of a terminating
    Turing machine.  By contrast, the type [Prop] includes both
    decidable and undecidable mathematical propositions; in
    particular, the type [nat -> Prop] does contain functions
    representing properties like "the nth Turing machine halts."

    The second row in the table above follow directly from this
    essential difference.  To evaluate a pattern match (or
    conditional) on a boolean, we need to know whether the scrutinee
    evaluates to [true] or [false]; this only works for [bool], not
    [Prop].  The third row highlights another important practical
    difference: equality functions like [eqb_nat] that return a
    boolean cannot be used directly to justify rewriting, whereas
    the propositional [eq] can be. *)

(* ================================================================= *)
(** ** Working with Decidable Properties *)

(** Since [Prop] includes _both_ decidable and undecidable properties,
    we have two choices when when we are dealing with a property that
    happens to be decidable: we can express it as a boolean
    computation or as a function into [Prop].

    For instance, to claim that a number [n] is even, we can say
    either... *)

(** ... that [even n] evaluates to [true]... *)
Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

(** Of course, it would be pretty strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!  Fortunately, we can prove that they do... *)

(** We first need two helper lemmas. *)
Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [| k'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars, standard (even_double_conv) *)

(* Hint: Use the [even_S] lemma from [Induction.v]. *)
Check even_S: forall n : nat, even (S n) = negb (even n).

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n. induction n as [| n' [x H]].
  - exists 0. reflexivity.
  - rewrite even_S. destruct (even n'); simpl; rewrite H.
    + exists x. reflexivity.
    + exists (S x). reflexivity.
Qed.

(** [] *)

(** Now the main theorem: *)
Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

(** In view of this theorem, we say that the boolean computation
    [even n] is _reflected_ in the truth of the proposition
    [exists k, n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent. *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(** Even when the boolean and propositional formulations of a claim
    are equivalent from a purely logical perspective, they are often
    not equivalent from the point of view of convenience for some
    specific purpose. *)

(** In the case of even numbers above, when proving the
    backwards direction of [even_bool_prop] (i.e., [even_double],
    going from the propositional to the boolean claim), we used a
    simple induction on [k].  On the other hand, the converse (the
    [even_double_conv] exercise) required a clever generalization,
    since we can't directly prove [(even n = true) -> Even n]. *)

(** We cannot _test_ whether a [Prop] is true or not in a
    function definition; as a consequence, the following code fragment
    is rejected: *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects
    an element of [bool] (or some other inductive type with two
    elements).  The reason has to do with the _computational_ nature
    of Coq's core language, which is designed so that every function
    it can express is computable and total.  One reason for this is to
    allow the extraction of executable programs from Coq developments.
    As a consequence, [Prop] in Coq does _not_ have a universal case
    analysis operation telling whether any given proposition is true
    or false, since such an operation would allow us to write
    non-computable functions.

    Beyond the fact that non-computable properties are impossible in
    general to phrase as boolean computations, even many _computable_
    properties are easier to express using [Prop] than [bool], since
    recursive function definitions in Coq are subject to significant
    restrictions.  For instance, the next chapter shows how to define
    the property that a regular expression matches a given string
    using [Prop].  Doing the same with [bool] would amount to writing
    a regular expression matching algorithm, which would be more
    complicated, harder to understand, and harder to reason about than
    a simple (non-algorithmic) definition of this property.

    Conversely, an important side benefit of stating facts using
    booleans is enabling some proof automation through computation
    with Coq terms, a technique known as _proof by reflection_.

    Consider the following statement: *)

Example even_1000 : Even 1000.

(** The most direct way to prove this is to give the value of [k]
    explicitly. *)

Proof. unfold Even. exists 500. reflexivity. Qed.

(** The proof of the corresponding boolean statement is even
    simpler (because we don't have to invent the witness: Coq's
    computation mechanism does it for us!). *)

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

(** What is interesting is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one without
    mentioning the value 500 explicitly: *)

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof-script
    size in this case, larger proofs can often be made considerably
    simpler by the use of reflection.  As an extreme example, a famous
    Coq proof of the even more famous _4-color theorem_ uses
    reflection to reduce the analysis of hundreds of different cases
    to a boolean computation. *)

(** Another notable difference is that the negation of a "boolean
    fact" is straightforward to state and prove: simply flip the
    expected boolean result. *)

Example not_even_1001 : even 1001 = false.
Proof.
  (* WORKED IN CLASS *)
  reflexivity.
Qed.

(** In contrast, propositional negation can be more difficult
    to work with directly. *)

Example not_even_1001' : ~(Even 1001).
Proof.
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

(** Equality provides a complementary example, where it is sometimes
    easier to work in the propositional world.

    Knowing that [(n =? m) = true] is generally of little direct help in
    the middle of a proof involving [n] and [m]; however, if we
    convert the statement to the equivalent form [n = m], we can
    rewrite with it. *)

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
    rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(** We won't discuss reflection any further for the moment, but it
    serves as a good example showing the complementary strengths of
    booleans and general propositions, and being able to cross back
    and forth between the boolean and propositional worlds will often
    be convenient in later chapters. *)

(** **** Exercise: 2 stars, standard (logical_connectives)

    The following theorems relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Theorem andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. split.
      (* TODO: Auto *)
    + rewrite andb_commutative in H.
      apply andb_true_elim2 in H. apply H.
    + apply andb_true_elim2 in H. apply H.
  - intros []. subst. reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. destruct b1.
    + left. reflexivity.
    + right. simpl in H. apply H.
  - intros [].
    + subst. reflexivity.
    + destruct b1; subst; reflexivity.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (eqb_neq)

    The following theorem is an alternate "negative" formulation of
    [eqb_eq] that is more convenient in certain situations.  (We'll see
    examples in later chapters.)  Hint: [not_true_iff_false]. *)

Check not_true_iff_false : forall b : bool,
  b <> true <-> b = false.

Search (?a =? ?b).

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. unfold not. split.
  - intros H1 H2.
    rewrite H2 in H1. rewrite eqb_refl in H1.
    discriminate.
  - intros H1.
    apply not_true_iff_false.
    unfold not. intros H2.
    apply eqb_eq in H2. apply H1 in H2.
    contradiction.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (eqb_list)

    Given a boolean operator [eqb] for testing equality of elements of
    some type [A], we can define a function [eqb_list] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [eqb_list] function below.  To make sure that your
    definition is correct, prove the lemma [eqb_list_true_iff]. *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | h1 :: t1, h2 :: t2 => eqb h1 h2 && eqb_list eqb t1 t2
  | [], [] => true
  | _, _ => false
  end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb eqb_H l1.
  induction l1 as [| h1 t1 IHt1].
  - intros [| h2 t2]; split;
      try repeat reflexivity;
      try repeat discriminate.
  - intros [| h2 t2].
    + split; discriminate.
    + simpl. destruct (eqb h1 h2) eqn:E; simpl; split.
      * intros H. apply IHt1 in H. apply eqb_H in E. subst. reflexivity.
      * apply eqb_H in E. subst. intros H. injection H. apply IHt1.
      * discriminate.
      * intros H. injection H as H _.
        apply eqb_H in H. rewrite H in E. discriminate.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (All_forallb)

    Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property defined above. *)

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l. induction l as [| h t]; split; simpl; intros.
  - apply I.
  - reflexivity.
  - apply andb_true_iff in H as []; split.
    + assumption.
    + apply IHt. assumption.
  - destruct H. apply andb_true_iff. split.
    + assumption.
    + apply IHt. assumption.
Qed.

(** (Ungraded thought question) Are there any important properties of
    the function [forallb] which are not captured by this
    specification? *)

(* Admitted. *)

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies to _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function. *)

(** However, if we happen to know that [P] is reflected in some
    boolean term [b], then knowing whether it holds or not is trivial:
    we just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m]. *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** It may seem strange that the general excluded middle is not
    available by default in Coq, since it is a standard feature of
    familiar logics like ZFC.  But there is a distinct advantage in
    not assuming the excluded middle: statements in Coq make stronger
    claims than the analogous statements in standard mathematics.
    Notably, when there is a Coq proof of [exists x, P x], it is
    always possible to explicitly exhibit a value of [x] for which we
    can prove [P x] -- in other words, every proof of existence is
    _constructive_. *)

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)

(** The following example illustrates why assuming the excluded middle
    may lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that
    [a ^ b] ([a] to the power [b]) is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.
    If [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b =
    sqrt 2] and we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is
    irrational.  In this case, we can take [a = sqrt 2 ^ sqrt 2] and
    [b = sqrt 2], since [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^
    2 = 2].  []

    Do you see what happened here?  We used the excluded middle to
    consider separately the cases where [sqrt 2 ^ sqrt 2] is rational
    and where it is not, without knowing which one actually holds!
    Because of that, we finish the proof knowing that such [a] and [b]
    exist but we cannot determine what their actual values are (at least,
    not from this line of argument).

    As useful as constructive logic is, it does have its limitations:
    There are many statements that can easily be proven in classical
    logic but that have only much more complicated constructive proofs, and
    there are some that are known to have no constructive proof at
    all!  Fortunately, like functional extensionality, the excluded
    middle is known to be compatible with Coq's logic, allowing us to
    add it safely as an axiom.  However, we will not need to do so
    here: the results that we cover can be developed entirely
    within constructive logic at negligible extra cost.

    It takes some practice to understand which proof techniques must
    be avoided in constructive reasoning, but arguments by
    contradiction, in particular, are infamous for leading to
    non-constructive proofs.  Here's a typical example: suppose that
    we want to show that there exists [x] with some property [P],
    i.e., such that [P x].  We start by assuming that our conclusion
    is false; that is, [~ exists x, P x]. From this premise, it is not
    hard to derive [forall x, ~ P x].  If we manage to show that this
    intermediate fact results in a contradiction, we arrive at an
    existence proof without ever exhibiting a value of [x] for which
    [P x] holds!

    The technical flaw here, from a constructive standpoint, is that
    we claimed to prove [exists x, P x] using a proof of
    [~ ~ (exists x, P x)].  Allowing ourselves to remove double
    negations from arbitrary statements is equivalent to assuming the
    excluded middle, as shown in one of the exercises below.  Thus,
    this line of reasoning cannot be encoded in Coq without assuming
    additional axioms. *)

(** **** Exercise: 3 stars, standard (excluded_middle_irrefutable)

    Proving the consistency of Coq with the general excluded middle
    axiom requires complicated reasoning that cannot be carried out
    within Coq itself.  However, the following theorem implies that it
    is always safe to assume a decidability axiom (i.e., an instance
    of excluded middle) for any _particular_ Prop [P].  Why?  Because
    we cannot prove the negation of such an axiom.  If we could, we
    would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)] (since [P]
    implies [~ ~ P], by lemma [double_neg], which we proved above),
    which would be a  contradiction.  But since we can't, it is safe
    to add [P \/ ~P] as an axiom.

    Succinctly: for any proposition P,
       [Coq is consistent ==> (Coq + P \/ ~P) is consistent].

    (Hint: You may need to come up with a clever assertion as the
    next step in the proof.) *)

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_exists_dist)

    It is a theorem of classical logic that the following two
    assertions are equivalent:

    ~ (exists x, ~ P x)
    forall x, P x

    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (classical_axioms)

    For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus [excluded_middle])
    are equivalent.

    Hint: Rather than considering all pairs of statements pairwise,
    prove a single circular chain of implications that connects them
    all. *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

(* FILL IN HERE

    [] *)

(* 2021-08-11 15:08 *)
