Set Warnings "-notation-overridden".

From LF Require Export Poly.

(*
 * THE `apply` TACTIC
 *)

(* When the goal is the same as a hypothesis or a previously proven lemma, the
 * `apply` tactic may be used.
 *)

Theorem silly1 : forall (n m : nat),
  n = m -> n = m.
Proof.
  intros n m Eq. apply Eq.
Qed.

(* Of course one could have used `rewrite eq. reflexivity.`, but `apply` is a
 * little terser. *)

(* `apply` also works with conditional hypothesis and lemmas.
 * When applying an implication, its premises will be added to the list of
 * sub-goals.
 *)

Theorem silly2 : forall (n m o p : nat),
  n = m ->
    (n = m -> [n; o] = [m; p]) ->
      [n; o] = [m; p].
Proof.
  intros n m o p Eq1 Eq2.
  (* Since `Eq2` is an implication, its premise `n = m` will added. *)
  apply Eq2.
  apply Eq1.
Qed.

(* When `apply H` is used, if `H` has some universally quantified variables, Coq
 * will try to match the `H` variables to the variables in the current context.
 *)

Theorem silly2a : forall (n m : nat),
  (n, n) = (m, m) ->
    (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
      [n] = [m].
Proof.
  intros n m Eq1 Eq2.
  (* `q` in `Eq2` gets instantiated with `n`, and `r`, with `m`. *)
  apply Eq2.
  apply Eq1.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
    (forall n, even n = false -> odd n = true) ->
      even p = true ->
        odd (S p) = true.
Proof.
  intros p Eq1 Eq2 Eq3.
  apply Eq2.
  apply Eq1.
  apply Eq3.
Qed.

(******************************************************************************)

(* Apply can only be used when there is a match.
 *)

Theorem silly3 : forall (n m : nat),
  n = m -> m = n.
Proof.
  intros n m H.
  Fail apply H.
  symmetry.
  apply H.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  symmetry. apply rev_involutive.
Qed.

(******************************************************************************)

(* Exercise *)

(* Briefly explain the difference between the tactics apply and rewrite. What
 * are the situations where both can usefully be applied?
 *)

(* `apply` should be used when one have matching expressions. It also finishes
 * the current goal. `rewrite` doesn't need matching expressions and won't
 * finish the goal.
 *)

(******************************************************************************)

(*
 * THE `apply with` TACTIC
 *)

(* Two rewrites in a row... *)
Example trans_eq_example : forall (a b c d e f : nat),
  [a; b] = [c; d] ->
  [c; d] = [e; f] ->
  [a; b] = [e; f].
Proof.
  intros a b c d e f Eq1 Eq2.
  rewrite Eq1.
  rewrite Eq2.
  reflexivity.
Qed.

(* Is a common pattern. So a lemma should state that equality is transitive. *)

Lemma trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o Eq1 Eq2.
  rewrite Eq1.
  apply Eq2.
Qed.

(* Now one may use `trans_eq` to prove the previous example. *)
Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f Eq1 Eq2.
  (* `apply trans_eq` would instantiate `X` (in `trans_eq`) with `[nat]`,
   * `n` with `[a; b]` and `o` with `[c; d]`. But what about `m`?
   *
   * “Unable to find an instance for the variable `m`.” *)
  Fail apply trans_eq.
  (* In such cases, `apply with` should be used. *)
  apply trans_eq with (m := [c; d]).
  (* Or just `apply trans_eq with [c; d].` *)
  (* And, just like `apply`, all `premises` are added as sub-goals. *)
  apply Eq1.
  apply Eq2.
Qed.

(* Coq has the `transitivity` tactic, which serves the same purpose as
 * `trans_eq`.
 *)

Example trans_eq_example'' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f Eq1 Eq2.
  transitivity [c; d].
  apply Eq1. apply Eq2.
Qed.

(******************************************************************************)

(* Exercise *)

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p Eq1 Eq2.
  transitivity m.
  apply Eq2.
  apply Eq1.
Qed.

(******************************************************************************)

(*
 * THE `injection` AND `discriminate` TACTICS
 *)

(* Recall the definition of natural numbers:
 *)

Module NatDefRecall.
  Inductive nat : Type :=
    | O
    | S (n : nat).
End NatDefRecall.

(* By that definition, it's evident that natural numbers can have one of two
 * forms. Either `O` or `S n`. There is more to it, though.
 *
 *  - The constructor `S` is injective (or one-to-one).
 *    Meaning that, if `S n = S m`, then `n = m`. Or, if `n != m`, then
 *      `S n != S m`.
 *    Every element of the function's codomain is the image of at most one
 *      element of its domain. In this case, every natural number is the
 *      successor of only one other natural number.
 *
 *  - The constructors `S` and `O` are disjoint.
 *    Meaning that, for every `n`, `S n` is not equal to `O`.
 *
 * Similar principles do apply for every inductively defined type. All
 * constructors are injective, and values built from distinct constructors are
 * never equal (different constructors are disjoint).
 *)

(* One may prove the injectivity of `S` by using the `Nat.prev` function: *)
Theorem S_injective : forall (n m :nat),
  S n = S m -> n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2.
  rewrite H1.
  simpl.
  reflexivity.
Qed.

(* Such technique can be generalized for any constructor by writing the
 * equivalent of `prev`.
 *
 * That's not always convenient, though. As such, Coq provides the `injection`
 * tactic, which lets one exploit the injectivity of any constructor.
 *)

Theorem S_injective' : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  (* By writing `injection H`, Coq will generate all equations using the
   * constructor's injectivity. In the case of `S n = S m`, Coq will generate
   * the `n = m` equation. *)
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> n = m.
Proof.
  intros n m o H.
  (* Injection can derive multiple equations at once. In this case, from the
   * hypothesis `H`, it can derive `n = o` and `m = o`. *)
  injection H as H1 H2.
  rewrite H1. rewrite H2.
  reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  (* [x, y, ...l] = [z, ...j] *)
  x :: y :: l = z :: j ->
  (* [...j] = [z, ...l] *)
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H1.
  rewrite H2.
  intros H3 H4.
  rewrite H4.
  injection H3 as H5.
  symmetry. apply H5.
Qed.

(******************************************************************************)

(* The principle of disjointness says that two terms constructed using different
 * constructors can never be equal.
 *
 * Hence, anytime one finds oneself in a context where it's assumed that two
 * terms with different constructors are equal, one may conclude anything since
 * the assumption is absurd.
 *
 * The `discriminate` tactic encodes such principle. It's used on a hypothesis
 * involving an (absurd) equality between different constructors. Since the
 * hypothesis is absurd, it finishes the current goal.
 *)

Theorem discriminate_ex1 : forall (n m : nat),
  false = true -> n = m.
Proof.
  intros n m contra.
  discriminate contra.
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

(* Those are examples of the logical principle of explosion, which asserts that
 * a contradictory hypothesis entails anything.
 *
 * Such proofs do not show that the conclusion holds. They just assert that,
 * in an absurd universe where such invalid premise arise, any absurd
 * conclusion could also be derived from it (because in such inconsistent
 * universe, every statement can absurdly be true).
 *)

Example discriminate_ex3:
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] -> x = z.
Proof.
  intros X x y z l j contra.
  discriminate contra.
Qed.

(* `discriminate` can also be used to reason about `=?` on natural numbers. *)
Theorem eqb_0_1 : forall n,
  0 =? n = true -> n = 0.
Proof.
  intros n H.
  destruct n as [| n'].
  - reflexivity.
  - discriminate H.
Qed.

(* The injectivity of constructors allows one to reason that:
 *
 *     forall (n m : nat), S n = S m -> n = m.
 *
 * The reciprocal of this implication:
 *
 *     forall (n m : nat), n = m -> S n = S m.
 *
 * Is an instance of a more general fact about both constructors and functions.
 * For example...
 *)

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros A B f x y Eq.
  rewrite Eq.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m Eq.
  rewrite Eq.
  reflexivity.
Qed.

(* Since it's quite general, Coq provides the `f_equal` tactic.
 * Given a goal in the form:
 *
 *     f a1 ... an = g b1 ... bn
 *
 * `f_equal` will produce sub-goals in the form:
 *
 *     - f = g
 *     - a1 = b1
 *     - (...)
 *     - an = bn
 *
 * Any trivial (i.e. provable using `reflexivity`) sub-goals will be
 * automatically discharged.
 *)

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m H.
  (* Current goal is in the form `S n = S m`, so Coq will generate the sub-goals
   * `S = S` (trivial) and `n = m`. *)
  f_equal.
  apply H.
Qed.

(******************************************************************************)

(*
 * USING TACTICS ON HYPOTHESES
 *)

(* By default, most tactics work on the goal formula, leaving the context
 * untouched. Most tactics, however, also have a variant that performs the
 * operation on a statement in the context.
 *
 *  - `simpl.` will operate on the current goal.
 *  - `simpl in H.` will operate on the `H` statement in the context.
 *)

Theorem S_inj : forall (n m : nat) (b : bool),
  (S n =? S m) = b ->
  (n =? m) = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

(* `apply L in H` matches some conditional statement `L` (of the form `X -> Y`)
 * against a hypothesis `H` in the context.
 *
 * Unlike “ordinary” `apply` (which rewrites a goal matching `Y` into a sub-goal
 * `X`), `apply L in H` matches `H` against `X` and, if successful, replaces it
 * with `Y`.
 *
 * `apply L in H` gives a form of “forward reasoning”, while `apply L` gives
 * a form of “backwards reasoning”.
 *)

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros n m p q Eq H.
  symmetry in H.
  apply Eq in H.
  symmetry in H.
  apply H.
Qed.

(* Forward reasoning starts from what is given (premises, previously proven
 * theorems) and iteratively draws conclusions from them until the goal is
 * reached.
 *
 * Backwards reasoning starts from the goal and iteratively reasons about what
 * would imply the goal, until premises or previously proven theorems are
 * reached.
 *)

(******************************************************************************)

(*
 * VARYING THE INDUCTION HYPOTHESIS
 *)

(* When carrying out a inductive proof, sometimes one need to be careful about
 * the assumptions are moved from the goal into the context. The order does
 * matter.
 *
 * The problem is that when the two variables are introduced before the
 * induction tactic, then the induction hypothesis would encompass all possible
 * values of the first variable (since it was the “induction argument”) but only
 * a specific value of the second variable (since it was introduced before the
 * `induction` tactic).
 *
 * One must be general, meaning prove the fact for all two variables. As such,
 * one must introduce the second variable after the induction tactic.
 *)

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  (* Since `m` won't be introduced here, it won't be particular. Rather, it
   * will be general (i.e. all `m`). *)
  intros n.
  (* Now the goals are general, i.e. they assert for all `m`. *)
  induction n as [| n' IHn'].
  - simpl. intros m Eq.
    (* Now `m` is particular. *)
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate Eq.
  - intros m Eq.
    destruct m as [| m'] eqn:E.
    + discriminate Eq.
    + f_equal.
      apply IHn'.
      injection Eq as goal.
      apply goal.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m Eq.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate Eq.
  - intros m Eq.
    destruct m as [| m'] eqn:E.
    + discriminate Eq.
    + f_equal.
      apply IHn'.
      simpl in Eq.
      apply Eq.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m Eq.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate Eq.
  - intros m Eq.
    destruct m as [| m'] eqn:E.
    + discriminate Eq.
    + f_equal.
      apply IHn'.
      do 2 (rewrite <- plus_n_Sm in Eq).
      simpl in Eq.
      injection Eq as goal.
      apply goal.
Qed.

(******************************************************************************)

(*
 * `generalize dependent`
 *)

(* Doing fewer `intros` before `induction` doesn't always work. When one wants
 * to use `induction` over a universally quantified variable Y that appears
 * before a variable X, one must introduce X before Y. The problem with this is
 * that X will be too specific in Y's induction hypothesis.
 *
 * To solve this, one needs to introduce all variables and then selectively
 * generalize some of them out of the proof context. The `generalize dependent`
 * tactic may be used to do so.
 *)

Theorem double_injective_take2 : forall n m,
  double n = double m -> n = m.
Proof.
  (* Since one will use induction over `m`, one must introduce `n` first. *)
  intros n m.
  (* Now one must generalize `n`, putting it back to the goal. *)
  generalize dependent n.
  induction m as [| m' IHm'].
  - simpl. intros n Eq.
    destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate Eq.
  - intros n Eq.
    destruct n as [| n'] eqn:E.
    + discriminate Eq.
    + f_equal.
      apply IHm'.
      injection Eq as goal.
      apply goal.
Qed.

(******************************************************************************)

(* Exercise *)

(* Prove this by induction on l. *)

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h' t' IHt'].
  - reflexivity.
  - intros n Eq.
    destruct n as [| n'] eqn:E.
    + discriminate.
    + simpl.
      apply IHt'.
      injection Eq as goal. apply goal.
Qed.

(******************************************************************************)

(*
 * UNFOLDING DEFINITIONS
 *)

Definition square n := n * n.

Lemma square_mult : forall n m,
  square (n * m) = square n * square m.
Proof.
  intros n m.
  (* `simpl` doesn't do anything here. *)
  simpl.
  (* So one must unfold `square`'s definition to manipulate its expression. *)
  unfold square.
  rewrite mult_assoc.
  assert (H: n * m * n = n * n * m).
  - rewrite mul_comm.
    (* `n * (m * p) = n * m * p` *)
    apply mult_assoc.
  - rewrite H.
    rewrite mult_assoc.
    reflexivity.
Qed.

Definition foo (x : nat) := 5.

(* Tactics like `simpl`, `reflexivity` and `apply` will automatically unfold
 * definitions of functions when progress is possible after the simplification.
 *)

Fact silly_fact_1 : forall m,
  foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  (* Will simplify `foo <expr>` to `5`. *)
  simpl.
  reflexivity.
Qed.

(* But automatically unfolding is often conservative... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(* Using `bar` definition, an analogous proof would fail. *)

Fact silly_fact_2_FAILED : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  (* Won't do nothing. *)
  simpl.
Abort.

(* The previous simplification doesn't do anything since, while trying to
 * simplify `bar`, Coq reaches a match in which the scrutinee is a variable
 * (which could be “anything”).
 *)

(* One option to simplify it is to break `m` over its possible constructors. *)
Fact silly_fact_2 : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m as [| m'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Another option is to directly unfold `bar`, which better shows that the
 * problem in the simplification lies in the match scrutinee. *)
Fact silly_fact_2' : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m as [| m'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(******************************************************************************)

(*
 * USING `destruct` ON COMPOUND EXPRESSIONS
 *)

(* The `destruct` tactic can be used to perform case analysis on arbitrary
 * computations. If `e` is an expression whose type is inductively defined,
 * `destruct e` will generate all possible sub-goals.
 *)

Definition silly_fun (n : nat) : bool :=
  if n =? 3
    then false
    else if n =? 5
      then false
      else false.

Theorem silly_fun_false : forall (n : nat),
  silly_fun n = false.
Proof.
  intros n. unfold silly_fun.
  (* Here one is stuck over if `n =? 3` is true or not. Since both cases are
   * possible, one can use destruct to reason about the two cases. *)
  destruct (n =? 3).
  - reflexivity.
  (* Same with `if n =? 5`. *)
  - destruct (n =? 5).
    + reflexivity.
    + reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

(* Both `split` and `combine` were defined in `Poly.v`.
 * Prove that `split` and `combine` are inverses in the following sense.
 *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h' t' IHt'].
  - intros l1 l2 Eq.
    injection Eq as Eq1 Eq2.
    rewrite <- Eq1. rewrite <- Eq2.
    reflexivity.
  - intros l1 l2.
    simpl.
    destruct h' as (x, y).
    destruct (split t') as [lx ly].
    intros Eq.
    injection Eq as Eq1 Eq2.
    rewrite <- Eq1. rewrite <- Eq2.
    simpl.
    f_equal.
    apply IHt'.
    reflexivity.
Qed.

(******************************************************************************)

(* Most of the time, `eqn:E` is optional in `destruct` uses. However, when
 * destructing compound statements, there are times when `eqn:E` is essential to
 * preserve context information, without which finishing the proof becomes
 * impossible.
 *)

Definition silly_fun1 (n : nat) : bool :=
  if n =? 3
    then true
    else if n =? 5
      then true
      else false.

Theorem silly_fun1_odd_FAILED : forall (n : nat),
  silly_fun1 n = true -> odd n = true.
Proof.
  intros n Eq.
  unfold silly_fun1 in Eq.
  destruct (n =? 3).
  (* One can't progress any further. There is not enough information.*)
Abort.

Theorem silly_fun1_odd : forall (n : nat),
  silly_fun1 n = true -> odd n = true.
Proof.
  intros n Eq.
  unfold silly_fun1 in Eq.
  (* By using `eqn:E`, one saves the information that `n = 3` in the context,
   * which latter will be used to prove that `odd n` is true, as `n` is 3. *)
  destruct (n =? 3) eqn:Eh3.
  - apply eqb_true in Eh3.
    rewrite Eh3.
    reflexivity.
  (* Same here. *)
  - destruct (n =? 5) eqn:Eh5.
    + apply eqb_true in Eh5.
      rewrite Eh5.
      reflexivity.
    + discriminate Eq.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem bool_fn_applied_thrice:
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn:Eb.
  - destruct (f true) eqn:Et.
    + rewrite Et. apply Et.
    + destruct (f false) eqn:Ef.
      * apply Et.
      * apply Ef.
  - destruct (f false) eqn:Ef.
    + destruct (f true) eqn:Et.
      * apply Et.
      * apply Ef.
    + rewrite Ef. apply Ef.
Qed.

(******************************************************************************)

(* Exercise *)

Search (?a =? ?b).

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m.
    destruct m as [| m'].
    + reflexivity.
    + reflexivity.
  - intros m.
    destruct m as [| m'].
    + reflexivity.
    + simpl. apply IHn'.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p Eq1 Eq2.
  apply eqb_true in Eq1.
  apply eqb_true in Eq2.
  rewrite Eq1. rewrite Eq2.
  apply eqb_refl.
Qed.

(******************************************************************************)

(* Exercise *)

(* We proved, in an exercise above, that for all lists of pairs, combine is the
 * inverse of split. How would you formalize the statement that split is the
 * inverse of combine? When is this property true?
 *
 * Complete the definition of split_combine_statement below with a property that
 * states that split is the inverse of combine. Then, prove that the property
 * holds. (Be sure to leave your induction hypothesis general by not doing
 * intros on more things than necessary. Hint: what property do you need of l1
 * and l2 for split (combine l1 l2) = (l1,l2) to be true?)
 *)

(* combine [a b c] [1 2 3 4 5] = [(a, 1) (b 2) (c 3)]
 * So, split [(a, 1) (b 2) (c 3)] = l1 l2, and l2 != [1 2 3 4 5]
 *
 * So initial l1 must be equal in length to initial l2.
 *
 * Previous definition:
 *
 *     forall X Y (l : list (X * Y)) l1 l2,
 *       split l = (l1, l2) -> combine l1 l2 = l.
 *)

Definition split_combine_statement : Prop :=
  forall X Y (l1 : list X) (l2 : list Y),
  length(l1) = length(l2) -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l1.
  induction l1 as [| hl1' tl1' IHtl1'].
  - intros l2 H_len.
    destruct l2 as [| hl2' tl2'] eqn:El2.
    + reflexivity.
    + simpl. discriminate H_len.
  - intros l2 H_len.
    destruct l2 as [| hl2' tl2'] eqn:El2.
    + simpl. discriminate H_len.
    + simpl. rewrite IHtl1'.
      * reflexivity.
      * simpl in H_len. injection H_len as goal. apply goal.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem filter_exercise :
  forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l.
  induction l as [| lh lt IHlt].
  - discriminate.
  - simpl filter. destruct (test lh) eqn:Et.
    + intros lf H.
      injection H as H1 H2. rewrite <- H1.
      apply Et.
    + apply IHlt.
Qed.

(******************************************************************************)

(* Exercise *)

(* Define two recursive Fixpoints, forallb and existsb. The first checks whether
 * every element in a list satisfies a given predicate.
 *
 * The second checks whether there exists an element in the list that satisfies
 * a given predicate.
 *)

Fixpoint forallb {X : Type} (pred : X -> bool) (l : list X) :=
  match l with
  | [] => true
  | h :: t => pred h && forallb pred t
  end.

Example test_forallb_1 : forallb odd [1; 3; 5; 7; 9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false; false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0; 2; 4; 5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (pred : X -> bool) (l : list X) :=
  match l with
  | [] => false
  | h :: t => pred h || existsb pred t
  end.

Example test_existsb_1 : existsb (eqb 5) [0; 2; 3; 6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true; true; false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1; 0; 0; 0; 0; 3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

(* Next, define a non-recursive version of existsb -- call it existsb' -- using
 * forallb and negb.
 *)

Definition existsb' {X : Type} (pred : X -> bool) (l : list X) :=
  negb (forallb (fun x => negb (pred x)) l).

(* Finally, prove a theorem existsb_existsb' stating that existsb' and existsb
 * have the same behavior.
 *)

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [| lh lt IHlt].
  - reflexivity.
  - unfold existsb'.
    simpl. destruct (test lh).
    + reflexivity.
    + rewrite IHlt. reflexivity.
Qed.

