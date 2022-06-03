From LF Require Export Basics.

(*
 * PROOF BY INDUCTION
 *)

(* Let's recap the definition of `plus`... *)

Module plus_recap.
    Fixpoint plus (a b : nat) : nat :=
        match a with
        | O => b
        | S n' => S (plus n' b)
        end.

    Example test_plus'_1 : plus 2 3 = 5.
    Proof. reflexivity. Qed.
End plus_recap.

(* By that definition, the simplification of `plus` depends on the parameter
 * `a`. Let's try to prove the neutrality of `0` when it is passed on the left.
 *)

Theorem add_0_l : forall n : nat, 0 + n = n.
Proof.
    (* This simplification is quite trivial. Recall the definition. When applied
     * on the left, the zero will be simply pattern matched which will, in turn,
     * return the right-hand side argument (in our theorem, `n`).
     *)
    simpl.
    reflexivity.
Qed.

(* However, when the `0` is on the right, things aren't so simple. Not because
 * of the zero on the right-hand side, but because of `n` on the left side.
 *)

Theorem add_0_r_first_try : forall n : nat, n + 0 = n.
Proof.
    (* This simplification does nothing. Well, that's quite fair. How would you
     * simplify the expression `n + 0` by that `plus` definition? Since `n` is
     * arbitrary (i.e. `n` can be any of the natural numbers), it could be
     * `O` or even `S n'`, being `n'` another arbitrary natural number.
     *)
    simpl.
Abort.

(* We can not even use something like `destruct` to solve this problem since,
 * when destructing `n: nat`, we would get `S n'`, being `n'` another arbitrary
 * natural number. If we try to `destruct` again, we'd get `S (S n'')`, which
 * also didn't help much. The `match` definition can't be simplified.
 *
 * You can see some kind of “growing recursion” pattern here. Indeed, natural
 * numbers may be inductively defined!
 *
 * Hence, most proofs on inductively-defined types also need to be implemented
 * using induction, a more powerful reasoning technique.
 *
 * For example, if we want to prove some proposition `P(n)` for all natural
 * numbers, we may proceed with induction as follows:
 *
 *   - Show that `P(O)` holds;
 *   - Show that, for any `n'`, if `P(n')` holds, then so does `P(S n')`;
 *   - Conclude that `P(n)` holds for all `n: nat`.
 *
 * In Coq, we may use the `induction` tactic to break a goal involving some
 * `n: nat` into two sub-goals:
 *
 *   - One to show `P(O)`;
 *   - One to show `P(n') -> P(S n')`.
 *)

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
    intros n.
    (* The `induction` tactic will break `n + 0 = n` into two sub-goals:
     *   - `0 + 0 = 0`, the base case (`P(O)`);
     *   - `n' + 0 = n' -> S n' + 0 = S n'`, (`P(n') -> P(S n')`).
     *)
    induction n as [| n' IHn' (* Induction hypothesis for n' *)].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

(******************************************************************************)

(* Exercises *)

Theorem mul_0_r : forall n : nat,
  n * 0 = 0.
Proof.
    intros n.
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
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - rewrite -> add_0_r. reflexivity.
    - simpl. rewrite -> IHn'. rewrite ->  plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
    intros n m p.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

(* Consider the following function, which doubles its argument: *)

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(* Use induction to prove this simple fact about double: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

Check negb_involutive: forall b : bool, negb (negb b) = b.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - rewrite -> IHn'.
      simpl.
      rewrite -> negb_involutive.
      reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

(* Briefly explain the difference between the tactics `destruct` and
 * `induction`.
 *)

(* At first glance, both tactics appear similar. Indeed, both break an
 * inductively-defined type over two N sub-goals, one for each constructor.
 *
 * However, `destruct` simply “breaks” a variable over its constructors, doing
 * nothing more than that. Indeed, it may be useful to prove definitions that
 * “go up”.
 *
 * On the other hand, `induction` is more powerful since, besides breaking a
 * variable over its constructors, it also creates assumptions that facilitate
 * proving some property for all possible values of a given inductively-defined
 * type. In general it is useful to prove definitions that “go down”.
 *
 * I should note that I am not still 100% sure about that “up” and “down”
 * metaphors. I might amend or even remove them later.
 *)

Definition manual_grade_for_destruct_induction : option (nat * string) := None.

(******************************************************************************)

(*
 * PROOFS WITHIN PROOFS
 *)

(* Sometimes it is useful to create a “proof within a proof”. For example, it
 * may be desirable to not pollute the top-level environment with a name that
 * won't be reused in another place.
 *
 * In such cases, the `assert` tactic may be used. It essentially asserts a
 * named assertion and introduces two sub-goals. The first one that is used to
 * prove assertion. The second sub-goal being the original goal (i.e. the one
 * before the `assert`, but with the proven assertion on its context).
 *
 * The `assert` tactic can also be used as a technique to better specify where
 * the `replace` tactic should act on.
 *
 * One may also use the `replace` tactic as an alternative to the combination of
 * the `assert` and `rewrite` tactics. The former takes the following form:
 *
 *     replace (a) with (b).
 *
 * It will generate two sub-goals, a) the expression with (a) is in place of (b)
 * and (b) is in place of (a); and b) a goal where `a = b`.
 *)

Theorem plus_rearrange_first_try : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* Here we only want to rewrite `n + m` as `m + n`. However, `replace` is also
   * rewriting `p + q`, which is not desirable here.
   *)
  rewrite add_comm.
Abort.

(* So we may use `assert` to specify where the rewrite should take place. And
 * prove such assertion with the `add_comm` theorem. *)

 Theorem plus_rearrange : forall n m p q : nat,
 (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). {
    (* Here we prove the assertion. *)
    rewrite -> add_comm. reflexivity.
  }
  (* Here we prove the original goal with the given assertion in the context.*)
  rewrite -> H.
  reflexivity.
Qed.

(******************************************************************************)

(*
 * MORE EXERCISES
 *)

(******************************************************************************)

(* Exercises *)

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  do 2 (rewrite -> add_assoc).
  assert (H: n + m = m + n). { rewrite -> add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

(* Helper *)
Theorem mul_n_0 : forall n : nat, n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Helper *)
Theorem mul_n_Sm : forall n m : nat,
  n * (S m) = n + n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> add_shuffle3. reflexivity.
Qed.

Theorem mul_comm : forall n m : nat,
  n * m = m * n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite -> mul_n_0. reflexivity.
  - simpl. rewrite -> mul_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

(******************************************************************************)

(* Exercises *)

Check leb: nat -> nat -> bool.

(* Guess: Induction; equal comparison is at the bottom, ref. “go down”. *)
Theorem leb_refl : forall n : nat,
  (n <=? n) = true.
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Guess: Simplification; this case is covered in the def. with “depth 1”. *)
Theorem zero_neqb_S : forall n : nat,
  0 =? (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* Guess: Case analysis; since first argument is matched first. *)
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(* Guess: Simplification and rewriting; since has assumption. *)
Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H.
  induction p as [| n' IHn'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed. (* Wrong guess. *)

(* Guess: Simplification; this case is covered in the def. with “depth 1”. *)
Theorem S_neqb_0 : forall n : nat,
  (S n) =? 0 = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* Guess: Induction; `n` (on the right) won't match with “depth 1”. *)
Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros n. simpl.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Guess: Case analysis; bool is not really a inductively-defined type. *)
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(* Guess: Induction. *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> add_assoc. reflexivity.
Qed.

(* Guess: Induction. *)
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  do 2 (rewrite -> add_assoc).
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite -> add_comm. reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

(* Taken from `Basics.v`, repeated for convenience. *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

(* Taken from `Basics.v`, repeated for convenience. *)
Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

(* Taken from `Basics.v`, repeated for convenience. *)
Fixpoint decr (m : bin) : bin :=
  match m with
  | Z => Z
  | B0 m' => B1 (decr m')
  | B1 Z => Z
  | B1 m' => B0 m'
  end.

(* Taken from `Basics.v`, repeated for convenience. *)
Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => 0
  | B0 m' => 2 * (bin_to_nat m')
  | B1 m' => 1 + 2 * (bin_to_nat m')
  end.

(* Theorem bin_to_nat_pres_incr : forall b : bin,
  S (bin_to_nat b) = bin_to_nat (incr b).
Proof.
  intros b.
  induction b as [| b0' IHb0' | b1' IHb1'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHb1'.
    simpl.
    rewrite plus_n_Sm.
    reflexivity. *)
