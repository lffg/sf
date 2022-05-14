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
