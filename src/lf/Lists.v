From LF Require Export Induction.

Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
  | (x, _) => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | (_, x) => x
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Example fst_test: (fst (3, 5)) = 3.
Proof. simpl. reflexivity. Qed.

Theorem surjective_pairing' : forall (n m : nat),
  (n, m) = (fst (n, m), snd (n, m)).
Proof.
  simpl.
  reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* Exercise *)

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(******************************************************************************)

(* To introduce the concept of a list, one may generalize the idea of pairs in
 * which a list is either the empty list or a pair of an element with another
 * list (which could be empty, of course).
 *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(* A list with 3 elements: *)
Definition my_list := cons 1 (cons 2 (cons 3 nil)).

(* Lower `level`s bind tighter. *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => []
  | S count' => n :: repeat n count'
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | [] => 0
  | h :: t => 1 + length t
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h :: t => h :: app t l2
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1: [1; 2; 3] ++ [4; 5] = [1; 2; 3; 4; 5].
Proof. reflexivity. Qed.
Example test_app2: [] ++ [4; 5] = [4; 5].
Proof. reflexivity. Qed.
Example test_app3: [1; 2; 3] ++ [] = [1; 2; 3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | [] => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => t
  end.

Example test_hd1: hd 0 [1; 2; 3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1; 2; 3] = [2; 3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => match h with
              | 0 => nonzeros t
              | n => n :: nonzeros t
              end
  end.

Example test_nonzeros: nonzeros [0; 1; 0; 2; 3; 0; 0] = [1; 2; 3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => if odd h
                then h :: oddmembers t
                else oddmembers t
  end.

Example test_oddmembers: oddmembers [0; 1; 0; 2; 3; 0; 0] = [1; 3].
Proof. reflexivity. Qed.

Definition countoddmembers (l : natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1; 0; 3; 1; 4; 5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0; 2; 4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

(******************************************************************************)

(* Exercise *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end.

(******************************************************************************)

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => 0
  | h :: t => let r := count v t in
                if h =? v then 1 + r else r
  end.

Example test_count1: count 1 [1; 2; 3; 1; 4; 1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1; 2; 3; 1; 4; 1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1; 2; 3] [1; 4; 1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1; 4; 1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1; 4; 1]) = 0.
Proof. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  negb (count v s =? 0).

Example test_member1: member 1 [1; 4; 1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1; 4; 1] = false.
Proof. reflexivity. Qed.

Fixpoint member' (v : nat) (s : bag) : bool :=
  match s with
  | [] => false
  | h :: t => if h =? v then true else member' v t
  end.

Example test_member'1: member' 1 [1; 4; 1] = true.
Proof. reflexivity. Qed.
Example test_member'2: member' 2 [1; 4; 1] = false.
Proof. reflexivity. Qed.

(******************************************************************************)

(* Exercises *)

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | h :: t => if h =? v
                then t
                else (h :: remove_one v t)
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2; 1; 5; 4; 1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2; 1; 4; 1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2; 1; 4; 5; 1; 4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2; 1; 5; 4; 5; 1; 4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | h :: t => let r := remove_all v t in
                if h =? v then r else h :: r
  end.


Example test_remove_all1:
  count 5 (remove_all 5 [2; 1; 5; 4; 1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2:
  count 5 (remove_all 5 [2; 1; 4; 1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:
  count 4 (remove_all 5 [2; 1; 4; 5; 1; 4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:
  count 5 (remove_all 5 [2; 1; 5; 4; 5; 1; 4; 5; 1; 4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1 s2 : bag) : bool :=
  match s1 with
  | [] => true
  | x :: s1' => member x s2 && subset s1' (remove_one x s2)
  end.

Example test_subset1: subset [1; 2] [2; 1; 4; 1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1; 2; 2] [2; 1; 4; 1] = false.
Proof. reflexivity. Qed.

(******************************************************************************)

(* Exercise *)

Theorem bag_add_theorem : forall (v : nat) (b : bag),
  count v (add v b) = S (count v b).
Proof.
  intros v b.
  simpl.
  rewrite eqb_refl.
  reflexivity.
Qed.

(******************************************************************************)

(* Example of a proof on a list that can be solved using just simplification. *)
Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. simpl. reflexivity. Qed.

(* Simplification was enough since `[]` was present in one of the app's pattern
 * match branches.
 *)

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [| n l'].
  - reflexivity.
  - reflexivity.
Qed.

(* Most interesting proofs on lists, however, can only be solved using
 * induction, just like with natural numbers.
 *)

(* Using induction to prove facts about lists is pretty much the same as that of
 * numbers.
 *
 * Inductively defined types declare a set of constructors, which are used to
 * build a value of such type. Notice that, if one applies some constructor to a
 * value of that constructor's type, one then has an inductively defined type.
 *
 * This fact raises a new way of thinking about inductively defined types. In
 * the cases where the constructor is applied to another value of such type,
 * the “inner” value can always be thought as of a “smaller” value if compared
 * to the “outer” value.
 *
 * For example, in the list `cons 1 (cons 2 nil)`, the “inner” list,
 * `cons 2 nil` is smaller than the “outer” list.
 *
 * Hence, wanting to prove some proposition `P` for all lists using induction,
 * one must:
 *
 *   - Show that `P` is valid for `nil`;
 *   - Show that `P` is valid for `cons n l'`, assuming that `P` holds for the
 *     smaller list `l'`.
 *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: l' => rev l' ++ [h]
  end.

Example test_rev1: rev [1; 2; 3] = [3; 2; 1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl.
    (* `rev l` is itself a list, so we are able to use the above lemma. *)
    rewrite -> app_length.
    simpl. rewrite -> IHl'.
    rewrite add_comm. reflexivity.
Qed.

(******************************************************************************)

(* Exercises *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  (* Since the definition of `app` pattern matches the first operator, this
   * cannot be trivially proven using simplification. *)
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  (* `l1` in `app` is arbitrary, so induction is one's last resort after
   * unsuccessful simplification or case analysis. *)
  induction l1 as [| n l1' IHl1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
    (* The definition or `rev` for `[]` is trivial. *)
  - reflexivity.
  - simpl. rewrite rev_app_distr.
    (* Step by step of `rev [n]` simplification, just to be explicit. *)
    simpl rev. simpl app.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  do 2 (rewrite app_assoc). reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - destruct n.
    + simpl. rewrite IHl1'. reflexivity.
    + simpl. rewrite IHl1'. reflexivity.
Qed.

(******************************************************************************)

(* Exercises *)

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], []             => true
  | h1 :: t1, h2 :: t2 => (h1 =? h2) && eqblist t1 t2
  | _, _               => false
  end.

Example test_eqblist1: (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2: eqblist [1; 2; 3] [1; 2; 3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3: eqblist [1; 2; 3] [1; 2; 4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall (l : natlist),
  true = eqblist l l.
Proof.
  intros l.
  (* Since `l` is arbitrary, one must use induction. *)
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. rewrite eqb_refl. reflexivity.
Qed.

(******************************************************************************)

(* Exercises *)

Theorem count_member_nonzero: forall s : bag,
  1 <=? (count 1 (1 :: s)) = true.
Proof.
intros s. induction s as [|h t IHs'].
- reflexivity.
- simpl count. simpl leb. reflexivity.
Qed.

Theorem leb_n_Sn : forall n : nat,
  n <=? S n = true.
Proof.
  intros n.
  (* `n` is arbitrary, `leb` can't *)
  induction n as [| n' IHn'].
    (* `0 <=? 1` has a match arm, `O, n => true`. *)
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s.
  induction s as [| n s' IHs'].
  - reflexivity.
  - destruct n as [| n'].
    + simpl. rewrite leb_n_Sn. reflexivity.
    + simpl. rewrite IHs'. reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

(* Write down an interesting theorem bag_count_sum about bags involving the
 * functions count and sum, and prove it using Coq. (You may find that the
 * difficulty of the proof depends on how you defined count! Hint: If you
 * defined count using =? you may find it useful to know that destruct works on
 * arbitrary expressions, not just simple identifiers.
 *)

Theorem bag_count_sum : forall (x : nat) (b1 b2 : bag),
  count x (sum b1 b2) = count x b1 + count x b2.
Proof.
  intros x b1 b2.
  induction b1 as [| n b1' IHb1'].
  - reflexivity.
  - simpl.
    (* Destruct `n =? x` for all constructors of `bool` (which is the type of
     * that expression. *)
    destruct (n =? x) eqn:E.
    + rewrite IHb1'. reflexivity.
    + rewrite IHb1'. reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

(******************************************************************************)

(*
 * OPTIONS
 *)

(* This is bad since the caller must always provide a default value. *)
Fixpoint nth_bad (default : nat) (l : natlist) (n : nat) : nat :=
  match l with
  | [] => default
  | h :: t => match n with
              | 0 => h
              | S n' => nth_bad default t n'
              end
  end.

(* Another option is to use some type to encode the absence of a value. *)
Inductive natoption : Type :=
  | None
  | Some (n : nat).

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
  | [] => None
  | h :: t => match n with
              | 0 => Some h
              | S n' => nth_error t n'
              end
  end.

Example test_nth_error1: nth_error [4; 5; 6; 7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2: nth_error [4; 5; 6; 7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3: nth_error [4; 5; 6; 7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n => n
  | None => d
  end.

(******************************************************************************)

End NatList.
