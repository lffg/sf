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
  | h :: t => (if h =? v then 1 else 0) + count v t
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
