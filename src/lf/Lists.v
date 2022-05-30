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

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end.
