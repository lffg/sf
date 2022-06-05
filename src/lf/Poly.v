Set Warnings "-notation-overridden".

From LF Require Export Lists.

(*
 * POLYMORPHISM
 *)

(* One doesn't want to define a new list type for every possible element a list
 * could have. For example, the following is non-ideal. *)
Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(* To avoid this kind of repetition, Coq supports polymorphic inductive type
 * definitions.
 *)

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(* With that kind of definition, instead of using the type `natlist`, one could
 * use `list nat`.
 *
 * But this raises the question: what is `list` itself? One could say that
 * `list` is a function from `Type` to `Type`. Meaning that, for every type `X`,
 * `list X` is the inductively defined set of lists (nil and cons ...) whose
 * elements are of type `X`.
 *)

Check list : Type -> Type.

(* The `X` in the definition of `list` automatically becomes a parameter to the
 * constructors as well.
 *
 * The constructors are also, in fact, polymorphic.
 *)

Check nil nat : list nat.
Check cons nat 3 (nil nat) : list nat.

Check nil : forall (X : Type), list X.
Check cons : forall (X : Type), X -> list X -> list X.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1: repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
Example test_repeat2: repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

(* Though, for the sake of clarity, it is better to explicitly annotate the
 * types in a definition, Coq is indeed able to infer most of types. *)
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat': forall (X : Type), X -> nat -> list X.
Check repeat : forall (X : Type), X -> nat -> list X.

(* When using a polymorphic function, one must explicitly pass the type
 * parameters, which can be cumbersome. In such cases, one can use a hole (`_`)
 * to tell Coq to infer the concrete type.
 *
 * To to this kind of inference, Coq attempts to unify all information available
 * in that region: the type of the function being applied, the types of its
 * arguments and what type is expected in the hole's position.
 *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(* However, the hole notation is still quite verbose at times. One can avoid
 * them by telling Coq always to infer some function's parameter.
 *
 * The `Arguments` directive specifies the name of a function and a list of the
 * leading arguments to be treated as implicit.
 *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

(* To declare a parameter explicit in the function's definition, such parameter
 * can be enclosed in curly braces. *)
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

(* Though one should always use the latter option to make a parameter implicit
 * right from the definition, one should still use the `Arguments` directive to
 * turn the constructor's parameters implicit since specifying the parameter of
 * the inductive type itself is usually the best thing to do. I.e., it's good
 * to be able to discriminate `list int` from `list bool`.
 *)

(* When Coq doesn't have enough information to automatically determine the
 * implicit type parameter, one can always explicitly annotate the expr. *)
Definition nat_nil: list nat := nil.

(* Alternatively, one can force explicit arguments by prefixing the function
 * name with `@`. *)
Definition nat_nil' := @nil nat.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h l1' => cons h (app l1' l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length t)
  end.

Example test_rev1: rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2: rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

(******************************************************************************)

(* Exercises *)

Theorem app_nil_r : forall (X : Type) (l : list X),
  l ++ [] = l.
Proof.
  intros T l.
  induction l as [| h l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc : forall (A : Type) (l1 l2 l3 : list A),
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  intros T l1 l2 l3.
  induction l1 as [| h l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros T l1 l2.
  induction l1 as [| h l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

(******************************************************************************)

(* Exercises *)

Theorem rev_app_distr: forall (X : Type) (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros T l1 l2.
  induction l1 as [| h l1' IHl1'].
  - rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros T l.
  induction l as [| h l' IHl'].
  - reflexivity.
  - simpl.
    rewrite rev_app_distr.
    rewrite IHl'.
    reflexivity.
Qed.

(******************************************************************************)

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y}.

(* Concrete notation for constructing a pair (value). *)
Notation "( x , y )" := (pair x y).

(* Standard notation for product types.
 *
 * The annotation `: type_scope` tells Coq that the abbreviation should only be
 * used when parsing types. This avoids the ambiguity with multiplication.
 *)
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(* Aka. `zip` in other programming languages. *)
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: combine tx ty
  end.

Check @combine: forall (X Y : Type), list X -> list Y -> list (X * Y).

(******************************************************************************)

(* Exercise *)

(* Aka. `unzip`. *)
Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: l' => let (xs, ys) := split l' in
                      ((x :: xs), (y :: ys))
  end.

Example test_split: split [(1, false); (2, false)] = ([1; 2], [false; false]).
Proof. reflexivity. Qed.

(******************************************************************************)

Module OptionPlayground.

Inductive option (X : Type) : Type :=
  | None
  | Some (x : X).

Arguments None {X}.
Arguments Some {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | [] => None
  | h :: t => match n with
              | 0    => Some h
              | S n' => nth_error t n'
              end
  end.

Example test_nth_error1 : nth_error [4; 5; 6; 7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1]; [2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(******************************************************************************)

(* Exercise *)

Definition hd_error {X : Type} (l : list X) : option X :=
 match l with
 | [] => None
 | h :: t => Some h
 end.

Check @hd_error: forall (X : Type), list X -> option X.

Example test_hd_error1: hd_error [1; 2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2: hd_error [[1]; [2]] = Some [1].
Proof. reflexivity. Qed.
Example test_hd_error3: @hd_error nat [] = None.
Proof. reflexivity. Qed.

(******************************************************************************)

(*
 * FUNCTIONS AS DATA
 *)

(* ... *)
