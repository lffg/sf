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

(* Coq treats functions as first-class citizens, meaning they can be used as any
 * other kind of value.
 *)

(* A higher-order function manipulates other functions. E.g.: *)
Definition do_it_3_times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @do_it_3_times: forall (X : Type), (X -> X) -> X -> X.

Example test_doit3times: do_it_3_times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': do_it_3_times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {T : Type} (pred : T -> bool) (l : list T) : list T :=
  match l with
  | [] => []
  | x :: l' => let rest := filter pred l' in
                if pred x then x :: rest else rest
  end.

Example test_filter1: filter even [1; 2; 3; 4] = [2; 4].
Proof. reflexivity. Qed.

Definition countoddmembers' (l : list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1: countoddmembers' [1; 0; 3; 1; 4; 5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0; 2; 4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' [] = 0.
Proof. reflexivity. Qed.

(* Anonymous functions. *)
Example test_anon_fun': do_it_3_times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.
Example test_anon_fun'': filter (fun x => leb x 2) [0; 1; 2; 3; 4] = [0; 1; 2].
Proof. reflexivity. Qed.

(******************************************************************************)

(* Use filter (instead of Fixpoint) to write a Coq function `filter_even_gt7`
 * that takes a list of natural numbers as input and returns a list of just
 * those that are even and greater than 7.
 *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => even n && (7 <=? n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1; 2; 6; 9; 10; 3; 12; 8] = [10; 12; 8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5; 2; 6; 19; 129] = [].
Proof. reflexivity. Qed.

(******************************************************************************)

(* Exercise *)

Definition partition {T : Type}
                     (pred : T -> bool)
                     (l : list T)
                   : list T * list T :=
  (filter pred l, filter (fun x => negb (pred x)) l).

Fixpoint partition' {T : Type}
                    (pred : T -> bool)
                    (l : list T)
                  : list T * list T :=
  match l with
  | [] => ([], [])
  | x :: l' => let (pass, fail) := partition' pred l' in
                if pred x then (x :: pass, fail) else (pass, x :: fail)
  end.

Example test_partition1: partition odd [1; 2; 3; 4; 5] = ([1; 3; 5], [2; 4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5; 9; 0] = ([], [5; 9; 0]).
Proof. reflexivity. Qed.
Example test_partition3: @partition nat (fun x => true) [] = ([], []).
Proof. reflexivity. Qed.

(******************************************************************************)

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | x :: l' => f x :: map f l'
  end.

Example test_map1: map (fun x => plus 3 x) [2; 0; 2] = [5; 3; 5].
Proof. reflexivity. Qed.
Example test_map2: map odd [2; 1; 2; 5] = [false; true; false; true].
Proof. reflexivity. Qed.

(******************************************************************************)

(* Exercise *)

Theorem map_app_distr :
  forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [| h l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| h l' IHl'].
  - reflexivity.
  - simpl.
    rewrite map_app_distr.
    rewrite IHl'.
    reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | x :: l' => f x ++ flat_map f l'
  end.

Example test_flat_map1:
  flat_map (fun n => [n; n; n]) [1; 5; 4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(******************************************************************************)

Definition option_map {X Y : Type} (f : X -> Y) (o : option X) : option Y :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Definition option_default {X : Type} (d : X) (o : option X) : X :=
  match o with
  | None => d
  | Some x => x
  end.

(******************************************************************************)

(* Intuitively, `fold` inserts the given binary operator `f` between every pair
 * of elements in a given list. *)
Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (init : Y) : Y :=
  match l with
  | [] => init
  | x :: l' => f x (fold f l' init)
  end.

Example fold_example1:
  (* For example, *)
  fold mult [1; 2; 3; 4] 1 =
  (* Which yields: *)
  1 * (2 * (3 * (4 * 1))).
Proof. reflexivity. Qed.

Check fold andb: list bool -> bool -> bool.

Example fold_example2: fold andb [true; true; false; true] true = false.
Proof. reflexivity. Qed.

Example fold_example3: fold app [[1]; []; [2; 3]; [4]] [] = [1; 2; 3; 4].
Proof. reflexivity. Qed.

(******************************************************************************)

(* Exercise *)

(* Observe that the type of fold is parameterized by two type variables, X and
 * Y, and the parameter f is a binary operator that takes an X and a Y and
 * returns a Y. Can you think of a situation where it would be useful for X and
 * Y to be different? *)

Definition plus_some_numbers := fun (list : list (option nat)) =>
  fold (fun opt => plus (option_default 0 opt)) list 0.

Example plus_some_numbers_test:
  plus_some_numbers [Some 1; None; Some 2; Some 3] = 6.
Proof. reflexivity. Qed.

(******************************************************************************)

(* Coq functions are “curried by default”. Taking the example from the type of
 * `plus`, *)
Check plus: nat -> nat -> nat.

(* Since the -> operator is right-associative, one may rewrite such type as: *)
Check plus: nat -> (nat -> nat).

(* Which is essentially a function take takes a `nat` and returns a function
 * that takes a `nat` and returns a `nat`. This allows partial application. *)

(* Indeed: *)
Definition plus_2 := plus 2.
Check plus_2: nat -> nat.

Example plus_2_test: plus_2 3 = 5.
Proof. reflexivity. Qed.

(******************************************************************************)

(*
 * ADDITIONAL EXERCISES
 *)

Module Exercises.

(******************************************************************************)

(* Exercise *)

(* Many common functions on lists can be implemented in terms of fold. For
 * example, here is an alternative definition of length: *)
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1: fold_length [4; 7; 0] = 3.
Proof. reflexivity. Qed.

(* Prove the correctness of `fold_length`. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [| h l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

(* We can also define `map` in terms of `fold`. Finish `fold_map` below and
 * prove its correctness. *)
Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun elt list => f elt :: list) l [].

Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
  @fold_map X Y f l = @map X Y f l.
Proof.
  intros X Y f l.
  induction l as [| h l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

(* We can define currying as follows: *)
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(* As an exercise, define its inverse, `prod_uncurry`. Then prove the theorems
 * below to show that the two are inverses. *)
Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
    let (x, y) := p in
      f x y.

Check @prod_curry: forall (X Y Z : Type),
  (X * Y -> Z) -> X -> Y -> Z.

Check @prod_uncurry: forall (X Y Z : Type),
  (X -> Y -> Z) -> X * Y -> Z.

Theorem uncurry_curry:
  forall (X Y Z : Type) (f : X -> Y -> Z) (x : X) (y : Y),
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem curry_uncurry:
  forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p as [x y].
  reflexivity.
Qed.

(******************************************************************************)

(* Exercise *)

Theorem nth_list_length_is_none: forall (X : Type) (l : list X) (n : nat),
  length l = n -> @nth_error X l n = None.
Proof.
  intros X l n.
  induction l as [| h l' IHl'].
  - reflexivity.
  - simpl.
Abort. (*        :(        *)

(******************************************************************************)

Module Church.

Definition cnat := forall (X : Type),
  (X -> X) -> X -> X.

Definition zero:  cnat := fun X s z => z.
Definition one:   cnat := fun X s z => s z.
Definition two:   cnat := fun X s z => s (s z).
Definition three: cnat := fun X s z => s (s (s z)).
(* or: Definition three: cnat := @do_it_3_times. *)

(* Exercise *)

Definition succ (n : cnat) : cnat :=
  fun X s z => s (n X s z).

Example succ_1: succ zero = one.
Proof. reflexivity. Qed.
Example succ_2: succ one = two.
Proof. reflexivity. Qed.
Example succ_3: succ two = three.
Proof. reflexivity. Qed.

(* Exercise *)

Definition plus (n m : cnat) : cnat :=
  fun X s z => n X s (m X s z).

Example plus_1: plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2: plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3:  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(* Exercise *)

Definition mult (n m : cnat) : cnat :=
  fun X s z => n X (m X s) z.

Example mult_1: mult one one = one.
Proof. reflexivity. Qed.
Example mult_2: mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3: mult two three = plus three three.
Proof. reflexivity. Qed.

(* Exercise *)

Definition exp (n m : cnat) : cnat :=
  fun X s z => m (X -> X) (n X) s z.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.

(******************************************************************************)

End Exercises.
