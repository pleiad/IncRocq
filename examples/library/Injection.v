From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Unset Collapse Sorts ToType.

Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (gen_icp_defs "nat").

(* ------------------------------------------------------------------ *)
(* Test 1 (tracer bullet): S n = S m gives n = m as hypothesis        *)
(* ------------------------------------------------------------------ *)

Goal forall n m : nat@{Inc;Set}, S n = S m -> n = m.
intros n m H.
icp_injection H.
(* Hinj : n = m is now in context *)
exact Hinj.
Qed.

(* ------------------------------------------------------------------ *)
(* Test 2: list with two arguments — both projections                  *)
(* ------------------------------------------------------------------ *)

Inductive list@{s;u} (A : Type@{s;u}) : Type@{s;u} :=
| nil  : list A
| cons : A -> list A -> list A.
Arguments nil  {A}.
Arguments cons {A}.
MetaRocq Run (gen_icp_defs "list").

Goal forall (a x : nat@{Inc;Set}) (l y : list@{Inc;Set} nat),
  cons a l = cons x y -> a = x.
intros a x l y H.
icp_injection H.
exact Hinj.
Qed.

Goal forall (a x : nat@{Inc;Set}) (l y : list@{Inc;Set} nat),
  cons a l = cons x y -> l = y.
intros a x l y H.
icp_injection H.
exact Hinj0.
Qed.

(* ------------------------------------------------------------------ *)
(* Test 2c: as — name both projections explicitly                     *)
(* ------------------------------------------------------------------ *)

Goal forall (a x : nat@{Inc;Set}) (l y : list@{Inc;Set} nat),
  cons a l = cons x y -> a = x /\ l = y.
intros a x l y H.
icp_injection H as Hhead Htail.
exact (conj Hhead Htail).
Qed.

(* ------------------------------------------------------------------ *)
(* Test 2d: as — wrong number of names gives an error                 *)
(* ------------------------------------------------------------------ *)

Goal forall (a x : nat@{Inc;Set}) (l y : list@{Inc;Set} nat),
  cons a l = cons x y -> a = x.
intros a x l y H.
Fail icp_injection H as Honly.
icp_injection H as Hhead Htail.
exact Hhead.
Qed.

(* ------------------------------------------------------------------ *)
(* Test 3: fail on different constructors — use icp_discriminate       *)
(* ------------------------------------------------------------------ *)

Goal forall n : nat@{Inc;Set}, S n = O -> False.
intros n H.
Fail icp_injection H.
icp_discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Test 4: fail when one side is a hole                                 *)
(* ------------------------------------------------------------------ *)

Goal forall n : nat@{Inc;Set}, S n = TODO nat -> False.
intros n H.
Fail icp_injection H.
icp_discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Test 5: two recursive arguments, every projection                   *)
(* ------------------------------------------------------------------ *)

(* A catch branch interleaves each recursive argument with its induction
   hypothesis, so the k-th value argument is not the k-th binder of the branch.
   Test 2 does not see it. [cons]'s only recursive argument is its last, so the
   induction hypothesis sits past both projections. Here the first argument is
   recursive, which shifts every projection after it. *)

Inductive tree : Type :=
| leaf : tree
| node : tree -> tree -> tree.
MetaRocq Run (gen_icp_defs "tree").

Goal forall l1 r1 l2 r2 : tree@{Inc;Set},
  node l1 r1 = node l2 r2 -> l1 = l2.
intros l1 r1 l2 r2 H.
icp_injection H.
exact Hinj.
Qed.

Goal forall l1 r1 l2 r2 : tree@{Inc;Set},
  node l1 r1 = node l2 r2 -> r1 = r2.
intros l1 r1 l2 r2 H.
icp_injection H.
exact Hinj0.
Qed.

Goal forall l1 r1 l2 r2 : tree@{Inc;Set},
  node l1 r1 = node l2 r2 -> l1 = l2 /\ r1 = r2.
intros l1 r1 l2 r2 H.
icp_injection H as Hl Hr.
exact (conj Hl Hr).
Qed.
