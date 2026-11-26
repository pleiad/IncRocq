(* Tests for icp_apply on the types gen_icp_defs declares: with parameters,
   nested, and with fields of another type. The completeness evidence and the
   refinement gaps go through the generated predicates and relations, and
   through the generic hints on them. EqAnti.v tests the same shapes on nat.
   icp_absurd_complete on generated types is tested in GenCompleteMinimal.v. *)
From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (gen_icp_defs "nat").

Inductive list (A : Type) : Type := nil | cons : A -> list A -> list A.
Arguments nil {A}. Arguments cons {A} _ _.
MetaRocq Run (gen_icp_defs "list").

Inductive pair (A B : Type) : Type := mkpair : A -> B -> pair A B.
Arguments mkpair {A B} _ _.
MetaRocq Run (gen_icp_defs "pair").

(* Fields of another type. *)
Inductive pt : Type := P : nat -> nat -> pt.
MetaRocq Run (gen_icp_defs "pt").

Inductive option (A : Type) : Type := None | Some : A -> option A.
Arguments None {A}. Arguments Some {A} _.
MetaRocq Run (gen_icp_defs "option").

(* A field whose type mentions a parameter. *)
Inductive otree (A : Type) : Type := Leaf | Node : option A -> otree A -> otree A.
Arguments Leaf {A}. Arguments Node {A} _ _.
MetaRocq Run (gen_icp_defs "otree").

Fixpoint app {A} (l m : list A) : list A :=
  match l with nil => m | cons a l => cons a (app l m) end.

(* ------------------------------------------------------------------ *)
(* An antitone-equality premise                                        *)
(* ------------------------------------------------------------------ *)

(* The completeness half of the premise is built by the hints, from the
   constructors of the generated predicates. *)
Goal forall (l : list nat),
  (forall k, app k nil ≈̇ cons O (cons (S O) nil) -> k = nil) ->
  app l nil = cons O (cons (S O) nil) -> l = nil.
Proof. intros l IH Heq. icp_apply IH. exact Heq. Qed.

(* Nested instances: a list of pairs of a nat and a pt. *)
Goal forall (l : list (pair nat pt)),
  (forall k, app k nil ≈̇ cons (mkpair O (P O (S O))) nil -> k = nil) ->
  app l nil = cons (mkpair O (P O (S O))) nil -> l = nil.
Proof. intros l IH Heq. icp_apply IH. exact Heq. Qed.

Goal forall (t : otree nat),
  (forall k, k ≈̇ Node (Some O) Leaf -> k = Leaf) ->
  t = Node (Some O) Leaf -> t = Leaf.
Proof. intros t IH Heq. icp_apply IH. exact Heq. Qed.

(* The evidence comes from a hypothesis, through the inversion hint. *)
Goal forall (a : nat) (l m : list nat),
  is_complete (cons a m) ->
  (forall k, app k nil ≈̇ m -> k = nil) -> app l nil = m -> l = nil.
Proof. intros a l m Hc IH Heq. icp_apply IH. exact Heq. Qed.

(* Failure leaves the goal untouched: [cons (TODO nat) nil] is not
   complete. *)
Goal forall (l : list nat), (cons (TODO nat) nil ≈̇ l -> l = l) -> l = l.
Proof. intros l h. Fail icp_apply h. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* A refinement goal                                                   *)
(* ------------------------------------------------------------------ *)

(* The transitive step, then the gap, through the generated relations. *)
Goal forall (n : nat), n ⊑ S (S O) -> n ⊑ S (S (TODO _)).
Proof. intros n H. icp_apply H. Qed.

Goal forall (p : pt), p ⊑ P O O -> p ⊑ P (TODO _) O.
Proof. intros p H. icp_apply H. Qed.

Goal forall (l : list nat), l ⊑ cons O nil -> l ⊑ TODO _.
Proof. intros l H. icp_apply H. Qed.

(* Through constructors of types with parameters. The parameter [nat] of
   [@cons nat O nil] stays in the head, and only [O] and [nil] are peeled. *)
Goal forall (l : list nat),
  l ⊑ cons O (cons (S O) nil) -> l ⊑ cons O (cons (S (TODO nat)) nil).
Proof. intros l H. icp_apply H. Qed.

Goal forall (p : pair nat pt), p ⊑ mkpair O (P O O) -> p ⊑ mkpair (TODO _) (P O (TODO _)).
Proof. intros p H. icp_apply H. Qed.

(* Through a function with a type argument, [@app nat]. *)
Goal forall (l m : list nat), l ⊑ app m (cons O nil) -> l ⊑ app m (cons (TODO _) nil).
Proof. intros l m H. icp_apply H. Qed.

(* ------------------------------------------------------------------ *)
(* A monotone equality goal                                            *)
(* ------------------------------------------------------------------ *)

Goal forall (t : otree nat), t ≈ Node (Some O) Leaf -> t ≈ Node (Some (TODO _)) (TODO _).
Proof. intros t H. icp_apply H. Qed.
