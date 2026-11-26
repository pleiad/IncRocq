(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Typeclass-based relations, tactics and standard instances

   This is the basic theory needed to formalize morphisms and setoids.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

From Stdlib Require Import Program.Basics.
From Stdlib Require Import Program.Tactics.
From Prelude Require Import Relation_Definitions.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.

(** We allow to unfold the [relation] definition while doing morphism search. *)

  (** We rebind relational properties in separate classes to be able to overload each proof. *)

  Class Reflexive {A : Type} (R : relation A) :=
    reflexivity : forall x : A, R x x.

  Definition complement {A : Type}(R : relation A) : relation A := fun x y => R x y -> False.

  (** Opaque for proof-search. *)
  Typeclasses Opaque complement.

  (** These are convertible. *)

  Class Irreflexive {A : Type}(R : relation A) :=
    irreflexivity : Reflexive (complement R).

  Class Symmetric {A : Type}(R : relation A) :=
    symmetry : forall {x y}, R x y -> R y x.

  Class Asymmetric {A : Type}(R : relation A) :=
    asymmetry : forall {x y}, R x y -> R y x -> False.

  Class Transitive {A : Type}(R : relation A) :=
    transitivity : forall {x y z}, R x y -> R y z -> R x z.

  (** Various combinations of reflexivity, symmetry and transitivity. *)

  (** A [PreOrder] is both Reflexive and Transitive. *)

  Class PreOrder {A : Type}(R : relation A) : Type := {
    #[global] PreOrder_Reflexive :: Reflexive R | 2 ;
    #[global] PreOrder_Transitive :: Transitive R | 2 }.

  (** A [StrictOrder] is both Irreflexive and Transitive. *)

  Class StrictOrder {A : Type}(R : relation A) : Type := {
    #[global] StrictOrder_Irreflexive :: Irreflexive R ;
    #[global] StrictOrder_Transitive :: Transitive R }.

  (** By definition, a strict order is also asymmetric *)
  Global Instance StrictOrder_Asymmetric {A : Type} `(StrictOrder A R) : Asymmetric R.
  Proof. firstorder. Qed.

  (** A partial equivalence relation is Symmetric and Transitive. *)

  Class PER {A : Type} (R : relation A) : Type := {
    #[global] PER_Symmetric :: Symmetric R | 3 ;
    #[global] PER_Transitive :: Transitive R | 3 }.

  (** Equivalence relations. *)

  Class Equivalence {A : Type}(R : relation A) : Type := {
    #[global] Equivalence_Reflexive :: Reflexive R ;
    #[global] Equivalence_Symmetric :: Symmetric R ;
    #[global] Equivalence_Transitive :: Transitive R }.

  (** An Equivalence is a PER plus reflexivity. *)

  Global Instance Equivalence_PER {A : Type}{R} `(E:Equivalence A R) : PER R | 10 :=
    { }.

  (** An Equivalence is a PreOrder plus symmetry. *)

  Global Instance Equivalence_PreOrder {A : Type}{R} `(E:Equivalence A R) : PreOrder R | 10 :=
    { }.

  (** We can now define antisymmetry w.r.t. an equivalence relation on the carrier. *)

  Class Antisymmetric {A : Type}eqA `{equ : Equivalence A eqA} (R : relation A) :=
    antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

  (** Rewrite relation on a given support: declares a relation as a rewrite
   relation for use by the generalized rewriting tactic.
   It helps choosing if a rewrite should be handled
   by the generalized or the regular rewriting tactic using leibniz equality.
   Users can declare an [RewriteRelation A RA] anywhere to declare default
   relations on a given type `A`. This is also done automatically by
   the [Declare Relation A RA] commands. It has no mode declaration:
   it will assign `?A := Prop, ?R := iff` on an entirely unspecified query
   `RewriteRelation ?A ?R`, or any prefered rewrite relation of priority < 2. *)

  Class RewriteRelation {A : Type}(RA : relation A).

  (** Leibniz equality. *)
    Global Instance eq_Reflexive {A : Type}: Reflexive (@eq A) := @eq_refl A.
    Global Instance eq_Symmetric {A : Type}: Symmetric (@eq A) := @eq_sym A.
    Global Instance eq_Transitive {A : Type}: Transitive (@eq A) := @eq_trans A.

    (** Leibinz equality [eq] is an equivalence relation.
        The instance has low priority as it is always applicable
        if only the type is constrained. *)

    Global Program Instance eq_equivalence {A : Type}: Equivalence (@eq A) | 10.

  (** Leibniz disequality. *)
    (** Disequality is symmetric. *)
    Global Instance neq_Symmetric {A : Type}: Symmetric (fun x y : A => x <> y) := (@not_eq_sym A).

(** Any [Equivalence] declared in the context is automatically considered
  a rewrite relation. This only applies if the relation is at least partially
  defined: setoid_rewrite won't try to infer arbitrary user rewrite relations. *)

Definition equivalence_rewrite_relation {A : Type}`(eqa : Equivalence A eqA) : RewriteRelation eqA :=
  Build_RewriteRelation A _.

Arguments irreflexivity {A R Irreflexive} [x] _ : rename.
Arguments symmetry {A} {R} {_} [x] [y] _.
Arguments asymmetry {A} {R} {_} [x] [y] _ _.
Arguments transitivity {A} {R} {_} [x] [y] [z] _ _.
Arguments Antisymmetric A eqA {_} _.

#[global]
Create HintDb ord.

#[global]
Hint Resolve irreflexivity : ord.

Unset Implicit Arguments.

Ltac solve_relation :=
  match goal with
  | [ |- ?R ?x ?x ] => reflexivity
  | [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry ; exact H
  end.

#[global]
Create HintDb relations.

#[global]
Hint Extern 4 => solve_relation : relations.

(** We can already dualize all these properties. *)

(** * Standard instances. *)

Ltac reduce_hyp H :=
  match type of H with
    | context [ _ <-> _ ] => fail 1
    | _ => red in H ; try reduce_hyp H
  end.

Ltac reduce_goal :=
  match goal with
    | [ |- _ <-> _ ] => fail 1
    | _ => red ; intros ; try reduce_goal
  end.

Tactic Notation "reduce" "in" hyp(Hid) := reduce_hyp Hid.

Ltac reduce := reduce_goal.

Tactic Notation "apply" "*" constr(t) :=
  first [ refine t | refine (t _) | refine (t _ _) | refine (t _ _ _) | refine (t _ _ _ _) |
    refine (t _ _ _ _ _) | refine (t _ _ _ _ _ _) | refine (t _ _ _ _ _ _ _) ].

(** Logical implication. *)

#[global]
Program Instance impl_Reflexive : Reflexive impl.
Next Obligation. intro H; exact H. Qed.

#[global]
Program Instance impl_Transitive : Transitive impl.
Next Obligation. intro Hx. apply (H0 (H Hx)). Qed.

(** Logical equivalence. *)

#[global]
Instance iff_Reflexive : Reflexive iff := iff_refl.
#[global]
Instance iff_Symmetric : Symmetric iff := iff_sym.
#[global]
Instance iff_Transitive : Transitive iff := iff_trans.

(** Logical equivalence [iff] is an equivalence relation. *)

#[global]
Program Instance iff_equivalence : Equivalence iff.

(* Register bindings for the generalized rewriting tactic *)

Register relation as rewrite.prop.relation.
Register subrelation as rewrite.prop.subrelation.
Register Reflexive as rewrite.prop.Reflexive.
Register reflexivity as rewrite.prop.reflexivity.
Register Symmetric as rewrite.prop.Symmetric.
Register symmetry as rewrite.prop.symmetry.
Register Transitive as rewrite.prop.Transitive.
Register transitivity as rewrite.prop.transitivity.

Register relation as rewrite.type.relation.
Register subrelation as rewrite.type.subrelation.
Register Reflexive as rewrite.type.Reflexive.
Register reflexivity as rewrite.type.reflexivity.
Register Symmetric as rewrite.type.Symmetric.
Register symmetry as rewrite.type.symmetry.
Register Transitive as rewrite.type.Transitive.
Register transitivity as rewrite.type.transitivity.
