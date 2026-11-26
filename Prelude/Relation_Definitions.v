(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Prelude Require Import Logic.
Set Universe Polymorphism.
Unset Collapse Sorts ToType.

Definition relation@{s1 s2;+} (A : Type@{s1;_}) := A -> A -> Type@{s2;_}.

  Definition reflexive (A : Type) (R : relation A) : Type := forall x:A, R x x.
  Definition transitive (A : Type) (R : relation A): Type := forall x y z:A, R x y -> R y z -> R x z.
  Definition symmetric (A : Type) (R : relation A): Type := forall x y:A, R x y -> R y x.
  Definition antisymmetric (A : Type) (R : relation A): Type := forall x y:A, R x y -> R y x -> x = y.

    (* for compatibility with Equivalence in  ../PROGRAMS/ALG/  *)
    Definition equiv (A : Type) (R : relation A):= reflexive A R /\ transitive A R /\ symmetric A R.

#[global]
Create HintDb sets.

#[global]
Hint Unfold reflexive transitive antisymmetric symmetric: sets.

