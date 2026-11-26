From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* Example types used in the examples                                  *)
(* ------------------------------------------------------------------ *)

Inductive bool : Type := true | false.
MetaRocq Run (gen_icp_defs "bool").

Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (gen_icp_defs "nat").

Inductive option@{s;u} (A : Type@{s;u}) : Type@{s;u} :=
| None : option A
| Some : A -> option A.
Arguments None {A}.
Arguments Some {A}.
MetaRocq Run (gen_icp_defs "option").

Inductive list@{s;u} (A : Type@{s;u}) : Type@{s;u} :=
| nil  : list A
| cons : A -> list A -> list A.
Arguments nil  {A}.
Arguments cons {A}.
MetaRocq Run (gen_icp_defs "list").

(* ------------------------------------------------------------------ *)
(* Constructor cases                                                   *)
(* ------------------------------------------------------------------ *)

(* The three-way split on an Inc-sorted bool: true, false, or a hole *)
Goal forall (b : bool@{Inc;}),
  b = true \/ b = false \/ b = TODO bool.
Proof.
  intros b.
  icp_catch b.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; reflexivity.
Qed.

(* The three-way split on an Inc-sorted nat: O, S m, or a hole *)
(* FIXME: Needs sort poly exist *)
(*Goal forall (n : nat@{Inc;}),*)
(*  n = O \/ (exists (m : nat@{Inc;}), n = S m) \/ n = TODO nat. *)
(*Proof.*)
(*  intros n.*)
(*  icp_catch n.*)
(*  - left; reflexivity.*)
(*  - right; left; eauto.*)
(*  - right; right; reflexivity.*)
(*Qed.*)

(* ------------------------------------------------------------------ *)
(* Hole case                                                           *)
(* ------------------------------------------------------------------ *)

(* icp_catch provides an Hhole branch; standard induction does not.
   Here we use it to prove a property that holds on constructors but is
   vacuously true on the hole (i.e., we just need to handle the hole case). *)
Goal forall (b : bool@{Inc;}),
  b = TODO bool \/ b <> TODO bool.
Proof.
  intros b.
  icp_catch b.
  - right; icp_discriminate.
  - right; icp_discriminate.
  - left; reflexivity.
Qed.

(* Using the recursive IH in the nat S-case, plus handling the hole *)
Goal forall (n : nat@{Inc;}),
  n = TODO nat \/ n <> TODO nat.
Proof.
  intros n.
  icp_catch n.
  - right; icp_discriminate.
  - right; icp_discriminate.
  - left; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Parameterized inductives                                            *)
(* ------------------------------------------------------------------ *)

(* FIXME: Need to add exist *)
(* option: three cases — None, Some a, or a hole *)
(*Goal forall (A : Type) (o : option@{Inc;0} A),*)
(*  o = None \/ (exists a, o = Some a) \/ o = TODO (option A). *)
(*Proof.*)
(*  intros A o.*)
(*  icp_catch 'o.*)
(*  - left; reflexivity.*)
(*  - right; left; eauto.*)
(*  - right; right; reflexivity.*)
(*Qed.*)
(**)
(*(* list: nil, cons, or a hole *) *)
(*Goal forall A (l : list A@{Inc;}),*)
(*  l = nil \/ (exists hd tl, l = cons hd tl) \/ l = TODO (list A). *)
(*Proof.*)
(*  intros A l.*)
(*  icp_catch 'l.*)
(*  - left; reflexivity.*)
(*  - right; left; eauto.*)
(*  - right; right; reflexivity.*)
(*Qed.*)

(* Hole case for option: a hole refines any option *)
Goal forall A, TODO (option A) = TODO (option A).
Proof.
  intro A.
  icp_catch (TODO (option A)).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Nested induction: icp_catch a1; icp_catch a2               *)
(* ------------------------------------------------------------------ *)

(* Nested induction on two bools: covers all 9 combinations
   (true/false/hole) × (true/false/hole).
   This exercises the Not_focussed fix — icp_catch a2 is called
   from within the 3 subgoals left by icp_catch a1. *)
Goal forall (b1 b2 : bool@{Inc;}),
  b1 = b2 \/ b1 <> b2.
Proof.
  intros b1 b2.
  icp_catch b1; icp_catch b2.
  all: first [ left; reflexivity | right; icp_discriminate ].
Qed.

(* ------------------------------------------------------------------ *)
(* Numeric form: icp_catch 1                                       *)
(* ------------------------------------------------------------------ *)

(* icp_catch 1 intros the first premise and inducts on it,
   just like Rocq's built-in induction 1.                              *)
Goal forall (b : bool@{Inc;}),
  b = true \/ b = false \/ b = TODO bool.
Proof.
  icp_catch 1.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Catch generated in a different module than the inductive            *)
(* ------------------------------------------------------------------ *)

(* Regression: icp_catch must resolve the catch symbol by current
   scope, not by assuming it lives in the inductive's defining module.
   Here `color` is defined inside `Palette`, but its catch is generated
   outside it — mirroring reuse of an inductive imported from another
   library (e.g. bool from Prelude).                                    *)
Module Palette.
  Inductive color : Type := red | green.
End Palette.
Import Palette.
MetaRocq Run (gen_icp_defs "color").

Goal forall (c : color@{Inc;}),
  c = red \/ c = green \/ c = TODO color.
Proof.
  intros c.
  icp_catch c.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; reflexivity.
Qed.
