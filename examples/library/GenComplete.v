(* Tests for gen_complete: the completeness predicate it generates, its
   Complete instance, and the generic completeness hints on them. gen_icp_defs
   runs the three generators below on every inductive. Here each one is called
   by its full name, so that the tests name the generator they exercise. The
   catch symbol is needed by the inversion hint. *)
From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* The generated predicates                                            *)
(* ------------------------------------------------------------------ *)

(* No parameters. *)
Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "nat").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "nat").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "nat").
Print complete_nat.
About complete_nat_inst.

(* One parameter. A field of the parameter's type gets the parameter's
   predicate. *)
Inductive option (A : Type) : Type := None | Some : A -> option A.
Arguments None {A}. Arguments Some {A} _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "option").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "option").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "option").
Print complete_option.
About complete_option_inst.

(* Two parameters. *)
Inductive pair (A B : Type) : Type := mkpair : A -> B -> pair A B.
Arguments mkpair {A B} _ _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "pair").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "pair").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "pair").

(* A parameter and a recursive field. *)
Inductive list (A : Type) : Type := nil | cons : A -> list A -> list A.
Arguments nil {A}. Arguments cons {A} _ _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "list").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "list").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "list").

(* Two recursive fields. *)
Inductive ty : Type := TyBool | TyArrow : ty -> ty -> ty.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "ty").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "ty").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "ty").

(* Fields of another type. Their type gets a predicate of its own, and the
   instance takes that type's Complete instance. The two fields share the
   predicate, since the qualities of their types are identified. *)
Inductive pt : Type := P : nat -> nat -> pt.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "pt").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "pt").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "pt").
Print complete_pt.
About complete_pt_inst.

(* A field whose type mentions a parameter. *)
Inductive otree (A : Type) : Type := Leaf | Node : option A -> otree A -> otree A.
Arguments Leaf {A}. Arguments Node {A} _ _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "otree").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "otree").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "otree").
About complete_otree_inst.

(* ------------------------------------------------------------------ *)
(* The instances, through the generic completeness hints               *)
(* ------------------------------------------------------------------ *)

Goal is_complete (S (S O)).
Proof. solve [eauto with icp]. Qed.

Goal is_complete (Some (S O)).
Proof. solve [eauto with icp]. Qed.

(* Nested instances: list of pairs of nat. *)
Goal is_complete (cons (mkpair O (S O)) nil).
Proof. solve [eauto with icp]. Qed.

Goal is_complete (TyArrow TyBool TyBool).
Proof. solve [eauto with icp]. Qed.

Goal is_complete (P O (S O)).
Proof. solve [eauto with icp]. Qed.

Goal is_complete (Node (Some O) Leaf).
Proof. solve [eauto with icp]. Qed.

(* Inversion, through complete_inversion0. *)
Goal forall n, is_complete (S n) -> is_complete n.
Proof. intros. solve [eauto with icp]. Qed.

Goal forall a (l : list nat), is_complete (cons a l) -> is_complete l.
Proof. intros. solve [eauto with icp]. Qed.

(* ------------------------------------------------------------------ *)
(* Holes                                                               *)
(* ------------------------------------------------------------------ *)

(* A hole is never complete, at the top or inside a value. *)
Goal is_complete (TODO nat) -> False.
Proof. icp_inversion 1. Qed.

Goal is_complete (S (TODO nat)).
Proof. Fail solve [eauto with icp]. Abort.

(* ------------------------------------------------------------------ *)
(* What the generator cannot build yet                               *)
(* ------------------------------------------------------------------ *)

(* A recursive field at other parameters, here [nlist (pair A A)]. The
   premise for it would have to be stated at [pair A A] instead of [A].
   gen_complete prints that it cannot generate complete_nlist yet, and
   declares nothing. *)
Inductive nlist (A : Type) : Type := nnil | ncons : A -> nlist (pair A A) -> nlist A.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "nlist").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "nlist").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "nlist").
Fail Check complete_nlist.

(* ------------------------------------------------------------------ *)
(* A type with its own completeness                                    *)
(* ------------------------------------------------------------------ *)

(* generate_catch and generate_hole_match_rule declare the catch symbol and
   the match rule but no completeness predicate, so the type's own instance
   is the only one. Here a flag is complete when it is not the hole. *)
Inductive flag : Type := on | off.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "flag").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "flag").
Fail Check complete_flag.

#[export] Instance completeFlag : Complete flag :=
  { is_complete f := f = TODO flag -> False }.

Goal is_complete on -> on = TODO flag -> False.
Proof. intros H. exact H. Qed.
