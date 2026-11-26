(* Tests for gen_refinable: the refinement relation it generates, the lemmas
   that it is reflexive and transitive, its Refinable instance, and the
   generic refinement hints on them. Each generator is called by its full
   name, so that the tests name the generator they exercise. The proofs of the
   lemmas need the catch symbol. *)
From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* The generated relations                                             *)
(* ------------------------------------------------------------------ *)

(* No parameters. *)
Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "nat").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "nat").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "nat").
Print refinement_nat.
About refinement_nat_refl.
About refinement_nat_trans.
About refinable_nat_inst.

(* No fields. *)
Inductive bool : Type := true | false.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "bool").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "bool").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "bool").
About refinable_bool_inst.

(* One parameter. A field of the parameter's type gets the parameter's
   relation. *)
Inductive option (A : Type) : Type := None | Some : A -> option A.
Arguments None {A}. Arguments Some {A} _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "option").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "option").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "option").
Print refinement_option.
About refinable_option_inst.

(* Two parameters. The universe of pair is not a single level, so the
   relation has a level of its own for TODO. *)
Inductive pair (A B : Type) : Type := mkpair : A -> B -> pair A B.
Arguments mkpair {A B} _ _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "pair").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "pair").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "pair").
Print refinement_pair.

(* A parameter and a recursive field. *)
Inductive list (A : Type) : Type := nil | cons : A -> list A -> list A.
Arguments nil {A}. Arguments cons {A} _ _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "list").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "list").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "list").
About refinement_list_trans.

(* Two recursive fields. *)
Inductive ty : Type := TyBool | TyArrow : ty -> ty -> ty.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "ty").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "ty").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "ty").

(* Two constructors with fields, so the proof of transitivity has a case for
   each. *)
Inductive tree : Type := Leaf | Node1 : tree -> tree | Node2 : tree -> tree -> tree.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "tree").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "tree").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "tree").
About refinement_tree_trans.

(* Fields of another type. Their type gets a relation of its own, and the
   instance takes that type's Refinable instance. The two fields share the
   relation, since the qualities of their types are identified. *)
Inductive pt : Type := P : nat -> nat -> pt.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "pt").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "pt").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "pt").
Print refinement_pt.
About refinable_pt_inst.

(* A field whose type mentions a parameter. *)
Inductive otree (A : Type) : Type := OLeaf | ONode : option A -> otree A -> otree A.
Arguments OLeaf {A}. Arguments ONode {A} _ _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "otree").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "otree").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "otree").
About refinable_otree_inst.

(* ------------------------------------------------------------------ *)
(* The lemmas, at a relation that is not an instance                  *)
(* ------------------------------------------------------------------ *)

(* The relation and its lemmas are sort polymorphic in the parameters. Here
   the elements live in Type and are related by equality. *)
Goal forall (A : Type) (a : A), refinement_list A eq (cons a nil) (cons a nil).
Proof. intros A a. apply refinement_list_refl. intros; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The instances, through the generic refinement hints                 *)
(* ------------------------------------------------------------------ *)

Goal S (S O) ⊑ S (TODO nat).
Proof. solve [eauto with typeclass_instances]. Qed.

Goal Some (S O) ⊑ Some (TODO nat).
Proof. solve [eauto with typeclass_instances]. Qed.

(* Nested instances: list of pairs. *)
Goal cons (mkpair O (Some TyBool)) nil ⊑ cons (mkpair (TODO _) (Some (TODO _))) (TODO _).
Proof. solve [eauto with typeclass_instances]. Qed.

Goal true ⊑ TODO bool.
Proof. solve [eauto with typeclass_instances]. Qed.

Goal Node2 (Node1 Leaf) Leaf ⊑ Node2 (Node1 (TODO tree)) Leaf.
Proof. solve [eauto with typeclass_instances]. Qed.

Goal TyArrow TyBool TyBool ⊑ TyArrow (TODO ty) TyBool.
Proof. solve [eauto with typeclass_instances]. Qed.

Goal P O (S O) ⊑ P (TODO nat) (S (TODO nat)).
Proof. solve [eauto with typeclass_instances]. Qed.

Goal ONode (Some O) OLeaf ⊑ ONode (Some (TODO _)) (TODO _).
Proof. solve [eauto with typeclass_instances]. Qed.

Goal forall l : list (option nat), l ⊑ l.
Proof. intros. reflexivity. Qed.

Goal forall l1 l2 l3 : list (option nat), l1 ⊑ l2 -> l2 ⊑ l3 -> l1 ⊑ l3.
Proof. intros. etransitivity; eassumption. Qed.

Goal forall t : ty, t ⊑ TODO ty.
Proof. intros. apply hole_is_top. Qed.

(* Different constructors are not related. *)
Goal S O ⊑ O -> False.
Proof. Fail solve [eauto with typeclass_instances]. Abort.

(* ------------------------------------------------------------------ *)
(* What the generator cannot build yet                               *)
(* ------------------------------------------------------------------ *)

(* A recursive field at other parameters, as for gen_complete.
   gen_refinable prints that it cannot generate refinement_nlist yet, and
   declares nothing. *)
Inductive nlist (A : Type) : Type := nnil | ncons : A -> nlist (pair A A) -> nlist A.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "nlist").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "nlist").
Fail Check refinement_nlist.
