(* Tests for gen_complete_minimal: the lemmas that the complete values of an
   inductive are minimal and that its hole is not complete, its
   CompleteMinimal instance, and the tactics that use the instance. Each
   generator is called by its full name, so that the tests name the generator
   they exercise. gen_complete_minimal needs the predicate and the relation
   that gen_complete and gen_refinable declare. *)
From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* The generated lemmas and instances                                  *)
(* ------------------------------------------------------------------ *)

(* No parameters. *)
Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "nat").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "nat").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "nat").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "nat").
MetaRocq Run (IncRocq.gen.CompleteMinimal.gen_complete_minimal "nat").
About complete_nat_minimal.
About complete_nat_hole.
About complete_minimal_nat_inst.

(* A parameter and a recursive field. *)
Inductive list (A : Type) : Type := nil | cons : A -> list A -> list A.
Arguments nil {A}. Arguments cons {A} _ _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "list").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "list").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "list").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "list").
MetaRocq Run (IncRocq.gen.CompleteMinimal.gen_complete_minimal "list").
About complete_list_minimal.
About complete_minimal_list_inst.

(* Two parameters. The universe of pair is not a single level. *)
Inductive pair (A B : Type) : Type := mkpair : A -> B -> pair A B.
Arguments mkpair {A B} _ _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "pair").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "pair").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "pair").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "pair").
MetaRocq Run (IncRocq.gen.CompleteMinimal.gen_complete_minimal "pair").

(* Fields of another type, which share a slot. *)
Inductive pt : Type := P : nat -> nat -> pt.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "pt").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "pt").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "pt").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "pt").
MetaRocq Run (IncRocq.gen.CompleteMinimal.gen_complete_minimal "pt").
About complete_minimal_pt_inst.

(* A field whose type mentions a parameter. *)
Inductive option (A : Type) : Type := None | Some : A -> option A.
Arguments None {A}. Arguments Some {A} _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "option").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "option").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "option").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "option").
MetaRocq Run (IncRocq.gen.CompleteMinimal.gen_complete_minimal "option").

Inductive otree (A : Type) : Type := Leaf | Node : option A -> otree A -> otree A.
Arguments Leaf {A}. Arguments Node {A} _ _.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "otree").
MetaRocq Run (IncRocq.gen.HoleMatch.generate_hole_match_rule "otree").
MetaRocq Run (IncRocq.gen.Complete.gen_complete "otree").
MetaRocq Run (IncRocq.gen.Refinable.gen_refinable "otree").
MetaRocq Run (IncRocq.gen.CompleteMinimal.gen_complete_minimal "otree").

(* ------------------------------------------------------------------ *)
(* The instances, through the class                                    *)
(* ------------------------------------------------------------------ *)

(* Nested instances: list of pairs of a nat and a pt. *)
Goal forall l : list (pair nat pt), is_complete l -> forall l', l' ⊑ l -> l' = l.
Proof. intros l Hl l' H. exact (is_complete_minimal l Hl l' H). Qed.

Goal forall t : otree nat, is_complete t -> forall t', t' ⊑ t -> t' = t.
Proof. intros. eapply is_complete_minimal; eassumption. Qed.

Goal @is_complete (list nat) _ (TODO _) -> False.
Proof. intros H. exact (hole_not_complete H). Qed.

(* icp_absurd_complete refutes a hole with the hole_not_complete field. *)
Goal @is_complete (otree nat) _ (TODO _) -> False.
Proof. intros Hc. icp_absurd_complete. Qed.

(* ------------------------------------------------------------------ *)
(* What the generator cannot build yet                                 *)
(* ------------------------------------------------------------------ *)

(* An inductive without a generated predicate and relation, as for
   gen_refinable. gen_complete_minimal prints that it cannot generate
   complete_nlist_minimal yet, and declares nothing. *)
Inductive nlist (A : Type) : Type := nnil | ncons : A -> nlist (pair A A) -> nlist A.
MetaRocq Run (IncRocq.gen.Catch.generate_catch "nlist").
MetaRocq Run (IncRocq.gen.CompleteMinimal.gen_complete_minimal "nlist").
Fail Check complete_nlist_minimal.
