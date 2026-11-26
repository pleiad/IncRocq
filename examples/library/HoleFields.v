(* Tests for the two hole fields, [hole_is_top] on [Refinable] and
   [hole_not_complete] on [CompleteMinimal], and for the rewrite rule that
   propagates holes through function types.  The instances here register no
   [icp] hint and no [Hint Constructors], so anything that closes a goal
   about a hole does so through the fields. *)
From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

Inductive nat : Type := O | S (n : nat).
(* The refinement relation is the computational one below, so the structural
   relation of gen_icp_defs is not declared. *)
MetaRocq Run (generate_catch "nat").
MetaRocq Run (generate_hole_match_rule "nat").
MetaRocq Run (gen_complete "nat").

(* ------------------------------------------------------------------ *)
(* Holes propagate through function types                             *)
(* ------------------------------------------------------------------ *)

(* A hole at a function type, applied, is a hole at the codomain. *)
Goal @TODO (nat@{Inc;} -> nat@{Inc;}) O = @TODO nat.
Proof. reflexivity. Qed.

Goal forall (f : nat@{Inc;} -> nat@{Inc;}), f = (fun n => □) -> f O = □.
Proof. intros f Hf. rewrite Hf. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* hole_is_top                                                        *)
(* ------------------------------------------------------------------ *)

(* Uniform parametric refinement, scrutinising the lower bound [n1] first.
   That leaves [n ⊑ □] stuck on a variable [n], so neither reduction nor
   [constructor] can close it; [EqMono.v] scrutinises [n2] first precisely to
   avoid this.  Here it is deliberate, so that the goals below can only go
   through the [hole_is_top] field. *)
Definition refinement_nat (n1 n2 : nat@{Inc;}) : Type :=
  nat_catch (fun _ => nat -> Type)
    (fun n      => nat_catch (fun _ => Type) True  (fun _ _ => False) True n)
    (fun _ ih n => nat_catch (fun _ => Type) False (fun p _ => ih p)  True n)
    (fun n      => nat_catch (fun _ => Type) False (fun _ _ => False) True n)
    n1 n2.

Lemma ref_refl : forall n, refinement_nat n n.
Proof. intros n. induction n using nat_catch; cbn; first [ exact I | exact IHn ]. Qed.

Lemma ref_trans : forall n1 n2 n3,
  refinement_nat n1 n2 -> refinement_nat n2 n3 -> refinement_nat n1 n3.
Proof.
  intros n1. induction n1 using nat_catch; intros n2 n3;
    induction n2 using nat_catch; induction n3 using nat_catch; cbn; intros H1 H2;
    first [ exact I | exact H1 | exact H2 | exact (IHn1 _ _ H1 H2)
          | solve [ destruct H1 ] | solve [ destruct H2 ] ].
Qed.

Lemma ref_top : forall n, refinement_nat n □.
Proof. intros n. induction n using nat_catch; exact I. Qed.

#[export] Instance refinableNat : Refinable nat@{Inc;} :=
  { refinement    := refinement_nat ;
    is_transitive := ref_trans ;
    is_reflexive  := ref_refl ;
    hole_is_top   := ref_top }.

(* The field is usable directly. *)
Goal forall n : nat@{Inc;}, n ⊑ □.
Proof. intros n. apply hole_is_top. Qed.

(* And it is what [icp_hole_refinement] closes the goal with. No constructor,
   no [typeclass_instances] hint, and the goal is stuck on [n]. *)
Goal forall n : nat@{Inc;}, n ⊑ □.
Proof. icp_hole_refinement. Qed.

(* The right-hand side only needs to reduce to a hole. *)
Definition succ_v0 (n : nat@{Inc;}) : nat := □.
Goal forall n : nat@{Inc;}, n ⊑ succ_v0 n.
Proof. icp_hole_refinement. Qed.

(* ------------------------------------------------------------------ *)
(* hole_not_complete                                                  *)
(* ------------------------------------------------------------------ *)

(* Minimality is not what this file tests; the hole field is. *)
Lemma complete_minimal_nat : forall a : nat@{Inc;}, is_complete a -> forall a', a' ⊑ a -> a' = a.
Proof. Admitted.

#[export] Instance completeMinimalNat : CompleteMinimal nat :=
  { is_complete_minimal := complete_minimal_nat ;
    hole_not_complete   := ltac2:(icp_inversion 1) }.

(* The field is usable directly. *)
Goal @is_complete nat _ □ -> False.
Proof. exact hole_not_complete. Qed.

(* And it is what [icp_absurd_complete] refutes the hypothesis with. This file
   registers nothing in the [icp] database. *)
Goal @is_complete nat _ □ -> False.
Proof. intros Hc. icp_absurd_complete. Qed.

Goal forall n : nat@{Inc;}, is_complete (succ_v0 n) -> S n = O.
Proof. intros n Hc. icp_absurd_complete. Qed.

(* Through an equation, as the reformed premises leave it. *)
Goal forall n m : nat@{Inc;}, is_complete m -> succ_v0 n = m -> S n = O.
Proof. intros n m Hc Heq. icp_absurd_complete. Qed.

(* ------------------------------------------------------------------ *)
(* Functions                                                          *)
(* ------------------------------------------------------------------ *)

(* [refinableFun] proves [hole_is_top] through the [hole_fun] rule: a hole at
   [nat -> nat] applied to [n] is a hole at [nat]. *)
Goal forall f : nat@{Inc;} -> nat@{Inc;}, f ⊑ □.
Proof. intros f. apply hole_is_top. Qed.

Goal succ_v0 ⊑ □.
Proof. icp_hole_refinement. Qed.

(* ------------------------------------------------------------------ *)
(* No default instances                                               *)
(* ------------------------------------------------------------------ *)

(* Equality is not a refinement relation: [hole_is_top] would say every value
   equals the hole. The former fallbacks are gone. A type whose instances do
   not come from gen_icp_defs has a [Refinable] instance only if one is
   declared. *)
Fail Check eqRefinable.
Fail Check eqCompleteTrue.
Fail Check eqCompleteMinimalTrue.

Module NoInstance.
  Inductive color : Type := red | green.
  MetaRocq Run (generate_catch "color").
  MetaRocq Run (generate_hole_match_rule "color").
  MetaRocq Run (gen_complete "color").
  Fail Definition refinable_color : Refinable color := _.
  Definition color_complete : Complete color := _.
End NoInstance.

(* An existential witness needs no [Refinable] instance, so it can range over
   a [Type]-sorted type, which cannot have one. *)
Goal IncRef (fun f : nat@{Inc;} -> nat@{Inc;} => exists k : nat@{Type;}, f O = O).
Proof. ltac1:(typeclasses eauto). Qed.
