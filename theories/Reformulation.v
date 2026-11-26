From Prelude Require Import Logic Relation_Definitions RelationClasses.
From IncRocq Require Import Base.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

#[local] Obligation Tactic := idtac.

Definition t := Type.
Definition type := t@{Type;_}.

(***********************************)
(*          Refinable              *)
(***********************************)
Class Refinable@{s2; u1 u2 u3} (A : Type@{Inc; u1}) : type@{u3} :=
  {
    refinement : A -> A -> Type@{s2; u2} ;
    is_transitive : forall a1 a2 a3, refinement a1 a2 -> refinement a2 a3 -> refinement a1 a3;
    is_reflexive : forall a, refinement a a;
    hole_is_top : forall a, refinement a (TODO A)
  }.

Infix "⊑" := refinement (at level 70).

Arguments refinement : simpl never.

Tactic Notation "unfold_refinement" := unfold refinement; cbn.
Tactic Notation "unfold_refinement" "in" hyp(H) := unfold refinement in H; cbn in H.

#[export] Hint Extern 1 (refinement _ _) => unfold_refinement : typeclass_instances.
#[export] Hint Extern 0 (refinement _ _) => eassumption : typeclass_instances.
#[export] Hint Extern 0 (?t ⊑ ?t) => reflexivity : typeclass_instances.

(* Applies a constructor of the inductive relation behind [refinement], then
   restates each premise on that same relation as a [refinement] goal, so that
   hints indexed on [refinement] apply to it. This makes per-type
   [Hint Constructors] unnecessary. Fails when the relation behind the instance
   is not an inductive applied to the two sides. *)
Ltac refinement_constructor :=
  lazymatch goal with
  | |- @refinement ?A ?inst _ _ =>
      unfold_refinement;
      lazymatch goal with
      | |- ?Rel _ _ =>
          constructor;
          try lazymatch goal with
              | |- Rel ?a ?b => change (@refinement A inst a b)
              end
      end
  end.

#[export] Hint Extern 2 (refinement _ _) => refinement_constructor : typeclass_instances.

#[export]
Instance refinableTransitive {A : Type} `{Refinable A} : Transitive refinement := { transitivity := is_transitive }.
#[export]
Instance refinableReflexive {A : Type} `{Refinable A} : Reflexive refinement := { reflexivity := is_reflexive }.


#[export]
Program Instance refinableFun {A B} `{Refinable B} : Refinable (A -> B) :=
  {
    refinement f g := forall a, f a ⊑ g a ;
  }.
 Next Obligation.
  simpl; intros.  etransitivity; eauto.
Qed.
Next Obligation.
  simpl; intros; reflexivity.
Qed.
Next Obligation.
  simpl; intros; apply hole_is_top.
Qed.

(* Deliberately not a Resolve hint on [typeclass_instances].
   Otherwise it forms a cycle with the [unfold_refinement] hint above, which eta-expands
   [f ⊑ g] into [forall a, f a ⊑ g a] only for this lemma to contract it back,
   and resolution then diverges on any refinement between two functions. *)
Lemma refinement_apply : forall {A B} `{Refinable B} (f g : A -> B),
    f ⊑ g -> forall a, f a ⊑ g a.
Proof. intros A B RB f g Hfg a. apply Hfg. Qed.

(***********************************)
(*          Monotonous             *)
(***********************************)
Definition is_monotone {A B} `{Refinable A} `{Refinable B} (f : A -> B) :=
    forall a1 a2, a1 ⊑ a2 -> f a1 ⊑ f a2.

#[export] Hint Extern 1 (is_monotone _) => unfold is_monotone : typeclass_instances.

Definition is_monotone_2 {A B C} `{Refinable A} `{Refinable B} `{Refinable C} (f : A -> B -> C) :=
  forall a1 a2, a1 ⊑ a2 -> forall b1 b2, b1 ⊑ b2 -> f a1 b1 ⊑ f a2 b2.

#[export] Hint Extern 1 (is_monotone_2 _) => unfold is_monotone_2 : typeclass_instances.

Definition is_monotone_3 {A B C D} `{Refinable A} `{Refinable B} `{Refinable C} `{Refinable D}
  (f : A -> B -> C -> D) :=
  forall a1 a2, a1 ⊑ a2 -> forall b1 b2, b1 ⊑ b2 -> forall c1 c2, c1 ⊑ c2 ->
  f a1 b1 c1 ⊑ f a2 b2 c2.

#[export] Hint Extern 1 (is_monotone_3 _) => unfold is_monotone_3 : typeclass_instances.

Existing Class is_monotone.

(* Discharges [is_monotone (fun x => x a1 .. ak)] at any arity k.  *)
Ltac solve_monotone_app :=
  unfold is_monotone;
  let H := fresh "Hmono" in
  intros ? ? H; repeat simple apply refinement_apply; exact H.

#[export] Hint Extern 1 (is_monotone _) => solve_monotone_app : typeclass_instances.

(***********************************)
(*          Complete               *)
(***********************************)
Class Complete@{s1 s2; u1 u2 u3} (A : Type@{s1;u1}) : type@{u3} :=
  {
    is_complete : A -> Type@{s2; u2} ;
  }.

Arguments is_complete : simpl never.

Tactic Notation "unfold_complete" "in" hyp(H) := unfold is_complete in H; cbn in H.
Tactic Notation "unfold_complete" := unfold is_complete; cbn.

#[export] Hint Extern 0 (Complete _) => eassumption : typeclass_instances.
#[export] Hint Extern 0 (@is_complete ?B _) => unfold B :  typeclass_instances.
#[export] Hint Extern 0 (is_complete _) => eassumption : typeclass_instances.
#[export] Hint Extern 1 (is_complete _) => unfold_complete : typeclass_instances.

(* The counterpart of [refinement_constructor] for [is_complete]. It is
   registered in [icp], where the ICP tactics send completeness obligations.
   The inverse direction, from the completeness of a value to that of its
   fields, is [complete_inversion0] in Tactics.v. *)
Ltac complete_constructor :=
  lazymatch goal with
  | |- @is_complete ?A ?inst _ =>
      unfold_complete;
      lazymatch goal with
      | |- ?P _ =>
          constructor;
          try lazymatch goal with
              | |- P ?a => change (@is_complete A inst a)
              end
      end
  end.

#[export] Hint Extern 2 (is_complete _) => complete_constructor : icp.

#[export]
Instance completeFun {A B} `{Complete A} `{Complete B} : Complete (A -> B) :=
  {
    is_complete f := forall a, is_complete a -> is_complete (f a) ;
  }.

#[export] Hint Extern 0 (is_complete (?f ?x)) => match goal with [H : is_complete ?f |- is_complete (?f ?x)] => apply H end : typeclass_instances.

Lemma apply_complete : forall {A B} `{Complete A} `{Complete B},
    forall a, is_complete a -> is_complete (fun f : A -> B => f a).
Proof.
  red; simpl; intros; eauto.
Qed.

 #[export] Hint Resolve apply_complete : typeclass_instances.

 Lemma is_complete_const_fun : forall {A B} `{Complete A} `{Complete B} (b : B),
  is_complete b -> is_complete (fun _ : A => b).
Proof.
  intros ? ? ? ? ? ? b Hb. red; cbn. intros; eauto.
Qed.

 #[export] Hint Resolve is_complete_const_fun : typeclass_instances.

(***********************************)
(*          CompleteMinimal        *)
(***********************************)
 Class CompleteMinimal@{s2; +} (A : Type@{Inc;_})
   {HRA : Refinable@{s2; _ _ _} A} {HCA : Complete@{Inc s2; _ _ _} A} : type :=
  {
    is_complete_minimal : forall (a : A), is_complete a -> forall a', a' ⊑ a -> @eq@{Inc s2; _ _} A a' a;
    hole_not_complete : is_complete (TODO A) -> False@{s2;_}
  }.


(***********************************)
(*       Completion axioms         *)
(***********************************)
Definition all_monotone : forall {A B : Type} `{Refinable A} `{Refinable B}
  (f : A -> B), is_monotone f := □.

Existing Class is_complete.

Definition all_complete : forall {A : Type} `{Complete A} (a : A), is_complete a := □.

#[export] Hint Resolve all_monotone | 100 : typeclass_instances.
#[export] Hint Resolve all_complete | 100 : typeclass_instances.


(***********************************)
(*        Monotone equality        *)
(***********************************)
(* Two partially defined values are monotonically equal when they have a common
   refinement. Read intuitively, [a1 ≈ a2] says the two sides can still be
   finished into the same thing. *)
Definition eq_mono {A : Type} `{Refinable A} (a1 a2 : A) : Type :=
  exists (a' : A), a' ⊑ a1 /\ a' ⊑ a2.

Infix "≈" := eq_mono (at level 70).

Arguments eq_mono : simpl never.

(* The introduction form, and the only way into a [≈] goal from outside the
   library. *)
Lemma eqm_intro : forall {A : Type} `{Refinable A} (a' : A) {a1 a2 : A},
    a' ⊑ a1 -> a' ⊑ a2 -> a1 ≈ a2.
Proof.
  intros A HA a' a1 a2 H1 H2. exists a'. split. exact H1. exact H2.
Qed.

Lemma eqm_refl : forall {A : Type} `{Refinable A} (a : A), a ≈ a.
Proof.
  intros A HA a. exists a. split. apply is_reflexive. apply is_reflexive.
Qed.

Lemma eqm_sym : forall {A : Type} `{Refinable A} {a1 a2 : A},
    a1 ≈ a2 -> a2 ≈ a1.
Proof.
  intros A HA a1 a2 H. destruct H as [a' [H1 H2]]. exists a'. split. exact H2. exact H1.
Qed.

#[export]
Instance eqMonoReflexive {A : Type} `{Refinable A} : Reflexive eq_mono :=
  { reflexivity := eqm_refl }.

#[export]
Instance eqMonoSymmetric {A : Type} `{Refinable A} : Symmetric eq_mono :=
  { symmetry := fun a1 a2 => eqm_sym }.

Lemma eqm_of_ref : forall {A : Type} `{Refinable A} {a1 a2 : A},
    a1 ⊑ a2 -> a1 ≈ a2.
Proof.
  intros A HA a1 a2 H. exists a1. split. apply is_reflexive. exact H.
Qed.

Lemma eqm_weaken : forall {A : Type} `{Refinable A} {a1 a2 b1 b2 : A},
    a1 ≈ a2 -> a1 ⊑ b1 -> a2 ⊑ b2 -> b1 ≈ b2.
Proof.
  intros A HA a1 a2 b1 b2 H Hb1 Hb2. destruct H as [a' [H1 H2]].
  exists a'. split.
  - exact (is_transitive _ _ _ H1 Hb1).
  - exact (is_transitive _ _ _ H2 Hb2).
Qed.

(* Equal values are trivially monotonically equal: they are already finished
   into the same thing. *)
Lemma eqm_of_eq : forall {A : Type} `{Refinable A} {a1 a2 : A},
    a1 = a2 -> a1 ≈ a2.
Proof.
  intros A HA a1 a2 H. rewrite H. apply eqm_refl.
Qed.

(* On complete values [≈] collapses back to [=].
   Together with [eqm_of_eq] this says [≈] agrees with [=] once nothing is
   left to fill in, which is what makes it safe to reason up to [≈] during the
   incremental phase. *)
Lemma eqm_compl_eq : forall {A : Type} `{Refinable A} `{Complete A}
    {HMA : CompleteMinimal A} {a1 a2 : A},
    is_complete a1 -> is_complete a2 -> a1 ≈ a2 -> a1 = a2.
Proof.
  intros A HRA HCA HMA a1 a2 Hc1 Hc2 H. destruct H as [a' [H1 H2]].
  rewrite <- (is_complete_minimal a1 Hc1 a' H1).
  exact (is_complete_minimal a2 Hc2 a' H2).
Qed.

Lemma eqm_app_1 : forall {A B : Type} `{Refinable A} `{Refinable B}
    (f : A -> B) (Hf : is_monotone f) {a1 a2 : A},
    a1 ≈ a2 -> f a1 ≈ f a2.
Proof.
  intros A B HA HB f Hf a1 a2 H. destruct H as [a' [H1 H2]].
  exists (f a'). split. apply Hf. exact H1. apply Hf. exact H2.
Qed.

Lemma eqm_app_2 : forall {A B C : Type} `{Refinable A} `{Refinable B} `{Refinable C}
    (f : A -> B -> C) (Hf : is_monotone_2 f) {a1 a2 : A} {b1 b2 : B},
    a1 ≈ a2 -> b1 ≈ b2 -> f a1 b1 ≈ f a2 b2.
Proof.
  intros A B C HA HB HC f Hf a1 a2 b1 b2 Ha Hb.
  destruct Ha as [a' [Ha1 Ha2]]. destruct Hb as [b' [Hb1 Hb2]].
  exists (f a' b'). split.
  - apply Hf. exact Ha1. exact Hb1.
  - apply Hf. exact Ha2. exact Hb2.
Qed.

Lemma eqm_app_3 : forall {A B C D : Type}
    `{Refinable A} `{Refinable B} `{Refinable C} `{Refinable D}
    (f : A -> B -> C -> D) (Hf : is_monotone_3 f) {a1 a2 : A} {b1 b2 : B} {c1 c2 : C},
    a1 ≈ a2 -> b1 ≈ b2 -> c1 ≈ c2 -> f a1 b1 c1 ≈ f a2 b2 c2.
Proof.
  intros A B C D HA HB HC HD f Hf a1 a2 b1 b2 c1 c2 Ha Hb Hc.
  destruct Ha as [a' [Ha1 Ha2]]. destruct Hb as [b' [Hb1 Hb2]].
  destruct Hc as [c' [Hc1 Hc2]].
  exists (f a' b' c'). split.
  - apply Hf. exact Ha1. exact Hb1. exact Hc1.
  - apply Hf. exact Ha2. exact Hb2. exact Hc2.
Qed.

(***********************************)
(*        Antitone equality        *)
(***********************************)
(* Either completeness conjunct follows from the other through the equation.
   Stating both is what makes [eqa_sym] a theorem, and with it the fact that
   provability does not depend on which side of [=] the function was written on.
   Introduction goes through [eqa_intro_l] or [eqa_intro_r], which ask for
   completeness on one side only. *)
Definition eq_anti {A : Type} `{Complete A} (a1 a2 : A) : Type :=
  is_complete a1 /\ is_complete a2 /\ a1 = a2.

Infix "≈̇" := eq_anti (at level 70).

Arguments eq_anti : simpl never.

Lemma eqa_intro_l : forall {A : Type} `{Complete A} {a1 a2 : A},
    is_complete a1 -> a1 = a2 -> a1 ≈̇ a2.
Proof.
  intros A HA a1 a2 Hc Heq. split. exact Hc. split.
  - rewrite <- Heq. exact Hc.
  - exact Heq.
Qed.

Lemma eqa_intro_r : forall {A : Type} `{Complete A} {a1 a2 : A},
    is_complete a2 -> a1 = a2 -> a1 ≈̇ a2.
Proof.
  intros A HA a1 a2 Hc Heq. split.
  - rewrite Heq. exact Hc.
  - split. exact Hc. exact Heq.
Qed.

Lemma eqa_eq : forall {A : Type} `{Complete A} {a1 a2 : A},
    a1 ≈̇ a2 -> a1 = a2.
Proof.
  intros A HA a1 a2 H. destruct H as [? [? Heq]]. exact Heq.
Qed.

Lemma eqa_complete_l : forall {A : Type} `{Complete A} {a1 a2 : A},
    a1 ≈̇ a2 -> is_complete a1.
Proof.
  intros A HA a1 a2 H. destruct H as [Hc [? ?]]. exact Hc.
Qed.

Lemma eqa_complete_r : forall {A : Type} `{Complete A} {a1 a2 : A},
    a1 ≈̇ a2 -> is_complete a2.
Proof.
  intros A HA a1 a2 H. destruct H as [? [Hc ?]]. exact Hc.
Qed.

#[export] Hint Resolve eqa_complete_l eqa_complete_r : icp.

(* Guarded on purpose. [a ≈̇ a] holds exactly when [a] is complete, so [eq_anti]
   is a PER and not an equivalence, and no [Reflexive] instance is declared.
   One would prove [??? ≈̇ ???] through [all_complete]. *)
Lemma eqa_refl : forall {A : Type} `{Complete A} {a : A},
    is_complete a -> a ≈̇ a.
Proof.
  intros A HA a Hc. exact (eqa_intro_l Hc eq_refl).
Qed.

Lemma eqa_sym : forall {A : Type} `{Complete A} {a1 a2 : A},
    a1 ≈̇ a2 -> a2 ≈̇ a1.
Proof.
  intros A HA a1 a2 H. destruct H as [Hc1 [Hc2 Heq]].
  split. exact Hc2. split. exact Hc1. exact (eq_sym Heq).
Qed.

Lemma eqa_trans : forall {A : Type} `{Complete A} {a1 a2 a3 : A},
    a1 ≈̇ a2 -> a2 ≈̇ a3 -> a1 ≈̇ a3.
Proof.
  intros A HA a1 a2 a3 H1 H2.
  destruct H1 as [Hc1 [? Heq1]]. destruct H2 as [? [Hc3 Heq2]].
  split. exact Hc1. split. exact Hc3. rewrite Heq1. exact Heq2.
Qed.

#[export]
Instance eqAntiSymmetric {A : Type} `{Complete A} : Symmetric eq_anti :=
  { symmetry := fun a1 a2 => eqa_sym }.

#[export]
Instance eqAntiTransitive {A : Type} `{Complete A} : Transitive eq_anti :=
  { transitivity := fun a1 a2 a3 => eqa_trans }.

#[export]
Instance eqAntiPER {A : Type} `{Complete A} : PER eq_anti := {}.

Lemma eqm_of_eqa : forall {A : Type} `{Refinable A} `{Complete A} {a1 a2 : A},
    a1 ≈̇ a2 -> a1 ≈ a2.
Proof.
  intros A HRA HCA a1 a2 H. exact (eqm_of_eq (eqa_eq H)).
Qed.

Class IncRef@{s2;u1 u2 u3 +} {A : Type@{Inc;u1}}
  {HRA : Refinable@{s2; _ _ _} A} {HCA : Complete@{Inc s2; _ _ _} A}
  (P : A -> Type@{s2;u2}) : type@{u3} :=
  {
    ir_mono : A -> Type@{s2;u2};
    ir_anti : A -> Type@{s2;u2};
    is_monotone_mono : forall (a1 a2 : A), a1 ⊑ a2 -> ir_mono a1 -> ir_mono a2;
    is_antitone_anti : forall (a1 a2 : A), a1 ⊑ a2 -> ir_anti a2 -> ir_anti a1;
    approx_mono : forall a, P a -> ir_mono a;
    approx_anti : forall a, ir_anti a -> P a;
    recoverability_mono : forall (a : A), is_complete a -> ir_mono a -> P a;
    recoverability_anti : forall (a : A), is_complete a -> P a -> ir_anti a
    }.

Arguments ir_mono {A} {HRA} {HCA} P {IncRef} a.
Arguments ir_anti {A} {HRA} {HCA} P {IncRef} a.

#[export]
Program Instance IncRefConst {A : Type} `{Refinable A} `{Complete A} {P : Type} : IncRef (fun a : A => P) := {
    ir_mono := fun _ => P ;
    ir_anti := fun _ => P ;
  }.
Next Obligation.
  (* is_monotone_mono *)
  intros A HRA HCA P. simpl. intros a1 a2 Ha Hm. exact Hm.
Qed.
Next Obligation.
  (* is_antitone_anti *)
  intros A HRA HCA P. simpl. intros a1 a2 Ha Hanti. exact Hanti.
Qed.
Next Obligation.
  (* approx_mono *)
  intros A HRA HCA P. simpl. intros a Hp. exact Hp.
Qed.
Next Obligation.
  (* approx_anti *)
  intros A HRA HCA P. simpl. intros a Hanti. exact Hanti.
Qed.
Next Obligation.
  (* recoverability_mono *)
  intros A HRA HCA P. simpl. intros a Hca Hm. exact Hm.
Qed.
Next Obligation.
  (* recoverability_anti *)
  intros A HRA HCA P. simpl. intros a Hca Hp. exact Hp.
Qed.

#[export]
Program Instance IncRefEq {A B} `{HRA: Refinable A} `{HCA: Complete A} `{HB : CompleteMinimal B}
  (f g : A -> B) (Hmf : is_monotone f) (Hmg : is_monotone g)
  (Hcf : is_complete f) (Hcg : is_complete g)
  : IncRef (fun a => f a = g a) | 2
  := {
    ir_mono := fun a => f a ≈ g a ;
    ir_anti := fun a => f a ≈̇ g a ;
  }.
Next Obligation.
  (* is_monotone_mono *)
  intros A B HRA HCA HRB HCB HB f g Hmf Hmg Hcf Hcg.
  intros a1 a2 Ha Hm.
  exact (eqm_weaken Hm (Hmf _ _ Ha) (Hmg _ _ Ha)).
Qed.
Next Obligation.
  (* is_antitone_anti *)
  intros A B HRA HCA HRB HCB HB f g Hmf Hmg Hcf Hcg.
  intros a1 a2 Ha H.
  assert (Hc2 : is_complete (f a2)) by exact (eqa_complete_l H).
  assert (Heq2 : f a2 = g a2) by exact (eqa_eq H).
  assert (Hf : f a1 = f a2)
    by exact (is_complete_minimal (f a2) Hc2 (f a1) (Hmf _ _ Ha)).
  assert (Hg : g a1 = g a2).
  { apply (is_complete_minimal (g a2)).
    - rewrite <- Heq2. exact Hc2.
    - exact (Hmg _ _ Ha). }
  apply eqa_intro_l.
  - rewrite Hf. exact Hc2.
  - rewrite Hf, Hg. exact Heq2.
Qed.
Next Obligation.
  (* approx_mono *)
  intros A B HRA HCA HRB HCB HB f g Hmf Hmg Hcf Hcg.
  simpl. intros a Heq. exact (eqm_of_eq Heq).
Qed.
Next Obligation.
  (* approx_anti *)
  intros A B HRA HCA HRB HCB HB f g Hmf Hmg Hcf Hcg.
  simpl. intros a H. exact (eqa_eq H).
Qed.
Next Obligation.
  (* recoverability_mono *)
  intros A B HRA HCA HRB HCB HB f g Hmf Hmg Hcf Hcg.
  intros a Hca Hm. exact (eqm_compl_eq (Hcf a Hca) (Hcg a Hca) Hm).
Qed.
Next Obligation.
  (* recoverability_anti *)
  intros A B HRA HCA HRB HCB HB f g Hmf Hmg Hcf Hcg.
  simpl. intros a Hca Heq. apply eqa_intro_l.
  - exact (Hcf a Hca).
  - exact Heq.
Qed.

#[export]
Program Instance IncRefEqL {A B} `{Refinable A} `{Complete A} `{HB : CompleteMinimal B}
  (f : A -> B) (Hcf : is_complete f) (Hmonof : is_monotone f)
  (b : B) (Hcb : is_complete b) : IncRef (fun a => f a = b) | 1 := {
    ir_mono := fun a => f a ≈ b ;
    ir_anti := fun a => f a ≈̇ b ;
  }.
Next Obligation.
  (* is_monotone_mono *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a1 a2 Ha Hm.
  exact (eqm_weaken Hm (Hmonof _ _ Ha) (is_reflexive b)).
Qed.
Next Obligation.
  (* is_antitone_anti *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a1 a2 Ha H.
  assert (Hcb2 : is_complete b) by exact (eqa_complete_r H).
  assert (Heq2 : f a2 = b) by exact (eqa_eq H).
  apply eqa_intro_r.
  - exact Hcb2.
  - apply (is_complete_minimal b Hcb2).
    rewrite <- Heq2. exact (Hmonof _ _ Ha).
Qed.
Next Obligation.
  (* approx_mono *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a Heq. exact (eqm_of_eq Heq).
Qed.
Next Obligation.
  (* approx_anti *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a H. exact (eqa_eq H).
Qed.
Next Obligation.
  (* recoverability_mono *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a Hca Hm. exact (eqm_compl_eq (Hcf a Hca) Hcb Hm).
Qed.
Next Obligation.
  (* recoverability_anti *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a Hca Heq. apply eqa_intro_r.
  - exact Hcb.
  - exact Heq.
Qed.

#[export]
Program Instance IncRefForall {A B} `{Refinable A} `{Complete A} {P : B -> A -> Type} `{HPB : forall b, IncRef (P b)} :
  IncRef (fun a => forall b, P b a) :=
  {
    ir_mono := fun a => forall b, ir_mono (P b) a ;
    ir_anti := fun a => forall b, ir_anti (P b) a ;
  }.
Next Obligation.
  (* is_monotone_mono *)
  intros A B HRA HCA P HPB. simpl. intros a1 a2 Ha Hm b.
  apply (is_monotone_mono a1 a2 Ha). exact (Hm b).
Qed.
Next Obligation.
  (* is_antitone_anti *)
  intros A B HRA HCA P HPB. simpl. intros a1 a2 Ha Hanti b.
  apply (is_antitone_anti a1 a2 Ha). exact (Hanti b).
Qed.
Next Obligation.
  (* approx_mono *)
  intros A B HRA HCA P HPB. simpl. intros a Hp b.
  apply approx_mono. exact (Hp b).
Qed.
Next Obligation.
  (* approx_anti *)
  intros A B HRA HCA P HPB. simpl. intros a Hanti b.
  apply approx_anti. exact (Hanti b).
Qed.
Next Obligation.
  (* recoverability_mono *)
  intros A B HRA HCA P HPB. simpl. intros a Hca Hm b.
  apply (recoverability_mono a Hca). exact (Hm b).
Qed.
Next Obligation.
  (* recoverability_anti *)
  intros A B HRA HCA P HPB. simpl. intros a Hca Hp b.
  apply (recoverability_anti a Hca). exact (Hp b).
Qed.

#[export]
Program Instance IncRefExists {A B} `{Refinable A} `{Complete A}
  {P : B -> A -> Type} `{HPB : forall b, IncRef (P b)}
  : IncRef (fun a => exists b, P b a) :=
  {
    ir_mono := fun a => exists b, ir_mono (P b) a ;
    ir_anti := fun a => exists b, ir_anti (P b) a ;
  }.
Next Obligation.
  (* is_monotone_mono *)
  intros A B HRA HCA P HPB. simpl. intros a1 a2 Ha [b Hb]. exists b.
  apply (is_monotone_mono a1 a2 Ha). exact Hb.
Qed.
Next Obligation.
  (* is_antitone_anti *)
  intros A B HRA HCA P HPB. simpl. intros a1 a2 Ha [b Hb]. exists b.
  apply (is_antitone_anti a1 a2 Ha). exact Hb.
Qed.
Next Obligation.
  (* approx_mono *)
  intros A B HRA HCA P HPB. simpl. intros a [b Hb]. exists b.
  apply approx_mono. exact Hb.
Qed.
Next Obligation.
  (* approx_anti *)
  intros A B HRA HCA P HPB. simpl. intros a [b Hb]. exists b.
  apply approx_anti. exact Hb.
Qed.
Next Obligation.
  (* recoverability_mono *)
  intros A B HRA HCA P HPB. simpl. intros a Hca [b Hb]. exists b.
  apply (recoverability_mono a Hca). exact Hb.
Qed.
Next Obligation.
  (* recoverability_anti *)
  intros A B HRA HCA P HPB. simpl. intros a Hca [b Hb]. exists b.
  apply (recoverability_anti a Hca). exact Hb.
Qed.

#[export]
Program Instance IncRefConj {A} `{Refinable A} `{Complete A} (P Q : A -> Type) {HP : IncRef P} {HQ : IncRef Q} :
  IncRef (fun a => P a /\ Q a) :=
  {
    ir_mono := fun a => (ir_mono P a) /\ (ir_mono Q a) ;
    ir_anti := fun a => (ir_anti P a) /\ (ir_anti Q a) ;
  }.
Next Obligation.
  (* is_monotone_mono *)
  intros A HRA HCA P Q HP HQ. simpl. intros a1 a2 Ha [Hp Hq]. split.
  - apply (is_monotone_mono a1 a2 Ha). exact Hp.
  - apply (is_monotone_mono a1 a2 Ha). exact Hq.
Qed.
Next Obligation.
  (* is_antitone_anti *)
  intros A HRA HCA P Q HP HQ. simpl. intros a1 a2 Ha [Hp Hq]. split.
  - apply (is_antitone_anti a1 a2 Ha). exact Hp.
  - apply (is_antitone_anti a1 a2 Ha). exact Hq.
Qed.
Next Obligation.
  (* approx_mono *)
  intros A HRA HCA P Q HP HQ. simpl. intros a [Hp Hq]. split.
  - apply approx_mono. exact Hp.
  - apply approx_mono. exact Hq.
Qed.
Next Obligation.
  (* approx_anti *)
  intros A HRA HCA P Q HP HQ. simpl. intros a [Hp Hq]. split.
  - apply approx_anti. exact Hp.
  - apply approx_anti. exact Hq.
Qed.
Next Obligation.
  (* recoverability_mono *)
  intros A HRA HCA P Q HP HQ. simpl. intros a Hca [Hp Hq]. split.
  - apply (recoverability_mono a Hca). exact Hp.
  - apply (recoverability_mono a Hca). exact Hq.
Qed.
Next Obligation.
  (* recoverability_anti *)
  intros A HRA HCA P Q HP HQ. simpl. intros a Hca [Hp Hq]. split.
  - apply (recoverability_anti a Hca). exact Hp.
  - apply (recoverability_anti a Hca). exact Hq.
Qed.

#[export]
Program Instance IncRefDisj {A} `{Refinable A} `{Complete A} (P Q : A -> Type) {HP : IncRef P} {HQ : IncRef Q} :
  IncRef (fun a => P a \/ Q a) :=
  {
    ir_mono := fun a => (ir_mono P a) \/ (ir_mono Q a) ;
    ir_anti := fun a => (ir_anti P a) \/ (ir_anti Q a) ;
  }.
Next Obligation.
  (* is_monotone_mono *)
  intros A HRA HCA P Q HP HQ. simpl. intros a1 a2 Ha [Hp | Hq].
  - left. apply (is_monotone_mono a1 a2 Ha). exact Hp.
  - right. apply (is_monotone_mono a1 a2 Ha). exact Hq.
Qed.
Next Obligation.
  (* is_antitone_anti *)
  intros A HRA HCA P Q HP HQ. simpl. intros a1 a2 Ha [Hp | Hq].
  - left. apply (is_antitone_anti a1 a2 Ha). exact Hp.
  - right. apply (is_antitone_anti a1 a2 Ha). exact Hq.
Qed.
Next Obligation.
  (* approx_mono *)
  intros A HRA HCA P Q HP HQ. simpl. intros a [Hp | Hq].
  - left. apply approx_mono. exact Hp.
  - right. apply approx_mono. exact Hq.
Qed.
Next Obligation.
  (* approx_anti *)
  intros A HRA HCA P Q HP HQ. simpl. intros a [Hp | Hq].
  - left. apply approx_anti. exact Hp.
  - right. apply approx_anti. exact Hq.
Qed.
Next Obligation.
  (* recoverability_mono *)
  intros A HRA HCA P Q HP HQ. simpl. intros a Hca [Hp | Hq].
  - left. apply (recoverability_mono a Hca). exact Hp.
  - right. apply (recoverability_mono a Hca). exact Hq.
Qed.
Next Obligation.
  (* recoverability_anti *)
  intros A HRA HCA P Q HP HQ. simpl. intros a Hca [Hp | Hq].
  - left. apply (recoverability_anti a Hca). exact Hp.
  - right. apply (recoverability_anti a Hca). exact Hq.
Qed.

#[export]
Program Instance IncRefArrow {A} `{Refinable A} `{Complete A} {P Q : A -> Type} {HP : IncRef P} {HQ : IncRef Q} :
  IncRef (fun a => P a -> Q a) :=
  {
    ir_mono := fun a => ir_anti P a -> ir_mono Q a ;
    ir_anti := fun a => ir_mono P a -> ir_anti Q a ;
  }.
Next Obligation.
  (* is_monotone_mono *)
  intros A HRA HCA P Q HP HQ. simpl. intros a1 a2 Ha Hm Hpa2.
  apply (is_monotone_mono a1 a2 Ha). apply Hm.
  apply (is_antitone_anti a1 a2 Ha). exact Hpa2.
Qed.
Next Obligation.
  (* is_antitone_anti *)
  intros A HRA HCA P Q HP HQ. simpl. intros a1 a2 Ha Hanti Hpa1.
  apply (is_antitone_anti a1 a2 Ha). apply Hanti.
  apply (is_monotone_mono a1 a2 Ha). exact Hpa1.
Qed.
Next Obligation.
  (* approx_mono *)
  intros A HRA HCA P Q HP HQ. simpl. intros a Hpq Hpa.
  apply approx_mono. apply Hpq. apply approx_anti. exact Hpa.
Qed.
Next Obligation.
  (* approx_anti *)
  intros A HRA HCA P Q HP HQ. simpl. intros a Hanti Hpa.
  apply approx_anti. apply Hanti. apply approx_mono. exact Hpa.
Qed.
Next Obligation.
  (* recoverability_mono *)
  intros A HRA HCA P Q HP HQ. simpl. intros a Hca Hm Hpa.
  apply (recoverability_mono a Hca). apply Hm.
  apply (recoverability_anti a Hca). exact Hpa.
Qed.
Next Obligation.
  (* recoverability_anti *)
  intros A HRA HCA P Q HP HQ. simpl. intros a Hca Hpq Hm.
  apply (recoverability_anti a Hca). apply Hpq.
  apply (recoverability_mono a Hca). exact Hm.
Qed.


Lemma complete_monotone_is_equivalent {A} {HRA : Refinable A} {HCA : Complete A}
  {P : A -> Type} {HP : @IncRef A HRA HCA P} :
  forall (a : A), is_complete a -> ir_mono P a <-> P a.
Proof.
  intros; split; [ apply recoverability_mono; eauto | apply approx_mono ].
Qed.

Lemma complete_antitone_is_equivalent {A} {HRA : Refinable A} {HCA : Complete A}
  {P : A -> Type} {HP : @IncRef A HRA HCA P} :
  forall (a : A), is_complete a -> ir_anti P a <-> P a.
Proof.
  intros; split; [ apply approx_anti | apply recoverability_anti; eauto ].
Qed.

Lemma IncRefEquiv : forall A (HRA : Refinable A) (HCA : Complete A) (P Q : A -> Type),
  @IncRef A HRA HCA P ->
  (forall a, P a <-> Q a) ->
  @IncRef A HRA HCA Q.
Proof.
  intros A HRA HCA P Q HPmono Hequiv.
  unshelve econstructor.
  - exact (ir_mono P).
  - exact (ir_anti P).
  - eapply HPmono.(is_monotone_mono).
  - eapply HPmono.(is_antitone_anti).
  - intros a Ha. apply approx_mono. exact (proj2 (Hequiv a) Ha).
  - intros a Ha. exact (proj1 (Hequiv a) (approx_anti a Ha)).
  - intros a Hac Hm. apply (proj1 (Hequiv a)).
    exact (proj1 (complete_monotone_is_equivalent a Hac) Hm).
  - intros a Hac HQa. apply (proj2 (complete_antitone_is_equivalent a Hac)).
    exact (proj2 (Hequiv a) HQa).
Defined.

(* Was this moved from Rocq's corelib/stdlib, etc? *)
Axiom functional_extensionality_dep :
  forall {A : Type} {B : A -> Type} (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g.

Lemma functional_extensionality {A B} (f g : A -> B) :
  (forall x, f x = g x) -> f = g.
Proof.
  intros ; eauto using @functional_extensionality_dep.
Qed.

#[export]
Instance IncRefEqFun {A B C} {HRA : Refinable A} {HCA : Complete A}
  `{Refinable B} `{Refinable C}
  (f g : A -> B -> C)
  {Hmono : @IncRef A HRA HCA (fun a => forall b, f a b = g a b)}
  : @IncRef A HRA HCA (fun a => f a = g a).
Proof.
  eapply IncRefEquiv.
  - apply Hmono.
  - intros; split.
    * intros. apply functional_extensionality; eauto.
    * intros Heq b. rewrite Heq; eauto.
Defined.

#[export]
Program Instance IncRefEqR {A B} `{Refinable A} `{Complete A} `{HB : CompleteMinimal B}
  (f : A -> B) (Hcf : is_complete f) (Hmonof : is_monotone f)
  (b : B) (Hcb : is_complete b) : IncRef (fun a => b = f a) | 1 := {
    ir_mono := fun a => b ≈ f a ;
    ir_anti := fun a => b ≈̇ f a ;
  }.
Next Obligation.
  (* is_monotone_mono *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a1 a2 Ha Hm.
  exact (eqm_weaken Hm (is_reflexive b) (Hmonof _ _ Ha)).
Qed.
Next Obligation.
  (* is_antitone_anti *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a1 a2 Ha H.
  assert (Hcb2 : is_complete b) by exact (eqa_complete_l H).
  assert (Heq2 : b = f a2) by exact (eqa_eq H).
  apply eqa_intro_l.
  - exact Hcb2.
  - apply eq_sym. apply (is_complete_minimal b Hcb2).
    rewrite Heq2. exact (Hmonof _ _ Ha).
Qed.
Next Obligation.
  (* approx_mono *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a Heq. exact (eqm_of_eq Heq).
Qed.
Next Obligation.
  (* approx_anti *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a H. exact (eqa_eq H).
Qed.
Next Obligation.
  (* recoverability_mono *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a Hca Hm. exact (eqm_compl_eq Hcb (Hcf a Hca) Hm).
Qed.
Next Obligation.
  (* recoverability_anti *)
  intros A B HRA HCA HRB HCB HB f Hcf Hmonof b Hcb.
  simpl. intros a Hca Heq. apply eqa_intro_l.
  - exact Hcb.
  - exact Heq.
Qed.

Lemma recover_mono : forall {A : Type} {HRA : Refinable A} {HCA : Complete A}
  {P : A -> Type} {HP : @IncRef A HRA HCA P} {a : A},
  ir_mono P a -> is_complete a -> P a.
Proof.
  intros A HRA HCA P HP a Hmono Hcomplete.
  eapply recoverability_mono; eassumption.
Qed.
(* Turns a goal [f a1 .. ak ⊑ f b1 .. bk] into the k pointwise refinements
   [ai ⊑ bi], for arities 1 to 5.

   Each one is derived from [all_monotone], so the family assumes nothing
   beyond that completion axiom. Arity k chains k refinements, changing one
   argument per step and peeling the arguments to its right with
   [refinement_apply]. *)
Lemma monotone_app_1 : forall {A B : Type}
  `{Refinable A} `{Refinable B}
  {f : A -> B}
  (a1 a2 : A), a1 ⊑ a2 ->
  f a1 ⊑ f a2.
Proof. intros A B RA RB f a1 a2 Ha. exact (all_monotone f a1 a2 Ha). Qed.

Lemma monotone_app_2 : forall {A B C : Type}
  `{Refinable A} `{Refinable B} `{Refinable C}
  {f : A -> B -> C}
  (a1 a2 : A), a1 ⊑ a2 ->
  forall (b1 b2 : B), b1 ⊑ b2 ->
  f a1 b1 ⊑ f a2 b2.
Proof.
  intros A B C RA RB RC f a1 a2 Ha b1 b2 Hb.
  etransitivity; [ exact (refinement_apply _ _ (all_monotone f a1 a2 Ha) b1) | ].
  exact (all_monotone (f a2) b1 b2 Hb).
Qed.

Lemma monotone_app_3 : forall {A B C D : Type}
  `{Refinable A} `{Refinable B} `{Refinable C} `{Refinable D}
  {f : A -> B -> C -> D}
  (a1 a2 : A), a1 ⊑ a2 ->
  forall (b1 b2 : B), b1 ⊑ b2 ->
  forall (c1 c2 : C), c1 ⊑ c2 ->
  f a1 b1 c1 ⊑ f a2 b2 c2.
Proof.
  intros A B C D RA RB RC RD f a1 a2 Ha b1 b2 Hb c1 c2 Hc.
  etransitivity; [ exact (refinement_apply _ _ (refinement_apply _ _ (all_monotone f a1 a2 Ha) b1) c1) | ].
  exact (monotone_app_2 b1 b2 Hb c1 c2 Hc).
Qed.

Lemma monotone_app_4 : forall {A B C D E : Type}
  `{Refinable A} `{Refinable B} `{Refinable C} `{Refinable D} `{Refinable E}
  {f : A -> B -> C -> D -> E}
  (a1 a2 : A), a1 ⊑ a2 ->
  forall (b1 b2 : B), b1 ⊑ b2 ->
  forall (c1 c2 : C), c1 ⊑ c2 ->
  forall (d1 d2 : D), d1 ⊑ d2 ->
  f a1 b1 c1 d1 ⊑ f a2 b2 c2 d2.
Proof.
  intros A B C D E RA RB RC RD RE f a1 a2 Ha b1 b2 Hb c1 c2 Hc d1 d2 Hd.
  etransitivity; [ exact (refinement_apply _ _ (refinement_apply _ _ (refinement_apply _ _ (all_monotone f a1 a2 Ha) b1) c1) d1) | ].
  exact (monotone_app_3 b1 b2 Hb c1 c2 Hc d1 d2 Hd).
Qed.

Lemma monotone_app_5 : forall {A B C D E F : Type}
  `{Refinable A} `{Refinable B} `{Refinable C} `{Refinable D} `{Refinable E} `{Refinable F}
  {f : A -> B -> C -> D -> E -> F}
  (a1 a2 : A), a1 ⊑ a2 ->
  forall (b1 b2 : B), b1 ⊑ b2 ->
  forall (c1 c2 : C), c1 ⊑ c2 ->
  forall (d1 d2 : D), d1 ⊑ d2 ->
  forall (e1 e2 : E), e1 ⊑ e2 ->
  f a1 b1 c1 d1 e1 ⊑ f a2 b2 c2 d2 e2.
Proof.
  intros A B C D E F RA RB RC RD RE RF f a1 a2 Ha b1 b2 Hb c1 c2 Hc d1 d2 Hd e1 e2 He.
  etransitivity; [ exact (refinement_apply _ _ (refinement_apply _ _ (refinement_apply _ _ (refinement_apply _ _ (all_monotone f a1 a2 Ha) b1) c1) d1) e1) | ].
  exact (monotone_app_4 b1 b2 Hb c1 c2 Hc d1 d2 Hd e1 e2 He).
Qed.

(* States that k monotone equalities [ei ≈ vi] and the equation
   [g v1 .. vk = r] give [g e1 .. ek ≈ r], for arities 1 to 5. The common
   refinement of the arguments, pushed through [g] with [monotone_app_k],
   refines both [g e1 .. ek] and [g v1 .. vk].

   The closing premise is an equation and not a [≈], since [≈] is not
   transitive. *)
Lemma eqm_congr_1 : forall {A1 B : Type} `{Refinable A1} `{Refinable B}
    (g : A1 -> B) {e1 v1 : A1} {r : B},
    g v1 = r -> e1 ≈ v1 -> g e1 ≈ r.
Proof.
  intros A1 B R1 RB g e1 v1 r Hr H1.
  destruct H1 as [a1 [He1 Hv1]].
  exists (g a1). split.
  - exact (monotone_app_1 (f := g) _ _ He1).
  - rewrite <- Hr. exact (monotone_app_1 (f := g) _ _ Hv1).
Qed.

Lemma eqm_congr_2 : forall {A1 A2 B : Type} `{Refinable A1} `{Refinable A2} `{Refinable B}
    (g : A1 -> A2 -> B) {e1 v1 : A1} {e2 v2 : A2} {r : B},
    g v1 v2 = r -> e1 ≈ v1 -> e2 ≈ v2 -> g e1 e2 ≈ r.
Proof.
  intros A1 A2 B R1 R2 RB g e1 v1 e2 v2 r Hr H1 H2.
  destruct H1 as [a1 [He1 Hv1]]. destruct H2 as [a2 [He2 Hv2]].
  exists (g a1 a2). split.
  - exact (monotone_app_2 (f := g) _ _ He1 _ _ He2).
  - rewrite <- Hr. exact (monotone_app_2 (f := g) _ _ Hv1 _ _ Hv2).
Qed.

Lemma eqm_congr_3 : forall {A1 A2 A3 B : Type}
    `{Refinable A1} `{Refinable A2} `{Refinable A3} `{Refinable B}
    (g : A1 -> A2 -> A3 -> B) {e1 v1 : A1} {e2 v2 : A2} {e3 v3 : A3} {r : B},
    g v1 v2 v3 = r -> e1 ≈ v1 -> e2 ≈ v2 -> e3 ≈ v3 -> g e1 e2 e3 ≈ r.
Proof.
  intros A1 A2 A3 B R1 R2 R3 RB g e1 v1 e2 v2 e3 v3 r Hr H1 H2 H3.
  destruct H1 as [a1 [He1 Hv1]]. destruct H2 as [a2 [He2 Hv2]].
  destruct H3 as [a3 [He3 Hv3]].
  exists (g a1 a2 a3). split.
  - exact (monotone_app_3 (f := g) _ _ He1 _ _ He2 _ _ He3).
  - rewrite <- Hr. exact (monotone_app_3 (f := g) _ _ Hv1 _ _ Hv2 _ _ Hv3).
Qed.

Lemma eqm_congr_4 : forall {A1 A2 A3 A4 B : Type}
    `{Refinable A1} `{Refinable A2} `{Refinable A3} `{Refinable A4} `{Refinable B}
    (g : A1 -> A2 -> A3 -> A4 -> B)
    {e1 v1 : A1} {e2 v2 : A2} {e3 v3 : A3} {e4 v4 : A4} {r : B},
    g v1 v2 v3 v4 = r -> e1 ≈ v1 -> e2 ≈ v2 -> e3 ≈ v3 -> e4 ≈ v4 ->
    g e1 e2 e3 e4 ≈ r.
Proof.
  intros A1 A2 A3 A4 B R1 R2 R3 R4 RB g e1 v1 e2 v2 e3 v3 e4 v4 r Hr H1 H2 H3 H4.
  destruct H1 as [a1 [He1 Hv1]]. destruct H2 as [a2 [He2 Hv2]].
  destruct H3 as [a3 [He3 Hv3]]. destruct H4 as [a4 [He4 Hv4]].
  exists (g a1 a2 a3 a4). split.
  - exact (monotone_app_4 (f := g) _ _ He1 _ _ He2 _ _ He3 _ _ He4).
  - rewrite <- Hr. exact (monotone_app_4 (f := g) _ _ Hv1 _ _ Hv2 _ _ Hv3 _ _ Hv4).
Qed.

Lemma eqm_congr_5 : forall {A1 A2 A3 A4 A5 B : Type}
    `{Refinable A1} `{Refinable A2} `{Refinable A3} `{Refinable A4} `{Refinable A5}
    `{Refinable B}
    (g : A1 -> A2 -> A3 -> A4 -> A5 -> B)
    {e1 v1 : A1} {e2 v2 : A2} {e3 v3 : A3} {e4 v4 : A4} {e5 v5 : A5} {r : B},
    g v1 v2 v3 v4 v5 = r -> e1 ≈ v1 -> e2 ≈ v2 -> e3 ≈ v3 -> e4 ≈ v4 -> e5 ≈ v5 ->
    g e1 e2 e3 e4 e5 ≈ r.
Proof.
  intros A1 A2 A3 A4 A5 B R1 R2 R3 R4 R5 RB g e1 v1 e2 v2 e3 v3 e4 v4 e5 v5 r
    Hr H1 H2 H3 H4 H5.
  destruct H1 as [a1 [He1 Hv1]]. destruct H2 as [a2 [He2 Hv2]].
  destruct H3 as [a3 [He3 Hv3]]. destruct H4 as [a4 [He4 Hv4]].
  destruct H5 as [a5 [He5 Hv5]].
  exists (g a1 a2 a3 a4 a5). split.
  - exact (monotone_app_5 (f := g) _ _ He1 _ _ He2 _ _ He3 _ _ He4 _ _ He5).
  - rewrite <- Hr.
    exact (monotone_app_5 (f := g) _ _ Hv1 _ _ Hv2 _ _ Hv3 _ _ Hv4 _ _ Hv5).
Qed.
