From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* Example type used in the examples                                   *)
(* ------------------------------------------------------------------ *)

Inductive nat : Type := O | S : nat -> nat.
(* The refinement relation is the computational one below, so the structural
   relation of gen_icp_defs is not declared. *)
MetaRocq Run (generate_catch "nat").
MetaRocq Run (generate_hole_match_rule "nat").
MetaRocq Run (gen_complete "nat").

(* Uniform parametric refinement, defined computationally with [nat_catch]
   rather than as an inductive relation. Constructors refine componentwise and
   [TODO nat] is the top element. All three class obligations are proved here.
   The case analysis goes on the upper bound [n2] first, so that [_ ⊑ ???]
   reduces to [True] whatever the lower bound is, a variable included. That is
   what keeps this definition usable by [icp_hole_refinement0], which reduces the
   conclusion and expects to close it outright. Scrutinising [n1] first would
   leave [n ⊑ ???] stuck on the variable [n]. The case studies get the same
   property from the constructor [refinement_nat_todo] of the generated relation. *)
Definition refinement_nat (n1 n2 : nat@{Inc;}) : Type :=
  nat_catch (fun _ => nat -> Type)
    (fun n      => nat_catch (fun _ => Type) True  (fun _ _ => False) False n)
    (fun _ ih n => nat_catch (fun _ => Type) False (fun p _ => ih p)  False n)
    (fun _      => True)
    n2 n1.

Lemma ref_refl : forall n, refinement_nat n n.
Proof.
  intros n. induction n using nat_catch; cbn.
  - exact I.
  - exact IHn.
  - exact I.
Qed.

Lemma ref_trans : forall n1 n2 n3,
  refinement_nat n1 n2 -> refinement_nat n2 n3 -> refinement_nat n1 n3.
Proof.
  (* The upper bound drives the recursion, so it is introduced first. The
     induction on [n3] is the only one with a useful hypothesis, the other two
     are case analyses. *)
  intros n1 n2 n3. revert n2 n1.
  induction n3 using nat_catch; intros n2;
    induction n2 using nat_catch; intros n1;
    (induction n1 using nat_catch; cbn; intros H1 H2);
    first [ exact I | exact H1 | exact H2 | exact (IHn3 _ _ H1 H2)
          (* the [False] hypotheses of the impossible cases. [solve] guards
             against a [True] one being consumed instead *)
          | solve [ destruct H1 ] | solve [ destruct H2 ] ].
Qed.

#[export] Instance refinableNat : Refinable nat@{Inc;} :=
  { refinement    := refinement_nat ;
    is_transitive := ref_trans ;
    is_reflexive  := ref_refl ;
    (* [_ ⊑ ???] is [True] by the case analysis on the upper bound. *)
    hole_is_top   := fun _ => I }.

(* ------------------------------------------------------------------ *)
(* Programs, complete and not                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint add (n m : nat) : nat :=
  match n with O => m | S p => S (add p m) end.

(* Fully incomplete, standing in for the case studies' [add_v0]. *)
Definition add_stub (n m : nat) : nat := ???.

(* One branch incomplete, standing in for the case studies' [add_v1]. Enough
   structure for a refinement goal to still be interesting. *)
Definition add_partial (n m : nat) : nat :=
  match n with O => m | S _ => ??? end.

(* Non-recursive, so its hole only surfaces through the generated
   hole propagation rewrite rule on the match. *)
Definition pred (n : nat@{Inc;}) : nat@{Inc;} :=
  match n with O => O | S p => p end.

(* ------------------------------------------------------------------ *)
(* The relation                                                        *)
(* ------------------------------------------------------------------ *)

(* Monotone equality is reflexive and symmetric through its class instances,
   so the stock tactics work on a [≈] goal and no [icp_] tactic is needed for
   either. *)

Goal forall (n : nat@{Inc;}), S n ≈ S n.
Proof. intros n. reflexivity. Qed.

(* A refinement is in particular a monotone equality, witnessed by the more
   defined side. Every value is monotonically equal to a hole. *)
Lemma eqm_hole_r : forall (n : nat@{Inc;}), n ≈ ???.
Proof. intros n. apply eqm_of_ref. icp_hole_refinement. Qed.

Goal forall (n : nat@{Inc;}), ??? ≈ S n.
Proof. intros n. symmetry. apply eqm_hole_r. Qed.

(* And it is not transitive. A hole is monotonically equal to everything, so
   transitivity would identify every two values of the type.

   Opening the hypothesis unfolds [eq_mono], the escape hatch out of the seal
   ([unfold_eq_mono] is the Ltac1 form of the same thing). It is used here because
   this file is about the notion itself; a proof script about a program never
   needs it. *)
Lemma O_not_eqm_S : (@eq_mono nat@{Inc;} _ O (S O)) -> False.
Proof.
  intros H. unfold eq_mono in H. destruct H as [b [H1 H2]].
  induction b using nat_catch.
  - cbn in H2. destruct H2.
  - cbn in H1. destruct H1.
  - cbn in H1. destruct H1.
Qed.

Lemma eqm_not_transitive :
  (forall (a1 a2 a3 : nat@{Inc;}), a1 ≈ a2 -> a2 ≈ a3 -> a1 ≈ a3) -> False.
Proof.
  intros Htrans. apply O_not_eqm_S.
  apply (Htrans O ??? (S O)).
  - apply eqm_hole_r.
  - symmetry. apply eqm_hole_r.
Qed.

(* ------------------------------------------------------------------ *)
(* reflexivity up to conversion                                        *)
(* ------------------------------------------------------------------ *)

(* Sides equal only up to conversion, since [add O (S n)] and [S (add O n)]
   both compute to [S n]. This is the [O] case of [add_succ_r] in the case
   study, where the common refinement used to be written out by hand. *)
Goal forall (n : nat@{Inc;}), add O (S n) ≈ S (add O n).
Proof. intros n. reflexivity. Qed.

(* Conversion through the hole propagation rewrite rule, which neither [cbn]
   nor [hnf] would fire. *)
Goal pred ??? ≈ pred ???.
Proof. reflexivity. Qed.

(* Several binders in front, as after [icp_reform] and [icp_induction]. Plain
   [reflexivity] introduces nothing, so the binders are the user's to take. *)
Goal forall (n m : nat@{Inc;}), add O (add n m) ≈ add n m.
Proof. intros n m. reflexivity. Qed.

(* Behind the completeness conjunction [icp_reform] leaves in the premise. *)
Goal forall (n : nat@{Inc;}), is_complete n /\ n = n -> S n ≈ S n.
Proof. intros n H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Negative cases                                                      *)
(* ------------------------------------------------------------------ *)

(* Sides that are not convertible. *)
Goal forall (n : nat@{Inc;}), S n ≈ S (S n).
Proof. intros n. Fail reflexivity. Abort.

(* Sides that hold only because one of them is a hole. They are not the same
   value, so reflexivity refuses them and [icp_eq_mono] owns them; see
   EqMonoTactic.v. *)
Goal forall (n : nat@{Inc;}), S ??? ≈ add_stub n n.
Proof. intros n. Fail reflexivity. icp_eq_mono. Qed.

(* The [S] case of [add_succ_r_v1] in the case study. The sides are not
   convertible, but they do merge once [n] is destructed, which is
   [icp_eq_mono]'s half of this goal shape. *)
Goal forall (n m : nat@{Inc;}), add_partial n (S m) ≈ S (add_partial n m).
Proof. intros n m. Fail reflexivity. Abort.

(* ------------------------------------------------------------------ *)
(* The lemmas behind icp_f_equal and icp_apply on a ≈ goal             *)
(* ------------------------------------------------------------------ *)

(* [eqm_app_1] peels one monotone layer, [eqm_weaken] transports a
   hypothesis stated at a more defined argument. Together they are the
   incremental mirror of [f_equal. apply IH.] and this is the shape the [S]
   case of a reformulated [add_succ_r] takes. *)
Goal forall (n m : nat@{Inc;}),
  (add_partial n (S m) ≈ S (add_partial n m)) ->
  S (add_partial n (S m)) ≈ S (S (add_partial n ???)).
Proof. intros n m H. icp_f_equal. icp_apply H. Qed.

(* [eqm_app_2] and [eqm_app_3], the other arities the family ships. *)
Goal forall (n1 n2 m1 m2 : nat@{Inc;}),
  n1 ≈ n2 -> m1 ≈ m2 -> add n1 m1 ≈ add n2 m2.
Proof. intros n1 n2 m1 m2 Hn Hm. icp_f_equal. exact Hn. exact Hm. Qed.

Goal forall (f : nat@{Inc;} -> nat@{Inc;} -> nat@{Inc;} -> nat@{Inc;})
  (a1 a2 b1 b2 c1 c2 : nat@{Inc;}),
  a1 ≈ a2 -> b1 ≈ b2 -> c1 ≈ c2 -> f a1 b1 c1 ≈ f a2 b2 c2.
Proof. intros f a1 a2 b1 b2 c1 c2 Ha Hb Hc. icp_f_equal. exact Ha. exact Hb. exact Hc. Qed.

(* [≈] is not transitive, so [icp_etrans] has no branch for it and says so. *)
Goal forall (n : nat@{Inc;}), S n ≈ S n.
Proof. intros n. Fail icp_etrans n. reflexivity. Qed.
