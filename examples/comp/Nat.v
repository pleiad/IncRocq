(* The running example of the article: natural numbers with [pred] and an
   incomplete [add], developed incrementally. This is the explicit version:
   incompleteness goals are closed one by one with the basic tactics of the
   table. [NatAuto.v] is the same development with the automation tactics. *)
Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(**********************************************************************)
(** * Peano natural numbers, definitions of operations *)
(**********************************************************************)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Declare Scope snat_scope.
Delimit Scope snat_scope with snat.
Bind Scope snat_scope with nat.
Arguments S _%_snat.

Local Open Scope snat_scope.

Definition nat_ind := nat_poly_rec@{_ Prop; _}.
Register Scheme nat_ind as ind_dep for nat.

(** ** Constants *)

Notation "0" := O : snat_scope.
Notation "1" := (S O) : snat_scope.
Notation "2" := (S (S O)) : snat_scope.
Notation "3" := (S (S (S O))) : snat_scope.

(** ** Basic operations *)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S p => p
  end.

(** Truncated subtraction: [n-m] is [0] if [n<=m] *)
Fixpoint sub n m :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end

where "n - m" := (sub n m) : snat_scope.

(*********************************)
(* Incremental                    *)
(*********************************)
From IncRocq Require Import IncRocq.

Local Open Scope snat_scope.

Theorem sub_0_r : forall (n : nat), n - 0 = n.
Proof.
  intros n; destruct n; reflexivity.
Qed.

Theorem sub_1_r : forall (n : nat), n - 1 = pred n.
Proof.
  intros n. destruct n.
  - reflexivity.
  - simpl. now rewrite sub_0_r.
Qed.

MetaRocq Run (gen_icp_defs "nat").


(**********************************************************************)
(** * The incremental scenario of the article (Figure 2) *)
(**********************************************************************)

(* One section per row of the figure: a version of [add] and the proof of
   [add_1] for it. The scripts are the article's, modulo [icp_reform] to enter
   ICP mode and the [icp_] prefix on the tactics.
   Here the [S] case of [add_1_v1], a hole, is closed explicitly by
   [icp_eq_mono]; [NatAuto.v] leaves it to [icp_induction], as in the figure. *)

(*************************************)
(* 1. Definition entirely incomplete *)
(*************************************)

Definition add_v0 (n m : nat) : nat := □.

Lemma add_1_v0 : forall (n : nat), add_v0 n 1 = S n.
Proof.
  icp_reform add_v0.
Qed.

(********************************************)
(* 2. Match and O branch defined, but wrong *)
(********************************************)

Definition add_v1_bad (n m : nat) : nat :=
  match n with
  | O => n (* bug *)
  | S p => □
  end.

Lemma add_1_v1_bad : forall (n : nat), add_v1_bad n 1 = S n.
Proof.
  icp_reform add_v1_bad.
  intros n. induction n.
  - Fail reflexivity.
Abort.

(******************************************)
(* 3. O branch fixed, S branch incomplete *)
(******************************************)

Definition add_v1 (n m : nat) : nat :=
  match n with
  | O => m (* fixed *)
  | S p => □
  end.

Lemma add_1_v1 : forall (n : nat), add_v1 n 1 = S n.
Proof.
  icp_reform add_v1.
  intros n. induction n.
  - reflexivity.
  - icp_eq_mono.
Qed.

(**********************************)
(* 4. S branch defined, but wrong *)
(**********************************)

Fixpoint add_v2_bad (n m : nat) : nat :=
  match n with
  | O => m
  | S p => add_v2_bad p m (* bug *)
  end.

Lemma add_1_v2_bad : forall (n : nat), add_v2_bad n 1 = S n.
Proof. intros n. induction n.
  - reflexivity.
  - simpl. f_equal. Fail apply IHn.
Abort.

(******************************************)
(* 5. S branch fixed, definition complete *)
(******************************************)

Fixpoint add_v2 (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (add_v2 p m) (* fixed *)
  end.

Lemma add_1_v2 : forall (n : nat), add_v2 n 1 = S n.
Proof. intros n. induction n.
  - reflexivity.
  - simpl. f_equal. apply IHn.
Qed.

(**********************************************************************)
(** * Beyond the figure *)
(**********************************************************************)

(* An intermediate increment between [add_v1] and [add_v2]: the [S] branch is
   written, but one of its arguments is still a hole. *)

Fixpoint add_v2_partial (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (add_v2_partial p □)
  end.

Lemma add_1_v2_partial : forall (n : nat), add_v2_partial n 1 = S n.
Proof.
  icp_reform add_v2_partial.
  intros n. induction n.
  - reflexivity.
  - simpl. icp_f_equal. icp_apply IHn.
Qed.

(* [pred_succ_pred] goes from complete code into [add] and back. *)

Lemma pred_succ_pred_v0 : forall (n : nat), (add_v0 (n - 1) 1) - 1 = pred n.
Proof.
  intros n.
  rewrite sub_1_r.
  rewrite (add_1_v0 (n - 1)).
  rewrite sub_1_r.
  reflexivity.
Qed.

Lemma pred_succ_pred_v1 : forall (n : nat), (add_v1 (n - 1) 1) - 1 = pred n.
Proof.
  intros n.
  rewrite sub_1_r.
  rewrite (add_1_v1 (n - 1)).
  rewrite sub_1_r.
  reflexivity.
Qed.

Lemma pred_succ_pred_v2_partial : forall (n : nat), (add_v2_partial (n - 1) 1) - 1 = pred n.
Proof.
  intros n.
  rewrite sub_1_r.
  rewrite (add_1_v2_partial (n - 1)).
  rewrite sub_1_r.
  reflexivity.
Qed.

Lemma pred_succ_pred_v2 : forall (n : nat), (add_v2 (n - 1) 1) - 1 = pred n.
Proof.
  intros n.
  rewrite sub_1_r.
  rewrite (add_1_v2 (n - 1)).
  rewrite sub_1_r.
  reflexivity.
Qed.

(* [add_inv] and [add_succ] of Figure 1, at each version. [add_inv] puts the
   incomplete code in a premise; [add_inv_l] is its mirror image. *)

(************)
(* [add_v0] *)
(************)

Lemma add_inv_l_v0 : forall (n m : nat), add_v0 n m = n -> m = 0.
Proof.
  icp_reform add_v0.
Qed.

Lemma add_inv_v0 : forall (n m : nat), add_v0 n m = m -> n = 0.
Proof.
  icp_reform add_v0.
Qed.

Lemma add_succ_v0 : forall n m, add_v0 n (S m) = S (add_v0 n m).
Proof.
  icp_reform add_v0.
Qed.

(************)
(* [add_v1] *)
(************)

Lemma add_inv_l_v1 : forall (n m : nat), add_v1 n m = n -> m = 0.
Proof.
  intros n; induction n.
  - intros m Heq. simpl in Heq. apply Heq.
  - intros m. cbn. icp_discriminate.
Qed.

Lemma add_succ_v1 : forall n m, add_v1 n (S m) = S (add_v1 n m).
Proof.
  icp_reform add_v1.
  intros n. induction n.
  - intros m. simpl. reflexivity.
  - icp_eq_mono.
Qed.

Lemma add_inv_v1 : forall (n m : nat), add_v1 n m = m -> n = 0.
Proof.
  icp_reform add_v1.
  intros n m. induction m.
  - intros Heq. destruct n.
    * reflexivity.
    * icp_discriminate.
  - intros Heq. rewrite add_succ_v1 in Heq.
    icp_injection Heq as Hinj. icp_apply IHm.
    apply Hinj.
Qed.

(********************)
(* [add_v2_partial] *)
(********************)

Lemma add_inv_l_v2_partial : forall (n m : nat), add_v2_partial n m = n -> m = 0.
Proof.
  intros n. induction n.
  - intros m Heq. simpl in Heq. apply Heq.
  - intros m Heq. simpl in Heq. icp_injection Heq.
    specialize (IHn □ Hinj). icp_discriminate.
Qed.

Lemma add_succ_v2_partial : forall n m, add_v2_partial n (S m) = S (add_v2_partial n m).
Proof.
  icp_reform add_v2_partial.
  intros n. induction n.
  - intros m. simpl. reflexivity.
  - intros m. simpl. icp_f_equal. icp_apply (IHn m).
Qed.

Lemma add_inv_v2_partial : forall (n m : nat), add_v2_partial n m = m -> n = 0.
Proof.
  icp_reform add_v2_partial.
  intros n m. induction m.
  - intros Heq. destruct n.
    * reflexivity.
    * icp_discriminate.
  - intros Heq. rewrite add_succ_v2_partial in Heq.
    icp_injection Heq as Hinj. icp_apply IHm.
    apply Hinj.
Qed.

(************)
(* [add_v2] *)
(************)

Lemma add_inv_l_v2 : forall (n m : nat), add_v2 n m = n -> m = 0.
Proof.
  intros n; induction n.
  - intros m Heq. simpl in Heq. apply Heq.
  - intros m Heq. simpl in Heq.
    apply IHn.
    (* injection *)
Admitted. (* We can return to Prop/Type at this point, otherwise we need LargeElimSort *)

Lemma add_succ_v2 : forall n m, add_v2 n (S m) = S (add_v2 n m).
Proof.
  intros n. induction n.
  - intros m. simpl. reflexivity.
  - intros m. simpl. f_equal. apply IHn.
Qed.

Lemma add_inv_v2 : forall (n m : nat), add_v2 n m = m -> n = 0.
Proof.
  intros n m. revert n. induction m.
  - intros n Heq. destruct n.
    * reflexivity.
    * simpl in Heq. admit. (* discriminate. *) (* We can return to Prop/Type at this point *)
  - intros n Heq. rewrite add_succ_v2 in Heq.
    (* injection and IHm *)
    (* We can return to Prop/Type at this point, otherwise we need LargeElimSort *)
Admitted.

(****************)
(* [add_v2_bad] *)
(****************)

Lemma add_inv_l_v2_bad : forall (n m : nat), add_v2_bad n m = n -> m = 0.
Proof.
  intros n; induction n.
  - intros m Heq. simpl in Heq. apply Heq.
  - intros m Heq. simpl in Heq.
    apply IHn.
Abort.

Lemma add_inv_v2_bad : forall (n m : nat), add_v2_bad n m = m -> n = 0.
Proof.
  intros n m. revert n. induction m.
  - intros n Heq. destruct n.
    * reflexivity.
    * simpl in Heq.
Abort.
