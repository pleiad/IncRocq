From Prelude Require Export Datatypes.
From IncRocq.examples Require Export Map.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(******************************************************************************)
(*                                Types                                     *)
(******************************************************************************)

Inductive ty : Type :=
  | TyBool : ty
  | TyArrow : ty -> ty -> ty.

Definition ty_rect := ty_poly_rec@{_ Type; _}.
Register Scheme ty_rect as rect_dep for ty.

#[local] Open Scope lazy_bool_scope.

(* Reserved Infix "==" (at level 80). *)
Fixpoint eq_ty (ty1 ty2 : ty) : bool :=
  match ty1, ty2 with
  | TyBool, TyBool => true
  | TyArrow T1 T2, TyArrow T1' T2' => (eq_ty T1 T1') &&& (eq_ty T2 T2')
  | _, _ => false
  end.

(******************************************************************************)
(*                                Terms                                     *)
(******************************************************************************)

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  (* ty could be in type as well, no? *)
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Definition tm_rect := tm_poly_rec@{_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Type; _}.
Register Scheme tm_rect as rect_dep for tm.

(******************************************************************************)
(*                                Typing defs                                 *)
(******************************************************************************)

Definition env := Map ty.

Fixpoint infer_type (Γ : env) (t : tm) : option ty :=
  match t with
  | tm_var x => map_get Γ x
  | tm_app t1 t2 =>
    match infer_type Γ t1 with
    | Some (TyArrow T11 T12) =>
      match infer_type Γ t2 with
      | Some T2 =>
        if eq_ty T2 T11 then Some T12 else None
      | _ => None
      end
    | _ => None
    end

  | tm_abs x T1 t2 =>
    match infer_type (map_set Γ x T1) t2 with
    | Some T => Some (TyArrow T1 T)
    | _ => None
    end

  | tm_true => Some TyBool
  | tm_false => Some TyBool
  | tm_if t1 t2 t3 =>
    match infer_type Γ t1 with
    | Some TyBool =>
      match infer_type Γ t2, infer_type Γ t3 with
      | Some T2, Some T3 =>
        if eq_ty T2 T3 then Some T2 else None
      | _, _ => None
      end
    | _ => None
    end
  end.

(******************************************************************************)
(*                                Incremental                                 *)
(******************************************************************************)

From IncRocq Require Import IncRocq.

(* The datatypes the case study uses, and variables, which are strings. Their
   refinement and completeness are the structural ones. *)
MetaRocq Run (gen_icp_defs "bool").
MetaRocq Run (gen_icp_defs "option").
MetaRocq Run (gen_icp_defs "nat").
MetaRocq Run (gen_icp_defs "Prelude.String.ascii").
MetaRocq Run (gen_icp_defs "Prelude.String.string").

MetaRocq Run (gen_icp_defs "ty").

(* This takes about 10 seconds. *)
MetaRocq Run (gen_icp_defs "tm").

(******************************************************************************)
(*                             Typing inversion                               *)
(******************************************************************************)

(* The following lemmas are about complete code, each one having a sort-polymorphic
   copy, named with the [icp_] prefix. The two scripts differ only by the [icp_]
   prefix on the tactics. This is currently by design to showcase the incremental
   process explicitly.

   The idea is that when working incrementally, one would import [IncRocq] and
   enable the necessary (incremental) flags, which would turn the lemmas into their
   sort-polymorphic versions and make the unprefixed script prove the lemma at every
   sort. Ideally, one would only ever see a single version of the code, and the
   change of sorts and tactics would not be visible in the script. The current
   [IncRocq] tactics do not shadow the standard definitions, and therefore the same
   script cannot be used for the complete and incremental scenarios. Hence we keep
   both versions at the same time, and for the incremental scenario we use the
   [icp_] versions. Note that for the complete version of [safety], we do use the
   unprefixed version.

   The goal in the end is to have a single version of each lemma. *)

#[universes(collapse_sort_variables=yes)]
Lemma eq_ty_refl : forall T, eq_ty T T = true.
Proof.
  induction T; try reflexivity.
  simpl. rewrite IHT1. apply IHT2.
Qed.

Lemma icp_eq_ty_refl : forall T, eq_ty T T = true.
Proof.
  icp_induction T; try reflexivity.
  simpl. rewrite IHT1. apply IHT2.
Qed.


#[universes(collapse_sort_variables=yes)]
Lemma eq_ty_true : forall (T1 T2 : ty), eq_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1. induction T1; intros T2; destruct T2; simpl; intros H.
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - specialize (IHT1_1 T2_1). specialize (IHT1_2 T2_2).
    destruct (eq_ty T1_1 T2_1).
    + rewrite (IHT1_1 eq_refl). rewrite (IHT1_2 H). reflexivity.
    + discriminate H.
Qed.

Lemma icp_eq_ty_true : forall (T1 T2 : ty), eq_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1. induction T1; intros T2; destruct T2; simpl; intros H.
  - reflexivity.
  - icp_discriminate H.
  - icp_discriminate H.
  - specialize (IHT1_1 T2_1). specialize (IHT1_2 T2_2).
    destruct (eq_ty T1_1 T2_1).
    + rewrite (IHT1_1 eq_refl). rewrite (IHT1_2 H). reflexivity.
    + icp_discriminate H.
Qed.

#[universes(collapse_sort_variables=yes)]
Lemma if_eq_ty_some_inv : forall {T1 T2 T : ty},
  (if eq_ty T1 T2 then Some T1 else None) = Some T -> T1 = T2 /\ T1 = T.
Proof.
  intros T1 T2 T H. assert (E := eq_ty_true T1 T2).
  destruct (eq_ty T1 T2).
  - injection H as HT. split.
    + exact (E eq_refl).
    + exact HT.
  - discriminate H.
Qed.

Lemma icp_if_eq_ty_some_inv : forall {T1 T2 T : ty},
  (if eq_ty T1 T2 then Some T1 else None) = Some T -> T1 = T2 /\ T1 = T.
Proof.
  intros T1 T2 T H. assert (E := icp_eq_ty_true T1 T2).
  destruct (eq_ty T1 T2).
  - icp_injection H as HT. split.
    + exact (E eq_refl).
    + exact HT.
  - icp_discriminate H.
Qed.

#[universes(collapse_sort_variables=yes)]
Lemma infer_type_if_inv : forall {Γ cond tb fb} {T : ty},
    infer_type Γ (tm_if cond tb fb) = Some T ->
    infer_type Γ cond = Some TyBool /\
    infer_type Γ tb = Some T /\
    infer_type Γ fb = Some T.
Proof.
  intros Γ cond tb fb T Hty. simpl in Hty. destruct (infer_type Γ cond) as [Tc|].
  2:{ discriminate Hty. }
  destruct Tc. 2:{ discriminate Hty. }
  destruct (infer_type Γ tb). 2:{ discriminate Hty. }
  destruct (infer_type Γ fb). 2:{ discriminate Hty. }
  destruct (if_eq_ty_some_inv Hty) as [E1 E2]. rewrite <- E1. rewrite <- E2.
  repeat split; reflexivity.
Qed.

Lemma icp_infer_type_if_inv : forall {Γ cond tb fb} {T : ty},
    infer_type Γ (tm_if cond tb fb) = Some T ->
    infer_type Γ cond = Some TyBool /\
    infer_type Γ tb = Some T /\
    infer_type Γ fb = Some T.
Proof.
  intros Γ cond tb fb T Hty. simpl in Hty. destruct (infer_type Γ cond) as [Tc|].
  2:{ icp_discriminate Hty. }
  destruct Tc. 2:{ icp_discriminate Hty. }
  destruct (infer_type Γ tb). 2:{ icp_discriminate Hty. }
  destruct (infer_type Γ fb). 2:{ icp_discriminate Hty. }
  destruct (icp_if_eq_ty_some_inv Hty) as [E1 E2]. rewrite <- E1. rewrite <- E2.
  repeat split; reflexivity.
Qed.

#[universes(collapse_sort_variables=yes)]
Lemma infer_type_app_inv : forall {Γ t1 t2} {T : ty},
    infer_type Γ (tm_app t1 t2) = Some T ->
    exists T1, infer_type Γ t1 = Some (TyArrow T1 T) /\ infer_type Γ t2 = Some T1.
Proof.
  intros Γ t1 t2 T Hty. simpl in Hty. destruct (infer_type Γ t1) as [Tf|].
  2:{ discriminate Hty. }
  destruct Tf as [|T11 T12]. 1:{ discriminate Hty. }
  destruct (infer_type Γ t2) as [T2|]. 2:{ discriminate Hty. }
  assert (E := eq_ty_true T2 T11). destruct (eq_ty T2 T11).
  - injection Hty as HT. exists T11. rewrite HT. rewrite (E eq_refl).
    split; reflexivity.
  - discriminate Hty.
Qed.

Lemma icp_infer_type_app_inv : forall {Γ t1 t2} {T : ty},
    infer_type Γ (tm_app t1 t2) = Some T ->
    exists T1, infer_type Γ t1 = Some (TyArrow T1 T) /\ infer_type Γ t2 = Some T1.
Proof.
  intros Γ t1 t2 T Hty. simpl in Hty. destruct (infer_type Γ t1) as [Tf|].
  2:{ icp_discriminate Hty. }
  destruct Tf as [|T11 T12]. 1:{ icp_discriminate Hty. }
  destruct (infer_type Γ t2) as [T2|]. 2:{ icp_discriminate Hty. }
  assert (E := icp_eq_ty_true T2 T11). destruct (eq_ty T2 T11).
  - icp_injection Hty as HT. exists T11. rewrite HT. rewrite (E eq_refl).
    split; reflexivity.
  - icp_discriminate Hty.
Qed.

#[universes(collapse_sort_variables=yes)]
Lemma infer_type_abs_inv : forall {Γ x U body} {T1 T2 : ty},
    infer_type Γ (tm_abs x U body) = Some (TyArrow T1 T2) ->
    U = T1 /\ infer_type (map_set Γ x U) body = Some T2.
Proof.
  intros Γ x U body T1 T2 Hty. simpl in Hty.
  destruct (infer_type (map_set Γ x U) body) as [Tb|]. 2:{ discriminate Hty. }
  injection Hty as HU HT. split.
  - exact HU.
  - rewrite HT. reflexivity.
Qed.

Lemma icp_infer_type_abs_inv : forall {Γ x U body} {T1 T2 : ty},
    infer_type Γ (tm_abs x U body) = Some (TyArrow T1 T2) ->
    U = T1 /\ infer_type (map_set Γ x U) body = Some T2.
Proof.
  intros Γ x U body T1 T2 Hty. simpl in Hty.
  destruct (infer_type (map_set Γ x U) body) as [Tb|]. 2:{ icp_discriminate Hty. }
  icp_injection Hty as Harr. icp_injection Harr as HU HT. split.
  - exact HU.
  - rewrite HT. reflexivity.
Qed.

(******************************************************************************)
(*                                 Weakening                                  *)
(******************************************************************************)

#[universes(collapse_sort_variables=yes)]
Lemma weakening : forall {t : tm} {Γ Γ' : env} {T : ty},
  included_in Γ Γ' -> infer_type Γ t = Some T -> infer_type Γ' t = Some T.
Proof.
  intros t. induction t as [y | t1 IH1 t2 IH2 | y U body IH | | | t1 IH1 t2 IH2 t3 IH3];
    intros Γ Γ' T Hinc Hty; simpl in *.
  - apply Hinc. exact Hty.
  - destruct (infer_type Γ t1) as [T1|] eqn:H1. 2:{ discriminate Hty. }
    rewrite (IH1 _ _ _ Hinc H1).
    destruct (infer_type Γ t2) as [T2|] eqn:H2. 2:{ destruct T1; discriminate Hty. }
    rewrite (IH2 _ _ _ Hinc H2). exact Hty.
  - destruct (infer_type (map_set Γ y U) body) as [Tb|] eqn:Hb. 2:{ discriminate Hty. }
    rewrite (IH _ _ _ (included_in_map_set y U Hinc) Hb). exact Hty.
  - exact Hty.
  - exact Hty.
  - destruct (infer_type Γ t1) as [T1|] eqn:H1. 2:{ discriminate Hty. }
    rewrite (IH1 _ _ _ Hinc H1).
    destruct (infer_type Γ t2) as [T2|] eqn:H2. 2:{ destruct T1; discriminate Hty. }
    rewrite (IH2 _ _ _ Hinc H2).
    destruct (infer_type Γ t3) as [T3|] eqn:H3. 2:{ destruct T1; discriminate Hty. }
    rewrite (IH3 _ _ _ Hinc H3). exact Hty.
Qed.

#[universes(collapse_sort_variables=yes)]
Corollary weakening_empty : forall {t : tm} {Γ : env} {T : ty},
  infer_type map_empty t = Some T -> infer_type Γ t = Some T.
Proof. intros t Γ T. exact (weakening (included_in_empty Γ)). Qed.
