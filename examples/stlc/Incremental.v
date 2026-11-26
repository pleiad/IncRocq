From Prelude Require Import Datatypes.
From IncRocq Require Import IncRocq.
From IncRocq.examples Require Import STLC.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(*********************************)
(* Fully incomplete              *)
(*********************************)

Definition eval_v0 (t : tm) : tm := ???.

Theorem safety_v0 : forall (t : tm) (T : ty),
  infer_type map_empty t = Some T ->
  infer_type map_empty (eval_v0 t) = Some T.
Proof.
  icp_reform eval_v0.
Qed.

(***********************************************)
(* App branch incomplete, bug in the if branch *)
(***********************************************)

Fixpoint eval_v1_bad (t : tm) : tm :=
  match t with
  | tm_app _ _ => ???
  | tm_if c tb fb =>
    match eval_v1_bad c with
    | tm_true => eval_v1_bad c (* bug *)
    | tm_false => eval_v1_bad fb
    | _ => t
    end
  | _ => t
  end.

Theorem safety_v1_bad : forall (t : tm) (T : ty),
  infer_type map_empty t = Some T ->
  infer_type map_empty (eval_v1_bad t) = Some T.
Proof.
  icp_reform eval_v1_bad.
  intros t. icp_induction t.
  all: intros T Hty.
  - unfold eval_v1_bad. rewrite Hty. reflexivity.
  - rewrite <- Hty. reflexivity.
  - rewrite <- Hty. reflexivity.
  - ltac1:(pose proof ((icp_infer_type_if_inv Hty)) as Hty').
    destruct Hty' as [Htycond [Hytb Htfb]].
    simpl. destruct (eval_v1_bad t1); rewrite ?Hty; try reflexivity.
    + Fail now apply IHt2.
Abort.

(*********************************)
(* App branch incomplete         *)
(*********************************)

Fixpoint eval_v1 (t : tm) : tm :=
  match t with
  | tm_app _ _ => ???
  | tm_if c tb fb =>
    match eval_v1 c with
    | tm_true => eval_v1 tb (* fixed *)
    | tm_false => eval_v1 fb
    | _ => t
    end
  | _ => t
  end.

Theorem safety_v1 : forall (t : tm) (T : ty),
  infer_type map_empty t = Some T ->
  infer_type map_empty (eval_v1 t) = Some T.
Proof.
  icp_reform eval_v1.
  intros t. icp_induction t.
  all: intros T Hty.
  - unfold eval_v1. rewrite Hty. reflexivity.
  - rewrite <- Hty. reflexivity.
  - rewrite <- Hty. reflexivity.
  - ltac1:(pose proof ((icp_infer_type_if_inv Hty)) as Hty').
    destruct Hty' as [Htycond [Hytb Htfb]].
    simpl. destruct (eval_v1 t1); rewrite ?Hty; try reflexivity.
    + now apply IHt2.
    + now apply IHt3.
Qed.

(*********************************************)
(* App branch implemented, subst incomplete  *)
(*********************************************)

Definition subst_v2 (x : string) (v t : tm) : tm := ???.

(* The app branch evaluates the body after substitution. That term is not a
   subterm of [t], so the guard checker rejects the recursive call, and [eval]
   needs fuel. *)
Fail Fixpoint eval_v2 (t : tm) : tm :=
  match t with
  | tm_app t1 t2 =>
    match eval_v2 t1 with
    | tm_abs x _ body => eval_v2 (subst_v2 x t2 body)
    | _ => t
    end
  | tm_if c tb fb =>
    match eval_v2 c with
    | tm_true => eval_v2 tb
    | tm_false => eval_v2 fb
    | _ => t
    end
  | _ => t
  end.

Fixpoint eval_v2 (n : nat) (t : tm) : tm :=
  match n with
  | O => t
  | S n' =>
    match t with
    | tm_app t1 t2 =>
      match eval_v2 n' t1 with
      | tm_abs x _ body => eval_v2 n' (subst_v2 x t2 body)
      | _ => t
      end
    | tm_if c tb fb =>
      match eval_v2 n' c with
      | tm_true => eval_v2 n' tb
      | tm_false => eval_v2 n' fb
      | _ => t
      end
    | _ => t
    end
  end.

Lemma subst_typing_v2 : forall (Γ : env) (x : string) (s t : tm) (T T' : ty),
  infer_type (map_set Γ x T) t = Some T' ->
  infer_type map_empty s = Some T ->
  infer_type Γ (subst_v2 x s t) = Some T'.
Proof.
  icp_reform subst_v2.
Qed.

Theorem safety_v2 : forall (n : nat) (t : tm) (T : ty),
  infer_type map_empty t = Some T ->
  infer_type map_empty (eval_v2 n t) = Some T.
Proof.
  intros n. icp_induction n.
  - intros t T Hty. simpl. rewrite Hty. reflexivity.
  - intros t. icp_destruct t.
    all: intros T Hty.
    + ltac1:(pose proof (icp_infer_type_app_inv Hty) as Hty').
      destruct Hty' as [T1 [Ht1 Ht2]].
      simpl. destruct (eval_v2 n t1) as [?|? ?|x U body| | |? ? ?] eqn:E;
        rewrite ?Hty; try reflexivity.
      ltac1:(pose proof (IHn t1 _ Ht1) as Habs).
      rewrite E in Habs.
      destruct (icp_infer_type_abs_inv Habs) as [HU Hbody]. subst U.
      apply IHn. apply subst_typing_v2 with (T := T1).
      * exact Hbody.
      * exact Ht2.
    + rewrite <- Hty. reflexivity.
    + rewrite <- Hty. reflexivity.
    + rewrite <- Hty. reflexivity.
    + ltac1:(pose proof ((icp_infer_type_if_inv Hty)) as Hty').
      destruct Hty' as [Htycond [Hytb Htfb]].
      simpl. destruct (eval_v2 n t1); rewrite ?Hty; try reflexivity.
      * now apply IHn.
      * now apply IHn.
Qed.

(*********************************************)
(* Var and abs branches of subst incomplete  *)
(*********************************************)

Fixpoint subst_v3 (x : string) (v t : tm) : tm :=
  match t with
  | tm_var _ => ???
  | tm_app t1 t2 => tm_app (subst_v3 x v t1) (subst_v3 x v t2)
  | tm_abs _ _ _ => ???
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c tb fb => tm_if (subst_v3 x v c) (subst_v3 x v tb) (subst_v3 x v fb)
  end.

Lemma subst_typing_v3 : forall (Γ : env) (x : string) (s t : tm) (T T' : ty),
  infer_type (map_set Γ x T) t = Some T' ->
  infer_type map_empty s = Some T ->
  infer_type Γ (subst_v3 x s t) = Some T'.
Proof.
  icp_reform subst_v3.
  intros Γ x s t. revert Γ. icp_induction t.
  all: intros Γ T T' Hty Hs.
  - apply icp_infer_type_app_inv in Hty. destruct Hty as [T1 [Htyarrow Htyarg]].
    simpl. icp_rewrite (IHt1 Γ T (TyArrow T1 T') Htyarrow Hs), (IHt2 Γ T T1 Htyarg Hs),
      icp_eq_ty_refl.
    reflexivity.
  - rewrite <- Hty. reflexivity.
  - rewrite <- Hty. reflexivity.
  - apply icp_infer_type_if_inv in Hty. destruct Hty as [Hc [Htb Hfb]].
    simpl. icp_rewrite (IHt1 Γ T TyBool Hc Hs), (IHt2 Γ T T' Htb Hs), (IHt3 Γ T T' Hfb Hs),
      icp_eq_ty_refl.
    reflexivity.
Qed.

Fixpoint eval_v3 (n : nat) (t : tm) : tm :=
  match n with
  | O => t
  | S n' =>
    match t with
    | tm_app t1 t2 =>
      match eval_v3 n' t1 with
      | tm_abs x _ body => eval_v3 n' (subst_v3 x t2 body)
      | _ => t
      end
    | tm_if c tb fb =>
      match eval_v3 n' c with
      | tm_true => eval_v3 n' tb
      | tm_false => eval_v3 n' fb
      | _ => t
      end
    | _ => t
    end
  end.

Theorem safety_v3 : forall (n : nat) (t : tm) (T : ty),
  infer_type map_empty t = Some T ->
  infer_type map_empty (eval_v3 n t) = Some T.
Proof.
  intros n. icp_induction n.
  - intros t T Hty. simpl. rewrite Hty. reflexivity.
  - intros t. icp_destruct t.
    all: intros T Hty.
    + ltac1:(pose proof (icp_infer_type_app_inv Hty) as Hty').
      destruct Hty' as [T1 [Ht1 Ht2]].
      simpl. destruct (eval_v3 n t1) as [?|? ?|x U body| | |? ? ?] eqn:E;
        rewrite ?Hty; try reflexivity.
      ltac1:(pose proof (IHn t1 _ Ht1) as Habs).
      rewrite E in Habs.
      destruct (icp_infer_type_abs_inv Habs) as [HU Hbody]. subst U.
      apply IHn. apply subst_typing_v3 with (T := T1).
      * exact Hbody.
      * exact Ht2.
    + rewrite <- Hty. reflexivity.
    + rewrite <- Hty. reflexivity.
    + rewrite <- Hty. reflexivity.
    + ltac1:(pose proof ((icp_infer_type_if_inv Hty)) as Hty').
      destruct Hty' as [Htycond [Hytb Htfb]].
      simpl. destruct (eval_v3 n t1); rewrite ?Hty; try reflexivity.
      * now apply IHn.
      * now apply IHn.
Qed.

(*********************************************)
(* Subst implemented, bug in the abs branch  *)
(*********************************************)

Fixpoint subst_v4_bad (x : string) (v t : tm) : tm :=
  match t with
  | tm_var y => if String.eqb y x then v else t
  | tm_app t1 t2 => tm_app (subst_v4_bad x v t1) (subst_v4_bad x v t2)
  | tm_abs y U body => tm_abs y U (subst_v4_bad x v body) (* bug, substitutes under a binder that shadows [x] *)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c tb fb =>
    tm_if (subst_v4_bad x v c) (subst_v4_bad x v tb) (subst_v4_bad x v fb)
  end.

#[universes(collapse_sort_variables=yes)]
Lemma subst_typing_v4_bad : forall (Γ : env) (x : string) (s t : tm) (T T' : ty),
  infer_type (map_set Γ x T) t = Some T' ->
  infer_type map_empty s = Some T ->
  infer_type Γ (subst_v4_bad x s t) = Some T'.
Proof.
  intros Γ x s t. revert Γ.
  induction t as [y | t1 IHt1 t2 IHt2 | y U body IH | | | t1 IHt1 t2 IHt2 t3 IHt3].
  all: intros Γ T T' Hty Hs.
  - simpl in *. destruct (String.eqb y x).
    + injection Hty as HT. rewrite <- HT. exact (weakening_empty Hs).
    + exact Hty.
  - apply infer_type_app_inv in Hty. destruct Hty as [T1 [Htyarrow Htyarg]].
    simpl. rewrite (IHt1 Γ T (TyArrow T1 T') Htyarrow Hs).
    rewrite (IHt2 Γ T T1 Htyarg Hs). rewrite eq_ty_refl. reflexivity.
  - simpl in Hty.
    destruct (infer_type (map_set (map_set Γ x T) y U) body) as [Tb|] eqn:Hb.
    2:{ discriminate Hty. }
    injection Hty as HT. rewrite <- HT. simpl.
    destruct (String.eqb y x) eqn:Hyx.
    + rewrite (eqb_true y x Hyx) in Hb.
      assert (Hbody := weakening (shadowing_included_in Γ x T U) Hb).
      rewrite (eqb_true y x Hyx).
      rewrite (IH (map_set Γ x U) T Tb).
      * reflexivity.
      * (* [IH] needs [body] typed under [x : T], but the inner binder gives [x : U]. *)
        Fail exact Hbody.
        admit.
      * exact Hs.
    + assert (Hneq : x = y -> False).
      { intros Exy. rewrite Exy in Hyx. rewrite eqb_refl in Hyx. discriminate Hyx. }
      assert (Hbody := weakening (map_permutation_included_in Γ x y T U Hneq) Hb).
      rewrite (IH (map_set Γ y U) T Tb Hbody Hs). reflexivity.
  - simpl in *. exact Hty.
  - simpl in *. exact Hty.
  - apply infer_type_if_inv in Hty. destruct Hty as [Hc [Htb Hfb]].
    simpl. rewrite (IHt1 Γ T TyBool Hc Hs). rewrite (IHt2 Γ T T' Htb Hs).
    rewrite (IHt3 Γ T T' Hfb Hs). rewrite eq_ty_refl. reflexivity.
Abort.

(*********************************************)
(* Complete                                  *)
(*********************************************)

Fixpoint subst_v4 (x : string) (v t : tm) : tm :=
  match t with
  | tm_var y => if String.eqb y x then v else t
  | tm_app t1 t2 => tm_app (subst_v4 x v t1) (subst_v4 x v t2)
  | tm_abs y U body =>
    tm_abs y U (if String.eqb y x then body else subst_v4 x v body) (* fixed *)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c tb fb => tm_if (subst_v4 x v c) (subst_v4 x v tb) (subst_v4 x v fb)
  end.

#[universes(collapse_sort_variables=yes)]
Lemma subst_typing_v4 : forall (Γ : env) (x : string) (s t : tm) (T T' : ty),
  infer_type (map_set Γ x T) t = Some T' ->
  infer_type map_empty s = Some T ->
  infer_type Γ (subst_v4 x s t) = Some T'.
Proof.
  intros Γ x s t. revert Γ.
  induction t as [y | t1 IHt1 t2 IHt2 | y U body IH | | | t1 IHt1 t2 IHt2 t3 IHt3].
  all: intros Γ T T' Hty Hs.
  - simpl in *. destruct (String.eqb y x).
    + injection Hty as HT. rewrite <- HT. exact (weakening_empty Hs).
    + exact Hty.
  - apply infer_type_app_inv in Hty. destruct Hty as [T1 [Htyarrow Htyarg]].
    simpl. rewrite (IHt1 Γ T (TyArrow T1 T') Htyarrow Hs), (IHt2 Γ T T1 Htyarg Hs),
      eq_ty_refl.
    reflexivity.
  - simpl in Hty.
    destruct (infer_type (map_set (map_set Γ x T) y U) body) as [Tb|] eqn:Hb.
    2:{ discriminate Hty. }
    injection Hty as HT. rewrite <- HT. simpl.
    destruct (String.eqb y x) eqn:Hyx.
    + rewrite (eqb_true y x Hyx) in Hb.
      assert (Hbody := weakening (shadowing_included_in Γ x T U) Hb).
      rewrite (eqb_true y x Hyx). rewrite Hbody. reflexivity.
    + assert (Hneq : x = y -> False).
      { intros Exy. rewrite Exy in Hyx. rewrite eqb_refl in Hyx. discriminate Hyx. }
      assert (Hbody := weakening (map_permutation_included_in Γ x y T U Hneq) Hb).
      rewrite (IH (map_set Γ y U) T Tb Hbody Hs). reflexivity.
  - simpl in *. exact Hty.
  - simpl in *. exact Hty.
  - apply infer_type_if_inv in Hty. destruct Hty as [Hc [Htb Hfb]].
    simpl. rewrite (IHt1 Γ T TyBool Hc Hs), (IHt2 Γ T T' Htb Hs), (IHt3 Γ T T' Hfb Hs),
      eq_ty_refl.
    reflexivity.
Qed.

Fixpoint eval_v4 (n : nat) (t : tm) : tm :=
  match n with
  | O => t
  | S n' =>
    match t with
    | tm_app t1 t2 =>
      match eval_v4 n' t1 with
      | tm_abs x _ body => eval_v4 n' (subst_v4 x t2 body)
      | _ => t
      end
    | tm_if c tb fb =>
      match eval_v4 n' c with
      | tm_true => eval_v4 n' tb
      | tm_false => eval_v4 n' fb
      | _ => t
      end
    | _ => t
    end
  end.

#[universes(collapse_sort_variables=yes)]
Theorem safety_v4 : forall (n : nat) (t : tm) (T : ty),
  infer_type map_empty t = Some T ->
  infer_type map_empty (eval_v4 n t) = Some T.
Proof.
  intros n. induction n as [|n IHn].
  - intros t T Hty. simpl. rewrite Hty. reflexivity.
  - intros t. destruct t as [y | t1 t2 | y U body | | | t1 t2 t3].
    all: intros T Hty.
    + simpl in Hty. discriminate Hty.
    + ltac1:(pose proof (infer_type_app_inv Hty) as Hty').
      destruct Hty' as [T1 [Ht1 Ht2]].
      simpl. destruct (eval_v4 n t1) as [?|? ?|x U body| | |? ? ?] eqn:E;
        rewrite ?Hty; try reflexivity.
      ltac1:(pose proof (IHn t1 _ Ht1) as Habs).
      rewrite E in Habs.
      destruct (infer_type_abs_inv Habs) as [HU Hbody]. subst U.
      apply IHn. apply subst_typing_v4 with (T := T1).
      * exact Hbody.
      * exact Ht2.
    + rewrite <- Hty. reflexivity.
    + rewrite <- Hty. reflexivity.
    + rewrite <- Hty. reflexivity.
    + ltac1:(pose proof ((infer_type_if_inv Hty)) as Hty').
      destruct Hty' as [Htycond [Hytb Htfb]].
      simpl. destruct (eval_v4 n t1); rewrite ?Hty; try reflexivity.
      * now apply IHn.
      * now apply IHn.
Qed.

