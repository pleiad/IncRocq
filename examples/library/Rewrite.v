From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* Example type used in the examples                                   *)
(* ------------------------------------------------------------------ *)

(* The tests need a type with a refinement order and the [Complete] instance
   that [ir_mono] and [≈̇] take. The structural ones of gen_icp_defs do. *)

Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (gen_icp_defs "nat").

(* ------------------------------------------------------------------ *)
(* eqm_congr_k                                                         *)
(* ------------------------------------------------------------------ *)

Lemma congr_2_direct : forall (g : nat -> nat -> nat) (e1 v1 e2 v2 r : nat),
  g v1 v2 = r -> e1 ≈ v1 -> e2 ≈ v2 -> g e1 e2 ≈ r.
Proof. intros g e1 v1 e2 v2 r Hr H1 H2. exact (eqm_congr_2 g Hr H1 H2). Qed.

(* ------------------------------------------------------------------ *)
(* icp_rewrite with monotone equalities                                *)
(* ------------------------------------------------------------------ *)

(* One hypothesis, under a match. *)
Lemma rewrite_one : forall (f : nat -> nat) (a : nat), f a ≈ S O ->
  match f a with O => O | S _ => S (S O) end ≈ S (S O).
Proof. intros f a H. icp_rewrite H. reflexivity. Qed.

(* Two hypotheses, the second one under a branch of the first match. *)
Lemma rewrite_batch : forall (f : nat -> nat) (a b : nat), f a ≈ S O -> f b ≈ O ->
  match f a with S _ => match f b with O => S (S O) | S _ => O end | O => O end ≈ S (S O).
Proof. intros f a b H1 H2. icp_rewrite H1, H2. reflexivity. Qed.

(* Every occurrence on the left-hand side is replaced. *)
Lemma rewrite_repeated : forall (g : nat -> nat -> nat) (f : nat -> nat) (a : nat),
  f a ≈ O -> g (f a) (f a) ≈ g O O.
Proof. intros g f a H. icp_rewrite H. reflexivity. Qed.

Lemma rewrite_three : forall (g : nat -> nat -> nat -> nat) (f : nat -> nat) (a b c : nat),
  f a ≈ O -> f b ≈ S O -> f c ≈ S (S O) -> g (f a) (f b) (f c) ≈ g O (S O) (S (S O)).
Proof. intros g f a b c Ha Hb Hc. icp_rewrite Ha, Hb, Hc. reflexivity. Qed.

Lemma rewrite_five : forall (g : nat -> nat -> nat -> nat -> nat -> nat) (f : nat -> nat)
  (a b c d e : nat), f a ≈ O -> f b ≈ O -> f c ≈ O -> f d ≈ O -> f e ≈ O ->
  g (f a) (f b) (f c) (f d) (f e) ≈ g O O O O O.
Proof.
  intros g f a b c d e Ha Hb Hc Hd He. icp_rewrite Ha, Hb, Hc, Hd, He. reflexivity.
Qed.

(* Only the left-hand side is rewritten. The right-hand side keeps [f a]. *)
Lemma rewrite_lhs_only : forall (f : nat -> nat) (a : nat), f a ≈ O ->
  S (f a) ≈ S (f a).
Proof.
  intros f a H. icp_rewrite H.
  change (S O = S (f a)).
Abort.

(* A term that occurs on the right-hand side only is rewritten there. *)
Lemma rewrite_symmetric : forall (f : nat -> nat) (a : nat), f a ≈ O ->
  S O ≈ S (f a).
Proof. intros f a H. icp_rewrite H. reflexivity. Qed.

(* The equation keeps the orientation of the goal, as with [rewrite]. *)
Lemma rewrite_symmetric_orientation : forall (f : nat -> nat) (a : nat), f a ≈ O ->
  O ≈ S (f a).
Proof.
  intros f a H. icp_rewrite H.
  change (O = S O).
Abort.

(* A hypothesis whose type is still folded, as [icp_reform] can leave it. *)
Lemma rewrite_folded : forall (f : nat -> nat) (a : nat),
  @ir_mono _ _ _ (fun _ : nat => f a ≈ S O) _ O ->
  match f a with O => O | S _ => S (S O) end ≈ S (S O).
Proof. intros f a H. icp_rewrite H. reflexivity. Qed.

(* Hypotheses can be applied terms, as induction hypotheses usually are. *)
Lemma rewrite_applied_terms : forall (f : nat -> nat), (forall x, f x ≈ O) ->
  forall a b, match f a with O => f b | S _ => S O end ≈ O.
Proof. intros f H a b. icp_rewrite (H a), (H b). reflexivity. Qed.

(* [≈] is not transitive, so the monotone equalities that close a goal go in
   one call. Rewriting with one of them leaves an equation, which the other
   one cannot rewrite. *)
Lemma rewrite_sequential_refused : forall (f : nat -> nat) (a b : nat),
  f a ≈ S O -> f b ≈ O ->
  match f a with S _ => match f b with O => S (S O) | S _ => O end | O => O end ≈ S (S O).
Proof.
  intros f a b H1 H2.
  Fail (icp_rewrite H1; icp_rewrite H2).
  icp_rewrite H1, H2. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* icp_rewrite with equations                                          *)
(* ------------------------------------------------------------------ *)

(* With no monotone equality involved, [icp_rewrite] is [rewrite]. *)
Lemma rewrite_eq_fallback : forall (a b : nat), a = b -> S a = S b.
Proof. intros a b H. icp_rewrite H. reflexivity. Qed.

Lemma rewrite_eq_on_eqm : forall (a b : nat), a = b -> S a ≈ S b.
Proof. intros a b H. icp_rewrite H. reflexivity. Qed.

(* An equation listed before the monotone equalities is rewritten before them. *)
Lemma rewrite_mixed : forall (f : nat -> nat) (a b : nat), a = b -> f b ≈ O ->
  S (f a) ≈ S O.
Proof. intros f a b He Hm. icp_rewrite He, Hm. reflexivity. Qed.

(* An equation listed after the monotone equalities rewrites the equation they
   leave, so it can rewrite a term that only they put in the goal. *)
Lemma rewrite_eq_after : forall (g f : nat -> nat) (a : nat), f a ≈ O -> g O = S O ->
  g (f a) ≈ S O.
Proof. intros g f a Hm He. icp_rewrite Hm, He. reflexivity. Qed.

(* A quantified equation goes to [rewrite] as it is. *)
Lemma rewrite_quantified_eq : forall (f : nat -> nat) (a : nat), (forall x, f x = x) ->
  S (f a) ≈ S a.
Proof. intros f a H. icp_rewrite H. reflexivity. Qed.

(* An antitone-equality counts as an equation. *)
Lemma rewrite_eq_anti : forall (a b : nat), a ≈̇ b -> S a ≈ S b.
Proof. intros a b H. icp_rewrite H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Failures                                                            *)
(* ------------------------------------------------------------------ *)

Lemma rewrite_absent : forall (f : nat -> nat) (a b : nat), f a ≈ O -> S b ≈ S b.
Proof. intros f a b H. Fail icp_rewrite H. reflexivity. Qed.

Lemma rewrite_split_sides : forall (f : nat -> nat) (a b : nat), f a ≈ O -> f b ≈ O ->
  S (f a) ≈ S (f b).
Proof. intros f a b H1 H2. Fail icp_rewrite H1, H2. Abort.

(* The monotone equalities are rewritten together, so an equation cannot go
   between two of them. *)
Lemma rewrite_eq_between : forall (g : nat -> nat -> nat) (f : nat -> nat) (a b c : nat),
  f a ≈ O -> b = c -> f c ≈ O -> g (f a) (f b) ≈ g O O.
Proof.
  intros g f a b c H1 He H2. Fail icp_rewrite H1, He, H2.
  icp_rewrite He, H1, H2. reflexivity.
Qed.

Lemma rewrite_duplicate_lhs : forall (f : nat -> nat) (a : nat), f a ≈ O -> f a ≈ S O ->
  S (f a) ≈ S O.
Proof. intros f a H1 H2. Fail icp_rewrite H1, H2. Abort.

Lemma rewrite_not_an_equation : forall (a : nat), a ⊑ O -> S a ≈ S a.
Proof. intros a H. Fail icp_rewrite H. reflexivity. Qed.

(* A monotone equality under binders has to be instantiated first. *)
Lemma rewrite_quantified_mono : forall (f : nat -> nat) (a : nat), (forall x, f x ≈ O) ->
  S (f a) ≈ S O.
Proof. intros f a H. Fail icp_rewrite H. icp_rewrite (H a). reflexivity. Qed.

(* The call fails rather than leave a listed hypothesis unused. Abstracting
   [f a] together with [g (f a)] leaves nothing of one of them to rewrite, in
   either order. *)
Lemma rewrite_nested_refused : forall (g f : nat -> nat) (a : nat),
  f a ≈ O -> g (f a) ≈ S O -> S (g (f a)) ≈ S (S O).
Proof. intros g f a H1 H2. Fail icp_rewrite H2, H1. Fail icp_rewrite H1, H2. Abort.
