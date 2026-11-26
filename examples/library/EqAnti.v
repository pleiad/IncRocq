From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* Example types used in the examples                                  *)
(* ------------------------------------------------------------------ *)

Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (gen_icp_defs "nat").

Fixpoint dbl (n : nat) : nat :=
  match n with O => O | S p => S (S (dbl p)) end.

(* ------------------------------------------------------------------ *)
(* The relation                                                        *)
(* ------------------------------------------------------------------ *)

(* Symmetric, which is what makes provability independent of which side of [=]
   the function was written on.                                          *)
Goal forall (n m : nat@{Inc;}), dbl n ≈̇ m -> m ≈̇ dbl n.
Proof. intros n m H. symmetry. exact H. Qed.

Goal forall (n m k : nat@{Inc;}), n ≈̇ m -> m ≈̇ k -> n ≈̇ k.
Proof. intros n m k H1 H2. etransitivity. exact H1. exact H2. Qed.

(* Not reflexive.  [a ≈̇ a] holds exactly when [a] is complete, so [eq_anti] is a
   PER and not an equivalence, and no [Reflexive] instance is declared.    *)
Lemma eqa_not_reflexive : @eq_anti nat _ ??? ??? -> False.
Proof. intros H. exact (hole_not_complete (eqa_complete_l H)). Qed.

Goal forall (n : nat@{Inc;}), n ≈̇ n.
Proof. intros n. Fail reflexivity. Abort.

Goal forall (n : nat@{Inc;}), is_complete n -> n ≈̇ n.
Proof. intros n Hc. exact (eqa_refl Hc). Qed.

(* ------------------------------------------------------------------ *)
(* The motivating shape                                                *)
(* ------------------------------------------------------------------ *)

(* What [icp_reform] leaves of an inductive hypothesis.  The premise is a
   antitone-equality, so supplying it means supplying both the completeness half and
   the half that is the actual content.  Compare [add_inv_r_v1] in
   examples/comp/Nat.v.                                                   *)
Goal forall (n m : nat@{Inc;}),
  is_complete m ->
  (forall k, dbl k ≈̇ m -> k = O) ->
  dbl n = m ->
  n = O.
Proof.
  intros n m Hc IH Heq.
  icp_apply IH.
  exact Heq.
Qed.

(* The evidence does not have to be in the context. Here the database builds it
   from the constructor [complete_O].                                            *)
Goal forall (n : nat@{Inc;}),
  (forall k, dbl k ≈̇ O -> k = O) ->
  dbl n = O ->
  n = O.
Proof.
  intros n IH Heq.
  icp_apply IH.
  exact Heq.
Qed.

(* ------------------------------------------------------------------ *)
(* The residual is left alone, even when automation could close it      *)
(* ------------------------------------------------------------------ *)

(* [Heq] proves the residual and sits in the context.  Deciding what to hand to
   the database by outcome rather than by shape would close it here, because
   [auto] tries [assumption] before consulting any database.  Only the
   completeness half of the antitone-equality goes to [icp], so the residual
   survives and [exact Heq] has a goal to close.                           *)
Goal forall (n m : nat@{Inc;}),
  dbl n = m ->
  is_complete m ->
  (dbl n ≈̇ m -> m = m) ->
  m = m.
Proof.
  intros n m Heq Hc h.
  icp_apply h.
  exact Heq.
Qed.

(* Several premises, only one of which is an antitone-equality.  The sweep runs back
   to front for index stability, so this checks that the subgoals still come out
   in [apply]'s order.                                                     *)
Goal forall (n m : nat@{Inc;}),
  dbl n = m ->
  is_complete m ->
  ((n = n) -> (dbl n ≈̇ m) -> m = m) ->
  m = m.
Proof.
  intros n m H1 Hc h.
  icp_apply h.
  - reflexivity.
  - exact H1.
Qed.

(* ------------------------------------------------------------------ *)
(* A premise that arrives folded                                       *)
(* ------------------------------------------------------------------ *)

(* [ir_anti P m] has not been reduced by [icp_reform] here, so the [≈̇] is not
   yet visible.  The tactic reduces each subgoal with [reform_flags] first,
   which unfolds the [IncRef] projections and instances and nothing else.
   [eq_anti] stays folded, and the residual is the user's own [dbl m = O].   *)
Goal forall (m : nat@{Inc;}),
  dbl m = O ->
  (ir_anti (fun a : nat => dbl a = O) m -> m = m) ->
  m = m.
Proof.
  intros m Hd h.
  icp_apply h.
  exact Hd.
Qed.

(* ------------------------------------------------------------------ *)
(* An antitone-equality in the conclusion                             *)
(* ------------------------------------------------------------------ *)

(* [≈̇] is handled in both positions: the goal is opened the same way before [h]
   is applied, so the user never builds one by hand.                       *)
Goal forall (n : nat@{Inc;}),
  is_complete n ->
  dbl n = n ->
  dbl n ≈̇ n.
Proof.
  intros n Hc Heq.
  icp_apply Heq.
Qed.

(* ------------------------------------------------------------------ *)
(* No antitone-equality anywhere: exactly [apply]                     *)
(* ------------------------------------------------------------------ *)

(* Whether a premise carries a [≈̇] depends on which [IncRef] instance fired,
   which a proof script should not have to know, so the tactic degrades into
   [apply] rather than failing. *)
Goal forall (n : nat@{Inc;}), (n = n -> n = O) -> n = O.
Proof.
  intros n h.
  icp_apply h. reflexivity.
Qed.

Goal forall (n : nat@{Inc;}), (n = O) -> n = O.
Proof.
  intros n h.
  icp_apply h.
Qed.

(* ------------------------------------------------------------------ *)
(* Failure leaves the goal untouched                                   *)
(* ------------------------------------------------------------------ *)

(* The obligation is false on both sides, since [TODO nat] is complete for no
   type and [n] is a variable.  The tactic fails and rolls the [apply] back,
   rather than leaving a hypothesis applied with an open [≈̇] leaf.         *)
Goal forall (n : nat@{Inc;}), ((??? : nat) ≈̇ n -> n = n) -> n = n.
Proof.
  intros n h.
  Fail icp_apply h.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* A type that registers no hints of its own                          *)
(* ------------------------------------------------------------------ *)

(* [color] has the [Complete] instance gen_icp_defs declares, and no [icp]
   hints. The generic [complete_constructor] hint builds the evidence from
   [complete_red]. *)
Module NoHint.
  Inductive color : Type := red | green.
  MetaRocq Run (gen_icp_defs "color").

  Goal forall (c : color@{Inc;}), (red ≈̇ red -> c = c) -> c = c.
  Proof.
    intros c h.
    icp_apply h.
    reflexivity.
  Qed.
End NoHint.
