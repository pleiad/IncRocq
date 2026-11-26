From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* Example type used in the examples                                   *)
(* ------------------------------------------------------------------ *)

(* The scaffold is EqMono.v's, since the two tactics split the same goal shape
   between them: plain [reflexivity] takes the sides that are already
   convertible, [icp_eq_mono] the ones a merge has to reconcile. The fill
   guard on [icp_eq_mono] keeps the two apart. *)

Inductive nat : Type := O | S : nat -> nat.
(* The refinement relation is the computational one below, so the structural
   relation of gen_icp_defs is not declared. *)
MetaRocq Run (generate_catch "nat").
MetaRocq Run (generate_hole_match_rule "nat").
MetaRocq Run (gen_complete "nat").

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
  intros n1 n2 n3. revert n2 n1.
  induction n3 using nat_catch; intros n2;
    induction n2 using nat_catch; intros n1;
    (induction n1 using nat_catch; cbn; intros H1 H2);
    first [ exact I | exact H1 | exact H2 | exact (IHn3 _ _ H1 H2)
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

(* One branch incomplete, standing in for the case studies' [add_v1]. *)
Definition add_partial (n m : nat) : nat :=
  match n with O => m | S _ => ??? end.

(* ------------------------------------------------------------------ *)
(* Sides differing only in their holes                                 *)
(* ------------------------------------------------------------------ *)

(* The fill sits at the root, where one side is nothing but a hole and the other
   a constructor over one. This is [add_succ_r_v0] in the case study, where the
   common refinement [S ???] used to be written out by hand. *)
Goal ??? ≈ S ???.
Proof. icp_eq_mono. Qed.

(* The same shape reached through the programs rather than written out, so the
   holes only surface once both sides are reduced. This is the [S] case of
   [add_succ_r_v1]. *)
Goal forall (n m : nat@{Inc;}),
  add_partial (S n) (S m) ≈ S (add_partial (S n) m).
Proof. icp_eq_mono. Qed.

(* The fill is under a constructor, so the merge descends and the witness is the
   complete side. The half [S (S O) ⊑ S ???] is then deeper than one layer,
   which is why the halves go to [icp_close_gap] and not to a flat solver. *)
Goal S ??? ≈ S (S O).
Proof. icp_eq_mono. Qed.

(* Behind binders and the completeness conjunction [icp_reform] leaves in the
   premise, as after [icp_reform] and [icp_induction]. The notation backtracks
   on [icp_intro_step], which splits that conjunction as it goes. *)
Goal forall (n : nat@{Inc;}),
  is_complete n /\ n = n -> ??? ≈ S ???.
Proof. icp_eq_mono. Qed.

(* ------------------------------------------------------------------ *)
(* The fill guard                                                      *)
(* ------------------------------------------------------------------ *)

(* Sides that merge without filling anything. The merge succeeds and returns
   [???], but no hole ever faced real structure, so the goal is trivial by
   reflexivity rather than by incompleteness and the guard refuses it. *)
Goal ??? ≈ ???.
Proof. Fail icp_eq_mono. reflexivity. Qed.

(* Same, with no hole in sight. Both sides compute to [S n]. Refusing this one
   is what keeps [icp_solve] off goals about complete code. *)
Goal forall (n : nat@{Inc;}),
  add O (S n) ≈ S (add O n).
Proof.
  Fail icp_eq_mono.
  (* The failure rolled every introduction back, so the binder is still there. *)
  intros n. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Negative cases                                                      *)
(* ------------------------------------------------------------------ *)

(* No common refinement, since the sides differ where neither of them is a
   hole. *)
Goal forall (n : nat@{Inc;}), S n ≈ S (S n).
Proof. Fail icp_eq_mono. intros n. Abort.

(* The branch that genuinely needs the induction hypothesis. With [n] a
   variable both sides are stuck, on a [match] and on [S] respectively, so they
   have no common refinement and the tactic leaves the goal alone. *)
Goal forall (n m : nat@{Inc;}),
  add_partial n (S m) ≈ S (add_partial n m).
Proof. Fail icp_eq_mono. Abort.

(* Not a monotone equality goal at all. *)
Goal forall (n : nat@{Inc;}), n ⊑ ???.
Proof. intros n. Fail icp_eq_mono. icp_hole_refinement. Qed.

(* An existential, but not the sealed one. *)
Goal exists b : nat@{Inc;}, b = O.
Proof. Fail icp_eq_mono. exists O. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Together with icp_solve                                             *)
(* ------------------------------------------------------------------ *)

(* The case-study goal disappears into [icp_solve], and with it into
   [icp_induction], instead of asking for a hand-written witness. *)
Goal forall (n m : nat@{Inc;}),
  add_stub n (S m) ≈ S (add_stub n m).
Proof. icp_solve. Qed.

(* [icp_induction] closes the [S] branch on its own and leaves the [O] branch,
   which is [reflexivity]'s. *)
Goal forall (n m : nat@{Inc;}),
  add_partial n (S m) ≈ S (add_partial n m).
Proof.
  intros n; icp_induction n.
  - intros m. reflexivity.
Qed.

(* A goal the guard refuses is left untouched by [icp_solve], introductions
   included, so the binder is still there afterwards. Plain [reflexivity]
   introduces nothing, so the binder is the user's to take. *)
Goal forall (n : nat@{Inc;}),
  add O (S n) ≈ S (add O n).
Proof.
  icp_solve.
  intros n. reflexivity.
Qed.
