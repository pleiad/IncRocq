From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* Example types used in the examples                                  *)
(* ------------------------------------------------------------------ *)

Inductive bool : Type := true | false.
MetaRocq Run (gen_icp_defs "bool").

Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (gen_icp_defs "nat").

(* The completeness predicates and the CompleteMinimal instances come from
   gen_icp_defs. Only the constructors are complete, [TODO T] is not.  The
   [hole_not_complete] field of each instance is what [icp_absurd_complete]
   refutes a hole with. *)

(* Incomplete programs, standing in for the case studies' [add_v0] & co. *)

(* Fully incomplete: the hole is behind a delta step only. *)
Definition stub (b : bool) : bool := ???.

Definition neg (b : bool) : bool :=
  match b with true => false | false => true end.

(* Here the hole only surfaces after the hole propagation rewrite rule fires
   on [neg]'s match — the shape neither [hnf] nor unification reaches.     *)
Definition deep (b : bool) : bool := neg ???.

Fixpoint dbl (n : nat) : nat :=
  match n with O => O | S p => S (S (dbl p)) end.

(* ------------------------------------------------------------------ *)
(* The completeness hypothesis is already headed by a hole               *)
(* ------------------------------------------------------------------ *)

(* No rewriting needed: the argument is literally [TODO bool]. *)
Goal @is_complete bool _ ??? -> False.
Proof. intros Hc. icp_absurd_complete. Qed.

(* Same, with a conclusion that is not [False]: the tactic does its own
   [exfalso].                                                            *)
Goal forall (b : bool@{Inc;}), @is_complete bool _ ??? -> b = true.
Proof. intros b Hc. icp_absurd_complete. Qed.

(* ------------------------------------------------------------------ *)
(* The hole is reached by rewriting with a context equality            *)
(* ------------------------------------------------------------------ *)

(* The motivating shape: [Hc] assumes a value complete, while [Heq] says that
   value is what a fully incomplete program computes.  Needs the RTL
   orientation — [b] is replaced by [stub b], not the other way round.   *)
Goal forall (b : bool@{Inc;}), is_complete b -> stub b = b -> False.
Proof. intros b Hc Heq. icp_absurd_complete. Qed.

(* The mirrored equation, closed by the LTR orientation. *)
Goal forall (b : bool@{Inc;}), is_complete b -> b = stub b -> False.
Proof. intros b Hc Heq. icp_absurd_complete. Qed.

(* Non-[False] conclusion again, this time via a rewrite. *)
Goal forall (b : bool@{Inc;}), is_complete b -> stub b = b -> b = neg b.
Proof. intros b Hc Heq. icp_absurd_complete. Qed.

(* The completeness argument is a compound term, not a variable — the
   hypothesis is located by type, so its shape does not matter.          *)
Goal forall (n : nat@{Inc;}), is_complete (S n) -> dbl n = S n -> False.
Proof.
  intros n Hc Heq.
  (* [dbl n] does not reduce to a hole, so this one is NOT provable this way *)
  Fail icp_absurd_complete.
Abort.

Goal forall (n : nat@{Inc;}), is_complete (S n) -> ??? = S n -> False.
Proof. intros n Hc Heq. icp_absurd_complete. Qed.

(* ------------------------------------------------------------------ *)
(* The hole only appears after the rewrite rules fire                  *)
(* ------------------------------------------------------------------ *)

(* [deep b] is [neg (TODO bool)]: exposing the hole needs the generated
   hole propagation rule, which plain unification never triggers.  This is
   why the tactic reduces the hypothesis in place instead of leaving the
   the hole to be discovered by the hint's unification.                    *)
Goal forall (b : bool@{Inc;}), is_complete b -> deep b = b -> False.
Proof. intros b Hc Heq. icp_absurd_complete. Qed.

(* ------------------------------------------------------------------ *)
(* Backtracking                                                        *)
(* ------------------------------------------------------------------ *)

(* Several equations in context: the irrelevant one comes first, so the
   equation [match!] must backtrack past it.                             *)
Goal forall (b c : bool@{Inc;}),
  is_complete b -> neg c = c -> stub b = b -> False.
Proof. intros b c Hc Hirrelevant Heq. icp_absurd_complete. Qed.

(* Several completeness hypotheses: the satisfiable one comes first, so the
   hypothesis [match!] must backtrack past it too.                        *)
Goal forall (b c : bool@{Inc;}),
  is_complete c -> is_complete b -> stub b = b -> False.
Proof. intros b c Hsat Hc Heq. icp_absurd_complete. Qed.

(* Both at once. *)
Goal forall (b c : bool@{Inc;}),
  is_complete c -> is_complete b -> neg c = c -> stub b = b -> False.
Proof. intros b c Hsat Hc Hirrelevant Heq. icp_absurd_complete. Qed.

(* ------------------------------------------------------------------ *)
(* Failure leaves the context untouched                                *)
(* ------------------------------------------------------------------ *)

(* [neg b] never reduces to a hole, so every rewrite attempted here is rolled
   back.  [exact Hc] then only typechecks if [Hc] is still [is_complete b]
   rather than the rewritten [is_complete (neg b)].                      *)
Goal forall (b : bool@{Inc;}), is_complete b -> neg b = b -> is_complete b.
Proof.
  intros b Hc Heq.
  Fail icp_absurd_complete.
  exact Hc.
Qed.

(* ------------------------------------------------------------------ *)
(* Negative cases                                                      *)
(* ------------------------------------------------------------------ *)

(* No completeness hypothesis at all. *)
Goal forall (b : bool@{Inc;}), b = b.
Proof. intros b. Fail icp_absurd_complete. reflexivity. Qed.

(* A completeness hypothesis, but no equation to rewrite with. *)
Goal forall (b : bool@{Inc;}), is_complete b -> b = b.
Proof. intros b Hc. Fail icp_absurd_complete. reflexivity. Qed.

(* An equation, but rewriting with it exposes no hole. *)
Goal forall (b : bool@{Inc;}), is_complete b -> neg b = b -> b = b.
Proof. intros b Hc Heq. Fail icp_absurd_complete. reflexivity. Qed.

(* A genuinely complete value: refuting it would be unsound. *)
Goal @is_complete bool _ true -> False.
Proof. intros Hc. Fail icp_absurd_complete. Abort.

(* ------------------------------------------------------------------ *)
(* A type without a CompleteMinimal instance                           *)
(* ------------------------------------------------------------------ *)

(* [color] is declared without gen_complete_minimal, so it has a [Complete]
   instance but no [CompleteMinimal] one, and there
   is no [hole_not_complete] field to refute the hypothesis with and the
   tactic fails, even though the hypothesis is just as contradictory as the
   [bool] ones above.  The refutation of a hole is a field, not a hint, and a
   type that wants the tactic declares the instance that carries it. *)
Module NoHint.
  Inductive color : Type := red | green.
  MetaRocq Run (generate_catch "color").
  MetaRocq Run (generate_hole_match_rule "color").
  MetaRocq Run (gen_complete "color").
  MetaRocq Run (gen_refinable "color").

  Goal @is_complete color _ ??? -> False.
  Proof.
    intros Hc.
    Fail icp_absurd_complete.
    (* Discharged by hand instead — the contradiction is real. *)
    icp_inversion Hc.
  Qed.
End NoHint.

(* ------------------------------------------------------------------ *)
(* Composition with icp_solve                                          *)
(* ------------------------------------------------------------------ *)

(* [icp_solve] gained [icp_absurd_complete] as its last branch, so it now
   closes goals that neither the refinement branch nor [icp_discriminate]
   can see.                                                              *)
Goal forall (b : bool@{Inc;}), is_complete b -> stub b = b -> False.
Proof. intros b Hc Heq. icp_solve. Qed.

(* And it stays silent on goals it cannot close, as before. *)
Goal forall (b : bool@{Inc;}), is_complete b -> neg b = b -> b = b.
Proof. intros b Hc Heq. icp_solve. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* icp_solve reaches the sealed premise on its own                      *)
(* ------------------------------------------------------------------ *)

(* This is the shape [icp_reform] leaves behind: the completeness assumption is
   sealed inside an antitone-equality, under binders, in the premise.
   [icp_absurd_complete] alone cannot see it, since it only looks at the
   context, and a plain [intro] backtrack would stop at the [≈̇] without opening
   it.  [icp_solve] gets there because it backtracks on [icp_intro_step], which
   unpacks the antitone-equality as it goes.                                 *)
Goal forall (b : bool@{Inc;}), stub b ≈̇ b -> False.
Proof. icp_solve. Qed.

(* The atom on its own is NOT enough for that shape — this is precisely the
   division of labour: the atom refutes, the wrapper introduces.          *)
Goal forall (b : bool@{Inc;}), stub b ≈̇ b -> False.
Proof. Fail icp_absurd_complete. icp_solve. Qed.

(* The premise introduced by hand, which is the shape a proof script has when it
   does not leave the introduction to [icp_solve].  The completeness is sealed
   inside the hypothesis rather than sitting in the context, and the atom
   projects it out itself.                                                 *)
Goal forall (b : bool@{Inc;}), stub b ≈̇ b -> False.
Proof. intros b H. icp_absurd_complete. Qed.

(* The incomplete side on the right, so the projection has to go through
   [eqa_complete_r].                                                    *)
Goal forall (b : bool@{Inc;}), b ≈̇ stub b -> False.
Proof. intros b H. icp_absurd_complete. Qed.

(* A projection that does not end in a refutation is rolled back, so a failed
   attempt leaves no hypothesis behind.                                    *)
Goal forall (b : bool@{Inc;}), b ≈̇ b -> False.
Proof.
  intros b H. Fail icp_absurd_complete.
  Fail (match! goal with [ _ : is_complete _ |- _ ] => () end).
Abort.

(* Several binders before the premise, and a non-[False] conclusion. *)
Goal forall (b c : bool@{Inc;}), stub b ≈̇ c -> b = neg c.
Proof. icp_solve. Qed.

(* Same for the [nat] side, with a compound value on the right. *)
Goal forall (n : nat@{Inc;}), ??? ≈̇ S n -> n = O.
Proof. icp_solve. Qed.

(* ------------------------------------------------------------------ *)
(* ...but only when incompleteness is what makes the goal go through    *)
(* ------------------------------------------------------------------ *)

(* [neg] is complete, so this conjunction is perfectly satisfiable and
   [icp_solve] must leave the goal alone. The [intros] afterwards is the check:
   it would fail with "No more goals" had [icp_solve] closed anything, and its
   pattern would fail had [icp_solve] left introductions behind.          *)
Goal forall (b : bool@{Inc;}), is_complete b /\ neg b = b -> b = b.
Proof.
  icp_solve.
  intros b [Hc Heq].
  reflexivity.
Qed.

(* Same check with the [nat] fixpoint: nothing incomplete, nothing closed. *)
Goal forall (n : nat@{Inc;}), is_complete n /\ dbl n = n -> n = n.
Proof.
  icp_solve.
  intros n [Hc Heq].
  reflexivity.
Qed.
