From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Unset Collapse Sorts ToType.

Inductive bool : Type := true | false.
MetaRocq Run (gen_icp_defs "bool").

(* ------------------------------------------------------------------ *)
(* Inductive with a hole-indexed constructor, used throughout          *)
(* ------------------------------------------------------------------ *)

(* A type whose only constructor witnesses a hole index *)
Inductive IsHole : bool -> Type :=
  | is_hole_ctor : IsHole (TODO bool).

(* ------------------------------------------------------------------ *)
(* Test 1 (tracer bullet): icp_inversion H — every branch is a hole   *)
(* ------------------------------------------------------------------ *)

(* inversion on H : IsHole true gives one subgoal: true = TODO bool,
   which icp_discriminate closes.                                       *)
Goal IsHole true -> False.
intros H.
icp_inversion H.
Qed.

(* ------------------------------------------------------------------ *)
(* Test 2: numeric form icp_inversion 1                                *)
(* ------------------------------------------------------------------ *)

(* Same goal without prior intros — the premise is the 1st forall binder *)
Goal IsHole true -> False.
icp_inversion 1.
Qed.

(* ------------------------------------------------------------------ *)
(* Test 3: non-contradictory subgoal is left open                      *)
(* ------------------------------------------------------------------ *)

(* inversion on H : IsHole (TODO bool) gives one case (is_hole_ctor)
   which is NOT contradictory, so icp_discriminate leaves the remaining
   goal for the user.                                                   *)
Goal IsHole (TODO bool) -> True.
intros H.
icp_inversion H.
trivial.
Qed.
