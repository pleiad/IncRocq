From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Unset Collapse Sorts ToType.

(* ------------------------------------------------------------------ *)
(* Example types used in the tests                                     *)
(* ------------------------------------------------------------------ *)

Inductive bool : Type := true | false.

MetaRocq Run (gen_icp_defs "bool").

Inductive nat : Type := O | S : nat -> nat.

MetaRocq Run (gen_icp_defs "nat").

(* ------------------------------------------------------------------ *)
(* Tests for icp_discriminate0                                  *)
(* ------------------------------------------------------------------ *)

(* bool: ctor vs ctor — annotate one side to force Inc sort *)
Goal true@{Inc;0} = false -> False.
intros H.
icp_discriminate0 None.
Show Proof.
Qed.

Goal false@{Inc;0} = true -> False.
intros H.
icp_discriminate0 None.
Qed.

(* bool: ctor vs hole — sort forced by the hole *)
Goal true = TODO bool -> False.
intros H.
icp_discriminate0 None.
Show Proof.
Qed.

Goal false = TODO bool -> False.
intros H.
icp_discriminate0 None.
Qed.

Goal TODO bool = true -> False.
intros H.
icp_discriminate0 None.
Qed.

Goal TODO bool = false -> False.
intros H.
icp_discriminate0 None.
Qed.

(* checking backtracking *)
Goal true@{Inc;Set} = true -> true@{Inc;Set} = false -> False.
intros H H2.
icp_discriminate0 None.
Show Proof.
Qed.

(* Checking with argument *)
Goal TODO bool = false -> False.
intros H.
icp_discriminate0 (Some 'H).
Qed.

(* Checking notation without arg *)
Goal TODO bool = false -> False.
intros H.
icp_discriminate.
Show Proof.
Qed.

(* Checking notation with arg *)
Goal TODO bool = false -> False.
intros H.
icp_discriminate H.
Show Proof.
Qed.

(* nat: ctor vs ctor — annotate one side to force Inc sort *)
Goal forall n, O@{Inc;Set} = S n -> False.
intros n H.
icp_discriminate0 None.
Show Proof.
Qed.

Goal forall n, S@{Inc;Set} n = O -> False.
intros n H.
icp_discriminate0 None.
Qed.

(* nat: ctor vs hole *)
Goal O = TODO nat -> False.
intros H.
icp_discriminate0 None.
Show Proof.
Qed.

Goal forall n, S n = TODO nat -> False.
intros n H.
icp_discriminate0 None.
Qed.

(* nat: hole vs ctor *)
Goal TODO nat = O -> False.
intros H.
icp_discriminate0 None.
Qed.

Goal forall n, TODO nat = S n -> False.
intros n H.
icp_discriminate0 None.
Qed.

(* ------------------------------------------------------------------ *)
(* Tests for backtracking intros (icp_discriminate without intros)     *)
(* ------------------------------------------------------------------ *)

(* Equality behind an arrow: no prior intros needed *)
Goal true@{Inc;Set} = false -> False.
icp_discriminate.
Qed.

Goal forall n, O@{Inc;Set} = S n -> False.
icp_discriminate.
Qed.

(* Failure should leave no intros behind *)
Goal true@{Inc;Set} = true -> False.
Fail icp_discriminate.
Abort.

(* ------------------------------------------------------------------ *)
(* Parameterized inductives                                            *)
(* ------------------------------------------------------------------ *)

Inductive option@{s;u} (A : Type@{s;u}) : Type@{s;u} :=
| None : option A
| Some : A -> option A.

Arguments None {A}.
Arguments Some {A}.

MetaRocq Run (gen_icp_defs "option").

(* option: ctor vs ctor *)
Goal @None nat = @Some nat O -> False.
intros H. icp_discriminate. Show Proof. Qed.

Goal forall (A : Type) (a : A), None = Some a -> False.
intros A a H. icp_discriminate. Show Proof. Qed.

Goal @Some nat O = @None nat -> False.
intros H. icp_discriminate. Qed.

(* option: ctor vs hole *)
Goal @None nat = TODO (option nat) -> False.
intros H. icp_discriminate. Qed.

Goal @Some nat O = TODO (option nat) -> False.
intros H. icp_discriminate. Qed.

(* option: hole vs ctor *)
Goal TODO (option nat) = @None nat -> False.
intros H. icp_discriminate. Qed.

Goal TODO (option nat) = @Some nat O -> False.
intros H. icp_discriminate. Qed.

(* option: backtracking intro *)
Goal @None nat = @Some nat O -> False.
icp_discriminate. Qed.

Goal forall (A : Type) (a : A), None = Some a -> False.
icp_discriminate. Qed.

(* option: icp_discriminate skips non-constructor hypothesis and finds the discriminable one.
   H1 : None = x  (x is a variable, not a ctor/hole — must be skipped with Control.zero)
   H2 : None = Some O  (discriminable)                                                       *)
Goal forall (x : option nat), None = x -> None = @Some nat O -> False.
intros x H1 H2. icp_discriminate. Qed.

Inductive list@{s;u} (A : Type@{s;u}) : Type@{s;u} :=
| nil  : list A
| cons : A -> list A -> list A.

Arguments nil  {A}.
Arguments cons {A}.

MetaRocq Run (gen_icp_defs "list").

(* list: ctor vs ctor *)
Goal @nil nat = @cons nat O nil -> False.
intros H. icp_discriminate. Qed.

Goal @cons nat O nil = @nil nat -> False.
intros H. icp_discriminate. Qed.

(* list: ctor vs hole *)
Goal @nil nat = TODO (list nat) -> False.
intros H. icp_discriminate. Qed.

Goal @cons nat O nil = TODO (list nat) -> False.
intros H. icp_discriminate. Qed.

(* list: hole vs ctor *)
Goal TODO (list nat) = @nil nat -> False.
intros H. icp_discriminate. Qed.

(* ------------------------------------------------------------------ *)
(* Types without a catch symbol                                        *)
(* ------------------------------------------------------------------ *)

(* An inductive that never went through [gen_icp_defs] has no catch symbol.
   The catch-based tactics then fail like any other tactic, so [try] and
   [icp_solve] leave the goal as they found it. *)
Inductive plain : Type := pa | pb.

Goal pa = pb -> pa = pa.
Proof. try (icp_discriminate). icp_solve. intros _. reflexivity. Qed.

(* [icp_destruct] runs [icp_solve] on both branches, and each branch carries an
   equality over [plain] in its premise. *)
Goal forall p : plain, p = pa -> p = p.
Proof. intros p. icp_destruct p; intros _; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Reference: proof term from standard (match-based) discriminate      *)
(* ------------------------------------------------------------------ *)

(* Check (fun H : true = false => *)
(*  let H0 : False := *)
(*    eq_ind true *)
(*      (fun e : bool => match e with true => True | false => False end) *)
(*      I false H in *)
(*  False_ind False H0). *)
