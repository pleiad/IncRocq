From Prelude Require Import Logic Datatypes.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

#[local] Open Scope lazy_bool_scope.

Inductive ascii : Type :=
    Ascii : bool ->
            bool ->
            bool ->
            bool ->
            bool ->
            bool -> bool -> bool -> ascii.

Declare Scope char_scope.
Delimit Scope char_scope with char.
Bind Scope char_scope with ascii.

Definition ascii_eqb (a b : ascii) : bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    eqb_bool a0 b0 &&& eqb_bool a1 b1 &&& eqb_bool a2 b2 &&& eqb_bool a3 b3
    &&& eqb_bool a4 b4 &&& eqb_bool a5 b5 &&& eqb_bool a6 b6 &&& eqb_bool a7 b7
 end.

Infix "=?" := ascii_eqb (at level 70, no associativity): char_scope.

Inductive string : Type :=
  | EmptyString : string
  | String : ascii -> string -> string.

Declare Scope string_scope.
Delimit Scope string_scope with string.
Bind Scope string_scope with string.
#[local] Open Scope string_scope.

Fixpoint eqb s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => ascii_eqb c1 c2 &&& eqb s1' s2'
 | _,_ => false
 end.

Infix "=?" := eqb : string_scope.

Definition string_rect := string_poly_rec@{_ _ _ _ _ _ _ _ _ _ Type; _}.
Register Scheme string_rect as rect_dep for string.

(* Each equality test decides equality. The lemmas are stated at the ground
   sorts, so they do not apply to [Inc]-sorted strings. *)
Set Collapse Sorts ToType.

Lemma ascii_eqb_true : forall (a1 a2 : ascii), ascii_eqb a1 a2 = true -> a1 = a2.
Proof.
  intros a1 a2. destruct a1 as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct a2 as [c0 c1 c2 c3 c4 c5 c6 c7]. unfold ascii_eqb. intros H.
  assert (E0 := eqb_bool_true b0 c0). destruct (eqb_bool b0 c0). 2:{ discriminate H. }
  assert (E1 := eqb_bool_true b1 c1). destruct (eqb_bool b1 c1). 2:{ discriminate H. }
  assert (E2 := eqb_bool_true b2 c2). destruct (eqb_bool b2 c2). 2:{ discriminate H. }
  assert (E3 := eqb_bool_true b3 c3). destruct (eqb_bool b3 c3). 2:{ discriminate H. }
  assert (E4 := eqb_bool_true b4 c4). destruct (eqb_bool b4 c4). 2:{ discriminate H. }
  assert (E5 := eqb_bool_true b5 c5). destruct (eqb_bool b5 c5). 2:{ discriminate H. }
  assert (E6 := eqb_bool_true b6 c6). destruct (eqb_bool b6 c6). 2:{ discriminate H. }
  assert (E7 := eqb_bool_true b7 c7).
  rewrite (E0 eq_refl). rewrite (E1 eq_refl). rewrite (E2 eq_refl). rewrite (E3 eq_refl).
  rewrite (E4 eq_refl). rewrite (E5 eq_refl). rewrite (E6 eq_refl). rewrite (E7 H).
  reflexivity.
Qed.

Lemma ascii_eqb_refl : forall (a : ascii), ascii_eqb a a = true.
Proof.
  intros a. destruct a as [b0 b1 b2 b3 b4 b5 b6 b7]. unfold ascii_eqb.
  rewrite (eqb_bool_refl b0). rewrite (eqb_bool_refl b1). rewrite (eqb_bool_refl b2).
  rewrite (eqb_bool_refl b3). rewrite (eqb_bool_refl b4). rewrite (eqb_bool_refl b5).
  rewrite (eqb_bool_refl b6). exact (eqb_bool_refl b7).
Qed.

Lemma eqb_true : forall (s1 s2 : string), eqb s1 s2 = true -> s1 = s2.
Proof.
  intros s1. induction s1 as [|a s1 IH]; intros s2; destruct s2 as [|c s2]; simpl; intros H.
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - assert (E := ascii_eqb_true a c). destruct (ascii_eqb a c). 2:{ discriminate H. }
    rewrite (E eq_refl). rewrite (IH s2 H). reflexivity.
Qed.

Lemma eqb_refl : forall (s : string), eqb s s = true.
Proof.
  intros s. induction s as [|a s IH]; simpl.
  - reflexivity.
  - rewrite (ascii_eqb_refl a). exact IH.
Qed.

Unset Collapse Sorts ToType.
