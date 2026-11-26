(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Collapse Sorts ToType.

Require Export Notations.
Require Import Ltac.

(** * Propositional connectives *)

(** [True] is the always true proposition *)

Inductive True : Type :=
  I : True.

Register True as core.True.type.
Register I as core.True.I.

(** [False] is the always false proposition *)
Inductive False : Type :=.

Register False as core.False.type.

Definition False_rect := False_poly_rec@{_ Type; _ _}.
Register Scheme False_rect as rect_dep for False.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A:Type) := A -> False.

Notation "~ x" := (not x) : type_scope.

Register not as core.not.type.

(** Negation of a type in [Type] *)

Definition notT (A:Type) := A -> False.

(** Create the "core" hint database, and set its transparent state for
  variables and constants explicitly. *)

Create HintDb core.
#[global]
Hint Variables Opaque : core.
#[global]
Hint Constants Opaque : core.

#[global]
Hint Unfold not: core.

  (** [and A B], written [A /\ B], is the conjunction of [A] and [B]

      [conj p q] is a proof of [A /\ B] as soon as
      [p] is a proof of [A] and [q] a proof of [B]

      [proj1] and [proj2] are first and second projections of a conjunction *)

Inductive and (A B:Type) : Type :=
  conj : A -> B -> A /\ B

where "A /\ B" := (and A B) : type_scope.

Register and as core.and.type.
Register conj as core.and.conj.

  Theorem proj1 (A B : Type) : A /\ B -> A.
  Proof.
    destruct 1; trivial.
  Qed.

  Theorem proj2 (A B : Type) : A /\ B -> B.
  Proof.
    destruct 1; trivial.
  Qed.


(** [or A B], written [A \/ B], is the disjunction of [A] and [B] *)

Inductive or (A B:Type) : Type :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B

where "A \/ B" := (or A B) : type_scope.

Arguments or_introl [A B] _, [A] B _.
Arguments or_intror [A B] _, A [B] _.

Register or as core.or.type.

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B:Type) := (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

Register iff as core.iff.type.
Register proj1 as core.iff.proj1.
Register proj2 as core.iff.proj2.

Section Equivalence.

Theorem iff_refl : forall A:Type, A <-> A.
  Proof.
    split; auto.
  Qed.

Theorem iff_trans : forall A B C:Type, (A <-> B) -> (B <-> C) -> (A <-> C).
  Proof.
    intros A B C [H1 H2] [H3 H4]; split; auto.
  Qed.

Theorem iff_sym : forall A B:Type, (A <-> B) -> (B <-> A).
  Proof.
    intros A B [H1 H2]; split; auto.
  Qed.

End Equivalence.

#[global]
Create HintDb extcore.

#[global]
Hint Unfold iff: extcore.

(** Backward direction of the equivalences above does not need assumptions *)

Theorem and_iff_compat_l : forall A B C : Type,
  (B <-> C) -> (A /\ B <-> A /\ C).
Proof.
  intros ? ? ? [Hl Hr]; split; intros [? ?]; (split; [ assumption | ]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem and_iff_compat_r : forall A B C : Type,
  (B <-> C) -> (B /\ A <-> C /\ A).
Proof.
  intros ? ? ? [Hl Hr]; split; intros [? ?]; (split; [ | assumption ]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem or_iff_compat_l : forall A B C : Type,
  (B <-> C) -> (A \/ B <-> A \/ C).
Proof.
  intros ? ? ? [Hl Hr]; split; (intros [?|?]; [left; assumption| right]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem or_iff_compat_r : forall A B C : Type,
  (B <-> C) -> (B \/ A <-> C \/ A).
Proof.
  intros ? ? ? [Hl Hr]; split; (intros [?|?]; [left| right; assumption]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem imp_iff_compat_l : forall A B C : Type,
  (B <-> C) -> ((A -> B) <-> (A -> C)).
Proof.
  intros ? ? ? [Hl Hr]; split; intros H ?; [apply Hl | apply Hr]; apply H; assumption.
Qed.

Theorem imp_iff_compat_r : forall A B C : Type,
  (B <-> C) -> ((B -> A) <-> (C -> A)).
Proof.
  intros ? ? ? [Hl Hr]; split; intros H ?; [apply H, Hr | apply H, Hl]; assumption.
Qed.

Theorem not_iff_compat : forall A B : Type,
  (A <-> B) -> (~ A <-> ~B).
Proof.
  intros; apply imp_iff_compat_r; assumption.
Qed.


(** Some equivalences *)

Theorem neg_false : forall A : Type, ~ A <-> (A <-> False).
Proof.
  intro A; unfold not; split.
  - intro H; split; [exact H | intro H1; elim H1].
  - intros [H _]; exact H.
Qed.

Theorem and_cancel_l : forall A B C : Type,
  (B -> A) -> (C -> A) -> ((A /\ B <-> A /\ C) <-> (B <-> C)).
Proof.
  intros A B C Hl Hr.
  split; [ | apply and_iff_compat_l]; intros [HypL HypR]; split; intros.
  + exact (proj2 (HypL (conj (Hl X) X))).
  + exact (proj2 (HypR (conj (Hr X) X))).
Qed.

Theorem and_cancel_r : forall A B C : Type,
  (B -> A) -> (C -> A) -> ((B /\ A <-> C /\ A) <-> (B <-> C)).
Proof.
  intros A B C Hl Hr.
  split; [ | apply and_iff_compat_r]; intros [HypL HypR]; split; intros.
  + exact (proj1 (HypL (conj X (Hl X)))).
  + exact (proj1 (HypR (conj X (Hr X)))).
Qed.

Theorem and_comm : forall A B : Type, A /\ B <-> B /\ A.
Proof.
  intros; split; intros [? ?]; split; assumption.
Qed.

Theorem and_assoc : forall A B C : Type, (A /\ B) /\ C <-> A /\ B /\ C.
Proof.
  intros; split; [ intros [[? ?] ?]| intros [? [? ?]]]; repeat split; assumption.
Qed.

Theorem or_cancel_l : forall A B C : Type,
  (B -> ~ A) -> (C -> ~ A) -> ((A \/ B <-> A \/ C) <-> (B <-> C)).
Proof.
  intros ? ? ? Fl Fr; split; [ | apply or_iff_compat_l]; intros [Hl Hr]; split; intros.
  { destruct Hl; [ right | destruct Fl | ]; assumption. }
  { destruct Hr; [ right | destruct Fr | ]; assumption. }
Qed.

Theorem or_cancel_r : forall A B C : Type,
  (B -> ~ A) -> (C -> ~ A) -> ((B \/ A <-> C \/ A) <-> (B <-> C)).
Proof.
  intros ? ? ? Fl Fr; split; [ | apply or_iff_compat_r]; intros [Hl Hr]; split; intros.
  { destruct Hl; [ left | | destruct Fl ]; assumption. }
  { destruct Hr; [ left | | destruct Fr ]; assumption. }
Qed.

Theorem or_comm : forall A B : Type, (A \/ B) <-> (B \/ A).
Proof.
  intros; split; (intros [? | ?]; [ right | left ]; assumption).
Qed.

Theorem or_assoc : forall A B C : Type, (A \/ B) \/ C <-> A \/ B \/ C.
Proof.
  intros; split; [ intros [[?|?]|?]| intros [?|[?|?]]].
  + left; assumption.
  + right; left; assumption.
  + right; right; assumption.
  + left; left; assumption.
  + left; right; assumption.
  + right; assumption.
Qed.
Lemma iff_and : forall A B : Type, (A <-> B) -> (A -> B) /\ (B -> A).
Proof.
  intros A B []; split; trivial.
Qed.

Lemma iff_to_and : forall A B : Type, (A <-> B) <-> (A -> B) /\ (B -> A).
Proof.
  intros; split; intros [Hl Hr]; (split; intros; [ apply Hl | apply Hr]); assumption.
Qed.

(** * First-order quantifiers *)

(** [ex P], or simply [exists x, P x], or also [exists x:A, P x],
    expresses the existence of an [x] of some type [A] in [Set] which
    satisfies the predicate [P].  This is existential quantification.

    [ex2 P Q], or simply [exists2 x, P x & Q x], or also
    [exists2 x:A, P x & Q x], expresses the existence of an [x] of
    type [A] which satisfies both predicates [P] and [Q].

    Universal quantification is primitively written [forall x:A, Q]. By
    symmetry with existential quantification, the construction [all P]
    is provided too.
*)

Inductive ex (A:Type) (P:A -> Type) : Type :=
  ex_intro : forall x:A, P x -> ex (A:=A) P.

Register ex as core.ex.type.
Register ex_intro as core.ex.intro.

(*Section Projections.*)

  (*Variables (A:Prop) (P:A->Prop).*)

Definition ex_proj1 (A : Type) (P : A -> Type) (x:ex P) : A :=
  match x with ex_intro _ a _ => a end.

Definition ex_proj2 (A : Type) (P : A -> Type) (x:ex P) : P (ex_proj1 x) :=
  match x with ex_intro _ _ b => b end.

Register ex_proj1 as core.ex.proj1.
Register ex_proj2 as core.ex.proj2.

(*End Projections.*)

Inductive ex2 (A:Type) (P Q:A -> Type) : Type :=
  ex_intro2 : forall x:A, P x -> Q x -> ex2 (A:=A) P Q.

(** [ex2] of a predicate can be projected to an [ex].

    This allows [ex_proj1] and [ex_proj2] to be usable with [ex2].

    We have two choices here: either we can set up the definition so
    that [ex_proj1] of a coerced [X : ex2 P Q] will unify with [let
    (a, _, _) := X in a] by restricting the first argument of [ex2] to
    be a [Prop], or we can define a more general [ex_of_ex2] which
    does not satisfy this conversion rule.  We choose the former,
    under the assumption that there is no reason to turn an [ex2] into
    an [ex] unless it is to project out the components. *)

Definition ex_of_ex2 (A : Type) (P Q : A -> Type) (X : ex2 P Q) : ex P
  := ex_intro P
              (let (a, _, _) := X in a)
              (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

(*Section ex2_Projections.*)
(**)
(*  Variables (A:Prop) (P Q:A->Prop).*)

  Definition ex_proj3 (A:Type) (P Q:A->Type) (x:ex2 P Q) : Q (ex_proj1 (ex_of_ex2 x)) :=
    match x with ex_intro2 _ _ _ _ b => b end.

(*End ex2_Projections.*)

Definition all (A:Type) (P:A -> Type) := forall x:A, P x.
Register all as core.all.

(* Rule order is important to give printing priority to fully typed exists *)

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x name, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x name, A at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  A ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

Notation "'exists2' ' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x strict pattern, p at level 200, right associativity) : type_scope.
Notation "'exists2' ' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x strict pattern, A at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' ' x  :  A ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

(** Derived rules for universal quantification *)

  Theorem inst (A : Type) (P : A -> Type) : forall x:A, all (fun x => P x) -> P x.
  Proof.
    unfold all; auto.
  Qed.

  Theorem gen (A : Type) (P : A -> Type) : forall (B:Type) (f:forall y:A, B -> P y), B -> all P.
  Proof.
    red; auto.
  Qed.

(** * Equality *)

(** [eq x y], or simply [x=y] expresses the equality of [x] and
    [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others properties (symmetry, transitivity, replacement of
    equals by equals) are proved below. The type of [x] and [y] can be
    made explicit using the notation [x = y :> A]. This is Leibniz equality
    as it expresses that [x] and [y] are equal iff every property on
    [A] which is true of [x] is also true of [y] *)

Inductive eq (A:Type) (x:A) : A -> Type :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Notation "x = y" := (eq x y) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

#[global]
Hint Resolve I conj or_introl or_intror : core.
#[global]
Hint Resolve eq_refl: core.
#[global]
Hint Resolve ex_intro ex_intro2: core.

Definition eq_poly_rec_nodep  (A : Type) (x : A) (P : A -> Type) (H : P x) (y : A) (e : x = y) : P y.
Proof. destruct e. exact H. Defined.

Definition eq_ind (A : Type) (x : A) (P : A -> Prop) (H : P x) (y : A) (e : x = y) : P y.
Proof. destruct e. exact H. Defined.

Definition eq_sind (A : Type) (x : A) (P : A -> SProp) (H : P x) (y : A) (e : x = y) : P y.
Proof. destruct e. exact H. Defined.

Definition eq_rec (A : Type) (x : A) (P : A -> Set) (H : P x) (y : A) (e : x = y) : P y.
Proof. destruct e. exact H. Defined.

#[local]
Definition type@{s;v} := Type@{s;v}.

Definition eq_rect (A : Type) (x : A) (P : A -> type@{Type;_}) (H : P x) (y : A) (e : x = y) : P y.
Proof. destruct e. exact H. Defined.

Arguments eq_ind  [A] x P _ y _ : rename.
Arguments eq_rec  [A] x P _ y _ : rename.
Arguments eq_rect [A] x P _ y _ : rename.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_sind as core.eq.sind.
Register eq_rect as core.eq.rect.
Register eq_rec as core.eq.rec.

Register Scheme eq_ind  as ind_nodep  for eq.
Register Scheme eq_rec  as rec_nodep  for eq.
Register Scheme eq_rect as rect_nodep for eq.
Register Scheme eq_sind as sind_nodep for eq.

(* Scheme Rewriting for eq. *)
(**)
(* Register eq_rew_dep as core.eq.rect_dep. *)
(* Register eq_rew_dep as core.eq.ind_dep. *)
(* Register eq_rew_r_dep as core.eq.rect_r_dep. *)
(* Register eq_rew_r_dep as core.eq.ind_r_dep. *)

Definition eq_sym [A:Type] [x y : A]
  (H : x = y) : y = x :=
  match H with eq_refl => eq_refl end.

Arguments eq_sym {A x y} _.
#[global] Hint Immediate eq_sym: core.

Register eq_sym as core.eq.sym.

Definition eq_rew [A : Type] [x : A] (P : A -> Type) (eq_refl : P x) (a : A) (e : x = a) :=
  match e in _ = a0 return P a0 with
  | eq_refl => eq_refl
  end.

Definition eq_rew_dep [A : Type] [x : A] (P : forall a : A, x = a -> Type)
  (eq_refl : P x eq_refl) (a : A) (e : x = a) :=
  match e as e0 in _ = a0 return P a0 e0 with
  | eq_refl => eq_refl
  end.

Definition eq_rew_fwd_dep [A : Type] [x y : A] (H : x = y) (P : forall y0 : A, x = y0 -> Type)
  (HC : P y H) :=
  match H as H0 in _ = y0 return P y0 H0 -> P x eq_refl with
  | eq_refl => fun HC0 : P x eq_refl => HC0
  end HC.

Definition eq_rew_r [A : Type] [x y : A] (P : A -> Type) (HC : P y) (H : x = y) :=
  match H in _ = y0 return P y0 -> P x with
  | eq_refl => fun HC0 : P x => HC0
  end HC.

Definition eq_sym_involutive [A : Type] [x y : A] (H : x = y) :=
  match H as H0 in _ = y0 return eq_sym (eq_sym H0) = H0 with
  | eq_refl => eq_refl
  end.

Definition eq_rew_r_dep [A : Type] [x y : A] (P : forall y0 : A, y0 = y -> Type)
  (HC : P y eq_refl) (H : x = y) :=
  match eq_sym_involutive H in _ = H0 return P x H0 with
  | eq_refl =>
    match eq_sym H as H0 in _ = y0 return P y0 (eq_sym H0) with
    | eq_refl => HC
    end
  end.

Definition eq_rew_fwd_r_dep [A : Type] [x y : A] (H : x = y) :=
  match
    H as H0 in _ = y0
    return (forall P : forall y1 : A, y1 = y0 -> Type, P x H0 -> P y0 eq_refl)
  with
  | eq_refl => fun (P : forall y0 : A, y0 = x -> Type) (HC : P x eq_refl) => HC
  end.

Register eq_rew_dep as core.eq.rect_dep.
Register eq_rew_dep as core.eq.ind_dep.
Register eq_rew_r_dep as core.eq.rect_r_dep.
Register eq_rew_r_dep as core.eq.ind_r_dep.

(* Populate the scheme cache (Ind_tables) that the [rewrite] tactic consults.
   This is distinct from the coqlib [Register ... as core.eq.*] table above.
   Without these, [rewrite] autogenerates the schemes on demand, which fails to
   pre-generate via [Scheme Rewriting for eq] because [eq] is sort-polymorphic
   (elimination into [Type] from a variable sort quality is not allowed). *)
Register Scheme eq_rew           as rew           for eq.
Register Scheme eq_rew_r         as rew_r         for eq.
Register Scheme eq_rew_dep       as rew_dep       for eq.
Register Scheme eq_rew_r_dep     as rew_r_dep     for eq.
Register Scheme eq_rew_fwd_dep   as rew_fwd_dep   for eq.
Register Scheme eq_rew_fwd_r_dep as rew_fwd_r_dep for eq.

(* [rewrite] looks for a Leibniz principle of the equality in the
   [rewrite_instances] database. This file gives both for the
   sort-polymorphic [eq] and [False]. *)
Definition eq_leibniz : Corelib.Init.Equality.Has_Leibniz (@eq) :=
  fun A x P px y e => eq_poly_rec_nodep P px e.
#[global] Hint Resolve eq_leibniz : rewrite_instances.


Arguments eq_sym_involutive [A]%_type_scope [x y] e : rename.

  Theorem absurd : forall A C:Prop, A -> ~ A -> C.
  Proof.
    unfold not; intros A C h1 h2.
    destruct (h2 h1).
  Qed.

    Theorem eq_trans (A : Type) (x y z : A) : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Register eq_trans as core.eq.trans.

    Theorem eq_trans_r (A : Type) (x y z : A) : x = y -> z = y -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Theorem f_equal (A B : Type) (f : A -> B) (x y : A) : x = y -> f x = f y.
    Proof.
      destruct 1; trivial.
    Defined.

    Register f_equal as core.eq.congr.

    Theorem not_eq_sym (A : Type) (x y : A) : x <> y -> y <> x.
    Proof.
      red; intros h1 h2; apply h1; destruct h2; trivial.
    Qed.

  Definition eq_sind_r :
    forall (A:Type) (x:A) (P:A -> SProp), P x -> forall y:A, y = x -> P y.
  Proof.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Register eq_ind_r as core.eq.ind_r.
  Register eq_sind_r as core.eq.sind_r.

  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rect_r :
    forall (A:Type) (x:A) (P:A -> type@{Type;_}), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.

  Register eq_rect_r as core.eq.rect_r.
  Register eq_rec_r as core.eq.rec_r.


Module EqNotations.
  Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  H  in  '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  H  in  '/' H' ']'").
  Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' -> H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' -> [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10, only parsing).

  Notation "'rew' 'dependent' H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, only parsing).
  Notation "'rew' 'dependent' <- H 'in' H'"
    := (match eq_sym H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name, only parsing).
  Notation "'rew' 'dependent' <- [ 'fun' y p => P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  <-  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          only parsing).
  Notation "'rew' 'dependent' <- [ P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
End EqNotations.

Import EqNotations.

Theorem f_equal_dep [A : Type] (B : A -> Type) (f : forall x, B x) [x y : A] (H: x = y) : rew H in f x = f y.
Proof.
  destruct H; reflexivity.
Defined.

Lemma f_equal_dep2 {A A' B B'} (f : A -> A') (g : forall a:A, B a -> B' (f a))
  {x1 x2 : A} {y1 : B x1} {y2 : B x2} (H : x1 = x2) :
  rew H in y1 = y2 -> rew f_equal f H in g x1 y1 = g x2 y2.
Proof.
  destruct H, 1. reflexivity.
Defined.

Lemma rew_opp_r A (P:A->Type) (x y:A) (H:x=y) (a:P y) : rew H in rew <- H in a = a.
Proof.
  destruct H. reflexivity.
Defined.

Lemma rew_opp_l A (P:A->Type) (x y:A) (H:x=y) (a:P x) : rew <- H in rew H in a = a.
Proof.
  destruct H. reflexivity.
Defined.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.

Register f_equal2 as core.eq.congr2.

Theorem f_equal3 :
  forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1)
    (x2 y2:A2) (x3 y3:A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof.
  destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal4 :
  forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal5 :
  forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal_compose A B C (a b:A) (f:A->B) (g:B->C) (e:a=b) :
  f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e.
Proof.
  destruct e. reflexivity.
Defined.

(** The groupoid structure of equality *)

Theorem eq_trans_refl_l A (x y:A) (e:x=y) : eq_trans eq_refl e = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_trans_refl_r A (x y:A) (e:x=y) : eq_trans e eq_refl = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_trans_sym_inv_l A (x y:A) (e:x=y) : eq_trans (eq_sym e) e = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_r A (x y:A) (e:x=y) : eq_trans e (eq_sym e) = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_assoc A (x y z t:A) (e:x=y) (e':y=z) (e'':z=t) :
  eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
Proof.
  destruct e''; reflexivity.
Defined.

Theorem rew_map A B (P:B->Type) (f:A->B) x1 x2 (H:x1=x2) (y:P (f x1)) :
  rew [fun x => P (f x)] H in y = rew f_equal f H in y.
Proof.
  destruct H; reflexivity.
Defined.

Theorem eq_trans_map {A} {B : A -> Type} {x1 x2 x3:A} {y1:B x1} {y2:B x2} {y3:B x3}
  (H1:x1=x2) (H2:x2=x3) (H1': rew H1 in y1 = y2) (H2': rew H2 in y2 = y3) :
  rew eq_trans H1 H2 in y1 = y3.
Proof.
  destruct H2. exact (eq_trans H1' H2').
Defined.

Lemma map_subst {A} {P Q:A->Type} (f : forall x, P x -> Q x) {x y} (H:x=y) (z:P x) :
  rew H in f x z = f y (rew H in z).
Proof.
  destruct H. reflexivity.
Defined.

Lemma map_subst_map {A B} {P:A->Type} {Q:B->Type} (f:A->B) (g : forall x, P x -> Q (f x))
  {x y} (H:x=y) (z:P x) :
  rew f_equal f H in g x z = g y (rew H in z).
Proof.
  destruct H. reflexivity.
Defined.

Lemma rew_swap A (P:A->Type) x1 x2 (H:x1=x2) (y1:P x1) (y2:P x2) : rew H in y1 = y2 -> y1 = rew <- H in y2.
Proof.
  destruct H. trivial.
Defined.

Lemma rew_compose A (P:A->Type) x1 x2 x3 (H1:x1=x2) (H2:x2=x3) (y:P x1) :
  rew H2 in rew H1 in y = rew (eq_trans H1 H2) in y.
Proof.
  destruct H2. reflexivity.
Defined.

(** Extra properties of equality *)

Theorem eq_id_comm_l A (f:A->A) (Hf:forall a, a = f a) a : f_equal f (Hf a) = Hf (f a).
(* Proof. *)
(*   unfold f_equal. *)
(*   rewrite <- (eq_trans_sym_inv_l (Hf a)). *)
(*   destruct (Hf a) at 1 2. *)
(*   destruct (Hf a). *)
(*   reflexivity. *)
(* Defined. *)
Admitted.

Theorem eq_id_comm_r A (f:A->A) (Hf:forall a, f a = a) a : f_equal f (Hf a) = Hf (f a).
(* Proof. *)
(*   unfold f_equal. *)
(*   rewrite <- (eq_trans_sym_inv_l (Hf (f (f a)))). *)
(*   set (Hfsymf := fun a => eq_sym (Hf a)). *)
(*   change (eq_sym (Hf (f (f a)))) with (Hfsymf (f (f a))). *)
(*   pattern (Hfsymf (f (f a))). *)
(*   destruct (eq_id_comm_l f Hfsymf (f a)). *)
(*   destruct (eq_id_comm_l f Hfsymf a). *)
(*   unfold Hfsymf. *)
(*   destruct (Hf a). simpl. *)
(*   rewrite eq_trans_refl_l. *)
(*   reflexivity. *)
(* Defined. *)
Admitted.

Lemma eq_refl_map_distr A B x (f:A->B) : f_equal f (eq_refl x) = eq_refl (f x).
Proof.
  reflexivity.
Qed.

Lemma eq_trans_map_distr A B x y z (f:A->B) (e:x=y) (e':y=z) : f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').
Proof.
  destruct e'. reflexivity.
Defined.

Lemma eq_sym_map_distr A B (x y:A) (f:A->B) (e:x=y) : eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
  destruct e. reflexivity.
Defined.

Lemma eq_trans_sym_distr A (x y z:A) (e:x=y) (e':y=z) : eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).
Proof.
  destruct e, e'. reflexivity.
Defined.

Lemma eq_trans_rew_distr A (P:A -> Type) (x y z:A) (e:x=y) (e':y=z) (k:P x) :
    rew (eq_trans e e') in k = rew e' in rew e in k.
Proof.
  destruct e, e'; reflexivity.
Qed.

Lemma rew_const A P (x y:A) (e:x=y) (k:P) :
    rew [fun _ => P] e in k = k.
Proof.
  destruct e; reflexivity.
Qed.

(* Aliases *)

Abbreviation sym_eq := eq_sym (only parsing).
Abbreviation trans_eq := eq_trans (only parsing).
Abbreviation sym_not_eq := not_eq_sym (only parsing).

Abbreviation refl_equal := eq_refl (only parsing).
Abbreviation sym_equal := eq_sym (only parsing).
Abbreviation trans_equal := eq_trans (only parsing).
Abbreviation sym_not_equal := not_eq_sym (only parsing).

#[global]
Hint Immediate eq_sym not_eq_sym: core.

(** Basic definitions about relations and properties *)

Definition subrelation (A B : Type) (R R' : A->B->Prop) :=
  forall x y, R x y -> R' x y.

Definition unique (A : Type) (P : A->Prop) (x:A) :=
  P x /\ forall (x':A), P x' -> x=x'.

Definition uniqueness (A:Type) (P:A->Prop) := forall x y, P x -> P y -> x = y.


