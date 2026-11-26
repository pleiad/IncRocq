From Prelude Require Import Logic Datatypes.
From Prelude Require Export String.
Import ListNotations.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

Local Open Scope list_scope.

Definition Map (A : Type) := list (string * A).

Definition map_empty {A} : Map A := [].

Fixpoint map_get {A : Type} (m : Map A) (x : string) : option A :=
  match m with
  | [] => None
  | kv :: m' =>
    if eqb x (fst kv) then Some (snd kv) else map_get m' x
  end.

Definition map_set {A : Type} (m:Map A) (x : string) (v : A) : Map A := (pair x v) :: m.


Definition included_in {A : Type} (m m' : Map A) :=
  forall x v, map_get m x = Some v -> map_get m' x = Some v.

(* The inclusion lemmas are stated at the ground sorts, so they do not apply to
   [Inc]-sorted maps. *)
Set Collapse Sorts ToType.

Lemma included_in_empty : forall {A : Type} (m : Map A), included_in map_empty m.
Proof. intros A m x v H. simpl in H. discriminate H. Qed.

Lemma included_in_map_set : forall {A : Type} {m m' : Map A} (x : string) (v : A),
  included_in m m' -> included_in (map_set m x v) (map_set m' x v).
Proof.
  intros A m m' x v Hinc z w H. simpl in *. destruct (eqb z x).
  - exact H.
  - apply Hinc. exact H.
Qed.

Lemma shadowing_included_in : forall {A : Type} (m : Map A) (x : string) (v1 v2 : A),
  included_in (map_set (map_set m x v1) x v2) (map_set m x v2).
Proof. intros A m x v1 v2 z v H. simpl in *. destruct (eqb z x); exact H. Qed.

Lemma map_permutation_included_in : forall {A : Type} (m : Map A) (x y : string) (vx vy : A),
  (x = y -> False) ->
  included_in (map_set (map_set m x vx) y vy) (map_set (map_set m y vy) x vx).
Proof.
  intros A m x y vx vy Hxy z v H. simpl in *.
  assert (Ex := eqb_true z x). assert (Ey := eqb_true z y).
  destruct (eqb z y); destruct (eqb z x).
  - pose proof (Ex eq_refl) as Hzx. pose proof (Ey eq_refl) as Hzy.
    rewrite Hzx in Hzy. destruct (Hxy Hzy).
  - exact H.
  - exact H.
  - exact H.
Qed.

Unset Collapse Sorts ToType.

