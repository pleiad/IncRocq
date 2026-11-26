
(* Require Import Notations. *)
(* Require Import Ltac. *)
From Prelude Require Import Logic.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

Definition type@{s;u} := Type@{s;u}.

(* Class LargeElimSort : type@{Type; _} := *)
(* { *)
(*   Univ : Type ; *)
(*   code : Type -> Univ ; *)
(*   El : Univ -> Type ; *)
(*   El_code A : El (code A) = A :> Type *)
(* }. *)

Class LargeElimSort@{s s2 ;u1 u2 u3 u4 u5|+} : type@{Type;u3} :=
{
  Univ : Type@{s;u2} ;
  code : Type@{s;u1} -> Univ ;
  El : Univ -> Type@{s;u1} ;
  El_code (A : Type@{s;u1}) : @eq@{Type s2;u4 u5} Type@{s;u1} (El (code A)) A
}.

#[export]
Instance TypeLargeElimSort@{s;l u2 u3 u4 u5} : LargeElimSort@{Type s;l u2 u3 u4 u5} := {
    Univ := Type@{l} ;
    code := fun A => A ;
    El := fun A => A ;
    El_code := fun A => eq_refl
}.

Definition lift_El {H:LargeElimSort} (A:Type) : A -> H.(El) (H.(code) A).
  intros a.
  eapply (@eq_poly_rec A a).
  rewrite (H.(El_code) A).
  exact a.
  reflexivity.
Qed.

Definition unlift_El {H:LargeElimSort} (A:Type) : H.(El) (H.(code) A) -> A.
  intros Hc.
  rewrite <- (H.(El_code) _).
  exact Hc.
Qed.

