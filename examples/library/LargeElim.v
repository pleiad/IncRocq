(* Example of Large Elimination on natural numbers *)

From Prelude Require Import Logic LargeElim Datatypes.

Definition P {H:LargeElimSort} (n : nat) :=
  match n return H.(Univ) with
    O => code True
  | _ => code False
  end.

Lemma eq_true {H:LargeElimSort} : forall (n:nat), O = n -> H.(El) (P n).
Proof.
  intros b e. destruct e. simpl. exact (lift_El _ I).
Qed.

Lemma nat_discr_gen {H:LargeElimSort} (n : nat) : O = S n -> False.
Proof.
  intro e. exact (unlift_El _ (eq_true _ e)).
Qed.

(* Direct Large Elimination *)

Definition Pred_nat (n : nat) :=
  match n return Type with
  | O => True
  | _ => False
  end.

Lemma eq_true' : forall (n:nat), O = n -> Pred_nat n.
Proof.
  intros b e. destruct e. exact I.
Qed.

Lemma nat_discr (n : nat) : O = S n -> False.
Proof.
  intro e. destruct (eq_true' _ e).
Qed.
