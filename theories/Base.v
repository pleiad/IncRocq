#[universes(polymorphic=no)]
Sort Inc.

#[universes(polymorphic), unfold_fix]
Symbol TODO@{u} : forall (A : Type@{Inc;u}), A.

Rewrite Rule hole_fun :=
@{u+} |- TODO@{u} (forall (x : ?A), ?B) => fun x => TODO@{u} ?B.

(* Two spellings of a hole. [???] is Scala's syntax for an unimplemented value.
   [□] is the shorter one the examples are written with. Both are parsed, and a
   term prints with the notation declared last, so holes display as [□]. *)
Notation "???" := (TODO _).
Notation "□" := (TODO _).

(* Hint database for the incremental layer.  It is the database the
   ICP tactics hand their residual goals to, kept apart from
   [typeclass_instances], which drives instance resolution.  Every
   [typeclasses eauto] searches that one, so a lemma registered there is
   retried in unrelated searches.

   It holds lemmas that establish completeness, such as [is_complete C] for
   a constructor [C], [is_complete a -> is_complete (C a)], and their
   inversions.  Nothing about holes is registered here.  [a ⊑ TODO A] and
   [is_complete (TODO A) -> False] are the [hole_is_top] and
   [hole_not_complete] fields of the [Refinable] and [CompleteMinimal]
   instances, and the tactics read them off the instance.
   Declaring the database here, alongside [TODO], lets any file downstream of
   [IncRocq.Base] contribute to it. *)
Create HintDb icp.
