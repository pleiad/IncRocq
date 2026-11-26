(* Single entry point for the framework.
   [From IncRocq Require Import IncRocq.] is the only import a client file
   needs. It pulls in the incremental substrate ([Base]), the catch-symbol generator ([gen.All]), the refinement
   and reformulation theory ([Reformulation]), and the tactics ([Tactics]),
   together with the sort-polymorphic equality from [Prelude.Logic] their
   statements are written with.

   The order of the exports matters. [Prelude/RelationClasses.v] and the
   [Corelib.Classes.RelationClasses] that MetaRocq pulls in both [Register] a
   [Reflexive] class under [rewrite.prop.Reflexive], and the module loaded last
   is the one the rewriting tactics look in. [gen.All] therefore comes before
   [Reformulation], whose import chain leaves Prelude's class registered. With
   the two reversed, [reflexivity] on a [⊑] goal fails with "the relation
   refinement is not a declared reflexive relation". The same reversal breaks
   [reflexivity] on [_ ≈ _], which goes through [eqMonoReflexive], and [symmetry]
   and [etransitivity] on [_ ≈̇ _]. *)

From IncRocq Require Export Base.
From IncRocq Require Export gen.All.
From Prelude Require Export Logic.
From IncRocq Require Export Reformulation.
From IncRocq Require Export Tactics.
