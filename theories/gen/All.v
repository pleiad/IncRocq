From MetaRocq.Template Require Import All.
Import MRMonadNotation.

From IncRocq Require Export gen.Catch gen.HoleMatch gen.Complete gen.Refinable gen.CompleteMinimal.

(* Declares, for the inductive [q], the catch symbol and its rules, the rule
   that propagates holes through a match on [q], the completeness predicate of
   [q] and its Complete instance, through gen_complete, the refinement relation
   of [q] and its Refinable instance, through gen_refinable, and the
   CompleteMinimal instance of [q], through gen_complete_minimal. A type whose
   completeness or refinement is not the structural one runs generate_catch
   and generate_hole_match_rule, followed by whichever of the other generators
   it still wants, and declares its own instances. *)
Definition gen_icp_defs (q : qualid) : TemplateMonad unit :=
  generate_catch q ;;
  generate_hole_match_rule q ;;
  gen_complete q ;;
  gen_refinable q ;;
  gen_complete_minimal q.
