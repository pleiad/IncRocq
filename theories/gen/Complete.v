(* Generates the structural completeness predicate of an inductive and its
   [Complete] instance.

   For an inductive [T A1 .. An] whose parameters are types, [gen_complete "T"]
   declares

     Inductive complete_T (A1 : _) .. (An : _)
         (P1 : B1 -> Type) .. (Pk : Bk -> Type) : T A1 .. An -> Type :=
     | complete_C : forall x1 .. xm, prem1 -> .. -> premk ->
                    complete_T A1 .. An P1 .. Pk (C x1 .. xm)
     ...

   with one predicate parameter per slot and one premise per field of [C].
   The slots [B1 .. Bk] are the parameters [A1 .. An], followed by each other
   type of a field, such as [bool] in a field [bool] or [option A1] in a field
   [option A1], once each, in the order they first occur. A field of type
   [T A1 .. An] gives [complete_T A1 .. An P1 .. Pk x], and a field of type
   [Bi] gives [Pi x]. There is no constructor for [TODO T], so a hole is never
   complete.

   Every inductive has such a predicate, but the generator does not build all
   of them yet. For an inductive with indices, a non-type parameter, a mutual
   block, or a field whose type mentions [T] other than as [T A1 .. An], or is
   an inductive with indices, it prints what it cannot generate yet and
   declares nothing.

   The instance is

     complete_T_inst : forall A1 .. An, Complete B1 -> .. -> Complete Bk ->
                       Complete (T A1 .. An)
     := fun A1 .. An H1 .. Hk =>
          {| is_complete := complete_T A1 .. An (@is_complete B1 H1) .. |}

   declared with [tmDefinitionU] and registered with [tmExistingInstance].
   Both constants are universe and sort polymorphic. Their contexts extend the
   context of [T], with the quality of [T] itself replaced by [Inc], as for the
   catch symbol. *)
From MetaRocq.Utils Require Export utils.
From MetaRocq.Template Require Import All.

From Stdlib Require Init.
Import MRMonadNotation.

From IncRocq Require Export Base.
From IncRocq Require Import gen.Utils gen.Source.

(* ------------------------------------------------------------------ *)
(* The Complete class, located by name                                 *)
(* ------------------------------------------------------------------ *)

(* gen/ loads before Reformulation.v, which declares [Complete], so the class
   is referred to by its kernel name. *)
Definition complete_lib : dirpath := ["Reformulation"; "IncRocq"].
Definition complete_class_kn : kername := (MPfile complete_lib, "Complete").
Definition complete_class : inductive :=
  {| inductive_mind := complete_class_kn; inductive_ind := 0 |}.
Definition is_complete_kn : kername := (MPfile complete_lib, "is_complete").

(* ------------------------------------------------------------------ *)
(* The predicate                                                       *)
(* ------------------------------------------------------------------ *)

(* complete_T has the universe layout of Source.v, with a predicate
   [Pi : Bi -> Type@{q_slot i; u_slot i}] for each slot [Bi]. *)
Definition pred_inst (s : source) : Instance.t :=
  Instance.make (map qvar (seq_nat 0 (q_result s + 1)))
                (map Level.lvar (seq_nat 0 (nlevels s + nslots s))).

(* The binders P0 .. P(k-1), under the parameters and P0 .. P(i-1). *)
Definition pred_binders (s : source) : list (aname * term) :=
  map (fun i =>
    (named ("P" ^ string_of_nat i) Relevant,
     tProd (named "a" (sort_relevance (slot_sort s i))) (slot_type s i i)
           (tSort (sQVar (QVar.Var (q_slot s i)) (lvl (u_slot s i))))))
    (seq_nat 0 (nslots s)).

Definition pred_type (s : source) : term :=
  mkProds (param_binders s ++ pred_binders s)
    (tProd (named "x" (sort_relevance s.(src_sort))) (T_applied s 0)
       (tSort (sQVar (QVar.Var (q_result s)) (result_universe s)))).

(* The type of the constructor of complete_T for the constructor [c], number
   [k], of T. In it, complete_T itself is the outermost [tRel]. *)
Definition pred_ctor (s : source) (k : nat) (c : constructor_body) : ident * term :=
  let n := s.(src_nparams) in
  let fields := List.rev c.(cstr_args) in
  let m := List.length fields in
  let kinds := field_kinds s c in
  (* The fields, with T itself in place of its [tRel] and the parameters
     shifted past the predicates. *)
  let field_binders :=
    mapi (fun j d =>
      let ty := src_term s d.(decl_type) in
      let ty := lift (nslots s) j (subst [tInd s.(src_ind) s.(src_inst)] (j + n) ty) in
      ({| binder_name := nNamed ("x" ^ string_of_nat j);
          binder_relevance := src_relevance s d.(decl_name).(binder_relevance) |}, ty))
      fields in
  let kinds := flat_map (fun o => match o with Some k => [k] | None => [] end) kinds in
  (* One premise per field, in order. The field [j] is [tRel (m - 1 - j + p)]
     under the [p] premises before it. *)
  let premises :=
    mapi (fun p '(j, kd) =>
      let x := tRel (m - 1 - j + p) in
      match kd with
      | FRecursive =>
          ({| binder_name := nAnon; binder_relevance := RelevanceVar (QVar.Var (q_result s)) |},
           mkApps (tRel (n + nslots s + m + p)) (params_and_slots s (m + p) ++ [x]))
      | FSlot i =>
          ({| binder_name := nAnon; binder_relevance := RelevanceVar (QVar.Var (q_slot s i)) |},
           mkApps (rel_S s (m + p) i) [x])
      end) (combine (seq_nat 0 m) kinds) in
  let np := List.length premises in
  let value :=
    mkApps (tConstruct s.(src_ind) k s.(src_inst))
      (map (rel_A s (m + np)) (seq_nat 0 n) ++ map (fun j => tRel (m - 1 - j + np)) (seq_nat 0 m)) in
  let concl := mkApps (tRel (n + nslots s + m + np)) (params_and_slots s (m + np) ++ [value]) in
  ("complete_" ^ c.(cstr_name),
   mkProds (param_binders s ++ pred_binders s ++ field_binders ++ premises) concl).

Definition pred_universes (s : source) : universes_decl :=
  Polymorphic_ctx
    (AUContext.make
       (mk_bound_names (s.(src_quals) ++ repeat nAnon (nslots s + 1))
                       (s.(src_levels) ++ repeat nAnon (nslots s)))
       s.(src_cstrs)).

Definition pred_body (s : source) (ctors : list (ident * term)) : mutual_inductive_body :=
  {| ind_finite := Finite;
     ind_npars := s.(src_nparams) + nslots s;
     ind_params := [];
     ind_bodies :=
       [{| ind_name := "complete_" ^ s.(src_id);
           ind_indices := [];
           ind_sort := sQVar (QVar.Var (q_result s)) (result_universe s);
           ind_type := pred_type s;
           ind_kelim := IntoAny;
           ind_ctors := map (fun '(nm, ty) =>
                              {| cstr_name := nm; cstr_args := []; cstr_indices := [];
                                 cstr_type := ty; cstr_arity := 0 |}) ctors;
           ind_projs := [];
           ind_relevance := Relevant |}];
     ind_universes := pred_universes s;
     ind_variance := None |}.

(* ------------------------------------------------------------------ *)
(* The instance                                                        *)
(* ------------------------------------------------------------------ *)

Definition gen_complete_instance (s : source) (pred : inductive) (class_cstrs : ConstraintSet.t)
    : TemplateMonad unit :=
  let n := s.(src_nparams) in
  let k := nslots s in
  let base := nlevels s + k in
  let slot_ql := map (fun '(_, so) => match param_quality_level so with
                                      | Some p => p
                                      | None => (Quality.qType, Level.lzero)
                                      end) s.(src_slots) in
  (* The class level of each Complete Bi is lvar (base + i). *)
  let c_i i := Level.lvar (base + i) in
  let next := base + k in
  match level_above s.(src_univ) next with
  | None => tmFail "gen_complete: the universe of the inductive has an increment"
  | Some (t1, k1, cs1) =>
  match level_above (result_universe s) (next + k1) with
  | None => tmFail "gen_complete: the universe of the predicate has an increment"
  | Some (t2, k2, cs2) =>
  let t3 := Level.lvar (next + k1 + k2) in
  let nfresh := k + k1 + k2 + 1 in
  let arg_inst i :=
    let '(q, l) := nth i slot_ql (Quality.qType, Level.lzero) in
    Instance.make [q; qvar (q_slot s i)] [l; u_slot s i; c_i i] in
  let res_inst := Instance.make [inc_quality; qvar (q_result s)] [t1; t2; t3] in
  let cstrs :=
    add_constraints
      (flat_map (fun i => let '(_, l) := nth i slot_ql (Quality.qType, Level.lzero) in
                          inst_constraints [l; u_slot s i; c_i i] class_cstrs) (seq_nat 0 k)
       ++ inst_constraints [t1; t2; t3] class_cstrs ++ cs1 ++ cs2)
      s.(src_cstrs) in
  let udecl :=
    Polymorphic_ctx
      (AUContext.make
         (mk_bound_names (s.(src_quals) ++ repeat nAnon (k + 1))
                         (s.(src_levels) ++ repeat nAnon (k + nfresh)))
         cstrs) in
  (* The binders H0 .. H(k-1) : Complete Bi, under the parameters and
     H0 .. H(i-1). *)
  let inst_binders :=
    map (fun i => (named ("H" ^ string_of_nat i) Relevant,
                   mkApps (tInd complete_class (arg_inst i)) [slot_type s i i])) (seq_nat 0 k) in
  let binders := param_binders s ++ inst_binders in
  (* Under the parameters and the instances, Ai is [rel_A s 0 i], Bi is
     [rel_B s 0 i] and Hi is [rel_S s 0 i], since the instances sit where the
     predicates sat. *)
  let T_A := T_applied s 0 in
  let preds := map (fun i => mkApps (tConst is_complete_kn (arg_inst i))
                                    [rel_B s 0 i; rel_S s 0 i]) (seq_nat 0 k) in
  let ty := mkProds binders (mkApps (tInd complete_class res_inst) [T_A]) in
  let body := mkLams binders
                (mkApps (tConstruct complete_class 0 res_inst)
                   [T_A; mkApps (tInd pred (pred_inst s))
                           (map (rel_A s 0) (seq_nat 0 n) ++ preds)]) in
  let name := "complete_" ^ s.(src_id) ^ "_inst" in
  tmDefinitionU name udecl ty body ;;
  gr <- tmLocate1 name ;;
  tmExistingInstance export gr
  end
  end.

(* ------------------------------------------------------------------ *)
(* gen_complete                                                        *)
(* ------------------------------------------------------------------ *)

(* Declares complete_T and complete_T_inst for the inductive described by [s],
   for which [generator_gap] finds nothing. *)
Definition gen_complete_generable (s : source) : TemplateMonad unit :=
  let ctors := map (fun '(k, c) => pred_ctor s k c)
                   (combine (seq_nat 0 (List.length s.(src_body).(ind_ctors)))
                            s.(src_body).(ind_ctors)) in
  tmMkInductive' (pred_body s ctors) ;;
  pgr <- tmLocate1 ("complete_" ^ s.(src_id)) ;;
  match pgr with
  | IndRef pred =>
      class_decl <- tmQuoteInductive complete_class_kn ;;
      match class_decl.(ind_universes) with
      | Polymorphic_ctx (_, class_cstrs) =>
          gen_complete_instance s pred class_cstrs ;;
          tmMsg ("complete_" ^ s.(src_id) ^ " and complete_" ^ s.(src_id)
                 ^ "_inst are declared")
      | Monomorphic_ctx => tmFail "gen_complete: Complete is not polymorphic"
      end
  | _ => tmFail "gen_complete: the predicate was not declared"
  end.

(* Declares the completeness predicate of [q] and its instance. When the
   generator cannot build them yet, it prints why and declares nothing, so that
   gen_icp_defs can run it on every inductive. It declares nothing either when
   the Complete class is not loaded. *)
Definition gen_complete (q : qualid) : TemplateMonad unit :=
  class <- tmLocate (string_of_kername complete_class_kn) ;;
  match class with
  | [] => ret tt
  | _ =>
      r <- check_source q ;;
      match r with
      | Generable s => gen_complete_generable s
      | NotYet why =>
          tmMsg ("gen_complete cannot yet generate complete_" ^ q ^ ": " ^ why)
      end
  end.
