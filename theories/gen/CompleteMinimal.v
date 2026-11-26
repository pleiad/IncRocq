(* Generates the proof that the complete values of an inductive are minimal
   for its refinement, and its [CompleteMinimal] instance.

   For an inductive [T A1 .. An] with the slots [B1 .. Bk] (see Source.v),
   whose completeness predicate and refinement relation [gen_complete] and
   [gen_refinable] declared, [gen_complete_minimal "T"] declares, with
   [tmLemmaU],

     complete_T_minimal : forall A1 .. An P1 .. Pk R1 .. Rk,
       (forall a, P1 a -> forall a', R1 a' a -> a' = a) -> .. ->
       forall x, complete_T A.. P.. x ->
       forall x', refinement_T A.. R.. x' x -> x' = x
     complete_T_hole : forall A1 .. An P1 .. Pk,
       complete_T A.. P.. (TODO (T A1 .. An)) -> False

   proved by [gen_complete_minimality] and [gen_complete_hole] from
   [Tactics.v], and the instance

     complete_minimal_T_inst : forall A1 .. An,
       Refinable B1 -> .. -> Refinable Bk ->
       Complete B1 -> .. -> Complete Bk ->
       CompleteMinimal B1 -> .. -> CompleteMinimal Bk ->
       CompleteMinimal (T A1 .. An)

   declared with [tmDefinitionU] and registered with [tmExistingInstance]. Its
   [Refinable] and [Complete] arguments are [refinable_T_inst] and
   [complete_T_inst]. The predicates, the relations, both inductives and the
   equalities share one quality, as they do in [CompleteMinimal], since the
   proof eliminates each of them into the others.

   The generator handles the inductives [gen_refinable] handles. For the
   others it prints what it cannot generate yet and declares nothing. *)
From MetaRocq.Utils Require Export utils.
From MetaRocq.Template Require Import All.

From Stdlib Require Init.
Import MRMonadNotation.

From IncRocq Require Export Base.
From IncRocq Require Import gen.Utils gen.Source gen.Complete gen.Refinable.

(* ------------------------------------------------------------------ *)
(* Names                                                               *)
(* ------------------------------------------------------------------ *)

Definition cm_lib : dirpath := ["Reformulation"; "IncRocq"].
Definition cm_class_kn : kername := (MPfile cm_lib, "CompleteMinimal").
Definition cm_class : inductive := {| inductive_mind := cm_class_kn; inductive_ind := 0 |}.
Definition is_complete_minimal_kn : kername := (MPfile cm_lib, "is_complete_minimal").

Definition logic_lib : dirpath := ["Logic"; "Prelude"].
Definition eq_ind : inductive := {| inductive_mind := (MPfile logic_lib, "eq"); inductive_ind := 0 |}.
Definition false_ind : inductive :=
  {| inductive_mind := (MPfile logic_lib, "False"); inductive_ind := 0 |}.

(* The tactics that prove the generated lemmas, in Tactics.v. *)
Definition minimality_tactic : string := "IncRocq.Tactics.gen_complete_minimality".
Definition hole_tactic : string := "IncRocq.Tactics.gen_complete_hole".

(* ------------------------------------------------------------------ *)
(* The lemmas                                                          *)
(* ------------------------------------------------------------------ *)

(* Both lemmas have the context of T, followed by one quality [s] for the
   predicates, the relations, the inductives and the equalities, and these
   levels:
     complete_T_minimal  T's .. | uP0 .. uP(k-1) | uR0 .. uR(k-1) | todo | e
     complete_T_hole     T's .. | uP0 .. uP(k-1) | todo | f
   where [todo] is a level above T's universe, when it is not a single level,
   [e] the level of the equalities and [f] that of [False]. *)
Definition sq (s : source) : nat := nquals s.

Definition lemma_quals (s : source) : list name :=
  s.(src_quals) ++ [nAnon].

(* The level of [TODO (T A..)] in a context where it would be [lvar next],
   the number of fresh levels it takes, and their constraints. *)
Definition todo_at (s : source) (next : nat) : Level.t * nat * list UnivConstraint.t :=
  match level_above s.(src_univ) next with
  | Some r => r
  | None => (Level.lzero, 0, [])
  end.

Definition minimal_todo (s : source) := todo_at s (nlevels s + Nat.mul 2 (nslots s)).
Definition hole_todo (s : source) := todo_at s (nlevels s + nslots s).

Definition minimal_nlevels (s : source) : nat :=
  let '(_, kt, _) := minimal_todo s in nlevels s + Nat.mul 2 (nslots s) + kt + 1.

Definition hole_nlevels (s : source) : nat :=
  let '(_, kt, _) := hole_todo s in nlevels s + nslots s + kt + 1.

Definition minimal_universes (s : source) : universes_decl :=
  let '(_, _, cs) := minimal_todo s in
  Polymorphic_ctx
    (AUContext.make
       (mk_bound_names (lemma_quals s) (s.(src_levels) ++ repeat nAnon (minimal_nlevels s - nlevels s)))
       (add_constraints cs s.(src_cstrs))).

Definition hole_universes (s : source) : universes_decl :=
  let '(_, _, cs) := hole_todo s in
  Polymorphic_ctx
    (AUContext.make
       (mk_bound_names (lemma_quals s) (s.(src_levels) ++ repeat nAnon (hole_nlevels s - nlevels s)))
       (add_constraints cs s.(src_cstrs))).

Definition T_levels (s : source) : list Level.t := map Level.lvar (seq_nat 0 (nlevels s)).
Definition T_quals (s : source) : list Quality.t := map qvar (seq_nat 0 (nquals s)).

(* The instances of complete_T and refinement_T in a lemma, with [s] for all
   their own qualities. *)
Definition pred_inst_in (s : source) (uPs : list Level.t) : Instance.t :=
  Instance.make (T_quals s ++ repeat (qvar (sq s)) (nslots s + 1)) (T_levels s ++ uPs).

Definition rel_inst_in (s : source) (uRs : list Level.t) (todo : list Level.t) : Instance.t :=
  Instance.make (T_quals s ++ repeat (qvar (sq s)) (nslots s + 1)) (T_levels s ++ uRs ++ todo).

(* Under the parameters and [d] binders after them, the binder [j] after the
   parameters and the parameter [Ai]. *)
Definition after (d j : nat) : term := tRel (d - 1 - j).
Definition param_at (s : source) (d i : nat) : term := tRel (d + s.(src_nparams) - 1 - i).

Definition T_at (s : source) (d : nat) : term :=
  mkApps (tInd s.(src_ind) s.(src_inst)) (map (param_at s d) (seq_nat 0 s.(src_nparams))).

Definition slot_level (s : source) (i : nat) : Level.t :=
  match param_quality_level (slot_sort s i) with
  | Some (_, l) => l
  | None => Level.lzero
  end.

Definition slot_quality (s : source) (i : nat) : Quality.t :=
  match param_quality_level (slot_sort s i) with
  | Some (q, _) => q
  | None => Quality.qType
  end.

Definition s_rel (s : source) : relevance := RelevanceVar (QVar.Var (sq s)).
Definition anon (r : relevance) : aname := {| binder_name := nAnon; binder_relevance := r |}.

(* The binders P0 .. P(k-1), at the levels [uPs], under the parameters. *)
Definition pred_binders_at (s : source) (uPs : list Level.t) : list (aname * term) :=
  map (fun i =>
    (named ("P" ^ string_of_nat i) Relevant,
     tProd (named "a" (sort_relevance (slot_sort s i))) (slot_type s i i)
           (tSort (sQVar (QVar.Var (sq s)) (lvl (nth i uPs Level.lzero))))))
    (seq_nat 0 (nslots s)).

(* The binders R0 .. R(k-1), at the levels [uRs], under the parameters and
   [d] more binders. *)
Definition rel_binders_at (s : source) (d : nat) (uRs : list Level.t) : list (aname * term) :=
  map (fun i =>
    let r := sort_relevance (slot_sort s i) in
    (named ("R" ^ string_of_nat i) Relevant,
     tProd (named "a" r) (slot_type s (d + i) i)
       (tProd (named "b" r) (slot_type s (d + i + 1) i)
          (tSort (sQVar (QVar.Var (sq s)) (lvl (nth i uRs Level.lzero)))))))
    (seq_nat 0 (nslots s)).

Definition eq_at (s : source) (q : Quality.t) (l e : Level.t) (A x y : term) : term :=
  mkApps (tInd eq_ind (Instance.make [q; qvar (sq s)] [l; e])) [A; x; y].

(* forall A.. P.. R.., (forall a, Pi a -> forall a', Ri a' a -> a' = a) -> .. ->
   forall x, complete_T A.. P.. x -> forall x', refinement_T A.. R.. x' x -> x' = x *)
Definition minimal_statement (s : source) (pred rel : inductive) : term :=
  let k := nslots s in
  let n := s.(src_nparams) in
  let uPs := map (fun i => Level.lvar (nlevels s + i)) (seq_nat 0 k) in
  let uRs := map (fun i => Level.lvar (nlevels s + k + i)) (seq_nat 0 k) in
  let '(lt, kt, _) := minimal_todo s in
  let e := Level.lvar (nlevels s + (Nat.mul 2 k) + kt) in
  let rs := s_rel s in
  (* HMi, under the parameters, P (k), R (k) and HM0 .. HM(i-1). *)
  let hyps :=
    map (fun i =>
      let d := (Nat.mul 2 k) + i in
      let ra := sort_relevance (slot_sort s i) in
      let B d' := slot_type s d' i in
      (named ("HM" ^ string_of_nat i) rs,
       tProd (named "a" ra) (B d)
         (tProd (anon rs) (mkApps (after (d + 1) i) [tRel 0])
            (tProd (named "a'" ra) (B (d + 2))
               (tProd (anon rs) (mkApps (after (d + 3) (k + i)) [tRel 0; tRel 2])
                  (eq_at s (slot_quality s i) (slot_level s i) e (B (d + 4)) (tRel 1) (tRel 3)))))))
      (seq_nat 0 k) in
  let preds_at d := map (fun i => after d i) (seq_nat 0 k) in
  let rels_at d := map (fun i => after d (k + i)) (seq_nat 0 k) in
  let params_at d := map (param_at s d) (seq_nat 0 n) in
  let D := (Nat.mul 3 k) in
  let rT := sort_relevance s.(src_sort) in
  mkProds (param_binders s ++ pred_binders_at s uPs ++ rel_binders_at s k uRs ++ hyps)
    (tProd (named "x" rT) (T_at s D)
       (tProd (anon rs) (mkApps (tInd pred (pred_inst_in s uPs))
                                (params_at (D + 1) ++ preds_at (D + 1) ++ [tRel 0]))
          (tProd (named "x'" rT) (T_at s (D + 2))
             (tProd (anon rs) (mkApps (tInd rel (rel_inst_in s uRs (repeat lt kt)))
                                      (params_at (D + 3) ++ rels_at (D + 3) ++ [tRel 0; tRel 2]))
                (eq_at s inc_quality lt e (T_at s (D + 4)) (tRel 1) (tRel 3)))))).

(* forall A.. P.., complete_T A.. P.. (TODO (T A..)) -> False *)
Definition hole_statement (s : source) (pred : inductive) : term :=
  let k := nslots s in
  let n := s.(src_nparams) in
  let uPs := map (fun i => Level.lvar (nlevels s + i)) (seq_nat 0 k) in
  let '(lt, kt, _) := hole_todo s in
  let f := Level.lvar (nlevels s + k + kt) in
  let todo := mkApps (tConst inc_todo_kn (Instance.make [] [lt])) [T_at s k] in
  mkProds (param_binders s ++ pred_binders_at s uPs)
    (tProd (anon (s_rel s))
       (mkApps (tInd pred (pred_inst_in s uPs))
               (map (param_at s k) (seq_nat 0 n) ++ map (after k) (seq_nat 0 k) ++ [todo]))
       (tInd false_ind (Instance.make [qvar (sq s)] [f]))).

(* ------------------------------------------------------------------ *)
(* The instance                                                        *)
(* ------------------------------------------------------------------ *)

(* The context of the instance extends T's levels with those of
   refinable_T_inst, then those of complete_T_inst, whose contexts both start
   with T's levels, and then with
     e | fT | mT | m0 f0 .. m(k-1) f(k-1)
   the level of the equalities, and the levels of [False] and of the class of
   each [CompleteMinimal]. Its qualities are those refinable_T_inst keeps of
   T, followed by [s]. In refinable_T_inst and complete_T_inst, the levels of
   slot [i] are [lvar (nlevels + i)] and [lvar (nlevels + k + i)], and their
   instances end with [Refinable@{_; a b c} (T A..)] and
   [Complete@{_ _; a b c} (T A..)]. *)
Definition levels_of (u : universes_decl) : nat :=
  match u with
  | Polymorphic_ctx (mkBoundNames _ us, _) => List.length us
  | Monomorphic_ctx => 0
  end.

Definition constraints_of (u : universes_decl) : ConstraintSet.t :=
  match u with
  | Polymorphic_ctx (_, cs) => cs
  | Monomorphic_ctx => ConstraintSet.empty
  end.

Fixpoint strip_prods (m : nat) (t : term) : term :=
  match m, t with
  | S m', tProd _ _ body => strip_prods m' body
  | _, _ => t
  end.

(* The levels of the class instance at the end of the type [ty] of an
   instance, past [m] binders. *)
Definition conclusion_levels (m : nat) (ty : term) : list Level.t :=
  match strip_prods m ty with
  | tApp (tInd _ u) _ => Instance.universes u
  | _ => []
  end.

Definition gen_complete_minimal_instance (s : source) (min_kn hole_kn : kername)
    (ref_inst com_inst : kername) (ref_body com_body : constant_body)
    (cm_cstrs : ConstraintSet.t) : TemplateMonad unit :=
  let n := s.(src_nparams) in
  let k := nslots s in
  let nl := nlevels s in
  let nkept := List.length (kept_qualities s) in
  let s' := nkept in
  let nR := levels_of ref_body.(cst_universes) - nl in
  let nC := levels_of com_body.(cst_universes) - nl in
  (* refinable_T_inst's levels are the first ones of the instance, and
     complete_T_inst's follow them. *)
  let R_lvl j := Level.lvar j in
  let C_lvl j := if Nat.ltb j nl then Level.lvar j else Level.lvar (nR + j) in
  let ref_levels := map R_lvl (seq_nat 0 (nl + nR)) in
  let com_levels := map C_lvl (seq_nat 0 (nl + nC)) in
  let e := Level.lvar (nl + nR + nC) in
  let fT := Level.lvar (nl + nR + nC + 1) in
  let mT := Level.lvar (nl + nR + nC + 2) in
  let m_i i := Level.lvar (nl + nR + nC + 3 + (Nat.mul 2 i)) in
  let f_i i := Level.lvar (nl + nR + nC + 4 + (Nat.mul 2 i)) in
  let nlev := nl + nR + nC + 3 + (Nat.mul 2 k) in
  let ref_inst_u := Instance.make (map qvar (seq_nat 0 nkept) ++ repeat (qvar s') (k + 1)) ref_levels in
  let com_inst_u := Instance.make (map (inst_quality s) (seq_nat 0 (nquals s))
                                   ++ repeat (qvar s') (k + 1)) com_levels in
  let mapped_quals := map (inst_quality s) (seq_nat 0 (nquals s)) ++ [qvar s'] in
  (* The levels of the class instances at the end of the two instances. *)
  match map (inst_level ref_levels) (conclusion_levels (n + k) ref_body.(cst_type)),
        map (inst_level com_levels) (conclusion_levels (n + k) com_body.(cst_type)) with
  | [aR; bR; cR], [aC; bC; cC] =>
  let uR i := Level.lvar (nl + i) in
  let cR_ i := Level.lvar (nl + k + i) in
  let uP i := C_lvl (nl + i) in
  let cP i := C_lvl (nl + k + i) in
  (* The lemmas' instances. *)
  let '(_, kmt, _) := minimal_todo s in
  let min_u := Instance.make mapped_quals
                 (T_levels s ++ map uP (seq_nat 0 k) ++ map uR (seq_nat 0 k)
                  ++ repeat aR kmt ++ [e]) in
  let '(_, kht, _) := hole_todo s in
  let hole_u := Instance.make mapped_quals
                  (T_levels s ++ map uP (seq_nat 0 k) ++ repeat aR kht ++ [fT]) in
  let ref_u i := Instance.make [qvar s'] [slot_level s i; uR i; cR_ i] in
  let com_u i := Instance.make [inc_quality; qvar s'] [slot_level s i; uP i; cP i] in
  let cm_u i := Instance.make [qvar s']
                  [slot_level s i; m_i i; uR i; cR_ i; e; uP i; cP i; f_i i] in
  let cmT_u := Instance.make [qvar s'] [aR; mT; bR; cR; e; bC; cC; fT] in
  let cstrs :=
    add_constraints
      (inst_constraints ref_levels (constraints_of ref_body.(cst_universes))
       ++ inst_constraints com_levels (constraints_of com_body.(cst_universes))
       ++ inst_constraints (Instance.universes min_u)
            (constraints_of (minimal_universes s))
       ++ inst_constraints (Instance.universes hole_u)
            (constraints_of (hole_universes s))
       ++ inst_constraints (Instance.universes cmT_u) cm_cstrs
       ++ flat_map (fun i => inst_constraints (Instance.universes (cm_u i)) cm_cstrs)
                   (seq_nat 0 k)
       ++ (if level_eqb aR aC then [] else [(aR, ConstraintType.Eq, aC)]))
      s.(src_cstrs) in
  let udecl :=
    Polymorphic_ctx
      (AUContext.make
         (mk_bound_names (map (fun j => nth j s.(src_quals) nAnon) (kept_qualities s) ++ [nAnon])
                         (s.(src_levels) ++ repeat nAnon (nlev - nl)))
         cstrs) in
  (* The binders: the parameters in Inc, then HR0 .. HR(k-1), HC0 .. HC(k-1)
     and HM0 .. HM(k-1). Under the parameters and [d] binders, the type of
     slot [i] is [B d i]. *)
  let B d i := map_term_qualities s (slot_type s d i) in
  let param_levels := map (fun so => match param_quality_level so with
                                     | Some (_, l) => l
                                     | None => Level.lzero
                                     end) s.(src_param_sorts) in
  let params :=
    mapi (fun i l => (named ("A" ^ string_of_nat i) Relevant, tSort (sQVar inc_qvar (lvl l))))
         param_levels in
  let HRs := map (fun i => (named ("HR" ^ string_of_nat i) Relevant,
                            mkApps (tInd refinable_class (ref_u i)) [B i i])) (seq_nat 0 k) in
  let HCs := map (fun i => (named ("HC" ^ string_of_nat i) Relevant,
                            mkApps (tInd complete_class (com_u i)) [B (k + i) i])) (seq_nat 0 k) in
  let HMs := map (fun i =>
                    let d := (Nat.mul 2 k) + i in
                    (named ("HM" ^ string_of_nat i) Relevant,
                     mkApps (tInd cm_class (cm_u i)) [B d i; after d i; after d (k + i)]))
                 (seq_nat 0 k) in
  let binders := params ++ HRs ++ HCs ++ HMs in
  let D := (Nat.mul 3 k) in
  let As := map (param_at s D) (seq_nat 0 n) in
  let HR i := after D i in
  let HC i := after D (k + i) in
  let HM i := after D ((Nat.mul 2 k) + i) in
  let T_A := mkApps (tInd s.(src_ind) (map_qualities s s.(src_inst))) As in
  let RI := mkApps (tConst ref_inst ref_inst_u) (As ++ map HR (seq_nat 0 k)) in
  let CI := mkApps (tConst com_inst com_inst_u) (As ++ map HC (seq_nat 0 k)) in
  let Ps := map (fun i => mkApps (tConst is_complete_kn (com_u i)) [B D i; HC i]) (seq_nat 0 k) in
  let Rs := map (fun i => mkApps (tConst refinement_kn (ref_u i)) [B D i; HR i]) (seq_nat 0 k) in
  let Ms := map (fun i => mkApps (tConst is_complete_minimal_kn (cm_u i))
                                 [B D i; HR i; HC i; HM i]) (seq_nat 0 k) in
  let minimal := mkApps (tConst min_kn min_u) (As ++ Ps ++ Rs ++ Ms) in
  let hole := mkApps (tConst hole_kn hole_u) (As ++ Ps) in
  let ty := mkProds binders (mkApps (tInd cm_class cmT_u) [T_A; RI; CI]) in
  let body := mkLams binders
                (mkApps (tConstruct cm_class 0 cmT_u) [T_A; RI; CI; minimal; hole]) in
  let name := "complete_minimal_" ^ s.(src_id) ^ "_inst" in
  tmDefinitionU name udecl ty body ;;
  gr <- tmLocate1 name ;;
  tmExistingInstance export gr
  | _, _ => tmFail "gen_complete_minimal: unexpected type of refinable_T_inst or complete_T_inst"
  end.

(* ------------------------------------------------------------------ *)
(* gen_complete_minimal                                                *)
(* ------------------------------------------------------------------ *)

Definition locate_ind (name : ident) : TemplateMonad (option inductive) :=
  grs <- tmLocate name ;;
  match grs with
  | IndRef ind :: _ => ret (Some ind)
  | _ => ret None
  end.

Definition locate_constant (name : ident) : TemplateMonad (option kername) :=
  grs <- tmLocate name ;;
  match grs with
  | ConstRef kn :: _ => ret (Some kn)
  | _ => ret None
  end.

(* Declares complete_T_minimal, complete_T_hole and complete_minimal_T_inst
   for the inductive described by [s], whose completeness predicate,
   refinement relation and their instances are declared. *)
Definition gen_complete_minimal_generable (s : source) (pred rel : inductive)
    (ref_inst com_inst : kername) : TemplateMonad unit :=
  let id := s.(src_id) in
  let min_name := "complete_" ^ id ^ "_minimal" in
  let hole_name := "complete_" ^ id ^ "_hole" in
  tmLemmaU min_name (minimal_universes s) (minimal_statement s pred rel) minimality_tactic ;;
  tmLemmaU hole_name (hole_universes s) (hole_statement s pred) hole_tactic ;;
  min_kn <- locate_const min_name ;;
  hole_kn <- locate_const hole_name ;;
  ref_body <- tmQuoteConstant ref_inst false ;;
  com_body <- tmQuoteConstant com_inst false ;;
  cm_decl <- tmQuoteInductive cm_class_kn ;;
  match cm_decl.(ind_universes) with
  | Polymorphic_ctx (_, cm_cstrs) =>
      gen_complete_minimal_instance s min_kn hole_kn ref_inst com_inst ref_body com_body cm_cstrs ;;
      tmMsg (min_name ^ ", " ^ hole_name ^ " and complete_minimal_" ^ id ^ "_inst are declared")
  | Monomorphic_ctx => tmFail "gen_complete_minimal: CompleteMinimal is not polymorphic"
  end.

(* Declares the minimality of the complete values of [q] and its instance.
   When the generator cannot build them yet, or [q] has no generated
   completeness predicate or refinement relation, it prints why and declares
   nothing, so that gen_icp_defs can run it on every inductive. It declares
   nothing either when the CompleteMinimal class is not loaded. *)
Definition gen_complete_minimal (q : qualid) : TemplateMonad unit :=
  class <- tmLocate (string_of_kername cm_class_kn) ;;
  match class with
  | [] => ret tt
  | _ =>
      r <- check_refinable q ;;
      match r with
      | NotYet why =>
          tmMsg ("gen_complete_minimal cannot yet generate complete_" ^ q ^ "_minimal: " ^ why)
      | Generable s =>
          let id := s.(src_id) in
          pred <- locate_ind ("complete_" ^ id) ;;
          rel <- locate_ind ("refinement_" ^ id) ;;
          ref_inst <- locate_constant ("refinable_" ^ id ^ "_inst") ;;
          com_inst <- locate_constant ("complete_" ^ id ^ "_inst") ;;
          match pred, rel, ref_inst, com_inst with
          | Some pred, Some rel, Some ri, Some ci => gen_complete_minimal_generable s pred rel ri ci
          | _, _, _, _ =>
              tmMsg ("gen_complete_minimal cannot generate complete_" ^ id
                     ^ "_minimal: complete_" ^ id ^ ", refinement_" ^ id
                     ^ " or their instances are not declared")
          end
      end
  end.
