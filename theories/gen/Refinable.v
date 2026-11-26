(* Generates the structural refinement relation of an inductive, the proofs
   that it is reflexive and transitive, and its [Refinable] instance.

   For an inductive [T A1 .. An] whose parameters are types,
   [gen_refinable "T"] declares

     Inductive refinement_T (A1 : _) .. (An : _)
         (R1 : B1 -> B1 -> Type) .. (Rk : Bk -> Bk -> Type)
       : T A1 .. An -> T A1 .. An -> Type :=
     | refinement_C : forall x1 y1 .. xm ym, prem1 -> .. -> premk ->
                      refinement_T A1 .. An R1 .. Rk (C x1 .. xm) (C y1 .. ym)
     ...
     | refinement_T_todo : forall x,
                           refinement_T A1 .. An R1 .. Rk x (TODO (T A1 .. An))

   with one relation parameter per slot, as for [gen_complete], and one premise
   per field of [C]. A field of type [T A1 .. An] gives
   [refinement_T A1 .. An R1 .. Rk xj yj], and a field of type [Bi] gives
   [Ri xj yj]. The relation is the binary parametricity translation of [T],
   restricted to a single type, with one more constructor that puts every value
   below the hole.

   It then declares, with [tmLemmaU],

     refinement_T_refl : forall A1 .. An R1 .. Rk,
       (forall a, R1 a a) -> .. -> forall x, refinement_T A.. R.. x x
     refinement_T_trans : forall A1 .. An R1 .. Rk,
       (forall a1 a2 a3, R1 a1 a2 -> R1 a2 a3 -> R1 a1 a3) -> .. ->
       forall x y z, refinement_T A.. R.. x y -> refinement_T A.. R.. y z ->
                     refinement_T A.. R.. x z

   proved by [gen_refinement_refl] and [gen_refinement_trans] from
   [Tactics.v], and the instance

     refinable_T_inst : forall A1 .. An, Refinable B1 -> .. -> Refinable Bk ->
                        Refinable (T A1 .. An)

   declared with [tmDefinitionU] and registered with [tmExistingInstance]. The
   relation and the lemmas are sort polymorphic in the parameters, while the
   instance takes the type of every slot in [Inc], as [Refinable] requires.

   The generator handles the shapes [gen_complete] handles, and also needs the
   type of every slot to live in [Inc] or a quality variable. For any other
   inductive it prints what it cannot generate yet and declares nothing. *)
From MetaRocq.Utils Require Export utils.
From MetaRocq.Template Require Import All.

From Stdlib Require Init.
Import MRMonadNotation.

From IncRocq Require Export Base.
From IncRocq Require Import gen.Utils gen.Source.

(* ------------------------------------------------------------------ *)
(* The Refinable class, located by name                                *)
(* ------------------------------------------------------------------ *)

Definition refinable_lib : dirpath := ["Reformulation"; "IncRocq"].
Definition refinable_class_kn : kername := (MPfile refinable_lib, "Refinable").
Definition refinable_class : inductive :=
  {| inductive_mind := refinable_class_kn; inductive_ind := 0 |}.
Definition refinement_kn : kername := (MPfile refinable_lib, "refinement").
Definition is_transitive_kn : kername := (MPfile refinable_lib, "is_transitive").
Definition is_reflexive_kn : kername := (MPfile refinable_lib, "is_reflexive").

(* The tactics that prove the generated lemmas, in Tactics.v. *)
Definition refl_tactic : string := "IncRocq.Tactics.gen_refinement_refl".
Definition trans_tactic : string := "IncRocq.Tactics.gen_refinement_trans".

(* ------------------------------------------------------------------ *)
(* The relation                                                        *)
(* ------------------------------------------------------------------ *)

(* refinement_T has the universe layout of Source.v, with a relation
   [Ri : Bi -> Bi -> Type@{q_slot i; u_slot i}] for each slot [Bi], and one
   more level for [TODO] when the universe of T is not a single level:
     qualities  T's .. | q_slot 0 .. q_slot (k-1) | q_result
     levels     T's .. | u_slot 0 .. u_slot (k-1) | todo *)

(* The level of [TODO (T A..)], the number of fresh levels it takes, and their
   constraints. *)
Definition todo_level (s : source) : Level.t * nat * list UnivConstraint.t :=
  match level_above s.(src_univ) (nlevels s + nslots s) with
  | Some r => r
  | None => (Level.lzero, 0, [])
  end.

Definition rel_nlevels (s : source) : nat :=
  let '(_, k, _) := todo_level s in nlevels s + nslots s + k.

Definition rel_universes (s : source) : universes_decl :=
  let '(_, _, cs) := todo_level s in
  Polymorphic_ctx
    (AUContext.make
       (mk_bound_names (s.(src_quals) ++ repeat nAnon (nslots s + 1))
                       (s.(src_levels) ++ repeat nAnon (rel_nlevels s - nlevels s)))
       (add_constraints cs s.(src_cstrs))).

(* The instance of a constant declared in the relation's own context. *)
Definition rel_inst (s : source) : Instance.t :=
  Instance.make (map qvar (seq_nat 0 (q_result s + 1)))
                (map Level.lvar (seq_nat 0 (rel_nlevels s))).

(* The binders R0 .. R(k-1), under the parameters and R0 .. R(i-1). *)
Definition rel_binders (s : source) : list (aname * term) :=
  map (fun i =>
    let r := sort_relevance (slot_sort s i) in
    (named ("R" ^ string_of_nat i) Relevant,
     tProd (named "a" r) (slot_type s i i)
       (tProd (named "b" r) (slot_type s (i + 1) i)
          (tSort (sQVar (QVar.Var (q_slot s i)) (lvl (u_slot s i)))))))
    (seq_nat 0 (nslots s)).

Definition T_relevance (s : source) : relevance := sort_relevance s.(src_sort).

Definition rel_type (s : source) : term :=
  mkProds (param_binders s ++ rel_binders s)
    (tProd (named "x" (T_relevance s)) (T_applied s 0)
       (tProd (named "y" (T_relevance s)) (T_applied s 1)
          (tSort (sQVar (QVar.Var (q_result s)) (result_universe s))))).

(* [TODO (T A..)] under [d] binders past the parameters and relations. *)
Definition todo_term (s : source) (d : nat) : term :=
  let '(l, _, _) := todo_level s in
  mkApps (tConst inc_todo_kn (Instance.make [] [l])) [T_applied s d].

(* The type of the constructor of refinement_T for the constructor [c],
   number [k], of T. In it, refinement_T itself is the outermost [tRel]. The
   fields come in pairs, [xj] then [yj]. *)
Definition rel_ctor (s : source) (k : nat) (c : constructor_body) : ident * term :=
  let n := s.(src_nparams) in
  let fields := List.rev c.(cstr_args) in
  let m := List.length fields in
  let kinds := flat_map (fun o => match o with Some k => [k] | None => [] end)
                        (field_kinds s c) in
  let field_type (kd : field_kind) (d : nat) :=
    match kd with
    | FRecursive => T_applied s d
    | FSlot i => rel_B s d i
    end in
  let field_binders :=
    flat_map (fun '(j, (d, kd)) =>
      let r := src_relevance s d.(decl_name).(binder_relevance) in
      let depth : nat := Nat.mul 2 j in
      let x : aname * term :=
        ({| binder_name := nNamed ("x" ^ string_of_nat j); binder_relevance := r |},
         field_type kd depth) in
      let y : aname * term :=
        ({| binder_name := nNamed ("y" ^ string_of_nat j); binder_relevance := r |},
         field_type kd (S depth)) in
      [x; y])
      (combine (seq_nat 0 m) (combine fields kinds)) in
  (* One premise per field, in order. Under the [p] premises before it, the
     field [j] is [tRel (2m - 1 - 2j + p)] on the left and
     [tRel (2m - 2 - 2j + p)] on the right. *)
  let premises :=
    mapi (fun p '(j, kd) =>
      let x := tRel (2 * m - 1 - 2 * j + p) in
      let y := tRel (2 * m - 2 - 2 * j + p) in
      match kd with
      | FRecursive =>
          ({| binder_name := nAnon; binder_relevance := RelevanceVar (QVar.Var (q_result s)) |},
           mkApps (tRel (n + nslots s + 2 * m + p)) (params_and_slots s (2 * m + p) ++ [x; y]))
      | FSlot i =>
          ({| binder_name := nAnon; binder_relevance := RelevanceVar (QVar.Var (q_slot s i)) |},
           mkApps (rel_S s (2 * m + p) i) [x; y])
      end) (combine (seq_nat 0 m) kinds) in
  let np := List.length premises in
  let d := 2 * m + np in
  let value (side : nat) :=
    mkApps (tConstruct s.(src_ind) k s.(src_inst))
      (map (rel_A s d) (seq_nat 0 n)
       ++ map (fun j => tRel (2 * m - 1 - 2 * j - side + np)) (seq_nat 0 m)) in
  let concl := mkApps (tRel (n + nslots s + d)) (params_and_slots s d ++ [value 0; value 1]) in
  ("refinement_" ^ c.(cstr_name),
   mkProds (param_binders s ++ rel_binders s ++ field_binders ++ premises) concl).

(* The constructor that puts every value below the hole. *)
Definition rel_todo_ctor (s : source) : ident * term :=
  let n := s.(src_nparams) in
  ("refinement_" ^ s.(src_id) ^ "_todo",
   mkProds (param_binders s ++ rel_binders s)
     (tProd (named "x" (T_relevance s)) (T_applied s 0)
        (mkApps (tRel (n + nslots s + 1)) (params_and_slots s 1 ++ [tRel 0; todo_term s 1])))).

Definition rel_body (s : source) (ctors : list (ident * term)) : mutual_inductive_body :=
  {| ind_finite := Finite;
     ind_npars := s.(src_nparams) + nslots s;
     ind_params := [];
     ind_bodies :=
       [{| ind_name := "refinement_" ^ s.(src_id);
           ind_indices := [];
           ind_sort := sQVar (QVar.Var (q_result s)) (result_universe s);
           ind_type := rel_type s;
           ind_kelim := IntoAny;
           ind_ctors := map (fun '(nm, ty) =>
                              {| cstr_name := nm; cstr_args := []; cstr_indices := [];
                                 cstr_type := ty; cstr_arity := 0 |}) ctors;
           ind_projs := [];
           ind_relevance := Relevant |}];
     ind_universes := rel_universes s;
     ind_variance := None |}.

(* ------------------------------------------------------------------ *)
(* The lemmas                                                          *)
(* ------------------------------------------------------------------ *)

(* refinement_T at the relation's own instance, applied to the parameters,
   the relations and [args], under [d] binders past them. *)
Definition rel_applied (s : source) (rel : inductive) (d : nat) (args : list term) : term :=
  mkApps (tInd rel (rel_inst s)) (params_and_slots s d ++ args).

Definition slot_relevance (s : source) (i : nat) : relevance :=
  sort_relevance (slot_sort s i).

Definition rel_relevance (s : source) (i : nat) : relevance :=
  RelevanceVar (QVar.Var (q_slot s i)).

(* forall A.. R.., (forall a, R0 a a) -> .. -> forall x, refinement_T A.. R.. x x *)
Definition refl_statement (s : source) (rel : inductive) : term :=
  let k := nslots s in
  let hyps :=
    map (fun i =>
      (named ("HR" ^ string_of_nat i) (rel_relevance s i),
       tProd (named "a" (slot_relevance s i)) (rel_B s i i)
         (mkApps (rel_S s (i + 1) i) [tRel 0; tRel 0]))) (seq_nat 0 k) in
  mkProds (param_binders s ++ rel_binders s ++ hyps)
    (tProd (named "x" (T_relevance s)) (T_applied s k)
       (rel_applied s rel (k + 1) [tRel 0; tRel 0])).

(* forall A.. R.., (forall a1 a2 a3, R0 a1 a2 -> R0 a2 a3 -> R0 a1 a3) -> .. ->
   forall x y z, refinement_T .. x y -> refinement_T .. y z -> refinement_T .. x z *)
Definition trans_statement (s : source) (rel : inductive) : term :=
  let k := nslots s in
  let anon (r : relevance) := {| binder_name := nAnon; binder_relevance := r |} in
  let hyps :=
    map (fun i =>
      let ra := slot_relevance s i in
      let rr := rel_relevance s i in
      let R (d : nat) (args : list term) := mkApps (rel_S s d i) args in
      (named ("HT" ^ string_of_nat i) rr,
       tProd (named "a1" ra) (rel_B s i i)
         (tProd (named "a2" ra) (rel_B s (i + 1) i)
            (tProd (named "a3" ra) (rel_B s (i + 2) i)
               (tProd (anon rr) (R (i + 3) [tRel 2; tRel 1])
                  (tProd (anon rr) (R (i + 4) [tRel 2; tRel 1])
                     (R (i + 5) [tRel 4; tRel 2]))))))) (seq_nat 0 k) in
  let rt := RelevanceVar (QVar.Var (q_result s)) in
  mkProds (param_binders s ++ rel_binders s ++ hyps)
    (tProd (named "x" (T_relevance s)) (T_applied s k)
       (tProd (named "y" (T_relevance s)) (T_applied s (k + 1))
          (tProd (named "z" (T_relevance s)) (T_applied s (k + 2))
             (tProd (anon rt) (rel_applied s rel (k + 3) [tRel 2; tRel 1])
                (tProd (anon rt) (rel_applied s rel (k + 4) [tRel 2; tRel 1])
                   (rel_applied s rel (k + 5) [tRel 4; tRel 2])))))).

(* ------------------------------------------------------------------ *)
(* The instance                                                        *)
(* ------------------------------------------------------------------ *)

(* The index of the quality of each slot's sort in T's context, without T's
   own quality, or None when that sort is Inc. *)
Definition slot_qualities (s : source) : list (option nat) :=
  map (fun '(_, so) => match so with
                       | sQVar (QVar.Var j) _ => Some j
                       | _ => None
                       end) s.(src_slots).

(* True when the type of every slot lives in a quality variable or in Inc, so
   that it can be instantiated at Inc. *)
Definition slots_in_qvars (s : source) : bool :=
  forallb (fun '(_, so) => match so with
                           | sQVar (QVar.Var _) _ => true
                           | sQVar q _ => QVar.eqb q inc_qvar
                           | _ => false
                           end) s.(src_slots).

Definition is_param_quality (s : source) (j : nat) : bool :=
  existsb (fun o => match o with Some j' => Nat.eqb j j' | None => false end)
          (slot_qualities s).

(* The qualities of T's context, without its own, that the instance keeps:
   those of no slot. *)
Definition kept_qualities (s : source) : list nat :=
  filter (fun j => negb (is_param_quality s j)) (seq_nat 0 (nquals s)).

(* The position of [j] in [l]. *)
Fixpoint index_of (j : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: rest => if Nat.eqb x j then 0 else S (index_of j rest)
  end.

(* What the quality [j] of T's context, without its own, becomes in the
   instance: Inc for the quality of a slot, and its position among the kept
   ones otherwise. *)
Definition inst_quality (s : source) (j : nat) : Quality.t :=
  if is_param_quality s j then inc_quality
  else qvar (index_of j (kept_qualities s)).

Definition map_qualities (s : source) (u : Instance.t) : Instance.t :=
  Instance.make
    (map (fun q => match q with
                   | Quality.qVar (QVar.Var j) => inst_quality s j
                   | _ => q
                   end) (Instance.qualities u))
    (Instance.universes u).

(* [map_qualities] on every universe instance in the type of a slot. *)
Fixpoint map_term_qualities (s : source) (t : term) : term :=
  match t with
  | tInd ind u => tInd ind (map_qualities s u)
  | tConst kn u => tConst kn (map_qualities s u)
  | tConstruct ind k u => tConstruct ind k (map_qualities s u)
  | tApp f args => tApp (map_term_qualities s f) (List.map (map_term_qualities s) args)
  | _ => t
  end.

Definition gen_refinable_instance (s : source) (rel : inductive)
    (refl_kn trans_kn : kername) (class_cstrs : ConstraintSet.t) : TemplateMonad unit :=
  let n := s.(src_nparams) in
  let k := nslots s in
  let nkept := List.length (kept_qualities s) in
  (* Qualities: the kept ones of T, one per relation, and the result's. *)
  let qR' i := nkept + i in
  let qr' := nkept + k in
  (* Levels: T's, one per relation, one per class level, then fresh ones. *)
  let base := nlevels s + k in
  let c_i i := Level.lvar (base + i) in
  let next := base + k in
  let level_of so := match param_quality_level so with
                     | Some (_, l) => l
                     | None => Level.lzero
                     end in
  let param_levels := map level_of s.(src_param_sorts) in
  let slot_levels := map (fun '(_, so) => level_of so) s.(src_slots) in
  match level_above s.(src_univ) next with
  | None => tmFail "gen_refinable: the universe of the inductive has an increment"
  | Some (t1, k1, cs1) =>
  match level_above (result_universe s) (next + k1) with
  | None => tmFail "gen_refinable: the universe of the relation has an increment"
  | Some (t2, k2, cs2) =>
  let t3 := Level.lvar (next + k1 + k2) in
  let nfresh := k + k1 + k2 + 1 in
  let arg_inst i :=
    Instance.make [qvar (qR' i)] [nth i slot_levels Level.lzero; u_slot s i; c_i i] in
  let res_inst := Instance.make [qvar qr'] [t1; t2; t3] in
  (* The relation's context, with T's qualities mapped as above and its TODO
     level, if it has one of its own, at t1. *)
  let '(_, ktodo, _) := todo_level s in
  let rinst :=
    Instance.make
      (map (inst_quality s) (seq_nat 0 (nquals s))
       ++ map (fun i => qvar (qR' i)) (seq_nat 0 k) ++ [qvar qr'])
      (map Level.lvar (seq_nat 0 (nlevels s + k)) ++ repeat t1 ktodo) in
  let T_inst := map_qualities s s.(src_inst) in
  let cstrs :=
    add_constraints
      (flat_map (fun i => inst_constraints [nth i slot_levels Level.lzero; u_slot s i; c_i i]
                                           class_cstrs) (seq_nat 0 k)
       ++ inst_constraints [t1; t2; t3] class_cstrs ++ cs1 ++ cs2)
      s.(src_cstrs) in
  let udecl :=
    Polymorphic_ctx
      (AUContext.make
         (mk_bound_names (map (fun j => nth j s.(src_quals) nAnon) (kept_qualities s)
                          ++ repeat nAnon (k + 1))
                         (s.(src_levels) ++ repeat nAnon (k + nfresh)))
         cstrs) in
  (* The parameters, now in Inc, and the binders H0 .. H(k-1) :
     Refinable Bi, under the parameters and H0 .. H(i-1). Under the
     parameters and the instances, Ai is [rel_A s 0 i], Bi is [rel_B s 0 i]
     and Hi is [rel_S s 0 i], since the instances sit where the relations
     sat. The types of the slots have their qualities mapped as T's. *)
  let params :=
    mapi (fun i l => (named ("A" ^ string_of_nat i) Relevant, tSort (sQVar inc_qvar (lvl l))))
         param_levels in
  let inst_binders :=
    map (fun i => (named ("H" ^ string_of_nat i) Relevant,
                   mkApps (tInd refinable_class (arg_inst i))
                          [map_term_qualities s (slot_type s i i)])) (seq_nat 0 k) in
  let binders := params ++ inst_binders in
  let As := map (rel_A s 0) (seq_nat 0 n) in
  let field kn i := mkApps (tConst kn (arg_inst i))
                           [map_term_qualities s (rel_B s 0 i); rel_S s 0 i] in
  let Rs := map (field refinement_kn) (seq_nat 0 k) in
  let T_A := mkApps (tInd s.(src_ind) T_inst) As in
  let relation := mkApps (tInd rel rinst) (As ++ Rs) in
  let trans := mkApps (tConst trans_kn rinst) (As ++ Rs ++ map (field is_transitive_kn) (seq_nat 0 k)) in
  let refl := mkApps (tConst refl_kn rinst) (As ++ Rs ++ map (field is_reflexive_kn) (seq_nat 0 k)) in
  let top := mkApps (tConstruct rel (List.length s.(src_body).(ind_ctors)) rinst) (As ++ Rs) in
  let ty := mkProds binders (mkApps (tInd refinable_class res_inst) [T_A]) in
  let body := mkLams binders
                (mkApps (tConstruct refinable_class 0 res_inst) [T_A; relation; trans; refl; top]) in
  let name := "refinable_" ^ s.(src_id) ^ "_inst" in
  tmDefinitionU name udecl ty body ;;
  gr <- tmLocate1 name ;;
  tmExistingInstance export gr
  end
  end.

(* ------------------------------------------------------------------ *)
(* gen_refinable                                                       *)
(* ------------------------------------------------------------------ *)

Definition locate_const (name : ident) : TemplateMonad kername :=
  gr <- tmLocate1 name ;;
  match gr with
  | ConstRef kn => ret kn
  | _ => tmFail ("gen_refinable: " ^ name ^ " is not a constant")
  end.

(* Declares refinement_T, its two lemmas and refinable_T_inst for the
   inductive described by [s], which the generator can handle. *)
Definition gen_refinable_generable (s : source) : TemplateMonad unit :=
  let ctors := map (fun '(k, c) => rel_ctor s k c)
                   (combine (seq_nat 0 (List.length s.(src_body).(ind_ctors)))
                            s.(src_body).(ind_ctors)) in
  let rel_name := "refinement_" ^ s.(src_id) in
  tmMkInductive' (rel_body s (ctors ++ [rel_todo_ctor s])) ;;
  rgr <- tmLocate1 rel_name ;;
  match rgr with
  | IndRef rel =>
      tmLemmaU (rel_name ^ "_refl") (rel_universes s) (refl_statement s rel) refl_tactic ;;
      tmLemmaU (rel_name ^ "_trans") (rel_universes s) (trans_statement s rel) trans_tactic ;;
      refl_kn <- locate_const (rel_name ^ "_refl") ;;
      trans_kn <- locate_const (rel_name ^ "_trans") ;;
      class_decl <- tmQuoteInductive refinable_class_kn ;;
      match class_decl.(ind_universes) with
      | Polymorphic_ctx (_, class_cstrs) =>
          gen_refinable_instance s rel refl_kn trans_kn class_cstrs ;;
          tmMsg (rel_name ^ ", its lemmas and refinable_" ^ s.(src_id)
                 ^ "_inst are declared")
      | Monomorphic_ctx => tmFail "gen_refinable: Refinable is not polymorphic"
      end
  | _ => tmFail "gen_refinable: the relation was not declared"
  end.

(* Either the description of [q], or what about it the generator cannot handle
   yet. *)
Definition check_refinable (q : qualid) : TemplateMonad (generable source) :=
  r <- check_source q ;;
  match r with
  | NotYet why => ret (NotYet why)
  | Generable s =>
      if slots_in_qvars s then ret (Generable s)
      else ret (NotYet "a parameter or the type of a field is not sort polymorphic, so it has no Refinable instance")
  end.

(* Declares the refinement relation of [q], its lemmas and its instance. When
   the generator cannot build them yet, it prints why and declares nothing, so
   that gen_icp_defs can run it on every inductive. It declares nothing either
   when the Refinable class is not loaded. *)
Definition gen_refinable (q : qualid) : TemplateMonad unit :=
  class <- tmLocate (string_of_kername refinable_class_kn) ;;
  match class with
  | [] => ret tt
  | _ =>
      r <- check_refinable q ;;
      match r with
      | Generable s => gen_refinable_generable s
      | NotYet why =>
          tmMsg ("gen_refinable cannot yet generate refinement_" ^ q ^ ": " ^ why)
      end
  end.
