(* Exported so that clients can write the argument of gen_icp_defs as a
   string literal, such as "nat".  [qualid] is MetaRocq's own string type,
   and utils provides the notation for its literals. *)
From MetaRocq.Utils Require Export utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Pretty.

From Stdlib Require Init.
Import MRMonadNotation.

From IncRocq Require Export Base.
From IncRocq Require Import gen.Utils.

Definition mkAnon relevance := {| binder_name := nAnon; binder_relevance := relevance |}.

Definition tmLocateConstRef (q : qualid) : TemplateMonad (global_reference * kername) :=
  gr <- tmLocate1 q ;;
  match gr with
  | ConstRef kn => ret (gr, kn)
  | _ => tmFail "not a constant"
  end.

(* Returns the full constant_body of `id ^ "_poly_rec"`, for the inductive
   [kn] whose name is [id]. *)
Definition get_eliminator_body (kn : kername) (id : ident) : TemplateMonad constant_body :=
  let suffix := "_poly_rec" in
  cref <- tmLocateConstRef (qualify_in kn (id ^ suffix)) ;;
  let: (_, kn) := cref in
  tmQuoteConstant kn false.

Definition poly_ctx_no_constraints (bnames : bound_names) : universes_decl :=
  let ctx := AUContext.make bnames ConstraintSet.empty in
  Polymorphic_ctx ctx.

(* Builds [TODO@{todo_level} ind]. *)
Definition mkHoleInd (todo_kn : kername) (ind : term) (todo_level : Level.t) : term :=
  mkApp (tConst todo_kn (Instance.make [] [todo_level])) ind.

(* ------------------------------------------------------------------ *)
(* Substitute quality variable q_idx → Inc, shift variables above it  *)
(* ------------------------------------------------------------------ *)

(* Replace quality variable q_idx with inc_q; shift QVar.Var i (i > q_idx) down by 1. *)
Definition subst_sort_quality_at (inc_q : Quality.t) (q_idx : nat) (q : Quality.t) : Quality.t :=
  match q with
  | Quality.qVar (QVar.Var i) =>
      if Nat.eqb i q_idx then inc_q
      else if Nat.ltb i q_idx then q
      else Quality.qVar (QVar.Var (Nat.pred i))
  | _ => q
  end.

Definition subst_sort_instance_at (inc_q : Quality.t) (q_idx : nat) (u : Instance.t) : Instance.t :=
  Instance.make
    (List.map (subst_sort_quality_at inc_q q_idx) (Instance.qualities u))
    (Instance.universes u).

Definition subst_sort_relevance_at (inc_qv : QVar.t) (q_idx : nat) (r : relevance) : relevance :=
  match r with
  | RelevanceVar (QVar.Var i) =>
      if Nat.eqb i q_idx then RelevanceVar inc_qv
      else if Nat.ltb i q_idx then r
      else RelevanceVar (QVar.Var (Nat.pred i))
  | _ => r
  end.

Definition subst_sort_aname_at (inc_qv : QVar.t) (q_idx : nat) (b : aname) : aname :=
  {| binder_name      := binder_name b;
     binder_relevance := subst_sort_relevance_at inc_qv q_idx (binder_relevance b) |}.

(* Structural traversal substituting quality variable q_idx → inc_q/inc_qv.
   Only cases that appear in eliminator types are handled; everything
   else is returned unchanged.  *)
Fixpoint subst_sort_at (inc_q : Quality.t) (inc_qv : QVar.t) (q_idx : nat) (t : term) : term :=
  match t with
  | tSort (Sort.sQVar (QVar.Var i) lvl) =>
      if Nat.eqb i q_idx then tSort (Sort.sQVar inc_qv lvl)
      else if Nat.ltb i q_idx then t
      else tSort (Sort.sQVar (QVar.Var (Nat.pred i)) lvl)
  | tSort _ => t
  | tProd b dom codom =>
      tProd (subst_sort_aname_at inc_qv q_idx b)
            (subst_sort_at inc_q inc_qv q_idx dom)
            (subst_sort_at inc_q inc_qv q_idx codom)
  | tLambda b dom body =>
      tLambda (subst_sort_aname_at inc_qv q_idx b)
              (subst_sort_at inc_q inc_qv q_idx dom)
              (subst_sort_at inc_q inc_qv q_idx body)
  | tLetIn b def ty body =>
      tLetIn (subst_sort_aname_at inc_qv q_idx b)
             (subst_sort_at inc_q inc_qv q_idx def)
             (subst_sort_at inc_q inc_qv q_idx ty)
             (subst_sort_at inc_q inc_qv q_idx body)
  | tApp hd args =>
      tApp (subst_sort_at inc_q inc_qv q_idx hd)
           (List.map (subst_sort_at inc_q inc_qv q_idx) args)
  | tInd ind u         => tInd ind (subst_sort_instance_at inc_q q_idx u)
  | tConst kn u        => tConst kn (subst_sort_instance_at inc_q q_idx u)
  | tConstruct ind k u => tConstruct ind k (subst_sort_instance_at inc_q q_idx u)
  | tCast t' k ty      => tCast (subst_sort_at inc_q inc_qv q_idx t') k
                                (subst_sort_at inc_q inc_qv q_idx ty)
  | tProj proj t'      => tProj proj (subst_sort_at inc_q inc_qv q_idx t')
  | _                  => t
  end.

(* ------------------------------------------------------------------ *)
(* Helpers to extract the scrutinee domain from the substituted type   *)
(* ------------------------------------------------------------------ *)

(* Gets the relevance of the eliminator's output sort, which the hole case's
   binder takes.  The binder after the uniform parameters is
   P : forall is, ind is -> Sort, and the relevance comes from the quality
   variable of that Sort.  Falls back to Relevant when that sort has no
   quality variable. *)
Definition get_output_relevance (nb_uparams : nat) (subst_ty : term) : relevance :=
  match skip_n_prods nb_uparams subst_ty with
  | Some (tProd _ p_ty _) =>
      match final_codomain p_ty with
      | tSort (Sort.sQVar q _) => RelevanceVar q
      | _ => Relevant  (* fallback *)
      end
  | _ => Relevant  (* fallback *)
  end.

(* Checks whether t mentions the inductive ind.  Only the term formers that
   occur in eliminator types are traversed, and any other term counts as not
   mentioning it. *)
Fixpoint mentions_ind (ind : inductive) (t : term) : bool :=
  match t with
  | tInd i _              => eqb i ind
  | tProd _ d c           => mentions_ind ind d || mentions_ind ind c
  | tLambda _ d c         => mentions_ind ind d || mentions_ind ind c
  | tLetIn _ b ty c       => mentions_ind ind b || mentions_ind ind ty || mentions_ind ind c
  | tApp f args           => mentions_ind ind f || existsb (mentions_ind ind) args
  | tCast c _ ty          => mentions_ind ind c || mentions_ind ind ty
  | _                     => false
  end.

(* Counts the leading binders of the eliminator elim_ty whose types do not
   mention ind, up to P, which is the first one that does. *)
Fixpoint count_uniform_params (ind : inductive) (elim_ty : term) : nat :=
  match elim_ty with
  | tProd _ dom codom =>
      if mentions_ind ind dom then 0 else S (count_uniform_params ind codom)
  | _ => 0
  end.

(* Splits off the first n binders of the product ty and returns them in
   order, with the type under them.  For example, for n = 2,
   forall x y z, T gives ([x; y], forall z, T).  Returns None when ty has
   fewer than n binders. *)
Fixpoint split_prods (n : nat) (ty : term) : option (list (aname * term) * term) :=
  match n with
  | 0 => Some ([], ty)
  | S k =>
    match ty with
    | tProd na dom codom =>
        option_map (fun p => let '(bs, rest) := p in ((na, dom) :: bs, rest))
                   (split_prods k codom)
    | _ => None
    end
  end.

Definition get_scrutinee_domain (nb_skips : nat) (ty : term) : option term :=
  match skip_n_prods nb_skips ty with
  | Some (tProd _ dom _) => Some dom
  | _                    => None
  end.

(* ------------------------------------------------------------------ *)
(* Drop a quality name at a given index from poly_rec's bound names    *)
(* ------------------------------------------------------------------ *)

Definition drop_quality_at_idx (q_idx : nat) (bn : bound_names) : bound_names :=
  match bn with
  | mkBoundNames qs us => mk_bound_names (list_remove_nth q_idx qs) us
  end.

(* ------------------------------------------------------------------ *)
(* Utilities for rewrite rule string generation                        *)
(* ------------------------------------------------------------------ *)

Definition gen_univ_name (i : nat) : string := "u" ^ string_of_nat i.

Definition gen_univ_names (us : list name) : list string :=
  mapi (fun i n => match n with nNamed s => s | nAnon => gen_univ_name i end) us.

(* ------------------------------------------------------------------ *)
(* Recursiveness detection for constructor arguments                   *)
(* ------------------------------------------------------------------ *)

(* Returns [Some m] when a constructor argument's type [ty] has the form
   [forall x1 … xm, I …], with [I] the inductive being defined, and [None]
   otherwise.  For example, [itree] gives [Some 0] and [nat -> itree]
   gives [Some 1].  [ind_idx] is the de Bruijn index of [I] in the context
   where [ty] is declared. *)
Fixpoint recursive_binders (ind_idx : nat) (ty : term) : option nat :=
  match ty with
  | tRel k          => if Nat.eqb k ind_idx then Some 0 else None
  | tApp (tRel k) _ => if Nat.eqb k ind_idx then Some 0 else None
  | tProd _ _ codom => option_map S (recursive_binders (S ind_idx) codom)
  | _ => None
  end.

(* For each constructor argument in [args], gets [Some m] when its type has
   the form [forall x1 … xm, I …], and [None] otherwise.  The results follow
   declaration order, while [args] lists the arguments last one first. *)
Definition args_recursive_binders (args : context) (nb_params : nat) : list (option nat) :=
  let n := length args in
  (* The argument at position [i] of [args] is declared after [n-1-i] other
     arguments and the [nb_params] parameters, so [I] is
     [tRel (nb_params+n-1-i)] in its type.  For example, for [cons], [args]
     is [[l; a]], so the tail [l] is at position 0 and its type [list A] is
     [tApp (tRel 2) [tRel 1]], with [A] at [tRel 1] and the head [a] at
     [tRel 0]. *)
  rev (mapi (fun i d => recursive_binders (nb_params + n - 1 - i) d.(decl_type)) args).

Definition has_recursive_args (args : context) (nb_params : nat) : bool :=
  existsb (fun o => match o with Some _ => true | None => false end)
          (args_recursive_binders args nb_params).

(* ------------------------------------------------------------------ *)
(* Universe annotation builders for rewrite rules                      *)
(* ------------------------------------------------------------------ *)

(* Universe declaration prefix: "@{u0 u1|}" for the option string *)
Definition univ_decl_string (us : list string) : option string :=
  match us with
  | [] => None
  | _ => Some ("@{" ^ string_join " " us ^ "|}")
  end.

(* Catch symbol with universe annotation: "I_catch@{_;u0 u1}" *)
Definition catch_annot (catch_name : ident) (qs us : list string) : string :=
  catch_name ^ "@{" ^ string_join " " qs ^ ";" ^ string_join " " us ^ "}".

(* ------------------------------------------------------------------ *)
(* Rewrite rule builders                                               *)
(* ------------------------------------------------------------------ *)

(* In the rule builders, [prefix] is the module of the inductive followed by
   a dot, which qualifies the names of its constructors. *)
Definition build_simple_rule
    (prefix : string) (catch_name : ident) (handler_names : list string)
    (qual_strs univ_strs : list string)
    (idx : nat) (c : constructor_body) (nb_params nb_uparams nb_indices : nat)
    : option string * string * string :=
  let udecl := univ_decl_string univ_strs in
  let sym   := catch_annot catch_name qual_strs univ_strs in
  let args := mapi (fun j h => if Nat.eqb j idx then h else "_") handler_names in
  (* The catch takes the uniform parameters before P, and the non-uniform ones
     with the indices after the hole case. *)
  let nb_slots := nb_params - nb_uparams + nb_indices in
  (* Index slots are wildcards too, since the constructor pattern determines
     them. *)
  let all_lhs_args :=
    repeat "_" nb_uparams ++ ["_"] ++ args ++ ["_"] ++ repeat "_" nb_slots in
  let ctor_args := map (fun i => "?a" ^ string_of_nat i) (seq_nat 0 c.(cstr_arity)) in
  (* For a parameterized constructor, the pattern is [@ctor ?B0 … args], with
     [@] so that no implicit arguments get inserted.  The catch's own
     parameter slots are wildcards, so each [?Bi] occurs once in the
     left-hand side, as rewrite rules require.  The right-hand side passes
     the non-uniform [?Bi] to the handler.  In a well-typed term the
     constructor's parameters equal the catch's, so the rule is sound. *)
  let param_hole_vars := map (fun i => "?B" ^ string_of_nat i) (seq_nat 0 nb_params) in
  let ctor_pat :=
    if Nat.eqb nb_params 0 then
      if Nat.eqb c.(cstr_arity) 0 then prefix ^ c.(cstr_name)
      else "(" ^ prefix ^ c.(cstr_name) ^ join_with_space ctor_args ^ ")"
    else
      "(@" ^ prefix ^ c.(cstr_name) ^ join_with_space (param_hole_vars ++ ctor_args) ^ ")" in
  let lhs := sym ^ join_with_space all_lhs_args ^ " " ^ ctor_pat in
  (* A constructor case quantifies over the non-uniform parameters first, so
     the handler gets their ?Bi before the constructor arguments. *)
  let rhs_handler := nth idx handler_names "?H" in
  let rhs := rhs_handler ^ join_with_space (skipn nb_uparams param_hole_vars ++ ctor_args) in
  (udecl, lhs, rhs).

Definition build_recursive_rule
    (prefix : string) (catch_name : ident) (handler_names : list string)
    (qual_strs univ_strs : list string)
    (idx : nat) (c : constructor_body) (nb_params nb_uparams nb_indices : nat)
    : option string * string * string :=
  let udecl := univ_decl_string univ_strs in
  let sym := catch_annot catch_name qual_strs univ_strs in
  (* The non-uniform parameters share the slots after the hole case with the
     indices. *)
  let nb_slots := nb_params - nb_uparams + nb_indices in
  (* On the left-hand side the parameter and index slots are wildcards, since
     ?Bi and ?ai already occur in the constructor pattern and a pattern must
     be linear. *)
  let all_lhs_args :=
    repeat "_" nb_uparams ++ ["?P"] ++ handler_names ++ ["?Hhole"] ++ repeat "_" nb_slots in
  let ctor_args := map (fun i => "?a" ^ string_of_nat i) (seq_nat 0 c.(cstr_arity)) in
  (* The recursive call on the right-hand side passes ?Bi, bound by the
     constructor pattern, for the uniform parameters.  It leaves the
     non-uniform parameters and the indices of the recursive argument as _,
     and elaboration reads them off that argument's type, so the generator
     never prints an index term. *)
  let param_hole_vars := map (fun i => "?B" ^ string_of_nat i) (seq_nat 0 nb_params) in
  let all_rhs_args :=
    firstn nb_uparams param_hole_vars ++ ["?P"] ++ handler_names ++ ["?Hhole"]
    ++ repeat "_" nb_slots in
  let ctor_pat :=
    if Nat.eqb nb_params 0 then "(" ^ prefix ^ c.(cstr_name) ^ join_with_space ctor_args ^ ")"
    else "(@" ^ prefix ^ c.(cstr_name) ^ join_with_space (param_hole_vars ++ ctor_args) ^ ")" in
  let lhs := sym ^ join_with_space all_lhs_args ^ " " ^ ctor_pat in
  let rec_binders := args_recursive_binders c.(cstr_args) nb_params in
  (* The induction hypothesis for an argument under m binders is a function:
     fun x0 … x(m-1) => I_catch … (a x0 … x(m-1)).  For m = 0 it is the plain
     recursive call. *)
  let catch_call := fun a m =>
    let xs := map (fun j => "x" ^ string_of_nat j) (seq_nat 0 m) in
    let call := "(" ^ catch_name ^ join_with_space all_rhs_args ^ " "
                ^ (if Nat.eqb m 0 then a else "(" ^ a ^ join_with_space xs ^ ")") ^ ")" in
    if Nat.eqb m 0 then call else "(fun" ^ join_with_space xs ^ " => " ^ call ^ ")" in
  let rhs_args := flat_map (fun (p : string * option nat) =>
    let '(a, rec) := p in
    match rec with
    | Some m => [a; catch_call a m]
    | None   => [a]
    end
  ) (combine ctor_args rec_binders) in
  (* A constructor case quantifies over the non-uniform parameters first, so
     the handler gets their ?Bi before the arguments and hypotheses. *)
  let rhs := nth idx handler_names "?H"
             ^ join_with_space (skipn nb_uparams param_hole_vars ++ rhs_args) in
  (udecl, lhs, rhs).

Definition build_hole_rule
    (catch_name ind_name todo_qualid : ident)
    (qual_strs univ_strs : list string)
    (nb_params nb_uparams nb_ctors nb_indices : nat) (has_fresh_todo : bool)
    : option string * string * string :=
  let udecl := univ_decl_string univ_strs in
  (* When the inductive's sort is a max universe, the catch has a dedicated
     level for [TODO], the last one in [univ_strs].  The left-hand side
     annotates [TODO] with that level and leaves the catch's slot for it as
     [_], so the level occurs once, as rewrite rules require.

     Without the annotation, the level of [TODO] would be the sort itself.
     For a sort such as [max(Set, u)], that algebraic universe contains
     [Set], so Rocq creates a level the rule does not bind and fails with
     "Universe … is unbound".  With the annotation, a rule for a
     [max(Set, …)] sort registers with a rewrite-rules-break-SR warning,
     because nothing relates the dedicated level to the others.  The
     warning is harmless, since the level of [TODO] does not matter to the
     theory. *)
  let '(catch_univ_strs, todo_annot) :=
    if has_fresh_todo then
      match rev univ_strs with
      | last :: rest_rev => (rev ("_" :: rest_rev), "@{" ^ last ^ "}")
      | []               => (univ_strs, "")
      end
    else (univ_strs, "") in
  let sym   := catch_annot catch_name qual_strs catch_univ_strs in
  let param_args := map (fun i => "?A" ^ string_of_nat i) (seq_nat 0 nb_params) in
  (* Every catch argument except the hole case and the scrutinee is a
     wildcard, so the [?Ai] and [?Ii] are bound only inside the [TODO]
     argument.  The hole case receives the non-uniform parameters and then
     the indices.  The catch carries the universe levels the rule declares,
     since with [_] in their place Rocq fails with "Universe … is unbound".
     The inductive inside [TODO] is left unannotated, and Rocq infers its
     levels from the catch's type, so no level occurs twice in the
     left-hand side. *)
  let index_args := map (fun i => "?I" ^ string_of_nat i) (seq_nat 0 nb_indices) in
  let slot_args  := skipn nb_uparams param_args ++ index_args in
  let wildcards  := repeat "_" (nb_uparams + nb_ctors + 1) in
  let todo_arg   :=
    if Nat.eqb (nb_params + nb_indices) 0 then ind_name
    else "(" ^ ind_name ^ join_with_space (param_args ++ index_args) ^ ")" in
  let lhs := sym ^ join_with_space wildcards
             ^ " ?Hhole" ^ join_with_space (repeat "_" (length slot_args))
             ^ " (" ^ todo_qualid ^ todo_annot ^ " " ^ todo_arg ^ ")" in
  (udecl, lhs, "?Hhole" ^ join_with_space slot_args).

Definition build_catch_rules
    (kn : kername) (id : ident) (ind_body : one_inductive_body) (bound_n : bound_names)
    (todo_qualid : string) (nb_params nb_uparams : nat) (has_fresh_todo : bool)
    : list (option string * string * string) :=
  let ctors    := ind_body.(ind_ctors) in
  let nb_ctors := length ctors in
  let nb_indices := length ind_body.(ind_indices) in
  let catch_name := id ^ "_catch" in
  let prefix := qualify_in kn "" in
  let handler_names := map (fun c => "?H" ^ c.(cstr_name)) ctors in
  let '(mkBoundNames bn_quals bn_univs) := bound_n in
  let univ_strs := gen_univ_names bn_univs in
  let qual_strs := map (fun _ => "_") bn_quals in
  let ctor_rules := mapi (fun idx c =>
    if has_recursive_args c.(cstr_args) nb_params
    then build_recursive_rule prefix catch_name handler_names qual_strs univ_strs idx c
           nb_params nb_uparams nb_indices
    else build_simple_rule    prefix catch_name handler_names qual_strs univ_strs idx c
           nb_params nb_uparams nb_indices
  ) ctors in
  let hole_rule :=
    build_hole_rule catch_name (qualify_in kn id) todo_qualid qual_strs univ_strs
      nb_params nb_uparams nb_ctors nb_indices has_fresh_todo in
  ctor_rules ++ [hole_rule].

(* ------------------------------------------------------------------ *)
(* insert_hole_binder                                                  *)
(* ------------------------------------------------------------------ *)

(* Inserts the hole case in the eliminator.
   For an eliminator of the form:
     forall (P : forall is, ind is -> Type)
     (Hc1 : ... -> P _ c1) ... (Hcn : ... -> P _ cn)
     is (i : ind is), P is i
   This function inserts a hole case after the last constructor case, one
   hole for each choice of the indices:
     forall (P : forall is, ind is -> Type)
     (Hc1 : ... -> P _ c1) ... (Hcn : ... -> P _ cn)
     (_ : forall is, P is (TODO (ind is)))
     is (i : ind is), P is i
   Here is stands for the nb_indices slots, the non-uniform parameters
   followed by the indices.  The function copies their binders and the
   scrutinee's type from the eliminator, since the new case is in the same
   context.  With no slots the case is (_ : P (TODO ind)).  Fails when the
   eliminator has fewer binders than nb_skips, the slots, and the scrutinee
   need. *)
Definition insert_hole_binder
    (todo_kn : kername) (elim_ty : term) (rel : relevance) (depth : nat)
    (nb_skips nb_indices : nat) (todo_level : Level.t)
    : TemplateMonad term :=
  let fix aux ty nb :=
    match ty, nb with
    | tProd b dom codom, 0 =>
      match split_prods nb_indices codom with
      | Some (idx_binders, tProd _ ind _) =>
        let idx_rels := map tRel (rev (seq_nat 0 nb_indices)) in
        let hole_ind := mkHoleInd todo_kn ind todo_level in
        let hole_case := mkApps (tRel (depth + nb_indices)) (idx_rels ++ [hole_ind]) in
        let hole_binder_type :=
          fold_right (fun (p : aname * term) acc => tProd (fst p) (snd p) acc)
                     hole_case idx_binders in
        let lifted_codom := lift0 1 codom in
        ret (tProd b dom (tProd (mkAnon rel) hole_binder_type lifted_codom))
      | _ => tmPrint codom ;; tmFail " does not bind the indices and the scrutinee"
      end
    | tProd b dom codom, S n =>
      res <- aux codom n ;;
      ret (tProd b dom res)
    | _, _ => tmPrint elim_ty ;; tmFail " is not a tProd"
    end
  in
  aux elim_ty nb_skips.

(* ------------------------------------------------------------------ *)
(* Pretty-print the catch symbol's type                                *)
(* ------------------------------------------------------------------ *)

(* Erases universe and quality annotations so the printed type stays
   readable.  MetaRocq's print_instance renders instances such as
   [@{qVar(...)|lvar0}] even with with_universes set to false, so this
   blanks every instance and turns sort variables into Type.  The result
   prints as, for example, "forall P : unit -> Type, P tt -> ...". *)
Fixpoint strip_term_universes (t : term) : term :=
  match t with
  | tSort (Sort.sQVar _ l) => tSort (Sort.sType l)
  | tSort _                => t
  | tInd ind _             => tInd ind Instance.empty
  | tConst kn _            => tConst kn Instance.empty
  | tConstruct ind k _     => tConstruct ind k Instance.empty
  | tProd b d c            => tProd b (strip_term_universes d) (strip_term_universes c)
  | tLambda b d body       => tLambda b (strip_term_universes d) (strip_term_universes body)
  | tLetIn b def ty' body  => tLetIn b (strip_term_universes def) (strip_term_universes ty')
                                       (strip_term_universes body)
  | tApp f args            => tApp (strip_term_universes f) (List.map strip_term_universes args)
  | tCast c k ty'          => tCast (strip_term_universes c) k (strip_term_universes ty')
  | tProj p c              => tProj p (strip_term_universes c)
  | _                      => t
  end.

(* Build a minimal global environment holding just the inductive [decl]
   (under its kername [kn]) so that print_term renders the scrutinee
   inductive by name rather than as UnboundInd.  [TODO] is left to print
   as its fully-qualified kername, which is fine for a diagnostic. *)
Definition print_catch_type (kn : kername) (decl : mutual_inductive_body) (ty : term) : string :=
  let env := add_global_decl empty_global_env (kn, InductiveDecl decl) in
  Tree.to_string
    (PrintTermTree.print_term (empty_ext env) false [] true (strip_term_universes ty)).

(* ------------------------------------------------------------------ *)
(* generate_catch_symbol                                               *)
(* ------------------------------------------------------------------ *)

Definition generate_catch_symbol (q : qualid) : TemplateMonad unit :=
  gr <- tmLocate1 q ;;
  match gr with
  | IndRef ind =>
      let kn := inductive_mind ind in
      let (_, id) := kn in
      decl <- tmQuoteInductive kn ;;
      match List.hd_error decl.(ind_bodies) with
      | None => tmFail "mutual inductive body with no bodies"
      | Some ind_body =>
          let nb_ctors  := List.length ind_body.(ind_ctors) in
          let nb_params := List.length decl.(ind_params) in
          let nb_indices := List.length ind_body.(ind_indices) in
          (* Retrieve poly_rec's constant body for its type and universe context *)
          elim_body <- get_eliminator_body kn id ;;
          let elim_ty := cst_type elim_body in
          (* The uniform parameters come before P.  The non-uniform ones and the
             indices make up the slots between the hole case and the scrutinee. *)
          let nb_uparams := count_uniform_params ind elim_ty in
          let nb_slots  := nb_params - nb_uparams + nb_indices in
          let nb_skips  := nb_uparams + nb_ctors in
          (* Identify which quality variable is the inductive's own sort.
             It is the quality variable of the sort that ind_body.(ind_type)
             returns under all its parameter and index binders.  The same index applies
             in poly_rec's universe context (same quality ordering, output appended last). *)
          let q_idx    := get_ind_sort_quality_idx ind_body.(ind_type) in
          (* Substitute Inc for that quality variable, decrementing the ones
             after it *)
          let subst_ty := subst_sort_at inc_quality inc_qvar q_idx elim_ty in
          (* Extract the scrutinee domain: tApp (tInd ...) [...] for parameterized types *)
          let inc_ind :=
            match get_scrutinee_domain (nb_uparams + nb_ctors + 1 + nb_slots) subst_ty with
            | Some dom => dom
            | None     => tInd ind (Instance.make [] [])  (* fallback, shouldn't happen *)
            end in
          (* The catch takes poly_rec's universe context without the quality
             q_idx, which becomes Inc.  Its level constraints come from the
             inductive, such as uA <= uI for option2, since the catch's type
             mentions the inductive's constructors.  poly_rec lists the
             inductive's levels first and then the output level, so the
             constraints' level indices stay valid. *)
          let bound_n :=
            match cst_universes elim_body with
            | Polymorphic_ctx ctx => drop_quality_at_idx q_idx (fst ctx)
            | _                  => mk_bound_names [] []
            end in
          let ind_level_cstrs :=
            match decl.(ind_universes) with
            | Polymorphic_ctx ctx => snd ctx
            | _                  => ConstraintSet.empty
            end in
          (* Compute the level to use for TODO@{?} (ind ...).
             If the inductive's sort universe is a single level lv, use lv directly
             (covers all single-sort inductives: bool, nat, option, option2, ...).
             If it is max(lv0, lv1, ...), introduce a fresh level u_todo appended
             to bound_n with constraints lvi ≤ u_todo; Rocq's cumulativity then
             accepts TODO@{u_todo} (ind ...) because max(lvi) ≤ u_todo. *)
          let hole_rel := get_output_relevance nb_uparams subst_ty in
          let '(todo_level, bound_n_final, cstrs_final) :=
            match get_ind_sort_universe ind_body.(ind_type) with
            | Some lvl =>
              match Universe.get_is_level lvl with
              | Some lv =>
                  (* single level: use directly *)
                  (lv, bound_n, ind_level_cstrs)
              | None =>
                  (* max of multiple levels: add fresh u_todo to bound_n *)
                  let lvl_exprs := LevelExprSet.elements lvl in
                  let lvars := flat_map (fun x =>
                    match x with
                    | (Level.lvar n, _) => [Level.lvar n]
                    | _ => []
                    end
                  ) lvl_exprs in
                  let fresh_idx :=
                    match bound_n with mkBoundNames _ us => length us end in
                  let fresh_lv := Level.lvar fresh_idx in
                  let new_cstrs := fold_left (fun cs lv =>
                    ConstraintSet.add (lv, ConstraintType.Le0, fresh_lv) cs
                  ) lvars ind_level_cstrs in
                  let bound_n' :=
                    match bound_n with
                    | mkBoundNames qs us => mkBoundNames qs (us ++ [nAnon])
                    end in
                  (fresh_lv, bound_n', new_cstrs)
              end
            | None =>
              (* Fallback: q_idx-based pick_level (shouldn't happen for well-formed types) *)
              let pick_l lvls :=
                nth (Nat.min q_idx (Nat.pred (length lvls))) lvls Level.lzero in
              let lv :=
                match inc_ind with
                | tApp (tInd _ u) _ => pick_l (Instance.universes u)
                | tInd _ u          => pick_l (Instance.universes u)
                | _                 => Level.lzero
                end in
              (lv, bound_n, ind_level_cstrs)
            end in
          tm_catch_type <- insert_hole_binder inc_todo_kn subst_ty hole_rel nb_ctors nb_skips nb_slots todo_level ;;
          tmSymbolU (id ^ "_catch") false
            (Polymorphic_ctx (AUContext.make bound_n_final cstrs_final)) tm_catch_type ;;
          tmMsg (id ^ "_catch : " ^ print_catch_type kn decl tm_catch_type)
      end
  | _ => tmFail "not an inductive"
  end.

(* ------------------------------------------------------------------ *)
(* generate_catch_rules: standalone rule generation                   *)
(* ------------------------------------------------------------------ *)

Definition generate_catch_rules (q : qualid) : TemplateMonad unit :=
  gr <- tmLocate1 q ;;
  match gr with
  | IndRef ind =>
      let kn := inductive_mind ind in
      let (_, id) := kn in
      decl <- tmQuoteInductive kn ;;
      match List.hd_error decl.(ind_bodies) with
      | None => tmFail "no inductive bodies"
      | Some ind_body =>
          elim_body <- get_eliminator_body kn id ;;
          let nb_ctors  := List.length ind_body.(ind_ctors) in
          let nb_params := List.length decl.(ind_params) in
          let nb_uparams := count_uniform_params ind (cst_type elim_body) in
          let q_idx := get_ind_sort_quality_idx ind_body.(ind_type) in
          let bound_n :=
            match cst_universes elim_body with
            | Polymorphic_ctx ctx => drop_quality_at_idx q_idx (fst ctx)
            | _                  => mk_bound_names [] []
            end in
          (* If the inductive's sort is a max universe, generate_catch_symbol added a
             fresh level to bound_n; mirror that here so the catch symbol annotation
             in the rewrite rules matches its declaration.  has_fresh_todo records
             whether that extra TODO level exists, so build_hole_rule can annotate
             `TODO` with it (see the note there). *)
          let has_fresh_todo :=
            match get_ind_sort_universe ind_body.(ind_type) with
            | Some lvl => match Universe.get_is_level lvl with
                          | None => true | Some _ => false end
            | None => false
            end in
          let bound_n_final :=
            if has_fresh_todo
            then match bound_n with
                 | mkBoundNames qs us => mkBoundNames qs (us ++ [nAnon])
                 end
            else bound_n in
          let rules := build_catch_rules kn id ind_body bound_n_final inc_todo_qualid nb_params nb_uparams has_fresh_todo in
          tmRewriteRuleU (id ^ "_catch_red") rules ;;
          tmMsg (id ^ "_catch_red is declared with the reduction rules for " ^ id ^ "_catch")
      end
  | _ => tmFail "not an inductive"
  end.

(* ------------------------------------------------------------------ *)
(* generate_catch: combined symbol + rules                            *)
(* ------------------------------------------------------------------ *)

Definition generate_catch (q : qualid) : TemplateMonad unit :=
  generate_catch_symbol q ;;
  generate_catch_rules q.
