From MetaRocq.Template Require Import All.
From Stdlib Require Init.
Import MRMonadNotation.

From IncRocq Require Import gen.Utils.

(* ------------------------------------------------------------------ *)
(* generate_hole_match_rule: hole propagation through match           *)
(* ------------------------------------------------------------------ *)

(* "O" for 0-arity, "S _" for 1-arity, "pair _ _" for 2-arity *)
Definition ctor_match_pat (cname : ident) (arity : nat) : string :=
  if Nat.eqb arity 0
  then cname
  else cname ^ join_with_space (repeat "_" arity).

(* [ind_name] and [first_name] are the full names of the inductive and of
   its first constructor (see [qualify_in]). *)
Definition build_hole_match_rule
    (ind_name todo_qualid : ident) (first_name : string) (first_ctor : constructor_body)
    (nb_ctors nb_params nb_indices : nat) (q_idx nb_ind_quals nb_ind_levels : nat)
    (has_max_sort : bool)
    : option string * string * string :=
  let param_args := map (fun i => "?A" ^ string_of_nat i) (seq_nat 0 nb_params) in
  let index_args := map (fun i => "?I" ^ string_of_nat i) (seq_nat 0 nb_indices) in
  let ind_applied annot :=
    if Nat.eqb (nb_params + nb_indices) 0 then ind_name ^ annot
    else "(" ^ ind_name ^ annot ^ join_with_space (param_args ++ index_args) ^ ")" in
  (* Build quality annotation: slot j is "Inc" if j=q_idx, else "qj".
     extra_qual_strs lists the non-Inc quality names for the universe binder. *)
  let before_Exc     := map (fun j => "q" ^ string_of_nat j) (seq_nat 0 q_idx) in
  let after_len      := nb_ind_quals - 1 - q_idx in
  let after_Exc      := map (fun j => "q" ^ string_of_nat j) (seq_nat (S q_idx) after_len) in
  let qual_list      := before_Exc ++ ["Inc"] ++ after_Exc in
  let extra_qual_strs := before_Exc ++ after_Exc in
  (* The `in` clause names the scrutinee's type with a wildcard per parameter
     and a variable per index.  Every inductive gets one, so families and
     other inductives share one rule shape.  The return type may mention the index
     variables, so the right-hand side instantiates them with the scrutinee's
     indices along with t0. *)
  let index_vars := map (fun i => "i" ^ string_of_nat i) (seq_nat 0 nb_indices) in
  let in_clause :=
    " in " ^ ind_name ^ join_with_space (repeat "_" nb_params ++ index_vars) in
  let ret_annot := in_clause ^ " return@{Inc;u'} ?P" in
  let index_inst :=
    fold_left (fun acc (p : string * string) => acc ^ fst p ^ " := " ^ snd p ^ "; ")
              (combine index_vars index_args) "" in
  let first_pat := ctor_match_pat first_name first_ctor.(cstr_arity) in
  let branches :=
    if Nat.eqb nb_ctors 1
    then "| " ^ first_pat ^ " => _"
    else "| " ^ first_pat ^ " => _ | _ => _" in
  if Nat.ltb 1 nb_ind_levels then
    (* Multi-level case: name each inductive level var u0..u_{n-1} separately,
       plus "us" for TODO (Rocq derives max(u0,...) <= us from the rule head)
       and "u'" for the return sort.  All quality slots are fully explicit. *)
    let ind_level_names := map (fun i => "u" ^ string_of_nat i) (seq_nat 0 nb_ind_levels) in
    let ind_annot := "@{" ^ string_join " " qual_list ^ "; " ^ string_join " " ind_level_names ^ "}" in
    let all_level_names := ind_level_names ++ ["us"; "u'"] in
    let udecl :=
      if Nat.eqb (length extra_qual_strs) 0
      then Some ("@{" ^ string_join " " all_level_names ^ "|+}")
      else Some ("@{" ^ string_join " " extra_qual_strs ^ "; " ^ string_join " " all_level_names ^ "|+}") in
    let scrutinee := todo_qualid ^ "@{us} " ^ ind_applied ind_annot in
    let lhs := "match " ^ scrutinee ^ " as t0 " ^ ret_annot
               ^ " with " ^ branches ^ " end" in
    let rhs := todo_qualid ^ "@{u'} (?P@{" ^ index_inst ^ "t0 := " ^ todo_qualid ^ "@{us} " ^ ind_applied "" ^ "})" in
    (udecl, lhs, rhs)
  else
    (* Single-level (or zero-level) case.  When the inductive's sort is a max
       universe ([has_max_sort]), [TODO] gets a dedicated level [us], as in
       the multi-level branch and for the reason given in build_hole_rule.
       Other single-level inductives leave [TODO] unannotated. *)
    let todo_annot    := if has_max_sort then "@{us}" else "" in
    let todo_out_ann  := if has_max_sort then "@{u'}" else "" in
    let ext           := if has_max_sort then "|+" else "|" in
    let lvl_names :=
      if Nat.eqb nb_ind_levels 0
      then (if has_max_sort then "us u'" else "u'")
      else (if has_max_sort then "u us u'" else "u u'") in
    let ind_annot :=
      if Nat.eqb nb_ind_levels 0
      then "@{" ^ string_join " " qual_list ^ ";}"
      else "@{" ^ string_join " " qual_list ^ "; u}" in
    let udecl :=
      if Nat.eqb (length extra_qual_strs) 0
      then Some ("@{" ^ lvl_names ^ ext ^ "}")
      else Some ("@{" ^ string_join " " extra_qual_strs ^ "; " ^ lvl_names ^ ext ^ "}") in
    let scrutinee := todo_qualid ^ todo_annot ^ " " ^ ind_applied ind_annot in
    let lhs := "match " ^ scrutinee ^ " as t0 " ^ ret_annot
               ^ " with " ^ branches ^ " end" in
    let rhs := todo_qualid ^ todo_out_ann ^ " (?P@{" ^ index_inst ^ "t0 := "
               ^ todo_qualid ^ todo_annot ^ " " ^ ind_applied "" ^ "})" in
    (udecl, lhs, rhs).

Definition generate_hole_match_rule (q : qualid) : TemplateMonad unit :=
  gr <- tmLocate1 q ;;
  match gr with
  | IndRef ind =>
      let kn := inductive_mind ind in
      let (_, id) := kn in
      decl <- tmQuoteInductive kn ;;
      match List.hd_error decl.(ind_bodies) with
      | None => tmFail "no inductive bodies"
      | Some ind_body =>
          match ind_body.(ind_ctors) with
          | [] => tmFail "empty constructor list"
          | first_ctor :: _ =>
              let nb_ctors  := length ind_body.(ind_ctors) in
              let nb_params := List.length decl.(ind_params) in
              let nb_indices := List.length ind_body.(ind_indices) in
              let q_idx := get_ind_sort_quality_idx ind_body.(ind_type) in
              let nb_ind_quals := match decl.(ind_universes) with
                | Polymorphic_ctx ctx =>
                    match fst ctx with
                    | mkBoundNames qs _ => length qs
                    end
                | _ => 1
                end in
              let nb_ind_levels := match decl.(ind_universes) with
                | Polymorphic_ctx ctx =>
                    match fst ctx with
                    | mkBoundNames _ us => length us
                    end
                | _ => 1
                end in
              (* The inductive's sort is a max universe, such as max(Set, u),
                 when it is not a single level.  [TODO] then needs a dedicated
                 level (see build_hole_match_rule). *)
              let has_max_sort :=
                match get_ind_sort_universe ind_body.(ind_type) with
                | Some lvl => match Universe.get_is_level lvl with
                              | None => true | Some _ => false end
                | None => false
                end in
              let rule := build_hole_match_rule (qualify_in kn id) inc_todo_qualid
                            (qualify_in kn first_ctor.(cstr_name)) first_ctor nb_ctors nb_params nb_indices q_idx nb_ind_quals nb_ind_levels has_max_sort in
              tmRewriteRuleU (id ^ "_hole_red") [rule] ;;
              tmMsg (id ^ "_hole_red is declared to propagate hole through pattern matching on " ^ id)
          end
      end
  | _ => tmFail "not an inductive"
  end.
