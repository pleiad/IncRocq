(* The description of an inductive that the generators of gen_complete,
   gen_refinable and gen_complete_minimal read, and the universe layout of
   what they declare.

   [check_source "T"] reads the quoted body of [T] into a [source]: its
   parameters, its universe context with the quality of [T] itself replaced
   by [Inc], and its slots. The slots are the parameters, followed by each
   other type of a field, once each, in the order they first occur. Each slot
   gets a predicate or relation parameter in what is generated. When the
   generators cannot handle [T] yet, [check_source] says why.

   A generated predicate or relation has the context of [T], followed by one
   quality and one level per slot, and the quality of its own sort:
     qualities  T's .. | q_slot 0 .. q_slot (k-1) | q_result
     levels     T's .. | u_slot 0 .. u_slot (k-1)
   Its binders are the parameters A0 .. A(n-1), then one per slot. *)
From MetaRocq.Utils Require Export utils.
From MetaRocq.Template Require Import All.

From Stdlib Require Init.
Import MRMonadNotation.

From IncRocq Require Export Base.
From IncRocq Require Import gen.Utils.

(* ------------------------------------------------------------------ *)
(* Small builders                                                      *)
(* ------------------------------------------------------------------ *)

Definition qvar (i : nat) : Quality.t := Quality.qVar (QVar.Var i).
Definition lvl (l : Level.t) : Universe.t := Universe.make' l.
Definition named (s : string) (r : relevance) : aname :=
  {| binder_name := nNamed s; binder_relevance := r |}.

(* Gets the relevance of the elements of a type whose sort is [s]. A
   transparent copy of [relevance_of_sort], which is opaque and would not
   reduce while the generator runs. *)
Definition sort_relevance (s : sort) : relevance :=
  match s with
  | sSProp => Irrelevant
  | sProp | sType _ => Relevant
  | sQVar q _ => RelevanceVar q
  end.

Definition sort_quality (s : sort) : option Quality.t :=
  match s with
  | sType _ => Some Quality.qType
  | sQVar q _ => Some (Quality.qVar q)
  | _ => None
  end.

Definition sort_universe (s : sort) : option Universe.t :=
  match s with
  | sType u | sQVar _ u => Some u
  | _ => None
  end.

(* Builds [forall b1 .. bk, t] from the binders listed outermost first. *)
Definition mkProds (bs : list (aname * term)) (t : term) : term :=
  fold_right (fun '(na, ty) acc => tProd na ty acc) t bs.

Definition mkLams (bs : list (aname * term)) (t : term) : term :=
  fold_right (fun '(na, ty) acc => tLambda na ty acc) t bs.

(* The levels of [u] other than [Set], or None when one of them carries an
   increment. *)
Definition universe_levels (u : Universe.t) : option (list Level.t) :=
  fold_right (fun '(l, k) acc =>
    match acc with
    | None => None
    | Some ls =>
        if Level.eqb l Level.lzero then Some ls
        else if Nat.eqb k 0 then Some (l :: ls) else None
    end) (Some []) (LevelExprSet.elements (Universes.t_set u)).

(* ------------------------------------------------------------------ *)
(* Fields                                                              *)
(* ------------------------------------------------------------------ *)

(* A recursive field, or a field whose premise is stated with the predicate or
   relation of slot [i]. *)
Variant field_kind := FRecursive | FSlot (i : nat).

(* True if [args] are the parameters in order, [tRel (j + n - 1)] down to
   [tRel j]. *)
Fixpoint are_params (j : nat) (args : list term) (k : nat) : bool :=
  match args, k with
  | [], 0 => true
  | tRel r :: rest, S k' => Nat.eqb r (j + k') && are_params j rest k'
  | _, _ => false
  end.

(* Classifies the type [ty] of the field declared after [j] other fields, for
   an inductive with [n] parameters. In the context of [ty], [tRel (j + n)] is
   the inductive and [tRel j] .. [tRel (j + n - 1)] are the parameters, the
   last one first. A recursive field must apply the inductive to the
   parameters unchanged, since the premise for it is stated at those
   parameters. *)
Definition classify_field (n j : nat) (ty : term) : option field_kind :=
  match ty with
  | tRel r =>
      if Nat.eqb r (j + n) then Some FRecursive
      else if Nat.leb j r && Nat.ltb r (j + n) then Some (FSlot (n - 1 - (r - j)))
      else None
  | tApp (tRel r) args =>
      if Nat.eqb r (j + n) && are_params j args n then Some FRecursive else None
  | _ => None
  end.

(* The type [ty] of the field declared after [j] other fields, moved to the
   context of the [n] parameters, when it is an inductive applied to
   arguments that mention neither [T] nor the fields before it. *)
Definition closed_field_type (n j : nat) (ty : term) : option term :=
  match decompose_app ty with
  | (tInd _ _, _) =>
      if noccur_between 0 j ty && noccur_between (j + n) 1 ty
      then Some (subst (repeat (tRel 0) j) 0 ty)
      else None
  | _ => None
  end.

(* ------------------------------------------------------------------ *)
(* The quoted inductive                                                *)
(* ------------------------------------------------------------------ *)

(* What the generator needs to know about [T], read off its quoted body. *)
Record source := {
  src_ind     : inductive;
  src_id      : ident;
  src_body    : one_inductive_body;
  src_nparams : nat;
  (* The sorts of the parameters, outermost first, with Inc in place of the
     quality of [T] itself. *)
  src_param_sorts : list sort;
  (* The bound names of the qualities of the generated context, which are
     those of [T] without its own, some of them identified (see
     [add_field_slots]), and the names and constraints of [T]'s levels. *)
  src_quals  : list name;
  src_levels : list name;
  src_cstrs  : ConstraintSet.t;
  (* [T]'s own instance, [Inc] for its own quality. *)
  src_inst   : Instance.t;
  (* The universe of [T A1 .. An], and its sort with [Inc]. *)
  src_univ   : Universe.t;
  src_sort   : sort;
  (* What each quality of [T]'s context becomes in the generated context:
     [Inc] for [T]'s own, and a quality variable for the others. *)
  src_qmap   : list Quality.t;
  (* The slots: the parameters, then the other field types. Each is a type in
     the context of the parameters, with its sort. *)
  src_slots  : list (term * sort)
}.

(* Renaming the qualities of [T]'s context by [m], whose entry [i] is what
   the quality [i] becomes. *)
Definition qmap_quality (m : list Quality.t) (q : Quality.t) : Quality.t :=
  match q with
  | Quality.qVar (QVar.Var i) => nth i m q
  | _ => q
  end.

Definition qmap_instance (m : list Quality.t) (u : Instance.t) : Instance.t :=
  Instance.make (map (qmap_quality m) (Instance.qualities u)) (Instance.universes u).

Definition qmap_relevance (m : list Quality.t) (r : relevance) : relevance :=
  match r with
  | RelevanceVar (QVar.Var i) =>
      match nth i m Quality.qType with
      | Quality.qVar v => RelevanceVar v
      | Quality.qSProp => Irrelevant
      | _ => Relevant
      end
  | _ => r
  end.

Definition qmap_sort (m : list Quality.t) (so : sort) : sort :=
  match so with
  | sQVar (QVar.Var i) u =>
      match nth i m Quality.qType with
      | Quality.qVar v => sQVar v u
      | Quality.qType => sType u
      | Quality.qProp => sProp
      | Quality.qSProp => sSProp
      end
  | _ => so
  end.

Definition qmap_aname (m : list Quality.t) (b : aname) : aname :=
  {| binder_name := b.(binder_name); binder_relevance := qmap_relevance m b.(binder_relevance) |}.

Fixpoint qmap_term (m : list Quality.t) (t : term) : term :=
  match t with
  | tSort so => tSort (qmap_sort m so)
  | tProd b dom codom => tProd (qmap_aname m b) (qmap_term m dom) (qmap_term m codom)
  | tLambda b dom body => tLambda (qmap_aname m b) (qmap_term m dom) (qmap_term m body)
  | tLetIn b def ty body =>
      tLetIn (qmap_aname m b) (qmap_term m def) (qmap_term m ty) (qmap_term m body)
  | tApp hd args => tApp (qmap_term m hd) (List.map (qmap_term m) args)
  | tInd ind u => tInd ind (qmap_instance m u)
  | tConst kn u => tConst kn (qmap_instance m u)
  | tConstruct ind k u => tConstruct ind k (qmap_instance m u)
  | tCast t' k ty => tCast (qmap_term m t') k (qmap_term m ty)
  | tProj proj t' => tProj proj (qmap_term m t')
  | _ => t
  end.

(* A term or binder relevance of [T], in the generated context. *)
Definition src_term (s : source) (t : term) : term := qmap_term s.(src_qmap) t.
Definition src_relevance (s : source) (r : relevance) : relevance :=
  qmap_relevance s.(src_qmap) r.

(* Either what the generator needs, or what about the type the generator
   cannot handle yet. *)
Variant generable (A : Type) := Generable (a : A) | NotYet (why : string).
Arguments Generable {A} a.
Arguments NotYet {A} why.

(* The types of the fields of [s]'s constructors that are neither [T] nor a
   parameter, in the context of the parameters, in the order they occur. *)
Definition other_field_types (s : source) : list term :=
  let n := s.(src_nparams) in
  flat_map (fun c =>
    flat_map (fun '(j, d) =>
      let ty := src_term s d.(decl_type) in
      match classify_field n j ty with
      | Some _ => []
      | None => match closed_field_type n j ty with
                | Some F => [F]
                | None => []
                end
      end) (combine (seq_nat 0 (List.length c.(cstr_args))) (List.rev c.(cstr_args))))
    s.(src_body).(ind_ctors).

(* Equality of the types of fields, which are inductives applied to
   arguments. The generic [eqb] on terms goes through an opaque obligation and
   would not reduce while the generator runs, so these compare by hand, and
   only the shapes such a type can take. *)
Definition level_eqb (a b : Level.t) : bool :=
  match a, b with
  | Level.lzero, Level.lzero => true
  | Level.level x, Level.level y => String.eqb x y
  | Level.lvar i, Level.lvar j => Nat.eqb i j
  | _, _ => false
  end.

Definition quality_eqb (a b : Quality.t) : bool :=
  match a, b with
  | Quality.qProp, Quality.qProp | Quality.qSProp, Quality.qSProp
  | Quality.qType, Quality.qType => true
  | Quality.qVar x, Quality.qVar y => QVar.eqb x y
  | _, _ => false
  end.

Fixpoint list_eqb {A} (f : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | [], [] => true
  | a :: l, b :: l' => f a b && list_eqb f l l'
  | _, _ => false
  end.

Definition instance_eqb_with (qeq : Quality.t -> Quality.t -> bool) (u v : Instance.t) : bool :=
  list_eqb qeq (Instance.qualities u) (Instance.qualities v)
  && list_eqb level_eqb (Instance.universes u) (Instance.universes v).

Definition kername_eqb (k k' : kername) : bool :=
  String.eqb (string_of_kername k) (string_of_kername k').

Definition inductive_eqb (i j : inductive) : bool :=
  kername_eqb (inductive_mind i) (inductive_mind j) && Nat.eqb (inductive_ind i) (inductive_ind j).

Fixpoint field_type_eqb_with (qeq : Quality.t -> Quality.t -> bool) (t u : term) : bool :=
  match t, u with
  | tRel i, tRel j => Nat.eqb i j
  | tInd i ui, tInd j uj => inductive_eqb i j && instance_eqb_with qeq ui uj
  | tConst k ui, tConst k' uj => kername_eqb k k' && instance_eqb_with qeq ui uj
  | tConstruct i c ui, tConstruct j d uj =>
      inductive_eqb i j && Nat.eqb c d && instance_eqb_with qeq ui uj
  | tApp f args, tApp g args' =>
      field_type_eqb_with qeq f g &&
      (fix go (l l' : list term) : bool :=
         match l, l' with
         | [], [] => true
         | a :: l, b :: l' => field_type_eqb_with qeq a b && go l l'
         | _, _ => false
         end) args args'
  | _, _ => false
  end.

Definition field_type_eqb := field_type_eqb_with quality_eqb.

(* Equality up to the quality variables of the generated context. *)
Definition same_up_to_qualities :=
  field_type_eqb_with (fun a b =>
    match a, b with
    | Quality.qVar (QVar.Var _), Quality.qVar (QVar.Var _) => true
    | _, _ => quality_eqb a b
    end).

(* The pairs of quality variables at the same position in [t] and [u], which
   are the same up to quality variables. *)
Definition instance_quality_pairs (u v : Instance.t) : list (nat * nat) :=
  flat_map (fun '(a, b) =>
    match a, b with
    | Quality.qVar (QVar.Var i), Quality.qVar (QVar.Var j) => [(i, j)]
    | _, _ => []
    end) (combine (Instance.qualities u) (Instance.qualities v)).

Fixpoint quality_pairs (t u : term) : list (nat * nat) :=
  match t, u with
  | tInd _ ui, tInd _ uj => instance_quality_pairs ui uj
  | tConst _ ui, tConst _ uj => instance_quality_pairs ui uj
  | tConstruct _ _ ui, tConstruct _ _ uj => instance_quality_pairs ui uj
  | tApp f args, tApp g args' =>
      quality_pairs f g ++
      (fix go (l l' : list term) : list (nat * nat) :=
         match l, l' with
         | a :: l, b :: l' => quality_pairs a b ++ go l l'
         | _, _ => []
         end) args args'
  | _, _ => []
  end.

(* Merges the classes of [i] and [j] in [rep], which maps each quality to the
   least quality of its class. *)
Definition union_qualities (rep : list nat) '((i, j) : nat * nat) : list nat :=
  let ri := nth i rep i in
  let rj := nth j rep j in
  let r := Nat.min ri rj in
  map (fun x => if Nat.eqb x ri || Nat.eqb x rj then r else x) rep.

Fixpoint position (j : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: rest => if Nat.eqb x j then 0 else S (position j rest)
  end.

(* [ts] without repetitions, each at its first occurrence. *)
Definition dedup_terms (ts : list term) : list term :=
  List.rev (fold_left (fun acc t => if existsb (field_type_eqb t) acc then acc else t :: acc) ts []).

(* The sort of the type [F], an inductive applied to arguments. *)
Definition inductive_type_sort (F : term) : TemplateMonad (option sort) :=
  match decompose_app F with
  | (tInd ind u, _) =>
      decl <- tmQuoteInductive (inductive_mind ind) ;;
      match nth_error decl.(ind_bodies) (inductive_ind ind) with
      | Some body =>
          if Nat.eqb (List.length body.(ind_indices)) 0
          then ret (Some (subst_instance_sort u body.(ind_sort)))
          else ret None
      | None => ret None
      end
  | _ => ret None
  end.

(* The description of [T], declared as [decl] with [body], when its qualities
   become [m] in a generated context whose qualities are named [qnames]. Its
   only slots are the parameters. *)
Definition make_source (ind : inductive) (decl : mutual_inductive_body)
    (body : one_inductive_body) (qnames us : list name) (cs : ConstraintSet.t)
    (m : list Quality.t) : generable source :=
  let n := decl.(ind_npars) in
  let param_sorts :=
    map (fun d => match qmap_term m d.(decl_type) with
                  | tSort s => Some s
                  | _ => None
                  end) (List.rev decl.(ind_params)) in
  if existsb (fun o => match o with None => true | _ => false end) param_sorts then
    NotYet "a parameter is not a type"
  else
  let param_sorts := flat_map (fun o => match o with Some s => [s] | None => [] end) param_sorts in
  let inst := Instance.make (map (fun i => qmap_quality m (qvar i)) (seq_nat 0 (List.length m)))
                            (map Level.lvar (seq_nat 0 (List.length us))) in
  match qmap_term m (tSort body.(ind_sort)) with
  | tSort s =>
      match sort_universe s with
      | Some u =>
          Generable {| src_ind := ind; src_id := snd (inductive_mind ind);
                       src_body := body; src_nparams := n;
                       src_param_sorts := param_sorts;
                       src_quals := qnames; src_levels := us;
                       src_cstrs := cs; src_inst := inst;
                       src_univ := u; src_sort := s; src_qmap := m;
                       src_slots := mapi (fun i so => (tRel (n - 1 - i), so)) param_sorts |}
      | None => NotYet "its sort has no universe"
      end
  | _ => NotYet "its sort is not a sort"
  end.

(* Adds to [s] a slot for each type of a field that is neither [T] nor a
   parameter. Each field of a sort polymorphic inductive has qualities of its
   own, so two fields of type [bool] have the types [bool@{a}] and [bool@{b}].
   Such qualities are identified first, so that the two fields share a slot.
   The generated constants then cover only the instances of [T] where those
   qualities are equal. *)
Definition add_field_slots (decl : mutual_inductive_body) (s : source)
    : TemplateMonad (generable source) :=
  let Fs := other_field_types s in
  let nq := List.length s.(src_quals) in
  let pairs := flat_map (fun F => flat_map (fun G =>
                 if same_up_to_qualities F G then quality_pairs F G else []) Fs) Fs in
  let rep := fold_left union_qualities pairs (seq_nat 0 nq) in
  let reps := filter (fun j => Nat.eqb (nth j rep j) j) (seq_nat 0 nq) in
  let sigma := map (fun j => qvar (position (nth j rep j) reps)) (seq_nat 0 nq) in
  match make_source s.(src_ind) decl s.(src_body)
          (map (fun j => nth j s.(src_quals) nAnon) reps) s.(src_levels) s.(src_cstrs)
          (map (qmap_quality sigma) s.(src_qmap)) with
  | NotYet why => ret (NotYet why)
  | Generable s =>
      let Fs := dedup_terms (other_field_types s) in
      sorts <- monad_map inductive_type_sort Fs ;;
      if existsb (fun o => match o with None => true | _ => false end) sorts then
        ret (NotYet "the type of a field is an inductive with indices")
      else
      let sorts := flat_map (fun o => match o with Some so => [so] | None => [] end) sorts in
      (* Normalized once, since the generators read the description many
         times and MetaRocq would otherwise compute it again each time. With
         [all] or [cbn] in place of [lazy], normalizing the description of
         Prelude's ascii does not finish. *)
      tmEval lazy (Generable {| src_ind := s.(src_ind); src_id := s.(src_id);
                    src_body := s.(src_body); src_nparams := s.(src_nparams);
                    src_param_sorts := s.(src_param_sorts);
                    src_quals := s.(src_quals); src_levels := s.(src_levels);
                    src_cstrs := s.(src_cstrs); src_inst := s.(src_inst);
                    src_univ := s.(src_univ); src_sort := s.(src_sort);
                    src_qmap := s.(src_qmap);
                    src_slots := s.(src_slots) ++ combine Fs sorts |})
  end.

Definition read_source (q : qualid) : TemplateMonad (generable source) :=
  gr <- tmLocate1 q ;;
  match gr with
  | IndRef ind =>
      decl <- tmQuoteInductive (inductive_mind ind) ;;
      match decl.(ind_bodies) with
      | [body] =>
          if negb (Nat.eqb (List.length body.(ind_indices)) 0) then
            ret (NotYet "it has indices")
          else
          let q_idx := get_ind_sort_quality_idx body.(ind_type) in
          match decl.(ind_universes) with
          | Polymorphic_ctx (mkBoundNames qs us, cs) =>
              (* T's own quality becomes Inc, and the others move down past it. *)
              let m := map (fun i => if Nat.eqb i q_idx then inc_quality
                                     else if Nat.ltb i q_idx then qvar i
                                     else qvar (Nat.pred i))
                           (seq_nat 0 (List.length qs)) in
              match make_source ind decl body (list_remove_nth q_idx qs) us cs m with
              | Generable s => add_field_slots decl s
              | NotYet why => ret (NotYet why)
              end
          | Monomorphic_ctx => ret (NotYet "it is not sort polymorphic, so it has no Inc instance")
          end
      | _ => ret (NotYet "it is a mutual inductive")
      end
  | _ => ret (NotYet "it is not an inductive")
  end.


(* ------------------------------------------------------------------ *)
(* The universe layout                                                 *)
(* ------------------------------------------------------------------ *)

Definition nquals (s : source) := List.length s.(src_quals).
Definition nlevels (s : source) := List.length s.(src_levels).
Definition nslots (s : source) := List.length s.(src_slots).
Definition q_slot (s : source) (i : nat) := nquals s + i.
Definition q_result (s : source) := nquals s + nslots s.
Definition u_slot (s : source) (i : nat) := Level.lvar (nlevels s + i).

Definition slot_sort (s : source) (i : nat) : sort := snd (nth i s.(src_slots) (tRel 0, sProp)).

(* The type of slot [i] under [d] binders past the parameters. *)
Definition slot_type (s : source) (d i : nat) : term :=
  lift0 d (fst (nth i s.(src_slots) (tRel 0, sProp))).

(* The universe of the sort of a generated predicate or relation: that of T,
   joined with the levels of the slots. *)
Definition result_universe (s : source) : Universe.t :=
  fold_left (fun u i => Universe.sup u (lvl (u_slot s i))) (seq_nat 0 (nslots s)) s.(src_univ).

(* The binders of the parameters A0 .. A(n-1), outermost first. *)
Definition param_binders (s : source) : list (aname * term) :=
  mapi (fun i so => (named ("A" ^ string_of_nat i) Relevant, tSort so)) s.(src_param_sorts).

(* [tRel] of Ai and of the binder of slot [i] (its predicate or relation), and
   the type of slot [i], under the parameters, the slot binders, and [d] more
   binders. *)
Definition rel_A (s : source) (d i : nat) := tRel (nslots s + s.(src_nparams) - 1 - i + d).
Definition rel_S (s : source) (d i : nat) := tRel (nslots s - 1 - i + d).
Definition rel_B (s : source) (d i : nat) := slot_type s (nslots s + d) i.

Definition params_and_slots (s : source) (d : nat) : list term :=
  map (rel_A s d) (seq_nat 0 s.(src_nparams)) ++ map (rel_S s d) (seq_nat 0 (nslots s)).

Definition T_applied (s : source) (d : nat) : term :=
  mkApps (tInd s.(src_ind) s.(src_inst)) (map (rel_A s d) (seq_nat 0 s.(src_nparams))).

(* ------------------------------------------------------------------ *)
(* Fields                                                              *)
(* ------------------------------------------------------------------ *)

Fixpoint find_slot (F : term) (slots : list (term * sort)) (i : nat) : option nat :=
  match slots with
  | [] => None
  | (B, _) :: rest => if field_type_eqb F B then Some i else find_slot F rest (S i)
  end.

Definition field_kind_of (s : source) (j : nat) (ty : term) : option field_kind :=
  match classify_field s.(src_nparams) j ty with
  | Some k => Some k
  | None =>
      match closed_field_type s.(src_nparams) j ty with
      | Some F => option_map FSlot (find_slot F s.(src_slots) 0)
      | None => None
      end
  end.

Definition field_kinds (s : source) (c : constructor_body) : list (option field_kind) :=
  mapi (fun j d => field_kind_of s j (src_term s d.(decl_type)))
       (List.rev c.(cstr_args)).

(* ------------------------------------------------------------------ *)
(* Levels and gaps                                                     *)
(* ------------------------------------------------------------------ *)

(* Instantiates the constraints of a polymorphic global, stated on its levels
   [lvar 0] .. [lvar k], at the levels [slots]. *)
Definition inst_level (slots : list Level.t) (l : Level.t) : Level.t :=
  match l with
  | Level.lvar k => nth k slots l
  | _ => l
  end.

Definition inst_constraints (slots : list Level.t) (cs : ConstraintSet.t) : list UnivConstraint.t :=
  map (fun '(l1, ct, l2) => (inst_level slots l1, ct, inst_level slots l2))
      (ConstraintSet.elements cs).

Definition add_constraints (cs : list UnivConstraint.t) (acc : ConstraintSet.t) : ConstraintSet.t :=
  fold_left (fun acc c => ConstraintSet.add c acc) cs acc.

(* A level above every level of [u]. When [u] is a single level, or [Set], it
   is that level. Otherwise it is the fresh level [lvar next], with the
   constraints that put it above [u]. Returns the level, the number of fresh
   levels used, and the constraints. *)
Definition level_above (u : Universe.t) (next : nat)
    : option (Level.t * nat * list UnivConstraint.t) :=
  match universe_levels u with
  | None => None
  | Some [] => Some (Level.lzero, 0, [])
  | Some [l] => Some (l, 0, [])
  | Some ls =>
      let fresh := Level.lvar next in
      Some (fresh, 1, map (fun l => (l, ConstraintType.Le0, fresh)) ls)
  end.

(* The quality and level of a parameter's sort, when it lives in a single
   level, or in the maximum of [Set] and a single level. *)
Definition param_quality_level (so : sort) : option (Quality.t * Level.t) :=
  match sort_quality so, option_map universe_levels (sort_universe so) with
  | Some q, Some (Some []) => Some (q, Level.lzero)
  | Some q, Some (Some [l]) => Some (q, l)
  | _, _ => None
  end.

(* What about the inductive described by [s] the generator cannot handle yet,
   if anything. *)
Definition generator_gap (s : source) : option string :=
  if existsb (fun c => existsb (fun o => match o with None => true | _ => false end)
                               (field_kinds s c))
             s.(src_body).(ind_ctors)
  then Some "the type of a field mentions the inductive other than applied to its parameters"
  else if existsb (fun '(_, so) => match param_quality_level so with None => true | _ => false end)
                  s.(src_slots)
  then Some "a parameter or the type of a field does not live in a single universe level"
  else match level_above s.(src_univ) 0, level_above (result_universe s) 0 with
       | Some _, Some _ => None
       | _, _ => Some "its universe has an increment"
       end.

(* Either the description of [q], or what about it the generator cannot handle
   yet. *)
Definition check_source (q : qualid) : TemplateMonad (generable source) :=
  r <- read_source q ;;
  match r with
  | NotYet why => ret (NotYet why)
  | Generable s =>
      match generator_gap s with
      | Some why => ret (NotYet why)
      | None => ret (Generable s)
      end
  end.
