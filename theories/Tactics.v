From Ltac2 Require Export Ltac2.
From Ltac2 Require Import Printf Constr.
From Prelude Require Import Logic.
From IncRocq Require Import Base Reformulation.

Import Unsafe.

(* Sort-polymorphic stand-in for the discriminate/injection motive codomain.
   Referencing this constant from Ltac2 (`'discr_sort`) yields a fresh sort
   quality variable on every use.

   The freshness matters when the discriminated equality is itself
   sort-polymorphic (e.g. `S n = TODO nat`, where the equality lives at a fresh
   sort while the equated terms live in `Inc`). Pinning the motive to a ground
   `Prop` collapses that fresh sort and, when it is shared with the surrounding
   goal, forces a forbidden `Inc -> Prop` elimination. A fresh sort is then
   unified with the goal's sort through [discr_absurd], and the equality only
   has to eliminate into the goal's sort. *)
#[universes(polymorphic)]
Definition discr_sort@{s;u} := Type@{s;u}.

(* Eliminates [False] into a goal of the same sort quality. Concluding a
   discrimination through it unifies the motive's quality with the goal's, so
   the proof term leaves no quality unconstrained. *)
#[universes(polymorphic)]
Definition discr_absurd@{s; u v} (G : Type@{s;v}) (f : False@{s;u}) : G :=
  match f with end.

(* [f_equal] with its conclusion in the quality of its premise. [f_equal]
   leaves the quality of its conclusion free, so each equation [icp_injection]
   derives through it would leave an unconstrained quality in the proof term. *)
#[universes(polymorphic)]
Definition injection_f_equal@{a b e; u v w w'} (A : Type@{a;u}) (B : Type@{b;v})
    (f : A -> B) (x y : A) (H : @eq@{a e; u w} A x y) : @eq@{b e; v w'} B (f x) (f y) :=
  f_equal f H.

(* ================================================================== *)
(* 1. Shared Ltac2 utilities                                          *)
(* ================================================================== *)

(* Helpers used by more than one group below. [retry_after] is the retry
   combinator every tactic goes through to reach under binders, and
   [is_todo_head] is shared by the catch layer and the incompleteness layer. *)

Ltac2 ident_of_string str := Option.get (Ident.of_string str).

(* Runs [tac]. Failing that, performs one [step] and retries, until [tac]
   succeeds or [step] runs out, at which point it fails with [msg]. Every tactic
   here that must work on a goal whose interesting part still hides under
   binders goes through it.

   The step is a parameter so that a tactic which does not depend on [Reformulation]
   never learns about [is_complete]. [icp_discriminate] and
   [icp_hole_refinement] pass [plain_intro_step], while [icp_solve] and
   [icp_eq_mono] pass [icp_intro_step], which also unpacks the antitone-equality
   [icp_reform] leaves in the premise.

   The nested [Control.plus] makes it safe under [try]. A branch that ultimately
   fails rolls back every step it took, so a goal the tactic cannot close is
   left exactly as it was found. *)
Ltac2 rec retry_after (msg : string) (step : unit -> unit) (tac : unit -> unit)
    : unit :=
  Control.plus
    (fun () => tac ())
    (fun _ =>
      Control.plus
        (fun () => step (); retry_after msg step tac)
        (fun _ =>
          Control.zero (Tactic_failure (Some (Message.of_string msg))))).

(* The step for tactics that do not depend on [Reformulation]. *)
Ltac2 plain_intro_step () : unit := Std.intro None None.


(* Checks whether [hd] is the `TODO` constant from [Base].

   Both constants are rebuilt with the same universe instance, the one taken
   from [hd], so that [Constr.equal] compares only the constant names. *)
Ltac2 is_todo_head (hd : constr) : bool :=
  let todo_path := [ ident_of_string "IncRocq"
                   ; ident_of_string "Base"
                   ; ident_of_string "TODO" ] in
  match Env.get todo_path with
  | None => false
  | Some (Std.ConstRef todo_cst) =>
      match kind hd with
      | Constant c inst =>
          Constr.equal (make (Constant c inst)) (make (Constant todo_cst inst))
      | _ => false
      end
  | _ => false
  end.


(* ================================================================== *)
(* 2. Bookkeeping tactics                                             *)
(* ================================================================== *)

(* Tactics that only move things between the goal and the context. They come
   first because [icp_intro_step] is the introduction step that [icp_solve] and
   [icp_eq_mono] backtrack on. *)

(* ------------------------------------------------------------------ *)
(* icp_intro_step                                                      *)
(* ------------------------------------------------------------------ *)

(* Returns [Some (x, y)] when the goal's immediate premise is the antitone-equality
   [x ≈̇ y] left by [icp_reform], [None] otherwise.

   Detection is by type via [lazy_match!], and [_ -> _] matches only a
   non-dependent [Prod], so it never fires on a dependent [forall x, ...]. *)
Ltac2 eq_anti_premise () : (constr * constr) option :=
  lazy_match! goal with
  | [ |- ?x ≈̇ ?y -> _ ] => Some (x, y)
  | [ |- _ ] => None
  end.

(* Gets the name of the completeness hypothesis for the argument [x] of
   [is_complete]. The name is [_Hcomplete_x] when [x] is exactly a variable,
   bare [_Hcomplete] otherwise ([S k], [0], [f a], ...). [Fresh.in_goal] avoids
   collisions.

   The name is cosmetic. [icp_absurd_complete] locates the completeness
   hypothesis by type, not by this name. *)
Ltac2 complete_name (x : constr) : ident :=
  let base :=
    match kind x with
    | Var id => String.app "_Hcomplete_" (Ident.to_string id)
    | _ => "_Hcomplete"
    end in
  match Ident.of_string base with
  | Some id => Fresh.in_goal id
  | None =>
      Control.throw (Tactic_failure (Some (Message.of_string
        "complete_name: invalid identifier")))
  end.

(* Performs one step of the incremental [intros]. When the immediate premise is
   an antitone-equality, unpacks it into the completeness of each side and the
   equation, otherwise performs a plain [intro] under [name]. [name] is [None]
   for automatic use, where nobody reads the resulting hypotheses.

   This is the step [icp_solve] backtracks on. A plain [intro] would leave the
   premise sealed as [x ≈̇ y], and neither the [is_complete] hypothesis
   [icp_absurd_complete] looks for nor the equation [icp_discriminate] looks for
   would be in the context. The unpacking is never seen: [retry_after] rolls it
   back on failure, and on success the goal is closed. *)
Ltac2 icp_intro_step (name : ident option) : unit :=
  match eq_anti_premise () with
  | Some (x, y) =>
      let hx := complete_name x in
      let hy := complete_name y in
      let hy :=
        if Ident.equal hx hy
        then Fresh.in_goal (ident_of_string (String.app (Ident.to_string hy) "_r"))
        else hy in
      let heq :=
        match name with
        | Some n => n
        | None => Fresh.in_goal (ident_of_string "Heq")
        end in
      Std.intros false
        [Std.IntroAction (Std.IntroOrAndPattern
           (Std.IntroAndPattern
              [Std.IntroNaming (Std.IntroIdentifier hx);
               Std.IntroAction (Std.IntroOrAndPattern
                 (Std.IntroAndPattern
                    [Std.IntroNaming (Std.IntroIdentifier hy);
                     Std.IntroNaming (Std.IntroIdentifier heq)]))]))]
  | None => Std.intro name None
  end.

(* Returns the plain equality behind [h]: [h] itself when its type is [_ = _],
   and [eqa_eq h] when it is [_ ≈̇ _]. This is what lets the equality-consuming
   tactics take a hypothesis in either form, so that a proof script does not have
   to know which [IncRef] instance produced its premise. *)
Ltac2 as_eq_proof (h : constr) : constr :=
  lazy_match! (Constr.type h) with
  | _ ≈̇ _ => '(eqa_eq $h)
  | _ => h
  end.


(* ================================================================== *)
(* 3. Catch-based tactics                                             *)
(* ================================================================== *)

(* Tactics that eliminate an [Inc]-sorted value through its catch symbol,
   which is the eliminator carrying the extra hole branch that plain
   [match] and [induction] lack. *)

(* ------------------------------------------------------------------ *)
(* Catch symbol lookup                                                 *)
(* ------------------------------------------------------------------ *)

Ltac2 ind_local_ident (ind : inductive) : ident :=
  List.last (Env.path (Std.IndRef ind)).

(* Gets the catch symbol for [ind], resolved as `<ind>_catch`.

   An inductive that never went through [gen_icp_defs] has none. The failure is
   raised with [Control.zero] so that it backtracks: [try], [first] and
   [retry_after] treat it as an ordinary tactic failure, and [icp_solve] stays
   silent on a goal with an equality over such a type. *)
Ltac2 get_catch_for_ind (ind : inductive) : constr :=
  let base        := Ident.to_string (ind_local_ident ind) in
  let catch_name  := String.concat "" [base; "_catch"] in
  let catch_ident := ident_of_string catch_name in
  (* Resolve the catch symbol by current scope (nametab visibility), exactly
     as writing `<ind>_catch` by hand would. This decouples where the catch is
     generated from where the inductive is defined, so you can reuse an
     inductive imported from another module (e.g. bool from Prelude). *)
  let rec first_const refs :=
    match refs with
    | [] =>
        Control.zero (Tactic_failure (Some (Message.of_string
          (String.concat "" ["no catch symbol "; catch_name;
                             " in scope, run gen_icp_defs on "; base]))))
    | r :: rest =>
        match r with
        | Std.ConstRef _ => r
        | _ => first_const rest
        end
    end in
  Env.instantiate (first_const (Env.expand [catch_ident])).


(* ------------------------------------------------------------------ *)
(* icp_discriminate                                                    *)
(* ------------------------------------------------------------------ *)

(* Wraps `leaf` in lambdas matching the leading Prod binders of `ty`.
   For non-recursive constructors (e.g. bool), `ty` is already non-Prod
   (it's `Prop` after specializing P), so `leaf` is returned directly.
   For recursive constructors (e.g. nat's S case), the extra foralls are
   wrapped: wrap_with_lambdas (forall n, Prop -> Prop) False
            = fun n _ => False. *)
Ltac2 rec wrap_with_lambdas (ty : constr) (leaf : constr) : constr :=
  match kind ty with
  | Prod b codom => make (Lambda b (wrap_with_lambdas codom leaf))
  | _ => leaf
  end.

(* Collects the domain types of the first n Prod binders in ty, in order. *)
Ltac2 rec collect_n_binder_types (n : int) (ty : constr) (acc : constr list)
    : constr list :=
  if Int.equal n 0
  then List.rev acc
  else
    match kind ty with
    | Prod b codom =>
        collect_n_binder_types (Int.sub n 1) codom (Constr.Binder.type b :: acc)
    | _ =>
        Control.throw
          (Invalid_argument (Some (Message.of_string "collect_n_binder_types: not enough Prod binders")))
    end.

(* Builds the catch-based discriminate predicate:
     catch_ref (fun _ => Prop) arg0 ... arg_{n-1} arg_hole
   where arg_i = wrap(True) if i = true_idx, else wrap(False).
   true_idx in 0..n_ctors-1 targets a constructor;
   true_idx = n_ctors targets the hole case.

   [true_idx] is the branch of the left-hand side of the equality, the side
   whose `I : True` is transported. Every other branch, the hole included, gets
   False, so the predicate reads as `x = _ is only satisfiable at x`, matching
   the convention of stock `discriminate`.

   The application proceeds in two steps, applying catch_ref to
   P=(fun _ => Prop) first. That lets Rocq substitute P in the remaining type,
   so collect_n_binder_types sees the actual (possibly unreduced) case-arg types
   T_i. wrap_with_lambdas then counts T_i's Prod binders to wrap True/False in
   the right number of lambdas (0 for bool, 2 for nat's S case, etc.). *)
Ltac2 build_catch_predicate
    (catch_ref : constr) (ind : inductive)
    (type_params : constr array)
    (n_ctors : int) (true_idx : int) : constr :=
  let ind_term := Env.instantiate (Std.IndRef ind) in
  (* Applied inductive type: `option nat`, `list bool`, or plain `bool`/`nat` *)
  let indt :=
    if Int.equal (Array.length type_params) 0
    then ind_term
    else make (App ind_term type_params)
  in
  (* Motive lands in a fresh sort (`discr_sort`), not ground `Prop`/`Type`, so
     the discriminated equality's own sort stays free. See `discr_sort`.
     discr_sort's universe instance [s;u] is reused verbatim for the True/False
     leaves. Since the term is assembled with Unsafe.make (no unification
     pass), bare True/False would each get an unrelated fresh sort.
     `True@{s;u} : Type@{s;u} = discr_sort@{s;u}`, so the instance arities match
     and the leaves land in exactly the motive's sort. The leaves are built
     from their references rather than quoted, since a quotation would declare
     a fresh instance that the term then never uses. *)
  let dsort   := 'discr_sort in
  let dinst   :=
    match kind dsort with
    | Constant _ i => i
    | _ => Control.throw
             (Invalid_argument (Some (Message.of_string "discr_sort is not a constant")))
    end in
  let leaf (path : ident list) : constr :=
    match Env.get path with
    | Some (Std.IndRef ind) => make (Ind ind dinst)
    | _ => Control.throw
             (Invalid_argument (Some (Message.of_string "build_catch_predicate: True or False not found")))
    end in
  let true_c  := leaf [@Prelude; @Logic; @True] in
  let false_c := leaf [@Prelude; @Logic; @False] in
  let b       := Constr.Binder.make None indt in
  let p       := make (Lambda b dsort) in
  (* Pre-apply type parameters to catch_ref before P, since parameterized
     catch symbols take type params first: option_catch A P ... *)
  let catch_applied :=
    if Int.equal (Array.length type_params) 0
    then catch_ref
    else make (App catch_ref type_params)
  in
  let catch_p := make (App catch_applied [| p |]) in
  (* Remaining type after P is fixed: T0 -> T1 -> ... -> T_{n-1} -> T_hole -> (I -> Prop) *)
  let ty_raw := Constr.type catch_p in
  (* Beta-normalize to reduce (fun _ => Prop) applied to constructor args.
     Cosmetic only. The original term is definitionally equal, but this keeps
     binder types like `Prop` instead of `(fun _ : nat => Prop) n` in the
     generated proof term. *)
  let ty := Std.eval_cbv
              { Std.rStrength := Std.Norm;
                Std.rBeta     := true;  Std.rDelta  := false;
                Std.rMatch    := false; Std.rFix    := false;
                Std.rCofix    := false; Std.rZeta   := false;
                Std.rConst    := [] } ty_raw in
  (* Collect n_ctors constructor types + 1 hole type *)
  let case_types := collect_n_binder_types (Int.add n_ctors 1) ty [] in
  let args := List.mapi (fun i ti =>
    let leaf := if Int.equal i true_idx then true_c else false_c in
    wrap_with_lambdas ti leaf
  ) case_types in
  make (App catch_p (Array.of_list args)).

Ltac2 destConstructor (t : constr) : (constructor * instance) option :=
  match kind t with
  | Constructor cstr i => Some (cstr, i)
  | _ => None
  end.

Ltac2 discriminate_equality (heq : constr) (x : constr) (y : constr) :=
    let x := Std.eval_hnf x in
    let y := Std.eval_hnf y in
    let (hx, _) := Constr.decompose_app x in
    let (hy, _) := Constr.decompose_app y in
    (* Determine true_idx (which slot in catch should be True) from hx,     *)
    (* n_ctors, and the inductive from whichever side is a constructor.     *)
    let (true_idx, n_ctors, ind) :=
      match destConstructor hx with
      | Some (cstr_x, _) =>
          let i := Constructor.inductive cstr_x in
          let n := Ind.nconstructors (Ind.data i) in
          (Constructor.index cstr_x, n, i)
      | None =>
          (* hx is not a constructor; it must be TODO I, and then the *)
          (* inductive can only be read off the right-hand side.      *)
          if is_todo_head hx then
            match destConstructor hy with
            | Some (cstr_y, _) =>
                let i := Constructor.inductive cstr_y in
                let n := Ind.nconstructors (Ind.data i) in
                (n, n, i)
            | None =>
                Control.zero
                  (Invalid_argument (Some (Message.of_string "discriminate_equality: y is not a constructor")))
            end
          else
            Control.zero
              (Invalid_argument (Some (Message.of_string "discriminate_equality: x is not a constructor or a hole")))
      end
    in
    let catch_ref := get_catch_for_ind ind in
    (* Extract type parameters from the concrete type of x (e.g., option nat → [| nat |]) *)
    let ind_type := Std.eval_hnf (Constr.type x) in
    let (_, type_params) := Constr.decompose_app ind_type in
    let predicate := build_catch_predicate catch_ref ind type_params n_ctors true_idx in
    let eq_ind_app := '(eq_poly_rec_nodep (x := $x) $predicate I (y := $y) $heq) in
    let proof := eq_ind_app in
    exact (discr_absurd _ $proof).

(* Refutes a discriminable equality. When [t] is [None], searches the context
   for one; when it is [Some h], uses that hypothesis. *)
Ltac2 icp_discriminate0 (t : constr option) : unit :=
  match t with
  | None =>
      match! goal with
      | [ heq : ?x = ?y |- _ ] => discriminate_equality (Control.hyp heq) x y
      | [ heq : ?x ≈̇ ?y |- _ ] =>
          discriminate_equality (as_eq_proof (Control.hyp heq)) x y
      end
  | Some heq =>
      let heq := as_eq_proof heq in
      lazy_match! (Std.eval_hnf (Constr.type heq)) with
      | ?x = ?y => discriminate_equality heq x y
      end
  end.

(* The notation adds intro-backtracking, so the tactic also works on a goal whose
   equality is still hidden under binders. [retry_after] rolls every [intro] back
   when no prefix of them lets [icp_discriminate0] succeed. It backtracks on
   [plain_intro_step] rather than [icp_intro_step], since the equality it looks
   for is already in the context by the time it runs. *)
Ltac2 Notation "icp_discriminate" t(opt(constr)) :=
  retry_after
    "icp_discriminate: No discriminable (incremental) equality found, even after introductions"
    plain_intro_step
    (fun () => icp_discriminate0 t).


(* ------------------------------------------------------------------ *)
(* icp_catch                                                           *)
(* ------------------------------------------------------------------ *)

(* Eliminates [arg] through the catch symbol of its inductive type, so the
   hole case gets a branch alongside the constructors. This is [induction]
   retargeted onto [<ind>_catch]. Plain [induction] and [match] have no hole
   branch, so they cannot eliminate an [Inc]-sorted value. Fails if [arg] is not
   of an inductive type. *)
Ltac2 icp_catch0 (arg : Std.destruction_arg) :=
  Control.enter (fun () =>
    (* For ElimOnAnonHyp n: intro n binders (last one named freshly),
       then induct on it by ident.  For all other forms, extract the
       term type directly and pass arg through unchanged.              *)
    let (arg', ty) :=
      match arg with
      | Std.ElimOnConstr f =>
          let (c, _) := f () in (arg, Constr.type c)
      | Std.ElimOnIdent id =>
          (arg, Constr.type (Control.hyp id))
      | Std.ElimOnAnonHyp n =>
          let fresh_id := Fresh.in_goal (ident_of_string "h") in
          let rec intro_n k :=
            if Int.equal k 1 then Std.intro (Some fresh_id) None
            else (Std.intro None None; intro_n (Int.sub k 1))
          in
          intro_n n;
          (Std.ElimOnIdent fresh_id, Constr.type (Control.hyp fresh_id))
      end
    in
    let ty' := Std.eval_hnf ty in
    let (hd, _) := Constr.decompose_app ty' in
    match kind hd with
    | Ind ind _ =>
        let ind_catch := get_catch_for_ind ind in
        let ic := [{ Std.indcl_arg := arg';
                     Std.indcl_eqn := None;
                     Std.indcl_as  := None;
                     Std.indcl_in  := None }] in
        Std.induction false ic (Some (ind_catch, Std.NoBindings))
    | _ =>
        Control.throw (Invalid_argument
          (Some (Message.of_string "icp_catch: argument is not an inductive type")))
    end).

Ltac2 Notation "icp_catch" arg(destruction_arg) := icp_catch0 arg.


(* ------------------------------------------------------------------ *)
(* icp_inversion                                                       *)
(* ------------------------------------------------------------------ *)

(* Runs the standard [inversion], then [icp_discriminate] to close the branches
   the standard tactic leaves open on [Inc]-sorted equalities. *)
Ltac2 Notation "icp_inversion" arg(destruction_arg) :=
  Std.inversion Std.FullInversion arg None None;
  try (icp_discriminate).


(* ------------------------------------------------------------------ *)
(* icp_injection                                                       *)
(* ------------------------------------------------------------------ *)

(* Counts the leading Prod binders in a type. *)
Ltac2 rec count_prod_binders (ty : constr) : int :=
  match kind ty with
  | Prod _ codom => Int.add 1 (count_prod_binders codom)
  | _ => 0
  end.

(* Skips the [n] leading Prod binders of a type, such as the parameter binders
   of a constructor's type. *)
Ltac2 rec skip_prod_binders (n : int) (ty : constr) : constr :=
  if Int.le n 0 then ty
  else match kind ty with
       | Prod _ codom => skip_prod_binders (Int.sub n 1) codom
       | _ => ty
       end.

(* Flags the value arguments of a constructor that are recursive, that is, whose
   type is headed by the inductive itself. [ty] is the constructor's type with
   its parameter binders already skipped.

   A catch branch follows each recursive argument with an induction hypothesis,
   which is what shifts the binder positions. A nested occurrence such as
   [list I] inside a constructor of [I] is not flagged, and the scheme carries no
   induction hypothesis for it either, so the flags and the branch agree. *)
Ltac2 rec ctor_rec_flags (ind : inductive) (ty : constr) : bool list :=
  match kind ty with
  | Prod b codom =>
      let (hd, _) := Constr.decompose_app (Constr.Binder.type b) in
      let is_rec :=
        match kind hd with
        | Ind i _ =>
            List.equal Ident.equal
              (Env.path (Std.IndRef i)) (Env.path (Std.IndRef ind))
        | _ => false
        end in
      is_rec :: ctor_rec_flags ind codom
  | _ => []
  end.

(* Returns the position of the [arg_idx]-th value argument among the binders of
   its catch branch, counted from the outermost.

   The binder position and [arg_idx] do not coincide. A catch branch interleaves
   each recursive argument with its induction hypothesis, as in
   [forall t, P t -> forall t0, P t0 -> P (TyArrow t t0)], so a recursive
   argument before [arg_idx] shifts it by two rather than by one. Reading the
   position off [arg_idx] alone lands on an induction hypothesis whenever a
   recursive argument comes first. *)
Ltac2 branch_binder_pos (flags : bool list) (arg_idx : int) : int :=
  let rec go (i : int) (fs : bool list) (acc : int) : int :=
    if Int.equal i arg_idx then acc
    else match fs with
         | [] => Int.add acc 1
         | f :: rest => go (Int.add i 1) rest (Int.add acc (if f then 2 else 1))
         end in
  go 0 flags 0.

(* Builds a projection function for the arg_idx-th value argument of ctor_idx:
     proj : indt -> binder_type
   using catch with P = fun _ => binder_type. All non-targeted cases return `ai`
   as a placeholder (only lhs/rhs reach the ctor case).

   [rec_flags] describes the constructor's value arguments, and locates the
   targeted one among the branch's binders through [branch_binder_pos]. *)
Ltac2 build_injection_proj
    (catch_ref : constr) (indt : constr)
    (type_params : constr array)
    (n_ctors : int) (ctor_idx : int) (arg_idx : int)
    (rec_flags : bool list)
    (ai : constr) : constr :=
  let binder_type := Constr.type ai in
  let b_proj := Constr.Binder.make None indt in
  let p_proj := make (Lambda b_proj binder_type) in
  let catch_applied :=
    if Int.equal (Array.length type_params) 0
    then catch_ref
    else make (App catch_ref type_params)
  in
  let catch_p_proj := make (App catch_applied [| p_proj |]) in
  let ty_raw := Constr.type catch_p_proj in
  let ty := Std.eval_cbv
              { Std.rStrength := Std.Norm;
                Std.rBeta     := true;  Std.rDelta  := false;
                Std.rMatch    := false; Std.rFix    := false;
                Std.rCofix    := false; Std.rZeta   := false;
                Std.rConst    := [] } ty_raw in
  let case_types := collect_n_binder_types (Int.add n_ctors 1) ty [] in
  let proj_cases := List.mapi (fun i ti =>
    if Int.equal i ctor_idx then
      let total_binders := count_prod_binders ti in
      let pos := branch_binder_pos rec_flags arg_idx in
      wrap_with_lambdas ti (make (Rel (Int.sub total_binders pos)))
    else
      wrap_with_lambdas ti ai
  ) case_types in
  make (App catch_p_proj (Array.of_list proj_cases)).

(* Builds a projection proj_j for each value argument j and asserts
   Hinj(j) : ai = bi via f_equal proj_j heq.
   The assertion type is eval_hnf of the proof type, which reduces via catch
   rewrite rules: proj_j lhs' ↝ ai, proj_j rhs' ↝ bi. *)
Ltac2 injection_equality (heq : constr) (lhs : constr) (rhs : constr)
    (names : ident list option) :=
  let lhs' := Std.eval_hnf lhs in
  let rhs' := Std.eval_hnf rhs in
  let (hd_lhs, args_lhs) := Constr.decompose_app lhs' in
  let (hd_rhs, args_rhs) := Constr.decompose_app rhs' in
  let fail msg := Control.zero (Tactic_failure (Some (Message.of_string msg))) in
  let (cstr, _) :=
    match destConstructor hd_lhs with
    | Some c => c
    | None   => fail "icp_injection: LHS is not a constructor"
    end
  in
  let _ :=
    match destConstructor hd_rhs with
    | Some (cstr', _) =>
        let same_ind :=
          List.equal Ident.equal
            (Env.path (Std.IndRef (Constructor.inductive cstr)))
            (Env.path (Std.IndRef (Constructor.inductive cstr')))
        in
        if same_ind
        then (if Int.equal (Constructor.index cstr) (Constructor.index cstr')
              then ()
              else fail "icp_injection: LHS and RHS constructors differ; use icp_discriminate")
        else fail "icp_injection: LHS and RHS constructors differ; use icp_discriminate"
    | None => fail "icp_injection: RHS is not a constructor; use icp_discriminate"
    end
  in
  let ind       := Constructor.inductive cstr in
  let ind_type  := Std.eval_hnf (Constr.type lhs') in
  let (_, type_params) := Constr.decompose_app ind_type in
  let n_ctors   := Ind.nconstructors (Ind.data ind) in
  let ctor_idx  := Constructor.index cstr in
  let n_params  := Array.length type_params in
  let n_val     := Int.sub (Array.length args_lhs) n_params in
  (* The type of the constructor at the instance it has in [lhs'], since a
     fresh instance would stay unconstrained in the proof. *)
  let rec_flags :=
    ctor_rec_flags ind
      (skip_prod_binders n_params (Constr.type hd_lhs)) in
  (* Validate user-supplied names before doing anything *)
  let names_arr :=
    match names with
    | None => None
    | Some ns =>
        let got := List.length ns in
        if Int.equal got n_val
        then Some (Array.of_list ns)
        else
          Control.zero (Tactic_failure (Some (
            Message.concat (Message.of_string "icp_injection: expected ")
              (Message.concat (Message.of_int n_val)
                (Message.concat (Message.of_string " identifier(s) after 'as', got ")
                  (Message.of_int got))))))
    end
  in
  (* args_lhs/args_rhs start with n_params type-parameter arguments. *)
  List.iteri (fun i ai =>
    if Int.lt i n_params then ()
    else
      let j    := Int.sub i n_params in
      let bi   := Array.get args_rhs i in
      (* A fresh instance of the catch symbol per field, since the motive of
         each projection lands in the sort of that field's type. *)
      let proj := build_injection_proj (get_catch_for_ind ind) ind_type type_params
                    n_ctors ctor_idx j rec_flags ai in
      let id_i :=
        match names_arr with
        | None   => Fresh.in_goal (ident_of_string "Hinj")
        | Some a => Array.get a j
        end
      in
      let ipat  := Some (Std.IntroNaming (Std.IntroIdentifier id_i)) in
      (* injection_f_equal has all explicit arguments; use @ with _ holes *)
      let proof := '(@injection_f_equal _ _ $proj _ _ $heq) in
      (* The type [ai = bi], at the instance of [eq] in the type of [proof]. A
         quotation would declare a fresh instance that nothing constrains. *)
      let (eq_hd, eq_args) := Constr.decompose_app (Constr.type proof) in
      let ty := make (App eq_hd [| Array.get eq_args 0; ai; bi |]) in
      Std.assert (Std.AssertType ipat ty
        (Some (fun () => exact $proof)))
  ) (Array.to_list args_lhs).

Ltac2 icp_injection0 (heq : constr) (names : ident list option) :=
  let heq := as_eq_proof heq in
  lazy_match! (Std.eval_hnf (Constr.type heq)) with
  | ?lhs = ?rhs => injection_equality heq lhs rhs names
  end.

Ltac2 Notation "icp_injection" heq(constr) :=
  icp_injection0 heq None.

Ltac2 Notation "icp_injection" heq(constr) "as" ids(list1(ident)) :=
  icp_injection0 heq (Some ids).


(* True if [t] is a constructor, possibly applied. *)
Ltac2 is_constructor_app (t : constr) : bool :=
  let (hd, _) := Constr.decompose_app t in
  match Constr.Unsafe.kind hd with
  | Constr.Unsafe.Constructor _ _ => true
  | _ => false
  end.


(* ================================================================== *)
(* 4. Incompleteness and refinement tactics                           *)
(* ================================================================== *)

(* Tactics that work on the refinement order. They reformulate a statement into
   its incremental form, or close a goal whose incompleteness makes it
   uninteresting. *)

(* ------------------------------------------------------------------ *)
(* icp_reform                                                          *)
(* ------------------------------------------------------------------ *)

Ltac2 reform_flags () : Std.red_flags :=
  { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := true;
    Std.rFix := true; Std.rCofix := true; Std.rZeta := true;
    Std.rDelta := false;
    Std.rConst :=
      [ reference:(ir_mono); reference:(ir_anti);
        reference:(IncRefConst); reference:(IncRefEq);
        reference:(IncRefEqL); reference:(IncRefEqR);
        reference:(IncRefEqFun);
        reference:(IncRefForall); reference:(IncRefExists);
        reference:(IncRefConj); reference:(IncRefDisj);
        reference:(IncRefArrow) ] }.

Ltac2 concl_clause () : Std.clause :=
  { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }.

(* Copies binder names from [src] into [dst] wherever the two terms share the
   same logical connective. The IncRef instances mirror the structure of the
   reformulated predicate, so the surviving forall/exists/and/or binders in the
   reduced goal correspond positionally to those in the original goal [src].

   At any structural divergence (e.g. an [eq] leaf becoming a [refinement] leaf,
   or an instance introducing a fresh [exists]) [dst] is left unchanged, since
   there is no user-chosen name to restore there. Only binder name annotations
   change, so the result is alpha-equivalent to [dst] and [change]-compatible. *)
Ltac2 rec transfer_names (src : constr) (dst : constr) : constr :=
  match (kind src, kind dst) with
  | (Prod sb sbody, Prod db dbody) =>
      let nb := Constr.Binder.make (Constr.Binder.name sb) (Constr.Binder.type db) in
      make (Prod nb (transfer_names sbody dbody))
  | (Lambda sb sbody, Lambda db dbody) =>
      let nb := Constr.Binder.make (Constr.Binder.name sb) (Constr.Binder.type db) in
      make (Lambda nb (transfer_names sbody dbody))
  | (App sf sargs, App df dargs) =>
      if Constr.equal sf df
      then
        if Int.equal (Array.length sargs) (Array.length dargs)
        then make (App df (Array.map2 transfer_names sargs dargs))
        else dst
      else dst
  | (_, _) => dst
  end.

(* Reformulates the goal into its incremental form with respect to [x].
   Abstracting the goal over [x] gives a predicate [p], [recover_mono] reduces
   proving [p x] to proving [ir_mono p x], and [cbn] with [reform_flags] unfolds
   the [IncRef] instances so the reformulated statement appears in place.
   [transfer_names] then restores the original binder names. Fails if the goal
   does not mention [x].

   [recover_mono] also takes [is_complete x], which this tactic supplies with
   [all_complete]. Here [x] is the function being reformed, so that premise
   bottoms out at [is_complete TODO] under [completeFun], and is false exactly
   when the tactic is useful. Supplying it here is what keeps the completion
   axioms out of proof scripts, while the lemmas and instances it goes through
   still state every requirement they have.

   The user-facing notation lives in section 5, because it also runs
   [icp_solve] on the reformulated goal. *)
Ltac2 icp_reform0 (x : constr) :=
  let g := Control.goal () in
  let px := Std.eval_pattern [(x, Std.AllOccurrences)] g in
  let p := match kind px with
    | App f _ => f
    | _ => Control.throw (Tactic_failure (Some (Message.of_string "icp_reform: goal does not mention x")))
    end in
  let ty := constr:(ir_mono $p $x) in
  Std.enough ty
    (Some (Some (fun () =>
      let h := Control.hyp @Hincr in
      exact (recover_mono $h (all_complete _))
    )))
    (Some (Std.IntroNaming (Std.IntroIdentifier @Hincr)));
  Control.enter (fun () =>
      Std.cbn (reform_flags ()) (concl_clause ());
      let reduced := Control.goal () in
      let renamed := transfer_names g reduced in
      Std.change None (fun _ => renamed) (concl_clause ())).


(* ------------------------------------------------------------------ *)
(* icp_hole_refinement                                                 *)
(* ------------------------------------------------------------------ *)

Ltac2 all_flags : Std.red_flags :=
  { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := true;
    Std.rFix := true; Std.rCofix := true; Std.rZeta := true;
    Std.rDelta := true; Std.rConst := [] }.

(* If [c] reduces to an application of [TODO], returns [Some nf] with that
   normal form; otherwise [None].
   [eval_cbv all_flags] is needed, not [eval_hnf] nor [eval_cbn]. Each weaker
   strategy misses a real case.
     - [cbn] is conservative and does not unfold a non-recursive definition like
       [add_v0 := fun _ _ => TODO nat], leaving the [TODO] hidden.
     - [hnf] does not apply the hole propagation rewrite rules, so it gets stuck
       on e.g. [infer_type map_empty (eval (tm_app t1 t2))] (where the hole
       only surfaces after [eval] reduces to [TODO tm] and the rewrite rule
       propagates it through [infer_type]'s match).
   [cbv] with full delta does both. It unfolds every constant and applies the
   rewrite rules, so both shapes reduce to [TODO _]. *)
Ltac2 hole_nf (c : constr) : constr option :=
  let c := Std.eval_cbv all_flags c in
  lazy_match! c with
  | TODO _ => Some c
  | _       => None
  end.

(* Reduction flags that unfold everything and apply rewrite rules, but keep the
   refinement head [⊑] (= [refinement]) folded, see [icp_hole_refinement0]. With
   [rDelta := true] the [rConst] list is the set of constants to leave folded. *)
Ltac2 expose_flags () : Std.red_flags :=
  { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := true;
    Std.rFix := true; Std.rCofix := true; Std.rZeta := true;
    Std.rDelta := true; Std.rConst := [reference:(refinement)] }.

(* Closes a goal of the form [lhs ⊑ rhs] when [rhs] reduces to [TODO _].
   [hole_nf] first probes the RHS non-destructively; only once it confirms a
   hole does it reduce the conclusion in place with [expose_flags] so the RHS
   becomes [TODO _] *syntactically*, then close with the [hole_is_top] field of
   the [Refinable] instance.
   The in-place reduction is essential. [apply] matches on the syntactic head,
   and unification does not reduce [rhs] far enough to expose the hole. In
   particular, the rewrite-rule hole propagation in
   [infer_type (eval (tm_app ..))] is never triggered by unification, and
   kernel conversion (so [change]) does not apply the rewrite rules either.
   [expose_flags] keeps [⊑] folded so the goal stays a refinement the field
   applies to; how the instance defines the relation, and whether [lhs] is
   stuck on a variable, does not matter. Fails on any other goal, so the caller
   wraps it in [try] to stay silent (a failure here rolls the reduction
   back). *)
Ltac2 icp_hole_refinement0 () :=
  lazy_match! goal with
  | [ |- _ ⊑ ?rhs ] =>
      match hole_nf rhs with
      | Some _ =>
          Std.cbv (expose_flags ()) (concl_clause ());
          apply hole_is_top
      | None =>
          Control.zero
            (Tactic_failure (Some (Message.of_string "icp_hole_refinement: RHS is not TODO _")))
      end
  | [ |- _ ] =>
      Control.zero
        (Tactic_failure (Some (Message.of_string "icp_hole_refinement: goal is not _ ⊑ _")))
  end.

(* The notation adds intro-backtracking. After [icp_reform] the leaf
   [_ ⊑ TODO _] often sits under binders, as in [forall n, succ n ⊑ add_v0 n 1].
   [icp_solve] does not go through this notation, it owns a single [retry_after]
   over all three of its branches. *)
Ltac2 Notation "icp_hole_refinement" :=
  retry_after
    "icp_hole_refinement: no [_ ⊑ TODO _] goal, even after introductions"
    plain_intro_step
    icp_hole_refinement0.


(* ------------------------------------------------------------------ *)
(* icp_absurd_complete                                                 *)
(* ------------------------------------------------------------------ *)

(* Reduction flags mirroring [expose_flags], but for the completeness side. They
   unfold everything and apply the rewrite rules, while keeping [is_complete]
   folded. Keeping the projection folded matters because [hole_not_complete]
   is stated as [is_complete (TODO T) -> False], and unfolding [is_complete]
   would turn the hypothesis into the bare per-type predicate
   ([CompleteNat _], ...), so the field would no longer apply.  The [Complete]
   instance argument does get unfolded, which is harmless. It is still
   convertible with the one the field expects. *)
Ltac2 expose_complete_flags () : Std.red_flags :=
  { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := true;
    Std.rFix := true; Std.rCofix := true; Std.rZeta := true;
    Std.rDelta := true; Std.rConst := [reference:(is_complete)] }.

Ltac2 hyp_clause (h : ident) : Std.clause :=
  { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
    Std.on_concl := Std.NoOccurrences }.

Ltac2 rewrite_in (ori : Std.orientation) (heq : constr) (h : ident) : unit :=
  Std.rewrite false
    [{ Std.rew_orient := Some ori; Std.rew_repeat := Std.Precisely 1;
       Std.rew_equatn := (fun () => (heq, Std.NoBindings)) }]
    (hyp_clause h) None.

(* [complete_arg ty] returns [Some x] when [ty] is a completeness hypothesis
   [is_complete x], [None] otherwise.  The bare counterpart of
   [eq_anti_premise], which looks for the antitone-equality [icp_reform] leaves in
   the goal's premise, while this one inspects the type of a hypothesis
   already in context. *)
Ltac2 complete_arg (ty : constr) : constr option :=
  lazy_match! ty with
  | is_complete ?x => Some x
  | _ => None
  end.

(* [absurd_complete_hyp hc] closes the current [False] goal from
   [hc : is_complete x], provided [x] reduces to [TODO _].
   [hole_nf] probes non-destructively first; only once it confirms a hole does
   it reduce the hypothesis in place, so that the hole becomes *syntactic*.
   That reduction is what makes the handoff robust. As with
   [icp_hole_refinement0], plain unification does not fire the hole propagation
   rewrite rules, so a field stated on [TODO T] would not see through a term
   that only reduces to one.
   The refutation is the [hole_not_complete] field of the type's
   [CompleteMinimal] instance, which instance search finds from the type of
   [hc]. A type without that instance is a type the tactic cannot refute a
   hole of, and the failure is an unresolved instance rather than a missing
   hint. *)
Ltac2 absurd_complete_hyp (hc : ident) : unit :=
  match complete_arg (Constr.type (Control.hyp hc)) with
  | None =>
      Control.zero (Tactic_failure (Some (Message.of_string
        "icp_absurd_complete: not a completeness hypothesis")))
  | Some x =>
      match hole_nf x with
      | Some _ =>
          Std.cbv (expose_complete_flags ()) (hyp_clause hc);
          let h := Control.hyp hc in
          exact (hole_not_complete $h)
      | None =>
          Control.zero (Tactic_failure (Some (Message.of_string
            "icp_absurd_complete: completeness argument does not reduce to a hole")))
      end
  end.

(* [icp_absurd_complete] closes any goal that sits on a contradictory
   completeness hypothesis. It looks for a hypothesis [hc : is_complete x] by
   type (as [icp_discriminate] and [eq_anti_premise] do, never by name), and:
     - if [x] already reduces to [TODO _], refutes [hc] directly;
     - otherwise, looks for an equality in context whose rewrite turns [x] into
       [TODO _] form, and refutes the rewritten hypothesis. This is the
       mechanized form of the [rewrite <- Heq in _Hcomplete_n; exfalso; apply ...]
       step the incremental premise proofs used to do by hand, where the
       completeness assumption is about a value the (still incomplete) program
       cannot produce.
     - failing both, projects a completeness hypothesis out of an antitone-equality
       in context with [eqa_complete_l] or [eqa_complete_r], and starts
       again. That is the shape a proof script has when it introduced the
       premise itself. The completeness is sealed inside [H : ??? ≈̇ x] rather
       than sitting in the context, which is where [icp_intro_step] would have
       put it had [icp_solve] owned the introduction.

   Both [match!]es backtrack, so every completeness hypothesis is tried against
   every equality, in both orientations, [RTL] first because that is the
   interesting direction, replacing the complete value by the incomplete term
   computing it. Every [rewrite] and every projection is rolled back when the
   branch does not end in a refutation, so on failure the context is left
   untouched and the tactic composes under [try]. *)
(* Asserts [is_complete x] from [proof] and returns the name it landed under.
   The name is cosmetic, as [absurd_complete_hyp] locates its hypothesis by the
   argument it is given rather than by name. *)
Ltac2 project_complete (proof : constr) (x : constr) : ident :=
  let hc := Fresh.in_goal (ident_of_string "_Hcomplete") in
  Std.assert (Std.AssertType
    (Some (Std.IntroNaming (Std.IntroIdentifier hc)))
    '(is_complete $x)
    (Some (fun () => exact $proof)));
  hc.

Ltac2 icp_absurd_complete0 () : unit :=
  (lazy_match! goal with
   | [ |- False ] => ()
   | [ |- _ ] => exfalso
   end);
  match! goal with
  | [ hc : is_complete _ |- _ ] =>
      Control.plus
        (fun () => absurd_complete_hyp hc)
        (fun _ =>
          match! goal with
          | [ heq : _ = _ |- _ ] =>
              let h := Control.hyp heq in
              first [ rewrite_in Std.RTL h hc | rewrite_in Std.LTR h hc ];
              absurd_complete_hyp hc
          end)
  | [ hm : ?x ≈̇ _ |- _ ] =>
      let h := Control.hyp hm in
      absurd_complete_hyp (project_complete '(eqa_complete_l $h) x)
  | [ hm : _ ≈̇ ?y |- _ ] =>
      let h := Control.hyp hm in
      absurd_complete_hyp (project_complete '(eqa_complete_r $h) y)
  end.

Ltac2 Notation "icp_absurd_complete" := icp_absurd_complete0 ().


(* ------------------------------------------------------------------ *)
(* complete_inversion                                                  *)
(* ------------------------------------------------------------------ *)

(* Replaces the hypothesis [h : is_complete (C a1 .. an)] by the completeness
   of the fields of [C], each stated on [is_complete] so that the [icp] hints
   apply to it. *)
Ltac2 invert_complete_hyp (h : ident) : unit :=
  lazy_match! (Constr.type (Control.hyp h)) with
  | @is_complete ?a ?inst _ =>
      let (pred, args) :=
        Constr.decompose_app (Std.eval_hnf (Constr.type (Control.hyp h))) in
      let p := Constr.Unsafe.make (Constr.Unsafe.App pred
                 (Array.sub args 0 (Int.sub (Array.length args) 1))) in
      Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
      Control.enter (fun () => try (icp_discriminate0 None));
      Control.enter (fun () =>
        repeat (match! goal with
          | [ e : ?l = ?r |- _ ] =>
              if Bool.and (is_constructor_app l) (is_constructor_app r)
              then () else Control.zero Match_failure;
              icp_injection0 (Control.hyp e) None; Std.clear [e]
          end);
        ltac1:(subst);
        ltac1:(p a inst |-
          repeat match goal with
                 | K : p ?x |- _ => change (@is_complete a inst x) in K
                 end)
          (Ltac1.of_constr p) (Ltac1.of_constr a) (Ltac1.of_constr inst);
        Std.clear [h])
  end.

(* Gives the [icp] hints the completeness of the fields of a value known to be
   complete. This makes per-type inversion lemmas such as
   [is_complete (S n) -> is_complete n] unnecessary. The known completeness is a
   hypothesis [is_complete (C a1 .. an)], or a side [C a1 .. an] of an
   antitone-equality hypothesis, projected as in [icp_absurd_complete]. Fails
   when the context has neither. A value [TODO _] has no constructor at its head
   and is left to [icp_absurd_complete]. *)
Ltac2 complete_inversion0 () :=
  match! goal with
  | [ hc : is_complete ?t |- _ ] =>
      if is_constructor_app t then invert_complete_hyp hc
      else Control.zero Match_failure
  | [ hm : _ ≈̇ ?y |- _ ] =>
      if is_constructor_app y then
        let h := Control.hyp hm in
        invert_complete_hyp (project_complete '(eqa_complete_r $h) y)
      else Control.zero Match_failure
  | [ hm : ?x ≈̇ _ |- _ ] =>
      if is_constructor_app x then
        let h := Control.hyp hm in
        invert_complete_hyp (project_complete '(eqa_complete_l $h) x)
      else Control.zero Match_failure
  end.

#[export] Hint Extern 3 (is_complete _) => complete_inversion0 () : icp.


(* ------------------------------------------------------------------ *)
(* Antitone-equality goals                                            *)
(* ------------------------------------------------------------------ *)

(* Hands the focused goal, known to be a completeness obligation, to the [icp]
   database.

   [solve] is what makes the handoff safe, as it does on [absurd_complete_hyp].
   A bare [eauto] succeeds without closing the goal when no hint applies, which
   would leave the hypothesis applied and an [is_complete] leaf open. The
   failure names the obligation, because the usual cause is a missing hint
   rather than a false goal.

   A hint applies only when it is stated on [is_complete]. [eauto] indexes hints
   by head symbol and the goal is headed by the projection, so a hint on the
   underlying predicate ([Hint Constructors CompleteNat]) is never tried,
   however convertible the two are. The generic hints [complete_constructor] in
   Reformulation.v and [complete_inversion0] above are stated on [is_complete]
   for that reason.

   [first] would catch the failure of its last alternative and re-raise it as an
   anonymous [Tactic_failure None], swallowing the message below, so the choice
   is made with [Control.case]. Dropping the continuation also makes the
   database call deterministic, so a later failure cannot backtrack into [eauto]
   for another proof of an obligation nobody reads. *)
Ltac2 discharge_complete (x : constr) : unit :=
  match Control.case (fun () => ltac1:(solve [ eauto with icp ])) with
  | Val _ => ()
  | Err _ =>
      Control.zero (Tactic_failure (Some
        (Message.concat
           (Message.of_string
              "icp_apply: the icp database did not discharge the completeness obligation is_complete ")
           (Message.of_constr x))))
  end.

(* Opens a [_ ≈̇ _] goal: the completeness half goes to the [icp] database and
   the equation is left open, which is the only content there was. The right
   side is tried first, then the left, since either completeness conjunct
   follows from the other through the equation and only one of the two is
   usually within the database's reach.

   The user never has to build an antitone-equality by hand, and never sees the
   conjunction it is made of. *)
Ltac2 eq_anti_intro_goal () : unit :=
  lazy_match! goal with
  | [ |- ?x ≈̇ ?y ] =>
      Control.plus
        (fun () =>
           Std.apply true false [fun () => ('(@eqa_intro_r), Std.NoBindings)] None;
           Control.focus 1 1 (fun () => discharge_complete y))
        (fun _ =>
           Std.apply true false [fun () => ('(@eqa_intro_l), Std.NoBindings)] None;
           Control.focus 1 1 (fun () => discharge_complete x))
  | [ |- _ ] =>
      Control.zero (Tactic_failure (Some (Message.of_string
        "eq_anti_intro_goal: goal is not _ ≈̇ _")))
  end.

(* [eq_anti_intro_goal] on an antitone-equality goal, nothing on any other goal. A
   goal that is not a [≈̇] is left alone rather than failing, so the tactics
   built on it degrade into their plain counterparts; a [≈̇] goal the database
   cannot discharge still fails with a message naming the obligation, since
   silently leaving it open would hand the user a goal only the library knows
   how to open. *)
Ltac2 eq_anti_intro_goal_opt () : unit :=
  lazy_match! goal with
  | [ |- _ ≈̇ _ ] => eq_anti_intro_goal ()
  | [ |- _ ] => ()
  end.


(* ------------------------------------------------------------------ *)
(* icp_f_equal                                                         *)
(* ------------------------------------------------------------------ *)

(* Peels a goal [h a1 .. ak ⊑ h b1 .. bk] into its k pointwise subgoals
   [ai ⊑ bi], or [h a1 .. ak ≈ h b1 .. bk] into [ai ≈ bi], the incremental
   mirror of [f_equal]. All k are left open, the reflexive ones included.
   Discharging the reflexive ones is left to the notation.

   The tactic dispatches on the goal shape so that a proof script mirrors the
   complete one whatever [IncRef] instance fired: [monotone_app_k] on a [⊑]
   goal, [eqm_app_k] on a [≈] one. The [≈] family carries its monotonicity
   premise explicitly, and it is discharged here with the matching
   [monotone_app_k] rather than by a hint, so every use of it is greppable. It
   stops at arity 3. There is no [is_monotone_4] and above to state the premise
   with.

   The head [h] and the arity [k] are read directly from the goal, then the
   lemma is applied with [f := h] fixed. Fixing the head sidesteps the
   higher-order unification ambiguity that makes a bare [apply monotone_app_k]
   fail whenever an argument repeats across positions. *)
(* The number of leading arguments in [args] that are types, such as the
   parameter [nat] of [@cons nat O nil] or of [@app nat l m]. *)
Ltac2 type_args_prefix (args : constr array) : int :=
  let n := Array.length args in
  let rec go (i : int) : int :=
    if Int.equal i n then i
    else match kind (Constr.type (Array.get args i)) with
         | Sort _ => go (Int.add i 1)
         | _ => i
         end
  in
  go 0.

(* Reads the common head and arity off the two sides of a peelable goal.
   Shared by the [⊑] and [≈] branches, which differ only in the lemma family
   they then apply. The leading type arguments stay in the head, so that
   [@cons nat O nil] peels into [O] and [nil] only, since there is no
   refinement between types. *)
Ltac2 peel_app (lhs : constr) (rhs : constr) : constr * int :=
  match kind lhs with
  | App h args =>
      (match kind rhs with
       | App h2 args2 =>
           if Bool.neg (Constr.equal h h2)
           then Control.throw (Tactic_failure
             (Some (Message.of_string "icp_f_equal: lhs and rhs have different heads")))
           else if Bool.neg (Int.equal (Array.length args) (Array.length args2))
           then Control.throw (Tactic_failure
             (Some (Message.of_string "icp_f_equal: lhs and rhs have different arities")))
           else
             let k := type_args_prefix args in
             let with_types f a :=
               if Int.equal k 0 then f else Constr.Unsafe.make (App f (Array.sub a 0 k)) in
             let head := with_types h args in
             let head2 := with_types h2 args2 in
             if Bool.neg (Constr.equal head head2)
             then Control.throw (Tactic_failure
               (Some (Message.of_string "icp_f_equal: lhs and rhs have different type arguments")))
             else if Int.equal k (Array.length args)
             then Control.throw (Tactic_failure
               (Some (Message.of_string "icp_f_equal: no argument to peel past the type arguments")))
             else (head, Int.sub (Array.length args) k)
       | _ => Control.throw (Tactic_failure
             (Some (Message.of_string "icp_f_equal: rhs is not an application")))
       end)
  | _ => Control.throw (Tactic_failure
        (Some (Message.of_string "icp_f_equal: lhs is not an application")))
  end.

Ltac2 icp_f_equal0 () : unit :=
  lazy_match! goal with
  | [ |- ?lhs ⊑ ?rhs ] =>
      let (h, k) := peel_app lhs rhs in
      if Int.equal k 1 then eapply (@monotone_app_1 _ _ _ _ $h)
      else if Int.equal k 2 then eapply (@monotone_app_2 _ _ _ _ _ _ $h)
      else if Int.equal k 3 then eapply (@monotone_app_3 _ _ _ _ _ _ _ _ $h)
      else if Int.equal k 4 then eapply (@monotone_app_4 _ _ _ _ _ _ _ _ _ _ $h)
      else if Int.equal k 5 then eapply (@monotone_app_5 _ _ _ _ _ _ _ _ _ _ _ _ $h)
      else Control.throw (Tactic_failure
        (Some (Message.of_string "icp_f_equal: arity not in 1..5")))
  | [ |- ?lhs ≈ ?rhs ] =>
      let (h, k) := peel_app lhs rhs in
      if Int.equal k 1
      then eapply (@eqm_app_1 _ _ _ _ $h (@monotone_app_1 _ _ _ _ $h))
      else if Int.equal k 2
      then eapply (@eqm_app_2 _ _ _ _ _ _ $h (@monotone_app_2 _ _ _ _ _ _ $h))
      else if Int.equal k 3
      then eapply (@eqm_app_3 _ _ _ _ _ _ _ _ $h (@monotone_app_3 _ _ _ _ _ _ _ _ $h))
      else Control.throw (Tactic_failure
        (Some (Message.of_string "icp_f_equal: arity not in 1..3 on a ≈ goal")))
  | [ |- _ ] => Control.throw (Tactic_failure
        (Some (Message.of_string "icp_f_equal: goal is not _ ⊑ _ nor _ ≈ _")))
  end.

(* The notation peels with [icp_f_equal0] and then discharges the reflexive
   subgoals [a ⊑ a] and [a ≈ a] with [reflexivity], mirroring how plain
   [f_equal] drops syntactically equal arguments. Both shapes are reachable by
   [reflexivity]: [refinableReflexive] covers the first and [eqMonoReflexive] the
   second. [icp_f_equal0] does the peeling on its own and this cleanup lives in
   the notation. *)
Ltac2 Notation "icp_f_equal" :=
  icp_f_equal0 ();
  try0 (fun () => Std.reflexivity ()).


(* ------------------------------------------------------------------ *)
(* icp_rewrite                                                         *)
(* ------------------------------------------------------------------ *)

(* Rewrites the goal with the equations and monotone equalities [h1 .. hk],
   the incremental mirror of [rewrite h1, .., hk]. The monotone equalities
   [ei ≈ vi] rewrite a [≈] goal all at once, up to five per call. The tactic
   abstracts the [ei] out of the side of the goal they occur on into a
   function [g], and [eqm_congr_k] leaves the equation [g v1 .. vk = r], shown
   with the [vi] in place of the [ei] as [rewrite] would leave it. The
   equations go through plain [rewrite], in the order of the list. Those
   listed before the monotone equalities rewrite the goal before them, and
   those listed after rewrite the equation they leave.

   The monotone equalities go in one call because [≈] is not transitive.
   After one of them the goal is an equation, which another one cannot
   rewrite. For the same reason they have to be listed together, and an
   equation between two of them fails. With no monotone equality among
   [h1 .. hk] the tactic is exactly
   [rewrite]. An antitone-equality counts as an equation, as in
   [as_eq_proof]. *)

Ltac2 Type rewrite_hyp := [ RwEquation (constr) | RwMono (constr, constr) ].

Ltac2 icp_rewrite_fail (msg : message) := Control.throw (Tactic_failure (Some msg)).

(* Returns the conclusion of [c] under its leading products, and true if there
   were any. *)
Ltac2 rec strip_prods (c : constr) : constr * bool :=
  match kind c with
  | Prod _ body => let (concl, _) := strip_prods body in (concl, true)
  | _ => (c, false)
  end.

(* Classifies [h] by the shape of its type. It reads the type as it is first,
   so the terms to rewrite are the ones you see, and reduces it with
   [reform_flags] only when it is a folded [ir_mono] or [ir_anti]. A quantified
   equation goes to [rewrite] as it is, which instantiates it. You have to give
   the arguments of a quantified monotone equality or antitone-equality, since
   the terms to abstract must be known. *)
Ltac2 classify_rewrite_hyp (h : constr) : rewrite_hyp :=
  let classify (ty : constr) :=
    let (concl, quantified) := strip_prods ty in
    let instantiate_first () := icp_rewrite_fail (fprintf
      "icp_rewrite: give the arguments of %t; the terms to rewrite must be known" h) in
    lazy_match! concl with
    | ?e ≈ _ => if quantified then instantiate_first () else Some (RwMono h e)
    | _ ≈̇ _ =>
        if quantified then instantiate_first () else Some (RwEquation '(eqa_eq $h))
    | _ = _ => Some (RwEquation h)
    | _ => None
    end in
  let ty := Constr.type h in
  match classify ty with
  | Some r => r
  | None =>
      match classify (Std.eval_cbn (reform_flags ()) ty) with
      | Some r => r
      | None => icp_rewrite_fail (fprintf
          "icp_rewrite: %t is neither an equation nor a monotone equality" h)
      end
  end.

Ltac2 rewrite_concl (heq : constr) : unit :=
  Std.rewrite false
    [{ Std.rew_orient := Some Std.LTR; Std.rew_repeat := Std.Precisely 1;
       Std.rew_equatn := (fun () => (heq, Std.NoBindings)) }]
    (concl_clause ()) None.

Ltac2 rec mono_hyps (rs : rewrite_hyp list) : (constr * constr) list :=
  match rs with
  | [] => []
  | r :: rest =>
      match r with
      | RwMono h e => (h, e) :: mono_hyps rest
      | RwEquation _ => mono_hyps rest
      end
  end.

(* True if [e] occurs in [c]; false otherwise. *)
Ltac2 occurs_in (e : constr) (c : constr) : bool :=
  match kind (Std.eval_pattern [(e, Std.AllOccurrences)] c) with
  | App f _ =>
      (match kind f with
       | Lambda _ body => Bool.neg (noccur_between 1 1 body)
       | _ => false
       end)
  | _ => false
  end.

Ltac2 rec check_distinct (es : constr list) : unit :=
  match es with
  | [] => ()
  | e :: rest =>
      (if List.exist (fun e' => Constr.equal e e') rest
       then icp_rewrite_fail (fprintf "icp_rewrite: %t is rewritten twice" e)
       else ());
      check_distinct rest
  end.

(* Substitutes the arguments of a head beta-redex [(fun x1 .. xk => b) v1 .. vk]
   into [b] without any other reduction, which gives the term [rewrite] shows.
   Returns any other term unchanged. *)
Ltac2 beta_head (c : constr) : constr :=
  match kind c with
  | App f args =>
      let rec go (f : constr) (vs : constr list) :=
        match vs with
        | [] => f
        | v :: rest =>
            match kind f with
            | Lambda _ body => go (substnl [v] 0 body) rest
            | _ => make (App f (Array.of_list vs))
            end
        end in
      go f (Array.to_list args)
  | _ => c
  end.

(* Beta-reduces the left-hand side of the equation goal [eqm_congr_k] leaves. *)
Ltac2 beta_head_lhs () : unit :=
  let c := Control.goal () in
  match kind c with
  | App eqh args =>
      let args := Array.copy args in
      let i := Int.sub (Array.length args) 2 in
      Array.set args i (beta_head (Array.get args i));
      Std.change None (fun _ => make (App eqh args)) (concl_clause ())
  | _ => ()
  end.

(* Fails unless every one of the k binders of [g] occurs in its body. A binder
   goes unused when its term [ei] sits inside another [ej] abstracted with it,
   and its hypothesis would otherwise go unused. *)
Ltac2 check_all_abstracted (g : constr) (es : constr list) : unit :=
  let rec body (c : constr) (n : int) :=
    if Int.equal n 0 then c
    else match kind c with
      | Lambda _ b => body b (Int.sub n 1)
      | _ => c
      end in
  let k := List.length es in
  let b := body g k in
  let rec check (es : constr list) (i : int) :=
    match es with
    | [] => ()
    | e :: rest =>
        (* The binder of [ei] is [Rel (k - i + 1)] in the innermost body. *)
        (if noccur_between (Int.add (Int.sub k i) 1) 1 b
         then icp_rewrite_fail (fprintf
           "icp_rewrite: %t occurs only inside another rewritten term" e)
         else ());
        check rest (Int.add i 1)
    end in
  check es 1.

(* Rewrites the left-hand side of a [≈] goal with the monotone equalities
   [(hi, ei)]. *)
Ltac2 rewrite_mono_lhs (monos : (constr * constr) list) : unit :=
  lazy_match! goal with
  | [ |- ?lhs ≈ _ ] =>
      let pats := List.map (fun (_, e) => (e, Std.AllOccurrences)) monos in
      let g := match kind (Std.eval_pattern pats lhs) with
        | App f _ => f
        | _ => icp_rewrite_fail (fprintf "icp_rewrite: cannot abstract %t" lhs)
        end in
      check_all_abstracted g (List.map (fun (_, e) => e) monos);
      (match List.map (fun (h, _) => h) monos with
       | [h1] => apply (fun hr => eqm_congr_1 $g hr $h1)
       | [h1; h2] => apply (fun hr => eqm_congr_2 $g hr $h1 $h2)
       | [h1; h2; h3] => apply (fun hr => eqm_congr_3 $g hr $h1 $h2 $h3)
       | [h1; h2; h3; h4] => apply (fun hr => eqm_congr_4 $g hr $h1 $h2 $h3 $h4)
       | [h1; h2; h3; h4; h5] =>
           apply (fun hr => eqm_congr_5 $g hr $h1 $h2 $h3 $h4 $h5)
       | _ => icp_rewrite_fail (fprintf "icp_rewrite: at most 5 monotone equalities per call")
       end);
      beta_head_lhs ()
  end.

(* Splits the classified hypotheses [(h, r)] into the equations before the
   first monotone equality, the monotone equalities, and the equations after
   the last one. Fails on an equation between two monotone equalities, since
   the monotone equalities are rewritten in one step. *)
Ltac2 split_rewrite_hyps (rs : (constr * rewrite_hyp) list)
  : constr list * rewrite_hyp list * constr list :=
  let rec equations (rs : (constr * rewrite_hyp) list) :=
    match rs with
    | (h, RwEquation heq) :: rest =>
        let (eqs, rest) := equations rest in ((h, heq) :: eqs, rest)
    | _ => ([], rs)
    end in
  let rec monos (rs : (constr * rewrite_hyp) list) :=
    match rs with
    | (_, RwMono h e) :: rest =>
        let (ms, rest) := monos rest in (RwMono h e :: ms, rest)
    | _ => ([], rs)
    end in
  let (before, rest) := equations rs in
  let (ms, rest) := monos rest in
  let (after, rest) := equations rest in
  match rest, after with
  | [], _ => (List.map snd before, ms, List.map snd after)
  | _, (h, _) :: _ => icp_rewrite_fail (fprintf
      "icp_rewrite: %t comes between two monotone equalities; list it before or after them" h)
  (* A nonempty [rest] starts with a monotone equality, so [after] is not empty. *)
  | _, [] => Control.throw Assertion_failure
  end.

Ltac2 icp_rewrite0 (hs : constr list) : unit :=
  let rs := List.map (fun h => (h, classify_rewrite_hyp h)) hs in
  let (before, rs, after) := split_rewrite_hyps rs in
  List.iter rewrite_concl before;
  let monos := mono_hyps rs in
  (match monos with
  | [] => ()
  | _ =>
      (if Int.gt (List.length monos) 5
       then icp_rewrite_fail (fprintf "icp_rewrite: at most 5 monotone equalities per call")
       else ());
      let es := List.map (fun (_, e) => e) monos in
      check_distinct es;
      lazy_match! goal with
      | [ |- ?lhs ≈ ?rhs ] =>
          if List.for_all (fun e => occurs_in e lhs) es then rewrite_mono_lhs monos
          else if List.for_all (fun e => occurs_in e rhs) es
          then (apply eqm_sym; rewrite_mono_lhs monos; Std.symmetry (concl_clause ()))
          else icp_rewrite_fail (fprintf
            "icp_rewrite: the rewritten terms must all occur on one side of ≈")
      | [ |- _ ] => icp_rewrite_fail (fprintf
          "icp_rewrite: monotone equalities can only rewrite a ≈ goal")
      end
  end);
  List.iter rewrite_concl after.

Ltac2 Notation "icp_rewrite" hs(list1(constr, ",")) := icp_rewrite0 hs.


(* ------------------------------------------------------------------ *)
(* icp_etrans                                                          *)
(* ------------------------------------------------------------------ *)

(* Performs the transitive step on a refinement goal. Given
   [h : a ⊑ b] and a goal [a ⊑ c] it advances the lower bound through [h] and
   leaves the single residual goal [b ⊑ c]. It is the [etransitivity] that the
   recursive-case proofs perform before discharging the leftover monotonicity
   gap. It does no [f_equal], no incompleteness solving and no hypothesis
   search. The stepping stone [h] is given explicitly. The middle
   point [b] is fixed by unification with the type of [h]; [c] comes from the
   goal. Fails on any non-refinement goal or when [h] does not match the lhs.

   There is no [≈] branch, and there cannot be one: monotone equality is not
   transitive. The [≈] goal a proof reaches for a transitive step is
   [icp_apply]'s, which goes through [eqm_weaken]. *)
Ltac2 icp_etrans0 (h : constr) : unit :=
  lazy_match! goal with
  | [ |- _ ⊑ _ ] => eapply (is_transitive _ _ _ $h)
  | [ |- _ ≈ _ ] => Control.throw (Tactic_failure
        (Some (Message.of_string
          "icp_etrans: ≈ is not transitive, use icp_apply")))
  | [ |- _ ] => Control.throw (Tactic_failure
        (Some (Message.of_string "icp_etrans: goal is not _ ⊑ _")))
  end.

Ltac2 Notation "icp_etrans" h(constr) := icp_etrans0 h.


(* ------------------------------------------------------------------ *)
(* icp_close_gap                                                       *)
(* ------------------------------------------------------------------ *)

(* Discharges a residual monotonicity/incompleteness gap on a refinement goal.
   On each subgoal it tries, in order: [reflexivity] (equal sides),
   [icp_hole_refinement0] (an [_ ⊑ TODO _] leaf), or, failing both, peeling one
   monotone layer with [icp_f_equal0] and recursing on every resulting subgoal.
   It terminates because each peel reduces structure, and fails if a leaf is
   neither reflexive, incomplete, nor a matching-head application. This is the
   iterative generalization of [f_equal; icp_solve], because the gap left after
   a transitive step can be deeper than one constructor (e.g.
   [S (add_v2 n m) ⊑ S (add_v2 n (TODO nat))]).

   It has no notation of its own. It introduces nothing, and no goal shape a
   user types calls for it directly. *)
Ltac2 rec icp_close_gap () : unit :=
  first
    [ Std.reflexivity ()
    | icp_hole_refinement0 ()
    | (icp_f_equal0 (); Control.enter (fun () => icp_close_gap ())) ].


(* ------------------------------------------------------------------ *)
(* icp_eq_mono                                                        *)
(* ------------------------------------------------------------------ *)

(* Checks whether [t] is an application of [TODO]. [meet_hole] runs on terms
   already in normal form, so a syntactic test is enough here. [hole_nf] is the
   counterpart for a term that still has to be reduced. *)
Ltac2 is_hole_app (t : constr) : bool :=
  match kind t with
  | App hd _ => is_todo_head hd
  | _ => false
  end.

(* Merges two terms in normal form into their least common refinement, with
   [TODO] read as a wildcard. A hole on either side yields the other side,
   equal heads descend argument-wise, and terms that are already the same yield
   themselves. The three cases are [icp_close_gap]'s on goals, so the halves a
   successful merge leaves are shapes it walks. Returns the merged term together
   with whether the merge ever *filled* a hole, that is, met a hole on one
   side facing real structure on the other. Returns [None] when the two sides
   have no common refinement at all, as for [O] against [S ???].

   The flag is the fill guard of [icp_eq_mono], and the reason it is computed here
   rather than tested afterwards. Two sides that merge with no fill are
   convertible, so the goal is trivial by reflexivity rather than by
   incompleteness, and closing it in [icp_solve] would break the rule that
   [icp_solve] never closes a goal about complete code. Asking instead whether a
   a hole occurs anywhere would not do. A stuck call to an incomplete function
   carries the hole of a branch that plays no part in the goal. *)
Ltac2 rec meet_hole (t1 : constr) (t2 : constr) : (constr * bool) option :=
  if is_hole_app t1
  then (if is_hole_app t2 then Some (t1, false) else Some (t2, true))
  else if is_hole_app t2 then Some (t1, true)
  else if Constr.equal t1 t2 then Some (t1, false)
  else
    match (kind t1, kind t2) with
    | (App h1 a1, App h2 a2) =>
        let n := Array.length a1 in
        if Bool.and (Constr.equal h1 h2) (Int.equal n (Array.length a2))
        then
          let rec go (i : int) (acc : constr list) (filled : bool)
              : (constr list * bool) option :=
            if Int.equal i n
            then Some (List.rev acc, filled)
            else
              match meet_hole (Array.get a1 i) (Array.get a2 i) with
              | None => None
              | Some (m, f) => go (Int.add i 1) (m :: acc) (Bool.or filled f)
              end in
          match go 0 [] false with
          | None => None
          | Some (args, filled) =>
              Some (make (App h1 (Array.of_list args)), filled)
          end
        else None
    | (_, _) => None
    end.

(* Closes a monotone equality goal [lhs ≈ rhs] whose two sides differ only
   where one of them is still a hole, as in [??? ≈ S ???]. That is the goal
   [IncRefEq] produces from an equality once both sides have reached incomplete
   code, and the common refinement it asks for is forced. It is the least common
   refinement of the two sides, which [meet_hole] reads off them.

   Plain [reflexivity] takes the sides of this shape that are already
   convertible, and the fill guard keeps this tactic off them. This one is an
   [icp_solve] branch, since a goal with no fill can be about complete code.
   [eqm_of_ref] closes these goals too and carries no fill guard, so it
   is not used here.

   Both sides are reduced with [all_flags] before merging, for the reasons
   spelled out on [hole_nf]. [cbn] would leave a non-recursive definition folded
   and [hnf] would not apply the hole propagation rewrite rules, so in either
   case the hole would stay hidden. The merged term goes in through
   [eqm_intro], which is the only way to place a witness now that [eq_mono] is
   sealed, and the two halves then go to [icp_close_gap]. [solve] makes it
   all-or-nothing. A half that does not close rolls the whole tactic back, so a
   goal it cannot finish is left exactly as it was found. *)
Ltac2 icp_eq_mono0 () : unit :=
  lazy_match! goal with
  | [ |- ?lhs ≈ ?rhs ] =>
      let l := Std.eval_cbv all_flags lhs in
      let r := Std.eval_cbv all_flags rhs in
      match meet_hole l r with
      | None =>
          Control.zero (Tactic_failure (Some (Message.of_string
            "icp_eq_mono: the two sides have no common refinement")))
      | Some (w, filled) =>
          if Bool.neg filled
          then
            Control.zero (Tactic_failure (Some (Message.of_string
              "icp_eq_mono: the sides merge without filling a hole, so this is a reflexivity goal")))
          else
            (eapply (@eqm_intro _ _ $w);
             Control.enter (fun () => solve [ icp_close_gap () ]))
      end
  | [ |- _ ] =>
      Control.zero (Tactic_failure (Some (Message.of_string
        "icp_eq_mono: goal is not _ ≈ _")))
  end.

(* The user-facing notation adds the introductions. After [icp_reform] the
   goal is still behind the binders of the reformulated statement, and possibly
   behind the completeness conjunction. *)
Ltac2 Notation "icp_eq_mono" :=
  retry_after
    "icp_eq_mono: no [_ ≈ _] goal whose sides merge through a hole, even after introductions"
    (fun () => icp_intro_step None)
    icp_eq_mono0.


(* ================================================================== *)
(* 5. Composite tactics                                               *)
(* ================================================================== *)

(* Tactics that are a composition of the groups above and introduce no new
   machinery of their own. *)

(* ------------------------------------------------------------------ *)
(* icp_solve                                                           *)
(* ------------------------------------------------------------------ *)

(* Closes an uninteresting incompleteness goal in one of four shapes:
     - conclusion form  [lhs ≈ rhs] whose two sides differ only in their holes,
       via [icp_eq_mono0];
     - conclusion form  [_ ⊑ TODO _]   via [icp_hole_refinement0];
     - premise form (an absurd equality [TODO = c], or a plain constructor
       clash) via [icp_discriminate0];
     - premise form again, but carried by a contradictory completeness
       hypothesis rather than by an equality, via [icp_absurd_complete0].
   [try] keeps it silent, and [retry_after]'s rollback keeps a goal it cannot
   close untouched, so it composes after [induction]/[intros] and leaves the
   interesting branches open.

   Plain [reflexivity] on a [≈] goal is deliberately not among them, and
   [icp_eq_mono0] carries the fill guard that keeps the two apart.
   Both close a [≈] goal, but reflexivity's sides are convertible, so its goals
   are trivial whatever the state of the code, and closing them here would break
   the rule that [icp_solve] never closes a goal about complete code.

   None of the four branches introduces anything. The single [retry_after]
   wrapping the [first] owns all the introduction, which is what lets
   [icp_solve] reach goals none of them can see on their own, and what makes the
   shallowest proof win instead of one branch exhausting all the intros before
   the next is tried. The step is [icp_intro_step], not [plain_intro_step],
   because the completeness hypothesis [icp_absurd_complete0] needs is buried
   inside the conjunction [icp_reform] leaves in the premise.

   This is a development-only tactic. Once a development is complete the
   [IncRocq.Tactics] import is dropped and proofs revert to standard tactics. *)
Ltac2 Notation "icp_solve" :=
  try (retry_after
         "icp_solve: no incompleteness goal, even after introductions"
         (fun () => icp_intro_step None)
         (fun () => first [ icp_eq_mono0 ()
                          | icp_hole_refinement0 ()
                          | icp_discriminate0 None
                          | icp_absurd_complete0 () ])).


(* ------------------------------------------------------------------ *)
(* icp_reform                                                          *)
(* ------------------------------------------------------------------ *)

(* Reformulates the goal with [icp_reform0], then runs [icp_solve] on the
   result. Reformulating a statement about code that is still entirely a hole
   leaves a goal that is uninteresting for that very reason, so the common case
   is that the reformulation is the whole proof and nothing is left to say.
   [icp_solve] is silent and rolls back what it cannot close, so a
   reformulation that does leave real work behind is unaffected. *)
Ltac2 Notation "icp_reform" x(reference) :=
  icp_reform0 (Env.instantiate x); icp_solve.


(* ------------------------------------------------------------------ *)
(* icp_apply                                                           *)
(* ------------------------------------------------------------------ *)

(* Steps through [h] and closes the whole residual gap with [icp_close_gap].
   This is the incremental drop-in for [apply h] in the recursive cases. Where
   the complete proof closes the branch with [apply IHn], the incremental proof
   closes it with [icp_apply IHn].

   It dispatches on the goal shape, as [icp_f_equal] does: a [⊑] goal takes the
   transitive step through [icp_etrans], and a [≈] goal goes through
   [eqm_weaken], which transports [h] along the refinement on both sides. The
   residual goals are [⊑] gaps in both cases, so the cleanup is the same. Any
   other goal, and a [≈] goal whose [h] is an implication rather than a bare
   monotone equality, goes to [icp_apply_generic], which is [apply h] plus
   the completeness obligations reformulation left behind.

   The leading constructor peel (e.g. [icp_f_equal] on [S _ ≈ S _] so the sides
   match [h]) stays a separate step by design, which is what makes the proof
   read like the complete one: [icp_f_equal. icp_apply IHn.] against
   [f_equal. apply IHn.] *)
(* Applies [h] on a goal that is neither a refinement nor an incremental
   equality, opening the antitone-equalities reformulation left on [h]'s premises.
   Each subgoal is reduced with [icp_reform]'s own flags first, so a premise
   arriving folded as [ir_anti P a] presents its [≈̇]; [eq_anti_intro_goal_opt]
   then sends the completeness half to the [icp] database and leaves the
   equation open. The subgoals are swept back to front for index stability.

   A goal that is itself an antitone-equality is opened the same way before [h] is
   applied, so [≈̇] is handled in both positions. When neither the goal nor [h]'s
   premises carry one this is exactly [apply h]. Which of the two it is depends
   on the [IncRef] instance that fired, which is not something a proof script
   should have to know. *)
Ltac2 icp_apply_generic (h : constr) : unit :=
  eq_anti_intro_goal_opt ();
  Std.apply true false [fun () => (h, Std.NoBindings)] None;
  let rec sweep (i : int) : unit :=
    if Int.le i 0 then ()
    else
      (Control.focus i i (fun () =>
         Std.cbn (reform_flags ()) (concl_clause ());
         eq_anti_intro_goal_opt ());
       sweep (Int.sub i 1))
  in
  sweep (Control.numgoals ()).

Ltac2 icp_apply0 (h : constr) : unit :=
  lazy_match! goal with
  | [ |- _ ⊑ _ ] => icp_etrans0 h; Control.enter (fun () => icp_close_gap ())
  | [ |- _ ≈ _ ] =>
      Control.plus
        (fun () =>
           eapply (eqm_weaken $h); Control.enter (fun () => icp_close_gap ()))
        (fun _ => icp_apply_generic h)
  | [ |- _ ] => icp_apply_generic h
  end.

Ltac2 Notation "icp_apply" h(constr) := icp_apply0 h.


(* ------------------------------------------------------------------ *)
(* icp_induction                                                       *)
(* ------------------------------------------------------------------ *)

(* Runs the standard [induction], then [icp_solve] on every resulting branch to
   discharge the ones made trivial by incompleteness. *)
Ltac2 Notation "icp_induction" arg(destruction_arg) :=
  Std.induction false
    [{ Std.indcl_arg := arg; Std.indcl_eqn := None;
        Std.indcl_as := None; Std.indcl_in := None }] None;
  icp_solve.


(* ------------------------------------------------------------------ *)
(* icp_destruct                                                        *)
(* ------------------------------------------------------------------ *)

(* Runs the standard [destruct], then [icp_solve] on every resulting branch to
   discharge the ones made trivial by incompleteness. *)
Ltac2 Notation "icp_destruct" arg(destruction_arg) :=
  Std.destruct false
    [{ Std.indcl_arg := arg; Std.indcl_eqn := None;
        Std.indcl_as := None; Std.indcl_in := None }] None;
  icp_solve.


(* ================================================================== *)
(* 6. Proofs of generated instances                                   *)
(* ================================================================== *)

(* The tactics that prove the lemmas [gen_refinable] and
   [gen_complete_minimal] declare through [tmLemmaU], which names them. Their proofs must leave no quality
   unconstrained, since a generated lemma has a fixed universe context. *)

(* Abstracts [l] in the goal [G l] as [w], with the equation [w = l] in the
   goal's own quality. [remember] would leave the quality of the equation
   unconstrained. *)
#[universes(polymorphic)]
Definition remember_eq@{a s; u v w} (A : Type@{a;u}) (l : A) (G : A -> Type@{s;v})
    (H : forall w, @eq@{a s; u w} A w l -> G w) : G l :=
  H l eq_refl.

(* Proves [refinement_T_refl], stated as
     forall A.. R.., (forall a, Ri a a) -> .. -> forall x, refinement_T A.. R.. x x
   by [icp_catch] on [x]. Each case is the constructor of the same name, with
   the premises given by the hypotheses on the [Ri] and the induction
   hypotheses. *)
Ltac gen_refinement_refl :=
  intros until x;
  ltac2:(icp_catch x);
  intros; constructor; solve [auto].

(* Proves [refinement_T_trans], stated as
     forall A.. R.., (forall a1 a2 a3, Ri a1 a2 -> Ri a2 a3 -> Ri a1 a3) -> .. ->
     forall x y z, refinement_T .. x y -> refinement_T .. y z -> refinement_T .. x z
   by induction on the first derivation and case analysis on the second. The
   middle value of the second derivation is abstracted with [remember_eq], and
   the equation then either is refuted by [icp_discriminate] or gives the
   equations between the fields through [icp_injection]. An Ltac2 step after
   [;] runs once over all the goals, so each one is wrapped in
   [Control.enter] to run on each goal. *)
Ltac gen_refinement_trans :=
  intros until y; intros z H H';
  revert z H'; induction H; intros z H';
  lazymatch type of H' with
  | ?Rel ?l ?r =>
      lazymatch goal with
      | |- ?concl =>
          revert H';
          refine (remember_eq _ l (fun w => Rel w r -> concl) _);
          intros w Hw H'
      end
  end;
  destruct H';
  try ltac2:(Control.enter (fun () => icp_discriminate &Hw));
  try solve [constructor];
  ltac2:(Control.enter (fun () => icp_injection &Hw)); subst; constructor; solve [eauto].

(* Proves [complete_T_minimal], stated as
     forall A.. P.. R.., (forall a, Pi a -> forall a', Ri a' a -> a' = a) -> .. ->
     forall x, complete_T A.. P.. x -> forall x', refinement_T A.. R.. x' x -> x' = x
   by induction on the completeness derivation and case analysis on the
   refinement. Its right side is abstracted with [remember_eq], and the
   equation either is refuted by [icp_discriminate] or gives the equations
   between the fields through [icp_injection]. Each field of [x'] is then
   equal to the field of [x], by the hypotheses on the [Pi] and [Ri] or by the
   induction hypothesis. Only premises between two variables are used, so that
   the loop ends. *)
Ltac gen_complete_minimality :=
  intros until x; intros Hx; induction Hx; intros x' Href;
  lazymatch type of Href with
  | ?Rel ?l ?r =>
      revert Href;
      refine (remember_eq _ r (fun w => Rel l w -> @eq _ l w) _);
      intros w Hw Href
  end;
  destruct Href;
  try ltac2:(Control.enter (fun () => icp_discriminate &Hw));
  ltac2:(Control.enter (fun () => icp_injection &Hw)); subst;
  repeat match goal with
         | Hr : ?R ?a' ?a |- _ =>
             is_var a'; is_var a;
             let E := fresh "E" in
             assert (E : a' = a) by (solve [eauto]); clear Hr; subst
         end;
  reflexivity.

(* Proves [complete_T_hole], stated as
     forall A.. P.., complete_T A.. P.. (TODO (T A..)) -> False
   by case analysis on the completeness derivation, with the hole abstracted
   by [remember_eq]. Each case equates a constructor with the hole, which
   [icp_discriminate] refutes. [icp_inversion] would leave the quality of its
   equations unconstrained. *)
Ltac gen_complete_hole :=
  intros until 1;
  lazymatch goal with
  | H : ?Pred ?t |- ?G =>
      revert H;
      refine (remember_eq _ t (fun w => Pred w -> G) _);
      intros w Hw H; destruct H;
      ltac2:(Control.enter (fun () => icp_discriminate &Hw))
  end.
