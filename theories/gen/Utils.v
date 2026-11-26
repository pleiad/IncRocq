From MetaRocq.Utils Require Export utils.
From MetaRocq.Template Require Import All.
From Stdlib Require Init.

(* The library that declares TODO and Inc.  A MetaRocq dirpath lists its
   components innermost first. *)
Definition inc_lib : dirpath := ["Base"; "IncRocq"].

(* Fully-qualified name used to find `TODO`, avoiding ambiguity with any
   homonym in MetaRocq.Utils.monad_utils. *)
Definition inc_todo_qualid : qualid := string_of_dirpath inc_lib ^ ".TODO".
Definition inc_todo_kn : kername := (MPfile inc_lib, "TODO").

(* The full name of [id] in the module of the inductive [kn], such as
   "Prelude.String.String" for a constructor of Prelude's string. The rewrite
   rules are declared from text, where a short name may resolve to a homonym,
   such as MetaRocq's own [string], which IncRocq exports. *)
Definition qualify_in (kn : kername) (id : ident) : string :=
  string_of_modpath (fst kn) ^ "." ^ id.

Definition inc_qvar : QVar.t :=
  QVar.Global {| QGlobal.library := inc_lib; QGlobal.id := "Inc" |}.
Definition inc_quality : Quality.t := Quality.qVar inc_qvar.

Fixpoint seq_nat (start len : nat) : list nat :=
  match len with 0 => [] | S n => start :: seq_nat (S start) n end.

(* [l] without its element at position [n]. *)
Fixpoint list_remove_nth {A} (n : nat) (l : list A) : list A :=
  match l, n with
  | [],     _ => []
  | _ :: t, 0 => t
  | h :: t, S k => h :: list_remove_nth k t
  end.

(* Space-separated join with leading space: ["a";"b"] → " a b" *)
Definition join_with_space (xs : list string) : string :=
  fold_left (fun acc x => acc ^ " " ^ x) xs "".

(* Join list elements with separator, no leading/trailing sep *)
Fixpoint string_join (sep : string) (xs : list string) : string :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: rest => x ^ sep ^ string_join sep rest
  end.

Fixpoint skip_n_prods (n : nat) (ty : term) : option term :=
  match n with
  | 0   => Some ty
  | S k =>
    match ty with
    | tProd _ _ codom => skip_n_prods k codom
    | _               => None
    end
  end.

(* Gets the codomain under every binder of [ty].  For an inductive's type,
   that is its own sort, under both the parameters and the indices. *)
Fixpoint final_codomain (ty : term) : term :=
  match ty with
  | tProd _ _ codom => final_codomain codom
  | _ => ty
  end.

(* Gets the index of the quality variable of the inductive's own sort.
   Falls back to 0 when that sort is not a quality variable. *)
Definition get_ind_sort_quality_idx (ind_type : term) : nat :=
  match final_codomain ind_type with
  | tSort (Sort.sQVar (QVar.Var i) _) => i
  | _ => 0
  end.

(* Gets the universe of the inductive's own sort, or None when that sort is
   not a quality variable.  A max universe, as in
   prod A B : Type@{max(uA,uB)}, means the catch symbol needs a dedicated
   TODO level. *)
Definition get_ind_sort_universe (ind_type : term) : option Universe.t :=
  match final_codomain ind_type with
  | tSort (Sort.sQVar _ lvl) => Some lvl
  | _ => None
  end.
