From IncRocq Require Import IncRocq.

Set Universe Polymorphism.

Inductive unit@{s;u} : Type@{s;u} := tt.

About unit_poly_rec.

MetaRocq Run (gen_icp_defs "unit").
About unit_catch.

Eval cbn in (unit_catch (fun _ => bool) true false tt).
Eval cbn in (unit_catch (fun _ => bool) true false (TODO unit)).
Eval cbn in (unit_catch (fun _ => Prop) True False (TODO unit)).

Inductive bool@{s;u} : Type@{s;u} := true | false.

About bool_poly_rec.

MetaRocq Run (gen_icp_defs "bool").
About bool_catch.

Inductive nat@{s;u} : Type@{s;u} := O | S : nat -> nat.
About nat_poly_rec.

MetaRocq Run (gen_icp_defs "nat").
About nat_catch.

Eval cbn in (nat_catch (fun _ => nat) (S O) (fun _ _ => S (S O)) (S (S (S O))) O).
Eval cbn in (nat_catch (fun _ => nat) (S O) (fun _ _ => S (S O)) (S (S (S O))) (S O)).
Eval cbn in (nat_catch (fun _ => nat) (S O) (fun _ _ => S (S O)) (S (S (S O))) (TODO nat)).

(** Match-hole reduction tests *)
Eval cbn in (match TODO unit with tt => true@{Inc;Set} end).
Eval cbn in (match TODO bool with true => (S O) | false => O@{Inc;Set} end).
Eval cbn in (match TODO nat with O => true | S _ => false@{Inc;Set} end).

(* ------------------------------------------------------------------ *)
(* Parameterized inductives                                             *)
(* ------------------------------------------------------------------ *)

(* option — 1 param, 2 non-recursive constructors *)
Inductive option@{s;u} (A : Type@{s;u}) : Type@{s;u} :=
| None : option A
| Some : A -> option A.

About option_poly_rec.

Arguments None {A}.
Arguments Some {A}.

MetaRocq Run (gen_icp_defs "option").
About option_catch.

Eval cbn in (option_catch nat (fun _ => nat) O (fun _ => S O) (S (S O)) None).
Eval cbn in (option_catch nat (fun _ => nat) O (fun _ => S O) (S (S O)) (Some O)).
Eval cbn in (option_catch nat (fun _ => nat) O (fun _ => S O) (S (S O)) (TODO (option nat))).

Eval cbn in (match TODO (option nat) with None => true@{Inc;Set} | Some _ => false end).

(* list — 1 param, nil + recursive cons constructor *)
Inductive list@{s;u} (A : Type@{s;u}) : Type@{s;u} :=
| nil  : list A
| cons : A -> list A -> list A.

About list_poly_rec.

Arguments nil {A}.
Arguments cons {A}.

MetaRocq Run (gen_icp_defs "list").
About list_catch.

Eval cbn in (list_catch nat (fun _ => nat) O (fun _ _ n => S n) (S (S O)) nil).
Eval cbn in (list_catch nat (fun _ => nat) O (fun _ _ n => S n) (S (S O)) (cons O nil)).
Eval cbn in (list_catch nat (fun _ => nat) O (fun _ _ n => S n) (S (S O)) (TODO (list nat))).

Eval cbn in (match TODO (list nat) with nil => true@{Inc;Set} | cons _ _ => false end).

(* ------------------------------------------------------------------ *)
(* Separate-sort inductives (explicit distinct sort vars for param/ind) *)
(* ------------------------------------------------------------------ *)

(* option with two explicit sort variables: sA for the parameter, sI for the inductive *)
Inductive option2@{sA sI; uA uI} (A : Type@{sA;uA}) : Type@{sI;uI} :=
| None2 : option2 A
| Some2 : A -> option2 A.

Set Printing Universes.
About option2_poly_rec.

Arguments None2 {A}.
Arguments Some2 {A}.

MetaRocq Run (gen_icp_defs "option2").
About option2_catch.
(* A's sort should be sA (not Inc), only the inductive sort sI is replaced by Inc *)

Eval cbn in (option2_catch nat (fun _ => nat) O (fun _ => S O) (S (S O)) None2).
Eval cbn in (option2_catch nat (fun _ => nat) O (fun _ => S O) (S (S O)) (Some2 O)).
Eval cbn in (option2_catch nat (fun _ => nat) O (fun _ => S O) (S (S O)) (TODO (option2 nat))).

Eval cbn in (match TODO (option nat) with None => true@{Inc;Set} | Some _ => false end).

(* ------------------------------------------------------------------ *)
(* prod — 2 params, natural definition (no explicit universe annots). *)
(* With Unset Collapse Sorts ToType, Rocq infers separate quality     *)
(* vars and prod_poly_rec@{α α0 α1 α2; u u0 u1} is generated.        *)
(* Sort of prod A B = max(uA, uB); generator must add fresh u_todo.   *)
(* ------------------------------------------------------------------ *)

#[universes(collapse_sort_variables=no)]
Inductive prod (A B : Type) : Type :=
| pair : A -> B -> prod A B.

MetaRocq Run (gen_icp_defs "prod").

Eval cbn in (prod_catch nat nat (fun _ => nat) (fun _ _ => S O) (S (S O))
               (@pair nat nat O O)).
Eval cbn in (prod_catch nat nat (fun _ => nat) (fun _ _ => S O) (S (S O))
               (TODO (prod nat nat))).
Eval cbn in (match TODO (prod nat nat) with pair _ _ => true@{Inc;Set} end).

(* ------------------------------------------------------------------ *)
(* optm — 1 param, sort max(Set, u)  (the shape of Prelude's option).  *)
(* With collapse off, optm@{sA sI; u} : Type@{sA;u} -> Type@{sI; max(Set,u)}. *)
(* Because the sort is max(Set,u) — an algebraic max containing the     *)
(* global Set — the hole rewrite rules need `TODO` annotated with a     *)
(* dedicated level; they register with a benign "breaks subject         *)
(* reduction" warning (TODO's universe is irrelevant to the theory).    *)
(* Regression test for that case.                                       *)
(* ------------------------------------------------------------------ *)
#[universes(collapse_sort_variables=no)]
Inductive optm (A : Type) : Type :=
| Nonem : optm A
| Somem : A -> optm A.

Arguments Nonem {A}.
Arguments Somem {A}.

MetaRocq Run (gen_icp_defs "optm").
About optm_catch.

Eval cbn in (optm_catch nat (fun _ => nat) O (fun a => a) (S (S O)) Nonem).
Eval cbn in (optm_catch nat (fun _ => nat) O (fun a => a) (S (S O)) (Somem (S O))).
Eval cbn in (optm_catch nat (fun _ => nat) O (fun a => a) (S (S O)) (TODO (optm nat))).
Eval cbn in (match TODO (optm nat) with Nonem => true@{Inc;Set} | Somem _ => false end).

(* ------------------------------------------------------------------ *)
(* Higher-order recursive arguments                                     *)
(* ------------------------------------------------------------------ *)

(* A recursive argument may sit under binders, as in [nat -> itree].
   Its induction hypothesis is then a function, so the catch rule must
   rebuild it as [fun x0 => itree_catch … (?a0 x0)]. A rule that leaves the
   hypothesis out still registers, with only a subject-reduction warning, so
   these tests turn that warning into an error. *)
Set Warnings "+rewrite-rules-break-SR".

Inductive itree@{s;u} : Type@{s;u} :=
| ileaf : itree
| inode : (nat@{s;u} -> itree) -> itree.

MetaRocq Run (gen_icp_defs "itree").

(* Follows child O at every node, so it counts the nodes on that path. *)
Eval cbn in (itree_catch (fun _ => nat) O (fun _ ih => S (ih O)) (S (S (S O)))
               (inode (fun _ => inode (fun _ => ileaf)))).
Eval cbn in (itree_catch (fun _ => nat) O (fun _ ih => S (ih O)) (S (S (S O)))
               (inode (fun _ => TODO itree))).
Eval cbn in (match TODO itree with ileaf => true@{Inc;Set} | inode _ => false end).

(* Two binders, a parameter, and a first-order recursive argument next to a
   higher-order one in the same constructor. *)
Inductive htree@{s;u} (A : Type@{s;u}) : Type@{s;u} :=
| hleaf : A -> htree A
| hnode : htree A -> (nat@{s;u} -> bool@{s;u} -> htree A) -> htree A.

Arguments hleaf {A}.
Arguments hnode {A}.

MetaRocq Run (gen_icp_defs "htree").

(* The first reads the first-order hypothesis, giving S O. The second reads
   the higher-order one at (O, true), giving S (S O).  The third reads it
   where that child is a hole, giving the hole case's O. *)
Eval cbn in (htree_catch nat (fun _ => nat) (fun a => a)
               (fun _ l _ _ => l) O
               (hnode (hleaf (S O)) (fun _ _ => hleaf (S (S O))))).
Eval cbn in (htree_catch nat (fun _ => nat) (fun a => a)
               (fun _ _ _ r => r O true) O
               (hnode (hleaf (S O)) (fun _ _ => hleaf (S (S O))))).
Eval cbn in (htree_catch nat (fun _ => nat) (fun a => a)
               (fun _ _ _ r => r O true) O
               (hnode (hleaf (S O)) (fun _ _ => TODO (htree nat)))).

Set Warnings "rewrite-rules-break-SR".

(* ------------------------------------------------------------------ *)
(* Inductive families                                                   *)
(* ------------------------------------------------------------------ *)

(* The hole case takes the indices, [Hhole : forall n, P n (TODO (vec A n))],
   and the hole rule passes them to it. *)
Set Warnings "+rewrite-rules-break-SR".

(* A recursive argument at a different index, and a non-variable index [S n]. *)
Inductive vec@{s;u} (A : Type@{s;u}) : nat@{s;u} -> Type@{s;u} :=
| vnil  : vec A O
| vcons : A -> forall n, vec A n -> vec A (S n).

Arguments vnil {A}.
Arguments vcons {A}.

MetaRocq Run (gen_icp_defs "vec").

(* The first counts the elements.  The other two count up to a hole and add
   the index that the hole case returns, S (S O) in the second and a hole in
   the third. *)
Eval cbn in (vec_catch nat (fun _ _ => nat) O (fun _ _ _ r => S r) (fun _ => O)
               _ (vcons O _ (vcons O _ vnil))).
Eval cbn in (vec_catch nat (fun _ _ => nat) O (fun _ _ _ r => S r) (fun n => n)
               _ (vcons O _ (TODO (vec nat (S (S O)))))).
Eval cbn in (vec_catch nat (fun _ _ => nat) O (fun _ _ _ r => S r) (fun n => n)
               _ (vcons O _ (TODO (vec nat (TODO nat))))).
Eval cbn in (match TODO (vec nat (S O)) in vec _ n return nat@{Inc;Set} with
             | vnil => O | vcons _ _ _ => S O end).
Eval cbn in (match TODO (vec nat (S O)) as v in vec _ n return vec nat n with
             | vnil => vnil | vcons a _ w => vcons a _ w end).

(* An index that a constructor ties to a parameter. *)
Inductive eqI@{s;u} (A : Type@{s;u}) (x : A) : A -> Type@{s;u} :=
| reflI : eqI A x x.

Arguments reflI {A x}.

MetaRocq Run (gen_icp_defs "eqI").

Eval cbn in (eqI_catch nat O (fun _ _ => bool) true (fun _ => false) O reflI).
Eval cbn in (eqI_catch nat O (fun _ _ => bool) true (fun _ => false) (S O)
               (TODO (eqI nat O (S O)))).
Eval cbn in (match TODO (eqI nat O (S O)) in eqI _ _ y return nat@{Inc;Set} with
             | reflI => O end).

(* A higher-order recursive argument whose index comes from a binder, as in
   the accessibility predicate. *)
Inductive acc@{s;u} (A : Type@{s;u}) (R : A -> A -> Type@{s;u}) : A -> Type@{s;u} :=
| acc_intro : forall x, (forall y, R y x -> acc A R y) -> acc A R x.

Arguments acc_intro {A R}.

MetaRocq Run (gen_icp_defs "acc").

(* The relation always holds, witnessed by [true].  Each node follows child
   O and adds one, and the hole case returns its index plus one, so both
   trees below give S (S O). *)
Eval cbn in (acc_catch nat (fun _ _ => bool) (fun _ _ => nat)
               (fun _ _ ih => S (ih O true)) (fun y => S y) (S O)
               (acc_intro (S O) (fun y _ => TODO (acc nat (fun _ _ => bool) y)))).
Eval cbn in (acc_catch nat (fun _ _ => bool) (fun _ _ => nat)
               (fun _ _ ih => S (ih O true)) (fun y => y) (S O)
               (acc_intro (S O) (fun y _ =>
                  acc_intro y (fun z _ => TODO (acc nat (fun _ _ => bool) z))))).

Set Warnings "rewrite-rules-break-SR".

(* ------------------------------------------------------------------ *)
(* Non-uniform parameters                                               *)
(* ------------------------------------------------------------------ *)

(* A parameter that changes in a recursive occurrence is non-uniform.  The
   eliminator quantifies over it after P, as it does over an index, so the
   catch symbol treats it as one, with [Hhole : forall A, P A (TODO (nlist A))].
   A match still treats it as a parameter. *)
Set Warnings "+rewrite-rules-break-SR".

Inductive nlist@{s;u} (A : Type@{s;u}) : Type@{s;u} :=
| nnil  : nlist A
| ncons : A -> nlist (prod A A) -> nlist A.

Arguments nnil {A}.
Arguments ncons {A}.

MetaRocq Run (gen_icp_defs "nlist").

(* The first counts the elements.  The second counts up to a hole and adds
   the three that the hole case returns. *)
Eval cbn in (nlist_catch (fun _ _ => nat) (fun _ => O) (fun _ _ _ r => S r)
               (fun _ => S (S (S O))) _ (ncons O (ncons (pair nat nat O O) nnil))).
Eval cbn in (nlist_catch (fun _ _ => nat) (fun _ => O) (fun _ _ _ r => S r)
               (fun _ => S (S (S O))) _ (ncons O (TODO (nlist (prod nat nat))))).
Eval cbn in (match TODO (nlist nat) with nnil => true@{Inc;Set} | ncons _ _ => false end).

(* A uniform parameter B, a non-uniform parameter A and an index together. *)
Inductive nvec@{s;u} (B A : Type@{s;u}) : nat@{s;u} -> Type@{s;u} :=
| nvnil  : nvec B A O
| nvcons : B -> A -> forall n, nvec B (prod A A) n -> nvec B A (S n).

Arguments nvnil {B A}.
Arguments nvcons {B A}.

MetaRocq Run (gen_icp_defs "nvec").

(* The hole case returns its index, so a hole of length S O after one
   element gives S (S O). *)
Eval cbn in (nvec_catch bool (fun _ _ _ => nat) (fun _ => O) (fun _ _ _ _ _ r => S r)
               (fun _ n => n) _ _ (nvcons true O _ (nvcons false (pair nat nat O O) _ nvnil))).
Eval cbn in (nvec_catch bool (fun _ _ _ => nat) (fun _ => O) (fun _ _ _ _ _ r => S r)
               (fun _ n => n) _ _ (nvcons true O _ (TODO (nvec bool (prod nat nat) (S O))))).
Eval cbn in (match TODO (nvec bool nat (S O)) in nvec _ _ n return nat@{Inc;Set} with
             | nvnil => O | nvcons _ _ _ _ => S O end).

Set Warnings "rewrite-rules-break-SR".

(* ------------------------------------------------------------------ *)
(* Families with other sort and universe shapes                         *)
(* ------------------------------------------------------------------ *)

(* An index in its own sort variable sN.  Only the family's sort sI becomes
   Inc, so the catch keeps the index at nat@{sN;u}. *)
Set Warnings "+rewrite-rules-break-SR".

Inductive vec2@{sI sN; u} (A : Type@{sI;u}) : nat@{sN;u} -> Type@{sI;u} :=
| v2nil  : vec2 A O
| v2cons : A -> forall n, vec2 A n -> vec2 A (S n).

Arguments v2nil {A}.
Arguments v2cons {A}.

MetaRocq Run (gen_icp_defs "vec2").

(* One element, then a hole whose case returns its index plus one. *)
Eval cbn in (vec2_catch nat (fun _ _ => nat) O (fun _ _ _ r => S r) (fun n => S n)
               _ (v2cons O _ (TODO (vec2 nat (S O))))).
Eval cbn in (match TODO (vec2 nat (S O)) in vec2 _ n return nat@{Inc;Set} with
             | v2nil => O | v2cons _ _ _ => S O end).

Set Warnings "rewrite-rules-break-SR".

(* With [collapse_sort_variables=no], Rocq gives these two families a sort
   of the form max(Set, …): max(Set,uA,uB,uN) for pvec, which has several universe
   levels, and max(Set,uA,uN) for vecm.  The catch then takes a dedicated
   TODO level, as for optm, and its rules register with the same benign
   subject-reduction warning described in build_hole_rule. *)
#[universes(collapse_sort_variables=no)]
Inductive pvec (A B : Type) : nat -> Type :=
| pvnil  : pvec A B O
| pvcons : A -> B -> forall n, pvec A B n -> pvec A B (S n).

Arguments pvnil {A B}.
Arguments pvcons {A B}.

MetaRocq Run (gen_icp_defs "pvec").

Eval cbn in (pvec_catch nat nat (fun _ _ => nat) O (fun _ _ _ _ r => S r) (fun n => S n)
               _ (pvcons O O _ (TODO (pvec nat nat (S O))))).
Eval cbn in (match TODO (pvec nat nat (S O)) in pvec _ _ n return nat@{Inc;Set} with
             | pvnil => O | pvcons _ _ _ _ => S O end).

#[universes(collapse_sort_variables=no)]
Inductive vecm (A : Type) : nat -> Type :=
| vmnil  : vecm A O
| vmcons : A -> forall n, vecm A n -> vecm A (S n).

Arguments vmnil {A}.
Arguments vmcons {A}.

MetaRocq Run (gen_icp_defs "vecm").

Eval cbn in (vecm_catch nat (fun _ _ => nat) O (fun _ _ _ r => S r) (fun n => S n)
               _ (vmcons O _ (TODO (vecm nat (S O))))).
Eval cbn in (match TODO (vecm nat (S O)) in vecm _ n return nat@{Inc;Set} with
             | vmnil => O | vmcons _ _ _ => S O end).


