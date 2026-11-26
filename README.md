# IncRocq

IncRocq is a Rocq framework for incremental certified programming. With it, you
can state and prove properties of programs while parts of those programs are
still incomplete.

## Setup

### Requirements

IncRocq runs on a fork of Rocq that adds the `Inc` sort, together with matching
forks of MetaRocq and Equations. These forks and the standard library are
pinned as Git submodules under `deps/`:

| Submodule | Source |
| --- | --- |
| `deps/coq` | [TDiazT/coq](https://github.com/TDiazT/coq), branch `icp` |
| `deps/metarocq` | [TDiazT/metarocq](https://github.com/TDiazT/metarocq), branch `icp` |
| `deps/Coq-Equations` | [TDiazT/Coq-Equations](https://github.com/TDiazT/Coq-Equations), branch `icp` |
| `deps/stdlib` | [rocq-prover/stdlib](https://github.com/rocq-prover/stdlib) |

You also need [opam](https://opam.ocaml.org/). `scripts/setup.sh` creates an
opam switch called `rocq-icp` with OCaml 4.14.2.

### Building

To create the switch, fetch the submodules, and install their dependencies:

```bash
./scripts/setup.sh
```

If a `rocq-icp` switch already exists, the script asks whether to remove and
recreate it.

To build the toolchain, install it into the switch, and then build IncRocq:

```bash
./scripts/build.sh
```

To rebuild only IncRocq after the toolchain is installed, activate the switch
and run `make`:

```bash
eval "$(opam env --switch=rocq-icp)"
make
```

To build the examples:

```bash
make examples
```

## How it works

IncRocq adds holes to stand for incomplete code, which compute like exceptions, and
provides the reasoning support to prove things about incomplete code.
It is built from recent Rocq features, namely user-defined sorts, sort
polymorphism, and rewrite rules, together with MetaRocq and Ltac2.
The summary of these pieces is:

**Holes that compute.** A hole, written `□` or `???`, is the constant `TODO`. It
is declared as a `Symbol` with rewrite rules, so it propagates like an
exception. For instance, a `match` on a hole reduces to a hole (see the [example](#example) below).

**A sort for incompleteness.** Holes alone would make the logic inconsistent,
since a hole that inhabited every type would make `False` provable. IncRocq
declares a new sort, `Inc`, and only types in `Inc` have holes, so `Prop` stays
consistent.
The information on the sort is inferred and tracked by Rocq, which allows checking whether a term is incomplete or not based on the sort.

**Incremental reformulation.** Specifications are generally not compatible with incomplete definitions.
For instance, an equation that the complete program satisfies is usually false while part of the program is still incomplete.
Instead, with IncRocq, you prove a reformulated specification that is trivially true for incomplete code,
but still fails if a bug is introduced, and which implies the original specification once
the program is complete. This way, you have the guarantee that what you are proving will (plausibly)
lead to your desired specification, and that actual problems are detected by the system.
In addition, any code increment is detected by the proof, which is no longer trivial, so proving the new cases is
synchronized with their increments.

**Incremental proof scripting.** IncRocq also provides tactics to carry out the
reformulation inside the proof script. `icp_reform` replaces the goal with its
reformulation, so the lemma keeps its original statement throughout development.
Even though the reformulation implies the original specification, the proof
script written against it does not necessarily resemble the one for the complete
program. Ideally, each version of the script extends the previous one with the
cases that the new code increment adds, and the final script carries no trace of
the incremental process. To get close to this, IncRocq includes a set of
tactics, prefixed with `icp_`, that stand in for the standard ones and handle
the steps that are specific to incompleteness.

**Generated definitions.** Supporting holes requires some boilerplate for every
inductive type. IncRocq provides MetaRocq tools that generate it, with a function
`gen_icp_defs` as the single entry point.

## Example

`add_v1` below leaves its `S` case as a hole. It still computes, and the hole
propagates through a `match` on its result. You can already prove that
`add_v1 n (S O)` is `S n`, starting the proof with `icp_reform`:

```rocq
From IncRocq Require Import IncRocq.

Set Universe Polymorphism.
Unset Collapse Sorts ToType.

Inductive nat : Type := O | S : nat -> nat.
MetaRocq Run (gen_icp_defs "nat").

Definition add_v1 (n m : nat) : nat :=
  match n with
  | O => m
  | S p => □
  end.

Compute add_v1 O (S O).                                   (* = S O *)
Compute add_v1 (S O) O.                                   (* = □ *)
Compute match add_v1 (S O) O with O => O | S p => p end.  (* = □ *)

Lemma add_1_v1 : forall (n : nat), add_v1 n (S O) = S n.
Proof.
  icp_reform add_v1.
  intros n. icp_induction n.
  - reflexivity.
Qed.
```

The full development, with the other versions of `add`, is in
[`examples/comp/NatAuto.v`](examples/comp/NatAuto.v).

## Layout

| Path | Logical name | Contents |
| --- | --- | --- |
| `theories/` | `IncRocq` | The framework. `IncRocq.v` is the entry point. |
| `theories/gen/` | `IncRocq.gen` | MetaRocq generators for catch symbols, completeness predicates, refinement relations, and their instances. `gen_icp_defs` runs all of them. |
| `Prelude/` | `Prelude` | Standard-library modules adapted to sort polymorphism. |
| `examples/comp/` | `IncRocq.examples.comp` | Running example: natural numbers. |
| `examples/stlc/` | `IncRocq.examples.stlc` | Case study: a simply typed lambda calculus. |
| `examples/library/` | `IncRocq.examples.library` | Tests for the generator and the tactics. |

Client files need one import, `From IncRocq Require Import IncRocq.`, which
loads the framework modules in the order they must be loaded. `IncRocq` also
exports Prelude's `Logic`. Files that need other Prelude modules (`Datatypes`,
`String`, or `LargeElim`) import them directly.
