# How the Lean proof was checked

## The statements

The main formal results, in [`formal/EHP6/Final.lean`](formal/EHP6/Final.lean), are

```lean
theorem EHP6.erdos_hajnal_P6_of_imported (hR : RodlCoP6) (hP : NssPath6) (hE : EhP5) (hC : NssComb) :
    EHforP6
theorem EHP6.erdos_hajnal_P6_of_cited (hR : RodlCoP6) (hE : EhP5) (hC : NssComb) : EHforP6
```

The first says that the four imported theorems, stated as propositions in
[`formal/EHP6/Imported.lean`](formal/EHP6/Imported.lean), imply the Erdős–Hajnal property for P6. The
second of them, NSS V statement 3.1, is proved in [`formal/EHP6/NSSPath.lean`](formal/EHP6/NSSPath.lean)
(`EHP6.nss_path6_proof`), so the second theorem needs only the other three. Both statements use only the
definitions in [`formal/EHP6/Defs.lean`](formal/EHP6/Defs.lean) and `Imported.lean`, and both proofs use
no axioms beyond Lean's standard `propext`, `Classical.choice` and `Quot.sound`. The unconditional
theorem `EHP6.erdos_hajnal_P6 : EHforP6` applies the second to the three axioms of
[`formal/EHP6/Axioms.lean`](formal/EHP6/Axioms.lean).

## The checks

All checks were run on Lean `v4.34.1` with Mathlib `v4.34.1`. They run again in GitHub Actions on every
push ([`.github/workflows/lean.yml`](.github/workflows/lean.yml)), with every tool pinned to the commit
given below, and the outputs are kept as build artifacts.

**1. Build and axiom audit.** `lake build` elaborates every file and sends every declaration to Lean's
kernel. `Audit.lean` then prints the axioms used by the three main theorems and by 32 intermediate
results. All of them use only the three standard axioms, except `erdos_hajnal_P6`, which also uses the
three axioms of `Axioms.lean`. CI checks this for every listed result, and also fails if any proof file
contains `sorry` or `admit`.

**2. Fresh replay.** `leanchecker --fresh EHP6.Final` (shipped with Lean, by Kim Morrison and Sebastian
Ullrich) takes every declaration that the main file depends on, Mathlib included, and checks it again in a
kernel that starts from an empty environment. Nothing is taken on trust from compiled `.olean` files. It
passes in about 11 minutes on one core.

**3. Comparator.** [comparator](https://github.com/leanprover/comparator) (Lean FRO, tag `v4.34.0`,
commit `d03acab`) builds [`formal/Challenge.lean`](formal/Challenge.lean), which states both main
theorems (`erdos_hajnal_P6_of_imported` and `erdos_hajnal_P6_of_cited`) with `sorry` and imports only
`Defs.lean` and `Imported.lean`. It then builds the project, exports both
with [lean4export](https://github.com/leanprover/lean4export) (tag `v4.34.0`, commit `076e8e5`), and
checks that the project proves exactly those statements, that the proofs use only the three standard
axioms, and that Lean's kernel accepts the exported proofs. Builds and exports run inside the
[landrun](https://github.com/Zouuup/landrun) sandbox (commit `811cfff`).

**4. A second kernel.** Comparator also gives the exported proofs to
[nanoda](https://github.com/ammkrn/nanoda_lib) (commit `3a24072`), a type checker for Lean written in Rust
that shares no code with Lean's kernel. It accepts them. Comparator's output ends with

```
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

**Negative controls.** To make sure comparator rejects what it should, it was also run on two wrong
challenges:

- `erdos_hajnal_P6_of_cited` without the hypothesis `hE : EhP5`, rejected with "Challenge and solution
  theorem statement do not match";
- the unconditional `EHP6.erdos_hajnal_P6`, with only the three standard axioms permitted, rejected with
  "Illegal axiom detected: 'EHP6.rodl_coP6'".

## Why Lean 4.34.1

The project was written for Lean 4.15.0 and later moved to 4.34.1, the current release. Lean versions up
to 4.33.0 have known kernel soundness bugs (see the list at
[lean4-soundness](https://github.com/madvorak/lean4-soundness) and the release notes of
[Lean 4.33.0](https://lean-lang.org/doc/reference/latest/releases/v4.33.0/) and
[Lean 4.34.0](https://lean-lang.org/doc/reference/latest/releases/v4.34.0/)). Exploiting them requires
deliberately constructed input, such as custom metaprograms or crafted declarations. This project has
none: no `unsafe` code, no `native_decide`, `implemented_by` or `extern`, and no metaprogramming. The
move still means that no check relies on a Lean version with a known kernel bug. It changed proof scripts
only (renamed Mathlib lemmas and a few tactic adjustments), and no statement.

According to the
[postmortem of the 2026 kernel bug hunt](https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/),
nanoda rejected the crafted proofs of `False` for every bug found except the two in `isProp` (#14807 and
#14843), and Lean's kernel has fixed all of them since 4.33.1. A false proof would have to fool both
kernels to pass checks 3 and 4.

## What only a human can check

- That the propositions `RodlCoP6`, `EhP5` and `NssComb` in `Imported.lean` say what the cited theorems
  say. They are quoted next to their sources in the [README](README.md) and in Section 0 of the
  [paper](paper/erdos-hajnal-p6.pdf). (`NssPath6` is proved, so it needs no check.)
- That the definitions in `Defs.lean` (P6-free graphs, cliques, stable sets, `EHforP6`) are the intended
  ones.

Both files are short. [`formal/DefsCheck.lean`](formal/DefsCheck.lean) makes the second check easier: it
proves that `P6`, `Free`, `IsCliqueF`, `IsStableF` and `Sparse` agree with Mathlib's `pathGraph 6`,
induced embeddings (`H ↪g G`), `IsClique`, `IsIndepSet` and degrees in `G.induce S`, and derives the main
theorem in a form that uses Mathlib's definitions only. CI runs it and checks that this form, too, uses
only the three standard axioms. The three results still assumed come from refereed papers; the fourth,
from the preprint [NSS V], is proved.

## Reproducing the checks

Install [elan](https://github.com/leanprover/elan), then in `formal/`:

```
lake exe cache get && lake build
lake env lean Audit.lean                  # check 1
lake env leanchecker --fresh EHP6.Final   # check 2
lake env lean DefsCheck.lean              # definitions against Mathlib
```

For checks 3 and 4 you also need Go and Rust. Build landrun, nanoda, comparator and lean4export at the
commits above (the workflow file has the exact commands), then run in `formal/`:

```
export COMPARATOR_LANDRUN=/path/to/landrun
export COMPARATOR_LEAN4EXPORT=/path/to/lean4export
export COMPARATOR_NANODA=/path/to/nanoda_bin
lake env /path/to/comparator comparator.json
```

Comparator calls landrun with `--best-effort`. On Linux kernels with an older Landlock version the sandbox
is therefore only partial. The sandbox protects the machine from a malicious proof; it does not change
which proofs the kernels accept.
