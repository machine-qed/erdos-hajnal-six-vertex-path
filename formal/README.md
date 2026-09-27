# The Lean formalization

Lean `v4.34.1`, Mathlib `v4.34.1` (commit `d13f23b723b8a846827a245b89c10fc7d3f11612`). No `sorry`.

## Main theorems

In [`EHP6/Final.lean`](EHP6/Final.lean):

```lean
theorem EHP6.erdos_hajnal_P6_of_imported (hR : RodlCoP6) (hP : NssPath6) (hE : EhP5) (hC : NssComb) :
    EHforP6
theorem EHP6.erdos_hajnal_P6_of_cited (hR : RodlCoP6) (hE : EhP5) (hC : NssComb) : EHforP6
```

`lake env lean Audit.lean` prints

```
'EHP6.erdos_hajnal_P6_of_imported' depends on axioms: [propext, Classical.choice, Quot.sound]
'EHP6.erdos_hajnal_P6_of_cited' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms. The hypotheses are the imported theorems, stated as
propositions in [`EHP6/Imported.lean`](EHP6/Imported.lean). `NssPath6` is proved in
[`EHP6/NSSPath.lean`](EHP6/NSSPath.lean) (`nss_path6_proof`, from `nss_path` for paths with any number of
vertices), which is how the second theorem drops it:

| proposition | imported theorem | source (checked against the arXiv LaTeX) |
|---|---|---|
| `RodlCoP6` | Rödl's theorem, for H the complement of P6 | NSS VII, Theorem 1.3 |
| `NssPath6` | sparse graphs without an induced path P have an anticomplete (1/y, ⌊y²\|G\|⌋)-blockade; used for P = P6 | NSS V (a preprint), statement 3.1; **proved** in `NSSPath.lean` |
| `EhP5` | the Erdős–Hajnal property of P5 | NSS VII, Theorem 1.2 |
| `NssComb` | the comb lemma | NSS VII, Lemma 4.3, a special case of a lemma of Chudnovsky, Scott, Seymour and Spirkl (*Erdős–Hajnal for graphs with no 5-hole*, Proc. London Math. Soc. 126 (2023)) |

[`EHP6/Axioms.lean`](EHP6/Axioms.lean) asserts the three remaining propositions as axioms (`rodl_coP6`,
`eh_P5`, `nss_comb`), and `EHP6.erdos_hajnal_P6 : EHforP6` is `erdos_hajnal_P6_of_cited` applied to them. The
source statements are quoted next to the Lean statements in the top-level [README](../README.md) and in
Section 0 of the paper.

## What to read

To trust the result you need to read two files: [`EHP6/Defs.lean`](EHP6/Defs.lean), to see that `Free`,
`P6`, `IsCliqueF`, `IsStableF` and `EHforP6` mean what they should, and
[`EHP6/Imported.lean`](EHP6/Imported.lean), to compare `RodlCoP6`, `EhP5` and `NssComb` with their
sources (`NssPath6` is proved).
Everything else is checked by Lean's kernel and, independently, by nanoda; see
[VERIFICATION.md](../VERIFICATION.md). [`DefsCheck.lean`](DefsCheck.lean) proves that the definitions in
`Defs.lean` agree with Mathlib's standard ones and restates the main theorem using only those.

## Building

```
lake exe cache get && lake build
lake env lean Audit.lean
lake env leanchecker --fresh EHP6.Final
lake env lean DefsCheck.lean
```

`Challenge.lean`, `Solution.lean` and `comparator.json` set up the comparator check described in
[VERIFICATION.md](../VERIFICATION.md).

## From the paper to the Lean files

Numbers refer to [the paper](../paper/erdos-hajnal-p6.pdf); Section 9 of the paper has the same table
with all theorem names. The last column lists the imported theorems a result depends on.

| paper | Lean | uses |
|---|---|---|
| Imported Theorems I–IV | `RodlCoP6`, `NssPath6`, `EhP5`, `NssComb` (Imported.lean); I, III, IV asserted in Axioms.lean | |
| Imported Theorem II (NSS V statement 3.1) | `nss_path`, `nss_path6_proof` (NSSPath.lean) | |
| Lemmas 0.3, 0.4 (NSS VII Lemmas 4.1, 4.2) | `nss_L41_proof`, `nss_L42_proof` (NSSL41.lean, NSSL42.lean) | |
| Lemma 0.5 | `exists_anticonn_subset` (Round2Util.lean) | |
| modular decomposition, Lemmas 0.6, 0.7 | MD.lean, MDGallai.lean | |
| the six-vertex certificate (Figure 1) | `coP6_of_facts` (Certificate.lean) | |
| Lemma 1.1, the module law | `module_law` (Local.lean) | |
| Lemmas 1.2, 1.3, the diagonal and house lemmas | `diagonal_lemma`, `house_lemma` (House.lean) | |
| Corollary 1.4 | `light_pattern_house_free` (House.lean), `light_hom` (Round2Hom.lean) | III |
| Lemma 2.1, the Tooth Lemma | `tooth_lemma` (Tooth.lean and Tooth*.lean) | |
| Lemma 2.2, the Pair Lemma | `pair_lemma` (Pair.lean) | |
| Lemma 3.1, the comb lemma for P6 | `comb_lemma` (Comb.lean, CombExtract.lean) | IV |
| Lemmas 4.1–4.3, round one | `round1_step`, `round1`, `round1_blockade` (Round1.lean) | I, II, IV |
| Theorem 5.1, the layout theorem | `layout_theorem` (Layout.lean) | |
| Lemma 5.2, P6 is nice | `nice_P6` (Nice.lean) | I, II, IV |
| Lemma 6.1, round two | `round2_step` (Round2.lean, Round2Pass.lean, Round2Hom.lean) | III |
| Lemma 6.2 | `round2` (Round2b.lean) | |
| Definition 7.1, Corollary 7.2 | `CruxC` (Defs.lean), `crux_P6` (Crux.lean) | I–IV |
| Lemma 8.1 | `c01_lemma1` (C01Lemma1.lean) | I, II |
| Lemma 8.2 | `c01_lemma2` (C01Tree.lean) | |
| Theorem 8.3, Theorem A | `polyRodl`, `eh_of_polyRodl`, `erdos_hajnal_P6_of_imported`, `erdos_hajnal_P6_of_cited` (Final.lean, C01EH.lean) | I–IV (II proved) |

## Differences from the arguments of Nguyen, Scott and Seymour

The paper gives every proof in the form in which it was formalized. In a few places this differs from
the corresponding argument in NSS VII:

- NSS VII Lemmas 4.1 and 4.2 are proved here by greedy arguments; the second replaces the random choice of
  arXiv version 3 and keeps its bound |A'| ≤ 1/x (for x < 1/2). The July 2026 revision of NSS VII also
  uses a greedy argument, with the bound 2/x for all x > 0.
- Steps 2 and 3 of Lemma 6.1 use a deterministic averaging pass instead of random subsets.
- Lemmas 4.2 and 8.1 take the largest admissible index on a discrete sequence of scales instead of the
  least admissible real y.
- Lemma 8.2 is proved by an induction on |F| that builds a family of pairwise anticomplete sets and a
  family of pairwise complete sets, instead of a maximal cograph layout.

## A bug the formalization caught

An early version assumed NSS VII Lemma 4.2 as an axiom, in the form of arXiv version 3: if every vertex of B has
at least x|A| neighbours in A, then some A' ⊆ A with |A'| ≤ 1/x covers half of B. For A = ∅ and B ≠ ∅
the hypothesis holds vacuously and the conclusion fails, so the axiom was false. The degenerate case is
harmless in the paper, but a false axiom makes a formalization worthless. The hypothesis A ≠ ∅ was added,
and the lemma is now proved rather than assumed. The four remaining imported statements were then
re-checked against their sources for the same kind of problem: empty sets, empty blocks and small graphs.
One of them, NSS V statement 3.1, has since been proved as well.
