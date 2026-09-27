# The Erdős–Hajnal property for the six-vertex path

[![Lean proof](https://github.com/machine-qed/erdos-hajnal-six-vertex-path/actions/workflows/lean.yml/badge.svg)](https://github.com/machine-qed/erdos-hajnal-six-vertex-path/actions/workflows/lean.yml)

This repository contains a proof that the six-vertex path P6 has the Erdős–Hajnal property, written up as
a paper and formalized in Lean 4. The proof has **not been refereed**. It was produced by Claude Opus 5.5, an AI
system made by Anthropic, in a research session commissioned by the repository owner. It is not a
publication of Anthropic, and Anthropic has not reviewed it. If you find a problem, please
[open an issue](../../issues).

## The result

> **Theorem.** There is τ > 0 such that every graph on n vertices with no induced path on six vertices
> has a clique or an independent set with at least n^τ vertices.

Erdős and Hajnal conjectured in 1977 that for every graph H, the graphs with no induced copy of H have a
clique or independent set of polynomial size, compared with the logarithmic size that is all one can
guarantee in general. The conjecture was known for every graph with at most five vertices, the last case
being the five-vertex path, settled by Nguyen, Scott and Seymour
([arXiv 2312.15333](https://arxiv.org/abs/2312.15333)). For P6 the best bound so far was
2^{(log n)^{1−o(1)}} (Nguyen, Scott and Seymour, [arXiv 2307.15032](https://arxiv.org/abs/2307.15032)).

The proof gives the stronger *polynomial Rödl property* for P6. It determines τ by a formula in two
constants of the imported theorems, the δ of Rödl's theorem and the exponent of the Erdős–Hajnal theorem
for P5, and no numerical values of those are available. So τ is not known numerically; the formula only
shows that τ < 10^−15.

## Where to start

| | |
|---|---|
| [paper/erdos-hajnal-p6.pdf](paper/erdos-hajnal-p6.pdf) | the paper (24 pages; source in [paper/](paper/)); written to be read without Lean |
| [formal/](formal/) | the Lean 4 project; the main theorem is in [`formal/EHP6/Final.lean`](formal/EHP6/Final.lean) |
| [VERIFICATION.md](VERIFICATION.md) | how the Lean proof was checked, with tool versions and outputs |
| [RELEASE.md](RELEASE.md) | versions and checksums of the tagged release |
| [LICENSE](LICENSE) | Apache 2.0 for the code; the paper is CC BY 4.0 |

## How the proof works

The proof follows the proof of Nguyen, Scott and Seymour for P5. That proof uses the absence of an
induced *house* (the complement of P5) in exactly two steps, and both steps fail for P6. This proof
replaces them.

New here:

- **The module law** (Lemma 1.1). In a comb, a vertex outside a tooth sees the tooth only through the
  tooth's modules. Otherwise six vertices induce the complement of P6.
- **The Tooth Lemma** (Lemma 2.1) combines the module law with the modular decomposition of the tooth.
  It leads to a comb lemma for P6 (Lemma 3.1) whose blockades are only *semisparse*: every two blocks are
  complete, or sparse on average.
- **Semisparse layouts** (Theorem 5.1). The layout theorem of Nguyen, Scott and Seymour only counts edges
  between blocks declared anticomplete, so it accepts semisparse input.
- **House-free patterns** (Lemmas 1.2 and 1.3, Corollary 1.4, and Step 4 of Lemma 6.1). The blocks on
  which a vertex is lightly mixed form a house-free pattern, so the Erdős–Hajnal theorem for P5 applies
  to that pattern.

Taken over from Nguyen, Scott and Seymour, with the constants recomputed: the two sparsification rounds
(Sections 4 and 6), niceness (Lemma 5.2) and the reduction to the polynomial Rödl property (Section 8).
The paper proves these steps in full as well.

The method does not extend to P7 without new ideas. The module law already fails in the complement of P6
itself, and that graph has no induced complement of P7.

## What you have to trust

The proof uses four theorems from the literature, stated as Lean propositions in
[`formal/EHP6/Imported.lean`](formal/EHP6/Imported.lean). The second is proved in the formalization, so
the formal result assumes only the other three:

| | imported theorem | source | Lean |
|---|---|---|---|
| I | Rödl's theorem, for H the complement of P6 | Rödl (1986), in the form of [NSS VII], Theorem 1.3 | `RodlCoP6` |
| II | sparse graphs without an induced path P have a long anticomplete blockade; used for P = P6 | [NSS V], statement 3.1 — **proved** in [`formal/EHP6/NSSPath.lean`](formal/EHP6/NSSPath.lean) | `NssPath6` |
| III | the Erdős–Hajnal property of P5 | [NSS VII], Theorem 1.2 | `EhP5` |
| IV | the comb lemma | [NSS VII], Lemma 4.3, a special case of a lemma of Chudnovsky, Scott, Seymour and Spirkl [CSSS] | `NssComb` |

I, III and IV come from refereed papers. II comes from [NSS V], which has not yet appeared in a journal.
Its proof takes half a page, and `EHP6.nss_path6_proof : NssPath6` formalizes it (for paths of any
length), so II is not an assumption of the formal result.

Independently of this project, Édouard Bonnet has formalized in Lean the Erdős–Hajnal theorems for C5
([lax-54](https://github.com/EdouardBonnet/EH-C5)) and P5 ([lax-57](https://github.com/EdouardBonnet/EH-P5)),
including Rödl's theorem and a version of the comb lemma with different constants. Connecting them to this
project would turn I and III into proved statements, and IV too after raising the constant 20 to 128,
which the proof can absorb. This has not been done yet.

The main Lean theorems take them as hypotheses:

```lean
theorem EHP6.erdos_hajnal_P6_of_imported (hR : RodlCoP6) (hP : NssPath6) (hE : EhP5) (hC : NssComb) :
    EHforP6
theorem EHP6.erdos_hajnal_P6_of_cited (hR : RodlCoP6) (hE : EhP5) (hC : NssComb) : EHforP6
```

Their proofs use no axioms beyond Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). So
Lean checks outright that I, III and IV imply the result. The file
[`formal/EHP6/Axioms.lean`](formal/EHP6/Axioms.lean) then asserts I, III and IV as axioms, and
`EHP6.erdos_hajnal_P6 : EHforP6` is the unconditional statement.

To trust the formal result you therefore need to check two short files by hand:

1. [`formal/EHP6/Imported.lean`](formal/EHP6/Imported.lean): `RodlCoP6`, `EhP5` and `NssComb` say what
   the cited theorems say. They are shown below next to the source statements (with `NssPath6`, which is
   proved and needs no check).
2. [`formal/EHP6/Defs.lean`](formal/EHP6/Defs.lean): the definitions of P6-free graphs, cliques, stable
   sets and the target statement `EHforP6` are the intended ones.

[`formal/DefsCheck.lean`](formal/DefsCheck.lean) reduces the second check. It proves that the project's
`P6`, `Free`, `IsCliqueF`, `IsStableF` and `Sparse` agree with Mathlib's path graph, induced embeddings,
cliques, independent sets and degrees in induced subgraphs, and restates the main theorem with Mathlib's
definitions only (still with just the three standard axioms). CI runs it on every push.

Each proposition is stated for an arbitrary vertex set `S`, meaning the induced subgraph `G[S]`. This is
equivalent to the source statement because induced subgraphs of H-free graphs are H-free. Below, `P6ᶜ` is
the complement of P6, `Sparse G x S` means that every vertex of `S` has at most x|S| neighbours in `S`,
and `Restricted G x S` means that `G[S]` or its complement is x-sparse.

<details>
<summary><b>I. Rödl's theorem</b></summary>

Source ([NSS VII], Theorem 1.3): "For every ε ∈ (0, 1/2) and every graph H, there exists δ > 0 such that
every H-free graph G has an ε-restricted induced subgraph with at least δ|G| vertices."

```lean
def RodlCoP6 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ δ : ℝ, 0 < δ ∧
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Free G P6ᶜ → ∀ S : Finset V, ∃ F ⊆ S, δ * S.card ≤ F.card ∧ Restricted G ε F
```
</details>

<details>
<summary><b>II. Anticomplete blockades in sparse graphs without a long induced path (proved)</b></summary>

Source ([NSS V], statement 3.1): "Let P be a path with k ≥ 2 vertices, and let 0 < y ≤ 1/(60k). Let G be
a y²-sparse graph. Then either G contains a copy of P, or G contains an anticomplete (1/y, ⌊y²|G|⌋)-blockade
in G." Here a copy is an induced copy, and blocks of a blockade may be empty. Used with k = 6, so
y ≤ 1/360.

```lean
def NssPath6 : Prop := ∀ y : ℝ, 0 < y → y ≤ 1 / 360 →
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V), Sparse G (y ^ 2) S → ¬ ContainsInduced G P6 S →
      ∃ β : Blockade S (1 / y) (⌊y ^ 2 * S.card⌋₊ : ℝ), β.IsAnticomplete G
```
</details>

<details>
<summary><b>III. The Erdős–Hajnal property of P5</b></summary>

Source ([NSS VII], Theorem 1.2): "P5 satisfies the Erdős–Hajnal conjecture", that is, there is c > 0 such
that every P5-free graph G has a clique or a stable set with at least |G|^c vertices.

```lean
def EhP5 : Prop := ∃ c : ℝ, 0 < c ∧
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Free G P5 → ∃ T : Finset V, (IsCliqueF G T ∨ IsStableF G T) ∧ (Fintype.card V : ℝ) ^ c ≤ T.card
```
</details>

<details>
<summary><b>IV. The comb lemma</b></summary>

Source ([NSS VII], Lemma 4.3): "Let G be a graph and let A, B ⊆ V(G) be nonempty and disjoint, such that
each vertex in A has at most Δ > 0 neighbours in B. Then either at most 20√(|B|Δ) vertices in B have a
neighbour in A; or for some integer k ≥ 1, there is a (k, |B|/k²)-comb ((a_i, B_i) : i ∈ [k]) in G where
a_i ∈ A and B_i ⊂ B for all i ∈ [k]." In a comb the a_i are distinct, the B_i are disjoint, and a_i is
complete to B_i and anticomplete to B_j for j ≠ i.

```lean
def NssComb : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (Δ : ℝ), Disjoint A B → A.Nonempty → B.Nonempty → 0 < Δ →
    (∀ a ∈ A, ((nbrs G a B).card : ℝ) ≤ Δ) →
    (((B.filter (fun b => ∃ a ∈ A, G.Adj a b)).card : ℝ) ≤ 20 * Real.sqrt (B.card * Δ)) ∨
    (∃ ℓ : ℕ, 1 ≤ ℓ ∧ ∃ (a : Fin ℓ → V) (C : Fin ℓ → Finset V),
      Function.Injective a ∧ (∀ i, a i ∈ A) ∧ (∀ i, C i ⊆ B) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ i, (B.card : ℝ) / ℓ ^ 2 ≤ (C i).card) ∧
      (∀ i, ∀ c ∈ C i, G.Adj (a i) c) ∧
      (∀ i j, i ≠ j → ∀ c ∈ C j, ¬ G.Adj (a i) c))
```
</details>

<details>
<summary><b>The target statement</b></summary>

From [`formal/EHP6/Defs.lean`](formal/EHP6/Defs.lean):

```lean
def EHforP6 : Prop :=
  ∃ τ : ℝ, 0 < τ ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Free G P6 → ∃ T : Finset V, (IsCliqueF G T ∨ IsStableF G T) ∧
        (Fintype.card V : ℝ) ^ τ ≤ T.card
```
</details>

## Checking the formal proof

The project uses Lean `v4.34.1` and Mathlib `v4.34.1`, the current release, which contains the fixes for
the kernel soundness bugs found in 2026. The proof was checked in four ways; [VERIFICATION.md](VERIFICATION.md)
gives the details.

1. **Build and axiom audit.** Every file compiles, and the main theorems and 32 intermediate results
   depend only on the three standard axioms.
2. **Fresh replay.** `leanchecker --fresh` re-checks every declaration the main theorem depends on,
   Mathlib included, starting from an empty environment.
3. **Comparator.** Lean's [comparator](https://github.com/leanprover/comparator) confirms that the
   project proves exactly the two statements in [`formal/Challenge.lean`](formal/Challenge.lean), which
   imports only `Defs.lean` and `Imported.lean`, with the three standard axioms.
4. **A second kernel.** Comparator also has the proof checked by
   [nanoda](https://github.com/ammkrn/nanoda_lib), a type checker written in Rust that shares no code with
   Lean's kernel.

To reproduce the first two, install [elan](https://github.com/leanprover/elan) and run

```
cd formal
lake exe cache get
lake build
lake env lean Audit.lean
lake env leanchecker --fresh EHP6.Final
```

GitHub Actions runs all four checks on every push, with each tool pinned to a fixed commit. The job fails
if any proof file contains `sorry` or `admit`, if any of the 35 results in the axiom audit uses an axiom
other than the three standard ones (only `erdos_hajnal_P6` may also use the three of `Axioms.lean`), if
`DefsCheck.lean` fails, if `leanchecker` fails, or if either kernel rejects the proof. [formal/README.md](formal/README.md) maps each result of the paper to its Lean
proof.

## Is it new?

To the best of our knowledge, yes. On 27 September 2026 we checked:

- every paper indexed by Semantic Scholar that cites [NSS V], [NSS VII], [CSSS] or
  [arXiv 2606.06258](https://arxiv.org/abs/2606.06258), and arXiv and the web more generally;
- Paul Seymour's list of papers;
- the page and discussion thread of the conjecture on the Erdős problems website
  ([Problem 61](https://www.erdosproblems.com/61)), the
  [list of AI contributions to Erdős problems](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems),
  the [FrontierMath Erdős](https://arxiv.org/abs/2609.25050) results and the [Lax archive](https://laxarchive.org) of Lean formalizations;
- GitHub and X, through web search.

We found no proof of the Erdős–Hajnal property for P6. The closest recent results are for other
six-vertex graphs ([arXiv 2606.06258](https://arxiv.org/abs/2606.06258),
[arXiv 2608.28551](https://arxiv.org/abs/2608.28551)). By the count in the second paper, eight
complementary pairs of prime six-vertex graphs were open as of 26 August 2026, and {P6, P̄6} is one of
them. The repository [jaredwilder/p6-erdos-hajnal](https://github.com/jaredwilder/p6-erdos-hajnal)
develops local structure for P6-free graphs towards the same goal and states that it does not prove the
full result. We did not have access to MathSciNet, zbMATH or Google Scholar, and web search covers X
poorly. We cannot rule out unpublished work. If you know of earlier work, please open an issue.

## For reviewers

- The only parts of the formal proof that need a human check are three propositions in `Imported.lean`
  (`RodlCoP6`, `EhP5`, `NssComb`) and the definitions in `Defs.lean`; `DefsCheck.lean` ties the latter to
  Mathlib's.
- In the mathematics, the new and least familiar parts are the Tooth Lemma (Lemma 2.1), Claim 2 in the
  proof of the layout theorem (Theorem 5.1), and Step 4 of Lemma 6.1.

## Credits

**Mathematics.** The proof builds on the work of Tung Nguyen, Alex Scott and Paul Seymour, whose proof
for P5 [NSS VII] supplies the architecture, and uses theorems of Vojtěch Rödl, of Nguyen, Scott and Seymour
[NSS V, NSS VII], and of Maria Chudnovsky, Alex Scott, Paul Seymour and Sophie Spirkl [CSSS]. The modular
decomposition goes back to Tibor Gallai.

**Software.** [Lean 4](https://lean-lang.org) and [Mathlib](https://github.com/leanprover-community/mathlib4);
`leanchecker` (Kim Morrison and Sebastian Ullrich), [comparator](https://github.com/leanprover/comparator)
and [lean4export](https://github.com/leanprover/lean4export) (Lean FRO);
[nanoda](https://github.com/ammkrn/nanoda_lib); [landrun](https://github.com/Zouuup/landrun) (Armin
Ranjbar); and the list of affected Lean versions at
[lean4-soundness](https://github.com/madvorak/lean4-soundness).

**Review.** Review comments from ChatGPT (OpenAI), passed on by the repository owner, led to several
corrections, including the move to a current Lean release and the independent kernel check.

**References.**
[NSS V] T. Nguyen, A. Scott, P. Seymour, *Induced subgraph density. V. All paths approach Erdős–Hajnal*,
[arXiv:2307.15032](https://arxiv.org/abs/2307.15032) (preprint).
[NSS VII] T. Nguyen, A. Scott, P. Seymour, *Induced subgraph density. VII. The five-vertex path*,
Proc. London Math. Soc. 132 (2026), e70133; [arXiv:2312.15333](https://arxiv.org/abs/2312.15333).
[CSSS] M. Chudnovsky, A. Scott, P. Seymour, S. Spirkl, *Erdős–Hajnal for graphs with no 5-hole*,
Proc. London Math. Soc. 126 (2023), 997–1014.

## License

The Lean code in [formal/](formal/) is released under the [Apache License 2.0](LICENSE), the license of
Lean and Mathlib. The paper in [paper/](paper/) is released under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
