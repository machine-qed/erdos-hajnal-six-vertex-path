import EHP6.Defs

/-!
# The four cited results used by the proof

Each of the four results below is stated as a proposition. The main theorem
`EHP6.erdos_hajnal_P6_of_imported` (in `EHP6/Final.lean`) has these four propositions as hypotheses and
uses no axioms beyond Lean's standard ones, so Lean checks the implication

  `RodlCoP6 → NssPath6 → EhP5 → NssComb → EHforP6`

outright. `NssPath6` is proved in `EHP6/NSSPath.lean`, so `EHP6.erdos_hajnal_P6_of_cited` needs only
the other three, and `EHP6/Axioms.lean` asserts those three, citing the literature, to obtain the
unconditional statement `EHP6.erdos_hajnal_P6 : EHforP6`.

Each proposition is stated as close as possible to its source; each is an instance or a
vertex-set-relative restatement of the cited statement (a statement about `G[S]` for every `S` is
equivalent to the statement for every graph, since induced subgraphs of H-free graphs are H-free).
**`RodlCoP6`, `EhP5` and `NssComb` must be checked by a human against the sources;** `NssPath6` is
proved, so its statement does not need that check.

* `RodlCoP6` — Rödl (1986), as stated in NSS VII (arXiv 2312.15333) Theorem 1.3, for H = P̄6.
* `NssPath6` — Nguyen–Scott–Seymour, *Induced subgraph density V* (arXiv 2307.15032, a preprint),
               statement 3.1, for the path P6 (k = 6). Proved in `EHP6/NSSPath.lean`
               (`EHP6.nss_path6_proof`), so it is no longer an assumption.
* `EhP5`     — Nguyen–Scott–Seymour, *Induced subgraph density VII* (arXiv 2312.15333), Theorem 1.2.
* `NssComb`  — NSS VII Lemma 4.3, a special case of a lemma of Chudnovsky–Scott–Seymour–Spirkl,
               *Erdős–Hajnal for graphs with no 5-hole*, Proc. LMS 126 (2023).

NSS VII Lemmas 4.1 and 4.2 are proved in `EHP6/NSSL41.lean` and `EHP6/NSSL42.lean`.
-/

namespace EHP6

open Finset

/-- **Rödl's theorem for H = P̄6** (NSS VII Thm 1.3): for every `ε ∈ (0, ½)` there is `δ > 0` such that
every P̄6-free graph has an `ε`-restricted induced subgraph on at least `δ|G|` vertices. -/
def RodlCoP6 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ δ : ℝ, 0 < δ ∧
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Free G P6ᶜ → ∀ S : Finset V, ∃ F ⊆ S, δ * S.card ≤ F.card ∧ Restricted G ε F

/-- **NSS V, statement 3.1, for P = P6**: if `0 < y ≤ 1/(60·6)` and `G[S]` is `y²`-sparse and has no
induced P6, then `G[S]` has an anticomplete `(1/y, ⌊y²|S|⌋)`-blockade. -/
def NssPath6 : Prop := ∀ y : ℝ, 0 < y → y ≤ 1 / 360 →
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V), Sparse G (y ^ 2) S → ¬ ContainsInduced G P6 S →
      ∃ β : Blockade S (1 / y) (⌊y ^ 2 * S.card⌋₊ : ℝ), β.IsAnticomplete G

/-- **EH for P5** (NSS VII Thm 1.2): there is `c > 0` such that every P5-free graph has a clique or a
stable set of size at least `|G|^c`. -/
def EhP5 : Prop := ∃ c : ℝ, 0 < c ∧
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Free G P5 → ∃ T : Finset V, (IsCliqueF G T ∨ IsStableF G T) ∧ (Fintype.card V : ℝ) ^ c ≤ T.card

/-- **Comb lemma** (NSS VII Lemma 4.3): let `A, B` be disjoint and nonempty, `Δ > 0`, and every vertex
of `A` have at most `Δ` neighbours in `B`. Then either at most `20√(|B|Δ)` vertices of `B` have a
neighbour in `A`, or for some integer `ℓ ≥ 1` there are distinct `a₁, …, a_ℓ ∈ A` and pairwise disjoint
`B₁, …, B_ℓ ⊆ B`, each of size at least `|B|/ℓ²`, with `aᵢ` complete to `Bᵢ` and anticomplete to `Bⱼ`
(`j ≠ i`). -/
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

end EHP6
