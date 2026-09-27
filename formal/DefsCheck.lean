import Mathlib
import EHP6.Final

/-!
# The definitions of `Defs.lean`, compared with Mathlib's

Proves that the project's definitions agree with Mathlib's standard notions (the path graph, induced
embeddings, cliques, independent sets and degrees in induced subgraphs), and restates the main theorem
using Mathlib's definitions only. Run with `lake env lean DefsCheck.lean`.
-/

set_option linter.unusedSectionVars false

namespace EHP6.Check

open EHP6

/-- The project's `P6` is Mathlib's path graph on six vertices. -/
theorem P6_eq : P6 = SimpleGraph.pathGraph 6 := by
  ext i j
  simp only [P6, pathGraph', SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨fun hij => by subst hij; omega, h⟩

theorem P5_eq : P5 = SimpleGraph.pathGraph 5 := by
  ext i j
  simp only [P5, pathGraph', SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨fun hij => by subst hij; omega, h⟩

section
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `Free G H` means: no induced embedding of `H` into `G` in Mathlib's sense (`H ↪g G` is an
embedding with `G.Adj (f a) (f b) ↔ H.Adj a b`). -/
theorem free_iff {n : ℕ} (H : SimpleGraph (Fin n)) : Free G H ↔ IsEmpty (H ↪g G) := by
  unfold Free ContainsInduced
  constructor
  · intro h
    exact ⟨fun f => h ⟨f, f.injective, fun _ => Finset.mem_univ _, fun i j => f.map_rel_iff⟩⟩
  · rintro ⟨h⟩ ⟨f, hf, -, hadj⟩
    exact h ⟨⟨f, hf⟩, fun {i j} => hadj i j⟩

theorem clique_iff (T : Finset V) : IsCliqueF G T ↔ G.IsClique (T : Set V) := by
  simp [IsCliqueF, SimpleGraph.IsClique, Set.Pairwise]

theorem stable_iff (T : Finset V) : IsStableF G T ↔ G.IsIndepSet (T : Set V) := by
  simp [IsStableF, SimpleGraph.IsIndepSet, Set.Pairwise]

/-- `nbrs` in the complement counts the non-neighbours other than `v` itself. -/
theorem nbrs_compl (v : V) (S : Finset V) :
    nbrs Gᶜ v S = (S.erase v).filter (fun w => ¬ G.Adj v w) := by
  ext w
  simp only [nbrs, Finset.mem_filter, Finset.mem_erase, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨hw, hne, hadj⟩; exact ⟨⟨fun h => hne h.symm, hw⟩, hadj⟩
  · rintro ⟨⟨hne, hw⟩, hadj⟩; exact ⟨hw, fun h => hne h.symm, hadj⟩

/-- `Sparse G x S` says that the induced subgraph `G[S]` has maximum degree at most `x|S|`,
with degrees computed by Mathlib in `G.induce S`. -/
theorem sparse_iff (x : ℝ) (S : Finset V) :
    Sparse G x S ↔ ∀ v : (S : Set V),
      (((G.induce (S : Set V)).neighborFinset v).card : ℝ) ≤ x * S.card := by
  classical
  have key : ∀ v : (S : Set V),
      ((G.induce (S : Set V)).neighborFinset v).card = (nbrs G v S).card := by
    intro v
    refine Finset.card_bij (fun w _ => (w : V)) ?_ ?_ ?_
    · intro w hw
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.comap_adj,
        Function.Embedding.subtype_apply] at hw
      simp [nbrs, hw]
    · intro a _ b _ h; exact Subtype.ext h
    · intro w hw
      simp only [nbrs, Finset.mem_filter] at hw
      exact ⟨⟨w, by simpa using hw.1⟩, by simpa [SimpleGraph.mem_neighborFinset] using hw.2, rfl⟩
  constructor
  · intro h v; rw [key]; exact h v (by simp)
  · intro h v hv; have := h ⟨v, by simpa using hv⟩; rwa [key] at this
end

/-- `P6` is not `P6`-free, and the complete graph on ten vertices is: `Free` is not vacuous. -/
example : ¬ Free P6 P6 :=
  fun h => h ⟨id, Function.injective_id, fun _ => Finset.mem_univ _, fun _ _ => Iff.rfl⟩

example : Free (⊤ : SimpleGraph (Fin 10)) P6 := by
  rintro ⟨f, hf, -, hadj⟩
  have h02 := (hadj 0 2).1 (by simp [hf.ne (by decide : (0 : Fin 6) ≠ 2)])
  exact absurd h02 (by decide)

/-- The theorem, restated with Mathlib's definitions only: `pathGraph`, induced embeddings,
`IsClique` and `IsIndepSet`. -/
theorem erdos_hajnal_P6_mathlib (hR : RodlCoP6) (hE : EhP5) (hC : NssComb) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      IsEmpty (SimpleGraph.pathGraph 6 ↪g G) →
      ∃ s : Finset (Fin n), (G.IsClique (s : Set (Fin n)) ∨ G.IsIndepSet (s : Set (Fin n))) ∧
        (n : ℝ) ^ τ ≤ s.card := by
  classical
  obtain ⟨τ, hτ, hG⟩ := erdos_hajnal_P6_of_cited hR hE hC
  refine ⟨τ, hτ, fun n G hfree => ?_⟩
  obtain ⟨T, hT, hcard⟩ := hG (Fin n) G (by rw [free_iff, P6_eq]; exact hfree)
  refine ⟨T, ?_, by simpa using hcard⟩
  rcases hT with hT | hT
  · exact Or.inl ((clique_iff G T).1 hT)
  · exact Or.inr ((stable_iff G T).1 hT)

end EHP6.Check

#print axioms EHP6.Check.erdos_hajnal_P6_mathlib
