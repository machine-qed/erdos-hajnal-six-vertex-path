import EHP6.Certificate

/-!
# §1 Local lemmas: the module law (Lemma 1.1)
-/

namespace EHP6

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Lemma 1.1 (module law).** Let `G` be P̄6-free, `v ≁ a`, `Z ⊆ N(v) ∩ N(a)`, `u ~ v`, `u ≁ a`.
Then every anticomponent of `G[N(u) ∩ Z]` is a module of `G[Z]`. -/
theorem module_law (hfree : Free G P6ᶜ) {v a u : V} {Z K : Finset V}
    (hva : ¬ G.Adj v a) (hZ : ∀ z ∈ Z, G.Adj v z ∧ G.Adj a z) (huv : G.Adj u v) (hua : ¬ G.Adj u a)
    (hK : IsAnticomponent G (Z.filter (G.Adj u)) K) : IsModule G Z K := by
  obtain ⟨hKsub, _, hKanti, hKc⟩ := hK
  have hKZ : K ⊆ Z := fun k hk => (mem_filter.1 (hKsub hk)).1
  have hKu : ∀ k ∈ K, G.Adj u k := fun k hk => (mem_filter.1 (hKsub hk)).2
  refine ⟨hKZ, fun y hy => ?_⟩
  obtain ⟨hyZ, hyK⟩ := mem_sdiff.1 hy
  by_cases hyu : G.Adj u y
  · exact Or.inl (hKc y (mem_sdiff.2 ⟨mem_filter.2 ⟨hyZ, hyu⟩, hyK⟩))
  by_cases hall : ∀ k ∈ K, G.Adj y k
  · exact Or.inl hall
  by_cases hnone : ∀ k ∈ K, ¬ G.Adj y k
  · exact Or.inr hnone
  exfalso
  push Not at hall hnone
  obtain ⟨p₀, hp₀K, hp₀⟩ := hnone
  obtain ⟨q₀, hq₀K, hq₀⟩ := hall
  obtain ⟨w, hwP, z, hzP, hwz⟩ := hKanti (K.filter (G.Adj y)) (filter_subset _ _)
    ⟨p₀, mem_filter.2 ⟨hp₀K, hp₀⟩⟩ ⟨q₀, mem_sdiff.2 ⟨hq₀K, fun h => hq₀ (mem_filter.1 h).2⟩⟩
  obtain ⟨hwK, hyw⟩ := mem_filter.1 hwP
  obtain ⟨hzK, hzy⟩ := mem_sdiff.1 hzP
  have hyz : ¬ G.Adj y z := fun h => hzy (mem_filter.2 ⟨hzK, h⟩)
  apply hfree
  -- complement path v – a – u – y – z – w
  exact coP6_of_facts G v a u y z w (G.adj_symm huv) (hZ y hyZ).1 (hZ z (hKZ hzK)).1 (hZ w (hKZ hwK)).1
    (hZ y hyZ).2 (hZ z (hKZ hzK)).2 (hZ w (hKZ hwK)).2 (hKu z hzK) (hKu w hwK) hyw
    hva (fun h => hua (G.adj_symm h)) hyu hyz (fun h => hwz (G.adj_symm h))

end EHP6
