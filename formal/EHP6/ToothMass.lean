import EHP6.ToothFacts

/-!
# Tooth Lemma: mass accounting (the atom parts `S(N)`, `N ∈ 𝓛`, partition `Y`)
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- (F1) `Σ_{N ∈ 𝓛} |S(N)| = |Y|` -/
lemma sum_atomPart_eq {Y : Finset V} {s : ℝ} (hs : 1 < s) (hsY : s ≤ Y.card) :
    ∑ N ∈ Lfam G Y s, ((atomPart G Y s N).card : ℝ) = Y.card := by
  have hdisj : (Lfam G Y s : Set (Finset V)).PairwiseDisjoint (atomPart G Y s) := by
    intro N hN N' hN' hne
    rw [Function.onFun, disjoint_left]
    intro v hv hv'
    exact hne (atomPart_unique hN hN' hv hv')
  have hcover : (Lfam G Y s).biUnion (atomPart G Y s) = Y := by
    apply subset_antisymm
    · intro v hv
      obtain ⟨N, hN, hvN⟩ := mem_biUnion.1 hv
      exact (mem_Lfam.1 hN).1 (atomPart_subset hvN)
    · intro v hv
      obtain ⟨N, hN, hvN⟩ := exists_atomPart (G := G) hs hsY hv
      exact mem_biUnion.2 ⟨N, hN, hvN⟩
  have := card_biUnion hdisj
  rw [hcover] at this
  exact_mod_cast this.symm

/-- the total atom-part mass of the members of `𝓛` inside a family of pairwise disjoint sets `𝒜`
(each member of `𝓛` in the sub-family lies inside some member of `𝒜`) is at most `Σ_{A ∈ 𝒜} |A|` -/
lemma sum_atomPart_le_of_cover {Y : Finset V} {s : ℝ} (hs : 1 < s) (hsY : s ≤ Y.card)
    (ℱ : Finset (Finset V)) (hℱ : ℱ ⊆ Lfam G Y s) (𝒜 : Finset (Finset V))
    (hcov : ∀ N ∈ ℱ, ∃ A ∈ 𝒜, N ⊆ A)
    (h𝒜 : (𝒜 : Set (Finset V)).PairwiseDisjoint id) :
    ∑ N ∈ ℱ, ((atomPart G Y s N).card : ℝ) ≤ ∑ A ∈ 𝒜, (A.card : ℝ) := by
  have hdisj : (ℱ : Set (Finset V)).PairwiseDisjoint (atomPart G Y s) := by
    intro N hN N' hN' hne
    rw [Function.onFun, disjoint_left]
    intro v hv hv'
    exact hne (atomPart_unique (hℱ hN) (hℱ hN') hv hv')
  have h1 : ∑ N ∈ ℱ, ((atomPart G Y s N).card : ℝ) = (ℱ.biUnion (atomPart G Y s)).card := by
    exact_mod_cast (card_biUnion hdisj).symm
  have h2 : ∑ A ∈ 𝒜, (A.card : ℝ) = (𝒜.biUnion id).card := by
    exact_mod_cast (card_biUnion h𝒜).symm
  rw [h1, h2]
  apply Nat.cast_le.2 (card_le_card _)
  intro v hv
  obtain ⟨N, hN, hvN⟩ := mem_biUnion.1 hv
  obtain ⟨A, hA, hNA⟩ := hcov N hN
  exact mem_biUnion.2 ⟨A, hA, hNA (atomPart_subset hvN)⟩

end EHP6
