import EHP6.ToothFacts
import EHP6.BlockadeUtil
import EHP6.Imported
import EHP6.NSSL41

/-!
# Tooth Lemma, Step 3: a thick layer `S(N)` gives TL3, TL4 or TL5
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
lemma conn_of_antiConnected_compl {D : Finset V} (h : AntiConnected Gᶜ D) : Conn G D := by
  intro P hP hne hrest
  obtain ⟨p, hp, q, hq, hpq⟩ := h P hP hne hrest
  refine ⟨p, hp, q, hq, ?_⟩
  by_contra hn
  exact hpq ((SimpleGraph.compl_adj G p q).2 ⟨fun e => (mem_sdiff.1 hq).2 (e ▸ hp), hn⟩)

omit [Fintype V] in
lemma nbrs_inter_eq {u : V} {Y S : Finset V} (hSY : S ⊆ Y) : nbrs G u Y ∩ S = nbrs G u S := by
  ext v; simp only [nbrs, mem_inter, mem_filter]
  constructor
  · rintro ⟨⟨-, h⟩, hv⟩; exact ⟨hv, h⟩
  · rintro ⟨hv, h⟩; exact ⟨⟨hSY hv, h⟩, hv⟩

theorem node_step {Y : Finset V} {s : ℝ} {N : Finset V} (hN : N ∈ Lfam G Y s) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ A, IsAnticomponent G (nbrs G u Y) A → IsModule G Y A)
    (x : ℝ) (K K' : ℕ) (hK2 : 2 ≤ K) (hK'2 : 2 ≤ K') (w₃ w₄ : ℝ)
    (h₃ : s ≤ (atomPart G Y s N).card / (K : ℝ) ∧ w₃ ≤ (atomPart G Y s N).card / (K : ℝ) ^ 2)
    (h₄ : ∀ r : ℝ, x * (atomPart G Y s N).card / 4 ≤ r → s ≤ r / K' ∧ w₄ ≤ r / (K' : ℝ) ^ 2) :
    (∃ β : Blockade Y K w₃, β.IsComplete G ∨ β.IsAnticomplete G) ∨
    (∃ β : Blockade Y K' w₄, β.IsComplete G) ∨
    (∀ u ∈ U, (∀ y ∈ atomPart G Y s N, G.Adj u y) ∨
      ((nbrs G u (atomPart G Y s N)).card : ℝ) < x * (atomPart G Y s N).card / 4) := by
  set S := atomPart G Y s N with hS
  obtain ⟨hNY, hNs, -⟩ := mem_Lfam.1 hN
  have hSY : S ⊆ Y := atomPart_subset.trans hNY
  by_cases hc : Conn G N
  · by_cases hc' : Conn Gᶜ N
    · -- prime node
      by_cases hbad : ∃ u ∈ U, ¬ (∀ y ∈ S, G.Adj u y) ∧
          x * S.card / 4 ≤ ((nbrs G u S).card : ℝ)
      · right; left
        obtain ⟨u, hu, hnotall, hbig⟩ := hbad
        have hT : ∀ A, IsAnticomponent G (nbrs G u Y) A → IsModule G Y A := hU u hu
        have hST : ¬ S ⊆ nbrs G u Y := fun h =>
          hnotall fun y hy => (mem_filter.1 (h hy)).2
        obtain ⟨hs', hw'⟩ := h₄ _ hbig
        have hsmall : ∀ D, IsAnticomponent G (nbrs G u S) D →
            (D.card : ℝ) < (nbrs G u S).card / K' := by
          intro D hD
          rw [← nbrs_inter_eq hSY] at hD
          exact (trace_pieces_small_of_prime hN hc hc' (filter_subset _ _) hT hST hD).trans_le hs'
        obtain ⟨β, hβ⟩ := nss_L41_proof (G := G) (nbrs G u S) K' hK'2 hsmall
        exact ⟨β.mono ((filter_subset _ _).trans hSY) le_rfl hw', hβ⟩
      · right; right
        intro u hu
        by_cases hall : ∀ y ∈ S, G.Adj u y
        · exact Or.inl hall
        · right; by_contra hge; push Not at hge; exact hbad ⟨u, hu, hall, hge⟩
    · -- series node: complete blockade
      left
      have hsmall : ∀ D, IsAnticomponent G S D → (D.card : ℝ) < S.card / K := by
        intro D hD
        obtain ⟨hDS, ⟨v, hv⟩, hDa, -⟩ := hD
        exact (anticonn_in_atom_of_series hN hc' hDS hDa hv).trans_le h₃.1
      obtain ⟨β, hβ⟩ := nss_L41_proof (G := G) S K hK2 hsmall
      exact ⟨β.mono hSY le_rfl h₃.2, Or.inl hβ⟩
  · -- parallel node: anticomplete blockade (NSS VII Lemma 4.1 = paper Lemma 0.3, in the complement)
    left
    have hsmall : ∀ D, IsAnticomponent Gᶜ S D → (D.card : ℝ) < S.card / K := by
      intro D hD
      obtain ⟨hDS, ⟨v, hv⟩, hDa, -⟩ := hD
      exact (conn_in_atom_of_parallel hN hc hDS (conn_of_antiConnected_compl hDa) hv).trans_le h₃.1
    obtain ⟨β, hβ⟩ := nss_L41_proof (G := Gᶜ) S K hK2 hsmall
    refine ⟨β.mono hSY le_rfl h₃.2, Or.inr fun i j hij a ha b hb hab => ?_⟩
    have hab' : a ≠ b := fun e => disjoint_left.1 (β.disj i j hij) ha (e ▸ hb)
    exact ((SimpleGraph.compl_adj G a b).1 (hβ i j hij a ha b hb)).2 hab

end EHP6
