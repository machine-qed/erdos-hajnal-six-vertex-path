import EHP6.Defs

/-!
# Lemma 2.2 (Pair Lemma)
-/

namespace EHP6

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
lemma edgesBetween_eq_sum (A B : Finset V) :
    edgesBetween G A B = ∑ b ∈ B, (A.filter (fun a => G.Adj a b)).card := by
  unfold edgesBetween
  rw [card_eq_sum_ones, sum_filter, sum_product_right]
  refine sum_congr rfl fun b _ => ?_
  rw [card_eq_sum_ones, sum_filter]

/-- **Lemma 2.2 (Pair Lemma).** If every vertex of `Y₁` sees all of `Y₂` or fewer than `θ|Y₂|` of it,
and symmetrically, then `(Y₁, Y₂)` is complete or weakly `2θ`-sparse. -/
theorem pair_lemma (Y₁ Y₂ : Finset V) (θ : ℝ) (hθ : 0 < θ)
    (h₁ : ∀ w ∈ Y₁, Y₂ ⊆ nbrs G w Y₂ ∨ ((nbrs G w Y₂).card : ℝ) < θ * Y₂.card)
    (h₂ : ∀ u ∈ Y₂, Y₁ ⊆ nbrs G u Y₁ ∨ ((nbrs G u Y₁).card : ℝ) < θ * Y₁.card) :
    Complete G Y₁ Y₂ ∨ WeaklySparse G (2 * θ) Y₁ Y₂ := by
  classical
  set F := Y₂.filter (fun u => Y₁ ⊆ nbrs G u Y₁) with hF
  by_cases hbig : θ * Y₂.card ≤ (F.card : ℝ)
  · left
    intro w hw b hb
    have hsub : F ⊆ nbrs G w Y₂ := by
      intro u hu
      obtain ⟨huY, hu1⟩ := mem_filter.1 hu
      exact mem_filter.2 ⟨huY, G.adj_symm (mem_filter.1 (hu1 hw)).2⟩
    have hcard : θ * Y₂.card ≤ ((nbrs G w Y₂).card : ℝ) :=
      hbig.trans (by exact_mod_cast card_le_card hsub)
    rcases h₁ w hw with h | h
    · exact (mem_filter.1 (h hb)).2
    · exact absurd hcard (not_le.2 h)
  · right
    push Not at hbig
    unfold WeaklySparse
    rw [edgesBetween_eq_sum]
    push_cast
    have key : ∀ b ∈ Y₂, ((Y₁.filter (fun a => G.Adj a b)).card : ℝ) ≤
        (if b ∈ F then (Y₁.card : ℝ) else θ * Y₁.card) := by
      intro b hb
      have heq : Y₁.filter (fun a => G.Adj a b) = nbrs G b Y₁ := by
        unfold nbrs; exact filter_congr fun a _ => ⟨fun h => G.adj_symm h, fun h => G.adj_symm h⟩
      rw [heq]
      split_ifs with hbF
      · exact_mod_cast card_le_card (filter_subset _ _)
      · rcases h₂ b hb with h | h
        · exact absurd (mem_filter.2 ⟨hb, h⟩) hbF
        · exact h.le
    calc ∑ b ∈ Y₂, ((Y₁.filter (fun a => G.Adj a b)).card : ℝ)
        ≤ ∑ b ∈ Y₂, (if b ∈ F then (Y₁.card : ℝ) else θ * Y₁.card) := sum_le_sum key
      _ ≤ ∑ b ∈ Y₂, ((if b ∈ F then (Y₁.card : ℝ) else 0) + θ * Y₁.card) := by
          refine sum_le_sum fun b _ => ?_
          split_ifs <;> nlinarith [(Nat.cast_nonneg Y₁.card : (0:ℝ) ≤ Y₁.card)]
      _ = F.card * Y₁.card + Y₂.card * (θ * Y₁.card) := by
          rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, hF]
          simp [nsmul_eq_mul, filter_filter]
          left; congr 1; exact filter_congr fun a ha => by simp [ha]
      _ ≤ 2 * θ * Y₁.card * Y₂.card := by
          nlinarith [(Nat.cast_nonneg Y₁.card : (0:ℝ) ≤ Y₁.card)]

end EHP6
