import EHP6.Round2

/-!
# Lemma 6.2 (NSS VII Lemma 7.2 for P̄6-free graphs): the `y' = √y` iteration
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
lemma sparseTo_zero_of_anticomplete {A B : Finset V} (h : Anticomplete G A B) :
    SparseTo G 0 B A := fun v hv => by
  have : nbrs G v A = ∅ := filter_eq_empty_iff.2 fun a ha hva => h a ha v hv (G.adj_symm hva)
  rw [this]; simp

omit [Fintype V] [DecidableEq V] in
lemma anticomplete_of_sparseTo_zero {A B : Finset V} (h : SparseTo G 0 B A) :
    Anticomplete G A B := fun a ha v hv hav => by
  have h1 := h v hv
  rw [zero_mul] at h1
  have h2 : (nbrs G v A).card = 0 := by exact_mod_cast le_antisymm h1 (Nat.cast_nonneg _)
  have : a ∈ nbrs G v A := mem_filter.2 ⟨ha, G.adj_symm hav⟩
  rw [card_eq_zero.1 h2] at this; exact notMem_empty a this

/-- the outcomes of Lemma 6.1 with exponent `A₁` -/
def Out61 (G : SimpleGraph V) [DecidableRel G.Adj] (A₁ : ℕ) : Prop :=
  ∀ y : ℝ, 0 < y → y ≤ 1 / 8 → ∀ S : Finset V, Sparse G y S →
    (∃ T ⊆ S, y ^ A₁ * S.card ≤ T.card ∧ Sparse G (y ^ 4) T) ∨
    (∃ β : Blockade S (1 / y) (y ^ A₁ * S.card), β.IsComplete G) ∨
    (∃ X ⊆ S, ∃ Y ⊆ S, Disjoint X Y ∧ y ^ A₁ * S.card ≤ X.card ∧
      (1 - 4 * y) * S.card ≤ Y.card ∧ Anticomplete G X Y)

lemma sqrt_facts {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 2 ^ 16) :
    0 < Real.sqrt y ∧ Real.sqrt y ≤ 1 / 2 ^ 8 ∧ Real.sqrt y ^ 2 = y ∧ 256 * y ≤ Real.sqrt y := by
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0.le
  have hs8 : Real.sqrt y ≤ 1 / 2 ^ 8 := by
    rw [show (1 : ℝ) / 2 ^ 8 = Real.sqrt ((1 / 2 ^ 8) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by linarith [show ((1 : ℝ) / 2 ^ 8) ^ 2 = 1 / 2 ^ 16 by norm_num])
  refine ⟨hs0, hs8, hsq, ?_⟩
  have : 256 * Real.sqrt y ≤ 1 := by linarith [show (256 : ℝ) * (1 / 2 ^ 8) = 1 by norm_num]
  calc 256 * y = (256 * Real.sqrt y) * Real.sqrt y := by rw [mul_assoc, ← pow_two, hsq]
    _ ≤ 1 * Real.sqrt y := mul_le_mul_of_nonneg_right this hs0.le
    _ = Real.sqrt y := one_mul _

omit [Fintype V] in
/-- **Lemma 6.2** (NSS VII Lemma 7.2 for P̄6-free graphs). With `A₁ = 2k` as in Lemma 6.1: for
`y ∈ (0, 2⁻¹⁶]` and `G[S]` `y`-sparse and P̄6-free, (i) some `T ⊆ S` with `|T| ≥ y^{k+1}|S|` is
`y²`-sparse, or (ii) there is a complete or anticomplete `(y^{-1/2}, y^{k+1}|S|)`-blockade. -/
theorem round2 {A₁ k : ℕ} (hA : A₁ = 2 * k) (h61 : Out61 G A₁) {y : ℝ} (hy0 : 0 < y)
    (hy : y ≤ 1 / 2 ^ 16) (S : Finset V) (hsp : Sparse G y S) :
    (∃ T ⊆ S, y ^ (k + 1) * S.card ≤ T.card ∧ Sparse G (y ^ 2) T) ∨
    (∃ β : Blockade S (1 / Real.sqrt y) (y ^ (k + 1) * S.card),
      β.IsComplete G ∨ β.IsAnticomplete G) := by
  obtain ⟨hs0, hs8, hsq, h256⟩ := sqrt_facts hy0 hy
  generalize hsdef : Real.sqrt y = s at hs0 hs8 hsq h256 ⊢
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hy1 : y ≤ 1 := hy.trans (by norm_num)
  have hsA : s ^ A₁ = y ^ k := by rw [hA, pow_mul, hsq]
  -- the case `S = ∅`
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe
    left; exact ⟨∅, subset_refl _, by simp, fun u hu => absurd hu (notMem_empty u)⟩
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hw : 0 < y ^ (k + 1) * S.card := by positivity
  have h5 : 4 * s ≤ 1 / 5 := by linarith [show (4 : ℝ) * (1 / 2 ^ 8) ≤ 1 / 5 by norm_num]
  have hq : 0 ≤ 1 - 4 * s := by linarith
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.findGreatest (SChain G S 0 (y ^ (k + 1) * S.card) (1 - 4 * s))
      S.card := ⟨_, rfl⟩
  have hPn : SChain G S 0 (y ^ (k + 1) * S.card) (1 - 4 * s) n := by
    rw [hn]; exact Nat.findGreatest_spec (Nat.zero_le _) (schain_zero S _ _ _)
  have hmax : ¬ SChain G S 0 (y ^ (k + 1) * S.card) (1 - 4 * s) (n + 1) := fun h => by
    have hb := schain_bound hw h
    rw [hn] at h hb
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hb h
  obtain ⟨B, hsub, hdisj, hspB, hwid, hlast⟩ := hPn
  by_cases hn1 : 1 / s ≤ n
  · -- an anticomplete blockade: outcome (ii)
    right
    refine ⟨⟨n, fun i => B i, hn1, fun i => hsub i i.2.le, fun i => hwid i i.2,
      fun i j hij => hdisj i i.2.le j j.2.le (fun h => hij (Fin.ext h))⟩, Or.inr ?_⟩
    intro i j hij
    rcases lt_or_gt_of_ne (fun e => hij (Fin.ext e)) with h | h
    · exact anticomplete_of_sparseTo_zero (hspB i j h j.2.le)
    · have := anticomplete_of_sparseTo_zero (hspB j i h i.2.le)
      exact fun a ha b hb hab => this b hb a ha (G.adj_symm hab)
  push Not at hn1
  have hns : (n : ℝ) * (4 * s) ≤ 4 := by
    have := (lt_div_iff₀ hs0).1 hn1
    nlinarith
  have hBn : (S.card : ℝ) / 2 ^ 8 ≤ (B n).card := by
    have := pow_one_sub_ge (by linarith) h5 hns
    have h2 := mul_le_mul_of_nonneg_right this hSpos.le
    linarith [show (S.card : ℝ) / 2 ^ 8 = 1 / 256 * S.card by ring]
  have hBnS := hsub n le_rfl
  have hsp' : Sparse G s (B n) := sparse_sub hsp hBnS (by
    have := mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ 256 * y)
    have a2 : 256 * y * ((B n).card : ℝ) ≤ s * (B n).card :=
      mul_le_mul_of_nonneg_right h256 (Nat.cast_nonneg _)
    linarith [show 256 * y * ((S.card : ℝ) / 2 ^ 8) = y * S.card by ring])
  have hwidth : y ^ (k + 1) * S.card ≤ s ^ A₁ * (B n).card := by
    rw [hsA]
    have a1 := mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ y ^ k)
    have a2 : y ^ (k + 1) * (S.card : ℝ) ≤ y ^ k * ((S.card : ℝ) / 2 ^ 8) := by
      have hy8 : y ≤ 1 / 2 ^ 8 := hy.trans (by norm_num)
      have := mul_le_mul_of_nonneg_left hy8 (by positivity : (0 : ℝ) ≤ y ^ k * S.card)
      linarith [show y ^ k * (S.card : ℝ) * y = y ^ (k + 1) * S.card by ring,
        show y ^ k * (S.card : ℝ) * (1 / 2 ^ 8) = y ^ k * ((S.card : ℝ) / 2 ^ 8) by ring]
    linarith
  rcases h61 s hs0 (hs8.trans (by norm_num)) (B n) hsp' with ⟨T, hT, hTc, hTsp⟩ |
      ⟨β, hβ⟩ | ⟨X, hX, Y, hY, hXY, hXc, hYc, hXYa⟩
  · left
    refine ⟨T, hT.trans hBnS, hwidth.trans hTc, ?_⟩
    rwa [show s ^ 4 = y ^ 2 by rw [← hsq]; ring] at hTsp
  · right
    exact ⟨β.mono hBnS le_rfl hwidth, Or.inl fun i j hij => hβ i j hij⟩
  · exfalso
    exact hmax (schain_extend hq hsub hdisj hspB hwid hlast hX hY hXY (hwidth.trans hXc) hYc
      (sparseTo_zero_of_anticomplete hXYa))

end EHP6
