import EHP6.Pair

/-!
# NSS VII Lemma 4.2 (paper Lemma 0.4), by greedy covering
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Lemma 4.2 (greedy covering) -/

omit [Fintype V] [DecidableEq V] in
lemma edgesBetween_eq_sum_left (A B : Finset V) :
    edgesBetween G A B = ∑ a ∈ A, (nbrs G a B).card := by
  unfold edgesBetween nbrs
  rw [card_eq_sum_ones, sum_filter, sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [card_eq_sum_ones, sum_filter]


omit [Fintype V] in
/-- averaging: some vertex of `A` covers an `x`-fraction of `U` -/
lemma exists_good_cover {A U : Finset V} {x : ℝ} (hA : A.Nonempty)
    (hdeg : ∀ b ∈ U, x * A.card ≤ ((nbrs G b A).card : ℝ)) :
    ∃ a ∈ A, x * U.card ≤ ((U.filter (fun b => G.Adj b a)).card : ℝ) := by
  have h1 : (edgesBetween G U A : ℝ) = ∑ a ∈ A, ((U.filter (fun b => G.Adj b a)).card : ℝ) := by
    rw [edgesBetween_eq_sum]; push_cast; rfl
  have h2 : (edgesBetween G U A : ℝ) = ∑ b ∈ U, ((nbrs G b A).card : ℝ) := by
    rw [edgesBetween_eq_sum_left]; push_cast; rfl
  have h3 : ∑ _a ∈ A, x * (U.card : ℝ) ≤ ∑ a ∈ A, ((U.filter (fun b => G.Adj b a)).card : ℝ) := by
    rw [← h1, h2, sum_const, nsmul_eq_mul]
    calc (A.card : ℝ) * (x * U.card) = ∑ _b ∈ U, x * (A.card : ℝ) := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ b ∈ U, ((nbrs G b A).card : ℝ) := sum_le_sum hdeg
  obtain ⟨a, ha, h⟩ := exists_le_of_sum_le hA h3
  exact ⟨a, ha, h⟩

omit [Fintype V] in
lemma greedy_cover {A B : Finset V} {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hA : A.Nonempty)
    (hdeg : ∀ b ∈ B, x * A.card ≤ ((nbrs G b A).card : ℝ)) :
    ∀ t : ℕ, ∃ A' ⊆ A, A'.card ≤ t ∧
      ((B.filter (fun b => ¬ ∃ a ∈ A', G.Adj b a)).card : ℝ) ≤ (1 - x) ^ t * B.card
  | 0 => ⟨∅, empty_subset _, le_rfl, by simp⟩
  | t + 1 => by
    obtain ⟨A', hA'A, hA'c, hU⟩ := greedy_cover hx hx1 hA hdeg t
    obtain ⟨U, hUdef⟩ : ∃ U, U = B.filter (fun b => ¬ ∃ a ∈ A', G.Adj b a) := ⟨_, rfl⟩
    rw [← hUdef] at hU
    obtain ⟨a, haA, ha⟩ := exists_good_cover (G := G) (U := U) hA
      (fun b hb => hdeg b (by rw [hUdef] at hb; exact (mem_filter.1 hb).1))
    have heq : B.filter (fun b => ¬ ∃ a' ∈ insert a A', G.Adj b a') =
        U.filter (fun b => ¬ G.Adj b a) := by
      rw [hUdef, filter_filter]
      apply filter_congr
      intro b _
      simp only [mem_insert, exists_eq_or_imp, not_or]
      tauto
    refine ⟨insert a A', insert_subset haA hA'A, (card_insert_le a A').trans (by omega), ?_⟩
    rw [heq]
    have hsplit := card_filter_add_card_filter_not (s := U) (fun b => G.Adj b a)
    have hs : ((U.filter (fun b => G.Adj b a)).card : ℝ) +
        ((U.filter (fun b => ¬ G.Adj b a)).card : ℝ) = U.card := by exact_mod_cast hsplit
    have h1 : ((U.filter (fun b => ¬ G.Adj b a)).card : ℝ) ≤ (1 - x) * U.card := by linarith
    calc ((U.filter (fun b => ¬ G.Adj b a)).card : ℝ) ≤ (1 - x) * U.card := h1
      _ ≤ (1 - x) * ((1 - x) ^ t * B.card) := mul_le_mul_of_nonneg_left hU (by linarith)
      _ = (1 - x) ^ (t + 1) * B.card := by ring

lemma half_bound {x : ℝ} (hx : 0 < x) (hx2 : x < 1 / 2) :
    (1 - x) ^ ⌊1 / x⌋₊ ≤ 1 / 2 := by
  obtain ⟨t, ht⟩ : ∃ t, t = ⌊1 / x⌋₊ := ⟨_, rfl⟩
  rw [← ht]
  have h1 : 1 / x < t + 1 := by rw [ht]; exact Nat.lt_floor_add_one _
  have ht1 : (1 : ℝ) ≤ t := by
    rw [ht]; exact_mod_cast Nat.le_floor (by rw [le_div_iff₀ hx]; push_cast; linarith)
  have htpos : (0 : ℝ) < t := by linarith
  -- `1 - x ≤ t/(t+1)` and `(1 + 1/t)^t ≥ 2`
  have h2 : 1 - x ≤ t / (t + 1) := by
    have : 1 / (t + 1) < x := by
      rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hx] at h1; linarith
    have e : (t : ℝ) / (t + 1) = 1 - 1 / (t + 1) := by field_simp <;> ring
    linarith
  have h3 : (2 : ℝ) ≤ (1 + 1 / t) ^ t := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / t by
      have : (0 : ℝ) ≤ 1 / t := by positivity
      linarith) t
    rw [mul_one_div_cancel htpos.ne'] at this; linarith
  have h4 : ((t : ℝ) / (t + 1)) ^ t * (1 + 1 / t) ^ t = 1 := by
    rw [← mul_pow]
    have : (t : ℝ) / (t + 1) * (1 + 1 / t) = 1 := by field_simp
    rw [this, one_pow]
  have h5 : ((t : ℝ) / (t + 1)) ^ t ≤ 1 / 2 := by
    have hp : (0 : ℝ) ≤ ((t : ℝ) / (t + 1)) ^ t := by positivity
    nlinarith
  calc (1 - x) ^ t ≤ ((t : ℝ) / (t + 1)) ^ t := pow_le_pow_left₀ (by linarith) h2 t
    _ ≤ 1 / 2 := h5

omit [Fintype V] in
/-- **NSS VII Lemma 4.2** (paper Lemma 0.4), proved. -/
theorem nss_L42_proof (A B : Finset V) (x : ℝ) (hx : 0 < x) (hx2 : x < 1 / 2) (hA : A.Nonempty)
    (hdeg : ∀ b ∈ B, x * A.card ≤ ((nbrs G b A).card : ℝ)) :
    ∃ A' ⊆ A, (A'.card : ℝ) ≤ 1 / x ∧
      (B.card : ℝ) / 2 ≤ ((B.filter (fun b => ∃ a ∈ A', G.Adj b a)).card : ℝ) := by
  obtain ⟨A', hA'A, hA'c, hU⟩ := greedy_cover (G := G) hx (by linarith) hA hdeg ⌊1 / x⌋₊
  refine ⟨A', hA'A, le_trans (by exact_mod_cast hA'c) (Nat.floor_le (by positivity)), ?_⟩
  have hsplit := card_filter_add_card_filter_not (s := B) (fun b => ∃ a ∈ A', G.Adj b a)
  have hs : ((B.filter (fun b => ∃ a ∈ A', G.Adj b a)).card : ℝ) +
      ((B.filter (fun b => ¬ ∃ a ∈ A', G.Adj b a)).card : ℝ) = B.card := by exact_mod_cast hsplit
  have h1 := mul_le_mul_of_nonneg_right (half_bound hx hx2) (Nat.cast_nonneg B.card)
  linarith

end EHP6
