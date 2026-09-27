import EHP6.Defs

/-!
# Tooth Lemma, Step 1: the antichain bound (counting part)
-/

namespace EHP6

open Finset

lemma inv_cube_le_tele (K : ℕ) (hK : 2 ≤ K) :
    (1 : ℝ) / (K : ℝ) ^ 3 ≤ 1 / ((K : ℝ) - 1) - 1 / (K : ℝ) := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < K := by linarith
  have : 1 / ((K : ℝ) - 1) - 1 / (K : ℝ) = 1 / (((K : ℝ) - 1) * K) := by
    field_simp <;> ring
  rw [this]
  apply one_div_le_one_div_of_le (by positivity)
  have e1 : ((K : ℝ) - 1) * K ≤ (K : ℝ) * K := by nlinarith
  have e2 : (K : ℝ) * K ≤ (K : ℝ) ^ 3 := by nlinarith
  linarith

lemma sum_inv_cube_tele (a : ℕ) (ha : 2 ≤ a) (c : ℕ) (hc : a ≤ c) :
    ∑ K ∈ Ico a c, (1 : ℝ) / (K : ℝ) ^ 3 ≤ 1 / ((a : ℝ) - 1) - 1 / ((c : ℝ) - 1) := by
  induction c, hc using Nat.le_induction with
  | base => simp
  | succ c hc ih =>
    rw [sum_Ico_succ_top hc]
    have h := inv_cube_le_tele c (ha.trans hc)
    have : ((c + 1 : ℕ) : ℝ) - 1 = c := by push_cast; ring
    rw [this]; linarith

/-- `Σ_{K ∈ [a, b)} 1/K³ ≤ 1/(a−1)` for `a ≥ 2` -/
lemma sum_inv_cube_le (a b : ℕ) (ha : 2 ≤ a) :
    ∑ K ∈ Ico a b, (1 : ℝ) / (K : ℝ) ^ 3 ≤ 1 / ((a : ℝ) - 1) := by
  have ha' : (1 : ℝ) ≤ (a : ℝ) - 1 := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  by_cases hab : a ≤ b
  · have h := sum_inv_cube_tele a ha b hab
    have hb : (0 : ℝ) ≤ 1 / ((b : ℝ) - 1) := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast ha.trans hab
      apply div_nonneg zero_le_one; linarith
    linarith
  · rw [Ico_eq_empty (by omega), sum_empty]
    exact div_nonneg zero_le_one (by linarith)

/-- **Antichain bound.** If for every integer `K ∈ [K₀, K₁]` fewer than `K` members of `𝒜` have size at
least `n/K⁴`, and all sizes are at most `M`, then the total size is at most
`(K₀−1)M + n/(K₀−1) + |𝒜|·n/K₁⁴`. -/
lemma antichain_mass {α : Type} [DecidableEq α] (𝒜 : Finset (Finset α)) (n M : ℝ) (K₀ K₁ : ℕ)
    (hK₀ : 2 ≤ K₀) (hK : K₀ ≤ K₁) (hn : 0 ≤ n) (hM0 : 0 ≤ M)
    (hM : ∀ A ∈ 𝒜, (A.card : ℝ) ≤ M)
    (hfew : ∀ K : ℕ, K₀ ≤ K → K ≤ K₁ →
      ((𝒜.filter (fun A => n / (K : ℝ) ^ 4 ≤ A.card)).card : ℝ) < K) :
    ∑ A ∈ 𝒜, (A.card : ℝ) ≤ ((K₀ : ℝ) - 1) * M + n / ((K₀ : ℝ) - 1) + 𝒜.card * (n / (K₁ : ℝ) ^ 4) := by
  classical
  set t : ℕ → ℝ := fun K => n / (K : ℝ) ^ 4 with ht
  have tnn : ∀ K, 0 ≤ t K := fun K => div_nonneg hn (by positivity)
  let f : Finset α → ℝ := fun A =>
    (if t K₀ ≤ A.card then M else 0) +
    ∑ K ∈ Ico K₀ K₁, (if t (K + 1) ≤ A.card then t K else 0) + t K₁
  -- pointwise bound
  have point : ∀ A ∈ 𝒜, (A.card : ℝ) ≤ f A := by
    intro A hA
    have hsum_nn : 0 ≤ ∑ K ∈ Ico K₀ K₁, (if t (K + 1) ≤ A.card then t K else 0) :=
      sum_nonneg fun K _ => by split_ifs <;> [exact tnn K; exact le_rfl]
    by_cases hbig : t K₀ ≤ A.card
    · simp only [f, if_pos hbig]; linarith [hM A hA, tnn K₁]
    by_cases hsmall : (A.card : ℝ) < t K₁
    · simp only [f, if_neg hbig]; linarith
    push Not at hbig hsmall
    -- find K ∈ [K₀, K₁) with t (K+1) ≤ |A| < t K
    let S := (Icc K₀ K₁).filter (fun K => (A.card : ℝ) < t K)
    have hSne : S.Nonempty := ⟨K₀, mem_filter.2 ⟨mem_Icc.2 ⟨le_rfl, hK⟩, hbig⟩⟩
    set K := S.max' hSne with hKdef
    have hKS : K ∈ S := max'_mem S hSne
    obtain ⟨hKI, hKlt⟩ := mem_filter.1 hKS
    obtain ⟨hK0K, hKK1⟩ := mem_Icc.1 hKI
    have hKne : K ≠ K₁ := fun e => by rw [e] at hKlt; linarith
    have hK1 : K + 1 ≤ K₁ := by omega
    have hnext : t (K + 1) ≤ A.card := by
      by_contra hc
      push Not at hc
      have : K + 1 ∈ S := mem_filter.2 ⟨mem_Icc.2 ⟨by omega, hK1⟩, hc⟩
      have := le_max' S (K + 1) this
      omega
    have hmem : K ∈ Ico K₀ K₁ := mem_Ico.2 ⟨hK0K, by omega⟩
    have hsingle := single_le_sum (f := fun K => if t (K + 1) ≤ (A.card : ℝ) then t K else 0)
      (fun K _ => by split_ifs <;> [exact tnn K; exact le_rfl]) hmem
    simp only [if_pos hnext] at hsingle
    simp only [f, if_neg (not_le.2 hbig)]
    linarith [tnn K₁]
  -- sum the pointwise bound
  have hsum : ∑ A ∈ 𝒜, (A.card : ℝ) ≤ ∑ A ∈ 𝒜, f A := sum_le_sum point
  have e1 : ∑ A ∈ 𝒜, (if t K₀ ≤ (A.card : ℝ) then M else 0) =
      ((𝒜.filter (fun A => t K₀ ≤ A.card)).card : ℝ) * M := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have e2 : ∑ A ∈ 𝒜, ∑ K ∈ Ico K₀ K₁, (if t (K + 1) ≤ (A.card : ℝ) then t K else 0) =
      ∑ K ∈ Ico K₀ K₁, t K * ((𝒜.filter (fun A => t (K + 1) ≤ A.card)).card : ℝ) := by
    rw [sum_comm]
    refine sum_congr rfl fun K _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have split : ∑ A ∈ 𝒜, f A = ((𝒜.filter (fun A => t K₀ ≤ A.card)).card : ℝ) * M +
      ∑ K ∈ Ico K₀ K₁, t K * ((𝒜.filter (fun A => t (K + 1) ≤ A.card)).card : ℝ) +
      𝒜.card * t K₁ := by
    simp only [f, sum_add_distrib, e1, e2, sum_const, nsmul_eq_mul]
  have c0 : (((𝒜.filter (fun A => t K₀ ≤ A.card)).card : ℕ) : ℝ) ≤ (K₀ : ℝ) - 1 := by
    have h := hfew K₀ le_rfl hK
    have : (𝒜.filter (fun A => t K₀ ≤ A.card)).card < K₀ := Nat.cast_lt.mp h
    have : (𝒜.filter (fun A => t K₀ ≤ A.card)).card ≤ K₀ - 1 := by omega
    have : (((𝒜.filter (fun A => t K₀ ≤ A.card)).card : ℕ) : ℝ) ≤ ((K₀ - 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at this; simpa using this
  have cK : ∀ K ∈ Ico K₀ K₁,
      t K * (((𝒜.filter (fun A => t (K + 1) ≤ A.card)).card : ℕ) : ℝ) ≤ n * (1 / (K : ℝ) ^ 3) := by
    intro K hK'
    obtain ⟨h1, h2⟩ := mem_Ico.1 hK'
    have h := hfew (K + 1) (by omega) (by omega)
    have : (𝒜.filter (fun A => t (K + 1) ≤ A.card)).card < K + 1 := by
      exact Nat.cast_lt.mp h
    have hc : (((𝒜.filter (fun A => t (K + 1) ≤ A.card)).card : ℕ) : ℝ) ≤ K := by
      exact_mod_cast (show (𝒜.filter (fun A => t (K + 1) ≤ A.card)).card ≤ K by omega)
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    calc t K * (((𝒜.filter (fun A => t (K + 1) ≤ A.card)).card : ℕ) : ℝ) ≤ t K * K :=
          mul_le_mul_of_nonneg_left hc (tnn K)
      _ = n * (1 / (K : ℝ) ^ 3) := by simp only [ht]; field_simp <;> ring
  have hsumK : ∑ K ∈ Ico K₀ K₁, t K * (((𝒜.filter (fun A => t (K + 1) ≤ A.card)).card : ℕ) : ℝ)
      ≤ n / ((K₀ : ℝ) - 1) := by
    calc _ ≤ ∑ K ∈ Ico K₀ K₁, n * (1 / (K : ℝ) ^ 3) := sum_le_sum cK
      _ = n * ∑ K ∈ Ico K₀ K₁, (1 / (K : ℝ) ^ 3) := by rw [mul_sum]
      _ ≤ n * (1 / ((K₀ : ℝ) - 1)) := mul_le_mul_of_nonneg_left (sum_inv_cube_le K₀ K₁ hK₀) hn
      _ = n / ((K₀ : ℝ) - 1) := by ring
  rw [split] at hsum
  have h0 := mul_le_mul_of_nonneg_right c0 hM0
  have h3 : (𝒜.card : ℝ) * t K₁ = 𝒜.card * (n / (K₁ : ℝ) ^ 4) := rfl
  linarith

end EHP6
