import EHP6.Defs

/-! Numeric conversions TL1–TL5 → outcome (ii) of Lemma 3.1. Throughout: `0 < x ≤ y ≤ 2⁻⁶⁴`,
`1/y ≤ ℓ ≤ k⁴`, `k ≥ 2¹⁶`, `k²x ≤ 4`, tooth size `Yc ≥ S/k²⁴` and `Yc ≥ x⁸ S`. -/

namespace EHP6

lemma cl_k16 {y ℓ k : ℝ} (hy0 : 0 < y) (hℓ : 1 / y ≤ ℓ) (hk : ℓ ≤ k ^ 4) (hk1 : 1 ≤ k) :
    1 ≤ y * k ^ 16 := by
  have h1 : k ^ 4 ≤ k ^ 16 := pow_le_pow_right₀ hk1 (by norm_num)
  have h2 : 1 / y ≤ k ^ 16 := hℓ.trans (hk.trans h1)
  rw [div_le_iff₀ hy0] at h2; linarith

lemma cl_kx1 {k x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1 / 4) (hk0 : 0 ≤ k) (hk2x : k ^ 2 * x ≤ 4) :
    k * x ≤ 1 := by
  have h : (k * x) ^ 2 ≤ 1 := by
    have : (k * x) ^ 2 = (k ^ 2 * x) * x := by ring
    rw [this]; nlinarith
  nlinarith [sq_nonneg (k * x - 1), show 0 ≤ k * x by positivity]

lemma cl_TL1 {y ℓ k K S Yc x : ℝ} (hy0 : 0 < y) (hℓ : 1 / y ≤ ℓ) (hkℓ : ℓ ≤ k ^ 4)
    (hk1 : 1 ≤ k) (hkK : k ≤ K ^ 4) (hK : K ≤ 1 / x) (hx : 0 < x) (hS : 0 ≤ S)
    (hY : S / k ^ 24 ≤ Yc) (hK0 : 0 < K) :
    1 ≤ y * K ^ 16 ∧ K * x ≤ 1 ∧ S / K ^ 100 ≤ Yc / K ^ 4 := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : k ^ 4 ≤ K ^ 16 := by
      have := pow_le_pow_left₀ (by linarith) hkK 4
      rw [show (K ^ 4) ^ 4 = K ^ 16 by ring] at this; exact this
    have h2 : 1 / y ≤ K ^ 16 := hℓ.trans (hkℓ.trans h1)
    rw [div_le_iff₀ hy0] at h2; linarith
  · rw [le_div_iff₀ hx] at hK; linarith
  · have h1 : k ^ 24 ≤ K ^ 96 := by
      have := pow_le_pow_left₀ (by linarith) hkK 24
      rw [show (K ^ 4) ^ 24 = K ^ 96 by ring] at this; exact this
    have h2 : S / K ^ 96 ≤ Yc :=
      le_trans (div_le_div_of_nonneg_left hS (by positivity) h1) hY
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : S * K ^ 4 = (S / K ^ 96) * K ^ 100 := by field_simp <;> ring
    rw [e]; exact mul_le_mul_of_nonneg_right h2 (by positivity)

lemma cl_TL2 {y ℓ k L S Yc x : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 2 ^ 64) (hℓ : 1 / y ≤ ℓ)
    (hkℓ : ℓ ≤ k ^ 4) (hk : 2 ^ 16 ≤ k) (hk2x : k ^ 2 * x ≤ 4) (hx : 0 < x) (hx1 : x ≤ 1)
    (hL0 : 0 ≤ L) (hL9 : k ^ 3 ≤ (9 * L) ^ 4) (hL8 : (8 * L) ^ 4 ≤ k ^ 3) (hS : 0 ≤ S)
    (hY : S / k ^ 24 ≤ Yc) : 1 ≤ y * L ^ 16 ∧ L * x ≤ 1 ∧ S / L ^ 100 ≤ Yc / (2 * k) := by
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk
  refine ⟨?_, ?_, ?_⟩
  · -- (9L)^16 ≥ k^12 ≥ ℓ^3 ≥ y^{-3}
    have h1 : k ^ 12 ≤ (9 * L) ^ 16 := by
      have := pow_le_pow_left₀ (by positivity) hL9 4
      rw [show (k ^ 3) ^ 4 = k ^ 12 by ring, show ((9 * L) ^ 4) ^ 4 = (9 * L) ^ 16 by ring] at this
      exact this
    have hyℓ : 1 ≤ y * ℓ := by rw [div_le_iff₀ hy0] at hℓ; linarith
    have hyk : 1 ≤ y * k ^ 4 := by nlinarith
    have h2 : 1 ≤ y ^ 3 * k ^ 12 := by
      have : y ^ 3 * k ^ 12 = (y * k ^ 4) ^ 3 := by ring
      rw [this]; exact one_le_pow₀ hyk
    have h3 : 1 ≤ y ^ 3 * (9 * L) ^ 16 := le_trans h2 (mul_le_mul_of_nonneg_left h1 (by positivity))
    have hy2 : y ^ 2 * 9 ^ 16 ≤ 1 := by
      have : y ^ 2 ≤ (1 / 2 ^ 64) ^ 2 := pow_le_pow_left₀ hy0.le hy 2
      have : (1 / 2 ^ 64 : ℝ) ^ 2 * 9 ^ 16 ≤ 1 := by norm_num
      nlinarith
    have e : y ^ 3 * (9 * L) ^ 16 = (y ^ 2 * 9 ^ 16) * (y * L ^ 16) := by ring
    rw [e] at h3
    nlinarith [show 0 ≤ y * L ^ 16 by positivity]
  · -- (8L)^8 x^3 ≤ k^6 x^3 ≤ 64
    have h1 : (8 * L) ^ 8 ≤ k ^ 6 := by
      have := pow_le_pow_left₀ (by positivity) hL8 2
      rw [show ((8 * L) ^ 4) ^ 2 = (8 * L) ^ 8 by ring, show (k ^ 3) ^ 2 = k ^ 6 by ring] at this
      exact this
    have h2 : k ^ 6 * x ^ 3 ≤ 64 := by
      have : k ^ 6 * x ^ 3 = (k ^ 2 * x) ^ 3 := by ring
      rw [this]; have := pow_le_pow_left₀ (by positivity) hk2x 3; norm_num at this; linarith
    have h3 : (L * x) ^ 8 ≤ 1 := by
      have e : (L * x) ^ 8 = ((8 * L) ^ 8 * x ^ 3) * x ^ 5 / 8 ^ 8 := by ring
      rw [e, div_le_one (by positivity)]
      have : (8 * L) ^ 8 * x ^ 3 ≤ 64 := le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) h2
      have : x ^ 5 ≤ 1 := pow_le_one₀ hx.le hx1
      nlinarith [show 0 ≤ (8 * L) ^ 8 * x ^ 3 by positivity]
    by_contra hc; push Not at hc
    have := one_lt_pow₀ hc (show 8 ≠ 0 by norm_num); linarith
  · -- L^100 ≥ 2 k^25
    have h1 : k ^ 75 ≤ (9 * L) ^ 100 := by
      have := pow_le_pow_left₀ (by positivity) hL9 25
      rw [show (k ^ 3) ^ 25 = k ^ 75 by ring, show ((9 * L) ^ 4) ^ 25 = (9 * L) ^ 100 by ring] at this
      exact this
    have h2 : 2 * 9 ^ 100 ≤ k ^ 50 := by
      have := pow_le_pow_left₀ (by positivity) hk 50
      have : (2 * 9 ^ 100 : ℝ) ≤ ((2 : ℝ) ^ 16) ^ 50 := by norm_num
      linarith
    have h3 : 2 * k ^ 25 ≤ L ^ 100 := by
      have e : (9 * L) ^ 100 = 9 ^ 100 * L ^ 100 := by ring
      rw [e] at h1
      have : 2 * k ^ 25 * 9 ^ 100 ≤ k ^ 75 := by
        have e2 : k ^ 75 = k ^ 50 * k ^ 25 := by ring
        rw [e2]; nlinarith [show 0 < k ^ 25 by positivity]
      nlinarith [show (0:ℝ) < 9 ^ 100 by positivity]
    have hL0' : 0 < L ^ 100 := lt_of_lt_of_le (by positivity) h3
    have h4 : S / L ^ 100 ≤ S / (2 * k ^ 25) := div_le_div_of_nonneg_left hS (by positivity) h3
    have h5 : S / (2 * k ^ 25) ≤ Yc / (2 * k) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hY
      nlinarith [show 0 < k by positivity]
    linarith

lemma cl_TL3 {y k K S Yc x : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2 ^ 64) (hk0 : 0 < k)
    (hkx : k * x ≤ 1) (hK1 : 1 / (2 * x) ≤ K) (hK2 : K ≤ 1 / x) (hS : 0 ≤ S)
    (hY : x ^ 8 * S ≤ Yc) : 1 ≤ y * K ^ 16 ∧ K * x ≤ 1 ∧ S / K ^ 100 ≤ x ^ 2 * Yc / k := by
  have hx64 : x ≤ 1 / 2 ^ 64 := hxy.trans hy
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK1
  have hK2x : 1 ≤ 2 * x * K := by rw [div_le_iff₀ (by positivity)] at hK1; linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 1 ≤ (2 * x * K) ^ 16 := one_le_pow₀ hK2x
    have h2 : 2 ^ 16 * x ^ 15 ≤ 1 := by
      have : x ^ 15 ≤ (1 / 2 ^ 64) ^ 15 := pow_le_pow_left₀ hx.le hx64 15
      have : (2 : ℝ) ^ 16 * (1 / 2 ^ 64) ^ 15 ≤ 1 := by norm_num
      nlinarith
    have e : (2 * x * K) ^ 16 = (2 ^ 16 * x ^ 15) * (x * K ^ 16) := by ring
    rw [e] at h1
    have : 1 ≤ x * K ^ 16 := by nlinarith [show 0 ≤ x * K ^ 16 by positivity]
    nlinarith [show 0 ≤ K ^ 16 by positivity]
  · rw [le_div_iff₀ hx] at hK2; linarith
  · have h1 : x ^ 11 * S ≤ x ^ 2 * Yc / k := by
      rw [le_div_iff₀ hk0]
      have : x ^ 11 * S * k = x ^ 2 * (x ^ 8 * S) * (k * x) := by ring
      rw [this]
      calc x ^ 2 * (x ^ 8 * S) * (k * x) ≤ x ^ 2 * (x ^ 8 * S) * 1 :=
            mul_le_mul_of_nonneg_left hkx (by positivity)
        _ ≤ x ^ 2 * Yc := by nlinarith [sq_nonneg x]
    have h2 : S / K ^ 100 ≤ x ^ 11 * S := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : 1 ≤ (2 * x * K) ^ 100 := one_le_pow₀ hK2x
      have h4 : 2 ^ 100 * x ^ 89 ≤ 1 := by
        have : x ^ 89 ≤ (1 / 2 ^ 64) ^ 89 := pow_le_pow_left₀ hx.le hx64 89
        have : (2 : ℝ) ^ 100 * (1 / 2 ^ 64) ^ 89 ≤ 1 := by norm_num
        nlinarith
      have e : (2 * x * K) ^ 100 = (2 ^ 100 * x ^ 89) * (x ^ 11 * K ^ 100) := by ring
      rw [e] at h3
      have : 1 ≤ x ^ 11 * K ^ 100 := by nlinarith [show 0 ≤ x ^ 11 * K ^ 100 by positivity]
      nlinarith
    linarith

lemma cl_TL4 {y k K S Yc x : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2 ^ 64) (hk1 : 1 ≤ k)
    (hk2x : k ^ 2 * x ≤ 4) (hK1 : 1 / (2 * (x * k)) ≤ K) (hK2 : K ≤ 1 / (x * k)) (hS : 0 ≤ S)
    (hY : x ^ 8 * S ≤ Yc) : 1 ≤ y * K ^ 16 ∧ K * x ≤ 1 ∧ S / K ^ 100 ≤ x ^ 3 * Yc / 4 := by
  have hx64 : x ≤ 1 / 2 ^ 64 := hxy.trans hy
  have hk0 : 0 < k := by linarith
  have hxk : 0 < x * k := by positivity
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK1
  have hKxk : 1 ≤ 2 * x * k * K := by
    rw [div_le_iff₀ (by positivity)] at hK1; linarith
  -- K² ≥ 1/(16x)
  have hK2' : 1 ≤ 16 * x * K ^ 2 := by
    have h1 : 1 ≤ (2 * x * k * K) ^ 2 := one_le_pow₀ hKxk
    have e : (2 * x * k * K) ^ 2 = 4 * x * (k ^ 2 * x) * K ^ 2 := by ring
    rw [e] at h1
    nlinarith [show 0 ≤ x * K ^ 2 by positivity]
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 1 ≤ (16 * x * K ^ 2) ^ 8 := one_le_pow₀ hK2'
    have h2 : 16 ^ 8 * x ^ 7 ≤ 1 := by
      have : x ^ 7 ≤ (1 / 2 ^ 64) ^ 7 := pow_le_pow_left₀ hx.le hx64 7
      have : (16 : ℝ) ^ 8 * (1 / 2 ^ 64) ^ 7 ≤ 1 := by norm_num
      nlinarith
    have e : (16 * x * K ^ 2) ^ 8 = (16 ^ 8 * x ^ 7) * (x * K ^ 16) := by ring
    rw [e] at h1
    have : 1 ≤ x * K ^ 16 := by nlinarith [show 0 ≤ x * K ^ 16 by positivity]
    nlinarith [show 0 ≤ K ^ 16 by positivity]
  · have : K * (x * k) ≤ 1 := by rw [le_div_iff₀ hxk] at hK2; linarith
    nlinarith
  · have h1 : x ^ 11 * S / 4 ≤ x ^ 3 * Yc / 4 := by
      have : x ^ 11 * S = x ^ 3 * (x ^ 8 * S) := by ring
      rw [this]; apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hY (by positivity)
    have h2 : S / K ^ 100 ≤ x ^ 11 * S / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h3 : 1 ≤ (16 * x * K ^ 2) ^ 50 := one_le_pow₀ hK2'
      have h4 : 4 * 16 ^ 50 * x ^ 39 ≤ 1 := by
        have : x ^ 39 ≤ (1 / 2 ^ 64) ^ 39 := pow_le_pow_left₀ hx.le hx64 39
        have : (4 : ℝ) * 16 ^ 50 * (1 / 2 ^ 64) ^ 39 ≤ 1 := by norm_num
        nlinarith
      have e : (16 * x * K ^ 2) ^ 50 = (16 ^ 50 * x ^ 39) * (x ^ 11 * K ^ 100) := by ring
      rw [e] at h3
      have hA : 0 < 16 ^ 50 * x ^ 39 := by positivity
      have hB : 4 ≤ x ^ 11 * K ^ 100 := by
        by_contra hc; push Not at hc
        have := mul_lt_mul_of_pos_left hc hA
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hB hS]
    linarith

lemma cl_TL5 {y ℓ k S Yc Y' x : ℝ} (hy0 : 0 < y) (hℓ : 1 / y ≤ ℓ) (hkℓ : ℓ ≤ k ^ 4)
    (hk1 : 1 ≤ k) (hx : 0 < x) (hx1 : x ≤ 1 / 4) (hk2x : k ^ 2 * x ≤ 4) (hS : 0 ≤ S)
    (hY : S / k ^ 24 ≤ Yc) (hY' : Yc / k ≤ Y') :
    1 ≤ y * k ^ 16 ∧ k * x ≤ 1 ∧ S / k ^ 100 ≤ Y' := by
  refine ⟨cl_k16 hy0 hℓ hkℓ hk1, cl_kx1 hx hx1 (by linarith) hk2x, ?_⟩
  have hk0 : 0 < k := by linarith
  have h1 : S / k ^ 100 ≤ S / k ^ 25 :=
    div_le_div_of_nonneg_left hS (by positivity) (pow_le_pow_right₀ hk1 (by norm_num))
  have h2 : S / k ^ 25 ≤ Yc / k := by
    rw [show S / k ^ 25 = (S / k ^ 24) / k by rw [div_div, ← pow_succ]]
    exact div_le_div_of_nonneg_right hY hk0.le
  linarith

end EHP6
