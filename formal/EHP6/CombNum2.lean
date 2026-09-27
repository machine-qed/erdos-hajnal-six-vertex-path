import EHP6.Defs

/-! Numeric conversions for Lemma 3.1 (tooth sizes and the TL1–TL5 → outcome (ii) conversions). -/

namespace EHP6

set_option linter.unusedVariables false

lemma cl_ell64 {y ℓ : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 2 ^ 64) (h : 1 / y ≤ ℓ) : (2 : ℝ) ^ 64 ≤ ℓ := by
  refine le_trans ?_ h
  rw [le_div_iff₀ hy0]
  have := mul_le_mul_of_nonneg_left hy (show (0 : ℝ) ≤ 2 ^ 64 by positivity)
  norm_num at this ⊢; linarith

lemma cl_kx {a x ℓ : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hx1 : x ≤ 1) (h1 : a ^ 4 < ℓ)
    (h2 : ℓ ≤ 1 / x ^ 2) : a + 1 ≤ 2 / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hs1 : Real.sqrt x ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx1
  -- a² < 1/x, so a·√x < 1
  have h3 : a ^ 4 * x ^ 2 < 1 := by
    have := mul_lt_mul_of_pos_right (lt_of_lt_of_le h1 h2) (show 0 < x ^ 2 by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this; linarith
  have h4 : (a * Real.sqrt x) ^ 4 < 1 := by
    have : (a * Real.sqrt x) ^ 4 = a ^ 4 * x ^ 2 := by
      rw [mul_pow, show Real.sqrt x ^ 4 = (Real.sqrt x * Real.sqrt x) ^ 2 by ring, hsx]
    linarith
  have h5 : a * Real.sqrt x < 1 := by
    by_contra hc; push Not at hc
    have := pow_le_pow_left₀ (by norm_num) hc 4; norm_num at this; linarith
  rw [le_div_iff₀ hs]
  nlinarith

lemma cl_tooth_size {x y ℓ S C : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2 ^ 64)
    (hℓ0 : 0 < ℓ) (hℓx : ℓ ≤ 1 / x ^ 2) (hS : 1 / x ^ 18 ≤ S) (hC : y ^ 4 * S / ℓ ^ 2 ≤ C) :
    x ^ 8 * S ≤ C ∧ 16 / x ^ 3 ≤ C := by
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hℓ2 : ℓ ^ 2 ≤ 1 / x ^ 4 := by
    have := pow_le_pow_left₀ hℓ0.le hℓx 2
    rw [show (1 / x ^ 2) ^ 2 = 1 / x ^ 4 by field_simp <;> ring] at this; exact this
  have h1 : x ^ 8 * S ≤ y ^ 4 * S / ℓ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hy4 : x ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hx.le hxy 4
    have : ℓ ^ 2 * x ^ 4 ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hℓ2; linarith
    calc x ^ 8 * S * ℓ ^ 2 = (ℓ ^ 2 * x ^ 4) * (x ^ 4 * S) := by ring
      _ ≤ 1 * (x ^ 4 * S) := mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ y ^ 4 * S := by nlinarith
  refine ⟨h1.trans hC, le_trans ?_ (h1.trans hC)⟩
  -- x⁸ S ≥ x⁸ / x¹⁸ = 1/x¹⁰ ≥ 16/x³
  have hx1 : x ≤ 1 / 2 ^ 64 := hxy.trans hy
  have h2 : 1 / x ^ 10 ≤ x ^ 8 * S := by
    have := mul_le_mul_of_nonneg_left hS (show 0 ≤ x ^ 8 by positivity)
    rw [show x ^ 8 * (1 / x ^ 18) = 1 / x ^ 10 by field_simp <;> ring] at this; exact this
  refine le_trans ?_ h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hx7 : 16 * x ^ 7 ≤ 1 := by
    have : x ^ 7 ≤ x := pow_le_of_le_one hx.le (by linarith [show (1:ℝ) / 2 ^ 64 ≤ 1 by norm_num]) (by norm_num)
    have : x ≤ 1 / 16 := hx1.trans (by norm_num)
    nlinarith
  have : 16 * x ^ 10 = (16 * x ^ 7) * x ^ 3 := by ring
  nlinarith [show 0 < x ^ 3 by positivity]

lemma cl_Ck24 {y ℓ S C k : ℝ} (hy0 : 0 < y) (hℓ : 1 / y ≤ ℓ) (hk : ℓ ≤ k ^ 4) (hS : 0 ≤ S)
    (hC : y ^ 4 * S / ℓ ^ 2 ≤ C) : S / k ^ 24 ≤ C := by
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ
  have hyℓ : 1 ≤ y * ℓ := by rw [div_le_iff₀ hy0] at hℓ; linarith
  have h1 : S / ℓ ^ 6 ≤ y ^ 4 * S / ℓ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 1 ≤ (y * ℓ) ^ 4 := one_le_pow₀ hyℓ
    have e : y ^ 4 * S * ℓ ^ 6 = (y * ℓ) ^ 4 * (S * ℓ ^ 2) := by ring
    rw [e]; nlinarith [show 0 ≤ S * ℓ ^ 2 by positivity]
  have h2 : S / k ^ 24 ≤ S / ℓ ^ 6 := by
    apply div_le_div_of_nonneg_left hS (by positivity)
    have := pow_le_pow_left₀ hℓ0.le hk 6
    rw [show (k ^ 4) ^ 6 = k ^ 24 by ring] at this; exact this
  linarith

end EHP6
