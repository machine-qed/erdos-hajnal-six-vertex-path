import EHP6.Defs

/-!
# Numeric facts for the Tooth Lemma (hypotheses: 0 < x ≤ 2⁻²⁰, 2¹⁶ ≤ k ≤ 2/√x)
-/

namespace EHP6

set_option linter.unusedSectionVars false

section
variable {x : ℝ} {k : ℕ} (hx : 0 < x) (hx20 : x ≤ 1 / 2 ^ 20) (hk : 2 ^ 16 ≤ k)
  (hkx : (k : ℝ) ≤ 2 / Real.sqrt x)
include hx hx20 hk hkx

lemma tn_sqrt : Real.sqrt x ≤ 1 / 2 ^ 10 := by
  have h : Real.sqrt (1 / 2 ^ 20) = 1 / 2 ^ 10 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]; norm_num
  rw [← h]
  exact Real.sqrt_le_sqrt hx20

lemma tn_ksqrt : (k : ℝ) * Real.sqrt x ≤ 2 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  rwa [le_div_iff₀ hs] at hkx

lemma tn_k2x : (k : ℝ) ^ 2 * x ≤ 4 := by
  have h := tn_ksqrt hx hx20 hk hkx
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have h0 : 0 ≤ (k : ℝ) * Real.sqrt x := by positivity
  nlinarith

lemma tn_xk : x * k ≤ 1 / 2 ^ 9 := by
  have h := tn_ksqrt hx hx20 hk hkx
  have hs := tn_sqrt hx hx20 hk hkx
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have h0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith

lemma tn_kpos : (2 : ℝ) ^ 16 ≤ k := by exact_mod_cast hk

end

lemma tn_s_gt_one {x n : ℝ} (hx : 0 < x) (hx20 : x ≤ 1 / 2 ^ 20) (hn : 16 / x ^ 3 ≤ n) :
    1 < x ^ 2 * n / 4 := by
  have hinvx : (2 : ℝ) ^ 20 ≤ 1 / x := by
    rw [le_div_iff₀ hx]
    have := mul_le_mul_of_nonneg_left hx20 (show (0 : ℝ) ≤ 2 ^ 20 by positivity)
    norm_num at this ⊢; linarith
  have h1 : 16 / x ≤ x ^ 2 * n := by
    have := mul_le_mul_of_nonneg_left hn (sq_nonneg x)
    have e : x ^ 2 * (16 / x ^ 3) = 16 / x := by field_simp <;> ring
    linarith
  have h2 : (16 : ℝ) / x = 16 * (1 / x) := by ring
  have h3 : (16 : ℝ) * 2 ^ 20 ≤ 16 * (1 / x) := by linarith
  have h4 : (4 : ℝ) < 16 * 2 ^ 20 := by norm_num
  linarith

lemma tn_s_le_t {x n : ℝ} {k : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hk : 0 < k) (hn : 0 ≤ n)
    (hxk : x * k ≤ 1) : x ^ 2 * n / 4 ≤ n / k := by
  rw [div_le_div_iff₀ (by norm_num) hk]
  have h1 := mul_le_mul_of_nonneg_left hxk (show 0 ≤ x * n by positivity)
  have h2 : x * n ≤ n := by nlinarith
  have e : x ^ 2 * n * k = x * n * (x * k) := by ring
  linarith

lemma tn_K0_le {a x k : ℝ} (ha : 15 ≤ a) (ha4 : a ^ 4 < k) (hk2x : k ^ 2 * x ≤ 4) (hx : 0 < x) :
    (a + 1) * x ≤ 1 := by
  have hapos : 0 < a := by linarith
  have h8 : a ^ 8 < k ^ 2 := by
    have : a ^ 8 = (a ^ 4) ^ 2 := by ring
    rw [this]; exact pow_lt_pow_left₀ ha4 (by positivity) (by norm_num)
  have h8x : a ^ 8 * x < 4 := by
    have := mul_lt_mul_of_pos_right h8 hx; linarith
  have h7 : (8 : ℝ) ≤ a ^ 7 := by
    have := pow_le_pow_left₀ (by norm_num) ha 7; norm_num at this; linarith
  have hax0 : 0 ≤ a * x := by positivity
  have e : a ^ 8 * x = (a * x) * a ^ 7 := by ring
  have h1 : (a * x) * 8 ≤ (a * x) * a ^ 7 := mul_le_mul_of_nonneg_left h7 hax0
  have h2 : x ≤ a * x := by nlinarith
  linarith

lemma tn_bound {a x k n K₁ : ℝ} (ha : 15 ≤ a) (ha4 : a ^ 4 < k) (hk : 0 < k) (hx : 0 < x)
    (hx20 : x ≤ 1 / 2 ^ 20) (hn : 0 < n) (hK₁ : 1 / (2 * x) ≤ K₁) :
    a * (n / k) + n / a + (n / (x ^ 2 * n / 4)) * (n / K₁ ^ 4) ≤ n / 4 := by
  have hapos : 0 < a := by linarith
  have t1 : a * (n / k) ≤ n / 3375 := by
    have h3 : (3375 : ℝ) ≤ a ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) ha 3; norm_num at this; linarith
    have h4 : a * 3375 ≤ a ^ 4 := by nlinarith
    have : a * 3375 ≤ k := by linarith
    rw [mul_div_assoc', div_le_div_iff₀ hk (by norm_num)]
    nlinarith
  have t2 : n / a ≤ n / 15 := div_le_div_of_nonneg_left hn.le (by norm_num) ha
  have hK14 : 1 / (16 * x ^ 4) ≤ K₁ ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hK₁ 4
    have e : (1 / (2 * x)) ^ 4 = 1 / (16 * x ^ 4) := by field_simp <;> ring
    linarith
  have hK1pos : 0 < K₁ ^ 4 := lt_of_lt_of_le (by positivity) hK14
  have t3 : (n / (x ^ 2 * n / 4)) * (n / K₁ ^ 4) ≤ 64 * x ^ 2 * n := by
    have hns : n / (x ^ 2 * n / 4) = 4 / x ^ 2 := by
      have := hn.ne'; have := hx.ne'; field_simp <;> ring
    rw [hns]
    have h1 : n / K₁ ^ 4 ≤ n / (1 / (16 * x ^ 4)) :=
      div_le_div_of_nonneg_left hn.le (by positivity) hK14
    have h2 : n / (1 / (16 * x ^ 4)) = 16 * x ^ 4 * n := by field_simp <;> ring
    have h3 : 4 / x ^ 2 * (16 * x ^ 4 * n) = 64 * x ^ 2 * n := by field_simp <;> ring
    calc 4 / x ^ 2 * (n / K₁ ^ 4) ≤ 4 / x ^ 2 * (16 * x ^ 4 * n) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 64 * x ^ 2 * n := h3
  have hx2 : x ^ 2 ≤ 1 / 2 ^ 40 := by
    have := pow_le_pow_left₀ hx.le hx20 2; norm_num at this ⊢; linarith
  have t4 : 64 * x ^ 2 * n ≤ 64 / 2 ^ 40 * n := by
    have := mul_le_mul_of_nonneg_right hx2 hn.le; nlinarith
  have : n / 3375 + n / 15 + 64 / 2 ^ 40 * n ≤ n / 4 := by
    have : (1 : ℝ) / 3375 + 1 / 15 + 64 / 2 ^ 40 ≤ 1 / 4 := by norm_num
    nlinarith
  linarith

lemma tn_L_mass {L a k : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (hk : 0 < k) (hLa : 8 * L * a ≤ k)
    {n : ℝ} (hn : 0 ≤ n) : 2 * L * (n / k) ≤ 3 * n / (4 * a) := by
  rw [show 2 * L * (n / k) = 2 * L * n / k by ring, div_le_div_iff₀ hk (by positivity)]
  nlinarith

lemma tn_La {L a k : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (hk : 0 ≤ k) (hL8 : (8 * L) ^ 4 ≤ k ^ 3)
    (ha4 : a ^ 4 < k) : 8 * L * a ≤ k := by
  have h4 : (8 * L * a) ^ 4 ≤ k ^ 4 := by
    have e : (8 * L * a) ^ 4 = (8 * L) ^ 4 * a ^ 4 := by ring
    rw [e, show k ^ 4 = k ^ 3 * k by ring]
    exact mul_le_mul hL8 ha4.le (by positivity) (by positivity)
  exact le_of_pow_le_pow_left₀ (by norm_num) hk h4

lemma tn_L9 {L k : ℝ} (hL8 : 8 ≤ L) (hnext : k ^ 3 < (8 * (L + 1)) ^ 4) : k ^ 3 ≤ (9 * L) ^ 4 := by
  have h2 : (8 * (L + 1)) ^ 4 ≤ (9 * L) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
  linarith

/-- the width/length facts for Step 3 -/
lemma tn_h3 {x n k K₁ S : ℝ} (hx : 0 < x) (hk : 0 < k) (hn : 0 ≤ n) (hxk : x * k ≤ 4)
    (hK₁ : 0 < K₁) (hK₁x : K₁ ≤ 1 / x) (hS : n / k ≤ S) :
    x ^ 2 * n / 4 ≤ S / K₁ ∧ x ^ 2 * n / k ≤ S / K₁ ^ 2 := by
  have hinv : x ≤ 1 / K₁ := by
    rw [le_div_iff₀ hK₁]; rw [le_div_iff₀ hx] at hK₁x; linarith
  have hS0 : 0 ≤ S := le_trans (by positivity) hS
  constructor
  · have e1 : x ^ 2 * n / 4 ≤ x * (n / k) := by
      rw [show x * (n / k) = x * n / k by ring, div_le_div_iff₀ (by norm_num) hk]
      have h1 := mul_le_mul_of_nonneg_left hxk (show 0 ≤ x * n by positivity)
      have e : x ^ 2 * n * k = x * n * (x * k) := by ring
      linarith
    calc x ^ 2 * n / 4 ≤ x * (n / k) := e1
      _ ≤ x * S := mul_le_mul_of_nonneg_left hS hx.le
      _ ≤ (1 / K₁) * S := mul_le_mul_of_nonneg_right hinv hS0
      _ = S / K₁ := by ring
  · have hsq : x ^ 2 ≤ 1 / K₁ ^ 2 := by
      rw [show 1 / K₁ ^ 2 = (1 / K₁) ^ 2 by ring]; exact pow_le_pow_left₀ hx.le hinv 2
    calc x ^ 2 * n / k = x ^ 2 * (n / k) := by ring
      _ ≤ x ^ 2 * S := mul_le_mul_of_nonneg_left hS (sq_nonneg x)
      _ ≤ (1 / K₁ ^ 2) * S := mul_le_mul_of_nonneg_right hsq hS0
      _ = S / K₁ ^ 2 := by ring

lemma tn_h4 {x n k K' S r : ℝ} (hx : 0 < x) (hk : 1 ≤ k) (hn : 0 ≤ n) (hK' : 0 < K')
    (hK'x : K' ≤ 1 / (x * k)) (hS : n / k ≤ S) (hr : x * S / 4 ≤ r) :
    x ^ 2 * n / 4 ≤ r / K' ∧ x ^ 3 * n / 4 ≤ r / K' ^ 2 := by
  have hkpos : 0 < k := by linarith
  have hxk : 0 < x * k := by positivity
  have hinv : x * k ≤ 1 / K' := by
    rw [le_div_iff₀ hK']; rw [le_div_iff₀ hxk] at hK'x; linarith
  have hr0 : x * (n / k) / 4 ≤ r :=
    le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS hx.le) (by norm_num)) hr
  have hrpos : 0 ≤ r := le_trans (by positivity) hr0
  constructor
  · calc x ^ 2 * n / 4 = (x * (n / k) / 4) * (x * k) := by field_simp <;> ring
      _ ≤ r * (x * k) := mul_le_mul_of_nonneg_right hr0 hxk.le
      _ ≤ r * (1 / K') := mul_le_mul_of_nonneg_left hinv hrpos
      _ = r / K' := by ring
  · have hsq : (x * k) ^ 2 ≤ 1 / K' ^ 2 := by
      rw [show 1 / K' ^ 2 = (1 / K') ^ 2 by ring]; exact pow_le_pow_left₀ hxk.le hinv 2
    have e : (x * (n / k) / 4) * (x * k) ^ 2 = x ^ 3 * n / 4 * k := by field_simp <;> ring
    calc x ^ 3 * n / 4 ≤ x ^ 3 * n / 4 * k := by
          have : 0 ≤ x ^ 3 * n / 4 := by positivity
          nlinarith
      _ = (x * (n / k) / 4) * (x * k) ^ 2 := e.symm
      _ ≤ r * (x * k) ^ 2 := mul_le_mul_of_nonneg_right hr0 (sq_nonneg _)
      _ ≤ r * (1 / K' ^ 2) := mul_le_mul_of_nonneg_left hsq hrpos
      _ = r / K' ^ 2 := by ring

end EHP6
