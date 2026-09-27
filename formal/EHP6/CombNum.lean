import EHP6.Defs

/-! Numeric steps of the comb extraction and of Lemma 3.1, isolated to keep contexts small. -/

namespace EHP6

lemma ce_Sy {x y S : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2 ^ 64) (hS : 1 / x ^ 18 ≤ S) :
    2 / y ≤ S := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hx1 : x ≤ 1 / 2 := (hxy.trans hy).trans (by norm_num)
  refine le_trans ?_ hS
  have hx17 : x ^ 17 ≤ 1 / 2 := by
    have : x ^ 17 ≤ x := pow_le_of_le_one hx.le (by linarith) (by norm_num)
    linarith
  rw [div_le_div_iff₀ hy0 (by positivity)]
  have e : x ^ 18 = x * x ^ 17 := by ring
  have : x * x ^ 17 ≤ y * (1 / 2) := mul_le_mul hxy hx17 (by positivity) hy0.le
  linarith

lemma ce_A'le {A' N S y : ℝ} (hN : 0 < N) (hy : 0 < y)
    (h : A' * (y ^ 2 * N / 2) ≤ N * (y ^ 3 * S)) : A' ≤ 2 * y * S := by
  have hy2 : 0 < y ^ 2 * N := by positivity
  have e1 : A' * (y ^ 2 * N / 2) = (A' / 2) * (y ^ 2 * N) := by ring
  have e2 : N * (y ^ 3 * S) = (y * S) * (y ^ 2 * N) := by ring
  rw [e1, e2] at h
  have := le_of_mul_le_mul_right h hy2
  linarith

lemma ce_Acard {S A N A' y : ℝ} (h1 : S ≤ A + (N + A' + 1)) (hN : N ≤ y ^ 3 * S)
    (hA' : A' ≤ 2 * y * S) (hSy : 2 / y ≤ S) (hy : 0 < y) (hy1 : y ≤ 1 / 40) :
    (1 - 3 * y) * S ≤ A := by
  have hyS : 2 ≤ y * S := by rw [div_le_iff₀ hy] at hSy; linarith
  have hy2 : y ^ 2 ≤ 1 / 2 := by nlinarith
  have hS0 : 0 ≤ S := by nlinarith
  have h3 : y ^ 3 * S ≤ (y * S) / 2 := by
    have : y ^ 3 * S = y ^ 2 * (y * S) := by ring
    rw [this]; nlinarith
  linarith

lemma ce_bad {Bad A N' x : ℝ} (hN' : 0 < N') (hx : 0 < x)
    (h : Bad * (x * N') ≤ N' * (x ^ 2 * A)) : Bad ≤ x * A := by
  have hxN : 0 < x * N' := by positivity
  have e : N' * (x ^ 2 * A) = (x * A) * (x * N') := by ring
  rw [e] at h
  exact le_of_mul_le_mul_right h hxN

lemma ce_final {A S Yc x y : ℝ} (hYc : (1 - x) * A ≤ Yc) (hA : (1 - 3 * y) * S ≤ A)
    (hxy : x ≤ y) (hx : 0 < x) (hS : 0 ≤ S) (hy1 : y ≤ 1 / 40) : (1 - 4 * y) * S ≤ Yc := by
  have h1 : (1 - x) * ((1 - 3 * y) * S) ≤ (1 - x) * A :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : (1 - 4 * y) * S ≤ (1 - x) * ((1 - 3 * y) * S) := by
    have : (1 - x) * ((1 - 3 * y) * S) - (1 - 4 * y) * S = (y - x + 3 * x * y) * S := by ring
    have : 0 ≤ (y - x + 3 * x * y) * S := mul_nonneg (by nlinarith) hS
    linarith
  linarith

lemma ce_AB' {aB aN N B y : ℝ} (h1 : aB ≤ aN) (h2 : aN < y ^ 2 * N / 2) (h3 : N / 2 ≤ B)
    (hy : 0 ≤ y) : aB ≤ y ^ 2 * B := by
  have : y ^ 2 * N / 2 ≤ y ^ 2 * B := by
    have := mul_le_mul_of_nonneg_left h3 (sq_nonneg y); linarith
  linarith

lemma ce_ell {B ℓ y : ℝ} (hB : 0 < B) (hℓ : 1 ≤ ℓ) (hy : 0 < y) (h : B / ℓ ^ 2 ≤ y ^ 2 * B) :
    1 / y ≤ ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  have h2 : 1 ≤ y ^ 2 * ℓ ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at h
    have : B * 1 ≤ B * (y ^ 2 * ℓ ^ 2) := by linarith
    exact le_of_mul_le_mul_left this hB
  have h3 : 1 ≤ y * ℓ := by
    have : (y * ℓ) ^ 2 = y ^ 2 * ℓ ^ 2 := by ring
    nlinarith [show 0 ≤ y * ℓ by positivity]
  rw [div_le_iff₀ hy]; linarith

end EHP6
