import EHP6.Defs

/-!
# Numerics for Lemma 6.1 (`ε = y^M`, `ℓ = ⌈1/ε⌉`, `m = ⌈ε^N|G|⌉`, `b = ⌈ε²m⌉`)
-/

namespace EHP6

lemma n61_eps {y : ℝ} {M : ℕ} (hy0 : 0 < y) (hy : y ≤ 1 / 8) (hM : 5 ≤ M) :
    0 < y ^ M ∧ y ^ M ≤ 1 / 2 ^ 12 ∧ y ^ M ≤ y ^ 5 ∧ 8 * y ^ M ≤ y ^ 2 := by
  have hy1 : y ≤ 1 := by linarith
  have h5 : y ^ M ≤ y ^ 5 := pow_le_pow_of_le_one hy0.le hy1 hM
  have h4 : y ^ M ≤ y ^ 4 := pow_le_pow_of_le_one hy0.le hy1 (by omega)
  have h4' : y ^ 4 ≤ (1 / 8) ^ 4 := pow_le_pow_left₀ hy0.le hy 4
  refine ⟨by positivity, by linarith [show ((1 : ℝ) / 8) ^ 4 = 1 / 2 ^ 12 by norm_num], h5, ?_⟩
  have h3 : y ^ M ≤ y ^ 3 := pow_le_pow_of_le_one hy0.le hy1 (by omega)
  have : 8 * y ^ 3 ≤ y ^ 2 := by
    have e : y ^ 3 = y ^ 2 * y := by ring
    rw [e]; nlinarith [pow_pos hy0 2]
  linarith

lemma n61_ell {ε : ℝ} {ℓ : ℕ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2 ^ 12) (hℓ : ℓ = ⌈1 / ε⌉₊) :
    1 / ε ≤ ℓ ∧ (ℓ : ℝ) ≤ 2 / ε ∧ 2 ≤ ℓ := by
  have h1 : 1 / ε ≤ ℓ := by rw [hℓ]; exact Nat.le_ceil _
  have hbig : 2 ^ 12 ≤ 1 / ε := by rw [le_div_iff₀ hε0]; rw [le_div_iff₀ (by positivity)] at hε; linarith
  refine ⟨h1, ?_, ?_⟩
  · have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / ε)
    rw [← hℓ] at this
    have e : 2 / ε = 1 / ε + 1 / ε := by ring
    linarith [show (1 : ℝ) ≤ 2 ^ 12 by norm_num]
  · have : (2 : ℝ) ≤ ℓ := by linarith [show (2 : ℝ) ≤ 2 ^ 12 by norm_num]
    exact_mod_cast this

lemma n61_m {ε s : ℝ} {N m : ℕ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : 1 / ε ^ (N + 3) < s)
    (hm : m = ⌈ε ^ N * s⌉₊) :
    ε ^ N * s ≤ m ∧ (m : ℝ) ≤ 2 * (ε ^ N * s) ∧ 1 / ε ^ 3 < m ∧ 0 < m := by
  have h1 : ε ^ N * s ≤ m := by rw [hm]; exact Nat.le_ceil _
  have h2 : 1 / ε ^ 3 < ε ^ N * s := by
    have := mul_lt_mul_of_pos_left hs (pow_pos hε0 N)
    have e : ε ^ N * (1 / ε ^ (N + 3)) = 1 / ε ^ 3 := by
      rw [pow_add]; field_simp
    linarith
  have h3 : (1 : ℝ) ≤ 1 / ε ^ 3 := by
    rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_one₀ hε0.le hε1
  refine ⟨h1, ?_, by linarith, ?_⟩
  · have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ ε ^ N * s)
    rw [← hm] at this; linarith
  · have : (0 : ℝ) < m := by linarith
    exact_mod_cast this

lemma n61_b {ε : ℝ} {m b ℓ : ℕ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2 ^ 12) (hm3 : 1 / ε ^ 3 < m)
    (hℓ2 : (ℓ : ℝ) ≤ 2 / ε) (hℓ0 : 0 < ℓ) (hb : b = ⌈ε ^ 2 * m⌉₊) :
    ε ^ 2 * m ≤ b ∧ (b : ℝ) ≤ 2 * (ε ^ 2 * m) ∧ 1 ≤ b ∧ b ≤ m ∧ (b : ℝ) ≤ (m / 2) / ℓ ∧
      ((ℓ : ℝ) - 1) * (ε ^ 2 * m) ≤ m / 2 := by
  have hε1 : ε ≤ 1 / 16 := hε.trans (by norm_num)
  have hmpos : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm3
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ0
  have h1 : ε ^ 2 * m ≤ b := by rw [hb]; exact Nat.le_ceil _
  have hinv : 2 ^ 12 ≤ 1 / ε := by
    rw [le_div_iff₀ hε0]; rw [le_div_iff₀ (by positivity)] at hε; linarith
  have hεm2 : 1 / ε ≤ ε ^ 2 * m := by
    have := mul_lt_mul_of_pos_left hm3 (pow_pos hε0 2)
    have e : ε ^ 2 * (1 / ε ^ 3) = 1 / ε := by field_simp <;> ring
    linarith
  have hεm1 : 16 ≤ ε * m := by
    have := mul_lt_mul_of_pos_left hm3 hε0
    have e : ε * (1 / ε ^ 3) = (1 / ε) * (1 / ε) := by field_simp <;> ring
    have : (16 : ℝ) ≤ (1 / ε) * (1 / ε) := by nlinarith
    linarith
  have h16 : (16 : ℝ) ≤ ε ^ 2 * m := by linarith [show (16 : ℝ) ≤ 2 ^ 12 by norm_num]
  have hlt := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ ε ^ 2 * m)
  rw [← hb] at hlt
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le (by linarith)
  have hbm : ε ^ 2 * (m : ℝ) ≤ m := by
    have := mul_le_mul_of_nonneg_right hε2 hmpos.le
    linarith
  refine ⟨h1, by linarith, ?_, ?_, ?_, ?_⟩
  · have : (1 : ℝ) ≤ b := by linarith
    exact_mod_cast this
  · rw [hb]; exact Nat.ceil_le.2 hbm
  · rw [le_div_iff₀ hℓr]
    have a1 : (b : ℝ) * ℓ ≤ (ε ^ 2 * m + 1) * (2 / ε) :=
      mul_le_mul hlt.le hℓ2 hℓr.le (by positivity)
    have a2 : (ε ^ 2 * m + 1) * (2 / ε) = 2 * (ε * m) + 2 / ε := by field_simp <;> ring
    have a3 : 2 / ε ≤ m / 8 := by
      rw [div_le_iff₀ hε0]; linarith
    have a4 : 2 * (ε * m) ≤ m / 8 := by
      have := mul_le_mul_of_nonneg_right hε1 hmpos.le
      linarith
    linarith
  · have a1 : ((ℓ : ℝ) - 1) * (ε ^ 2 * m) ≤ (2 / ε) * (ε ^ 2 * m) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have a2 : (2 / ε) * (ε ^ 2 * m) = 2 * (ε * m) := by field_simp <;> ring
    have a4 : 2 * (ε * m) ≤ m / 8 := by
      have := mul_le_mul_of_nonneg_right hε1 hmpos.le
      linarith
    linarith

lemma n61_consts {ε : ℝ} {d ℓ : ℕ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2 ^ 12) (hd : 200 ≤ d)
    (hℓ2 : (ℓ : ℝ) ≤ 2 / ε) :
    2 * ℓ * (2 * ℓ * ε ^ d) ≤ ε ^ (d - 3) ∧ ε ^ (d - 3) ≤ ε ^ 2 * ε ^ (d - 5) ∧
      ε ^ (d - 5) ≤ ε ^ 2 * ε ^ (d - 7) ∧ ε ^ (d - 7) < 1 / 2 ∧ ε ^ (d - 7) ≤ ε ∧
      0 < ε ^ (d - 5) ∧ 0 < ε ^ (d - 7) := by
  have hε1 : ε ≤ 1 / 16 := hε.trans (by norm_num)
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  refine ⟨?_, le_of_eq ?_, le_of_eq ?_, ?_, ?_, by positivity, by positivity⟩
  · have hsq : (ℓ : ℝ) ^ 2 ≤ (2 / ε) ^ 2 := pow_le_pow_left₀ hℓ0 hℓ2 2
    have e1 : ε ^ d = ε ^ (d - 3) * ε ^ 3 := by rw [← pow_add]; congr 1; omega
    have e2 : 2 * ℓ * (2 * ℓ * ε ^ d) = 4 * ((ℓ : ℝ) ^ 2 * ε ^ 3) * ε ^ (d - 3) := by rw [e1]; ring
    have e3 : (2 / ε) ^ 2 * ε ^ 3 = 4 * ε := by field_simp <;> ring
    have h1 : (ℓ : ℝ) ^ 2 * ε ^ 3 ≤ 4 * ε := by
      rw [← e3]; exact mul_le_mul_of_nonneg_right hsq (by positivity)
    rw [e2]
    have h2 : 4 * ((ℓ : ℝ) ^ 2 * ε ^ 3) ≤ 1 := by linarith
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ ε ^ (d - 3))
    linarith
  · rw [← pow_add]; congr 1; omega
  · rw [← pow_add]; congr 1; omega
  · have : ε ^ (d - 7) ≤ ε := by
      calc ε ^ (d - 7) ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le (by linarith) (by omega)
        _ = ε := pow_one ε
    linarith
  · calc ε ^ (d - 7) ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le (by linarith) (by omega)
      _ = ε := pow_one ε

lemma n61_cw {ε s D ℓ m : ℝ} {N : ℕ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (hs : 0 ≤ s)
    (hm : m ≤ 2 * (ε ^ N * s)) (hmN : ε ^ N * s ≤ m) (hD : m / 2 ≤ D) (hℓ : ℓ ≤ 2 / ε)
    (hℓ0 : 0 < ℓ) : ε ^ (N + 3) * s ≤ D / ℓ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have hsq : ℓ ^ 2 ≤ (2 / ε) ^ 2 := pow_le_pow_left₀ hℓ0.le hℓ 2
  have a1 : ε ^ (N + 3) * s * ℓ ^ 2 ≤ ε ^ (N + 3) * s * (2 / ε) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have e : ε ^ (N + 3) * s * (2 / ε) ^ 2 = 4 * ε * (ε ^ N * s) := by
    rw [pow_add]; field_simp <;> ring
  have a2 : 4 * ε * (ε ^ N * s) ≤ 4 * ε * m := mul_le_mul_of_nonneg_left hmN (by positivity)
  have a3 : 4 * ε * m ≤ m / 2 := by
    have hm0 : 0 ≤ m := le_trans (by positivity) hmN
    nlinarith
  linarith

lemma n61_wb {ε s m b : ℝ} {N : ℕ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 ≤ s)
    (hmN : ε ^ N * s ≤ m) (hb : ε ^ 2 * m ≤ b) : ε ^ (N + 3) * s ≤ b := by
  have e : ε ^ (N + 3) * s = ε ^ 3 * (ε ^ N * s) := by ring
  have a1 : ε ^ 3 * (ε ^ N * s) ≤ ε ^ 3 * m := mul_le_mul_of_nonneg_left hmN (by positivity)
  have hm0 : 0 ≤ m := le_trans (by positivity) hmN
  have a2 : ε ^ 3 * m ≤ ε ^ 2 * m := by
    have : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this hm0
  linarith

lemma n61_union {ε s m b ℓ y : ℝ} {N : ℕ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 ≤ s)
    (hℓ : ℓ ≤ 2 / ε) (hℓ0 : 0 ≤ ℓ) (hb : b ≤ 2 * (ε ^ 2 * m)) (hb0 : 0 ≤ b)
    (hm : m ≤ 2 * (ε ^ N * s)) (h8 : 8 * ε ≤ y ^ 2) : ℓ * b ≤ y ^ 2 * s := by
  have a1 : ℓ * b ≤ (2 / ε) * (2 * (ε ^ 2 * m)) := mul_le_mul hℓ hb hb0 (by positivity)
  have e : (2 / ε) * (2 * (ε ^ 2 * m)) = 4 * ε * m := by field_simp <;> ring
  have a2 : 4 * ε * m ≤ 4 * ε * (2 * (ε ^ N * s)) := mul_le_mul_of_nonneg_left hm (by positivity)
  have hN : ε ^ N ≤ 1 := pow_le_one₀ hε0.le hε1
  have a3 : ε ^ N * s ≤ s := by nlinarith
  have a4 : 4 * ε * (2 * (ε ^ N * s)) ≤ 8 * ε * s := by nlinarith
  have a5 : 8 * ε * s ≤ y ^ 2 * s := mul_le_mul_of_nonneg_right h8 hs
  linarith

lemma n61_thr {y κ I ℓ : ℝ} {M : ℕ} (hy0 : 0 < y) (hy1 : y ≤ 1 / 8) (hκ : 0 < κ)
    (hM : 5 / κ + 4 ≤ M) (hℓ : 1 / y ^ M ≤ ℓ) (hI : y * ℓ ≤ I) : 1 / y ^ 5 ≤ I ^ κ := by
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith [show 0 < 5 / κ by positivity]
    exact_mod_cast this
  have hyinv : 1 ≤ 1 / y := by rw [le_div_iff₀ hy0]; linarith
  have h1 : (1 / y) ^ (M - 1) ≤ I := by
    have e : (1 / y) ^ (M - 1) = y * (1 / y ^ M) := by
      have : M = (M - 1) + 1 := by omega
      conv_rhs => rw [this]
      rw [pow_succ, one_div_pow]; field_simp
    rw [e]
    exact (mul_le_mul_of_nonneg_left hℓ hy0.le).trans hI
  have h2 : ((1 / y) ^ (M - 1)) ^ κ ≤ I ^ κ := Real.rpow_le_rpow (by positivity) h1 hκ.le
  have h3 : ((1 / y) ^ (M - 1)) ^ κ = (1 / y) ^ (((M - 1 : ℕ) : ℝ) * κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hMk : (5 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) * κ := by
    rw [Nat.cast_sub hM1, Nat.cast_one]
    have : 5 / κ ≤ (M : ℝ) - 1 := by linarith
    have := mul_le_mul_of_nonneg_right this hκ.le
    rwa [div_mul_cancel₀ _ hκ.ne'] at this
  have h4 : (1 / y) ^ (5 : ℝ) ≤ (1 / y) ^ (((M - 1 : ℕ) : ℝ) * κ) :=
    Real.rpow_le_rpow_of_exponent_le hyinv hMk
  have h5 : (1 / y) ^ (5 : ℝ) = 1 / y ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div_pow]
  rw [← h5]; linarith

lemma n61_final {y s R Y L H : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1 / 8) (hs : 0 ≤ s)
    (hR : (1 - y ^ 2) * s ≤ R) (hsum : R ≤ Y + L + H) (hL : L ≤ y * R) (hH : H ≤ 2 * y * s) :
    (1 - 4 * y) * s ≤ Y := by
  have h1 : (1 - y) * R ≤ Y + H := by nlinarith
  have hy' : 0 ≤ 1 - y := by linarith
  have h2 : (1 - y) * ((1 - y ^ 2) * s) ≤ (1 - y) * R := mul_le_mul_of_nonneg_left hR hy'
  have h3 : (1 - 2 * y) * s ≤ (1 - y) * ((1 - y ^ 2) * s) := by
    have : (1 - 2 * y) ≤ (1 - y) * (1 - y ^ 2) := by nlinarith
    nlinarith
  nlinarith

end EHP6
