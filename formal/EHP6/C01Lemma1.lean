import EHP6.C01EH

/-!
# Lemma 8.1 (paper; analogue of NSS VII Lemma 7.3)
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
lemma sparse_mono_param {a b : ℝ} {F : Finset V} (h : Sparse G a F) (hab : a ≤ b) :
    Sparse G b F := sparse_sub h subset_rfl (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _))

omit [Fintype V] in
lemma restricted_single (x : ℝ) (hx : 0 ≤ x) (S : Finset V) (hS : S.Nonempty) :
    ∃ F ⊆ S, 1 ≤ (F.card : ℝ) ∧ Restricted G x F := by
  obtain ⟨v, hv⟩ := hS
  refine ⟨{v}, singleton_subset_iff.2 hv, by simp, Or.inl fun u hu => ?_⟩
  rw [mem_singleton.1 hu]
  have : nbrs G v {v} = ∅ := by
    apply filter_eq_empty_iff.2; intro w hw; rw [mem_singleton.1 hw]; exact G.irrefl
  rw [this, card_empty, Nat.cast_zero]; positivity

lemma l1_kbounds {x y : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hxy : x ≤ y) (hy : y ≤ 1 / 4) :
    2 ≤ (⌈1 / Real.sqrt y⌉₊ : ℝ) ∧ (⌈1 / Real.sqrt y⌉₊ : ℝ) * x ≤ 1 ∧
      1 / (⌈1 / Real.sqrt y⌉₊ : ℝ) ^ 2 ≤ y := by
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0.le
  have hs2 : Real.sqrt y ≤ 1 / 2 := by
    rw [show (1 : ℝ) / 2 = Real.sqrt ((1 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num])
  have hk1 : 1 / Real.sqrt y ≤ (⌈1 / Real.sqrt y⌉₊ : ℝ) := Nat.le_ceil _
  have hk2 : (⌈1 / Real.sqrt y⌉₊ : ℝ) < 1 / Real.sqrt y + 1 := Nat.ceil_lt_add_one (by positivity)
  have hinv2 : 2 ≤ 1 / Real.sqrt y := by rw [le_div_iff₀ hs0]; linarith
  have hsx : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsxsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hsx2 : Real.sqrt x ≤ 1 / 2 := by
    rw [show (1 : ℝ) / 2 = Real.sqrt ((1 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num])
  refine ⟨by linarith, ?_, ?_⟩
  · -- `k ≤ 2/√y ≤ 2/√x`, and `(2/√x)·x = 2√x ≤ 1`
    have a1 : (⌈1 / Real.sqrt y⌉₊ : ℝ) ≤ 2 / Real.sqrt y := by
      have : 1 ≤ 1 / Real.sqrt y := by linarith
      linarith [show 2 / Real.sqrt y = 1 / Real.sqrt y + 1 / Real.sqrt y by ring]
    have a2 : 2 / Real.sqrt y ≤ 2 / Real.sqrt x := div_le_div_of_nonneg_left (by norm_num) hsx0 hsx
    have a3 : 2 / Real.sqrt x * x = 2 * Real.sqrt x := by
      calc 2 / Real.sqrt x * x = 2 / Real.sqrt x * Real.sqrt x ^ 2 := by rw [hsxsq]
        _ = 2 * Real.sqrt x := by rw [pow_two, ← mul_assoc, div_mul_cancel₀ _ hsx0.ne']
    have := mul_le_mul_of_nonneg_right (a1.trans a2) hx0.le
    linarith
  · have hkpos : (0 : ℝ) < (⌈1 / Real.sqrt y⌉₊ : ℝ) := by linarith
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ Real.sqrt y * (⌈1 / Real.sqrt y⌉₊ : ℝ) := by
      rw [div_le_iff₀ hs0] at hk1; linarith
    have h2 : (1 : ℝ) ≤ (Real.sqrt y * (⌈1 / Real.sqrt y⌉₊ : ℝ)) ^ 2 := one_le_pow₀ this
    rw [mul_pow, hsq] at h2; linarith

lemma l1_width {y k s f : ℝ} {a t A : ℕ} (hy0 : 0 < y) (hk : 1 ≤ k) (hky : 1 / k ^ 2 ≤ y)
    (hA : 2 * (a + t) ≤ A) (hf : y ^ t * s ≤ f) (hs : 0 ≤ s) : s / k ^ A ≤ y ^ a * f := by
  have hk0 : 0 < k := by linarith
  have h1 : (1 / k ^ 2) ^ (a + t) ≤ y ^ (a + t) := pow_le_pow_left₀ (by positivity) hky _
  have h2 : 1 / k ^ A ≤ (1 / k ^ 2) ^ (a + t) := by
    rw [one_div_pow, ← pow_mul]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_right₀ hk hA
  have h3 : y ^ (a + t) * s ≤ y ^ a * f := by
    rw [pow_add, mul_assoc]; exact mul_le_mul_of_nonneg_left hf (by positivity)
  have h4 : s / k ^ A = 1 / k ^ A * s := by ring
  rw [h4]
  have := mul_le_mul_of_nonneg_right (h2.trans h1) hs
  linarith

set_option maxHeartbeats 1000000 in
/-- **Lemma 8.1.** From Crux (C): there is `A` such that for every `x ∈ (0, ½)` and every
P̄6-free `G[S]`, either some `F ⊆ S` with `|F| ≥ x^A|S|` is `x`-restricted, or `G[S]` has a complete or
anticomplete `(k, |S|/k^A)`-blockade for some integer `k ∈ [2, 1/x]`. -/
theorem c01_lemma1 (hRodl : RodlCoP6) (hP : NssPath6) {a : ℕ} (hcrux : CruxC a) : ∃ A : ℕ, 1 ≤ A ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Free H P6ᶜ → ∀ x : ℝ, 0 < x → x < 1 / 2 → ∀ S : Finset W,
        (∃ F ⊆ S, x ^ A * S.card ≤ F.card ∧ Restricted H x F) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) * x ≤ 1 ∧
          ∃ β : Blockade S k (S.card / (k : ℝ) ^ A), β.IsComplete H ∨ β.IsAnticomplete H) := by
  obtain ⟨δ, hδ0, hR⟩ := hRodl (1 / 2 ^ 17) (by norm_num) (by norm_num)
  obtain ⟨t₀, ht₀⟩ := exists_pow_lt_of_lt_one hδ0 (by norm_num : (1 : ℝ) / 2 ^ 17 < 1)
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (2 / ((1 / 360) ^ 2 * δ)) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨t, ht⟩ : ∃ t, t = t₀ + a + 1 := ⟨_, rfl⟩
  have hct : ((1 : ℝ) / 2 ^ 17) ^ t ≤ δ :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)).trans ht₀.le
  have hηδ : 0 < (1 / 360 : ℝ) ^ 2 * δ := by positivity
  have hL' : 2 ≤ (1 / 360) ^ 2 * δ * 2 ^ L := by
    rw [div_lt_iff₀ hηδ] at hL; linarith
  refine ⟨2 * (a + t) + L, by omega, fun W _ _ H _ hfree x hx0 hx S => ?_⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * (a + t) + L := ⟨_, rfl⟩
  rw [← hA]
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hx1 : x ≤ 1 := by linarith
  -- small `S`
  by_cases hsmall : (S.card : ℝ) < 1 / x ^ A
  · left
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · subst hSe
      exact ⟨∅, subset_rfl, by simp, Or.inl fun v hv => absurd hv (notMem_empty v)⟩
    obtain ⟨F, hF, hF1, hFr⟩ := restricted_single (G := H) x hx0.le S hSne
    refine ⟨F, hF, ?_, hFr⟩
    rw [lt_div_iff₀ (by positivity)] at hsmall; linarith
  push Not at hsmall
  have h2A : (2 : ℝ) ^ A ≤ S.card := by
    have h2x : (2 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
    have : (2 : ℝ) ^ A ≤ (1 / x) ^ A := pow_le_pow_left₀ (by norm_num) h2x A
    rw [one_div_pow] at this; linarith
  have h2L : (2 : ℝ) ^ L ≤ 2 ^ A := pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨F₀, hF₀S, hF₀c, hF₀r⟩ := hR W H hfree S
  by_cases hxc : 1 / 2 ^ 17 ≤ x
  · -- `F₀` is already `x`-restricted
    left
    refine ⟨F₀, hF₀S, le_trans ?_ hF₀c, hF₀r.imp (fun h => sparse_mono_param (G := H) h hxc)
      (fun h => sparse_mono_param (G := Hᶜ) h hxc)⟩
    apply mul_le_mul_of_nonneg_right _ hS0
    have a1 : x ^ A ≤ (1 / 2) ^ A := pow_le_pow_left₀ hx0.le hx.le A
    have a2 : ((1 : ℝ) / 2) ^ A * 2 ^ A = 1 := by rw [← mul_pow]; norm_num
    have a3 : (1 : ℝ) ≤ δ * 2 ^ A := by
      have : (1 / 360 : ℝ) ^ 2 * δ * 2 ^ L ≤ δ * 2 ^ A := by
        have b1 : (1 / 360 : ℝ) ^ 2 * δ ≤ δ := by nlinarith
        exact mul_le_mul b1 h2L (by positivity) hδ0.le
      linarith
    nlinarith
  push Not at hxc
  rcases hF₀r with hsp | hspc
  swap
  · -- the complement of `F₀` is sparse: a complete pair of blocks
    right
    have hnot := compl_not_contains hfree F₀
    have hspc' : Sparse Hᶜ ((1 / 360) ^ 2) F₀ := sparse_mono_param (G := Hᶜ) hspc (by norm_num)
    obtain ⟨β, hβ⟩ := hP (1 / 360) (by norm_num) le_rfl W Hᶜ F₀ hspc' hnot
    have hwid : (S.card : ℝ) / (2 : ℕ) ^ A ≤ (⌊((1 : ℝ) / 360) ^ 2 * F₀.card⌋₊ : ℝ) := by
      have hηF : (1 / 360 : ℝ) ^ 2 * δ * S.card ≤ (1 / 360) ^ 2 * F₀.card := by
        have := mul_le_mul_of_nonneg_left hF₀c (by positivity : (0 : ℝ) ≤ (1 / 360) ^ 2)
        linarith [show (1 / 360 : ℝ) ^ 2 * (δ * S.card) = (1 / 360) ^ 2 * δ * S.card by ring]
      have hηδA : 2 ≤ (1 / 360 : ℝ) ^ 2 * δ * 2 ^ A :=
        hL'.trans (mul_le_mul_of_nonneg_left h2L hηδ.le)
      have h1 : 1 ≤ (1 / 360 : ℝ) ^ 2 * F₀.card := by
        have := mul_le_mul_of_nonneg_left h2A hηδ.le
        nlinarith
      have h2 := floor_half h1
      push_cast
      rw [div_le_iff₀ (by positivity)]
      have h3 : 2 * (S.card : ℝ) ≤ (1 / 360) ^ 2 * δ * 2 ^ A * S.card :=
        mul_le_mul_of_nonneg_right hηδA hS0
      have h4 : (1 / 360 : ℝ) ^ 2 * δ * S.card / 2 ≤ (⌊((1 : ℝ) / 360) ^ 2 * F₀.card⌋₊ : ℝ) := by
        linarith
      have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ 2 ^ A)
      linarith [show (1 / 360 : ℝ) ^ 2 * δ * S.card / 2 * 2 ^ A =
        (1 / 360) ^ 2 * δ * 2 ^ A * S.card / 2 by ring]
    refine ⟨2, le_rfl, by push_cast; linarith, ⟨β.m, β.B, le_trans (by norm_num) β.len,
      fun i => (β.sub i).trans hF₀S, fun i => hwid.trans (β.wid i), β.disj⟩, Or.inl ?_⟩
    intro i j hij a ha b hb
    have hab : a ≠ b := fun e => disjoint_left.1 (β.disj i j hij) ha (e ▸ hb)
    by_contra hn
    exact hβ i j hij a ha b hb ((SimpleGraph.compl_adj H a b).2 ⟨hab, hn⟩)
  -- `F₀` is sparse: the discretized minimal scale `y_j = c₀^{2^j}`
  obtain ⟨Nb, hNb⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < x ^ 2)
    (by norm_num : (1 : ℝ) / 2 ^ 17 < 1)
  let Q : ℕ → Prop := fun j => x ^ 2 ≤ ((1 : ℝ) / 2 ^ 17) ^ (2 ^ j) ∧ ∃ F ⊆ S,
    Sparse H (((1 : ℝ) / 2 ^ 17) ^ (2 ^ j)) F ∧ (((1 : ℝ) / 2 ^ 17) ^ (2 ^ j)) ^ t * S.card ≤ F.card
  have hbound : ∀ j, Q j → j ≤ Nb := by
    intro j hj
    by_contra hjN; push Not at hjN
    have h1 : ((1 : ℝ) / 2 ^ 17) ^ (2 ^ j) ≤ (1 / 2 ^ 17) ^ Nb :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hjN.le.trans (Nat.lt_pow_self (by norm_num : 1 < 2) : j < 2 ^ j).le)
    linarith [hj.1]
  have hQ0 : Q 0 := by
    refine ⟨?_, F₀, hF₀S, ?_, ?_⟩ <;> simp only [pow_zero, pow_one]
    · nlinarith
    · exact hsp
    · exact le_trans (mul_le_mul_of_nonneg_right hct hS0) hF₀c
  obtain ⟨j, hj⟩ : ∃ j, j = Nat.findGreatest Q Nb := ⟨_, rfl⟩
  have hQj : Q j := by rw [hj]; exact Nat.findGreatest_spec (Nat.zero_le _) hQ0
  have hQj1 : ¬ Q (j + 1) := fun h => by
    have hb := hbound _ h
    rw [hj] at h hb
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hb h
  obtain ⟨hxj, F, hFS, hFsp, hFc⟩ := hQj
  have hsq : ((1 : ℝ) / 2 ^ 17) ^ (2 ^ (j + 1)) = (((1 : ℝ) / 2 ^ 17) ^ (2 ^ j)) ^ 2 := by
    rw [← pow_mul, ← pow_succ]
  have hyc : ((1 : ℝ) / 2 ^ 17) ^ (2 ^ j) ≤ 1 / 2 ^ 17 := by
    calc ((1 : ℝ) / 2 ^ 17) ^ (2 ^ j) ≤ (1 / 2 ^ 17) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.one_le_two_pow)
      _ = 1 / 2 ^ 17 := pow_one _
  generalize hydef : ((1 : ℝ) / 2 ^ 17) ^ (2 ^ j) = y at hxj hFsp hFc hsq hyc
  have hy0 : 0 < y := by rw [← hydef]; positivity
  by_cases hxy : x ≤ y
  · -- Crux (C) applies to `F`
    rcases hcrux W H hfree y hy0 (hyc.trans (by norm_num)) F hFsp with ⟨T, hTF, hTc, hTsp⟩ |
        ⟨β, hβ⟩
    · exfalso
      apply hQj1
      refine ⟨?_, T, hTF.trans hFS, ?_, ?_⟩ <;> rw [hsq]
      · exact pow_le_pow_left₀ hx0.le hxy 2
      · exact hTsp
      · -- `(y²)^t |S| ≤ y^{a+t}|S| ≤ y^a |F| ≤ |T|`
        have h1 : (y ^ 2) ^ t ≤ y ^ (a + t) := by
          rw [← pow_mul]
          exact pow_le_pow_of_le_one hy0.le (hyc.trans (by norm_num)) (by omega)
        have h2 : y ^ (a + t) * S.card ≤ y ^ a * F.card := by
          rw [pow_add, mul_assoc]; exact mul_le_mul_of_nonneg_left hFc (by positivity)
        have := mul_le_mul_of_nonneg_right h1 hS0
        linarith
    · right
      obtain ⟨hk2, hkx, hky⟩ := l1_kbounds hx0 (by linarith) hxy (hyc.trans (by norm_num))
      have hkm : ((⌈1 / Real.sqrt y⌉₊ : ℕ) : ℝ) ≤ β.m := by
        have : ⌈1 / Real.sqrt y⌉₊ ≤ β.m := Nat.ceil_le.2 β.len
        exact_mod_cast this
      have hw := l1_width (a := a) (t := t) (A := A) hy0 (by linarith) hky (by omega) hFc hS0
      refine ⟨⌈1 / Real.sqrt y⌉₊, by exact_mod_cast hk2, hkx, ⟨β.m, β.B, hkm,
        fun i => (β.sub i).trans hFS, fun i => hw.trans (β.wid i), β.disj⟩, ?_⟩
      rcases hβ with h | h
      · exact Or.inl fun i j hij => h i j hij
      · exact Or.inr fun i j hij => h i j hij
  · -- `y < x`: `F` is `x`-sparse
    push Not at hxy
    left
    refine ⟨F, hFS, le_trans ?_ hFc, Or.inl (sparse_mono_param (G := H) hFsp hxy.le)⟩
    apply mul_le_mul_of_nonneg_right _ hS0
    calc x ^ A ≤ x ^ (2 * t) := pow_le_pow_of_le_one hx0.le hx1 (by omega)
      _ = (x ^ 2) ^ t := by rw [pow_mul]
      _ ≤ y ^ t := pow_le_pow_left₀ (by positivity) hxj t

end EHP6
