import EHP6.CombExtract
import EHP6.CombNum2
import EHP6.CombNum3
import EHP6.Tooth
import EHP6.Local

/-!
# Lemma 3.1 (the comb lemma for P̄6)
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- outcome (ii): an `x`-semisparse `(K, |S|/K^e)`-blockade with `K ∈ [y^{-1/16}, 1/x]` -/
def Outcome2 (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (x y : ℝ) (e : ℕ) : Prop :=
  ∃ K : ℕ, 1 ≤ y * (K : ℝ) ^ 16 ∧ (K : ℝ) * x ≤ 1 ∧
    ∃ β : Blockade S K (S.card / (K : ℝ) ^ e), β.IsSemisparse G x

omit [Fintype V] in
lemma weaklySparse_of_anticomplete {A B : Finset V} {x : ℝ} (hx : 0 ≤ x)
    (h : Anticomplete G A B) : WeaklySparse G x A B := by
  unfold WeaklySparse edgesBetween
  have : ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)) = ∅ := by
    apply filter_eq_empty_iff.2
    rintro ⟨a, b⟩ hp; exact h a (mem_product.1 hp).1 b (mem_product.1 hp).2
  rw [this]; simp; positivity

omit [Fintype V] in
lemma weaklySparse_mono {A B : Finset V} {x x' : ℝ} (hxx : x ≤ x') (h : WeaklySparse G x A B) :
    WeaklySparse G x' A B := by
  unfold WeaklySparse at *
  have : x * A.card * B.card ≤ x' * A.card * B.card := by
    have := mul_le_mul_of_nonneg_right hxx (show (0:ℝ) ≤ A.card * B.card by positivity)
    linarith [show x * A.card * B.card = x * (A.card * B.card) by ring,
      show x' * A.card * B.card = x' * (A.card * B.card) by ring]
  linarith

omit [Fintype V] in
lemma semisparse_of_pure {S : Finset V} {k w x : ℝ} (hx : 0 ≤ x) (β : Blockade S k w)
    (h : β.IsPure G) : β.IsSemisparse G x := fun i j hij =>
  (h i j hij).elim Or.inl (fun h' => Or.inr (weaklySparse_of_anticomplete hx h'))

lemma exists_k_of_ell {ℓ : ℕ} (hℓ : 2 ^ 64 ≤ ℓ) :
    ∃ k : ℕ, ℓ ≤ k ^ 4 ∧ (k - 1) ^ 4 < ℓ ∧ 2 ^ 16 ≤ k ∧ k ≤ ℓ := by
  have hex : ∃ K : ℕ, ℓ ≤ K ^ 4 := ⟨ℓ, Nat.le_self_pow (by norm_num) ℓ⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_, Nat.find_min' hex (Nat.le_self_pow (by norm_num) ℓ)⟩
  · by_cases h0 : Nat.find hex = 0
    · have := Nat.find_spec hex; rw [h0] at this; norm_num at this; omega
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push Not at this; exact this
  · by_contra h; push Not at h
    have h1 : (Nat.find hex) ^ 4 ≤ (2 ^ 16 - 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h2 := Nat.find_spec hex
    have h3 : ((2 : ℕ) ^ 16 - 1) ^ 4 < 2 ^ 64 := by norm_num
    omega

lemma floor_half {z : ℝ} (hz : 1 ≤ z) : z / 2 ≤ (⌊z⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one z
  have h1 : (1 : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hz)
  linarith

/-- the TL5 outcome for one tooth -/
def TL5 (G : SimpleGraph V) [DecidableRel G.Adj] (x : ℝ) (k : ℕ) (Y U : Finset V) : Prop :=
  ∃ Y' ⊆ Y, (Y.card : ℝ) / k ≤ Y'.card ∧
    ∀ u ∈ U, (∀ y ∈ Y', G.Adj u y) ∨ ((nbrs G u Y').card : ℝ) < x * Y'.card / 4

theorem comb_from_data (hfree : Free G P6ᶜ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ 1 / 2 ^ 64) {S : Finset V} (hS : 1 / x ^ 18 ≤ (S.card : ℝ))
    (D : CombData G S x y) : Outcome2 G S x y 100 := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hx64 : x ≤ 1 / 2 ^ 64 := hxy.trans hy
  have hx1 : x ≤ 1 := hx64.trans (by norm_num)
  have hx14 : x ≤ 1 / 4 := hx64.trans (by norm_num)
  have hx20 : x ≤ 1 / 2 ^ 20 := hx64.trans (by norm_num)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hℓ64 : (2 : ℝ) ^ 64 ≤ D.ℓ := cl_ell64 hy0 hy D.hℓy
  have hℓ64n : 2 ^ 64 ≤ D.ℓ := by exact_mod_cast hℓ64
  have hℓpos : (0 : ℝ) < D.ℓ := lt_of_lt_of_le (by positivity) hℓ64
  obtain ⟨k, hkℓ, hkmin, hk16, hkle⟩ := exists_k_of_ell hℓ64n
  have hkℓr : (D.ℓ : ℝ) ≤ (k : ℝ) ^ 4 := by exact_mod_cast hkℓ
  have ha4 : ((k - 1 : ℕ) : ℝ) ^ 4 < D.ℓ := by exact_mod_cast hkmin
  have hk16r : (2 : ℝ) ^ 16 ≤ k := by exact_mod_cast hk16
  have hk1 : (1 : ℝ) ≤ k := le_trans (by norm_num) hk16r
  have hk0 : (0 : ℝ) < k := by linarith
  have hkx : (k : ℝ) ≤ 2 / Real.sqrt x := by
    have h := cl_kx (a := ((k - 1 : ℕ) : ℝ)) (Nat.cast_nonneg _) hx hx1 ha4 D.hℓx
    have e : ((k - 1 : ℕ) : ℝ) + 1 = k := by rw [Nat.cast_sub (by omega)]; simp
    rwa [e] at h
  have hk2x := tn_k2x hx hx20 hk16 hkx
  have hkx1 : (k : ℝ) * x ≤ 1 := cl_kx1 hx hx14 hk0.le hk2x
  -- the first k teeth
  let idx : Fin k → Fin D.ℓ := Fin.castLE hkle
  let Y : Fin k → Finset V := fun i => D.C (idx i)
  let U : Fin k → Finset V := fun i => (univ.filter (fun j => j ≠ i)).biUnion Y
  have hYS : ∀ i, Y i ⊆ S := fun i => (D.hC _).trans (filter_subset _ _)
  have hYdisj : ∀ i j, i ≠ j → Disjoint (Y i) (Y j) := fun i j h =>
    D.hdisj _ _ (fun e => h (Fin.castLE_injective _ e))
  have hsizes : ∀ i, x ^ 8 * S.card ≤ (Y i).card ∧ 16 / x ^ 3 ≤ ((Y i).card : ℝ) := fun i =>
    cl_tooth_size hx hxy hy hℓpos D.hℓx hS (D.hsize _)
  have hsize24 : ∀ i, (S.card : ℝ) / (k : ℝ) ^ 24 ≤ (Y i).card := fun i =>
    cl_Ck24 hy0 D.hℓy hkℓr hS0 (D.hsize _)
  -- the module law supplies the Tooth Lemma hypothesis for every tooth
  have hU : ∀ i, ∀ u ∈ U i, ∀ A, IsAnticomponent G (nbrs G u (Y i)) A → IsModule G (Y i) A := by
    intro i u hu A hA
    obtain ⟨j, hj, huj⟩ := mem_biUnion.1 hu
    have hji : j ≠ i := (mem_filter.1 hj).2
    have huN : u ∈ nbrs G D.v S := D.hC _ huj
    refine module_law G hfree (v := D.v) (a := D.a (idx i)) (u := u) (D.ha _).2 ?_ ?_ ?_ hA
    · intro z hz
      exact ⟨(mem_filter.1 (D.hC _ hz)).2, D.hcomp _ z hz⟩
    · exact G.adj_symm (mem_filter.1 huN).2
    · intro h
      exact D.hanti (idx i) (idx j) (fun e => hji (Fin.castLE_injective _ e).symm) u huj (G.adj_symm h)
  have T := fun i => tooth_lemma (G := G) hx hx20 hk16 hkx (Y i) (U i) (hsizes i).2 (hU i)
  by_cases hall : ∀ i, TL5 G x k (Y i) (U i)
  · -- all teeth give TL5: a semisparse (k, |S|/k^100)-blockade via the Pair Lemma
    choose Y' hY'sub hY'size hY'prop using hall
    have hconds := cl_TL5 hy0 D.hℓy hkℓr hk1 hx hx14 hk2x hS0 (hsize24 ⟨0, by omega⟩)
      (hY'size ⟨0, by omega⟩)
    refine ⟨k, hconds.1, hconds.2.1,
      ⟨k, Y', le_rfl, fun i => (hY'sub i).trans (hYS i),
        fun i => (cl_TL5 hy0 D.hℓy hkℓr hk1 hx hx14 hk2x hS0 (hsize24 i) (hY'size i)).2.2,
        fun i j h => disjoint_of_subset_left (hY'sub i)
          (disjoint_of_subset_right (hY'sub j) (hYdisj i j h))⟩, fun i j hij => ?_⟩
    have mem_U : ∀ i j, i ≠ j → ∀ w ∈ Y' i, w ∈ U j := fun i j h w hw =>
      mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ _, h⟩, hY'sub i hw⟩
    have conv : ∀ i j, i ≠ j → ∀ w ∈ Y' i, Y' j ⊆ nbrs G w (Y' j) ∨
        ((nbrs G w (Y' j)).card : ℝ) < x / 4 * (Y' j).card := by
      intro i j h w hw
      rcases hY'prop j w (mem_U i j h w hw) with h' | h'
      · exact Or.inl fun z hz => mem_filter.2 ⟨hz, h' z hz⟩
      · exact Or.inr (by linarith)
    rcases pair_lemma G (Y' i) (Y' j) (x / 4) (by positivity) (conv i j hij)
      (conv j i (Ne.symm hij)) with h | h
    · exact Or.inl h
    · exact Or.inr (weaklySparse_mono (by linarith) h)
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    rcases T i with ⟨K, hkK, hKx, β, hβ⟩ | ⟨L, hL9, hL8, β, hβ⟩ | ⟨β, hβ⟩ | ⟨β, hβ⟩ | h5
    · have hK0 : (0 : ℝ) < K := by
        have : (0 : ℝ) < (K : ℝ) ^ 4 := lt_of_lt_of_le hk0 hkK
        rcases Nat.eq_zero_or_pos K with h | h
        · rw [h] at this; simp at this
        · exact_mod_cast h
      obtain ⟨c1, c2, c3⟩ := cl_TL1 hy0 D.hℓy hkℓr hk1 hkK hKx hx hS0 (hsize24 i) hK0
      exact ⟨K, c1, c2, β.mono (hYS i) le_rfl c3, semisparse_of_pure hx.le _ hβ⟩
    · obtain ⟨c1, c2, c3⟩ := cl_TL2 hy0 hy D.hℓy hkℓr hk16r hk2x hx hx1 (Nat.cast_nonneg L) hL9 hL8
        hS0 (hsize24 i)
      exact ⟨L, c1, c2, β.mono (hYS i) le_rfl c3, semisparse_of_pure hx.le _ hβ⟩
    · have hK1 : 1 / (2 * x) ≤ ((⌊1 / x⌋₊ : ℕ) : ℝ) := by
        have := floor_half (z := 1 / x) (by rw [le_div_iff₀ hx]; linarith)
        rwa [show 1 / x / 2 = 1 / (2 * x) by ring] at this
      obtain ⟨c1, c2, c3⟩ := cl_TL3 hx hxy hy hk0 hkx1 hK1 (Nat.floor_le (by positivity)) hS0
        (hsizes i).1
      refine ⟨_, c1, c2, β.mono (hYS i) le_rfl c3, fun a b hab => ?_⟩
      rcases hβ with h | h
      · exact Or.inl (h a b hab)
      · exact Or.inr (weaklySparse_of_anticomplete hx.le (h a b hab))
    · have hxk : 0 < x * k := by positivity
      have hK1 : 1 / (2 * (x * k)) ≤ ((⌊1 / (x * k)⌋₊ : ℕ) : ℝ) := by
        have := floor_half (z := 1 / (x * k)) (by rw [le_div_iff₀ hxk]; linarith)
        rwa [show 1 / (x * k) / 2 = 1 / (2 * (x * k)) by ring] at this
      obtain ⟨c1, c2, c3⟩ := cl_TL4 hx hxy hy hk1 hk2x hK1 (Nat.floor_le (by positivity)) hS0
        (hsizes i).1
      exact ⟨_, c1, c2, β.mono (hYS i) le_rfl c3, fun a b hab => Or.inl (hβ a b hab)⟩
    · exact absurd h5 hi

/-- **Lemma 3.1.** Let `0 < x ≤ y ≤ 2⁻⁶⁴` and let `G[S]` be `y³`-sparse and P̄6-free with
`|S| ≥ x⁻¹⁸`. Then (i) `G[S]` is `2y⁴`-sparse; or (ii) for some `K ∈ [y^{-1/16}, 1/x]` there is an
`x`-semisparse `(K, |S|/K¹⁰⁰)`-blockade; or (iii) there are disjoint `X, Y ⊆ S` with `|X| ≥ y⁴|S|`,
`|Y| ≥ (1−4y)|S|` and `Y` `x`-sparse to `X`. -/
theorem comb_lemma (hcomb : NssComb) (hfree : Free G P6ᶜ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ 1 / 2 ^ 64) (S : Finset V) (hsp : Sparse G (y ^ 3) S)
    (hS : 1 / x ^ 18 ≤ (S.card : ℝ)) :
    Sparse G (2 * y ^ 4) S ∨ Outcome2 G S x y 100 ∨ Outcome3 G S x y := by
  rcases comb_extract hcomb hx hxy hy S hsp hS with h | h | hD
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · obtain ⟨D⟩ := hD
    exact Or.inr (Or.inl (comb_from_data hfree hx hxy hy hS D))

end EHP6
