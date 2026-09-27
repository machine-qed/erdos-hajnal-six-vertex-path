import EHP6.ToothNum
import EHP6.ToothChain
import EHP6.ToothNode
import EHP6.ToothChunk

/-!
# Lemma 2.1 (Tooth Lemma)

Formal statement (lengths stated without real roots: `k ≤ K⁴` means `K ≥ k^{1/4}`,
`k³ ≤ (9L)⁴ ∧ (8L)⁴ ≤ k³` means `k^{3/4}/9 ≤ L ≤ k^{3/4}/8`).
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]


lemma exists_K0 {k : ℕ} (hk : 2 ^ 16 ≤ k) : ∃ K₀ : ℕ, k ≤ K₀ ^ 4 ∧ (K₀ - 1) ^ 4 < k ∧ 16 ≤ K₀ := by
  classical
  have hex : ∃ K : ℕ, k ≤ K ^ 4 := ⟨k, Nat.le_self_pow (by norm_num) k⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
  · by_cases h0 : Nat.find hex = 0
    · have := Nat.find_spec hex; rw [h0] at this; norm_num at this; omega
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push Not at this; exact this
  · by_contra h; push Not at h
    have h1 : (Nat.find hex) ^ 4 ≤ 15 ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h2 := Nat.find_spec hex
    have h3 : (2 : ℕ) ^ 16 = 65536 := by norm_num
    have h4 : (15 : ℕ) ^ 4 = 50625 := by norm_num
    omega

lemma exists_L {k : ℕ} (hk : 2 ^ 16 ≤ k) :
    ∃ L : ℕ, 8 ≤ L ∧ (8 * L) ^ 4 ≤ k ^ 3 ∧ k ^ 3 < (8 * (L + 1)) ^ 4 := by
  classical
  let P : ℕ → Prop := fun L => (8 * L) ^ 4 ≤ k ^ 3
  have hk3 : (2 ^ 16) ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left hk 3
  have hP8 : P 8 := by
    show (8 * 8) ^ 4 ≤ k ^ 3
    calc (8 * 8) ^ 4 ≤ (2 ^ 16) ^ 3 := by norm_num
      _ ≤ k ^ 3 := hk3
  have h8 : 8 ≤ k ^ 3 := le_trans (by norm_num) hk3
  refine ⟨Nat.findGreatest P (k ^ 3), Nat.le_findGreatest h8 hP8,
    Nat.findGreatest_spec (P := P) (Nat.zero_le _) (by simp [P]), ?_⟩
  set L := Nat.findGreatest P (k ^ 3)
  have hLspec : (8 * L) ^ 4 ≤ k ^ 3 := Nat.findGreatest_spec (P := P) (Nat.zero_le _) (by simp [P])
  have hLlt : L < k ^ 3 := by
    by_contra h; push Not at h
    have : k ^ 3 < (8 * L) ^ 4 :=
      calc k ^ 3 ≤ L := h
        _ < 8 * L := by omega
        _ ≤ (8 * L) ^ 4 := Nat.le_self_pow (by norm_num) _
    omega
  have := Nat.findGreatest_is_greatest (P := P) (show L < L + 1 by omega) (by omega)
  simp only [P, not_le] at this; exact this

theorem tooth_lemma {x : ℝ} {k : ℕ} (hx : 0 < x) (hx20 : x ≤ 1 / 2 ^ 20) (hk : 2 ^ 16 ≤ k)
    (hkx : (k : ℝ) ≤ 2 / Real.sqrt x) (Y U : Finset V) (hn : 16 / x ^ 3 ≤ (Y.card : ℝ))
    (hU : ∀ u ∈ U, ∀ A, IsAnticomponent G (nbrs G u Y) A → IsModule G Y A) :
    (∃ K : ℕ, (k : ℝ) ≤ (K : ℝ) ^ 4 ∧ (K : ℝ) ≤ 1 / x ∧
        ∃ β : Blockade Y K (Y.card / (K : ℝ) ^ 4), β.IsPure G) ∨
    (∃ L : ℕ, (k : ℝ) ^ 3 ≤ (9 * (L : ℝ)) ^ 4 ∧ (8 * (L : ℝ)) ^ 4 ≤ (k : ℝ) ^ 3 ∧
        ∃ β : Blockade Y L (Y.card / (2 * k)), β.IsPure G) ∨
    (∃ β : Blockade Y ⌊1 / x⌋₊ (x ^ 2 * Y.card / k), β.IsComplete G ∨ β.IsAnticomplete G) ∨
    (∃ β : Blockade Y ⌊1 / (x * k)⌋₊ (x ^ 3 * Y.card / 4), β.IsComplete G) ∨
    (∃ Y' ⊆ Y, (Y.card : ℝ) / k ≤ Y'.card ∧
        ∀ u ∈ U, (∀ y ∈ Y', G.Adj u y) ∨ ((nbrs G u Y').card : ℝ) < x * Y'.card / 4) := by
  have hkr : (2 : ℝ) ^ 16 ≤ k := tn_kpos hx hx20 hk hkx
  have hk2x : (k : ℝ) ^ 2 * x ≤ 4 := tn_k2x hx hx20 hk hkx
  have hxk : x * k ≤ 1 / 2 ^ 9 := tn_xk hx hx20 hk hkx
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hkr
  have hk1 : (1 : ℝ) ≤ k := le_trans (by norm_num) hkr
  have hxk1 : x * k ≤ 1 := hxk.trans (by norm_num)
  have hx1 : x ≤ 1 := hx20.trans (by norm_num)
  have hnpos : 0 < (Y.card : ℝ) := lt_of_lt_of_le (by positivity) hn
  have hs1 := tn_s_gt_one hx hx20 hn
  have hst := tn_s_le_t hx hx1 hkpos hnpos.le hxk1 (n := Y.card)
  have htn : (Y.card : ℝ) / k ≤ Y.card := div_le_self hnpos.le hk1
  have htpos : 0 < (Y.card : ℝ) / k := div_pos hnpos hkpos
  obtain ⟨K₀, hK₀spec, hK₀min, hK₀16⟩ := exists_K0 hk
  have ha15 : (15 : ℝ) ≤ ((K₀ - 1 : ℕ) : ℝ) := by exact_mod_cast (show 15 ≤ K₀ - 1 by omega)
  have ha4 : ((K₀ - 1 : ℕ) : ℝ) ^ 4 < k := by exact_mod_cast hK₀min
  have haK : (K₀ : ℝ) - 1 = ((K₀ - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; simp
  have hK₀4 : (k : ℝ) ≤ (K₀ : ℝ) ^ 4 := by exact_mod_cast hK₀spec
  have hK₀x : (K₀ : ℝ) ≤ 1 / x := by
    have := tn_K0_le ha15 ha4 hk2x hx
    rw [le_div_iff₀ hx]; rw [← haK] at this; linarith
  have hK₀K₁ : K₀ ≤ ⌊1 / x⌋₊ := Nat.le_floor hK₀x
  have hK₁x : ((⌊1 / x⌋₊ : ℕ) : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
  have hK₁half : 1 / (2 * x) ≤ ((⌊1 / x⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (1 / x)
    have hinv : (2 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
    have e : 1 / (2 * x) = (1 / x) / 2 := by field_simp <;> ring
    rw [e]; linarith
  have hK₁2 : 2 ≤ ⌊1 / x⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hx]; push_cast; linarith)
  have hbound := tn_bound ha15 ha4 hkpos hx hx20 hnpos hK₁half
  rw [← haK] at hbound
  have htK : (Y.card : ℝ) / (K₀ : ℝ) ^ 4 ≤ Y.card / k :=
    div_le_div_of_nonneg_left hnpos.le hkpos hK₀4
  rcases heavy_chain (G := G) (Y := Y) hs1 hst htn (by omega) hK₀K₁ htK hbound with
    ⟨K, hK0K, hKK1, β, hβ⟩ | ⟨𝒞, h𝒞, hchain, hbig, hmass⟩
  · left
    have hKr : (K₀ : ℝ) ≤ K := by exact_mod_cast hK0K
    refine ⟨K, hK₀4.trans (pow_le_pow_left₀ (by positivity) hKr 4), ?_, β, hβ⟩
    exact (show (K : ℝ) ≤ (⌊1 / x⌋₊ : ℕ) by exact_mod_cast hKK1).trans hK₁x
  by_cases hthick : ∃ N ∈ 𝒞, (Y.card : ℝ) / k ≤ ((atomPart G Y (x ^ 2 * Y.card / 4) N).card : ℝ)
  · obtain ⟨N, hN𝒞, hNt⟩ := hthick
    have hN := h𝒞 hN𝒞
    have hxkpos : 0 < x * k := by positivity
    have hK'x : ((⌊1 / (x * k)⌋₊ : ℕ) : ℝ) ≤ 1 / (x * k) := Nat.floor_le (by positivity)
    have hK'2 : 2 ≤ ⌊1 / (x * k)⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hxkpos]; push_cast; linarith)
    have hK'pos : (0 : ℝ) < ((⌊1 / (x * k)⌋₊ : ℕ) : ℝ) := by exact_mod_cast (show 0 < ⌊1 / (x * k)⌋₊ by omega)
    have hK₁pos : (0 : ℝ) < ((⌊1 / x⌋₊ : ℕ) : ℝ) := by exact_mod_cast (show 0 < ⌊1 / x⌋₊ by omega)
    have h₃ := tn_h3 hx hkpos hnpos.le (hxk1.trans (by norm_num)) hK₁pos hK₁x hNt
    have h₄ := fun r hr => tn_h4 hx hk1 hnpos.le hK'pos hK'x hNt (r := r) hr
    rcases node_step hN U hU x ⌊1 / x⌋₊ ⌊1 / (x * k)⌋₊ hK₁2 hK'2 (x ^ 2 * Y.card / k)
      (x ^ 3 * Y.card / 4) h₃ h₄ with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, atomPart_subset.trans (mem_Lfam.1 hN).1, hNt, h⟩)))
  · push Not at hthick
    right; left
    obtain ⟨L, hL8, hLspec, hLnext⟩ := exists_L hk
    have hL8r : (8 : ℝ) ≤ L := by exact_mod_cast hL8
    have hL8' : (8 * (L : ℝ)) ^ 4 ≤ (k : ℝ) ^ 3 := by exact_mod_cast hLspec
    have hLn : (k : ℝ) ^ 3 < (8 * ((L : ℝ) + 1)) ^ 4 := by exact_mod_cast hLnext
    have hL9 := tn_L9 hL8r hLn
    have hLa := tn_La (by positivity) (by positivity) hkpos.le hL8' ha4
    have hapos : (0 : ℝ) < ((K₀ - 1 : ℕ) : ℝ) := by linarith
    have hLm := tn_L_mass (by positivity) hapos hkpos hLa hnpos.le (n := Y.card)
    have hmass' : 2 * (L : ℝ) * (Y.card / k) ≤ ∑ N ∈ 𝒞, ((atomPart G Y (x ^ 2 * Y.card / 4) N).card : ℝ) := by
      rw [← haK] at hLm; linarith
    have hne : ∀ N ∈ 𝒞, N.Nonempty := fun N hN =>
      card_pos.1 (by exact_mod_cast (show (0 : ℝ) < N.card by linarith [hbig N hN]))
    obtain ⟨β, hβ⟩ := chain_blockade h𝒞 hchain hne htpos hthick L hmass'
    exact ⟨L, hL9, hL8', β.mono subset_rfl le_rfl (by rw [div_div, mul_comm]), hβ⟩

end EHP6
