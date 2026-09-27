import EHP6.Round2Util

/-!
# Lemma 6.1, Steps 2 and 3: equal-size blocks (a deterministic averaging pass replacing the random
sampling of NSS VII) and anticonnected sub-blocks
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- pass 1 after `i` steps: `X p ⊆ A p` of size `m` (`p < i`), with `e(X_p, A_q) ≤ K₁ m |A_q|` for later
non-complete `q` and `e(X_{p'}, X_p) ≤ K₂ m²` for earlier non-complete pairs -/
def Pass1 (A : ℕ → Finset V) (ℓ m : ℕ) (K₁ K₂ : ℝ) (i : ℕ) : Prop :=
  ∃ X : ℕ → Finset V, (∀ p < i, X p ⊆ A p ∧ (X p).card = m) ∧
    (∀ p < i, ∀ q < ℓ, p < q → ¬ Complete G (A p) (A q) →
      (edgesBetween G (X p) (A q) : ℝ) ≤ K₁ * m * (A q).card) ∧
    (∀ p' p, p' < p → p < i → ¬ Complete G (A p') (A p) →
      (edgesBetween G (X p') (X p) : ℝ) ≤ K₂ * m ^ 2)

omit [Fintype V] in
lemma pass1_zero (A : ℕ → Finset V) (ℓ m : ℕ) (K₁ K₂ : ℝ) : Pass1 G A ℓ m K₁ K₂ 0 :=
  ⟨fun _ => ∅, fun p h => absurd h (Nat.not_lt_zero p), fun p h => absurd h (Nat.not_lt_zero p),
    fun _ p _ h => absurd h (Nat.not_lt_zero p)⟩

omit [Fintype V] in
lemma pass1_step {A : ℕ → Finset V} {ℓ m : ℕ} {c K₁ K₂ : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hK1 : 2 * ℓ * c ≤ K₁) (hK2 : 2 * ℓ * K₁ ≤ K₂) (hA : ∀ i < ℓ, m ≤ (A i).card)
    (hws : ∀ p < ℓ, ∀ q < ℓ, p < q → ¬ Complete G (A p) (A q) → WeaklySparse G c (A p) (A q))
    {i : ℕ} (hi : i < ℓ) (h : Pass1 G A ℓ m K₁ K₂ i) : Pass1 G A ℓ m K₁ K₂ (i + 1) := by
  obtain ⟨X, hX1, hX2, hX3⟩ := h
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hK10 : 0 < K₁ := lt_of_lt_of_le (by positivity) hK1
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  -- the parts of `A i`
  obtain ⟨n, hn⟩ : ∃ n, n = (A i).card / m := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by rw [hn]; exact (Nat.one_le_div_iff hm).2 (hA i hi)
  have hnm : n * m ≤ (A i).card := by rw [hn]; exact Nat.div_mul_le_self _ _
  have hAn : ((A i).card : ℝ) ≤ 2 * n * m := by
    have h1 : (A i).card < n * m + m := by rw [hn]; exact Nat.lt_div_mul_add hm
    have h2 : (A i).card ≤ 2 * n * m := by nlinarith
    exact_mod_cast h2
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_equal_parts m n (A i) hnm
  -- the scores
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Fin n → ℝ, f = fun q k =>
      if q < i then (if ¬ Complete G (A q) (A i) then
        (edgesBetween G (X q) (P k) : ℝ) / (2 * K₁ * m ^ 2) else 0)
      else (if ¬ Complete G (A i) (A q) then
        (edgesBetween G (P k) (A q) : ℝ) / (2 * c * m * (A q).card) else 0) := ⟨_, rfl⟩
  have hf0 : ∀ q k, 0 ≤ f q k := fun q k => by
    rw [hf]; dsimp only; split_ifs <;> first | exact le_rfl | positivity
  have hQ : ∀ q ∈ (range ℓ).erase i, ∑ k, f q k ≤ n := by
    intro q hq
    obtain ⟨hqi, hqℓ⟩ := mem_erase.1 hq
    have hqℓ' := mem_range.1 hqℓ
    rw [hf]; dsimp only
    by_cases h1 : q < i
    · simp only [if_pos h1]
      by_cases h2 : ¬ Complete G (A q) (A i)
      · simp only [if_pos h2]
        rw [← sum_div, div_le_iff₀ (by positivity)]
        have a1 : (∑ k, edgesBetween G (X q) (P k) : ℝ) ≤ edgesBetween G (X q) (A i) := by
          exact_mod_cast sum_edges_parts (X q) (A i) P hP1 hP3
        have a2 := hX2 q h1 i hi h1 h2
        push_cast at a1
        have a3 : K₁ * m * ((A i).card : ℝ) ≤ K₁ * m * (2 * n * m) :=
          mul_le_mul_of_nonneg_left hAn (by positivity)
        nlinarith
      · simp only [if_neg h2, sum_const_zero]; positivity
    · simp only [if_neg h1]
      have hiq : i < q := by omega
      by_cases h2 : ¬ Complete G (A i) (A q)
      · simp only [if_pos h2]
        have hAq : (0 : ℝ) < (A q).card := by
          have := hA q hqℓ'; have : 0 < (A q).card := by omega
          exact_mod_cast this
        rw [← sum_div, div_le_iff₀ (by positivity)]
        have a1 : (∑ k, edgesBetween G (P k) (A q) : ℝ) ≤ edgesBetween G (A i) (A q) := by
          exact_mod_cast sum_edges_parts' (A q) (A i) P hP1 hP3
        have a2 := hws i hi q hqℓ' hiq h2
        unfold WeaklySparse at a2
        push_cast at a1
        have a3 : c * ((A i).card : ℝ) * (A q).card ≤ c * (2 * n * m) * (A q).card := by
          have := mul_le_mul_of_nonneg_left hAn hc.le
          exact mul_le_mul_of_nonneg_right this hAq.le
        nlinarith
      · simp only [if_neg h2, sum_const_zero]; positivity
  -- a part with small total score
  have hsum : ∑ k, ∑ q ∈ (range ℓ).erase i, f q k ≤ ∑ _k : Fin n, (ℓ : ℝ) := by
    rw [sum_comm]
    calc ∑ q ∈ (range ℓ).erase i, ∑ k, f q k ≤ ∑ _q ∈ (range ℓ).erase i, (n : ℝ) := sum_le_sum hQ
      _ = ((range ℓ).erase i).card * n := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ℓ * n := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          have := card_erase_le (s := range ℓ) (a := i)
          rw [card_range] at this; exact_mod_cast this
      _ = ∑ _k : Fin n, (ℓ : ℝ) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨k, -, hk⟩ := exists_le_of_sum_le hne hsum
  have hfk : ∀ q ∈ (range ℓ).erase i, f q k ≤ ℓ := fun q hq =>
    (single_le_sum (fun q _ => hf0 q k) hq).trans hk
  refine ⟨fun p => if p = i then P k else X p, fun p hp => ?_, fun p hp q hq hpq hnc => ?_,
    fun p' p hpp hp hnc => ?_⟩
  · by_cases hpi : p = i
    · subst hpi; simp only [↓reduceIte]; exact ⟨hP1 k, hP2 k⟩
    · simp only [if_neg hpi]; exact hX1 p (by omega)
  · by_cases hpi : p = i
    · subst hpi
      simp only [↓reduceIte]
      have hqm : q ∈ (range ℓ).erase p := mem_erase.2 ⟨by omega, mem_range.2 hq⟩
      have := hfk q hqm
      rw [hf] at this; dsimp only at this
      rw [if_neg (by omega), if_pos hnc] at this
      have hAq : (0 : ℝ) < (A q).card := by
        have := hA q hq; have : 0 < (A q).card := by omega
        exact_mod_cast this
      rw [div_le_iff₀ (by positivity)] at this
      have a3 : (ℓ : ℝ) * (2 * c * m * (A q).card) ≤ K₁ * m * (A q).card := by
        have := mul_le_mul_of_nonneg_right hK1 (by positivity : (0 : ℝ) ≤ m * (A q).card)
        linarith [show (ℓ : ℝ) * (2 * c * m * (A q).card) = 2 * ℓ * c * (m * (A q).card) by ring,
          show K₁ * m * (A q).card = K₁ * (m * (A q).card) by ring]
      linarith
    · simp only [if_neg hpi]; exact hX2 p (by omega) q hq hpq hnc
  · by_cases hpi : p = i
    · subst hpi
      simp only [if_neg (show p' ≠ p by omega), ↓reduceIte]
      have hqm : p' ∈ (range ℓ).erase p := mem_erase.2 ⟨by omega, mem_range.2 (by omega)⟩
      have := hfk p' hqm
      rw [hf] at this; dsimp only at this
      rw [if_pos hpp, if_pos hnc, div_le_iff₀ (by positivity)] at this
      have a3 : (ℓ : ℝ) * (2 * K₁ * m ^ 2) ≤ K₂ * m ^ 2 := by
        have := mul_le_mul_of_nonneg_right hK2 (by positivity : (0 : ℝ) ≤ m ^ 2)
        linarith [show (ℓ : ℝ) * (2 * K₁ * m ^ 2) = 2 * ℓ * K₁ * m ^ 2 by ring]
      linarith
    · simp only [if_neg hpi, if_neg (show p' ≠ i by omega)]
      exact hX3 p' p hpp (by omega) hnc

omit [Fintype V] in
lemma pass1_full {A : ℕ → Finset V} {ℓ m : ℕ} {c K₁ K₂ : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hK1 : 2 * ℓ * c ≤ K₁) (hK2 : 2 * ℓ * K₁ ≤ K₂) (hA : ∀ i < ℓ, m ≤ (A i).card)
    (hws : ∀ p < ℓ, ∀ q < ℓ, p < q → ¬ Complete G (A p) (A q) → WeaklySparse G c (A p) (A q)) :
    ∀ i ≤ ℓ, Pass1 G A ℓ m K₁ K₂ i
  | 0, _ => pass1_zero A ℓ m K₁ K₂
  | i + 1, h => pass1_step hm hc hK1 hK2 hA hws (by omega)
      (pass1_full hm hc hK1 hK2 hA hws i (by omega))

variable (G) in
/-- pass 2 after `i` steps: anticonnected `B p ⊆ X p` of size `b` (`p < i`), `θ₁`-sparse to later
non-complete `X q`, and earlier non-complete pairs `θ₂`-sparse both ways -/
def Pass2 (A X : ℕ → Finset V) (ℓ b : ℕ) (θ₁ θ₂ : ℝ) (i : ℕ) : Prop :=
  ∃ B : ℕ → Finset V, (∀ p < i, B p ⊆ X p ∧ (B p).card = b ∧ AntiConnected G (B p)) ∧
    (∀ p < i, ∀ q < ℓ, p < q → ¬ Complete G (A p) (A q) → SparseTo G θ₁ (B p) (X q)) ∧
    (∀ p' p, p' < p → p < i → ¬ Complete G (A p') (A p) →
      SparseTo G θ₂ (B p) (B p') ∧ SparseTo G θ₂ (B p') (B p))

omit [Fintype V] in
lemma pass2_zero (A X : ℕ → Finset V) (ℓ b : ℕ) (θ₁ θ₂ : ℝ) : Pass2 G A X ℓ b θ₁ θ₂ 0 :=
  ⟨fun _ => ∅, fun p h => absurd h (Nat.not_lt_zero p), fun p h => absurd h (Nat.not_lt_zero p),
    fun _ p _ h => absurd h (Nat.not_lt_zero p)⟩

/-- the complete-blockade alternative of a pass-2 step -/
def Pass2Out (G : SimpleGraph V) [DecidableRel G.Adj] (Xi : Finset V) (ℓ m : ℕ) : Prop :=
  ∃ D ⊆ Xi, (m : ℝ) / 2 ≤ D.card ∧ ∃ β : Blockade D ℓ (D.card / (ℓ : ℝ) ^ 2), β.IsComplete G

lemma pass2_step {A X : ℕ → Finset V} {ℓ m b : ℕ} {K₂ θ₁ θ₂ ρ : ℝ}
    (hX : ∀ p < ℓ, X p ⊆ A p ∧ (X p).card = m)
    (hXX : ∀ p' p, p' < p → p < ℓ → ¬ Complete G (A p') (A p) →
      (edgesBetween G (X p') (X p) : ℝ) ≤ K₂ * m ^ 2)
    (hℓ : 2 ≤ ℓ) (hm : 0 < m) (hb : 1 ≤ b) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hK : K₂ ≤ ρ * θ₁) (hθ : θ₁ ≤ ρ * θ₂) (hθb : θ₁ * m ≤ θ₂ * b)
    (hDm : ((ℓ : ℝ) - 1) * (ρ * m) ≤ m / 2) (hbD : (b : ℝ) ≤ (m / 2) / ℓ)
    {i : ℕ} (hi : i < ℓ) (h : Pass2 G A X ℓ b θ₁ θ₂ i) :
    Pass2Out G (X i) ℓ m ∨ Pass2 G A X ℓ b θ₁ θ₂ (i + 1) := by
  obtain ⟨B, hB1, hB2, hB3⟩ := h
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hbr : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hρ : 0 < ρ := by
    by_contra h; push Not at h
    have : ρ * θ₂ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hθ₂.le
    linarith
  obtain ⟨hXi, hXic⟩ := hX i hi
  obtain ⟨C, hC⟩ : ∃ C : ℕ → Finset V, C = fun q =>
      if q < i ∧ ¬ Complete G (A q) (A i) then
        (X i).filter (fun w => θ₂ * b ≤ ((nbrs G w (B q)).card : ℝ))
      else if i < q ∧ ¬ Complete G (A i) (A q) then
        (X i).filter (fun w => θ₁ * m ≤ ((nbrs G w (X q)).card : ℝ))
      else ∅ := ⟨_, rfl⟩
  have hCsize : ∀ q ∈ (range ℓ).erase i, ((C q).card : ℝ) ≤ ρ * m := by
    intro q hq
    obtain ⟨hqi, hqℓ⟩ := mem_erase.1 hq
    have hqℓ' := mem_range.1 hqℓ
    rw [hC]; dsimp only
    by_cases h1 : q < i ∧ ¬ Complete G (A q) (A i)
    · rw [if_pos h1]
      have a1 := card_high_deg (G := G) (X i) (B q) (θ₂ * b)
      have a2 : (edgesBetween G (X i) (B q) : ℝ) ≤ b * (θ₁ * m) := by
        rw [edgesBetween_comm]
        have := edges_le_of_sparseTo (hB2 q h1.1 i hi h1.1 h1.2)
        rwa [(hB1 q h1.1).2.1, hXic] at this
      have a3 : θ₂ * b * ((X i).filter (fun w => θ₂ * b ≤ ((nbrs G w (B q)).card : ℝ))).card ≤
          θ₂ * b * (ρ * m) := by
        have : b * (θ₁ * m) ≤ θ₂ * b * (ρ * m) := by
          have := mul_le_mul_of_nonneg_left hθ (by positivity : (0 : ℝ) ≤ b * m)
          nlinarith
        linarith
      exact le_of_mul_le_mul_left a3 (by positivity)
    · rw [if_neg h1]
      by_cases h2 : i < q ∧ ¬ Complete G (A i) (A q)
      · rw [if_pos h2]
        have a1 := card_high_deg (G := G) (X i) (X q) (θ₁ * m)
        have a2 := hXX i q h2.1 hqℓ' h2.2
        have a3 : θ₁ * m * ((X i).filter (fun w => θ₁ * m ≤ ((nbrs G w (X q)).card : ℝ))).card ≤
            θ₁ * m * (ρ * m) := by
          have : K₂ * (m : ℝ) ^ 2 ≤ θ₁ * m * (ρ * m) := by
            have := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)
            nlinarith
          linarith
        exact le_of_mul_le_mul_left a3 (by positivity)
      · rw [if_neg h2, card_empty, Nat.cast_zero]; exact mul_nonneg hρ.le hmr.le
  -- the surviving vertices
  obtain ⟨D, hD⟩ : ∃ D : Finset V, D = X i \ ((range ℓ).erase i).biUnion C := ⟨_, rfl⟩
  have hDX : D ⊆ X i := by rw [hD]; exact sdiff_subset
  have hDnot : ∀ w ∈ D, ∀ q ∈ (range ℓ).erase i, w ∉ C q := by
    intro w hw q hq hwq
    rw [hD] at hw
    exact (mem_sdiff.1 hw).2 (mem_biUnion.2 ⟨q, hq, hwq⟩)
  have hDcard : (m : ℝ) / 2 ≤ D.card := by
    have h1 : (X i).card ≤ D.card + (((range ℓ).erase i).biUnion C).card := by
      rw [hD]; exact card_le_card_sdiff_add_card
    have h2 : ((((range ℓ).erase i).biUnion C).card : ℝ) ≤ ((ℓ : ℝ) - 1) * (ρ * m) := by
      have a := card_biUnion_le (s := (range ℓ).erase i) (t := C)
      have a' : ((((range ℓ).erase i).biUnion C).card : ℝ) ≤ ∑ q ∈ (range ℓ).erase i, ((C q).card : ℝ) := by
        exact_mod_cast a
      have b' : ∑ q ∈ (range ℓ).erase i, ((C q).card : ℝ) ≤ ((range ℓ).erase i).card * (ρ * m) := by
        have := sum_le_sum hCsize
        rwa [sum_const, nsmul_eq_mul] at this
      have c' : (((range ℓ).erase i).card : ℝ) = ℓ - 1 := by
        rw [card_erase_of_mem (mem_range.2 hi), card_range]; push_cast [show 1 ≤ ℓ by omega]; ring
      rw [c'] at b'
      linarith
    have h1' : (m : ℝ) ≤ D.card + (((range ℓ).erase i).biUnion C).card := by
      rw [← hXic]; exact_mod_cast h1
    linarith
  by_cases hsmall : ∀ K, IsAnticomponent G D K → (K.card : ℝ) < D.card / ℓ
  · exact Or.inl ⟨D, hDX, hDcard, nss_L41_proof (G := G) D ℓ hℓ hsmall⟩
  push Not at hsmall
  obtain ⟨K, hK, hKc⟩ := hsmall
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hbK : b ≤ K.card := by
    have : (b : ℝ) ≤ K.card := hbD.trans ((div_le_div_of_nonneg_right hDcard hℓr.le).trans hKc)
    exact_mod_cast this
  obtain ⟨Bi, hBiK, hBic, hBia⟩ := exists_anticonn_subset hK.2.2.1 b hb hbK
  have hBiD : Bi ⊆ D := hBiK.trans hK.1
  right
  refine ⟨fun p => if p = i then Bi else B p, fun p hp => ?_, fun p hp q hq hpq hnc => ?_,
    fun p' p hpp hp hnc => ?_⟩
  · by_cases hpi : p = i
    · subst hpi; simp only [↓reduceIte]; exact ⟨hBiD.trans hDX, hBic, hBia⟩
    · simp only [if_neg hpi]; exact hB1 p (by omega)
  · by_cases hpi : p = i
    · subst hpi
      simp only [↓reduceIte]
      intro w hw
      have hqm : q ∈ (range ℓ).erase p := mem_erase.2 ⟨by omega, mem_range.2 hq⟩
      have hwC := hDnot w (hBiD hw) q hqm
      rw [hC] at hwC; dsimp only at hwC
      rw [if_neg (fun h => by omega), if_pos ⟨hpq, hnc⟩] at hwC
      have : ¬ (θ₁ * m ≤ ((nbrs G w (X q)).card : ℝ)) := fun h' =>
        hwC (mem_filter.2 ⟨(hBiD.trans hDX) hw, h'⟩)
      rw [(hX q hq).2]; push Not at this; exact this.le
    · simp only [if_neg hpi]; exact hB2 p (by omega) q hq hpq hnc
  · by_cases hpi : p = i
    · subst hpi
      simp only [if_neg (show p' ≠ p by omega), ↓reduceIte]
      constructor
      · intro w hw
        have hqm : p' ∈ (range ℓ).erase p := mem_erase.2 ⟨by omega, mem_range.2 (by omega)⟩
        have hwC := hDnot w (hBiD hw) p' hqm
        rw [hC] at hwC; dsimp only at hwC
        rw [if_pos ⟨hpp, hnc⟩] at hwC
        have : ¬ (θ₂ * b ≤ ((nbrs G w (B p')).card : ℝ)) := fun h' =>
          hwC (mem_filter.2 ⟨(hBiD.trans hDX) hw, h'⟩)
        rw [(hB1 p' hpp).2.1]; push Not at this; exact this.le
      · intro u hu
        have a1 := hB2 p' hpp p hi hpp hnc u hu
        rw [hXic] at a1
        have a2 : (nbrs G u Bi).card ≤ (nbrs G u (X p)).card :=
          card_le_card (filter_subset_filter _ (hBiD.trans hDX))
        have a2' : ((nbrs G u Bi).card : ℝ) ≤ (nbrs G u (X p)).card := by exact_mod_cast a2
        rw [hBic]; linarith
    · simp only [if_neg hpi, if_neg (show p' ≠ i by omega)]
      exact hB3 p' p hpp (by omega) hnc

lemma pass2_full {A X : ℕ → Finset V} {ℓ m b : ℕ} {K₂ θ₁ θ₂ ρ : ℝ}
    (hX : ∀ p < ℓ, X p ⊆ A p ∧ (X p).card = m)
    (hXX : ∀ p' p, p' < p → p < ℓ → ¬ Complete G (A p') (A p) →
      (edgesBetween G (X p') (X p) : ℝ) ≤ K₂ * m ^ 2)
    (hℓ : 2 ≤ ℓ) (hm : 0 < m) (hb : 1 ≤ b) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hK : K₂ ≤ ρ * θ₁) (hθ : θ₁ ≤ ρ * θ₂) (hθb : θ₁ * m ≤ θ₂ * b)
    (hDm : ((ℓ : ℝ) - 1) * (ρ * m) ≤ m / 2) (hbD : (b : ℝ) ≤ (m / 2) / ℓ) :
    ∀ i ≤ ℓ, (∃ j < ℓ, Pass2Out G (X j) ℓ m) ∨ Pass2 G A X ℓ b θ₁ θ₂ i
  | 0, _ => Or.inr (pass2_zero A X ℓ b θ₁ θ₂)
  | i + 1, h => by
    rcases pass2_full hX hXX hℓ hm hb hθ₁ hθ₂ hK hθ hθb hDm hbD i (by omega) with h' | h'
    · exact Or.inl h'
    · rcases pass2_step hX hXX hℓ hm hb hθ₁ hθ₂ hK hθ hθb hDm hbD (by omega) h' with h'' | h''
      · exact Or.inl ⟨i, by omega, h''⟩
      · exact Or.inr h''

end EHP6
