import EHP6.C01Tree

/-!
# Proof of Theorem A (paper, end of §8): polynomial Rödl ⇒ `hom(G) ≥ |G|^τ`
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
/-- greedy: a vertex set of maximum degree `≤ D` has a stable subset of size `≥ |T|/(D+1)` -/
lemma greedy_stable {H : SimpleGraph V} [DecidableRel H.Adj] (D : ℝ) :
    ∀ n : ℕ, ∀ T : Finset V, T.card = n → (∀ v ∈ T, ((nbrs H v T).card : ℝ) ≤ D) →
      ∃ I ⊆ T, IsStableF H I ∧ (T.card : ℝ) ≤ (D + 1) * I.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hTn hdeg
  rcases T.eq_empty_or_nonempty with hTe | ⟨v, hv⟩
  · subst hTe
    exact ⟨∅, subset_rfl, fun a ha => absurd ha (notMem_empty a), by simp⟩
  obtain ⟨T', hT'⟩ : ∃ T', T' = T \ insert v (nbrs H v T) := ⟨_, rfl⟩
  have hT'T : T' ⊆ T := by rw [hT']; exact sdiff_subset
  have hvT' : v ∉ T' := by rw [hT']; simp
  have hlt : T'.card < n := by rw [← hTn]; exact card_lt_card ⟨hT'T, fun h => hvT' (h hv)⟩
  have hdeg' : ∀ u ∈ T', ((nbrs H u T').card : ℝ) ≤ D := fun u hu => by
    have := card_le_card (filter_subset_filter (H.Adj u) hT'T)
    have h' : ((nbrs H u T').card : ℝ) ≤ (nbrs H u T).card := by exact_mod_cast this
    exact h'.trans (hdeg u (hT'T hu))
  obtain ⟨I', hI'T', hI'st, hI'c⟩ := ih _ hlt T' rfl hdeg'
  have hfar : ∀ b ∈ I', ¬ H.Adj v b := fun b hb hadj => by
    have := hI'T' hb
    rw [hT'] at this
    exact (mem_sdiff.1 this).2 (mem_insert_of_mem (mem_filter.2 ⟨(mem_sdiff.1 this).1, hadj⟩))
  refine ⟨insert v I', insert_subset hv (hI'T'.trans hT'T), ?_, ?_⟩
  · intro a ha b hb hab
    rcases mem_insert.1 ha with rfl | ha' <;> rcases mem_insert.1 hb with rfl | hb'
    · exact absurd rfl hab
    · exact hfar b hb'
    · exact fun h => hfar a ha' (H.adj_symm h)
    · exact hI'st a ha' b hb' hab
  · have h1 : T.card ≤ T'.card + (insert v (nbrs H v T)).card := by
      rw [hT']; exact card_le_card_sdiff_add_card
    have h2 : ((insert v (nbrs H v T)).card : ℝ) ≤ D + 1 := by
      have a1 := card_insert_le v (nbrs H v T)
      have a2 : ((insert v (nbrs H v T)).card : ℝ) ≤ (nbrs H v T).card + 1 := by exact_mod_cast a1
      linarith [hdeg v hv]
    have h3 : (insert v I').card = I'.card + 1 := card_insert_of_notMem (fun h => hvT' (hI'T' h))
    have h1' : (T.card : ℝ) ≤ T'.card + (insert v (nbrs H v T)).card := by exact_mod_cast h1
    rw [h3]; push_cast
    nlinarith

/-- a P6-free graph has P̄6-free complement -/
lemma compl_free (hfree : Free G P6) : Free Gᶜ P6ᶜ := by
  rintro ⟨f, hinj, -, hadj⟩
  apply hfree
  refine ⟨f, hinj, fun i => mem_univ _, fun i j => ?_⟩
  have h := hadj i j
  rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj] at h
  by_cases hij : i = j
  · subst hij
    simp only [SimpleGraph.irrefl]
  · have hf : f i ≠ f j := fun e => hij (hinj e)
    constructor
    · intro hG; by_contra hp; exact (h.2 ⟨hij, hp⟩).2 hG
    · intro hp; by_contra hG; exact (h.1 ⟨hf, hG⟩).2 hp

/-- **Proof of Theorem A** (paper, §8). The polynomial Rödl property for P̄6-free graphs, with
exponent `3A`, gives EH(P6) with `τ = 1/((3A+1)(3A+2))`. -/
theorem eh_of_polyRodl {A : ℕ}
    (hR : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Free H P6ᶜ → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∃ T : Finset W, ε ^ (3 * A) * Fintype.card W ≤ T.card ∧ Restricted H ε T) : EHforP6 := by
  obtain ⟨N, hN⟩ : ∃ N, N = (3 * A + 1) * (3 * A + 2) := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; positivity
  refine ⟨((N : ℕ) : ℝ)⁻¹, by positivity, fun W _ _ H _ hfree => ?_⟩
  have hfc := compl_free hfree
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card W := ⟨_, rfl⟩
  rw [← hn]
  have hu0 : (0 : ℝ) ≤ (n : ℝ) ^ ((N : ℝ)⁻¹) := by positivity
  have hu : ((n : ℝ) ^ ((N : ℝ)⁻¹)) ^ N = n := Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) hN0
  generalize hudef : (n : ℝ) ^ ((N : ℝ)⁻¹) = u at hu0 hu ⊢
  by_cases hsmall : u < 2
  · -- small graphs: one or two vertices suffice
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · refine ⟨univ, Or.inl fun a _ b _ hab => absurd (Finset.card_le_one.1 (by
        rw [card_univ, ← hn]; omega) a (mem_univ _) b (mem_univ _)) hab, ?_⟩
      rw [card_univ, ← hn]
      by_contra h
      push Not at h
      have : (n : ℝ) < u ^ N := by
        calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (n : ℝ) ^ N := by
              rcases Nat.eq_zero_or_pos n with h0 | h0
              · rw [h0]; simp [hN0]
              · exact pow_le_pow_right₀ (by exact_mod_cast h0) (Nat.one_le_iff_ne_zero.2 hN0)
          _ < u ^ N := pow_lt_pow_left₀ h (Nat.cast_nonneg _) hN0
      linarith
    · obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by rw [← hn]; omega)
      have hc : ({a, b} : Finset W).card = 2 := card_pair hab
      by_cases hadj : H.Adj a b
      · refine ⟨{a, b}, Or.inl ?_, by rw [hc]; push_cast; linarith⟩
        intro x hx y hy hxy
        simp only [mem_insert, mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact hadj
        · exact H.adj_symm hadj
        · exact absurd rfl hxy
      · refine ⟨{a, b}, Or.inr ?_, by rw [hc]; push_cast; linarith⟩
        intro x hx y hy hxy
        simp only [mem_insert, mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact hadj
        · exact fun h => hadj (H.adj_symm h)
        · exact absurd rfl hxy
  push Not at hsmall
  -- large graphs: `ε = 1/z`, `z = u^{3A+2} = n^{1/(3A+1)}`
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = u ^ (3 * A + 2) := ⟨_, rfl⟩
  have hz4 : 2 * u ≤ z := by
    rw [hz, pow_succ]
    have : (2 : ℝ) ≤ u ^ (3 * A + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (3 * A + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ u ^ (3 * A + 1) := pow_le_pow_left₀ (by norm_num) hsmall _
    nlinarith
  have hzpos : 0 < z := by linarith
  have hzn : z ^ (3 * A + 1) = n := by
    rw [hz, ← pow_mul, ← hu, hN]; ring
  have hε0 : 0 < 1 / z := by positivity
  have hε2 : 1 / z < 1 / 2 := by
    rw [div_lt_div_iff₀ hzpos (by norm_num)]; linarith
  obtain ⟨T, hTc, hTr⟩ := hR W Hᶜ hfc (1 / z) hε0 hε2
  rw [← hn] at hTc
  have hTz : z ≤ T.card := by
    have e : (1 / z) ^ (3 * A) * (n : ℝ) = z := by
      rw [← hzn, pow_succ, one_div_pow]; field_simp
    linarith
  have hεT : 1 ≤ 1 / z * T.card := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hzpos]; linarith
  have hbound : ∀ I : Finset W, (T.card : ℝ) ≤ (1 / z * T.card + 1) * I.card → u ≤ I.card := by
    intro I hI
    have h1 : (T.card : ℝ) ≤ (2 * (1 / z * T.card)) * I.card := by nlinarith
    have h2 : (T.card : ℝ) ≤ (2 / z) * T.card * I.card := by
      have e : 2 * (1 / z * (T.card : ℝ)) * I.card = (2 / z) * T.card * I.card := by ring
      linarith
    have hTpos : (0 : ℝ) < T.card := lt_of_lt_of_le hzpos hTz
    have h3 : z / 2 ≤ I.card := by
      have : (1 : ℝ) ≤ (2 / z) * I.card := by
        have := h2
        rw [mul_assoc, mul_comm (T.card : ℝ), ← mul_assoc] at this
        nlinarith
      rw [div_le_iff₀ (by norm_num)]
      rw [div_mul_eq_mul_div, le_div_iff₀ hzpos] at this
      linarith
    linarith
  rcases hTr with hs | hs
  · obtain ⟨I, -, hIst, hIc⟩ := greedy_stable (H := Hᶜ) (1 / z * T.card) T.card T rfl hs
    refine ⟨I, Or.inl fun a ha b hb hab => ?_, hbound I hIc⟩
    by_contra h
    exact hIst a ha b hb hab ((SimpleGraph.compl_adj H a b).2 ⟨hab, h⟩)
  · obtain ⟨I, -, hIst, hIc⟩ := greedy_stable (H := Hᶜᶜ) (1 / z * T.card) T.card T rfl hs
    refine ⟨I, Or.inr fun a ha b hb hab h => ?_, hbound I hIc⟩
    apply hIst a ha b hb hab
    rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
    exact ⟨hab, fun h' => h'.2 h⟩

end EHP6
