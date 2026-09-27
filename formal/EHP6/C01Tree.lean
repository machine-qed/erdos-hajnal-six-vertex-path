import EHP6.Crux

/-!
# Lemma 8.2 (paper; NSS VII Theorem 7.4), proved by strong induction

Instead of a maximal cograph layout (which needs perfection of cographs), we track, for every large
`F`, a family `Pf` of pairwise anticomplete and a family `Qf` of pairwise complete disjoint subsets of
`F`, all of size `≥ w`, with `(|Pf|·|Qf|)^A · T ≥ |F|`.
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- pairwise disjoint subsets of `F`, each of size at least `w` -/
def GoodFam (F : Finset V) (w : ℝ) (Pf : Finset (Finset V)) : Prop :=
  (∀ P ∈ Pf, P ⊆ F ∧ w ≤ P.card) ∧ (∀ P ∈ Pf, ∀ Q ∈ Pf, P ≠ Q → Disjoint P Q)

omit [Fintype V] in
lemma combine {m : ℕ} {F : Finset V} {w : ℝ} (hw : 0 < w) (R R' : Finset V → Finset V → Prop)
    (hmono : ∀ A B A' B', A' ⊆ A → B' ⊆ B → R A B → R A' B')
    (B : Fin m → Finset V) (hBF : ∀ i, B i ⊆ F) (hBd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hBR : ∀ i j, i ≠ j → R (B i) (B j)) (𝒳 𝒴 : Fin m → Finset (Finset V))
    (h𝒳 : ∀ i, GoodFam (B i) w (𝒳 i)) (h𝒴 : ∀ i, GoodFam (B i) w (𝒴 i))
    (h𝒳R : ∀ i, ∀ P ∈ 𝒳 i, ∀ Q ∈ 𝒳 i, P ≠ Q → R P Q)
    (h𝒴R : ∀ i, ∀ P ∈ 𝒴 i, ∀ Q ∈ 𝒴 i, P ≠ Q → R' P Q) (hm : 0 < m) :
    ∃ 𝒳' 𝒴' : Finset (Finset V), GoodFam F w 𝒳' ∧ GoodFam F w 𝒴' ∧
      (∀ P ∈ 𝒳', ∀ Q ∈ 𝒳', P ≠ Q → R P Q) ∧ (∀ P ∈ 𝒴', ∀ Q ∈ 𝒴', P ≠ Q → R' P Q) ∧
      ∑ i, (𝒳 i).card * (𝒴 i).card ≤ 𝒳'.card * 𝒴'.card := by
  have hne : (univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, mem_univ _⟩
  obtain ⟨i₀, -, hi₀⟩ := exists_max_image univ (fun i => (𝒴 i).card) hne
  have key : ∀ i j, ∀ P ∈ 𝒳 i, P ∈ 𝒳 j → i = j := by
    intro i j P hPi hPj
    by_contra hij
    have hP : P.Nonempty := card_pos.1 (by
      have := ((h𝒳 i).1 P hPi).2
      have : (0 : ℝ) < P.card := lt_of_lt_of_le hw this
      exact_mod_cast this)
    obtain ⟨v, hv⟩ := hP
    exact disjoint_left.1 (hBd i j hij) (((h𝒳 i).1 P hPi).1 hv) (((h𝒳 j).1 P hPj).1 hv)
  refine ⟨univ.biUnion 𝒳, 𝒴 i₀, ⟨fun P hP => ?_, fun P hP Q hQ hPQ => ?_⟩,
    ⟨fun P hP => ⟨((h𝒴 i₀).1 P hP).1.trans (hBF i₀), ((h𝒴 i₀).1 P hP).2⟩, (h𝒴 i₀).2⟩,
    fun P hP Q hQ hPQ => ?_, h𝒴R i₀, ?_⟩
  · obtain ⟨i, -, hi⟩ := mem_biUnion.1 hP
    exact ⟨((h𝒳 i).1 P hi).1.trans (hBF i), ((h𝒳 i).1 P hi).2⟩
  · obtain ⟨i, -, hi⟩ := mem_biUnion.1 hP
    obtain ⟨j, -, hj⟩ := mem_biUnion.1 hQ
    by_cases hij : i = j
    · subst hij; exact (h𝒳 i).2 P hi Q hj hPQ
    · exact disjoint_of_subset_left ((h𝒳 i).1 P hi).1
        (disjoint_of_subset_right ((h𝒳 j).1 Q hj).1 (hBd i j hij))
  · obtain ⟨i, -, hi⟩ := mem_biUnion.1 hP
    obtain ⟨j, -, hj⟩ := mem_biUnion.1 hQ
    by_cases hij : i = j
    · subst hij; exact h𝒳R i P hi Q hj hPQ
    · exact hmono _ _ _ _ ((h𝒳 i).1 P hi).1 ((h𝒳 j).1 Q hj).1 (hBR i j hij)
  · rw [card_biUnion (fun i _ j _ hij => disjoint_left.2 fun P hPi hPj => hij (key i j P hPi hPj)),
      sum_mul]
    exact sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hi₀ i (mem_univ _))

omit [Fintype V] in
lemma complete_mono : ∀ A B A' B' : Finset V, A' ⊆ A → B' ⊆ B → Complete G A B → Complete G A' B' :=
  fun _ _ _ _ hA hB h a ha b hb => h a (hA ha) b (hB hb)

omit [Fintype V] in
lemma anticomplete_mono :
    ∀ A B A' B' : Finset V, A' ⊆ A → B' ⊆ B → Anticomplete G A B → Anticomplete G A' B' :=
  fun _ _ _ _ hA hB h a ha b hb => h a (hA ha) b (hB hb)

lemma tree_num {k μ sm pq : ℕ} {A : ℕ} {F b T : ℝ} (hk : 1 ≤ k) (hFb : F / (k : ℝ) ^ A ≤ b)
    (hbμ : b ≤ (μ : ℝ) ^ A * T) (hT : 0 ≤ T) (hsm : k * μ ≤ sm) (hpq : sm ≤ pq) :
    F ≤ ((pq : ℕ) : ℝ) ^ A * T := by
  have hk0 : (0 : ℝ) < (k : ℝ) ^ A := by positivity
  have h1 : F ≤ (k : ℝ) ^ A * b := by rw [div_le_iff₀ hk0] at hFb; linarith
  have h2 : ((k * μ : ℕ) : ℝ) ≤ pq := by exact_mod_cast hsm.trans hpq
  have h3 : ((k * μ : ℕ) : ℝ) ^ A ≤ (pq : ℝ) ^ A := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 A
  push_cast at h3
  rw [mul_pow] at h3
  have h4 : (k : ℝ) ^ A * b ≤ (k : ℝ) ^ A * ((μ : ℝ) ^ A * T) := mul_le_mul_of_nonneg_left hbμ hk0.le
  have h5 := mul_le_mul_of_nonneg_right h3 hT
  nlinarith

/-- the induction behind Lemma 8.2 -/
theorem c01_tree {S : Finset V} {ε T w : ℝ} {A : ℕ} (hε0 : 0 < ε) (hT0 : 0 ≤ T)
    (hw : w ≤ ε ^ A * T) (hw0 : 0 < w)
    (hyp : ∀ F ⊆ S, T ≤ F.card → ∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) * ε ≤ 1 ∧
      ∃ β : Blockade F k (F.card / (k : ℝ) ^ A), β.IsComplete G ∨ β.IsAnticomplete G) :
    ∀ n : ℕ, ∀ F ⊆ S, F.card = n → w ≤ F.card → ∃ Pf Qf : Finset (Finset V),
      GoodFam F w Pf ∧ GoodFam F w Qf ∧
      (∀ P ∈ Pf, ∀ Q ∈ Pf, P ≠ Q → Anticomplete G P Q) ∧
      (∀ P ∈ Qf, ∀ Q ∈ Qf, P ≠ Q → Complete G P Q) ∧
      (F.card : ℝ) ≤ ((Pf.card * Qf.card : ℕ) : ℝ) ^ A * T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hFS hFn hwF
  have hsingle : GoodFam F w {F} := ⟨fun P hP => by rw [mem_singleton.1 hP]; exact ⟨subset_rfl, hwF⟩,
    fun P hP Q hQ h => absurd ((mem_singleton.1 hP).trans (mem_singleton.1 hQ).symm) h⟩
  by_cases hsmall : (F.card : ℝ) < T
  · refine ⟨{F}, {F}, hsingle, hsingle, fun P hP Q hQ h => absurd ((mem_singleton.1 hP).trans
      (mem_singleton.1 hQ).symm) h, fun P hP Q hQ h => absurd ((mem_singleton.1 hP).trans
      (mem_singleton.1 hQ).symm) h, ?_⟩
    simp only [card_singleton, mul_one, Nat.cast_one, one_pow, one_mul]; exact hsmall.le
  push Not at hsmall
  obtain ⟨k, hk2, hkε, β, hβ⟩ := hyp F hFS hsmall
  have hkA : (k : ℝ) ^ A * ε ^ A ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by positivity) hkε
  have hk0 : (0 : ℝ) < (k : ℝ) ^ A := by have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
                                         positivity
  -- every block is large
  have hBw : ∀ i, w ≤ (β.B i).card := fun i => by
    refine le_trans ?_ (β.wid i)
    rw [le_div_iff₀ hk0]
    have := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ ε ^ A)
    nlinarith
  have hm2 : 2 ≤ β.m := by
    have : (2 : ℝ) ≤ β.m := le_trans (by exact_mod_cast hk2) β.len
    exact_mod_cast this
  -- every block is strictly smaller than `F`
  have hBlt : ∀ i, (β.B i).card < F.card := fun i => by
    obtain ⟨j, hj⟩ : ∃ j : Fin β.m, j ≠ i := by
      by_cases h : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
      · exact ⟨⟨0, by omega⟩, fun e => h (by rw [← e])⟩
    have hjne : (β.B j).Nonempty := card_pos.1 (by
      have : (0 : ℝ) < (β.B j).card := lt_of_lt_of_le hw0 (hBw j)
      exact_mod_cast this)
    have h1 : (β.B i ∪ β.B j).card = (β.B i).card + (β.B j).card :=
      card_union_of_disjoint (β.disj i j (Ne.symm hj))
    have h2 : (β.B i ∪ β.B j).card ≤ F.card := card_le_card (union_subset (β.sub i) (β.sub j))
    have := hjne.card_pos
    omega
  have hIH : ∀ i, ∃ Pf Qf : Finset (Finset V), GoodFam (β.B i) w Pf ∧ GoodFam (β.B i) w Qf ∧
      (∀ P ∈ Pf, ∀ Q ∈ Pf, P ≠ Q → Anticomplete G P Q) ∧
      (∀ P ∈ Qf, ∀ Q ∈ Qf, P ≠ Q → Complete G P Q) ∧
      ((β.B i).card : ℝ) ≤ ((Pf.card * Qf.card : ℕ) : ℝ) ^ A * T := fun i =>
    ih _ (hFn ▸ hBlt i) (β.B i) ((β.sub i).trans hFS) rfl (hBw i)
  choose Pf Qf hPf hQf hPfa hQfc hsize using hIH
  -- the block with the smallest product
  have hne : (univ : Finset (Fin β.m)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨i₀, -, hi₀⟩ := exists_min_image univ (fun i => (Pf i).card * (Qf i).card) hne
  have hsm : k * ((Pf i₀).card * (Qf i₀).card) ≤ ∑ i, (Pf i).card * (Qf i).card := by
    have h1 := card_nsmul_le_sum univ (fun i => (Pf i).card * (Qf i).card) _
      (fun i hi => hi₀ i hi)
    rw [card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 : k ≤ β.m := by
      have : (k : ℝ) ≤ β.m := β.len
      exact_mod_cast this
    exact (Nat.mul_le_mul_right _ h2).trans h1
  rcases hβ with hc | ha
  · obtain ⟨𝒳', 𝒴', h1, h2, h3, h4, h5⟩ := combine hw0 (Complete G) (Anticomplete G) complete_mono
      β.B β.sub β.disj hc Qf Pf hQf hPf hQfc hPfa (by omega)
    refine ⟨𝒴', 𝒳', h2, h1, h4, h3, ?_⟩
    refine tree_num (by omega) (β.wid i₀) (hsize i₀) hT0 hsm ?_
    rw [mul_comm (𝒴'.card)]
    calc ∑ i, (Pf i).card * (Qf i).card = ∑ i, (Qf i).card * (Pf i).card :=
          sum_congr rfl fun i _ => mul_comm _ _
      _ ≤ 𝒳'.card * 𝒴'.card := h5
  · obtain ⟨𝒳', 𝒴', h1, h2, h3, h4, h5⟩ := combine hw0 (Anticomplete G) (Complete G)
      anticomplete_mono β.B β.sub β.disj ha Pf Qf hPf hQf hPfa hQfc (by omega)
    exact ⟨𝒳', 𝒴', h1, h2, h3, h4, tree_num (by omega) (β.wid i₀) (hsize i₀) hT0 hsm h5⟩

omit [Fintype V] in
/-- from a family of `r ≥ 1/ε` pairwise `R`-related disjoint sets of size `≥ w`, equal-size pieces form
a set in which every vertex is `H`-adjacent only inside its own piece -/
lemma pieces_sparse {H : SimpleGraph V} [DecidableRel H.Adj] {F : Finset V} {w ε : ℝ} (hw : 0 < w)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (Pf : Finset (Finset V)) (hP : GoodFam F w Pf) (hr : 1 / ε ≤ Pf.card)
    (hloc : ∀ P ∈ Pf, ∀ Q ∈ Pf, P ≠ Q → ∀ a ∈ P, ∀ b ∈ Q, ¬ H.Adj a b) :
    ∃ T ⊆ F, w ≤ T.card ∧ Sparse H ε T := by
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, m₀ = ⌈w⌉₊ := ⟨_, rfl⟩
  have hsub : ∀ P ∈ Pf, ∃ P' ⊆ P, P'.card = m₀ := fun P hPm =>
    exists_subset_card_eq (by rw [hm₀]; exact Nat.ceil_le.2 (hP.1 P hPm).2)
  choose f hf hfc using hsub
  obtain ⟨T, hT⟩ : ∃ T, T = Pf.attach.biUnion (fun P => f P.1 P.2) := ⟨_, rfl⟩
  have hdisj : ∀ P ∈ Pf.attach, ∀ Q ∈ Pf.attach, P ≠ Q → Disjoint (f P.1 P.2) (f Q.1 Q.2) :=
    fun P _ Q _ hPQ => disjoint_of_subset_left (hf _ _) (disjoint_of_subset_right (hf _ _)
      (hP.2 _ P.2 _ Q.2 (fun e => hPQ (Subtype.ext e))))
  have hTc : T.card = Pf.card * m₀ := by
    rw [hT, card_biUnion hdisj]
    simp only [hfc, sum_const, card_attach, smul_eq_mul]
  have hrpos : 1 ≤ Pf.card := by
    have : (1 : ℝ) ≤ Pf.card := le_trans (by rw [le_div_iff₀ hε0]; linarith) hr
    exact_mod_cast this
  refine ⟨T, ?_, ?_, fun v hv => ?_⟩
  · rw [hT]; exact biUnion_subset.2 fun P _ => (hf _ _).trans (hP.1 _ P.2).1
  · rw [hTc]; push_cast
    have : w ≤ m₀ := by rw [hm₀]; exact Nat.le_ceil _
    have : (1 : ℝ) ≤ Pf.card := by exact_mod_cast hrpos
    nlinarith [show (0 : ℝ) ≤ m₀ from Nat.cast_nonneg _]
  · rw [hT] at hv
    obtain ⟨P, -, hvP⟩ := mem_biUnion.1 hv
    have hnb : nbrs H v T ⊆ f P.1 P.2 := by
      intro u hu
      obtain ⟨huT, hvu⟩ := mem_filter.1 hu
      rw [hT] at huT
      obtain ⟨Q, -, huQ⟩ := mem_biUnion.1 huT
      by_cases hPQ : P = Q
      · rw [hPQ]; exact huQ
      · exact absurd hvu (hloc _ P.2 _ Q.2 (fun e => hPQ (Subtype.ext e)) v (hf _ _ hvP) u
          (hf _ _ huQ))
    have h1 : ((nbrs H v T).card : ℝ) ≤ m₀ := by
      have := card_le_card hnb; rw [hfc] at this; exact_mod_cast this
    have h2 : (m₀ : ℝ) ≤ ε * T.card := by
      rw [hTc]; push_cast
      have := (div_le_iff₀ hε0).1 hr
      nlinarith [show (0 : ℝ) ≤ m₀ from Nat.cast_nonneg _]
    linarith

/-- **Lemma 8.2** (NSS VII Theorem 7.4): if every `F ⊆ S` with `|F| ≥ ε^{2A}|S|` has a pure
`(k, |F|/k^A)`-blockade with `k ∈ [2, 1/ε]`, then `S` has an `ε`-restricted subset of size
`≥ ε^{3A}|S|`. -/
theorem c01_lemma2 {S : Finset V} {ε : ℝ} {A : ℕ} (hA : 1 ≤ A) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hyp : ∀ F ⊆ S, ε ^ (2 * A) * S.card ≤ F.card → ∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) * ε ≤ 1 ∧
      ∃ β : Blockade F k (F.card / (k : ℝ) ^ A), β.IsComplete G ∨ β.IsAnticomplete G) :
    ∃ T ⊆ S, ε ^ (3 * A) * S.card ≤ T.card ∧ Restricted G ε T := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe
    exact ⟨∅, subset_rfl, by simp, Or.inl fun v hv => absurd hv (notMem_empty v)⟩
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hw0 : 0 < ε ^ (3 * A) * S.card := by positivity
  have hwT : ε ^ (3 * A) * S.card ≤ ε ^ A * (ε ^ (2 * A) * S.card) := by
    rw [show 3 * A = A + 2 * A by ring, pow_add]; ring_nf; exact le_rfl
  have hwS : ε ^ (3 * A) * S.card ≤ S.card := by
    have : ε ^ (3 * A) ≤ 1 := pow_le_one₀ hε0.le hε1.le
    nlinarith
  obtain ⟨Pf, Qf, hP, hQ, hPa, hQc, hsize⟩ := c01_tree hε0 (by positivity) hwT hw0 hyp S.card S
    subset_rfl rfl hwS
  -- `(|Pf|·|Qf|)^A ≥ ε^{-2A}`, so one of the families has at least `1/ε` members
  have hpq : 1 / ε ^ 2 ≤ ((Pf.card * Qf.card : ℕ) : ℝ) := by
    by_contra h
    push Not at h
    have h1 : ((Pf.card * Qf.card : ℕ) : ℝ) ^ A ≤ (1 / ε ^ 2) ^ A :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h.le A
    have h2 : ((Pf.card * Qf.card : ℕ) : ℝ) ^ A < (1 / ε ^ 2) ^ A :=
      pow_lt_pow_left₀ h (Nat.cast_nonneg _) (by omega)
    have h3 : (1 / ε ^ 2) ^ A * (ε ^ (2 * A) * S.card) = S.card := by
      rw [pow_mul, one_div_pow, ← pow_mul]; field_simp
    have h4 := mul_lt_mul_of_pos_right h2 (by positivity : (0 : ℝ) < ε ^ (2 * A) * S.card)
    linarith
  have hcase : 1 / ε ≤ (Pf.card : ℝ) ∨ 1 / ε ≤ (Qf.card : ℝ) := by
    by_contra h
    push Not at h
    have h1 : ((Pf.card : ℝ)) * Qf.card < 1 / ε * (1 / ε) :=
      mul_lt_mul'' h.1 h.2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    push_cast at hpq
    have : 1 / ε * (1 / ε) = 1 / ε ^ 2 := by field_simp <;> ring
    linarith
  rcases hcase with hr | hr
  · obtain ⟨T, hT, hTc, hTs⟩ := pieces_sparse hw0 hε0 hε1.le Pf hP hr hPa
    exact ⟨T, hT, hTc, Or.inl hTs⟩
  · obtain ⟨T, hT, hTc, hTs⟩ := pieces_sparse (H := Gᶜ) hw0 hε0 hε1.le Qf hQ hr
      (fun P hP' Q hQ' hPQ a ha b hb hab => ((SimpleGraph.compl_adj G a b).1 hab).2
        (hQc P hP' Q hQ' hPQ a ha b hb))
    exact ⟨T, hT, hTc, Or.inr hTs⟩

end EHP6
