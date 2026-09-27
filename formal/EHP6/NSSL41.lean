import EHP6.MDGallai

/-!
# NSS VII Lemma 4.1 (paper Lemma 0.3)

If every anticomponent of `G[S]` has fewer than `|S|/k` vertices (`k ≥ 2`), then `G[S]` has a complete
`(k, |S|/k²)`-blockade: group the anticomponents greedily into `k` groups of total size `≥ |S|/k²`.
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
lemma comp_unique {H : SimpleGraph V} {N D D' : Finset V} (hD : IsComp H N D) (hD' : IsComp H N D')
    {v : V} (hv : v ∈ D) (hv' : v ∈ D') : D' ⊆ D := by
  intro z hz
  by_contra hzD
  obtain ⟨p, hp, q, hq, hpq⟩ := hD'.2.2.1 (D' ∩ D) inter_subset_left ⟨v, mem_inter.2 ⟨hv', hv⟩⟩
    ⟨z, mem_sdiff.2 ⟨hz, fun h => hzD (mem_inter.1 h).2⟩⟩
  obtain ⟨hqD', hqn⟩ := mem_sdiff.1 hq
  have hqD : q ∉ D := fun h => hqn (mem_inter.2 ⟨hqD', h⟩)
  exact hD.2.2.2 p (mem_inter.1 hp).2 q (mem_sdiff.2 ⟨hD'.1 hqD', hqD⟩) hpq

omit [Fintype V] in
lemma comp_to_anti {S K : Finset V} (h : IsComp Gᶜ S K) : IsAnticomponent G S K := by
  refine ⟨h.1, h.2.1, fun P hP hPne hrest => ?_, fun t ht k hk => ?_⟩
  · obtain ⟨p, hp, q, hq, hpq⟩ := h.2.2.1 P hP hPne hrest
    exact ⟨p, hp, q, hq, ((SimpleGraph.compl_adj G p q).1 hpq).2⟩
  · have hne : k ≠ t := fun e => (mem_sdiff.1 ht).2 (e ▸ hk)
    have := h.2.2.2 k hk t ht
    rw [SimpleGraph.compl_adj] at this
    push Not at this
    exact G.adj_symm (this hne)

omit [Fintype V] in
/-- from a family of total size `≥ w` whose members are all `< c`, a subfamily of total size in
`[w, w + c)` -/
lemma exists_subfam {w c : ℝ} (hw : 0 < w) (f : Finset V → ℝ) :
    ∀ 𝒦 : Finset (Finset V), (∀ K ∈ 𝒦, f K < c) → w ≤ ∑ K ∈ 𝒦, f K →
      ∃ 𝒦' ⊆ 𝒦, w ≤ ∑ K ∈ 𝒦', f K ∧ ∑ K ∈ 𝒦', f K < w + c := by
  intro 𝒦
  induction 𝒦 using Finset.induction_on with
  | empty => intro _ h; simp at h; linarith
  | insert K₀ 𝒦₀ hK₀ ih =>
    intro hc hsum
    rw [sum_insert hK₀] at hsum
    by_cases h₀ : w ≤ ∑ K ∈ 𝒦₀, f K
    · obtain ⟨𝒦', h1, h2, h3⟩ := ih (fun K hK => hc K (mem_insert_of_mem hK)) h₀
      exact ⟨𝒦', h1.trans (subset_insert _ _), h2, h3⟩
    · push Not at h₀
      refine ⟨insert K₀ 𝒦₀, subset_rfl, by rw [sum_insert hK₀]; exact hsum, ?_⟩
      rw [sum_insert hK₀]
      have := hc K₀ (mem_insert_self _ _)
      linarith

/-- the grouping invariant after `j` groups -/
def Grp (𝒦 : Finset (Finset V)) (w c : ℝ) (j : ℕ) : Prop :=
  ∃ 𝒢 : ℕ → Finset (Finset V), (∀ i < j, 𝒢 i ⊆ 𝒦) ∧
    (∀ i < j, ∀ i' < j, i ≠ i' → Disjoint (𝒢 i) (𝒢 i')) ∧
    (∀ i < j, w ≤ ∑ K ∈ 𝒢 i, (K.card : ℝ)) ∧
    ∑ K ∈ (range j).biUnion 𝒢, (K.card : ℝ) ≤ j * (w + c)

omit [Fintype V] in
lemma grp_step {𝒦 : Finset (Finset V)} {w c n : ℝ} {j : ℕ} (hw : 0 < w)
    (hc : ∀ K ∈ 𝒦, (K.card : ℝ) < c) (hn : ∑ K ∈ 𝒦, (K.card : ℝ) = n)
    (hroom : w ≤ n - j * (w + c)) (h : Grp 𝒦 w c j) : Grp 𝒦 w c (j + 1) := by
  obtain ⟨𝒢, h1, h2, h3, h4⟩ := h
  obtain ⟨U, hU⟩ : ∃ U, U = (range j).biUnion 𝒢 := ⟨_, rfl⟩
  rw [← hU] at h4
  have hUK : U ⊆ 𝒦 := by
    rw [hU]; exact biUnion_subset.2 fun i hi => h1 i (mem_range.1 hi)
  have hrest : ∑ K ∈ 𝒦 \ U, (K.card : ℝ) = n - ∑ K ∈ U, (K.card : ℝ) := by
    rw [← hn, ← sum_sdiff hUK]; ring
  obtain ⟨𝒢j, hj1, hj2, hj3⟩ := exists_subfam hw (fun K => (K.card : ℝ)) (𝒦 \ U)
    (fun K hK => hc K (mem_sdiff.1 hK).1) (by rw [hrest]; linarith)
  refine ⟨fun i => if i = j then 𝒢j else 𝒢 i, fun i hi => ?_, fun i hi i' hi' hii' => ?_,
    fun i hi => ?_, ?_⟩
  · by_cases hij : i = j
    · subst hij; simp only [↓reduceIte]; exact hj1.trans sdiff_subset
    · simp only [if_neg hij]; exact h1 i (by omega)
  · have hjU : ∀ i < j, Disjoint 𝒢j (𝒢 i) := fun i hi => by
      refine disjoint_of_subset_left hj1 ?_
      rw [disjoint_left]; intro K hK hKi
      exact (mem_sdiff.1 hK).2 (by rw [hU]; exact mem_biUnion.2 ⟨i, mem_range.2 hi, hKi⟩)
    by_cases hij : i = j <;> by_cases hi'j : i' = j
    · exact absurd (hij.trans hi'j.symm) hii'
    · subst hij; simp only [↓reduceIte, if_neg hi'j]; exact hjU i' (by omega)
    · subst hi'j; simp only [↓reduceIte, if_neg hij]; exact (hjU i (by omega)).symm
    · simp only [if_neg hij, if_neg hi'j]; exact h2 i (by omega) i' (by omega) hii'
  · by_cases hij : i = j
    · subst hij; simp only [↓reduceIte]; exact hj2
    · simp only [if_neg hij]; exact h3 i (by omega)
  · have e : (range (j + 1)).biUnion (fun i => if i = j then 𝒢j else 𝒢 i) = U ∪ 𝒢j := by
      rw [range_add_one, biUnion_insert, hU, union_comm]
      simp only [↓reduceIte]
      congr 1
      exact biUnion_congr rfl fun i hi => by rw [if_neg (by have := mem_range.1 hi; omega)]
    rw [e]
    have hdisj : Disjoint U 𝒢j := by
      rw [disjoint_right]; intro K hK hKU; exact (mem_sdiff.1 (hj1 hK)).2 hKU
    rw [sum_union hdisj]
    push_cast
    linarith

omit [Fintype V] in
lemma grp_all {𝒦 : Finset (Finset V)} {w c n : ℝ} {k : ℕ} (hw : 0 < w)
    (hc : ∀ K ∈ 𝒦, (K.card : ℝ) < c) (hn : ∑ K ∈ 𝒦, (K.card : ℝ) = n)
    (hroom : w ≤ n - (k - 1 : ℝ) * (w + c)) (hwc : 0 ≤ w + c) :
    ∀ j ≤ k, Grp 𝒦 w c j
  | 0, _ => ⟨fun _ => ∅, fun i h => absurd h (Nat.not_lt_zero i),
      fun i h => absurd h (Nat.not_lt_zero i), fun i h => absurd h (Nat.not_lt_zero i), by simp⟩
  | j + 1, h => grp_step hw hc hn (by
      have : (j : ℝ) ≤ k - 1 := by
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
        linarith
      nlinarith) (grp_all hw hc hn hroom hwc j (by omega))

/-- **NSS VII Lemma 4.1** (paper Lemma 0.3), proved. -/
theorem nss_L41_proof (S : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hsmall : ∀ K, IsAnticomponent G S K → (K.card : ℝ) < S.card / k) :
    ∃ β : Blockade S k (S.card / (k : ℝ) ^ 2), β.IsComplete G := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe
    refine ⟨⟨k, fun _ => ∅, le_rfl, fun _ => empty_subset _, fun _ => by simp,
      fun _ _ _ => disjoint_empty_left _⟩, fun i j _ a ha => absurd ha (notMem_empty a)⟩
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  -- the anticomponents
  have hex : ∀ v ∈ S, ∃ D, IsComp Gᶜ S D ∧ v ∈ D := fun v hv => by
    obtain ⟨D, hD, hvD, -⟩ := exists_comp (G := Gᶜ) hv
    exact ⟨D, hD, hvD⟩
  choose comp hcomp hvcomp using hex
  obtain ⟨𝒦, h𝒦⟩ : ∃ 𝒦 : Finset (Finset V), 𝒦 = S.attach.image (fun v => comp v.1 v.2) :=
    ⟨_, rfl⟩
  have hKc : ∀ K ∈ 𝒦, IsComp Gᶜ S K := fun K hK => by
    rw [h𝒦] at hK; obtain ⟨v, -, rfl⟩ := mem_image.1 hK; exact hcomp _ _
  have hKdisj : ∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → Disjoint K K' := fun K hK K' hK' hne => by
    rw [disjoint_left]; intro v hv hv'
    exact hne (subset_antisymm (comp_unique (hKc K' hK') (hKc K hK) hv' hv)
      (comp_unique (hKc K hK) (hKc K' hK') hv hv'))
  have hcover : 𝒦.biUnion id = S := by
    apply subset_antisymm
    · exact biUnion_subset.2 fun K hK => (hKc K hK).1
    · intro v hv
      exact mem_biUnion.2 ⟨comp v hv, by rw [h𝒦]; exact mem_image.2 ⟨⟨v, hv⟩, mem_attach _ _, rfl⟩,
        hvcomp v hv⟩
  have hsum : ∑ K ∈ 𝒦, (K.card : ℝ) = S.card := by
    have := card_biUnion (s := 𝒦) (t := id) (fun K hK K' hK' h => hKdisj K hK K' hK' h)
    rw [hcover] at this
    simp only [id] at this
    exact_mod_cast this.symm
  have hsmall' : ∀ K ∈ 𝒦, (K.card : ℝ) < S.card / k := fun K hK => hsmall K (comp_to_anti (hKc K hK))
  have hcompl : ∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → Complete G K K' := fun K hK K' hK' hne a ha b hb => by
    have hbK : b ∉ K := fun h => disjoint_left.1 (hKdisj K hK K' hK' hne) h hb
    have := (comp_to_anti (hKc K hK)).2.2.2 b (mem_sdiff.2 ⟨(hKc K' hK').1 hb, hbK⟩) a ha
    exact G.adj_symm this
  -- group them
  have hw : 0 < (S.card : ℝ) / (k : ℝ) ^ 2 := by positivity
  have hroom : (S.card : ℝ) / (k : ℝ) ^ 2 ≤
      S.card - ((k : ℝ) - 1) * (S.card / (k : ℝ) ^ 2 + S.card / k) := by
    have e : ((k : ℝ) - 1) * (S.card / (k : ℝ) ^ 2 + S.card / k) =
        S.card - S.card / (k : ℝ) ^ 2 := by field_simp <;> ring
    rw [e]; linarith
  obtain ⟨𝒢, hG1, hG2, hG3, -⟩ := grp_all hw hsmall' hsum hroom (by positivity) k le_rfl
  -- the blockade
  have hGdisj : ∀ i < k, ∀ K ∈ 𝒢 i, ∀ K' ∈ 𝒢 i, K ≠ K' → Disjoint K K' := fun i hi K hK K' hK' h =>
    hKdisj K (hG1 i hi hK) K' (hG1 i hi hK') h
  refine ⟨⟨k, fun i => (𝒢 i).biUnion id, le_rfl, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩,
    fun i j hij => ?_⟩
  · rw [← hcover]; exact biUnion_subset_biUnion_of_subset_left _ (hG1 i i.2)
  · show (S.card : ℝ) / (k : ℝ) ^ 2 ≤ (((𝒢 i).biUnion id).card : ℝ)
    rw [card_biUnion (t := id) (fun K hK K' hK' h => hGdisj i i.2 K hK K' hK' h)]
    simp only [id]; push_cast; exact hG3 i i.2
  · rw [disjoint_left]; intro v hv hv'
    obtain ⟨K, hK, hvK⟩ := mem_biUnion.1 hv
    obtain ⟨K', hK', hvK'⟩ := mem_biUnion.1 hv'
    have hne : K ≠ K' := fun e => disjoint_left.1
      (hG2 i i.2 j j.2 (fun h => hij (Fin.ext h))) hK (e ▸ hK')
    exact disjoint_left.1 (hKdisj K (hG1 i i.2 hK) K' (hG1 j j.2 hK') hne) hvK hvK'
  · intro a ha b hb
    obtain ⟨K, hK, haK⟩ := mem_biUnion.1 ha
    obtain ⟨K', hK', hbK'⟩ := mem_biUnion.1 hb
    have hne : K ≠ K' := fun e => disjoint_left.1
      (hG2 i i.2 j j.2 (fun h => hij (Fin.ext h))) hK (e ▸ hK')
    exact hcompl K (hG1 i i.2 hK) K' (hG1 j j.2 hK') hne a haK b hbK'

end EHP6
