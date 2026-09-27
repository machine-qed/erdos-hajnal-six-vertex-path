import EHP6.Comb

/-!
# Theorem 5.1 (layout theorem, semisparse form): layouts, decided and wrong pairs
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- a layout of `S`: pairwise disjoint nonempty blocks `ℱ` and a symmetric set `𝒥` of ordered pairs of
distinct blocks declared complete (and complete in `G`) -/
def IsLayout (S : Finset V) (ℱ : Finset (Finset V)) (𝒥 : Finset (Finset V × Finset V)) : Prop :=
  (∀ A ∈ ℱ, A ⊆ S ∧ A.Nonempty) ∧ (∀ A ∈ ℱ, ∀ B ∈ ℱ, A ≠ B → Disjoint A B) ∧
  (∀ p ∈ 𝒥, p.1 ∈ ℱ ∧ p.2 ∈ ℱ ∧ p.1 ≠ p.2 ∧ Complete G p.1 p.2) ∧ (∀ p ∈ 𝒥, (p.2, p.1) ∈ 𝒥)

/-- decided ordered pairs: distinct vertices of `S` not in a common block -/
noncomputable def decided (S : Finset V) (ℱ : Finset (Finset V)) : Finset (V × V) :=
  (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ ∀ A ∈ ℱ, ¬ (p.1 ∈ A ∧ p.2 ∈ A))

variable (G) in
/-- wrong ordered pairs: adjacent, in distinct blocks not declared complete -/
noncomputable def wrong (S : Finset V) (ℱ : Finset (Finset V)) (𝒥 : Finset (Finset V × Finset V)) :
    Finset (V × V) :=
  (S ×ˢ S).filter (fun p => G.Adj p.1 p.2 ∧
    ∃ A ∈ ℱ, ∃ B ∈ ℱ, A ≠ B ∧ p.1 ∈ A ∧ p.2 ∈ B ∧ (A, B) ∉ 𝒥)

/-- ordered pairs inside distinct members of a family -/
noncomputable def crossPairs (ℬ : Finset (Finset V)) : Finset (V × V) :=
  ℬ.offDiag.biUnion (fun q => q.1 ×ˢ q.2)

variable (G) in
/-- the refined blocks: `A` replaced by the members of `ℬ` -/
noncomputable def refF (ℱ : Finset (Finset V)) (A : Finset V) (ℬ : Finset (Finset V)) :
    Finset (Finset V) := ℱ.erase A ∪ ℬ

variable (G) in
/-- the refined complete-pairs -/
noncomputable def refJ (ℱ : Finset (Finset V)) (𝒥 : Finset (Finset V × Finset V)) (A : Finset V)
    (ℬ : Finset (Finset V)) : Finset (Finset V × Finset V) :=
  𝒥.filter (fun p => p.1 ≠ A ∧ p.2 ≠ A) ∪ (ℬ ×ˢ ℱ).filter (fun p => (A, p.2) ∈ 𝒥) ∪
    (ℱ ×ˢ ℬ).filter (fun p => (p.1, A) ∈ 𝒥) ∪ ℬ.offDiag.filter (fun p => Complete G p.1 p.2)

section refine
variable {S : Finset V} {ℱ : Finset (Finset V)} {𝒥 : Finset (Finset V × Finset V)} {A : Finset V}
  {ℬ : Finset (Finset V)}

omit [Fintype V] in
lemma ref_notmem (hL : IsLayout G S ℱ 𝒥) (hA : A ∈ ℱ) (hℬ : ∀ B ∈ ℬ, B ⊆ A ∧ B.Nonempty)
    {B C : Finset V} (hB : B ∈ ℬ) (hC : C ∈ ℱ.erase A) : Disjoint B C := by
  obtain ⟨hCA, hCℱ⟩ := mem_erase.1 hC
  exact disjoint_of_subset_left (hℬ B hB).1 (hL.2.1 A hA C hCℱ (Ne.symm hCA))

omit [Fintype V] in
lemma ref_ne (hL : IsLayout G S ℱ 𝒥) (hA : A ∈ ℱ) (hℬ : ∀ B ∈ ℬ, B ⊆ A ∧ B.Nonempty)
    {B C : Finset V} (hB : B ∈ ℬ) (hC : C ∈ ℱ.erase A) : B ≠ C := by
  intro e; subst e
  obtain ⟨v, hv⟩ := (hℬ B hB).2
  exact disjoint_left.1 (ref_notmem hL hA hℬ hB hC) hv hv

omit [Fintype V] in
lemma ref_isLayout (hL : IsLayout G S ℱ 𝒥) (hA : A ∈ ℱ) (hℬ : ∀ B ∈ ℬ, B ⊆ A ∧ B.Nonempty)
    (hℬd : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Disjoint B B') :
    IsLayout G S (refF ℱ A ℬ) (refJ G ℱ 𝒥 A ℬ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hL
  have hAS := (h1 A hA).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB
    rcases mem_union.1 hB with h | h
    · exact h1 B (mem_erase.1 h).2
    · exact ⟨(hℬ B h).1.trans hAS, (hℬ B h).2⟩
  · intro B hB C hC hBC
    rcases mem_union.1 hB with hB' | hB' <;> rcases mem_union.1 hC with hC' | hC'
    · exact h2 B (mem_erase.1 hB').2 C (mem_erase.1 hC').2 hBC
    · exact (ref_notmem ⟨h1, h2, h3, h4⟩ hA hℬ hC' hB').symm
    · exact ref_notmem ⟨h1, h2, h3, h4⟩ hA hℬ hB' hC'
    · exact hℬd B hB' C hC' hBC
  · intro p hp
    simp only [refJ, mem_union, mem_filter, mem_product, mem_offDiag] at hp
    rcases hp with ((⟨hp𝒥, hp1, hp2⟩ | ⟨⟨hpB, hpF⟩, hAp⟩) | ⟨⟨hpF, hpB⟩, hpA⟩) | ⟨⟨hpB1, hpB2, hne⟩, hc⟩
    · obtain ⟨m1, m2, ne, c⟩ := h3 p hp𝒥
      exact ⟨mem_union_left _ (mem_erase.2 ⟨hp1, m1⟩), mem_union_left _ (mem_erase.2 ⟨hp2, m2⟩), ne, c⟩
    · obtain ⟨-, m2, ne, c⟩ := h3 _ hAp
      have hC : p.2 ∈ ℱ.erase A := mem_erase.2 ⟨Ne.symm ne, m2⟩
      exact ⟨mem_union_right _ hpB, mem_union_left _ hC, ref_ne ⟨h1, h2, h3, h4⟩ hA hℬ hpB hC,
        fun a ha b hb => c a ((hℬ _ hpB).1 ha) b hb⟩
    · obtain ⟨m1, -, ne, c⟩ := h3 _ hpA
      have hC : p.1 ∈ ℱ.erase A := mem_erase.2 ⟨ne, m1⟩
      exact ⟨mem_union_left _ hC, mem_union_right _ hpB,
        Ne.symm (ref_ne ⟨h1, h2, h3, h4⟩ hA hℬ hpB hC), fun a ha b hb => c a ha b ((hℬ _ hpB).1 hb)⟩
    · exact ⟨mem_union_right _ hpB1, mem_union_right _ hpB2, hne, hc⟩
  · intro p hp
    simp only [refJ, mem_union, mem_filter, mem_product, mem_offDiag] at hp ⊢
    rcases hp with ((⟨hp𝒥, hp1, hp2⟩ | ⟨⟨hpB, hpF⟩, hAp⟩) | ⟨⟨hpF, hpB⟩, hpA⟩) | ⟨⟨hpB1, hpB2, hne⟩, hc⟩
    · exact Or.inl (Or.inl (Or.inl ⟨h4 p hp𝒥, hp2, hp1⟩))
    · exact Or.inl (Or.inr ⟨⟨hpF, hpB⟩, h4 _ hAp⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨⟨hpB, hpF⟩, h4 _ hpA⟩))
    · exact Or.inr ⟨⟨hpB2, hpB1, Ne.symm hne⟩, fun a ha b hb => G.adj_symm (hc b hb a ha)⟩

end refine

variable (G) in
/-- the possible new wrong pairs: edges between non-complete pairs of new blocks -/
noncomputable def wrongR (ℬ : Finset (Finset V)) : Finset (V × V) :=
  (ℬ.offDiag.filter (fun q => ¬ Complete G q.1 q.2)).biUnion
    (fun q => (q.1 ×ˢ q.2).filter (fun p => G.Adj p.1 p.2))

section refine2
variable {S : Finset V} {ℱ : Finset (Finset V)} {𝒥 : Finset (Finset V × Finset V)} {A : Finset V}
  {ℬ : Finset (Finset V)}

omit [Fintype V] in
lemma ref_wrong_subset (hL : IsLayout G S ℱ 𝒥) (hA : A ∈ ℱ)
    (hℬ : ∀ B ∈ ℬ, B ⊆ A ∧ B.Nonempty) :
    wrong G S (refF ℱ A ℬ) (refJ G ℱ 𝒥 A ℬ) ⊆ wrong G S ℱ 𝒥 ∪ wrongR G ℬ := by
  intro p hp
  simp only [wrong, mem_filter] at hp
  obtain ⟨hpS, hadj, A₁, hA₁, A₂, hA₂, hne, hp1, hp2, hJ⟩ := hp
  have hJ' : ∀ q, q ∈ refJ G ℱ 𝒥 A ℬ → q ≠ (A₁, A₂) := fun q hq e => hJ (e ▸ hq)
  simp only [refJ, mem_union, mem_filter, mem_product, mem_offDiag, not_or, not_and] at hJ
  obtain ⟨⟨⟨hJ1, hJ2⟩, hJ3⟩, hJ4⟩ := hJ
  rcases mem_union.1 hA₁ with h₁ | h₁ <;> rcases mem_union.1 hA₂ with h₂ | h₂
  · -- both old blocks
    refine mem_union_left _ (mem_filter.2 ⟨hpS, hadj, A₁, (mem_erase.1 h₁).2, A₂, (mem_erase.1 h₂).2,
      hne, hp1, hp2, fun h => ?_⟩)
    exact hJ1 h (mem_erase.1 h₁).1 (mem_erase.1 h₂).1
  · -- first old, second new
    refine mem_union_left _ (mem_filter.2 ⟨hpS, hadj, A₁, (mem_erase.1 h₁).2, A, hA,
      (mem_erase.1 h₁).1, hp1, (hℬ A₂ h₂).1 hp2, fun h => ?_⟩)
    exact hJ3 ⟨(mem_erase.1 h₁).2, h₂⟩ h
  · -- first new, second old
    refine mem_union_left _ (mem_filter.2 ⟨hpS, hadj, A, hA, A₂, (mem_erase.1 h₂).2,
      Ne.symm (mem_erase.1 h₂).1, (hℬ A₁ h₁).1 hp1, hp2, fun h => ?_⟩)
    exact hJ2 ⟨h₁, (mem_erase.1 h₂).2⟩ h
  · -- both new
    refine mem_union_right _ (mem_biUnion.2 ⟨(A₁, A₂), mem_filter.2 ⟨mem_offDiag.2 ⟨h₁, h₂, hne⟩,
      fun hc => hJ4 ⟨h₁, h₂, hne⟩ hc⟩, mem_filter.2 ⟨mem_product.2 ⟨hp1, hp2⟩, hadj⟩⟩)

omit [Fintype V] in
lemma card_crossPairs (hℬd : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Disjoint B B') :
    ((crossPairs ℬ).card : ℝ) = ∑ q ∈ ℬ.offDiag, ((q.1.card : ℝ) * q.2.card) := by
  unfold crossPairs
  rw [card_biUnion]
  · push_cast; refine sum_congr rfl fun q _ => ?_; rw [card_product]; push_cast; ring
  · intro q hq q' hq' hqq'
    refine disjoint_left.2 ?_
    rintro ⟨a, b⟩ h h'
    obtain ⟨ha, hb⟩ := mem_product.1 h
    obtain ⟨ha', hb'⟩ := mem_product.1 h'
    obtain ⟨hq1, hq2, -⟩ := mem_offDiag.1 hq
    obtain ⟨hq1', hq2', -⟩ := mem_offDiag.1 hq'
    have e1 : q.1 = q'.1 := by
      by_contra hc; exact disjoint_left.1 (hℬd _ hq1 _ hq1' hc) ha ha'
    have e2 : q.2 = q'.2 := by
      by_contra hc; exact disjoint_left.1 (hℬd _ hq2 _ hq2' hc) hb hb'
    exact hqq' (Prod.ext e1 e2)

omit [Fintype V] in
lemma card_wrongR {x : ℝ} (hx : 0 ≤ x) (hℬd : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Disjoint B B')
    (hsemi : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Complete G B B' ∨ WeaklySparse G x B B') :
    ((wrongR G ℬ).card : ℝ) ≤ x * (crossPairs ℬ).card := by
  rw [card_crossPairs hℬd, mul_sum]
  unfold wrongR
  calc ((ℬ.offDiag.filter (fun q => ¬ Complete G q.1 q.2)).biUnion
        (fun q => (q.1 ×ˢ q.2).filter (fun p => G.Adj p.1 p.2))).card
      ≤ ∑ q ∈ ℬ.offDiag.filter (fun q => ¬ Complete G q.1 q.2), (edgesBetween G q.1 q.2 : ℝ) := by
        have := card_biUnion_le (s := ℬ.offDiag.filter (fun q => ¬ Complete G q.1 q.2))
          (t := fun q => (q.1 ×ˢ q.2).filter (fun p => G.Adj p.1 p.2))
        exact_mod_cast this
    _ ≤ ∑ q ∈ ℬ.offDiag.filter (fun q => ¬ Complete G q.1 q.2), x * ((q.1.card : ℝ) * q.2.card) := by
        refine sum_le_sum fun q hq => ?_
        obtain ⟨hq, hnc⟩ := mem_filter.1 hq
        obtain ⟨h1, h2, hne⟩ := mem_offDiag.1 hq
        have := ((hsemi _ h1 _ h2 hne).resolve_left hnc)
        unfold WeaklySparse at this; linarith [show x * q.1.card * q.2.card = x * (q.1.card * q.2.card) by ring]
    _ ≤ ∑ q ∈ ℬ.offDiag, x * ((q.1.card : ℝ) * q.2.card) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)

lemma ref_decided (hL : IsLayout G S ℱ 𝒥) (hA : A ∈ ℱ) (hℬ : ∀ B ∈ ℬ, B ⊆ A ∧ B.Nonempty)
    (hℬd : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Disjoint B B') :
    Disjoint (decided S ℱ) (crossPairs ℬ) ∧ decided S ℱ ∪ crossPairs ℬ ⊆ decided S (refF ℱ A ℬ) := by
  have hAS := (hL.1 A hA).1
  have hcross : ∀ p ∈ crossPairs ℬ, ∃ B ∈ ℬ, ∃ B' ∈ ℬ, B ≠ B' ∧ p.1 ∈ B ∧ p.2 ∈ B' := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_biUnion.1 hp
    obtain ⟨h1, h2, hne⟩ := mem_offDiag.1 hq
    exact ⟨q.1, h1, q.2, h2, hne, (mem_product.1 hpq).1, (mem_product.1 hpq).2⟩
  refine ⟨?_, ?_⟩
  · rw [disjoint_left]
    intro p hp hp'
    obtain ⟨B, hB, B', hB', -, h1, h2⟩ := hcross p hp'
    exact (mem_filter.1 hp).2.2 A hA ⟨(hℬ B hB).1 h1, (hℬ B' hB').1 h2⟩
  · intro p hp
    rcases mem_union.1 hp with hp | hp
    · obtain ⟨hpS, hne, hno⟩ := mem_filter.1 hp
      refine mem_filter.2 ⟨hpS, hne, fun C hC ⟨h1, h2⟩ => ?_⟩
      rcases mem_union.1 hC with hC | hC
      · exact hno C (mem_erase.1 hC).2 ⟨h1, h2⟩
      · exact hno A hA ⟨(hℬ C hC).1 h1, (hℬ C hC).1 h2⟩
    · obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := hcross p hp
      have hpS : p ∈ S ×ˢ S := mem_product.2 ⟨hAS ((hℬ B hB).1 h1), hAS ((hℬ B' hB').1 h2)⟩
      have hne : p.1 ≠ p.2 := fun e => disjoint_left.1 (hℬd B hB B' hB' hBB') h1 (e ▸ h2)
      refine mem_filter.2 ⟨hpS, hne, fun C hC ⟨c1, c2⟩ => ?_⟩
      rcases mem_union.1 hC with hC | hC
      · exact disjoint_left.1 (ref_notmem hL hA hℬ hB hC) h1 c1
      · have e1 : C = B := by
          by_contra hc; exact disjoint_left.1 (hℬd C hC B hB hc) c1 h1
        have e2 : C = B' := by
          by_contra hc; exact disjoint_left.1 (hℬd C hC B' hB' hc) c2 h2
        exact hBB' (e1.symm.trans e2)

/-- **(L3) is preserved under refinement** (the semisparse bookkeeping of Theorem 5.1). -/
lemma ref_L3 {x : ℝ} (hx : 0 ≤ x) (hL : IsLayout G S ℱ 𝒥) (hA : A ∈ ℱ)
    (hℬ : ∀ B ∈ ℬ, B ⊆ A ∧ B.Nonempty) (hℬd : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Disjoint B B')
    (hsemi : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Complete G B B' ∨ WeaklySparse G x B B')
    (h3 : ((wrong G S ℱ 𝒥).card : ℝ) ≤ x * (decided S ℱ).card) :
    ((wrong G S (refF ℱ A ℬ) (refJ G ℱ 𝒥 A ℬ)).card : ℝ) ≤ x * (decided S (refF ℱ A ℬ)).card := by
  have h1 : ((wrong G S (refF ℱ A ℬ) (refJ G ℱ 𝒥 A ℬ)).card : ℝ) ≤
      (wrong G S ℱ 𝒥).card + (wrongR G ℬ).card := by
    have := (card_le_card (ref_wrong_subset hL hA hℬ)).trans (card_union_le _ _)
    exact_mod_cast this
  have h2 := card_wrongR hx hℬd hsemi
  obtain ⟨hd, hsub⟩ := ref_decided hL hA hℬ hℬd
  have h4 : ((decided S ℱ).card : ℝ) + (crossPairs ℬ).card ≤ (decided S (refF ℱ A ℬ)).card := by
    have := card_le_card hsub
    rw [card_union_of_disjoint hd] at this
    exact_mod_cast this
  nlinarith

end refine2

section main
variable {S : Finset V}

/-- the potential `Σ |A|^{1/d}` -/
noncomputable def pot (d : ℕ) (ℱ : Finset (Finset V)) : ℝ := ∑ A ∈ ℱ, ((A.card : ℝ) ^ ((d : ℝ)⁻¹))

omit [Fintype V] in
lemma pow_rpow_inv {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : d ≠ 0) : (a ^ ((d : ℝ)⁻¹)) ^ d = a :=
  Real.rpow_inv_natCast_pow ha hd

omit [Fintype V] in
/-- a family with potential at least `|S|^{1/d}` has a member of size at least `|S|/|ℱ|^d` -/
lemma big_block {d : ℕ} (hd : d ≠ 0) {ℱ : Finset (Finset V)} (hne : ℱ.Nonempty) {A : Finset V}
    (hA : A ∈ ℱ) (hmax : ∀ B ∈ ℱ, B.card ≤ A.card) {n : ℝ} (hn : 0 ≤ n)
    (hpot : n ^ ((d : ℝ)⁻¹) ≤ pot d ℱ) : n ≤ (ℱ.card : ℝ) ^ d * A.card := by
  have h1 : pot d ℱ ≤ ℱ.card * (A.card : ℝ) ^ ((d : ℝ)⁻¹) := by
    unfold pot
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun B hB => Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast hmax B hB) (by positivity)
  have h2 : n ^ ((d : ℝ)⁻¹) ≤ ℱ.card * (A.card : ℝ) ^ ((d : ℝ)⁻¹) := hpot.trans h1
  have h3 := pow_le_pow_left₀ (by positivity) h2 d
  rw [pow_rpow_inv hn hd, mul_pow, pow_rpow_inv (Nat.cast_nonneg _) hd] at h3
  exact h3

variable (G) in
/-- the layout conditions (L1)–(L3) -/
def GoodLayout (S : Finset V) (ε x : ℝ) (d : ℕ) (ℱ : Finset (Finset V))
    (𝒥 : Finset (Finset V × Finset V)) : Prop :=
  IsLayout G S ℱ 𝒥 ∧ (∀ A ∈ ℱ, ε ^ (2 * d) * S.card ≤ A.card) ∧
  (S.card : ℝ) ^ ((d : ℝ)⁻¹) ≤ pot d ℱ ∧ ((wrong G S ℱ 𝒥).card : ℝ) ≤ x * (decided S ℱ).card

omit [Fintype V] in
lemma edges_le_wrong {ℱ : Finset (Finset V)} {𝒥 : Finset (Finset V × Finset V)}
    (hL : IsLayout G S ℱ 𝒥) {A B : Finset V} (hA : A ∈ ℱ) (hB : B ∈ ℱ) (hne : A ≠ B)
    (hJ : (A, B) ∉ 𝒥) : edgesBetween G A B ≤ (wrong G S ℱ 𝒥).card := by
  unfold edgesBetween
  apply card_le_card
  intro p hp
  obtain ⟨hp, hadj⟩ := mem_filter.1 hp
  obtain ⟨h1, h2⟩ := mem_product.1 hp
  exact mem_filter.2 ⟨mem_product.2 ⟨(hL.1 A hA).1 h1, (hL.1 B hB).1 h2⟩, hadj, A, hA, B, hB, hne,
    h1, h2, hJ⟩

lemma decided_card_le (ℱ : Finset (Finset V)) :
    ((decided S ℱ).card : ℝ) ≤ (S.card : ℝ) * S.card := by
  have : (decided S ℱ).card ≤ S.card * S.card := by
    have := card_le_card (filter_subset (fun p : V × V => p.1 ≠ p.2 ∧ ∀ A ∈ ℱ, ¬ (p.1 ∈ A ∧ p.2 ∈ A))
      (S ×ˢ S))
    rwa [card_product] at this
  exact_mod_cast this

/-- **Claim 1** of Theorem 5.1: two blocks of a good layout are complete or weakly `ε^d`-sparse. -/
lemma claim1 {ε x : ℝ} {d : ℕ} (hε0 : 0 < ε) (hx : x = ε ^ (5 * d)) {ℱ : Finset (Finset V)}
    {𝒥 : Finset (Finset V × Finset V)} (hG : GoodLayout G S ε x d ℱ 𝒥)
    {A B : Finset V} (hA : A ∈ ℱ) (hB : B ∈ ℱ) (hne : A ≠ B) :
    Complete G A B ∨ WeaklySparse G (ε ^ d) A B := by
  by_cases hJ : (A, B) ∈ 𝒥
  · exact Or.inl (hG.1.2.2.1 _ hJ).2.2.2
  · right
    unfold WeaklySparse
    have h1 : (edgesBetween G A B : ℝ) ≤ (wrong G S ℱ 𝒥).card := by
      exact_mod_cast edges_le_wrong hG.1 hA hB hne hJ
    have h2 := hG.2.2.2
    have h3 := decided_card_le (S := S) ℱ
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    have h4 := mul_le_mul_of_nonneg_left h3 hx0
    have h5 := mul_le_mul (hG.2.1 A hA) (hG.2.1 B hB) (by positivity) (by positivity)
    have h6 := mul_le_mul_of_nonneg_left h5 (le_of_lt (pow_pos hε0 d))
    have e : x * ((S.card : ℝ) * S.card) =
        ε ^ d * ((ε ^ (2 * d) * S.card) * (ε ^ (2 * d) * S.card)) := by rw [hx]; ring
    have e2 : ε ^ d * ((A.card : ℝ) * B.card) = ε ^ d * A.card * B.card := by ring
    linarith

omit [Fintype V] in
lemma width_num {ε x k s a : ℝ} {d : ℕ} (hx0 : 0 ≤ x) (hxε : x ≤ ε) (hk0 : 0 < k) (hkx : k * x ≤ 1)
    (hs : 0 ≤ s) (hA : ε ^ d * s ≤ a) : x ^ (2 * d) * s ≤ a / k ^ d := by
  rw [le_div_iff₀ (pow_pos hk0 d)]
  have h1 : (k * x) ^ d ≤ 1 := pow_le_one₀ (by positivity) hkx
  have h2 : x ^ d ≤ ε ^ d := pow_le_pow_left₀ hx0 hxε d
  have e : x ^ (2 * d) * s * k ^ d = (x ^ d * s) * (k * x) ^ d := by ring
  rw [e]
  have h3 : x ^ d * s ≤ ε ^ d * s := mul_le_mul_of_nonneg_right h2 hs
  calc (x ^ d * s) * (k * x) ^ d ≤ (x ^ d * s) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ a := by linarith

omit [Fintype V] in
lemma l2_num {k a m : ℝ} {d : ℕ} (hd : d ≠ 0) (hk0 : 0 < k) (ha : 0 ≤ a) (hm : k ≤ m) :
    a ^ ((d : ℝ)⁻¹) ≤ m * (a / k ^ d) ^ ((d : ℝ)⁻¹) := by
  rw [Real.div_rpow ha (by positivity), Real.pow_rpow_inv_natCast hk0.le hd]
  have h0 : 0 ≤ a ^ ((d : ℝ)⁻¹) := Real.rpow_nonneg ha _
  rw [mul_div_assoc', le_div_iff₀ hk0]
  nlinarith

/-- **Claim 2** of Theorem 5.1 (refinement step): if the largest block has an `x`-semisparse blockade
of length `k ≤ 1/ε`, the layout refines to a good layout with more blocks. -/
lemma good_refine {ε x : ℝ} {d : ℕ} (hd : d ≠ 0) (hε0 : 0 < ε) (hx0 : 0 ≤ x)
    {ℱ : Finset (Finset V)} {𝒥 : Finset (Finset V × Finset V)} (hG : GoodLayout G S ε x d ℱ 𝒥)
    {A : Finset V} (hA : A ∈ ℱ) (hAbig : ε ^ d * S.card ≤ A.card) {k : ℝ} (hk2 : 2 ≤ k)
    (hkε : k * ε ≤ 1) (β : Blockade A k (A.card / k ^ d)) (hβ : β.IsSemisparse G x) :
    ∃ ℱ' 𝒥', GoodLayout G S ε x d ℱ' 𝒥' ∧ ℱ.card < ℱ'.card := by
  obtain ⟨hL, hL1, hL2, hL3⟩ := hG
  have hAne := (hL.1 A hA).2
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  have hk0 : 0 < k := by linarith
  have hw : 0 < (A.card : ℝ) / k ^ d := by positivity
  have hBne : ∀ i, (β.B i).Nonempty := fun i => by
    have h := β.wid i
    have : 0 < (β.B i).card := by exact_mod_cast hw.trans_le h
    exact card_pos.1 this
  have hinj : Function.Injective β.B := by
    intro i j hij
    by_contra hne
    obtain ⟨v, hv⟩ := hBne i
    exact disjoint_left.1 (β.disj i j hne) hv (hij ▸ hv)
  obtain ⟨ℬ, hℬdef⟩ : ∃ ℬ : Finset (Finset V), ℬ = univ.image β.B := ⟨_, rfl⟩
  have hcardℬ : ℬ.card = β.m := by
    rw [hℬdef, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hmem : ∀ B ∈ ℬ, ∃ i, β.B i = B := fun B hB => by
    rw [hℬdef] at hB
    obtain ⟨i, -, hi⟩ := mem_image.1 hB; exact ⟨i, hi⟩
  have hℬ : ∀ B ∈ ℬ, B ⊆ A ∧ B.Nonempty := fun B hB => by
    obtain ⟨i, rfl⟩ := hmem B hB; exact ⟨β.sub i, hBne i⟩
  have hℬd : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Disjoint B B' := fun B hB B' hB' hne => by
    obtain ⟨i, rfl⟩ := hmem B hB; obtain ⟨j, rfl⟩ := hmem B' hB'
    exact β.disj i j (fun h => hne (h ▸ rfl))
  have hsemi : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Complete G B B' ∨ WeaklySparse G x B B' :=
    fun B hB B' hB' hne => by
    obtain ⟨i, rfl⟩ := hmem B hB; obtain ⟨j, rfl⟩ := hmem B' hB'
    exact hβ i j (fun h => hne (h ▸ rfl))
  have hdisjF : Disjoint (ℱ.erase A) ℬ := by
    rw [disjoint_left]; intro C hC hCℬ
    exact ref_ne hL hA hℬ hCℬ hC rfl
  have hm2 : 2 ≤ β.m := by
    have : (2 : ℝ) ≤ β.m := hk2.trans β.len
    exact_mod_cast this
  refine ⟨refF ℱ A ℬ, refJ G ℱ 𝒥 A ℬ,
    ⟨ref_isLayout hL hA hℬ hℬd, ?_, ?_, ref_L3 hx0 hL hA hℬ hℬd hsemi hL3⟩, ?_⟩
  · -- (L1)
    intro B hB
    rcases mem_union.1 hB with hB | hB
    · exact hL1 B (mem_erase.1 hB).2
    · obtain ⟨i, rfl⟩ := hmem B hB
      exact (width_num hε0.le le_rfl hk0 hkε (Nat.cast_nonneg _) hAbig).trans (β.wid i)
  · -- (L2)
    unfold pot refF
    rw [sum_union hdisjF]
    have hsplit : (A.card : ℝ) ^ ((d : ℝ)⁻¹) + ∑ B ∈ ℱ.erase A, ((B.card : ℝ) ^ ((d : ℝ)⁻¹)) =
        ∑ B ∈ ℱ, ((B.card : ℝ) ^ ((d : ℝ)⁻¹)) :=
      add_sum_erase ℱ (fun B : Finset V => (B.card : ℝ) ^ ((d : ℝ)⁻¹)) hA
    have hℬpot : (A.card : ℝ) ^ ((d : ℝ)⁻¹) ≤ ∑ B ∈ ℬ, ((B.card : ℝ) ^ ((d : ℝ)⁻¹)) := by
      calc (A.card : ℝ) ^ ((d : ℝ)⁻¹) ≤ ℬ.card * ((A.card : ℝ) / k ^ d) ^ ((d : ℝ)⁻¹) :=
            l2_num hd hk0 hApos.le (by rw [hcardℬ]; exact β.len)
        _ = ∑ B ∈ ℬ, ((A.card : ℝ) / k ^ d) ^ ((d : ℝ)⁻¹) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ B ∈ ℬ, ((B.card : ℝ) ^ ((d : ℝ)⁻¹)) := sum_le_sum fun B hB => by
            obtain ⟨i, rfl⟩ := hmem B hB
            exact Real.rpow_le_rpow hw.le (β.wid i) (by positivity)
    unfold pot at hL2
    linarith
  · -- more blocks
    unfold refF
    rw [card_union_of_disjoint hdisjF, hcardℬ]
    have := card_erase_add_one hA
    omega

/-- **Theorem 5.1** (the layout theorem, semisparse form; NSS VII Theorem 6.1 with semisparse
blockades): with `x = ε^{5d}`, if every `F ⊆ S` with `|F| ≥ ε^d|S|` has an `x`-semisparse
`(k, |F|/k^d)`-blockade for some `k ∈ [2, 1/x]`, then `S` has an `(ε^{-1}, x^{2d}|S|)`-blockade in
which every two blocks are complete or weakly `ε^d`-sparse. -/
theorem layout_theorem {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {d : ℕ} (hd : d ≠ 0) (S : Finset V)
    (hyp : ∀ F ⊆ S, ε ^ d * S.card ≤ F.card → ∃ k : ℝ, 2 ≤ k ∧ k * ε ^ (5 * d) ≤ 1 ∧
      ∃ β : Blockade F k (F.card / k ^ d), β.IsSemisparse G (ε ^ (5 * d))) :
    ∃ β : Blockade S (1 / ε) ((ε ^ (5 * d)) ^ (2 * d) * S.card), β.IsSemisparse G (ε ^ d) := by
  have hx0 : 0 < ε ^ (5 * d) := pow_pos hε0 _
  have hxε : ε ^ (5 * d) ≤ ε ^ d := pow_le_pow_of_le_one hε0.le hε1.le (by omega)
  have hxε1 : ε ^ (5 * d) ≤ ε := hxε.trans (pow_le_of_le_one hε0.le hε1.le hd)
  generalize hxdef : ε ^ (5 * d) = x at hyp hx0 hxε hxε1 ⊢
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · refine ⟨⟨⌈1 / ε⌉₊, fun _ => ∅, Nat.le_ceil _, fun _ => empty_subset _, fun _ => by simp,
      fun _ _ _ => disjoint_empty_left _⟩, fun i j _ => Or.inl (fun a ha => absurd ha (notMem_empty a))⟩
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  obtain ⟨𝒞, h𝒞⟩ : ∃ 𝒞 : Finset (Finset (Finset V) × Finset (Finset V × Finset V)),
      𝒞 = ((S.powerset.powerset) ×ˢ ((S.powerset ×ˢ S.powerset).powerset)).filter
        (fun p => GoodLayout G S ε x d p.1 p.2) := ⟨_, rfl⟩
  have hin : ∀ ℱ 𝒥, GoodLayout G S ε x d ℱ 𝒥 → (ℱ, 𝒥) ∈ 𝒞 := by
    intro ℱ 𝒥 h
    rw [h𝒞]
    refine mem_filter.2 ⟨mem_product.2 ⟨mem_powerset.2 fun A hA => mem_powerset.2 (h.1.1 A hA).1,
      mem_powerset.2 fun p hp => mem_product.2 ⟨mem_powerset.2 (h.1.1 _ (h.1.2.2.1 p hp).1).1,
        mem_powerset.2 (h.1.1 _ (h.1.2.2.1 p hp).2.1).1⟩⟩, h⟩
  have h0 : GoodLayout G S ε x d {S} ∅ := by
    refine ⟨⟨fun A hA => ?_, fun A hA B hB hne => ?_, fun p hp => absurd hp (notMem_empty p),
      fun p hp => absurd hp (notMem_empty p)⟩, fun A hA => ?_, ?_, ?_⟩
    · rw [mem_singleton.1 hA]; exact ⟨subset_refl _, hSne⟩
    · exact absurd ((mem_singleton.1 hA).trans (mem_singleton.1 hB).symm) hne
    · rw [mem_singleton.1 hA]
      have : ε ^ (2 * d) ≤ 1 := pow_le_one₀ hε0.le hε1.le
      nlinarith
    · simp [pot]
    · have : wrong G S {S} ∅ = ∅ := by
        apply filter_eq_empty_iff.2
        rintro p - ⟨-, A, hA, B, hB, hne, -⟩
        exact hne ((mem_singleton.1 hA).trans (mem_singleton.1 hB).symm)
      rw [this, card_empty, Nat.cast_zero]; positivity
  obtain ⟨⟨ℱ, 𝒥⟩, hmem, hmax⟩ := exists_max_image 𝒞 (fun p => p.1.card) ⟨_, hin _ _ h0⟩
  have hG : GoodLayout G S ε x d ℱ 𝒥 := by rw [h𝒞] at hmem; exact (mem_filter.1 hmem).2
  by_cases hbig : 1 / ε ≤ ℱ.card
  · -- Claim 1: the blocks themselves
    have hw : ∀ A ∈ ℱ, x ^ (2 * d) * S.card ≤ (A.card : ℝ) := fun A hA => by
      have h1 : x ^ (2 * d) ≤ ε ^ (2 * d) := pow_le_pow_left₀ hx0.le hxε1 _
      exact (mul_le_mul_of_nonneg_right h1 hSpos.le).trans (hG.2.1 A hA)
    refine ⟨Blockade.ofFamily S (1 / ε) _ ℱ (fun A hA => (hG.1.1 A hA).1) hG.1.2.1 hw hbig,
      fun i j hij => ?_⟩
    exact claim1 hε0 hxdef.symm hG (Blockade.ofFamily_mem S _ _ ℱ _ _ _ _ i)
      (Blockade.ofFamily_mem S _ _ ℱ _ _ _ _ j) (Blockade.ofFamily_ne S _ _ ℱ _ _ _ _ hij)
  · push Not at hbig
    have hℱne : ℱ.Nonempty := by
      rw [nonempty_iff_ne_empty]; rintro rfl
      have h := hG.2.2.1
      rw [show pot d (∅ : Finset (Finset V)) = 0 from sum_empty] at h
      linarith [Real.rpow_pos_of_pos hSpos ((d : ℝ)⁻¹)]
    obtain ⟨A, hA, hAmax⟩ := exists_max_image ℱ card hℱne
    have hAbig : ε ^ d * S.card ≤ A.card := by
      have h1 := big_block hd hℱne hA hAmax hSpos.le hG.2.2.1
      have h2 : (ℱ.card : ℝ) ^ d ≤ (1 / ε) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hbig.le d
      have h3 : (S.card : ℝ) ≤ (1 / ε) ^ d * A.card :=
        h1.trans (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _))
      have h4 : ε ^ d * (1 / ε) ^ d = 1 := by
        rw [← mul_pow, mul_one_div_cancel hε0.ne', one_pow]
      have h5 := mul_le_mul_of_nonneg_left h3 (pow_pos hε0 d).le
      rw [← mul_assoc, h4, one_mul] at h5
      exact h5
    obtain ⟨k, hk2, hkx, β, hβ⟩ := hyp A (hG.1.1 A hA).1 hAbig
    by_cases hkε : k * ε ≤ 1
    · -- Claim 2: otherwise the layout could be refined
      obtain ⟨ℱ', 𝒥', hG', hlt⟩ := good_refine hd hε0 hx0.le hG hA hAbig hk2 hkε β hβ
      have := hmax _ (hin _ _ hG')
      simp only at this
      omega
    · push Not at hkε
      have hk1 : 1 / ε ≤ k := by rw [div_le_iff₀ hε0]; linarith
      refine ⟨β.mono (hG.1.1 A hA).1 hk1
        (width_num hx0.le hxε1 (by linarith) hkx hSpos.le hAbig), fun i j hij => ?_⟩
      exact (hβ i j hij).imp id (weaklySparse_mono hxε)

end main

end EHP6
