import EHP6.ToothFacts

/-!
# Tooth Lemma, Step 4: prefix masses along a chain

For a chain `𝒞` (totally ordered by inclusion) with weights `m N ≥ 0`, let
`P N = Σ_{N' ∈ 𝒞, N ⊆ N'} m N'` (the mass of `N` and everything above it). The members with
`P ≤ θ` carry mass in `(θ − t, θ]` when every weight is `< t` and `θ ≤ total`.
-/

namespace EHP6

open Finset Classical

variable {α : Type} [DecidableEq α]

/-- prefix mass -/
noncomputable def pmass (𝒞 : Finset (Finset α)) (m : Finset α → ℝ) (N : Finset α) : ℝ :=
  ∑ N' ∈ 𝒞.filter (fun N' => N ⊆ N'), m N'

variable {𝒞 : Finset (Finset α)} {m : Finset α → ℝ}

lemma pmass_anti (hm : ∀ N ∈ 𝒞, 0 ≤ m N) {N N' : Finset α} (h : N ⊆ N') :
    pmass 𝒞 m N' ≤ pmass 𝒞 m N := by
  unfold pmass
  apply sum_le_sum_of_subset_of_nonneg
  · intro X hX; obtain ⟨hX1, hX2⟩ := mem_filter.1 hX; exact mem_filter.2 ⟨hX1, h.trans hX2⟩
  · intro X hX _; exact hm X (mem_filter.1 hX).1

lemma prefix_upper (hchain : ∀ N ∈ 𝒞, ∀ N' ∈ 𝒞, N ⊆ N' ∨ N' ⊆ N) (hm : ∀ N ∈ 𝒞, 0 ≤ m N)
    {θ : ℝ} (hθ : 0 ≤ θ) : ∑ N ∈ 𝒞.filter (fun N => pmass 𝒞 m N ≤ θ), m N ≤ θ := by
  set U := 𝒞.filter (fun N => pmass 𝒞 m N ≤ θ)
  rcases U.eq_empty_or_nonempty with hU | hU
  · rw [hU, sum_empty]; exact hθ
  obtain ⟨N₀, hN₀U, hN₀min⟩ := U.exists_min_image card hU
  obtain ⟨hN₀C, hN₀θ⟩ := mem_filter.1 hN₀U
  have hsub : U ⊆ 𝒞.filter (fun N' => N₀ ⊆ N') := by
    intro N hN
    obtain ⟨hNC, -⟩ := mem_filter.1 hN
    refine mem_filter.2 ⟨hNC, ?_⟩
    rcases hchain N hNC N₀ hN₀C with h | h
    · rw [eq_of_subset_of_card_le h (hN₀min N hN)]
    · exact h
  calc ∑ N ∈ U, m N ≤ ∑ N ∈ 𝒞.filter (fun N' => N₀ ⊆ N'), m N :=
        sum_le_sum_of_subset_of_nonneg hsub (fun X hX _ => hm X (mem_filter.1 hX).1)
    _ = pmass 𝒞 m N₀ := rfl
    _ ≤ θ := hN₀θ

lemma prefix_lower (hchain : ∀ N ∈ 𝒞, ∀ N' ∈ 𝒞, N ⊆ N' ∨ N' ⊆ N) (hm : ∀ N ∈ 𝒞, 0 ≤ m N)
    {t θ : ℝ} (ht : 0 < t) (hmt : ∀ N ∈ 𝒞, m N < t) (hθ : θ ≤ ∑ N ∈ 𝒞, m N) :
    θ - t < ∑ N ∈ 𝒞.filter (fun N => pmass 𝒞 m N ≤ θ), m N := by
  set U := 𝒞.filter (fun N => pmass 𝒞 m N ≤ θ)
  by_cases hall : 𝒞 \ U = ∅
  · have : U = 𝒞 := by
      apply subset_antisymm (filter_subset _ _)
      intro N hN; by_contra hc
      have : N ∈ 𝒞 \ U := mem_sdiff.2 ⟨hN, hc⟩
      rw [hall] at this; exact notMem_empty _ this
    rw [this]; linarith
  obtain ⟨N₁, hN₁, hN₁max⟩ := (𝒞 \ U).exists_max_image card (nonempty_iff_ne_empty.2 hall)
  obtain ⟨hN₁C, hN₁U⟩ := mem_sdiff.1 hN₁
  have hN₁P : θ < pmass 𝒞 m N₁ := by
    by_contra hc; push Not at hc; exact hN₁U (mem_filter.2 ⟨hN₁C, hc⟩)
  -- everything strictly above N₁ is in U
  have habove : 𝒞.filter (fun N' => N₁ ⊆ N' ∧ N' ≠ N₁) ⊆ U := by
    intro N hN
    obtain ⟨hNC, hN₁N, hne⟩ := mem_filter.1 hN
    by_contra hNU
    have := hN₁max N (mem_sdiff.2 ⟨hNC, hNU⟩)
    exact hne (eq_of_subset_of_card_le hN₁N this).symm
  have hsplit : pmass 𝒞 m N₁ = m N₁ + ∑ N ∈ 𝒞.filter (fun N' => N₁ ⊆ N' ∧ N' ≠ N₁), m N := by
    unfold pmass
    have : 𝒞.filter (fun N' => N₁ ⊆ N') = insert N₁ (𝒞.filter (fun N' => N₁ ⊆ N' ∧ N' ≠ N₁)) := by
      ext X; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hX, hsub⟩
        by_cases h : X = N₁
        · exact Or.inl h
        · exact Or.inr ⟨hX, hsub, h⟩
      · rintro (rfl | ⟨hX, hsub, -⟩)
        · exact ⟨hN₁C, subset_rfl⟩
        · exact ⟨hX, hsub⟩
    rw [this, sum_insert (by simp)]
  have hle : ∑ N ∈ 𝒞.filter (fun N' => N₁ ⊆ N' ∧ N' ≠ N₁), m N ≤ ∑ N ∈ U, m N :=
    sum_le_sum_of_subset_of_nonneg habove (fun X hX _ => hm X (mem_filter.1 hX).1)
  linarith [hmt N₁ hN₁C]

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- the type of a vertex relative to the chain: complete to every member not containing it -/
def ChainTyp (G : SimpleGraph V) (𝒞 : Finset (Finset V)) (v : V) : Prop :=
  ∀ N' ∈ 𝒞, v ∉ N' → ∀ w ∈ N', G.Adj v w

lemma not_typ_anti {Y : Finset V} {s : ℝ} {𝒞 : Finset (Finset V)} (h𝒞 : 𝒞 ⊆ Lfam G Y s)
    (hchain : ∀ N ∈ 𝒞, ∀ N' ∈ 𝒞, N ⊆ N' ∨ N' ⊆ N) (hne : ∀ N ∈ 𝒞, N.Nonempty) {v : V}
    (hvY : v ∈ Y) (hv : ¬ ChainTyp G 𝒞 v) : ∀ N' ∈ 𝒞, v ∉ N' → ∀ w ∈ N', ¬ G.Adj v w := by
  unfold ChainTyp at hv
  push Not at hv
  obtain ⟨N'', hN''C, hvN'', w₀, hw₀, hvw₀⟩ := hv
  have hmod : ∀ N ∈ 𝒞, IsModule G Y N := fun N hN => (mem_Lfam.1 (h𝒞 hN)).2.1.1
  have anti'' : ∀ w ∈ N'', ¬ G.Adj v w := by
    rcases (hmod N'' hN''C).2 v (mem_sdiff.2 ⟨hvY, hvN''⟩) with h | h
    · exact absurd (h w₀ hw₀) hvw₀
    · exact h
  intro N' hN'C hvN' w hw
  rcases (hmod N' hN'C).2 v (mem_sdiff.2 ⟨hvY, hvN'⟩) with h | h
  · exfalso
    rcases hchain N' hN'C N'' hN''C with h' | h'
    · exact anti'' w (h' hw) (h w hw)
    · exact hvw₀ (h w₀ (h' hw₀))
  · exact h w hw

/-- **Step 4 (TL2).** Along a chain of members of `𝓛` with thin layers (`|S(N)| < t`) and total layer
mass at least `2Lt`, there is a pure `(L, t/2)`-blockade. -/
theorem chain_blockade {Y : Finset V} {s : ℝ} {𝒞 : Finset (Finset V)} (h𝒞 : 𝒞 ⊆ Lfam G Y s)
    (hchain : ∀ N ∈ 𝒞, ∀ N' ∈ 𝒞, N ⊆ N' ∨ N' ⊆ N) (hne : ∀ N ∈ 𝒞, N.Nonempty)
    {t : ℝ} (ht : 0 < t) (hthin : ∀ N ∈ 𝒞, ((atomPart G Y s N).card : ℝ) < t) (L : ℕ)
    (hL : 2 * L * t ≤ ∑ N ∈ 𝒞, ((atomPart G Y s N).card : ℝ)) :
    ∃ β : Blockade Y L (t / 2), β.IsPure G := by
  set m : Finset V → ℝ := fun N => ((atomPart G Y s N).card : ℝ) with hmdef
  have hm : ∀ N ∈ 𝒞, 0 ≤ m N := fun N _ => Nat.cast_nonneg _
  set P := pmass 𝒞 m with hP
  -- chunks
  let chunk : ℕ → Finset (Finset V) := fun a =>
    𝒞.filter (fun N => 2 * a * t < P N ∧ P N ≤ 2 * (a + 1) * t)
  let Γ : ℕ → Finset V := fun a => (chunk a).biUnion (atomPart G Y s)
  have Sdisj : ∀ N ∈ 𝒞, ∀ N' ∈ 𝒞, N ≠ N' → Disjoint (atomPart G Y s N) (atomPart G Y s N') := by
    intro N hN N' hN' hNN'
    rw [disjoint_left]; intro v hv hv'
    exact hNN' (atomPart_unique (h𝒞 hN) (h𝒞 hN') hv hv')
  have Γcard : ∀ a, ((Γ a).card : ℝ) = ∑ N ∈ chunk a, m N := by
    intro a
    have hpd : ((chunk a : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint (atomPart G Y s) :=
      fun N hN N' hN' hne' => Sdisj N (mem_filter.1 hN).1 N' (mem_filter.1 hN').1 hne'
    simp only [Γ]; rw [card_biUnion hpd]; push_cast; rfl
  have Γbig : ∀ a : ℕ, a < L → t < ((Γ a).card : ℝ) := by
    intro a ha
    have htot := hL
    have ha' : ((a : ℝ) + 1) ≤ L := by exact_mod_cast ha
    have hθ₂ : 2 * ((a : ℝ) + 1) * t ≤ ∑ N ∈ 𝒞, m N := by nlinarith
    have hlow := prefix_lower hchain hm ht hthin hθ₂
    have hup := prefix_upper (𝒞 := 𝒞) (m := m) hchain hm (θ := 2 * a * t) (by positivity)
    have hsplit : 𝒞.filter (fun N => P N ≤ 2 * ((a : ℝ) + 1) * t) =
        𝒞.filter (fun N => P N ≤ 2 * a * t) ∪ chunk a := by
      ext N; simp only [mem_filter, mem_union, chunk]
      constructor
      · rintro ⟨hN, h⟩
        by_cases h' : P N ≤ 2 * a * t
        · exact Or.inl ⟨hN, h'⟩
        · exact Or.inr ⟨hN, not_le.1 h', h⟩
      · rintro (⟨hN, h⟩ | ⟨hN, -, h⟩)
        · exact ⟨hN, h.trans (by nlinarith)⟩
        · exact ⟨hN, h⟩
    have hdisj : Disjoint (𝒞.filter (fun N => P N ≤ 2 * a * t)) (chunk a) := by
      rw [disjoint_left]; intro N h1 h2
      exact absurd (mem_filter.1 h1).2 (not_le.2 (mem_filter.1 h2).2.1)
    rw [Γcard a]
    rw [hsplit, sum_union hdisj] at hlow
    linarith
  -- chunk members are ordered: a < b ⇒ members of chunk b lie strictly inside members of chunk a
  have order : ∀ a b : ℕ, a < b → ∀ N ∈ chunk a, ∀ N' ∈ chunk b, N' ⊆ N ∧ N' ≠ N := by
    intro a b hab N hN N' hN'
    obtain ⟨hNC, -, hNP⟩ := mem_filter.1 hN
    obtain ⟨hN'C, hN'P, -⟩ := mem_filter.1 hN'
    have hab' : ((a : ℝ) + 1) ≤ b := by exact_mod_cast hab
    have hlt : P N < P N' := by nlinarith
    rcases hchain N hNC N' hN'C with h | h
    · exact absurd (pmass_anti hm h) (not_le.2 hlt)
    · exact ⟨h, fun e => by rw [e] at hlt; exact lt_irrefl _ hlt⟩
  have cross : ∀ a b : ℕ, a < b → ∀ v ∈ Γ a, ∀ w ∈ Γ b,
      (ChainTyp G 𝒞 v → G.Adj v w) ∧ (¬ ChainTyp G 𝒞 v → ¬ G.Adj v w) := by
    intro a b hab v hv w hw
    obtain ⟨N, hN, hvN⟩ := mem_biUnion.1 hv
    obtain ⟨N', hN', hwN'⟩ := mem_biUnion.1 hw
    obtain ⟨hN'N, hne'⟩ := order a b hab N hN N' hN'
    have hNC := (mem_filter.1 hN).1
    have hN'C := (mem_filter.1 hN').1
    have hvN' : v ∉ N' := fun h => disjoint_left.1
      (atomPart_disjoint (h𝒞 hNC) (h𝒞 hN'C) (Finset.ssubset_iff_subset_ne.2 ⟨hN'N, hne'⟩)) hvN h
    have hvY : v ∈ Y := (mem_Lfam.1 (h𝒞 hNC)).1 (atomPart_subset hvN)
    have hwN'' : w ∈ N' := atomPart_subset hwN'
    exact ⟨fun h => h N' hN'C hvN' w hwN'',
      fun h => not_typ_anti h𝒞 hchain hne hvY h N' hN'C hvN' w hwN''⟩
  -- majority type
  let Γ' : ℕ → Finset V := fun a =>
    if ((Γ a).card : ℝ) / 2 ≤ (((Γ a).filter (ChainTyp G 𝒞)).card : ℝ)
    then (Γ a).filter (ChainTyp G 𝒞) else (Γ a).filter (fun v => ¬ ChainTyp G 𝒞 v)
  have Γ'sub : ∀ a, Γ' a ⊆ Γ a := by
    intro a; simp only [Γ']; split_ifs <;> exact filter_subset _ _
  have Γ'big : ∀ a, ((Γ a).card : ℝ) / 2 ≤ ((Γ' a).card : ℝ) := by
    intro a; simp only [Γ']
    split_ifs with h
    · exact h
    · have := card_filter_add_card_filter_not (s := Γ a) (ChainTyp G 𝒞)
      have h' : (((Γ a).filter (ChainTyp G 𝒞)).card : ℝ) +
          (((Γ a).filter (fun v => ¬ ChainTyp G 𝒞 v)).card : ℝ) = (Γ a).card := by
        exact_mod_cast this
      push Not at h; linarith
  have Γ'typ : ∀ a, (∀ v ∈ Γ' a, ChainTyp G 𝒞 v) ∨ (∀ v ∈ Γ' a, ¬ ChainTyp G 𝒞 v) := by
    intro a; simp only [Γ']
    split_ifs
    · exact Or.inl fun v hv => (mem_filter.1 hv).2
    · exact Or.inr fun v hv => (mem_filter.1 hv).2
  have pure_lt : ∀ a b : ℕ, a < b → Complete G (Γ' a) (Γ' b) ∨ Anticomplete G (Γ' a) (Γ' b) := by
    intro a b hab
    rcases Γ'typ a with h | h
    · exact Or.inl fun v hv w hw => (cross a b hab v (Γ'sub a hv) w (Γ'sub b hw)).1 (h v hv)
    · exact Or.inr fun v hv w hw => (cross a b hab v (Γ'sub a hv) w (Γ'sub b hw)).2 (h v hv)
  have hsub : ∀ i : Fin L, Γ' i.val ⊆ Y := fun i => (Γ'sub i.val).trans (biUnion_subset.2 fun N hN =>
      atomPart_subset.trans (mem_Lfam.1 (h𝒞 (mem_filter.1 hN).1)).1)
  have hwid : ∀ i : Fin L, t / 2 ≤ ((Γ' i.val).card : ℝ) := by
    intro i
    have h1 := Γbig i.val i.isLt
    have h2 := Γ'big i.val
    linarith
  have hdj : ∀ i j : Fin L, i ≠ j → Disjoint (Γ' i.val) (Γ' j.val) := by
    intro i j hij
    apply disjoint_of_subset_left (Γ'sub i.val)
    apply disjoint_of_subset_right (Γ'sub j.val)
    rw [disjoint_left]; intro v hv hv'
    obtain ⟨N, hN, hvN⟩ := mem_biUnion.1 hv
    obtain ⟨N', hN', hvN'⟩ := mem_biUnion.1 hv'
    have := atomPart_unique (h𝒞 (mem_filter.1 hN).1) (h𝒞 (mem_filter.1 hN').1) hvN hvN'
    subst this
    have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    rcases lt_or_gt_of_ne hij' with h | h
    · exact (order _ _ h N hN N hN').2 rfl
    · exact (order _ _ h N hN' N hN).2 rfl
  refine ⟨⟨L, fun i => Γ' i.val, le_rfl, hsub, hwid, hdj⟩, fun i j hij => ?_⟩
  have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
  rcases lt_or_gt_of_ne hij' with h | h
  · exact pure_lt _ _ h
  · rcases pure_lt _ _ h with h' | h'
    · exact Or.inl fun a ha b hb => G.adj_symm (h' b hb a ha)
    · exact Or.inr fun a ha b hb hab => h' b hb a ha (G.adj_symm hab)

end EHP6
