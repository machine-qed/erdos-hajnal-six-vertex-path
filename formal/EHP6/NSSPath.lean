import EHP6.Imported

/-!
# NSS V statement 3.1 (paper: Imported Theorem II), proved

Nguyen, Scott and Seymour, *Induced subgraph density. V*, statement 3.1: let `P` be a path with
`k` vertices and `0 < y ≤ 1/(60k)`; if `G` is `y²`-sparse, then `G` contains an induced copy of `P`
or an anticomplete `(1/y, ⌊y²|G|⌋)`-blockade.

The proof follows theirs. Instead of removing poorly expanding sets one at a time, we take a
maximal admissible family of them (`Admissible`), which has the same two properties as the result
of the removal process. If the removed part is large, its pieces are grouped into the blocks of
the blockade (`exists_groups`). Otherwise the remaining vertex set `T` expands well, and a chain of
sets `S₀, S₁, …, S_{k-1}` gives an induced path (`exists_chain`, `exists_path`).
-/

namespace EHP6

open Finset

section

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- the vertices of `T \ X` with a neighbour in `X` -/
def nbhd (T X : Finset V) : Finset V := (T \ X).filter (fun u => ∃ a ∈ X, G.Adj a u)

omit [Fintype V] in
lemma mem_nbhd {T X : Finset V} {u : V} :
    u ∈ nbhd G T X ↔ u ∈ T ∧ u ∉ X ∧ ∃ a ∈ X, G.Adj a u := by
  simp [nbhd, and_assoc]

omit [Fintype V] in
lemma nbhd_empty (T : Finset V) : nbhd G T ∅ = ∅ := by
  ext u; simp [mem_nbhd]

/-! ### Grouping small pieces into blocks -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- Pieces of size at most `s` with total size at least `2ks` can be grouped into `k` disjoint
subfamilies, each of total size at least `s`. -/
lemma exists_groups {s : ℝ} (hs : 0 < s) : ∀ (k : ℕ) (𝒜 : Finset (Finset V)),
    (∀ P ∈ 𝒜, (P.card : ℝ) ≤ s) → 2 * k * s ≤ ∑ P ∈ 𝒜, (P.card : ℝ) →
    ∃ 𝔊 : Finset (Finset (Finset V)), k ≤ 𝔊.card ∧ (∀ ℱ ∈ 𝔊, ℱ ⊆ 𝒜) ∧
      (∀ ℱ ∈ 𝔊, s ≤ ∑ P ∈ ℱ, (P.card : ℝ)) ∧
      (∀ ℱ ∈ 𝔊, ∀ ℱ' ∈ 𝔊, ℱ ≠ ℱ' → Disjoint ℱ ℱ') := by
  intro k
  induction k with
  | zero =>
    intro 𝒜 _ _
    exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    intro 𝒜 hsmall htot
    classical
    -- a minimal subfamily of total size at least `s`
    have hne : (𝒜.powerset.filter (fun ℱ => s ≤ ∑ P ∈ ℱ, (P.card : ℝ))).Nonempty := by
      refine ⟨𝒜, mem_filter.2 ⟨mem_powerset_self _, ?_⟩⟩
      have : s ≤ 2 * ((k + 1 : ℕ) : ℝ) * s := by
        have : (1 : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by push_cast; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
        nlinarith
      linarith
    obtain ⟨ℱ, hℱmem, hℱmin⟩ := exists_min_image _ card hne
    obtain ⟨hℱsub, hℱs⟩ := mem_filter.1 hℱmem
    rw [mem_powerset] at hℱsub
    have hℱne : ℱ.Nonempty := by
      rw [nonempty_iff_ne_empty]; rintro rfl; simp at hℱs; linarith
    obtain ⟨P, hP⟩ := hℱne
    have hlt : ∑ Q ∈ ℱ.erase P, (Q.card : ℝ) < s := by
      by_contra hc; push Not at hc
      have := hℱmin (ℱ.erase P) (mem_filter.2 ⟨mem_powerset.2 ((erase_subset _ _).trans hℱsub), hc⟩)
      have := card_erase_lt_of_mem hP
      omega
    have hℱ2 : ∑ Q ∈ ℱ, (Q.card : ℝ) ≤ 2 * s := by
      rw [← add_sum_erase _ _ hP]
      linarith [hsmall P (hℱsub hP)]
    -- recurse on the remaining pieces
    have hrest : 2 * k * s ≤ ∑ Q ∈ 𝒜 \ ℱ, (Q.card : ℝ) := by
      rw [sum_sdiff_eq_sub hℱsub]
      push_cast at htot
      linarith
    obtain ⟨𝔊, hk, hsub, hsum, hdisj⟩ :=
      ih (𝒜 \ ℱ) (fun Q hQ => hsmall Q (mem_sdiff.1 hQ).1) hrest
    have hℱnot : ℱ ∉ 𝔊 := by
      intro h
      have := hsub ℱ h hP
      exact (mem_sdiff.1 this).2 hP
    refine ⟨insert ℱ 𝔊, ?_, ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem hℱnot]; omega
    · intro ℱ' h
      rcases mem_insert.1 h with rfl | h
      · exact hℱsub
      · exact (hsub ℱ' h).trans sdiff_subset
    · intro ℱ' h
      rcases mem_insert.1 h with rfl | h
      · exact hℱs
      · exact hsum ℱ' h
    · have key : ∀ ℱ' ∈ 𝔊, Disjoint ℱ ℱ' := fun ℱ' h =>
        disjoint_left.2 fun Q hQ hQ' => (mem_sdiff.1 (hsub ℱ' h hQ')).2 hQ
      intro ℱ₁ h₁ ℱ₂ h₂ hne
      rcases mem_insert.1 h₁ with e₁ | h₁'
      · rcases mem_insert.1 h₂ with e₂ | h₂'
        · exact absurd (e₁.trans e₂.symm) hne
        · rw [e₁]; exact key _ h₂'
      · rcases mem_insert.1 h₂ with e₂ | h₂'
        · rw [e₂]; exact (key _ h₁').symm
        · exact hdisj _ h₁' _ h₂' hne

/-! ### A maximal family of poorly expanding pieces -/

/-- Admissible families: nonempty pieces of `S` of size at most `s`, pairwise disjoint and
anticomplete, whose union `A` has at most `μ|A|` neighbours in `S \ A`. A maximal one plays the
role of the removal process of NSS V. -/
def Admissible (S : Finset V) (s μ : ℝ) (𝒜 : Finset (Finset V)) : Prop :=
  (∀ P ∈ 𝒜, P ⊆ S ∧ P.Nonempty ∧ (P.card : ℝ) ≤ s) ∧
  (∀ P ∈ 𝒜, ∀ Q ∈ 𝒜, P ≠ Q → Disjoint P Q ∧ Anticomplete G P Q) ∧
  ((nbhd G S (𝒜.biUnion id)).card : ℝ) ≤ μ * (𝒜.biUnion id).card

omit [Fintype V] in
/-- There is an admissible family after whose removal (together with its neighbourhood) every
nonempty set of at most `s` vertices expands by a factor larger than `μ`. -/
lemma exists_maximal_admissible (S : Finset V) (s μ : ℝ) :
    ∃ 𝒜, Admissible G S s μ 𝒜 ∧
      ∀ X ⊆ S \ (𝒜.biUnion id ∪ nbhd G S (𝒜.biUnion id)), X.Nonempty → (X.card : ℝ) ≤ s →
        μ * X.card < ((nbhd G (S \ (𝒜.biUnion id ∪ nbhd G S (𝒜.biUnion id))) X).card : ℝ) := by
  classical
  have hne : (S.powerset.powerset.filter (Admissible G S s μ)).Nonempty := by
    refine ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, ?_, ?_, ?_⟩⟩
    · simp
    · simp
    · simp [nbhd_empty]
  obtain ⟨𝒜, h𝒜mem, h𝒜max⟩ := exists_max_image _ (fun 𝒜 : Finset (Finset V) => (𝒜.biUnion id).card) hne
  have h𝒜 := (mem_filter.1 h𝒜mem).2
  refine ⟨𝒜, h𝒜, ?_⟩
  set A := 𝒜.biUnion id with hA
  set N := nbhd G S A with hN
  set T := S \ (A ∪ N) with hT
  intro X hXT hXne hXs
  by_contra hc; push Not at hc
  have hXA : Disjoint X A := disjoint_left.2 fun x hx hxA =>
    (mem_sdiff.1 (hXT hx)).2 (mem_union_left _ hxA)
  have hXnot : X ∉ 𝒜 := by
    intro h
    obtain ⟨x, hx⟩ := hXne
    exact disjoint_left.1 hXA hx (mem_biUnion.2 ⟨X, h, hx⟩)
  -- `X` is anticomplete to `A`
  have hanti : ∀ x ∈ X, ∀ a ∈ A, ¬ G.Adj a x := by
    intro x hx a ha hadj
    have hxS : x ∈ S := (mem_sdiff.1 (hXT hx)).1
    have hxA : x ∉ A := disjoint_left.1 hXA hx
    have : x ∈ N := (mem_nbhd G).2 ⟨hxS, hxA, a, ha, hadj⟩
    exact (mem_sdiff.1 (hXT hx)).2 (mem_union_right _ this)
  have hunion : (insert X 𝒜).biUnion id = X ∪ A := by
    rw [biUnion_insert]; rfl
  have hadm : Admissible G S s μ (insert X 𝒜) := by
    refine ⟨?_, ?_, ?_⟩
    · intro P hP
      rcases mem_insert.1 hP with rfl | hP
      · exact ⟨hXT.trans sdiff_subset, hXne, hXs⟩
      · exact h𝒜.1 P hP
    · intro P hP Q hQ hPQ
      have hPA : ∀ P ∈ 𝒜, P ⊆ A := fun P hP x hx => mem_biUnion.2 ⟨P, hP, hx⟩
      rcases mem_insert.1 hP with eP | hP'
      · rcases mem_insert.1 hQ with eQ | hQ'
        · exact absurd (eP.trans eQ.symm) hPQ
        · rw [eP]
          exact ⟨disjoint_of_subset_right (hPA Q hQ') hXA,
            fun x hx q hq h => hanti x hx q (hPA Q hQ' hq) (G.adj_symm h)⟩
      · rcases mem_insert.1 hQ with eQ | hQ'
        · rw [eQ]
          exact ⟨disjoint_of_subset_left (hPA P hP') hXA.symm,
            fun p hp x hx h => hanti x hx p (hPA P hP' hp) h⟩
        · exact h𝒜.2.1 P hP' Q hQ' hPQ
    · rw [hunion]
      have hsub : nbhd G S (X ∪ A) ⊆ N ∪ nbhd G T X := by
        intro u hu
        obtain ⟨huS, huXA, a, ha, hadj⟩ := (mem_nbhd G).1 hu
        by_cases huN : u ∈ N
        · exact mem_union_left _ huN
        · apply mem_union_right
          have huA : u ∉ A := fun h => huXA (mem_union_right _ h)
          have huT : u ∈ T := mem_sdiff.2 ⟨huS, fun h => (mem_union.1 h).elim huA huN⟩
          rcases mem_union.1 ha with haX | haA
          · exact (mem_nbhd G).2 ⟨huT, fun h => huXA (mem_union_left _ h), a, haX, hadj⟩
          · exact absurd ((mem_nbhd G).2 ⟨huS, huA, a, haA, hadj⟩) huN
      have h1 : ((nbhd G S (X ∪ A)).card : ℝ) ≤ N.card + (nbhd G T X).card := by
        have := (card_le_card hsub).trans (card_union_le _ _); exact_mod_cast this
      have h2 : ((X ∪ A).card : ℝ) = X.card + A.card := by
        rw [card_union_of_disjoint hXA]; push_cast; ring
      rw [h2]
      linarith [h𝒜.2.2]
  have := h𝒜max (insert X 𝒜) (mem_filter.2 ⟨?_, hadm⟩)
  · rw [hunion, card_union_of_disjoint hXA] at this
    have : 0 < X.card := card_pos.2 hXne
    omega
  · rw [mem_powerset]; intro P hP; rw [mem_powerset]; exact (hadm.1 P hP).1

/-! ### The expanding case: a chain of neighbourhoods and an induced path -/

/-- Layers `S₀, …, S_t` inside `T`, with `R_j ⊆ S_{j-1}` the private roots of `S_j` (properties
used for the induced path). -/
def ChainProps (T : Finset V) (s : ℝ) (w t : ℕ) (Sq R : ℕ → Finset V) : Prop :=
  (∀ j ≤ t, Sq j ⊆ T) ∧
  (∀ i ≤ t, ∀ j ≤ t, i ≠ j → Disjoint (Sq i) (Sq j)) ∧
  (∀ j ≤ t, ((Sq j).card : ℝ) ≤ 2 * s) ∧ w ≤ (Sq t).card ∧
  (∀ j, 1 ≤ j → j ≤ t → R j ⊆ Sq (j - 1)) ∧
  (∀ j, 1 ≤ j → j ≤ t → ∀ x ∈ Sq j, ∃ r ∈ R j, G.Adj r x) ∧
  (∀ j, 1 ≤ j → j ≤ t → ∀ u ∈ T, (∀ l ≤ j, u ∉ Sq l) → ∀ r ∈ R j, ¬ G.Adj u r)

omit [Fintype V] in
/-- In a well-expanding set `T`, the chain can be continued as long as the layers stay small. -/
lemma exists_chain {S T : Finset V} (hTS : T ⊆ S) {s μ : ℝ} {w : ℕ} (hw1 : 1 ≤ w)
    (hws : (w : ℝ) ≤ s) (hwT : w ≤ T.card)
    (hsp : ∀ v ∈ S, ((nbrs G v S).card : ℝ) ≤ s)
    (hexp : ∀ X ⊆ T, X.Nonempty → (X.card : ℝ) ≤ s → μ * X.card < ((nbhd G T X).card : ℝ))
    {k : ℕ} (hnum : ∀ t : ℕ, t + 1 < k → s + (t + 1) * (2 * s) ≤ μ * w) :
    ∀ t, t < k → ∃ Sq R : ℕ → Finset V, ChainProps G T s w t Sq R := by
  have hs0 : 0 < s := lt_of_lt_of_le (by exact_mod_cast hw1) hws
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨S0, hS0T, hS0card⟩ := exists_subset_card_eq hwT
    refine ⟨fun _ => S0, fun _ => ∅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j _; exact hS0T
    · intro i hi j hj hij; omega
    · intro j _; rw [hS0card]; linarith
    · rw [hS0card]
    · intro j h1 h2; omega
    · intro j h1 h2; omega
    · intro j h1 h2; omega
  | succ t ih =>
    intro htk
    classical
    obtain ⟨Sq, R, hT, hdisj, hsmall, hlast, hR, hroot, hpriv⟩ := ih (by omega)
    set U := (range (t + 1)).biUnion Sq with hU
    have hmemU : ∀ u, u ∈ U ↔ ∃ l ≤ t, u ∈ Sq l := by
      intro u; simp [hU]
    have hUcard : (U.card : ℝ) ≤ (t + 1) * (2 * s) := by
      have h1 : (U.card : ℝ) ≤ ∑ l ∈ range (t + 1), ((Sq l).card : ℝ) := by
        exact_mod_cast card_biUnion_le
      have h2 : ∑ l ∈ range (t + 1), ((Sq l).card : ℝ) ≤ ∑ _l ∈ range (t + 1), 2 * s :=
        sum_le_sum fun l hl => hsmall l (Nat.lt_succ_iff.1 (mem_range.1 hl))
      rw [sum_const, card_range, nsmul_eq_mul] at h2
      push_cast at h2
      linarith
    -- a `w`-subset of the last layer expands
    obtain ⟨T', hT'S, hT'card⟩ := exists_subset_card_eq hlast
    have hT'ne : T'.Nonempty := card_pos.1 (by omega)
    have hexpT' := hexp T' (hT'S.trans (hT t le_rfl)) hT'ne (by rw [hT'card]; exact hws)
    rw [hT'card] at hexpT'
    have hgood : s ≤ ((nbhd G T T' \ U).card : ℝ) := by
      have h1 : ((nbhd G T T').card : ℝ) ≤ (nbhd G T T' \ U).card + U.card := by
        have := card_le_card_sdiff_add_card (s := nbhd G T T') (t := U); exact_mod_cast this
      linarith [hnum t htk]
    -- a minimal root set
    have hne : ((Sq t).powerset.filter (fun Rt => s ≤ ((nbhd G T Rt \ U).card : ℝ))).Nonempty :=
      ⟨T', mem_filter.2 ⟨mem_powerset.2 hT'S, hgood⟩⟩
    obtain ⟨Rt, hRtmem, hRtmin⟩ := exists_min_image _ card hne
    obtain ⟨hRtsub, hRts⟩ := mem_filter.1 hRtmem
    rw [mem_powerset] at hRtsub
    have hRtne : Rt.Nonempty := by
      rw [nonempty_iff_ne_empty]; rintro rfl
      rw [nbhd_empty] at hRts; simp at hRts; linarith
    set St := nbhd G T Rt \ U with hSt
    obtain ⟨r, hr⟩ := hRtne
    have hStsmall : (St.card : ℝ) ≤ 2 * s := by
      have hlt : ((nbhd G T (Rt.erase r) \ U).card : ℝ) < s := by
        by_contra hc; push Not at hc
        have := hRtmin (Rt.erase r)
          (mem_filter.2 ⟨mem_powerset.2 ((erase_subset _ _).trans hRtsub), hc⟩)
        have := card_erase_lt_of_mem hr
        omega
      have hsub : St ⊆ (nbhd G T (Rt.erase r) \ U) ∪ nbrs G r S := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := mem_sdiff.1 hu
        obtain ⟨huT, huR, a, ha, hadj⟩ := (mem_nbhd G).1 hu1
        by_cases har : a = r
        · subst har
          exact mem_union_right _ (mem_filter.2 ⟨hTS huT, hadj⟩)
        · exact mem_union_left _ (mem_sdiff.2 ⟨(mem_nbhd G).2
            ⟨huT, fun h => huR (mem_of_mem_erase h), a, mem_erase.2 ⟨har, ha⟩, hadj⟩, hu2⟩)
      have hrS : r ∈ S := hTS (hT t le_rfl (hRtsub hr))
      have h1 : (St.card : ℝ) ≤ (nbhd G T (Rt.erase r) \ U).card + (nbrs G r S).card := by
        have := (card_le_card hsub).trans (card_union_le _ _); exact_mod_cast this
      linarith [hsp r hrS]
    refine ⟨Function.update Sq (t + 1) St, Function.update R (t + 1) Rt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_or_ge j (t + 1) with h | h
      · rw [Function.update_of_ne (by omega)]; exact hT j (by omega)
      · rw [show j = t + 1 by omega, Function.update_self]
        exact fun u hu => ((mem_nbhd G).1 (mem_sdiff.1 hu).1).1
    · have hnew : ∀ l ≤ t, Disjoint St (Sq l) := fun l hl =>
        disjoint_left.2 fun u hu hul => (mem_sdiff.1 hu).2 ((hmemU u).2 ⟨l, hl, hul⟩)
      intro i hi j hj hij
      rcases Nat.lt_or_ge i (t + 1) with h1 | h1 <;> rcases Nat.lt_or_ge j (t + 1) with h2 | h2
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hdisj i (by omega) j (by omega) hij
      · rw [Function.update_of_ne (by omega), show j = t + 1 by omega, Function.update_self]
        exact (hnew i (by omega)).symm
      · rw [show i = t + 1 by omega, Function.update_self, Function.update_of_ne (by omega)]
        exact hnew j (by omega)
      · omega
    · intro j hj
      rcases Nat.lt_or_ge j (t + 1) with h | h
      · rw [Function.update_of_ne (by omega)]; exact hsmall j (by omega)
      · rw [show j = t + 1 by omega, Function.update_self]; exact hStsmall
    · rw [Function.update_self]
      have : (w : ℝ) ≤ St.card := hws.trans hRts
      exact_mod_cast this
    · intro j h1 h2
      rcases Nat.lt_or_ge j (t + 1) with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hR j h1 (by omega)
      · rw [show j = t + 1 by omega, Function.update_self, Nat.add_sub_cancel,
          Function.update_of_ne (by omega)]
        exact hRtsub
    · intro j h1 h2
      rcases Nat.lt_or_ge j (t + 1) with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hroot j h1 (by omega)
      · rw [show j = t + 1 by omega, Function.update_self, Function.update_self]
        intro x hx
        obtain ⟨-, -, a, ha, hadj⟩ := (mem_nbhd G).1 (mem_sdiff.1 hx).1
        exact ⟨a, ha, hadj⟩
    · intro j h1 h2 u huT hnot
      rcases Nat.lt_or_ge j (t + 1) with h | h
      · rw [Function.update_of_ne (by omega)]
        refine hpriv j h1 (by omega) u huT fun l hl => ?_
        have := hnot l hl
        rwa [Function.update_of_ne (by omega)] at this
      · rw [show j = t + 1 by omega, Function.update_self]
        intro r' hr' hadj
        have hnotU : u ∉ U := fun h => by
          obtain ⟨l, hl, hul⟩ := (hmemU u).1 h
          have := hnot l (by omega)
          rw [Function.update_of_ne (by omega)] at this
          exact this hul
        have huRt : u ∉ Rt := fun h => hnotU ((hmemU u).2 ⟨t, le_rfl, hRtsub h⟩)
        have : u ∈ St := mem_sdiff.2
          ⟨(mem_nbhd G).2 ⟨huT, huRt, r', hr', G.adj_symm hadj⟩, hnotU⟩
        have := hnot (t + 1) (by omega)
        rw [Function.update_self] at this
        exact this ‹u ∈ St›

omit [Fintype V] in
/-- An induced path through the layers of a chain. -/
lemma exists_path {T : Finset V} {s : ℝ} {w t₀ : ℕ} {Sq R : ℕ → Finset V}
    (h : ChainProps G T s w t₀ Sq R) :
    ∀ t ≤ t₀, ∀ x ∈ Sq t, ∃ f : ℕ → V, f t = x ∧ (∀ j ≤ t, f j ∈ Sq j) ∧
      (∀ j < t, f j ∈ R (j + 1)) ∧
      ∀ i ≤ t, ∀ j ≤ t, (G.Adj (f i) (f j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
  obtain ⟨hT, hdisj, -, -, hR, hroot, hpriv⟩ := h
  intro t
  induction t with
  | zero =>
    intro _ x hx
    refine ⟨fun _ => x, rfl, ?_, ?_, ?_⟩
    · intro j hj; rwa [Nat.le_zero.1 hj]
    · intro j hj; omega
    · intro i hi j hj
      exact ⟨fun h => absurd h G.irrefl, fun h => by omega⟩
  | succ t ih =>
    intro ht x hx
    obtain ⟨r, hr, hrx⟩ := hroot (t + 1) (by omega) ht x hx
    have hrS : r ∈ Sq t := by simpa using hR (t + 1) (by omega) ht hr
    obtain ⟨f, hft, hfS, hfR, hfadj⟩ := ih (by omega) r hrS
    have hxT : x ∈ T := hT (t + 1) ht hx
    -- `x` is not adjacent to the earlier path vertices
    have hfar : ∀ j < t, ¬ G.Adj x (f j) := by
      intro j hj
      refine hpriv (j + 1) (by omega) (by omega) x hxT (fun l hl hxl => ?_) (f j) (hfR j hj)
      exact disjoint_left.1 (hdisj (t + 1) ht l (by omega) (by omega)) hx hxl
    refine ⟨Function.update f (t + 1) x, Function.update_self _ _ _, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_or_ge j (t + 1) with h | h
      · rw [Function.update_of_ne (by omega)]; exact hfS j (by omega)
      · rw [show j = t + 1 by omega, Function.update_self]; exact hx
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_or_ge j t with h | h
      · exact hfR j h
      · rw [show j = t by omega, hft]; exact hr
    · intro i hi j hj
      rcases Nat.lt_or_ge i (t + 1) with h1 | h1 <;> rcases Nat.lt_or_ge j (t + 1) with h2 | h2
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfadj i (by omega) j (by omega)
      · rw [Function.update_of_ne (by omega), show j = t + 1 by omega, Function.update_self]
        rcases Nat.lt_or_ge i t with h3 | h3
        · constructor
          · intro hadj; exact absurd (G.adj_symm hadj) (hfar i h3)
          · intro hc; omega
        · rw [show i = t by omega, hft]
          exact ⟨fun _ => Or.inl rfl, fun _ => hrx⟩
      · rw [show i = t + 1 by omega, Function.update_self, Function.update_of_ne (by omega)]
        rcases Nat.lt_or_ge j t with h3 | h3
        · constructor
          · intro hadj; exact absurd hadj (hfar j h3)
          · intro hc; omega
        · rw [show j = t by omega, hft]
          exact ⟨fun _ => Or.inr rfl, fun _ => hrx.symm⟩
      · rw [show i = t + 1 by omega, show j = t + 1 by omega, Function.update_self]
        simp

end

/-! ### The statement -/

/-- **NSS V, statement 3.1**, for the path with `k ≥ 1` vertices: if `0 < y ≤ 1/(60k)` and `G[S]` is
`y²`-sparse with no induced `P_k`, then `G[S]` has an anticomplete `(1/y, ⌊y²|S|⌋)`-blockade. -/
theorem nss_path (k : ℕ) (hk : 1 ≤ k) (y : ℝ) (hy : 0 < y) (hyk : y ≤ 1 / (60 * k))
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hsp : Sparse G (y ^ 2) S) (hfree : ¬ ContainsInduced G (pathGraph' k) S) :
    ∃ β : Blockade S (1 / y) (⌊y ^ 2 * S.card⌋₊ : ℝ), β.IsAnticomplete G := by
  classical
  set n : ℝ := (S.card : ℝ) with hn
  set s : ℝ := y ^ 2 * n with hs
  set w : ℕ := ⌊s⌋₊ with hw
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hy60 : y ≤ 1 / 60 := hyk.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  -- the trivial case: blocks may be empty
  by_cases hs1 : s < 1
  · have hw0 : w = 0 := Nat.floor_eq_zero.2 hs1
    refine ⟨⟨⌈1 / y⌉₊, fun _ => ∅, Nat.le_ceil _, fun _ => empty_subset _, fun _ => ?_,
      fun _ _ _ => disjoint_empty_left _⟩, fun _ _ _ a ha => by simp at ha⟩
    rw [hw0]; simp
  push Not at hs1
  set μ : ℝ := 1 / (12 * y) with hμ
  have hsp' : ∀ v ∈ S, ((nbrs G v S).card : ℝ) ≤ s := fun v hv => by
    have := hsp v hv; rwa [← hn] at this
  obtain ⟨𝒜, h𝒜, hexp⟩ := exists_maximal_admissible G S s μ
  set A := 𝒜.biUnion id with hA
  set N := nbhd G S A with hN
  set T := S \ (A ∪ N) with hT
  have hAS : A ⊆ S := fun a ha => by
    obtain ⟨P, hP, haP⟩ := mem_biUnion.1 ha
    exact (h𝒜.1 P hP).1 haP
  have hNS : N ⊆ S := fun u hu => ((mem_nbhd G).1 hu).1
  by_cases hTsmall : (T.card : ℝ) ≤ n / 2
  · -- the removed pieces are numerous: group them into blocks
    have hsize : n ≤ T.card + A.card + N.card := by
      have h1 : S.card ≤ T.card + (A ∪ N).card := card_le_card_sdiff_add_card
      have h2 := card_union_le A N
      have : (S.card : ℝ) ≤ T.card + A.card + N.card := by exact_mod_cast (by omega : S.card ≤ _)
      rwa [← hn] at this
    have hNA : (N.card : ℝ) ≤ μ * A.card := h𝒜.2.2
    have hsum : ∑ P ∈ 𝒜, (P.card : ℝ) = A.card := by
      rw [hA, card_biUnion]
      · push_cast; rfl
      · intro P hP Q hQ hPQ; exact (h𝒜.2.1 P hP Q hQ hPQ).1
    have hμpos : 0 < μ := by positivity
    have hApos : n / (2 * (1 + μ)) ≤ A.card := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hkey : 2 * (⌈1 / y⌉₊ : ℝ) * s ≤ A.card := by
      have hc : (⌈1 / y⌉₊ : ℝ) ≤ 1 / y + 1 := (Nat.ceil_lt_add_one (by positivity)).le
      have h1 : 2 * (⌈1 / y⌉₊ : ℝ) * s ≤ 2 * (1 / y + 1) * s := by
        have : 0 ≤ s := by positivity
        nlinarith
      have h2 : 2 * (1 / y + 1) * s = (2 * y + 2 * y ^ 2) * n := by
        rw [hs]; field_simp
      have h3 : (2 * y + 2 * y ^ 2) * n ≤ n / (2 * (1 + μ)) := by
        rw [hμ, le_div_iff₀ (by positivity)]
        have : (2 * y + 2 * y ^ 2) * (2 * (1 + 1 / (12 * y))) = (2 + 2 * y) * (2 * y + 1 / 6) := by
          field_simp; ring
        rw [mul_assoc, mul_comm n, ← mul_assoc, this]
        have : (2 + 2 * y) * (2 * y + 1 / 6) ≤ 1 := by nlinarith
        nlinarith
      linarith
    obtain ⟨𝔊, h𝔊card, h𝔊sub, h𝔊sum, h𝔊disj⟩ := exists_groups (lt_of_lt_of_le one_pos hs1)
      ⌈1 / y⌉₊ 𝒜 (fun P hP => (h𝒜.1 P hP).2.2) (by rw [hsum]; exact hkey)
    -- blocks are the unions of the groups
    let B : Fin 𝔊.card → Finset V := fun i => (𝔊.equivFin.symm i).val.biUnion id
    have hBmem : ∀ i, (𝔊.equivFin.symm i).val ∈ 𝔊 := fun i => (𝔊.equivFin.symm i).prop
    have hparts : ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ z ∈ B j,
        ∃ P ∈ 𝒜, ∃ Q ∈ 𝒜, P ≠ Q ∧ x ∈ P ∧ z ∈ Q := by
      intro i j hij x hx z hz
      obtain ⟨P, hP, hxP⟩ := mem_biUnion.1 hx
      obtain ⟨Q, hQ, hzQ⟩ := mem_biUnion.1 hz
      have hne : (𝔊.equivFin.symm i).val ≠ (𝔊.equivFin.symm j).val := fun h =>
        hij (𝔊.equivFin.symm.injective (Subtype.ext h))
      refine ⟨P, h𝔊sub _ (hBmem i) hP, Q, h𝔊sub _ (hBmem j) hQ, ?_, hxP, hzQ⟩
      rintro rfl
      exact disjoint_left.1 (h𝔊disj _ (hBmem i) _ (hBmem j) hne) hP hQ
    refine ⟨⟨𝔊.card, B, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (Nat.le_ceil _).trans (by exact_mod_cast h𝔊card)
    · intro i x hx
      obtain ⟨P, hP, hxP⟩ := mem_biUnion.1 hx
      exact (h𝒜.1 P (h𝔊sub _ (hBmem i) hP)).1 hxP
    · intro i
      have hcard : ((B i).card : ℝ) = ∑ P ∈ (𝔊.equivFin.symm i).val, (P.card : ℝ) := by
        simp only [B]
        rw [card_biUnion]
        · push_cast; rfl
        · intro P hP Q hQ hPQ
          exact (h𝒜.2.1 P (h𝔊sub _ (hBmem i) hP) Q (h𝔊sub _ (hBmem i) hQ) hPQ).1
      rw [hcard]
      exact (Nat.floor_le (by positivity)).trans (h𝔊sum _ (hBmem i))
    · intro i j hij
      refine disjoint_left.2 fun x hx hx' => ?_
      obtain ⟨P, hP, Q, hQ, hPQ, hxP, hxQ⟩ := hparts i j hij x hx x hx'
      exact disjoint_left.1 (h𝒜.2.1 P hP Q hQ hPQ).1 hxP hxQ
    · intro i j hij x hx z hz
      obtain ⟨P, hP, Q, hQ, hPQ, hxP, hzQ⟩ := hparts i j hij x hx z hz
      exact (h𝒜.2.1 P hP Q hQ hPQ).2 x hxP z hzQ
  · -- the rest expands well: build an induced path, contradicting `P_k`-freeness
    exfalso
    push Not at hTsmall
    have hw1 : 1 ≤ w := Nat.le_floor (by exact_mod_cast hs1)
    have hws : (w : ℝ) ≤ s := Nat.floor_le (by positivity)
    have hwhalf : s / 2 ≤ w := by
      have := Nat.lt_floor_add_one s
      rcases lt_or_ge s 2 with h | h
      · have : (1 : ℝ) ≤ w := by exact_mod_cast hw1
        linarith
      · linarith
    have hsn : s ≤ n / 2 := by
      rw [hs]; have : y ^ 2 ≤ 1 / 2 := by nlinarith
      nlinarith
    have hwT : w ≤ T.card := by
      have : (w : ℝ) < T.card := by linarith
      exact_mod_cast this.le
    have hnum : ∀ t : ℕ, t + 1 < k → s + (t + 1) * (2 * s) ≤ μ * w := by
      intro t ht
      have htk : ((t : ℝ) + 1) ≤ k - 1 := by
        have : t + 1 ≤ k - 1 := by omega
        have := (Nat.cast_le (α := ℝ)).2 this
        push_cast [Nat.cast_sub hk] at this; linarith
      have hs0 : 0 ≤ s := by positivity
      have h1 : s + (t + 1) * (2 * s) ≤ (2 * k - 1) * s := by nlinarith
      have h2 : μ * (s / 2) ≤ μ * w := mul_le_mul_of_nonneg_left hwhalf (by positivity)
      have h3 : (2 * k - 1) * s ≤ μ * (s / 2) := by
        rw [hμ]
        have hyk' : y * (60 * k) ≤ 1 := by
          rw [le_div_iff₀ (by positivity)] at hyk; linarith
        have : (2 * (k : ℝ) - 1) * (24 * y) ≤ 1 := by nlinarith
        have e : 1 / (12 * y) * (s / 2) = s / (24 * y) := by field_simp; ring
        rw [e, le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    obtain ⟨Sq, R, hchain⟩ := exists_chain G (sdiff_subset : T ⊆ S) hw1 hws hwT hsp'
      (fun X hX hXne hXs => hexp X hX hXne hXs) hnum (k - 1) (by omega)
    obtain ⟨x, hx⟩ : (Sq (k - 1)).Nonempty := card_pos.1 (by have := hchain.2.2.2.1; omega)
    obtain ⟨f, -, hfS, -, hfadj⟩ := exists_path G hchain (k - 1) le_rfl x hx
    apply hfree
    refine ⟨fun i => f i.val, ?_, ?_, ?_⟩
    · intro i j hij
      by_contra hne
      have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
      exact disjoint_left.1 (hchain.2.1 i.val (by omega) j.val (by omega) hne')
        (hfS i.val (by omega)) (by
          have hij' : f i.val = f j.val := hij
          rw [hij']; exact hfS j.val (by omega))
    · intro i
      exact sdiff_subset (hchain.1 i.val (by omega) (hfS i.val (by omega)))
    · intro i j
      rw [hfadj i.val (by omega) j.val (by omega), pathGraph', SimpleGraph.fromRel_adj]
      constructor
      · intro h
        exact ⟨fun hij => by rw [hij] at h; omega, h⟩
      · exact fun h => h.2

/-- **Imported Theorem II, proved**: NSS V statement 3.1 for `P6`. -/
theorem nss_path6_proof : NssPath6 := by
  intro y hy hy6 V _ _ G _ S hsp hfree
  exact nss_path 6 (by norm_num) y hy (by norm_num at hy6 ⊢; linarith) G S hsp hfree

end EHP6
