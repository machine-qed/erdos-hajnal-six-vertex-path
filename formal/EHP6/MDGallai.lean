import EHP6.MD

/-!
# Gallai's trichotomy (the forms used in the Tooth Lemma)
-/

namespace EHP6

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `G[K]` is connected (every partition of `K` into two nonempty parts has an edge across). -/
def Conn (G : SimpleGraph V) (K : Finset V) : Prop :=
  ∀ P ⊆ K, P.Nonempty → (K \ P).Nonempty → ∃ p ∈ P, ∃ q ∈ K \ P, G.Adj p q

omit [Fintype V] in
lemma conn_singleton (v : V) : Conn G {v} := by
  intro P hP hPne hrest
  obtain ⟨p, hp⟩ := hPne
  obtain ⟨q, hq⟩ := hrest
  have hp' := mem_singleton.1 (hP hp)
  have hq' := mem_sdiff.1 hq
  rw [mem_singleton.1 hq'.1, ← hp'] at hq'
  exact absurd hp hq'.2

omit [Fintype V] in
/-- the union of two intersecting connected sets is connected -/
lemma conn_union {K L : Finset V} (hK : Conn G K) (hL : Conn G L) (hKL : (K ∩ L).Nonempty) :
    Conn G (K ∪ L) := by
  intro P hP hPne hrest
  obtain ⟨c, hc⟩ := hKL
  obtain ⟨hcK, hcL⟩ := mem_inter.1 hc
  -- if P splits K or L we are done
  by_cases hK1 : (K ∩ P).Nonempty ∧ (K \ P).Nonempty
  · obtain ⟨p, hp, q, hq, hpq⟩ := hK (K ∩ P) inter_subset_left hK1.1
      (by simpa [sdiff_inter_self_left] using hK1.2)
    refine ⟨p, (mem_inter.1 hp).2, q, ?_, hpq⟩
    have hq' := mem_sdiff.1 hq
    exact mem_sdiff.2 ⟨mem_union_left _ hq'.1, fun h => hq'.2 (mem_inter.2 ⟨hq'.1, h⟩)⟩
  by_cases hL1 : (L ∩ P).Nonempty ∧ (L \ P).Nonempty
  · obtain ⟨p, hp, q, hq, hpq⟩ := hL (L ∩ P) inter_subset_left hL1.1
      (by simpa [sdiff_inter_self_left] using hL1.2)
    refine ⟨p, (mem_inter.1 hp).2, q, ?_, hpq⟩
    have hq' := mem_sdiff.1 hq
    exact mem_sdiff.2 ⟨mem_union_right _ hq'.1, fun h => hq'.2 (mem_inter.2 ⟨hq'.1, h⟩)⟩
  exfalso
  -- otherwise K and L each lie entirely inside or outside P, and they share c
  obtain ⟨p, hpP⟩ := hPne
  obtain ⟨q, hq⟩ := hrest
  obtain ⟨hqKL, hqP⟩ := mem_sdiff.1 hq
  have hpKL := hP hpP
  by_cases hcP : c ∈ P
  · -- then all of K and L are inside P
    have hKin : K ⊆ P := by
      intro x hx; by_contra hxP
      exact hK1 ⟨⟨c, mem_inter.2 ⟨hcK, hcP⟩⟩, ⟨x, mem_sdiff.2 ⟨hx, hxP⟩⟩⟩
    have hLin : L ⊆ P := by
      intro x hx; by_contra hxP
      exact hL1 ⟨⟨c, mem_inter.2 ⟨hcL, hcP⟩⟩, ⟨x, mem_sdiff.2 ⟨hx, hxP⟩⟩⟩
    rcases mem_union.1 hqKL with h | h
    · exact hqP (hKin h)
    · exact hqP (hLin h)
  · have hKout : ∀ x ∈ K, x ∉ P := by
      intro x hx hxP
      exact hK1 ⟨⟨x, mem_inter.2 ⟨hx, hxP⟩⟩, ⟨c, mem_sdiff.2 ⟨hcK, hcP⟩⟩⟩
    have hLout : ∀ x ∈ L, x ∉ P := by
      intro x hx hxP
      exact hL1 ⟨⟨x, mem_inter.2 ⟨hx, hxP⟩⟩, ⟨c, mem_sdiff.2 ⟨hcL, hcP⟩⟩⟩
    rcases mem_union.1 hpKL with h | h
    · exact hKout p h hpP
    · exact hLout p h hpP

omit [Fintype V] in
lemma conn_pair {u w : V} (h : G.Adj u w) : Conn G {u, w} := by
  intro P hP hPne hrest
  obtain ⟨p, hp⟩ := hPne
  obtain ⟨q, hq⟩ := hrest
  obtain ⟨hq1, hq2⟩ := mem_sdiff.1 hq
  have hp1 := hP hp
  simp only [mem_insert, mem_singleton] at hp1 hq1
  refine ⟨p, hp, q, hq, ?_⟩
  rcases hp1 with rfl | rfl <;> rcases hq1 with rfl | rfl
  · exact absurd hp hq2
  · exact h
  · exact G.adj_symm h
  · exact absurd hp hq2

/-- a component of `G[N]`: nonempty, connected, anticomplete to the rest of `N` -/
def IsComp (G : SimpleGraph V) (N D : Finset V) : Prop :=
  D ⊆ N ∧ D.Nonempty ∧ Conn G D ∧ ∀ d ∈ D, ∀ z ∈ N \ D, ¬ G.Adj d z

omit [Fintype V] in
/-- every vertex lies in a component, namely a largest connected set through it -/
lemma exists_comp {N : Finset V} {v : V} (hv : v ∈ N) :
    ∃ D, IsComp G N D ∧ v ∈ D ∧ ∀ K ⊆ N, Conn G K → v ∈ K → K ⊆ D := by
  classical
  let F := N.powerset.filter (fun K => Conn G K ∧ v ∈ K)
  have hvF : {v} ∈ F := mem_filter.2 ⟨mem_powerset.2 (singleton_subset_iff.2 hv),
    conn_singleton v, mem_singleton_self v⟩
  obtain ⟨D, hDF, hDmax⟩ := F.exists_max_image card ⟨_, hvF⟩
  obtain ⟨hDN, hDc, hvD⟩ := mem_filter.1 hDF
  have hDN := mem_powerset.1 hDN
  -- maximality: any connected K ⊆ N through v is inside D
  have hsub : ∀ K ⊆ N, Conn G K → v ∈ K → K ⊆ D := by
    intro K hKN hK hvK
    have hU : D ∪ K ∈ F := mem_filter.2 ⟨mem_powerset.2 (union_subset hDN hKN),
      conn_union hDc hK ⟨v, mem_inter.2 ⟨hvD, hvK⟩⟩, mem_union_left _ hvD⟩
    have hle := hDmax _ hU
    have heq : D ∪ K = D := (eq_of_subset_of_card_le subset_union_left hle).symm
    rw [← heq]; exact subset_union_right
  refine ⟨D, ⟨hDN, ⟨v, hvD⟩, hDc, fun d hd z hz hdz => ?_⟩, hvD, hsub⟩
  obtain ⟨hzN, hzD⟩ := mem_sdiff.1 hz
  have hK : Conn G (D ∪ {d, z}) := conn_union hDc (conn_pair hdz) ⟨d, by simp [hd]⟩
  have := hsub (D ∪ {d, z}) (union_subset hDN (by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hDN hd
    · exact hzN)) hK (mem_union_left _ hvD)
  exact hzD (this (by simp))

omit [Fintype V] in
lemma IsComp.anti {N D : Finset V} (hD : IsComp G N D) {d z : V} (hd : d ∈ D) (hz : z ∈ N)
    (hzD : z ∉ D) : ¬ G.Adj z d := fun h => hD.2.2.2 d hd z (mem_sdiff.2 ⟨hz, hzD⟩) (G.adj_symm h)

omit [Fintype V] in
lemma comp_isModule {Y N D : Finset V} (hN : IsModule G Y N) (hD : IsComp G N D) :
    IsModule G Y D := by
  refine ⟨hD.1.trans hN.1, fun z hz => ?_⟩
  obtain ⟨hzY, hzD⟩ := mem_sdiff.1 hz
  by_cases hzN : z ∈ N
  · exact Or.inr fun m hm => hD.anti hm hzN hzD
  · rcases hN.2 z (mem_sdiff.2 ⟨hzY, hzN⟩) with h | h
    · exact Or.inl fun m hm => h m (hD.1 hm)
    · exact Or.inr fun m hm => h m (hD.1 hm)

omit [Fintype V] in
lemma comp_union_isModule {Y N D₁ D₂ : Finset V} (hN : IsModule G Y N) (h₁ : IsComp G N D₁)
    (h₂ : IsComp G N D₂) : IsModule G Y (D₁ ∪ D₂) := by
  refine ⟨union_subset (h₁.1.trans hN.1) (h₂.1.trans hN.1), fun z hz => ?_⟩
  obtain ⟨hzY, hzD⟩ := mem_sdiff.1 hz
  have hz₁ : z ∉ D₁ := fun h => hzD (mem_union_left _ h)
  have hz₂ : z ∉ D₂ := fun h => hzD (mem_union_right _ h)
  by_cases hzN : z ∈ N
  · exact Or.inr fun m hm => (mem_union.1 hm).elim (fun h => h₁.anti h hzN hz₁)
      (fun h => h₂.anti h hzN hz₂)
  · rcases hN.2 z (mem_sdiff.2 ⟨hzY, hzN⟩) with h | h
    · exact Or.inl fun m hm => h m ((mem_union.1 hm).elim (fun h' => h₁.1 h') (fun h' => h₂.1 h'))
    · exact Or.inr fun m hm => h m ((mem_union.1 hm).elim (fun h' => h₁.1 h') (fun h' => h₂.1 h'))

omit [Fintype V] in
/-- components of a strong module are strong modules -/
lemma comp_isStrong {Y N D : Finset V} (hN : IsStrong G Y N) (hD : IsComp G N D) :
    IsStrong G Y D := by
  refine ⟨comp_isModule hN.1 hD, fun X hX => ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hXD, hXsub, hDsub⟩ := hc
  obtain ⟨u, huX, huD⟩ := not_disjoint_iff.1 hXD
  obtain ⟨w, hwX, hwD⟩ := not_subset.1 hXsub
  obtain ⟨d', hd'D, hd'X⟩ := not_subset.1 hDsub
  have hXN : X ⊆ N := by
    rcases hN.2 X hX with h | h | h
    · exact absurd (hD.1 huD) (disjoint_left.1 h huX)
    · exact h
    · exact absurd (h (hD.1 hd'D)) hd'X
  -- every vertex of D \ X is anticomplete to X (it is non-adjacent to w ∈ X)
  have hanti : ∀ d ∈ D, d ∉ X → ∀ m ∈ X, ¬ G.Adj d m := by
    intro d hd hdX
    rcases hX.2 d (mem_sdiff.2 ⟨hN.1.1 (hD.1 hd), hdX⟩) with h | h
    · exact absurd (h w hwX) (fun h' => hD.anti hd (hXN hwX) hwD (G.adj_symm h'))
    · exact h
  obtain ⟨p, hp, q, hq, hpq⟩ := hD.2.2.1 (D ∩ X) inter_subset_left ⟨u, mem_inter.2 ⟨huD, huX⟩⟩
    ⟨d', mem_sdiff.2 ⟨hd'D, fun h => hd'X (mem_inter.1 h).2⟩⟩
  obtain ⟨hqD, hqX⟩ := mem_sdiff.1 hq
  exact hanti q hqD (fun h => hqX (mem_inter.2 ⟨hqD, h⟩)) p (mem_inter.1 hp).2 (G.adj_symm hpq)

omit [Fintype V] in
/-- **Parallel case.** If `G[N]` is disconnected, every nonempty child of the strong module `N` is a
component of `G[N]`. -/
lemma child_isComp_of_not_conn {Y N C : Finset V} (hN : IsStrong G Y N) (hdis : ¬ Conn G N)
    (hC : IsChild G Y N C) (hCne : C.Nonempty) : IsComp G N C := by
  obtain ⟨v, hvC⟩ := hCne
  have hvN := hC.2.1.1 hvC
  obtain ⟨D, hD, hvD, hDmax⟩ := exists_comp (G := G) hvN
  have hDs := comp_isStrong hN hD
  have hDN : D ⊂ N := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨hD.1, fun h => hdis ?_⟩
    rw [← h]; exact hD.2.2.1
  rcases strong_laminar hC.1 hDs with h | h | h
  · exact absurd hvD (disjoint_left.1 h hvC)
  · have := hC.2.2 D hDs h hDN; rw [← this]; exact hD
  · -- D ⊆ C: show C ⊆ D, otherwise build a module overlapping C
    by_cases hCD : C ⊆ D
    · rw [subset_antisymm hCD h]; exact hD
    exfalso
    obtain ⟨w, hwC, hwD⟩ := not_subset.1 hCD
    have hwN := hC.2.1.1 hwC
    obtain ⟨D', hD', hwD', hD'max⟩ := exists_comp (G := G) hwN
    have hDD' : Disjoint D D' := by
      rw [disjoint_iff_ne]
      rintro a haD b hbD' rfl
      have hU := conn_union hD.2.2.1 hD'.2.2.1 ⟨a, mem_inter.2 ⟨haD, hbD'⟩⟩
      exact hwD (hDmax _ (union_subset hD.1 hD'.1) hU (mem_union_left _ hvD)
        (mem_union_right _ hwD'))
    have hD's := comp_isStrong hN hD'
    have hD'C : D' ⊆ C := by
      rcases strong_laminar hD's hC.1 with h' | h' | h'
      · exact absurd hwC (disjoint_left.1 h' hwD')
      · exact h'
      · exact absurd (h' hvC) (disjoint_left.1 hDD' hvD)
    obtain ⟨r, hrN, hrC⟩ := not_subset.1 (fun h' : N ⊆ C => (hC.2.1).2 h')
    obtain ⟨D'', hD'', hrD'', -⟩ := exists_comp (G := G) hrN
    have hD''s := comp_isStrong hN hD''
    have hD''C : Disjoint D'' C := by
      rcases strong_laminar hD''s hC.1 with h' | h' | h'
      · exact h'
      · exact absurd (h' hrD'') hrC
      · exact absurd (h (hDmax D'' hD''.1 hD''.2.2.1 (h' hvC) hrD'')) hrC
    have hX := comp_union_isModule hN.1 hD' hD''
    rcases hC.1.2 _ hX with h' | h' | h'
    · exact disjoint_left.1 h' (mem_union_left _ hwD') hwC
    · exact hrC (h' (mem_union_right _ hrD''))
    · rcases mem_union.1 (h' hvC) with h'' | h''
      · exact disjoint_left.1 hDD' hvD h''
      · exact disjoint_left.1 hD''C h'' hvC

omit [Fintype V] in
/-- **Parallel case.** If `G[N]` is disconnected, distinct nonempty children of `N` are anticomplete. -/
lemma children_anticomplete_of_not_conn {Y N C₁ C₂ : Finset V} (hN : IsStrong G Y N)
    (hdis : ¬ Conn G N) (h₁ : IsChild G Y N C₁) (h₂ : IsChild G Y N C₂) (hne : C₁ ≠ C₂)
    (h₁ne : C₁.Nonempty) : Anticomplete G C₁ C₂ := by
  have hD₁ := child_isComp_of_not_conn hN hdis h₁ h₁ne
  intro a ha b hb hab
  have hbN := h₂.2.1.1 hb
  have hbC₁ : b ∉ C₁ := fun h => disjoint_left.1 (child_disjoint h₁ h₂ hne) h hb
  exact hD₁.anti ha hbN hbC₁ (G.adj_symm hab)

omit [Fintype V] in
lemma isModule_compl {Y M : Finset V} : IsModule Gᶜ Y M ↔ IsModule G Y M := by
  constructor
  · rintro ⟨hMY, h⟩
    refine ⟨hMY, fun z hz => ?_⟩
    have hzM := (mem_sdiff.1 hz).2
    rcases h z hz with h' | h'
    · exact Or.inr fun m hm => ((SimpleGraph.compl_adj G z m).1 (h' m hm)).2
    · refine Or.inl fun m hm => ?_
      by_contra hn
      exact h' m hm ((SimpleGraph.compl_adj G z m).2 ⟨fun e => hzM (e ▸ hm), hn⟩)
  · rintro ⟨hMY, h⟩
    refine ⟨hMY, fun z hz => ?_⟩
    have hzM := (mem_sdiff.1 hz).2
    rcases h z hz with h' | h'
    · exact Or.inr fun m hm hc => ((SimpleGraph.compl_adj G z m).1 hc).2 (h' m hm)
    · exact Or.inl fun m hm => (SimpleGraph.compl_adj G z m).2 ⟨fun e => hzM (e ▸ hm), h' m hm⟩

omit [Fintype V] in
lemma isStrong_compl {Y M : Finset V} : IsStrong Gᶜ Y M ↔ IsStrong G Y M := by
  unfold IsStrong
  simp only [isModule_compl]

omit [Fintype V] in
lemma isChild_compl {Y N C : Finset V} : IsChild Gᶜ Y N C ↔ IsChild G Y N C := by
  unfold IsChild
  simp only [isStrong_compl]

omit [Fintype V] in
/-- **Series case.** If the complement of `G[N]` is disconnected, distinct nonempty children of `N`
are complete to each other. -/
lemma children_complete_of_not_conn_compl {Y N C₁ C₂ : Finset V} (hN : IsStrong G Y N)
    (hdis : ¬ Conn Gᶜ N) (h₁ : IsChild G Y N C₁) (h₂ : IsChild G Y N C₂) (hne : C₁ ≠ C₂)
    (h₁ne : C₁.Nonempty) : Complete G C₁ C₂ := by
  have ha := children_anticomplete_of_not_conn (G := Gᶜ) (isStrong_compl.2 hN) hdis
    (isChild_compl.2 h₁) (isChild_compl.2 h₂) hne h₁ne
  intro a ha' b hb
  by_contra hn
  have hab : a ≠ b := fun e => disjoint_left.1 (child_disjoint h₁ h₂ hne) ha' (e ▸ hb)
  exact ha a ha' b hb ((SimpleGraph.compl_adj G a b).2 ⟨hab, hn⟩)

omit [Fintype V] in
/-- Gallai's key lemma: two overlapping proper modules inside `N` cannot cover `N` if both `G[N]` and
its complement are connected. -/
lemma not_cover_of_prime {Y N M₁ M₂ : Finset V} (hN : N ⊆ Y) (hc : Conn G N) (hc' : Conn Gᶜ N)
    (h₁ : IsModule G Y M₁) (h₂ : IsModule G Y M₂) (h₁N : M₁ ⊆ N) (h₂N : M₂ ⊆ N)
    (h₁ne : M₁ ≠ N) (h₂ne : M₂ ≠ N) (hov : (M₁ ∩ M₂).Nonempty) (hcov : M₁ ∪ M₂ = N) : False := by
  obtain ⟨a₀, ha₀N, ha₀M₂⟩ := not_subset.1 (fun h : N ⊆ M₂ => h₂ne (subset_antisymm h₂N h))
  obtain ⟨b₀, hb₀N, hb₀M₁⟩ := not_subset.1 (fun h : N ⊆ M₁ => h₁ne (subset_antisymm h₁N h))
  have ha₀M₁ : a₀ ∈ M₁ := by
    rw [← hcov] at ha₀N; exact (mem_union.1 ha₀N).resolve_right ha₀M₂
  have hb₀M₂ : b₀ ∈ M₂ := by
    rw [← hcov] at hb₀N; exact (mem_union.1 hb₀N).resolve_left hb₀M₁
  have P_ne : (N \ (M₁ ∩ M₂)).Nonempty :=
    ⟨a₀, mem_sdiff.2 ⟨ha₀N, fun h => ha₀M₂ (mem_inter.1 h).2⟩⟩
  -- every vertex outside M₁ ∩ M₂ lies in exactly one of them
  have split : ∀ q ∈ N \ (M₁ ∩ M₂), (q ∈ M₁ ∧ q ∉ M₂) ∨ (q ∈ M₂ ∧ q ∉ M₁) := by
    intro q hq
    obtain ⟨hqN, hqI⟩ := mem_sdiff.1 hq
    rw [← hcov] at hqN
    rcases mem_union.1 hqN with h | h
    · exact Or.inl ⟨h, fun h' => hqI (mem_inter.2 ⟨h, h'⟩)⟩
    · exact Or.inr ⟨h, fun h' => hqI (mem_inter.2 ⟨h', h⟩)⟩
  by_cases hab : G.Adj a₀ b₀
  · -- everything outside M₁ ∩ M₂ is complete to it: the complement of G[N] is disconnected
    have hb₀c : ∀ m ∈ M₁, G.Adj b₀ m := by
      rcases h₁.2 b₀ (mem_sdiff.2 ⟨hN hb₀N, hb₀M₁⟩) with h | h
      · exact h
      · exact absurd (G.adj_symm hab) (h a₀ ha₀M₁)
    have ha₀c : ∀ m ∈ M₂, G.Adj a₀ m := by
      rcases h₂.2 a₀ (mem_sdiff.2 ⟨hN ha₀N, ha₀M₂⟩) with h | h
      · exact h
      · exact absurd hab (h b₀ hb₀M₂)
    have hA : ∀ a ∈ M₁, a ∉ M₂ → ∀ m ∈ M₂, G.Adj a m := by
      intro a ha haM₂
      rcases h₂.2 a (mem_sdiff.2 ⟨hN (h₁N ha), haM₂⟩) with h | h
      · exact h
      · exact absurd (G.adj_symm (hb₀c a ha)) (h b₀ hb₀M₂)
    have hB : ∀ b ∈ M₂, b ∉ M₁ → ∀ m ∈ M₁, G.Adj b m := by
      intro b hb hbM₁
      rcases h₁.2 b (mem_sdiff.2 ⟨hN (h₂N hb), hbM₁⟩) with h | h
      · exact h
      · exact absurd (G.adj_symm (ha₀c b hb)) (h a₀ ha₀M₁)
    obtain ⟨p, hp, q, hq, hpq⟩ := hc' (M₁ ∩ M₂) (inter_subset_left.trans h₁N) hov P_ne
    have hpq' := ((SimpleGraph.compl_adj G p q).1 hpq).2
    obtain ⟨hp₁, hp₂⟩ := mem_inter.1 hp
    rcases split q hq with ⟨hq₁, hq₂⟩ | ⟨hq₂, hq₁⟩
    · exact hpq' (G.adj_symm (hA q hq₁ hq₂ p hp₂))
    · exact hpq' (G.adj_symm (hB q hq₂ hq₁ p hp₁))
  · -- everything outside M₁ ∩ M₂ is anticomplete to it: G[N] is disconnected
    have hb₀c : ∀ m ∈ M₁, ¬ G.Adj b₀ m := by
      rcases h₁.2 b₀ (mem_sdiff.2 ⟨hN hb₀N, hb₀M₁⟩) with h | h
      · exact absurd (G.adj_symm (h a₀ ha₀M₁)) hab
      · exact h
    have ha₀c : ∀ m ∈ M₂, ¬ G.Adj a₀ m := by
      rcases h₂.2 a₀ (mem_sdiff.2 ⟨hN ha₀N, ha₀M₂⟩) with h | h
      · exact absurd (h b₀ hb₀M₂) hab
      · exact h
    have hA : ∀ a ∈ M₁, a ∉ M₂ → ∀ m ∈ M₂, ¬ G.Adj a m := by
      intro a ha haM₂
      rcases h₂.2 a (mem_sdiff.2 ⟨hN (h₁N ha), haM₂⟩) with h | h
      · exact absurd (G.adj_symm (h b₀ hb₀M₂)) (hb₀c a ha)
      · exact h
    have hB : ∀ b ∈ M₂, b ∉ M₁ → ∀ m ∈ M₁, ¬ G.Adj b m := by
      intro b hb hbM₁
      rcases h₁.2 b (mem_sdiff.2 ⟨hN (h₂N hb), hbM₁⟩) with h | h
      · exact absurd (G.adj_symm (h a₀ ha₀M₁)) (ha₀c b hb)
      · exact h
    obtain ⟨p, hp, q, hq, hpq⟩ := hc (M₁ ∩ M₂) (inter_subset_left.trans h₁N) hov P_ne
    obtain ⟨hp₁, hp₂⟩ := mem_inter.1 hp
    rcases split q hq with ⟨hq₁, hq₂⟩ | ⟨hq₂, hq₁⟩
    · exact hA q hq₁ hq₂ p hp₂ (G.adj_symm hpq)
    · exact hB q hq₂ hq₁ p hp₁ (G.adj_symm hpq)

omit [Fintype V] in
/-- **Prime case (MD2).** If `G[N]` and its complement are both connected, every nonempty module of
`G[Y]` properly inside the strong module `N` lies inside a child of `N`. -/
lemma module_in_child_of_prime {Y N X : Finset V} (hN : IsStrong G Y N) (hc : Conn G N)
    (hc' : Conn Gᶜ N) (hX : IsModule G Y X) (hXN : X ⊆ N) (hXne : X ≠ N) :
    ∃ C, IsChild G Y N C ∧ X ⊆ C := by
  classical
  let F := N.powerset.filter (fun M => IsModule G Y M ∧ X ⊆ M ∧ M ≠ N)
  have hXF : X ∈ F := mem_filter.2 ⟨mem_powerset.2 hXN, hX, subset_rfl, hXne⟩
  obtain ⟨M, hMF, hMmax⟩ := F.exists_max_image card ⟨X, hXF⟩
  obtain ⟨hMN, hM, hXM, hMne⟩ := mem_filter.1 hMF
  have hMN := mem_powerset.1 hMN
  have hMs : IsStrong G Y M := by
    refine ⟨hM, fun Z hZ => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hZM, hZsub, hMsub⟩ := hcon
    obtain ⟨u, huZ, huM⟩ := not_disjoint_iff.1 hZM
    have hZN : Z ⊆ N := by
      rcases hN.2 Z hZ with h | h | h
      · exact absurd (hMN huM) (disjoint_left.1 h huZ)
      · exact h
      · exact absurd (hMN.trans h) hMsub
    have hU := module_union hZ hM ⟨u, mem_inter.2 ⟨huZ, huM⟩⟩
    by_cases hUN : Z ∪ M = N
    · have hZne : Z ≠ N := fun h => hMsub (h ▸ hMN)
      exact not_cover_of_prime hN.1.1 hc hc' hZ hM hZN hMN hZne hMne
        ⟨u, mem_inter.2 ⟨huZ, huM⟩⟩ hUN
    · have hUF : Z ∪ M ∈ F := mem_filter.2 ⟨mem_powerset.2 (union_subset hZN hMN), hU,
        hXM.trans subset_union_right, hUN⟩
      have heq := eq_of_subset_of_card_le (subset_union_right (s₁ := Z)) (hMmax _ hUF)
      exact hZsub (heq ▸ subset_union_left)
  refine ⟨M, ⟨hMs, Finset.ssubset_iff_subset_ne.2 ⟨hMN, hMne⟩, fun M' hM' hMM' hM'N => ?_⟩, hXM⟩
  have hM'F : M' ∈ F := mem_filter.2 ⟨mem_powerset.2 hM'N.1, hM'.1, hXM.trans hMM', hM'N.ne⟩
  exact (eq_of_subset_of_card_le hMM' (hMmax _ hM'F)).symm

end EHP6
