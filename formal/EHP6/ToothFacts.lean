import EHP6.MDGallai

/-!
# The Tooth Lemma: structural facts (F1)–(F3) and the three node types

`𝓛` = strong modules of `G[Y]` with at least `s` vertices; `S(N)` = union of the children of `N` with
fewer than `s` vertices ("atoms").
-/

namespace EHP6

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
lemma antiConnected_iff_conn_compl {K : Finset V} : AntiConnected G K ↔ Conn Gᶜ K := by
  constructor
  · intro h P hP hne hrest
    obtain ⟨p, hp, q, hq, hpq⟩ := h P hP hne hrest
    exact ⟨p, hp, q, hq, (SimpleGraph.compl_adj G p q).2
      ⟨fun e => (mem_sdiff.1 hq).2 (e ▸ hp), hpq⟩⟩
  · intro h P hP hne hrest
    obtain ⟨p, hp, q, hq, hpq⟩ := h P hP hne hrest
    exact ⟨p, hp, q, hq, ((SimpleGraph.compl_adj G p q).1 hpq).2⟩

omit [Fintype V] in
lemma isAnticomponent_iff_isComp_compl {T A : Finset V} :
    IsAnticomponent G T A ↔ IsComp Gᶜ T A := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, antiConnected_iff_conn_compl.1 h3, fun d hd z hz hc => ?_⟩
    exact ((SimpleGraph.compl_adj G d z).1 hc).2 (G.adj_symm (h4 z hz d hd))
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, antiConnected_iff_conn_compl.2 h3, fun t ht k hk => ?_⟩
    by_contra hn
    have htk : t ≠ k := fun e => (mem_sdiff.1 ht).2 (e ▸ hk)
    exact h4 k hk t ht ((SimpleGraph.compl_adj G k t).2 ⟨htk.symm, fun h => hn (G.adj_symm h)⟩)

variable (G)

open Classical in
/-- `𝓛`: strong modules of `G[Y]` with at least `s` vertices -/
noncomputable def Lfam (Y : Finset V) (s : ℝ) : Finset (Finset V) :=
  Y.powerset.filter (fun N => IsStrong G Y N ∧ s ≤ N.card)

open Classical in
/-- `S(N)`: the union of the children of `N` with fewer than `s` vertices -/
noncomputable def atomPart (Y : Finset V) (s : ℝ) (N : Finset V) : Finset V :=
  N.filter (fun v => ∃ C, IsChild G Y N C ∧ v ∈ C ∧ (C.card : ℝ) < s)

open Classical

variable {G}

lemma mem_Lfam {Y : Finset V} {s : ℝ} {N : Finset V} :
    N ∈ Lfam G Y s ↔ N ⊆ Y ∧ IsStrong G Y N ∧ s ≤ N.card := by
  unfold Lfam; simp [mem_filter, mem_powerset, and_assoc]

lemma atomPart_subset {Y : Finset V} {s : ℝ} {N : Finset V} : atomPart G Y s N ⊆ N :=
  filter_subset _ _

/-- (F3) if `M ⊊ N` are both in `𝓛`, then `S(N)` misses `M` -/
lemma atomPart_disjoint {Y : Finset V} {s : ℝ} {N M : Finset V} (hN : N ∈ Lfam G Y s)
    (hM : M ∈ Lfam G Y s) (hMN : M ⊂ N) : Disjoint (atomPart G Y s N) M := by
  rw [disjoint_left]
  intro v hv hvM
  obtain ⟨-, C, hC, hvC, hCs⟩ := mem_filter.1 hv
  obtain ⟨-, hMs, hMsz⟩ := mem_Lfam.1 hM
  rcases strong_laminar hMs hC.1 with h | h | h
  · exact disjoint_left.1 h hvM hvC
  · have : (M.card : ℝ) ≤ C.card := by exact_mod_cast card_le_card h
    linarith
  · have heq := hC.2.2 M hMs h hMN
    subst heq
    linarith

/-- (F1, uniqueness) a vertex lies in `S(N)` for at most one `N ∈ 𝓛` -/
lemma atomPart_unique {Y : Finset V} {s : ℝ} {N N' : Finset V} (hN : N ∈ Lfam G Y s)
    (hN' : N' ∈ Lfam G Y s) {v : V} (hv : v ∈ atomPart G Y s N) (hv' : v ∈ atomPart G Y s N') :
    N = N' := by
  have hvN := atomPart_subset hv
  have hvN' := atomPart_subset hv'
  rcases strong_laminar (mem_Lfam.1 hN).2.1 (mem_Lfam.1 hN').2.1 with h | h | h
  · exact absurd hvN' (disjoint_left.1 h hvN)
  · by_contra hne
    exact disjoint_left.1 (atomPart_disjoint hN' hN (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩)) hv' hvN
  · by_contra hne
    exact disjoint_left.1 (atomPart_disjoint hN hN' (Finset.ssubset_iff_subset_ne.2 ⟨h, Ne.symm hne⟩))
      hv hvN'

/-- (F1, existence) if `1 < s ≤ |Y|`, every vertex of `Y` lies in `S(N)` for some `N ∈ 𝓛` -/
lemma exists_atomPart {Y : Finset V} {s : ℝ} (hs : 1 < s) (hsY : s ≤ Y.card) {v : V} (hv : v ∈ Y) :
    ∃ N ∈ Lfam G Y s, v ∈ atomPart G Y s N := by
  classical
  let F := (Lfam G Y s).filter (fun N => v ∈ N)
  have hYF : Y ∈ F := mem_filter.2 ⟨mem_Lfam.2 ⟨subset_rfl, isStrong_self Y, hsY⟩, hv⟩
  obtain ⟨N, hNF, hNmin⟩ := F.exists_min_image card ⟨Y, hYF⟩
  obtain ⟨hNL, hvN⟩ := mem_filter.1 hNF
  obtain ⟨hNY, hNs, hNsz⟩ := mem_Lfam.1 hNL
  have h2 : ∃ w ∈ N, w ≠ v := by
    by_contra hc
    push Not at hc
    have : N ⊆ {v} := fun w hw => mem_singleton.2 (hc w hw)
    have : (N.card : ℝ) ≤ 1 := by exact_mod_cast (card_le_card this).trans (card_singleton v).le
    linarith
  obtain ⟨C, hC, hvC⟩ := exists_child hNs hvN h2
  refine ⟨N, hNL, mem_filter.2 ⟨hvN, C, hC, hvC, ?_⟩⟩
  by_contra hCs
  push Not at hCs
  have hCF : C ∈ F := mem_filter.2 ⟨mem_Lfam.2 ⟨hC.2.1.1.trans hNY, hC.1, hCs⟩, hvC⟩
  have := hNmin C hCF
  exact absurd (card_lt_card hC.2.1) (not_lt.2 this)

/-- a child of `N` meeting `S(N)` is an atom -/
lemma child_small_of_meets {Y : Finset V} {s : ℝ} {N C : Finset V} (hC : IsChild G Y N C)
    {v : V} (hvC : v ∈ C) (hv : v ∈ atomPart G Y s N) : (C.card : ℝ) < s := by
  classical
  obtain ⟨-, C', hC', hvC', hC's⟩ := mem_filter.1 hv
  by_cases h : C = C'
  · rw [h]; exact hC's
  · exact absurd hvC' (disjoint_left.1 (child_disjoint hC hC' h) hvC)

/-- **Parallel node.** Connected subsets of `S(N)` lie inside a single atom. -/
lemma conn_in_atom_of_parallel {Y : Finset V} {s : ℝ} {N D : Finset V} (hN : N ∈ Lfam G Y s)
    (hdis : ¬ Conn G N) (hDS : D ⊆ atomPart G Y s N) (hD : Conn G D) {v : V} (hvD : v ∈ D) :
    (D.card : ℝ) < s := by
  classical
  obtain ⟨-, C, hC, hvC, hCs⟩ := mem_filter.1 (hDS hvD)
  have hDC : D ⊆ C := by
    by_contra hc
    obtain ⟨w, hwD, hwC⟩ := not_subset.1 hc
    obtain ⟨p, hp, q, hq, hpq⟩ := hD (D ∩ C) inter_subset_left ⟨v, mem_inter.2 ⟨hvD, hvC⟩⟩
      ⟨w, mem_sdiff.2 ⟨hwD, fun h => hwC (mem_inter.1 h).2⟩⟩
    obtain ⟨hqD, hqDC⟩ := mem_sdiff.1 hq
    have hqC : q ∉ C := fun h => hqDC (mem_inter.2 ⟨hqD, h⟩)
    obtain ⟨-, Cq, hCq, hqCq, -⟩ := mem_filter.1 (hDS hqD)
    have hne : C ≠ Cq := fun e => hqC (e ▸ hqCq)
    exact children_anticomplete_of_not_conn (mem_Lfam.1 hN).2.1 hdis hC hCq hne ⟨v, hvC⟩
      p (mem_inter.1 hp).2 q hqCq hpq
  have : (D.card : ℝ) ≤ C.card := by exact_mod_cast card_le_card hDC
  linarith

/-- **Series node.** Anticonnected subsets of `S(N)` lie inside a single atom. -/
lemma anticonn_in_atom_of_series {Y : Finset V} {s : ℝ} {N D : Finset V} (hN : N ∈ Lfam G Y s)
    (hdis : ¬ Conn Gᶜ N) (hDS : D ⊆ atomPart G Y s N) (hD : AntiConnected G D) {v : V}
    (hvD : v ∈ D) : (D.card : ℝ) < s := by
  classical
  obtain ⟨-, C, hC, hvC, hCs⟩ := mem_filter.1 (hDS hvD)
  have hDC : D ⊆ C := by
    by_contra hc
    obtain ⟨w, hwD, hwC⟩ := not_subset.1 hc
    obtain ⟨p, hp, q, hq, hpq⟩ := hD (D ∩ C) inter_subset_left ⟨v, mem_inter.2 ⟨hvD, hvC⟩⟩
      ⟨w, mem_sdiff.2 ⟨hwD, fun h => hwC (mem_inter.1 h).2⟩⟩
    obtain ⟨hqD, hqDC⟩ := mem_sdiff.1 hq
    have hqC : q ∉ C := fun h => hqDC (mem_inter.2 ⟨hqD, h⟩)
    obtain ⟨-, Cq, hCq, hqCq, -⟩ := mem_filter.1 (hDS hqD)
    have hne : C ≠ Cq := fun e => hqC (e ▸ hqCq)
    exact hpq (children_complete_of_not_conn_compl (mem_Lfam.1 hN).2.1 hdis hC hCq hne ⟨v, hvC⟩
      p (mem_inter.1 hp).2 q hqCq)
  have : (D.card : ℝ) ≤ C.card := by exact_mod_cast card_le_card hDC
  linarith

/-- **(F2), prime node.** If `u`'s trace `T` has module anticomponents and does not contain `S(N)`,
every anticomponent of `G[T ∩ S(N)]` has fewer than `s` vertices. -/
lemma trace_pieces_small_of_prime {Y : Finset V} {s : ℝ} {N : Finset V} (hN : N ∈ Lfam G Y s)
    (hc : Conn G N) (hc' : Conn Gᶜ N) {T : Finset V} (hTY : T ⊆ Y)
    (hT : ∀ A, IsAnticomponent G T A → IsModule G Y A) (hST : ¬ atomPart G Y s N ⊆ T)
    {K : Finset V} (hK : IsAnticomponent G (T ∩ atomPart G Y s N) K) : (K.card : ℝ) < s := by
  obtain ⟨hKsub, ⟨v, hvK⟩, hKanti, -⟩ := hK
  have hvT := (mem_inter.1 (hKsub hvK)).1
  have hvS := (mem_inter.1 (hKsub hvK)).2
  obtain ⟨A, hA, hvA, hAmax⟩ := exists_comp (G := Gᶜ) hvT
  have hKA : K ⊆ A := hAmax K (hKsub.trans inter_subset_left)
    (antiConnected_iff_conn_compl.1 hKanti) hvK
  have hAmod := hT A (isAnticomponent_iff_isComp_compl.2 hA)
  obtain ⟨hNY, hNs, -⟩ := mem_Lfam.1 hN
  have hAN : A ⊆ N ∧ A ≠ N := by
    rcases hNs.2 A hAmod with h | h | h
    · exact absurd (atomPart_subset hvS) (disjoint_left.1 h hvA)
    · refine ⟨h, fun e => hST ?_⟩
      rw [← e] at *
      exact atomPart_subset.trans hA.1
    · exact absurd ((atomPart_subset (s := s)).trans (h.trans hA.1)) hST
  obtain ⟨C, hC, hAC⟩ := module_in_child_of_prime hNs hc hc' hAmod hAN.1 hAN.2
  have hCs := child_small_of_meets hC (hAC hvA) hvS
  have : (K.card : ℝ) ≤ C.card := by exact_mod_cast card_le_card (hKA.trans hAC)
  linarith

end EHP6
