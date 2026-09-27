import EHP6.Defs

/-!
# Modular decomposition (the facts used in the Tooth Lemma)

All modules are modules of `G[Y]` for a fixed vertex set `Y`. We prove:
* (MD1) disjoint modules are pure to each other;
* strong modules are laminar; the *children* of a strong module `N` (maximal strong modules properly
  inside `N`) are pairwise disjoint and cover `N` (when `|N| ≥ 2`);
* Gallai's trichotomy in the form used: if `G[N]` is disconnected, distinct children are anticomplete;
  if the complement is disconnected, they are complete; if both are connected, every module properly
  inside `N` lies inside one child (MD2).
-/

namespace EHP6

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- a strong module of `G[Y]`: a module overlapping no other module -/
def IsStrong (Y M : Finset V) : Prop :=
  IsModule G Y M ∧ ∀ X, IsModule G Y X → Disjoint X M ∨ X ⊆ M ∨ M ⊆ X

/-- `C` is a child of `N`: a maximal strong module properly contained in `N` -/
def IsChild (Y N C : Finset V) : Prop :=
  IsStrong G Y C ∧ C ⊂ N ∧ ∀ M, IsStrong G Y M → C ⊆ M → M ⊂ N → M = C

variable {G}

omit [Fintype V] in
lemma isModule_singleton {Y : Finset V} {v : V} (hv : v ∈ Y) : IsModule G Y {v} := by
  refine ⟨singleton_subset_iff.2 hv, fun z _ => ?_⟩
  by_cases h : G.Adj z v
  · exact Or.inl fun m hm => by rw [mem_singleton.1 hm]; exact h
  · exact Or.inr fun m hm => by rw [mem_singleton.1 hm]; exact h

omit [Fintype V] in
lemma isModule_self (Y : Finset V) : IsModule G Y Y :=
  ⟨subset_rfl, fun z hz => absurd (mem_sdiff.1 hz).1 (mem_sdiff.1 hz).2⟩

omit [Fintype V] in
/-- (MD1) disjoint modules are pure to each other -/
lemma module_pure {Y A B : Finset V} (hA : IsModule G Y A) (hB : IsModule G Y B)
    (hAB : Disjoint A B) : Complete G A B ∨ Anticomplete G A B := by
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact Or.inl fun a _ b hb => absurd hb (notMem_empty b)
  have hb₀A : b₀ ∉ A := fun h => disjoint_left.1 hAB h hb₀
  rcases hA.2 b₀ (mem_sdiff.2 ⟨hB.1 hb₀, hb₀A⟩) with hc | hn
  · refine Or.inl fun a ha b hb => ?_
    have haB : a ∉ B := fun h => disjoint_left.1 hAB ha h
    rcases hB.2 a (mem_sdiff.2 ⟨hA.1 ha, haB⟩) with h | h
    · exact h b hb
    · exact absurd (G.adj_symm (hc a ha)) (h b₀ hb₀)
  · refine Or.inr fun a ha b hb => ?_
    have haB : a ∉ B := fun h => disjoint_left.1 hAB ha h
    rcases hB.2 a (mem_sdiff.2 ⟨hA.1 ha, haB⟩) with h | h
    · exact absurd (G.adj_symm (h b₀ hb₀)) (hn a ha)
    · exact h b hb

omit [Fintype V] in
/-- the union of two overlapping modules is a module -/
lemma module_union {Y M₁ M₂ : Finset V} (h₁ : IsModule G Y M₁) (h₂ : IsModule G Y M₂)
    (hov : (M₁ ∩ M₂).Nonempty) : IsModule G Y (M₁ ∪ M₂) := by
  obtain ⟨c, hc⟩ := hov
  obtain ⟨hc₁, hc₂⟩ := mem_inter.1 hc
  refine ⟨union_subset h₁.1 h₂.1, fun z hz => ?_⟩
  obtain ⟨hzY, hzM⟩ := mem_sdiff.1 hz
  have hz₁ : z ∉ M₁ := fun h => hzM (mem_union_left _ h)
  have hz₂ : z ∉ M₂ := fun h => hzM (mem_union_right _ h)
  rcases h₁.2 z (mem_sdiff.2 ⟨hzY, hz₁⟩) with a₁ | a₁ <;>
    rcases h₂.2 z (mem_sdiff.2 ⟨hzY, hz₂⟩) with a₂ | a₂
  · exact Or.inl fun m hm => (mem_union.1 hm).elim (a₁ m) (a₂ m)
  · exact absurd (a₁ c hc₁) (a₂ c hc₂)
  · exact absurd (a₂ c hc₂) (a₁ c hc₁)
  · exact Or.inr fun m hm => (mem_union.1 hm).elim (a₁ m) (a₂ m)

omit [Fintype V] in
lemma isStrong_singleton {Y : Finset V} {v : V} (hv : v ∈ Y) : IsStrong G Y {v} := by
  refine ⟨isModule_singleton hv, fun X _ => ?_⟩
  by_cases h : v ∈ X
  · exact Or.inr (Or.inr (singleton_subset_iff.2 h))
  · exact Or.inl (disjoint_singleton_right.2 h)

omit [Fintype V] in
lemma isStrong_self (Y : Finset V) : IsStrong G Y Y :=
  ⟨isModule_self Y, fun X hX => Or.inr (Or.inl hX.1)⟩

omit [Fintype V] in
/-- strong modules are laminar -/
lemma strong_laminar {Y M N : Finset V} (hM : IsStrong G Y M) (hN : IsStrong G Y N) :
    Disjoint M N ∨ M ⊆ N ∨ N ⊆ M :=
  hN.2 M hM.1

omit [Fintype V] in
/-- distinct children of `N` are disjoint -/
lemma child_disjoint {Y N C₁ C₂ : Finset V} (h₁ : IsChild G Y N C₁) (h₂ : IsChild G Y N C₂)
    (hne : C₁ ≠ C₂) : Disjoint C₁ C₂ := by
  rcases strong_laminar h₁.1 h₂.1 with h | h | h
  · exact h
  · exact absurd (h₁.2.2 C₂ h₂.1 h h₂.2.1).symm hne
  · exact absurd (h₂.2.2 C₁ h₁.1 h h₁.2.1) hne

omit [Fintype V] in
/-- every vertex of a strong module `N` with at least two vertices lies in a child of `N` -/
lemma exists_child {Y N : Finset V} (hN : IsStrong G Y N) {v : V} (hv : v ∈ N)
    (hN2 : ∃ w ∈ N, w ≠ v) : ∃ C, IsChild G Y N C ∧ v ∈ C := by
  classical
  let F := N.powerset.filter (fun M => IsStrong G Y M ∧ v ∈ M ∧ M ⊂ N)
  have hvF : {v} ∈ F := by
    obtain ⟨w, hw, hwv⟩ := hN2
    refine mem_filter.2 ⟨mem_powerset.2 (singleton_subset_iff.2 hv),
      isStrong_singleton (hN.1.1 hv), mem_singleton_self v, ?_⟩
    refine Finset.ssubset_iff_subset_ne.2 ⟨singleton_subset_iff.2 hv, fun h => hwv ?_⟩
    rw [← h] at hw; exact mem_singleton.1 hw
  obtain ⟨C, hCF, hCmax⟩ := F.exists_max_image card ⟨_, hvF⟩
  obtain ⟨-, hCs, hvC, hCN⟩ := mem_filter.1 hCF
  refine ⟨C, ⟨hCs, hCN, fun M hM hCM hMN => ?_⟩, hvC⟩
  have hMF : M ∈ F := mem_filter.2 ⟨mem_powerset.2 hMN.1, hM, hCM hvC, hMN⟩
  exact (eq_of_subset_of_card_le hCM (hCmax M hMF)).symm

end EHP6
