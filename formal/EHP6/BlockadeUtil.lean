import EHP6.MD

/-!
# Blockade utilities
-/

namespace EHP6

open Finset

variable {V : Type} [DecidableEq V]

/-- enlarge the ambient set and weaken length/width -/
def Blockade.mono {S S' : Finset V} {k w k' w' : ℝ} (β : Blockade S k w) (hS : S ⊆ S')
    (hk : k' ≤ k) (hw : w' ≤ w) : Blockade S' k' w' where
  m := β.m
  B := β.B
  len := hk.trans β.len
  sub := fun i => (β.sub i).trans hS
  wid := fun i => hw.trans (β.wid i)
  disj := β.disj

/-- a blockade from a family of pairwise disjoint sets, indexed by an enumeration of the family -/
noncomputable def Blockade.ofFamily (S : Finset V) (k w : ℝ) (𝒜 : Finset (Finset V))
    (hsub : ∀ A ∈ 𝒜, A ⊆ S) (hdisj : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → Disjoint A B)
    (hw : ∀ A ∈ 𝒜, w ≤ (A.card : ℝ)) (hk : k ≤ 𝒜.card) : Blockade S k w where
  m := 𝒜.card
  B := fun i => (𝒜.equivFin.symm i).val
  len := hk
  sub := fun i => hsub _ (𝒜.equivFin.symm i).prop
  wid := fun i => hw _ (𝒜.equivFin.symm i).prop
  disj := fun i j hij => hdisj _ (𝒜.equivFin.symm i).prop _ (𝒜.equivFin.symm j).prop
    (fun h => hij (𝒜.equivFin.symm.injective (Subtype.ext h)))

lemma Blockade.ofFamily_mem (S : Finset V) (k w : ℝ) (𝒜 : Finset (Finset V)) (hsub hdisj hw hk)
    (i : Fin (Blockade.ofFamily S k w 𝒜 hsub hdisj hw hk).m) :
    (Blockade.ofFamily S k w 𝒜 hsub hdisj hw hk).B i ∈ 𝒜 :=
  (𝒜.equivFin.symm i).prop

lemma Blockade.ofFamily_ne (S : Finset V) (k w : ℝ) (𝒜 : Finset (Finset V)) (hsub hdisj hw hk)
    {i j : Fin (Blockade.ofFamily S k w 𝒜 hsub hdisj hw hk).m} (hij : i ≠ j) :
    (Blockade.ofFamily S k w 𝒜 hsub hdisj hw hk).B i ≠
      (Blockade.ofFamily S k w 𝒜 hsub hdisj hw hk).B j :=
  fun h => hij (𝒜.equivFin.symm.injective (Subtype.ext h))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- a family of pairwise disjoint modules of `G[Y]` gives a pure blockade (MD1) -/
lemma pure_of_modules (Y : Finset V) (k w : ℝ) (𝒜 : Finset (Finset V))
    (hmod : ∀ A ∈ 𝒜, IsModule G Y A) (hdisj : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → Disjoint A B)
    (hw : ∀ A ∈ 𝒜, w ≤ (A.card : ℝ)) (hk : k ≤ 𝒜.card) :
    ∃ β : Blockade Y k w, β.IsPure G := by
  refine ⟨Blockade.ofFamily Y k w 𝒜 (fun A hA => (hmod A hA).1) hdisj hw hk, fun i j hij => ?_⟩
  have hi := Blockade.ofFamily_mem Y k w 𝒜 (fun A hA => (hmod A hA).1) hdisj hw hk i
  have hj := Blockade.ofFamily_mem Y k w 𝒜 (fun A hA => (hmod A hA).1) hdisj hw hk j
  exact module_pure (hmod _ hi) (hmod _ hj)
    (hdisj _ hi _ hj (Blockade.ofFamily_ne Y k w 𝒜 _ hdisj hw hk hij))

end EHP6
