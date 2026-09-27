import EHP6.Round2Pass

/-!
# Corollary 1.4 (second part) and the Claim in Step 4 of Lemma 6.1
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- the conclusion of EH(P5) with exponent `κ` -/
def EHP5 (κ : ℝ) : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    Free H P5 → ∃ T : Finset U, (IsCliqueF H T ∨ IsStableF H T) ∧ (Fintype.card U : ℝ) ^ κ ≤ T.card

/-- **Corollary 1.4 (second part).** Among the blocks on which `v` is lightly mixed there are
`|I(v)|^κ` which are pairwise complete or pairwise non-complete. -/
theorem light_hom (hfree : Free G P6ᶜ) {ℓ : ℕ} {B : Fin ℓ → Finset V} {W : ℕ} {x : ℝ}
    (hS : BlockSystem G B W x) (v : V) {κ : ℝ} (hEH : EHP5 κ) :
    ∃ R ⊆ lightIdx G B W v,
      ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → Complete G (B i) (B j)) ∨
       (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬ Complete G (B i) (B j))) ∧
      ((lightIdx G B W v).card : ℝ) ^ κ ≤ R.card := by
  obtain ⟨I, hI⟩ : ∃ I, I = lightIdx G B W v := ⟨_, rfl⟩
  rw [← hI]
  let H : SimpleGraph {i // i ∈ I} :=
    { Adj := fun a b => a ≠ b ∧ ¬ (patternGraph G B).Adj a.val b.val
      symm := ⟨fun a b h => ⟨h.1.symm, fun h' => h.2 ((patternGraph G B).adj_symm h')⟩⟩
      loopless := ⟨fun a h => h.1 rfl⟩ }
  have hH : ∀ a b : {i // i ∈ I}, H.Adj a b ↔ a ≠ b ∧ ¬ (patternGraph G B).Adj a.val b.val :=
    fun a b => Iff.rfl
  haveI : DecidableRel H.Adj := Classical.decRel _
  have hfreeH : Free H P5 := by
    rintro ⟨g, hg, -, hadj⟩
    apply light_pattern_house_free hfree hS v
    refine ⟨fun t => (g t).val, fun s t h => hg (Subtype.ext h), fun t => hI ▸ (g t).prop,
      fun s t => ?_⟩
    have h := hadj s t
    rw [hH] at h
    rw [SimpleGraph.compl_adj]
    by_cases hst : s = t
    · subst hst
      simp only [ne_eq, not_true_eq_false, false_and, iff_false]
      exact (patternGraph G B).irrefl
    · have hne : g s ≠ g t := fun e => hst (hg e)
      constructor
      · intro hp; exact ⟨hst, fun hP => (h.2 hP).2 hp⟩
      · rintro ⟨-, hnP⟩; by_contra hp; exact hnP (h.1 ⟨hne, hp⟩)
  obtain ⟨T, hT, hTc⟩ := hEH {i // i ∈ I} H hfreeH
  refine ⟨T.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro i hi; obtain ⟨j, -, rfl⟩ := mem_map.1 hi; exact j.prop
  · rcases hT with hc | hs
    · right
      intro i hi j hj hij hcomp
      obtain ⟨i', hi', rfl⟩ := mem_map.1 hi
      obtain ⟨j', hj', rfl⟩ := mem_map.1 hj
      have hne : i' ≠ j' := fun e => hij (by rw [e])
      have := (hH i' j').1 (hc i' hi' j' hj' hne)
      exact this.2 ⟨hij, hcomp, fun a ha b hb => G.adj_symm (hcomp b hb a ha)⟩
    · left
      intro i hi j hj hij
      obtain ⟨i', hi', rfl⟩ := mem_map.1 hi
      obtain ⟨j', hj', rfl⟩ := mem_map.1 hj
      have hne : i' ≠ j' := fun e => hij (by rw [e])
      have h1 := hs i' hi' j' hj' hne
      rw [hH] at h1
      push Not at h1
      exact (h1 hne).2.1
  · rw [card_map]; rwa [Fintype.card_coe] at hTc

/-- **The Claim in Step 4 of Lemma 6.1**: a vertex lightly mixed on many blocks yields outcome (a) or (b). -/
theorem light_small (hfree : Free G P6ᶜ) {ℓ : ℕ} {B : Fin ℓ → Finset V} {b : ℕ} {θ : ℝ}
    (hS : BlockSystem G B b θ) (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) {S : Finset V}
    (hBS : ∀ i, B i ⊆ S) (v : V) {κ y w : ℝ} (hEH : EHP5 κ) (hy0 : 0 < y) (hy : y ≤ 1 / 2)
    (hr : 1 / y ^ 5 ≤ ((lightIdx G B b v).card : ℝ) ^ κ) (hθ : θ ≤ y ^ 5) (hbw : w ≤ b) :
    (∃ T ⊆ S, w ≤ T.card ∧ Sparse G (y ^ 4) T) ∨ (∃ β : Blockade S (1 / y) w, β.IsComplete G) := by
  obtain ⟨R, -, hR, hRc⟩ := light_hom hfree hS v hEH
  have hRr : 1 / y ^ 5 ≤ (R.card : ℝ) := hr.trans hRc
  have hy1 : y ≤ 1 := by linarith
  have h1y : 1 / y ≤ 1 / y ^ 5 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    calc y ^ 5 ≤ y ^ 1 := pow_le_pow_of_le_one hy0.le hy1 (by norm_num)
      _ = y := pow_one y
  have hRpos : 0 < R.card := by
    have : (1 : ℝ) ≤ 1 / y ^ 5 := by
      rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_one₀ hy0.le hy1
    have : (0 : ℝ) < R.card := by linarith
    exact_mod_cast this
  rcases hR with hc | hn
  · -- pairwise complete: outcome (b)
    right
    refine ⟨⟨R.card, fun k => B (R.equivFin.symm k), h1y.trans hRr, fun k => hBS _,
      fun k => by rw [hS.card]; exact hbw, fun k k' hkk' => hdisj _ _ (fun e => hkk'
        (R.equivFin.symm.injective (Subtype.ext e)))⟩, fun k k' hkk' => ?_⟩
    exact hc _ (R.equivFin.symm k).prop _ (R.equivFin.symm k').prop
      (fun e => hkk' (R.equivFin.symm.injective (Subtype.ext e)))
  · -- pairwise non-complete: outcome (a) on the union
    left
    have hTc : ((R.biUnion B).card : ℝ) = R.card * b := by
      rw [card_biUnion (fun i _ j _ h => hdisj i j h)]
      simp only [hS.card, sum_const, smul_eq_mul]; push_cast; ring
    have hbr : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    refine ⟨R.biUnion B, biUnion_subset.2 fun i _ => hBS i, ?_, fun u hu => ?_⟩
    · rw [hTc]
      have : (1 : ℝ) ≤ R.card := by exact_mod_cast hRpos
      nlinarith
    · obtain ⟨i, hi, hui⟩ := mem_biUnion.1 hu
      have hsub : nbrs G u (R.biUnion B) ⊆ R.biUnion (fun j => nbrs G u (B j)) := by
        intro z hz
        obtain ⟨hzT, hzu⟩ := mem_filter.1 hz
        obtain ⟨j, hj, hzj⟩ := mem_biUnion.1 hzT
        exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨hzj, hzu⟩⟩
      have h1 : ((nbrs G u (R.biUnion B)).card : ℝ) ≤ ∑ j ∈ R, ((nbrs G u (B j)).card : ℝ) := by
        have := (card_le_card hsub).trans card_biUnion_le
        exact_mod_cast this
      have h2 : ∑ j ∈ R, ((nbrs G u (B j)).card : ℝ) ≤ b + (R.card - 1) * (θ * b) := by
        rw [← add_sum_erase R _ hi]
        have a1 : ((nbrs G u (B i)).card : ℝ) ≤ b := by
          have := card_le_card (filter_subset (G.Adj u) (B i))
          rw [hS.card] at this; exact_mod_cast this
        have a2 : ∑ j ∈ R.erase i, ((nbrs G u (B j)).card : ℝ) ≤ ∑ _j ∈ R.erase i, θ * b :=
          sum_le_sum fun j hj => by
            obtain ⟨hji, hjR⟩ := mem_erase.1 hj
            have hsp := (hS.sparse_of_not_complete (Ne.symm hji) (hn i hi j hjR (Ne.symm hji))).1
            have := hsp u hui
            rwa [hS.card] at this
        rw [sum_const, card_erase_of_mem hi, nsmul_eq_mul] at a2
        have : ((R.card - 1 : ℕ) : ℝ) = R.card - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [this] at a2
        linarith
      have hθ0 : 0 < θ := hS.hx
      have h3 : (b : ℝ) ≤ y ^ 5 * (R.card * b) := by
        have := mul_le_mul_of_nonneg_left hRr (by positivity : (0 : ℝ) ≤ y ^ 5 * b)
        have e : y ^ 5 * b * (1 / y ^ 5) = b := by field_simp
        nlinarith
      have h4 : (R.card - 1) * (θ * b) ≤ y ^ 5 * (R.card * b) := by
        have : ((R.card : ℝ) - 1) * (θ * b) ≤ R.card * (θ * b) := by nlinarith
        have := mul_le_mul_of_nonneg_right hθ (by positivity : (0 : ℝ) ≤ R.card * b)
        nlinarith
      have h5 : 2 * y ^ 5 ≤ y ^ 4 := by
        have : y ^ 5 = y ^ 4 * y := by ring
        nlinarith [pow_pos hy0 4]
      rw [hTc]
      nlinarith [show (0 : ℝ) ≤ R.card * b by positivity]

end EHP6
