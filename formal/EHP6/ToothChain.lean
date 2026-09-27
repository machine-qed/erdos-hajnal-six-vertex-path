import EHP6.ToothMass
import EHP6.ToothCount
import EHP6.BlockadeUtil

/-!
# Tooth Lemma, Steps 1–2: many large disjoint modules (TL1) or a heavy chain

`t` plays the role of `n/k`. Numeric hypotheses are kept abstract here and discharged in the
assembly of the Tooth Lemma.
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Lfam_laminar {Y : Finset V} {s : ℝ} {N N' : Finset V} (hN : N ∈ Lfam G Y s)
    (hN' : N' ∈ Lfam G Y s) : Disjoint N N' ∨ N ⊆ N' ∨ N' ⊆ N :=
  strong_laminar (mem_Lfam.1 hN).2.1 (mem_Lfam.1 hN').2.1

theorem heavy_chain {Y : Finset V} {s t : ℝ} {K₀ K₁ : ℕ} (hs : 1 < s) (hst : s ≤ t)
    (htY : t ≤ Y.card) (hK₀ : 2 ≤ K₀) (hK : K₀ ≤ K₁) (htK : (Y.card : ℝ) / (K₀ : ℝ) ^ 4 ≤ t)
    (hbound : ((K₀ : ℝ) - 1) * t + Y.card / ((K₀ : ℝ) - 1) +
      (Y.card / s) * (Y.card / (K₁ : ℝ) ^ 4) ≤ Y.card / 4) :
    (∃ K : ℕ, K₀ ≤ K ∧ K ≤ K₁ ∧ ∃ β : Blockade Y K (Y.card / (K : ℝ) ^ 4), β.IsPure G) ∨
    ∃ 𝒞 ⊆ Lfam G Y s, (∀ N ∈ 𝒞, ∀ N' ∈ 𝒞, N ⊆ N' ∨ N' ⊆ N) ∧ (∀ N ∈ 𝒞, t ≤ (N.card : ℝ)) ∧
      3 * Y.card / (4 * ((K₀ : ℝ) - 1)) ≤ ∑ N ∈ 𝒞, ((atomPart G Y s N).card : ℝ) := by
  set n : ℝ := (Y.card : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hK₀r : (2 : ℝ) ≤ K₀ := by exact_mod_cast hK₀
  have hsY : s ≤ n := hst.trans htY
  set Ls := (Lfam G Y s).filter (fun N => t ≤ (N.card : ℝ)) with hLs
  set Lt := (Lfam G Y s).filter (fun N => ¬ t ≤ (N.card : ℝ)) with hLt
  set Mn := Ls.filter (fun N => ∀ M ∈ Ls, M ⊆ N → M = N) with hMn
  set Mx := Lt.filter (fun N => ∀ M ∈ Lt, N ⊆ M → M = N) with hMx
  have hLsL : Ls ⊆ Lfam G Y s := filter_subset _ _
  have hLtL : Lt ⊆ Lfam G Y s := filter_subset _ _
  have hYLs : Y ∈ Ls := mem_filter.2 ⟨mem_Lfam.2 ⟨subset_rfl, isStrong_self Y, hsY⟩, htY⟩
  -- pairwise disjointness of the minimal heavy and maximal light members
  have Mn_disj : ∀ A ∈ Mn, ∀ B ∈ Mn, A ≠ B → Disjoint A B := by
    intro A hA B hB hAB
    obtain ⟨hALs, hAmin⟩ := mem_filter.1 hA
    obtain ⟨hBLs, hBmin⟩ := mem_filter.1 hB
    rcases Lfam_laminar (hLsL hALs) (hLsL hBLs) with h | h | h
    · exact h
    · exact absurd (hBmin A hALs h) hAB
    · exact absurd (hAmin B hBLs h).symm hAB
  have Mx_disj : ∀ A ∈ Mx, ∀ B ∈ Mx, A ≠ B → Disjoint A B := by
    intro A hA B hB hAB
    obtain ⟨hALt, hAmax⟩ := mem_filter.1 hA
    obtain ⟨hBLt, hBmax⟩ := mem_filter.1 hB
    rcases Lfam_laminar (hLtL hALt) (hLtL hBLt) with h | h | h
    · exact h
    · exact absurd (hAmax B hBLt h).symm hAB
    · exact absurd (hBmax A hALt h) hAB
  have mod_of : ∀ A ∈ Lfam G Y s, IsModule G Y A := fun A hA => (mem_Lfam.1 hA).2.1.1
  -- TL1 from many minimal heavy members
  by_cases hMnbig : (K₀ : ℝ) ≤ Mn.card
  · left
    refine ⟨K₀, le_rfl, hK, pure_of_modules G Y K₀ _ Mn
      (fun A hA => mod_of A (hLsL (mem_filter.1 hA).1)) Mn_disj (fun A hA => ?_) hMnbig⟩
    exact htK.trans (mem_filter.1 (mem_filter.1 hA).1).2
  push Not at hMnbig
  -- TL1 from many large maximal light members, else the antichain bound
  by_cases hfew : ∃ K : ℕ, K₀ ≤ K ∧ K ≤ K₁ ∧
      (K : ℝ) ≤ ((Mx.filter (fun A => n / (K : ℝ) ^ 4 ≤ A.card)).card : ℝ)
  · left
    obtain ⟨K, hK0K, hKK1, hKc⟩ := hfew
    refine ⟨K, hK0K, hKK1, pure_of_modules G Y K _ _
      (fun A hA => mod_of A (hLtL (mem_filter.1 (mem_filter.1 hA).1).1))
      (fun A hA B hB => Mx_disj A (mem_filter.1 hA).1 B (mem_filter.1 hB).1)
      (fun A hA => (mem_filter.1 hA).2) hKc⟩
  push Not at hfew
  right
  have Mx_small : ∀ A ∈ Mx, (A.card : ℝ) ≤ t := fun A hA =>
    le_of_lt (not_le.1 (mem_filter.1 (mem_filter.1 hA).1).2)
  have Mx_sub : ∀ A ∈ Mx, A ⊆ Y := fun A hA => (mem_Lfam.1 (hLtL (mem_filter.1 hA).1)).1
  have Mx_big : ∀ A ∈ Mx, s ≤ (A.card : ℝ) := fun A hA =>
    (mem_Lfam.1 (hLtL (mem_filter.1 hA).1)).2.2
  have Mx_pd : (Mx : Set (Finset V)).PairwiseDisjoint id := fun A hA B hB hAB => Mx_disj A hA B hB hAB
  have Mx_total : ∑ A ∈ Mx, (A.card : ℝ) ≤ n := by
    have : ∑ A ∈ Mx, (A.card : ℝ) = (Mx.biUnion id).card := by
      exact_mod_cast (card_biUnion Mx_pd).symm
    have hsub : Mx.biUnion id ⊆ Y := biUnion_subset.2 (fun A hA => Mx_sub A hA)
    rw [this, hn]; exact_mod_cast card_le_card hsub
  have Mx_count : (Mx.card : ℝ) * s ≤ n := by
    calc (Mx.card : ℝ) * s = ∑ A ∈ Mx, s := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ A ∈ Mx, (A.card : ℝ) := sum_le_sum Mx_big
      _ ≤ n := Mx_total
  have hmass := antichain_mass Mx n t K₀ K₁ hK₀ hK hn0 (by linarith) Mx_small hfew
  have hK1pos : (0 : ℝ) < (K₁ : ℝ) ^ 4 := by
    have : (2 : ℝ) ≤ K₁ := by exact_mod_cast hK₀.trans hK
    positivity
  have Mx_card_le : (Mx.card : ℝ) ≤ n / s := by rw [le_div_iff₀ (by linarith)]; exact Mx_count
  have hMxsum : ∑ A ∈ Mx, (A.card : ℝ) ≤ n / 4 := by
    have : (Mx.card : ℝ) * (n / (K₁ : ℝ) ^ 4) ≤ (n / s) * (n / (K₁ : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_right Mx_card_le (div_nonneg hn0 hK1pos.le)
    linarith
  -- light members lie inside maximal light members
  have Lt_cov : ∀ N ∈ Lt, ∃ A ∈ Mx, N ⊆ A := by
    intro N hN
    let F := Lt.filter (fun M => N ⊆ M)
    obtain ⟨A, hAF, hAmax⟩ := F.exists_max_image card ⟨N, mem_filter.2 ⟨hN, subset_rfl⟩⟩
    obtain ⟨hALt, hNA⟩ := mem_filter.1 hAF
    refine ⟨A, mem_filter.2 ⟨hALt, fun M hM hAM => ?_⟩, hNA⟩
    exact (eq_of_subset_of_card_le hAM (hAmax M (mem_filter.2 ⟨hM, hNA.trans hAM⟩))).symm
  have hLtmass : ∑ N ∈ Lt, ((atomPart G Y s N).card : ℝ) ≤ n / 4 :=
    (sum_atomPart_le_of_cover hs hsY Lt hLtL Mx Lt_cov Mx_pd).trans hMxsum
  have hLsmass : 3 * n / 4 ≤ ∑ N ∈ Ls, ((atomPart G Y s N).card : ℝ) := by
    have htot := sum_atomPart_eq (G := G) hs hsY
    rw [← sum_filter_add_sum_filter_not (Lfam G Y s) (fun N => t ≤ (N.card : ℝ))] at htot
    linarith
  -- chains through minimal heavy members
  have Ls_cov : ∀ N ∈ Ls, ∃ m ∈ Mn, m ⊆ N := by
    intro N hN
    let F := Ls.filter (fun M => M ⊆ N)
    obtain ⟨m, hmF, hmmin⟩ := F.exists_min_image card ⟨N, mem_filter.2 ⟨hN, subset_rfl⟩⟩
    obtain ⟨hmLs, hmN⟩ := mem_filter.1 hmF
    refine ⟨m, mem_filter.2 ⟨hmLs, fun M hM hMm => ?_⟩, hmN⟩
    exact eq_of_subset_of_card_le hMm (hmmin M (mem_filter.2 ⟨hM, hMm.trans hmN⟩))
  set f : Finset V → ℝ := fun N => ((atomPart G Y s N).card : ℝ) with hf
  have fnn : ∀ N, 0 ≤ f N := fun N => Nat.cast_nonneg _
  have hcover : ∑ N ∈ Ls, f N ≤ ∑ m ∈ Mn, ∑ N ∈ Ls.filter (fun N => m ⊆ N), f N := by
    calc ∑ N ∈ Ls, f N ≤ ∑ N ∈ Ls, ∑ m ∈ Mn, (if m ⊆ N then f N else 0) := by
          refine sum_le_sum fun N hN => ?_
          obtain ⟨m, hm, hmN⟩ := Ls_cov N hN
          have := single_le_sum (f := fun m => if m ⊆ N then f N else 0)
            (fun m _ => by split_ifs <;> [exact fnn N; exact le_rfl]) hm
          simpa [hmN] using this
      _ = ∑ m ∈ Mn, ∑ N ∈ Ls.filter (fun N => m ⊆ N), f N := by
          rw [sum_comm]; refine sum_congr rfl fun m _ => ?_; exact (sum_filter _ _).symm
  have hMnne : Mn.Nonempty := by
    obtain ⟨m, hm, -⟩ := Ls_cov Y hYLs; exact ⟨m, hm⟩
  have hMncard : (Mn.card : ℝ) ≤ (K₀ : ℝ) - 1 := by
    have : Mn.card < K₀ := by exact_mod_cast hMnbig
    have : Mn.card ≤ K₀ - 1 := by omega
    have h' : ((Mn.card : ℕ) : ℝ) ≤ ((K₀ - 1 : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h'; simpa using h'
  set c : ℝ := 3 * n / (4 * ((K₀ : ℝ) - 1)) with hc
  have hc0 : 0 ≤ c := by apply div_nonneg (by linarith) (by linarith)
  have hsumc : ∑ m ∈ Mn, c ≤ ∑ m ∈ Mn, ∑ N ∈ Ls.filter (fun N => m ⊆ N), f N := by
    rw [sum_const, nsmul_eq_mul]
    calc (Mn.card : ℝ) * c ≤ ((K₀ : ℝ) - 1) * c := mul_le_mul_of_nonneg_right hMncard hc0
      _ = 3 * n / 4 := by
          have hK1ne : (K₀ : ℝ) - 1 ≠ 0 := by linarith
          rw [hc]; field_simp <;> ring
      _ ≤ _ := hLsmass.trans hcover
  obtain ⟨m, hm, hmc⟩ := exists_le_of_sum_le hMnne hsumc
  obtain ⟨hmLs, -⟩ := mem_filter.1 hm
  have hmne : m.Nonempty := by
    have : t ≤ (m.card : ℝ) := (mem_filter.1 hmLs).2
    exact card_pos.1 (by exact_mod_cast (show (0 : ℝ) < m.card by linarith))
  refine ⟨Ls.filter (fun N => m ⊆ N), (filter_subset _ _).trans hLsL, fun N hN N' hN' => ?_,
    fun N hN => (mem_filter.1 (mem_filter.1 hN).1).2, hmc⟩
  obtain ⟨hNLs, hmN⟩ := mem_filter.1 hN
  obtain ⟨hN'Ls, hmN'⟩ := mem_filter.1 hN'
  rcases Lfam_laminar (hLsL hNLs) (hLsL hN'Ls) with h | h | h
  · obtain ⟨v, hv⟩ := hmne
    exact absurd (hmN' hv) (disjoint_left.1 h (hmN hv))
  · exact Or.inl h
  · exact Or.inr h

end EHP6
