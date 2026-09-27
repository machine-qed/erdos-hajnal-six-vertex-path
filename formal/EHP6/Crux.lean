import EHP6.Round2b

/-!
# Corollary 7.2 (paper): Crux (C) holds for P̄6-free graphs
-/

namespace EHP6

/-- **Corollary 7.2.** Crux (C) holds with `d = 2`, `γ = ½`, `y₀ = 2⁻¹⁶` and some exponent `a`
(`a = A₁/2 + 1` with `A₁ = M(10d² + 3)`, `M` even, `M ≥ 5/κ + 4`). -/
theorem crux_P6 (hR : RodlCoP6) (hP : NssPath6) (hE : EhP5) (hcomb : NssComb) :
    ∃ a : ℕ, CruxC a := by
  obtain ⟨d, hd, hnd⟩ := nice_P6 hR hP hcomb
  obtain ⟨κ, hκ, hEH⟩ := hE
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, M' = ⌈5 / κ + 4⌉₊ := ⟨_, rfl⟩
  have hM : 5 / κ + 4 ≤ ((2 * M' : ℕ) : ℝ) := by
    have h1 : 5 / κ + 4 ≤ (M' : ℝ) := by rw [hM']; exact Nat.le_ceil _
    have h0 : (0 : ℝ) ≤ M' := Nat.cast_nonneg _
    push_cast; linarith
  refine ⟨M' * (10 * d ^ 2 + 3) + 1, fun V _ _ G _ hfree y hy0 hy S hsp => ?_⟩
  have h61 : Out61 G ((2 * M') * (10 * d ^ 2 + 3)) := fun y' hy'0 hy' S' hsp' =>
    round2_step hfree hd (fun ε hε0 hε S'' hS'' => hnd ε hε0 hε V G hfree S'' hS'') hκ hEH hM
      hy'0 hy' S' hsp'
  exact round2 (k := M' * (10 * d ^ 2 + 3)) (by ring) h61 hy0 hy S hsp

end EHP6
