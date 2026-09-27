import EHP6.Layout
import EHP6.Round1

/-!
# Lemma 5.2 (niceness of P6): Lemma 4.3 feeds Theorem 5.1
-/

namespace EHP6

open Finset

lemma nice_size {ε s f : ℝ} {d : ℕ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : 1 / ε ^ (10 * d ^ 2) ≤ s)
    (hf : ε ^ d * s ≤ f) : 1 / (ε ^ (5 * d)) ^ d ≤ f := by
  have e1 : (ε ^ (5 * d)) ^ d = ε ^ (5 * d ^ 2) := by rw [← pow_mul]; congr 1; ring
  rw [e1]
  have h1 : ε ^ (10 * d ^ 2) ≤ ε ^ d * ε ^ (5 * d ^ 2) := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one hε0.le hε1 (by nlinarith)
  have h2 : ε ^ d * (1 / ε ^ (10 * d ^ 2)) ≤ ε ^ d * s :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h3 : 1 / ε ^ (5 * d ^ 2) ≤ ε ^ d * (1 / ε ^ (10 * d ^ 2)) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  linarith

/-- **Lemma 5.2** (NSS VII Theorem 6.2 for P6). With `d` from Lemma 4.3: for every `ε ∈ (0, ½)` and
every P̄6-free `G[S]` with `|S| ≥ ε^{-10d²}`, `G[S]` has an `(ε⁻¹, ε^{10d²}|S|)`-blockade in which every
two blocks are complete or weakly `ε^d`-sparse. -/
theorem nice_P6 (hR : RodlCoP6) (hP : NssPath6) (hcomb : NssComb) : ∃ d : ℕ, 200 ≤ d ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Free H P6ᶜ → ∀ S : Finset W, 1 / ε ^ (10 * d ^ 2) ≤ (S.card : ℝ) →
        ∃ β : Blockade S (1 / ε) (ε ^ (10 * d ^ 2) * S.card), β.IsSemisparse H (ε ^ d) := by
  obtain ⟨d, hd, h43⟩ := round1_blockade hR hP hcomb
  refine ⟨d, hd, fun ε hε0 hε1 W _ _ H _ hfree S hS => ?_⟩
  have hε1' : ε < 1 := by linarith
  have hx : ε ^ (5 * d) < 1 / 2 ^ d := by
    have h1 : ε ^ (5 * d) ≤ ε ^ d := pow_le_pow_of_le_one hε0.le hε1'.le (by omega)
    have h2 : ε ^ d < (1 / 2) ^ d := pow_lt_pow_left₀ hε1 hε0.le (by omega)
    rw [one_div_pow] at h2
    linarith
  obtain ⟨β, hβ⟩ := layout_theorem (G := H) hε0 hε1' (by omega) S (fun F hF hFc =>
    h43 (ε ^ (5 * d)) (by positivity) hx W H hfree F (nice_size hε0 hε1'.le hS hFc))
  have e : (ε ^ (5 * d)) ^ (2 * d) = ε ^ (10 * d ^ 2) := by rw [← pow_mul]; congr 1; ring
  exact ⟨β.mono subset_rfl le_rfl (by rw [e]), fun i j hij => hβ i j hij⟩

end EHP6
