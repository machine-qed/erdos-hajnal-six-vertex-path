import EHP6.C01Lemma1
import EHP6.NSSPath
import EHP6.Axioms

/-!
# The Erdős–Hajnal property for P6

The main theorem `EHP6.erdos_hajnal_P6_of_imported` derives `EHforP6` from the four imported theorems of
`EHP6/Imported.lean`, using only Lean's standard axioms. The second of them, NSS V statement 3.1, is
proved in `EHP6/NSSPath.lean`, so `EHP6.erdos_hajnal_P6_of_cited` needs only the other three.
`EHP6.erdos_hajnal_P6 : EHforP6` applies it to the three axioms of `EHP6/Axioms.lean`. Run
`lake env lean Audit.lean` to see the axioms each theorem uses.
-/

namespace EHP6

open Finset Classical

/-- **Theorem 8.3** (paper): the polynomial Rödl property for P̄6-free graphs. -/
theorem polyRodl {A : ℕ} (hA : 1 ≤ A)
    (hL1 : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Free H P6ᶜ → ∀ x : ℝ, 0 < x → x < 1 / 2 → ∀ S : Finset W,
        (∃ F ⊆ S, x ^ A * S.card ≤ F.card ∧ Restricted H x F) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) * x ≤ 1 ∧
          ∃ β : Blockade S k (S.card / (k : ℝ) ^ A), β.IsComplete H ∨ β.IsAnticomplete H))
    (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hfree : Free H P6ᶜ) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ∃ T : Finset W, ε ^ (3 * A) * Fintype.card W ≤ T.card ∧ Restricted H ε T := by
  rw [← card_univ]
  by_cases h : ∃ F ⊆ (univ : Finset W), ε ^ (2 * A) * (univ : Finset W).card ≤ F.card ∧
      ∃ T ⊆ F, ε ^ A * F.card ≤ T.card ∧ Restricted H ε T
  · obtain ⟨F, -, hFc, T, -, hTc, hTr⟩ := h
    refine ⟨T, le_trans ?_ hTc, hTr⟩
    have := mul_le_mul_of_nonneg_left hFc (by positivity : (0 : ℝ) ≤ ε ^ A)
    rw [show 3 * A = A + 2 * A by ring, pow_add, mul_assoc]; exact this
  · push Not at h
    obtain ⟨T, -, hTc, hTr⟩ := c01_lemma2 (G := H) (S := univ) hA hε0 (by linarith)
      (fun F hF hFc => by
        rcases hL1 W H hfree ε hε0 hε F with ⟨F', hF', hF'c, hF'r⟩ | hb
        · exact absurd hF'r (h F hF hFc F' hF' hF'c)
        · exact hb)
    exact ⟨T, hTc, hTr⟩

/-- **Theorem A, as an implication checked without extra axioms.** The four cited results of
`EHP6/Imported.lean` (Rödl's theorem, NSS V 3.1, EH(P5), and the comb lemma NSS VII Lemma 4.3) imply the
Erdős–Hajnal property for P6: there is `τ > 0` such that every P6-free graph has a clique or a stable set
of size at least `|G|^τ`. `#print axioms` lists only Lean's standard axioms for this theorem. -/
theorem erdos_hajnal_P6_of_imported (hR : RodlCoP6) (hP : NssPath6) (hE : EhP5) (hC : NssComb) :
    EHforP6 := by
  obtain ⟨a, ha⟩ := crux_P6 hR hP hE hC
  obtain ⟨A, hA, hL1⟩ := c01_lemma1 hR hP ha
  exact eh_of_polyRodl (A := A) fun W _ _ H _ hfree ε hε0 hε =>
    polyRodl hA hL1 W H hfree ε hε0 hε

/-- **Theorem A from three cited results.** NSS V statement 3.1 (`NssPath6`) is proved in
`EHP6/NSSPath.lean`, so Rödl's theorem, EH(P5) and the comb lemma suffice. `#print axioms` lists only
Lean's standard axioms for this theorem. -/
theorem erdos_hajnal_P6_of_cited (hR : RodlCoP6) (hE : EhP5) (hC : NssComb) : EHforP6 :=
  erdos_hajnal_P6_of_imported hR nss_path6_proof hE hC

/-- **The Erdős–Hajnal property for P6** (Theorem A of the paper), with the three remaining cited
results asserted as the axioms of `EHP6/Axioms.lean`. -/
theorem erdos_hajnal_P6 : EHforP6 :=
  erdos_hajnal_P6_of_cited rodl_coP6 eh_P5 nss_comb

end EHP6
