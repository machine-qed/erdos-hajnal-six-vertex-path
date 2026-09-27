import EHP6.Defs

/-!
# The six-vertex certificate

If six vertices `v₀, …, v₅` of `G` have exactly the non-edges `v₀v₁, v₁v₂, v₂v₃, v₃v₄, v₄v₅` (and all
other ten pairs are edges), they induce a copy of P̄6. Every use of P̄6-freeness in the proof
(Lemmas 1.1, 1.2, 1.3) goes through this lemma.
-/

namespace EHP6

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem coP6_of_facts (v₀ v₁ v₂ v₃ v₄ v₅ : V)
    (e02 : G.Adj v₀ v₂) (e03 : G.Adj v₀ v₃) (e04 : G.Adj v₀ v₄) (e05 : G.Adj v₀ v₅)
    (e13 : G.Adj v₁ v₃) (e14 : G.Adj v₁ v₄) (e15 : G.Adj v₁ v₅)
    (e24 : G.Adj v₂ v₄) (e25 : G.Adj v₂ v₅) (e35 : G.Adj v₃ v₅)
    (n01 : ¬ G.Adj v₀ v₁) (n12 : ¬ G.Adj v₁ v₂) (n23 : ¬ G.Adj v₂ v₃) (n34 : ¬ G.Adj v₃ v₄)
    (n45 : ¬ G.Adj v₄ v₅) :
    ContainsInduced G P6ᶜ Finset.univ := by
  -- distinctness: adjacent pairs by irreflexivity, the five non-adjacent pairs by a separating vertex
  have d02 := G.ne_of_adj e02; have d03 := G.ne_of_adj e03; have d04 := G.ne_of_adj e04
  have d05 := G.ne_of_adj e05; have d13 := G.ne_of_adj e13; have d14 := G.ne_of_adj e14
  have d15 := G.ne_of_adj e15; have d24 := G.ne_of_adj e24; have d25 := G.ne_of_adj e25
  have d35 := G.ne_of_adj e35
  have d01 : v₀ ≠ v₁ := fun h => by subst h; first | exact n12 e02 | exact n12 (G.adj_symm e02)
  have d12 : v₁ ≠ v₂ := fun h => by subst h; first | exact n23 e13 | exact n23 (G.adj_symm e13)
  have d23 : v₂ ≠ v₃ := fun h => by subst h; first | exact n34 e24 | exact n34 (G.adj_symm e24)
  have d34 : v₃ ≠ v₄ := fun h => by subst h; first | exact n45 e35 | exact n45 (G.adj_symm e35)
  have d45 : v₄ ≠ v₅ := fun h => by subst h; first | exact n34 e35 | exact n34 (G.adj_symm e35)
  have hP : ∀ i j : Fin 6, P6ᶜ.Adj i j ↔ (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) := by decide
  refine ⟨![v₀, v₁, v₂, v₃, v₄, v₅], ?_, fun _ => Finset.mem_univ _, ?_⟩
  · intro i j hij
    have h5 : (![v₀, v₁, v₂, v₃, v₄, v₅] : Fin 6 → V) 5 = v₅ := rfl
    fin_cases i <;> fin_cases j <;> simp [h5] at hij ⊢ <;> first | exact absurd hij d02 | exact absurd hij d03 | exact absurd hij d04 | exact absurd hij d05 | exact absurd hij d13 | exact absurd hij d14 | exact absurd hij d15 | exact absurd hij d24 | exact absurd hij d25 | exact absurd hij d35 | exact absurd hij d01 | exact absurd hij d12 | exact absurd hij d23 | exact absurd hij d34 | exact absurd hij d45 | exact absurd hij d02.symm | exact absurd hij d03.symm | exact absurd hij d04.symm | exact absurd hij d05.symm | exact absurd hij d13.symm | exact absurd hij d14.symm | exact absurd hij d15.symm | exact absurd hij d24.symm | exact absurd hij d25.symm | exact absurd hij d35.symm | exact absurd hij d01.symm | exact absurd hij d12.symm | exact absurd hij d23.symm | exact absurd hij d34.symm | exact absurd hij d45.symm
  · intro i j
    rw [hP]
    have f1 : ∀ x : V, ¬ G.Adj x x := fun x => G.irrefl
    have h5 : (![v₀, v₁, v₂, v₃, v₄, v₅] : Fin 6 → V) 5 = v₅ := rfl
    have n10 : ¬ G.Adj v₁ v₀ := fun h => n01 (G.adj_symm h)
    have n21 : ¬ G.Adj v₂ v₁ := fun h => n12 (G.adj_symm h)
    have n32 : ¬ G.Adj v₃ v₂ := fun h => n23 (G.adj_symm h)
    have n43 : ¬ G.Adj v₄ v₃ := fun h => n34 (G.adj_symm h)
    have n54 : ¬ G.Adj v₅ v₄ := fun h => n45 (G.adj_symm h)
    have e20 : G.Adj v₂ v₀ := G.adj_symm e02
    have e30 : G.Adj v₃ v₀ := G.adj_symm e03
    have e40 : G.Adj v₄ v₀ := G.adj_symm e04
    have e50 : G.Adj v₅ v₀ := G.adj_symm e05
    have e31 : G.Adj v₃ v₁ := G.adj_symm e13
    have e41 : G.Adj v₄ v₁ := G.adj_symm e14
    have e51 : G.Adj v₅ v₁ := G.adj_symm e15
    have e42 : G.Adj v₄ v₂ := G.adj_symm e24
    have e52 : G.Adj v₅ v₂ := G.adj_symm e25
    have e53 : G.Adj v₅ v₃ := G.adj_symm e35
    fin_cases i <;> fin_cases j <;> simp [f1, h5, e02, e03, e04, e05, e13, e14, e15, e24, e25, e35, n01, n12, n23, n34, n45, e20, e30, e40, e50, e31, e41, e51, e42, e52, e53, n10, n21, n32, n43, n54]
end EHP6
