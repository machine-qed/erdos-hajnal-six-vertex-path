import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Definitions for the formalization of EH(P6)

Conventions follow Section 0 of the paper (`paper/erdos-hajnal-p6.pdf`), which follows
Nguyen–Scott–Seymour. Everything is stated for a finite simple graph `G` on a type `V` and a vertex set
`S : Finset V`; "`G[S]` has property X" is expressed by a predicate on `S`. All sizes are compared as
real numbers.
-/

namespace EHP6

open Finset

section Graph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- neighbours of `v` inside `A` -/
def nbrs (v : V) (A : Finset V) : Finset V := A.filter (G.Adj v)

/-- `G[S]` is `x`-sparse: every vertex of `S` has at most `x|S|` neighbours in `S`. -/
def Sparse (x : ℝ) (S : Finset V) : Prop :=
  ∀ v ∈ S, ((nbrs G v S).card : ℝ) ≤ x * S.card

/-- `G[S]` is `x`-restricted: `G[S]` or its complement is `x`-sparse. -/
def Restricted (x : ℝ) (S : Finset V) : Prop :=
  Sparse G x S ∨ Sparse Gᶜ x S

/-- `B` is `x`-sparse to `A`: every vertex of `B` has at most `x|A|` neighbours in `A`. -/
def SparseTo (x : ℝ) (B A : Finset V) : Prop :=
  ∀ v ∈ B, ((nbrs G v A).card : ℝ) ≤ x * A.card

/-- number of edges between `A` and `B` (ordered pairs `(a, b)` with `a ∈ A`, `b ∈ B`) -/
def edgesBetween (A B : Finset V) : ℕ :=
  ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card

/-- `(A, B)` is weakly `x`-sparse: `e(A, B) ≤ x|A||B|`. -/
def WeaklySparse (x : ℝ) (A B : Finset V) : Prop :=
  (edgesBetween G A B : ℝ) ≤ x * A.card * B.card

def Complete (A B : Finset V) : Prop := ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

def Anticomplete (A B : Finset V) : Prop := ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

def IsCliqueF (T : Finset V) : Prop := ∀ a ∈ T, ∀ b ∈ T, a ≠ b → G.Adj a b

def IsStableF (T : Finset V) : Prop := ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ¬ G.Adj a b

/-- `G[S]` contains an induced copy of the graph `H` on `Fin n`. -/
def ContainsInduced {n : ℕ} (H : SimpleGraph (Fin n)) (S : Finset V) : Prop :=
  ∃ f : Fin n → V, Function.Injective f ∧ (∀ i, f i ∈ S) ∧ ∀ i j, G.Adj (f i) (f j) ↔ H.Adj i j

/-- `G` has no induced copy of `H`. -/
def Free {n : ℕ} (H : SimpleGraph (Fin n)) : Prop := ¬ ContainsInduced G H Finset.univ

/-- `K` is anticonnected: the complement of `G[K]` is connected (for nonempty `K`), i.e. every
partition of `K` into two nonempty parts has a non-adjacent cross pair. -/
def AntiConnected (K : Finset V) : Prop :=
  ∀ P ⊆ K, P.Nonempty → (K \ P).Nonempty → ∃ p ∈ P, ∃ q ∈ K \ P, ¬ G.Adj p q

/-- `K` is an anticomponent of `T` (the vertex set of a component of the complement of `G[T]`):
nonempty, anticonnected, and complete to the rest of `T`. -/
def IsAnticomponent (T K : Finset V) : Prop :=
  K ⊆ T ∧ K.Nonempty ∧ AntiConnected G K ∧ ∀ t ∈ T \ K, ∀ k ∈ K, G.Adj t k

/-- `M` is a module of `G[Y]`: `M ⊆ Y` and every vertex of `Y \ M` is complete or anticomplete to `M`. -/
def IsModule (Y M : Finset V) : Prop :=
  M ⊆ Y ∧ ∀ z ∈ Y \ M, (∀ m ∈ M, G.Adj z m) ∨ (∀ m ∈ M, ¬ G.Adj z m)

end Graph

/-- The path on `Fin n`: `i ~ j` iff `|i − j| = 1`. -/
def pathGraph' (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun i j => i.val + 1 = j.val)

instance (n : ℕ) : DecidableRel (pathGraph' n).Adj := fun i j =>
  decidable_of_iff (i ≠ j ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) (by simp [pathGraph'])

/-- the six-vertex path P6 -/
def P6 : SimpleGraph (Fin 6) := pathGraph' 6

/-- the five-vertex path P5 -/
def P5 : SimpleGraph (Fin 5) := pathGraph' 5

instance : DecidableRel P6.Adj := inferInstanceAs (DecidableRel (pathGraph' 6).Adj)
instance : DecidableRel P5.Adj := inferInstanceAs (DecidableRel (pathGraph' 5).Adj)

/-- A `(k, w)`-blockade inside `S`: at least `k` pairwise disjoint subsets of `S`, each of size at
least `w` (`k`, `w` real, as in the paper). -/
structure Blockade {V : Type} [DecidableEq V] (S : Finset V) (k w : ℝ) where
  m : ℕ
  B : Fin m → Finset V
  len : k ≤ m
  sub : ∀ i, B i ⊆ S
  wid : ∀ i, w ≤ ((B i).card : ℝ)
  disj : ∀ i j, i ≠ j → Disjoint (B i) (B j)

section BlockadeProps

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {S : Finset V} {k w : ℝ}

def Blockade.IsComplete (β : Blockade S k w) : Prop :=
  ∀ i j, i ≠ j → Complete G (β.B i) (β.B j)

def Blockade.IsAnticomplete (β : Blockade S k w) : Prop :=
  ∀ i j, i ≠ j → Anticomplete G (β.B i) (β.B j)

def Blockade.IsPure (β : Blockade S k w) : Prop :=
  ∀ i j, i ≠ j → Complete G (β.B i) (β.B j) ∨ Anticomplete G (β.B i) (β.B j)

/-- every two blocks complete or weakly `x`-sparse -/
def Blockade.IsSemisparse (x : ℝ) (β : Blockade S k w) : Prop :=
  ∀ i j, i ≠ j → Complete G (β.B i) (β.B j) ∨ WeaklySparse G x (β.B i) (β.B j)

/-- `B_j` is `x`-sparse to `B_i` whenever `i < j` -/
def Blockade.IsSparse (x : ℝ) (β : Blockade S k w) : Prop :=
  ∀ i j, i < j → SparseTo G x (β.B j) (β.B i)

end BlockadeProps

/-- **Crux (C)** (paper, Definition 7.1) for P̄6-free graphs, with the parameters of Corollary 7.2:
sparsity exponent `d = 2`, `γ = ½`, threshold `y₀ = 2⁻¹⁶` (here `y ≤ y₀`), and exponent `a`. -/
def CruxC (a : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Free G P6ᶜ → ∀ y : ℝ, 0 < y → y ≤ 1 / 2 ^ 16 → ∀ S : Finset V, Sparse G y S →
      (∃ T ⊆ S, y ^ a * S.card ≤ T.card ∧ Sparse G (y ^ 2) T) ∨
      (∃ β : Blockade S (1 / Real.sqrt y) (y ^ a * S.card), β.IsComplete G ∨ β.IsAnticomplete G)

/-- The Erdős–Hajnal property for P6 (the target theorem). -/
def EHforP6 : Prop :=
  ∃ τ : ℝ, 0 < τ ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Free G P6 → ∃ T : Finset V, (IsCliqueF G T ∨ IsStableF G T) ∧
        (Fintype.card V : ℝ) ^ τ ≤ T.card

end EHP6
