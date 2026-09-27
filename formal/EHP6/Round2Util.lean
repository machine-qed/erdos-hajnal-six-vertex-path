import EHP6.Round1
import EHP6.House

/-!
# Utilities for §6: anticonnected subsets, edge counting, averaging
-/

namespace EHP6

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
lemma anticonn_singleton (v : V) : AntiConnected G {v} := by
  intro P hP hPne hrest
  obtain ⟨u, hu⟩ := hPne
  obtain ⟨w, hw⟩ := hrest
  obtain ⟨hw1, hw2⟩ := mem_sdiff.1 hw
  rw [mem_singleton.1 hw1] at hw2
  rw [← mem_singleton.1 (hP hu)] at hw2
  exact absurd hu hw2

omit [Fintype V] [DecidableRel G.Adj] in
lemma anticonn_insert {B : Finset V} (hB : AntiConnected G B) {p q : V} (hp : p ∈ B) (hq : q ∉ B)
    (hpq : ¬ G.Adj p q) : AntiConnected G (insert q B) := by
  intro P hP hPne hrest
  by_cases hqP : q ∈ P
  · by_cases hPB : (P ∩ B).Nonempty
    · by_cases hBP : B ⊆ P
      · exfalso
        obtain ⟨w, hw⟩ := hrest
        obtain ⟨hw1, hw2⟩ := mem_sdiff.1 hw
        rcases mem_insert.1 hw1 with rfl | h
        · exact hw2 hqP
        · exact hw2 (hBP h)
      · obtain ⟨b, hbB, hbP⟩ := not_subset.1 hBP
        obtain ⟨p', hp', q', hq', h⟩ := hB (P ∩ B) inter_subset_right hPB
          ⟨b, mem_sdiff.2 ⟨hbB, fun h => hbP (mem_inter.1 h).1⟩⟩
        obtain ⟨hq'B, hq'PB⟩ := mem_sdiff.1 hq'
        exact ⟨p', (mem_inter.1 hp').1, q', mem_sdiff.2 ⟨mem_insert_of_mem hq'B,
          fun h' => hq'PB (mem_inter.2 ⟨h', hq'B⟩)⟩, h⟩
    · have hpP : p ∉ P := fun h => hPB ⟨p, mem_inter.2 ⟨h, hp⟩⟩
      exact ⟨q, hqP, p, mem_sdiff.2 ⟨mem_insert_of_mem hp, hpP⟩, fun h => hpq (G.adj_symm h)⟩
  · have hPsub : P ⊆ B := fun w hw => by
      rcases mem_insert.1 (hP hw) with rfl | h
      · exact absurd hw hqP
      · exact h
    by_cases hBP : (B \ P).Nonempty
    · obtain ⟨p', hp', q', hq', h⟩ := hB P hPsub hPne hBP
      exact ⟨p', hp', q', mem_sdiff.2 ⟨mem_insert_of_mem (mem_sdiff.1 hq').1, (mem_sdiff.1 hq').2⟩, h⟩
    · have hBsub : B ⊆ P := fun w hw => by
        by_contra h; exact hBP ⟨w, mem_sdiff.2 ⟨hw, h⟩⟩
      exact ⟨p, hBsub hp, q, mem_sdiff.2 ⟨mem_insert_self _ _, hqP⟩, hpq⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- an anticonnected set contains anticonnected subsets of every size `1 ≤ k ≤ |D|` -/
lemma exists_anticonn_subset {D : Finset V} (hD : AntiConnected G D) :
    ∀ k : ℕ, 1 ≤ k → k ≤ D.card → ∃ B ⊆ D, B.card = k ∧ AntiConnected G B
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, hk => by
    obtain ⟨v, hv⟩ := card_pos.1 (by omega : 0 < D.card)
    exact ⟨{v}, singleton_subset_iff.2 hv, card_singleton v, anticonn_singleton v⟩
  | k + 2, _, hk => by
    obtain ⟨B, hBD, hBc, hB⟩ := exists_anticonn_subset hD (k + 1) (by omega) (by omega)
    have hBne : B.Nonempty := card_pos.1 (by omega)
    have hrest : (D \ B).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset hBD]; omega
    obtain ⟨p, hp, q, hq, hpq⟩ := hD B hBD hBne hrest
    obtain ⟨hqD, hqB⟩ := mem_sdiff.1 hq
    exact ⟨insert q B, insert_subset hqD hBD, by rw [card_insert_of_notMem hqB, hBc],
      anticonn_insert hB hp hqB hpq⟩

omit [Fintype V] [DecidableEq V] in
lemma edgesBetween_mono {A A' B B' : Finset V} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    edgesBetween G A' B' ≤ edgesBetween G A B := by
  unfold edgesBetween
  exact card_le_card (filter_subset_filter _ (product_subset_product hA hB))

omit [Fintype V] in
/-- the edges from `Y` into pairwise disjoint parts of `A` add up to at most `e(Y, A)` -/
lemma sum_edges_parts {n : ℕ} (Y A : Finset V) (P : Fin n → Finset V) (hP : ∀ k, P k ⊆ A)
    (hd : ∀ k k', k ≠ k' → Disjoint (P k) (P k')) :
    ∑ k, edgesBetween G Y (P k) ≤ edgesBetween G Y A := by
  have h1 : ∑ k, edgesBetween G Y (P k) = edgesBetween G Y (univ.biUnion P) := by
    rw [edgesBetween_eq_sum, sum_biUnion (fun k _ k' _ h => hd k k' h)]
    exact sum_congr rfl fun k _ => edgesBetween_eq_sum G Y (P k)
  rw [h1]
  exact edgesBetween_mono subset_rfl (biUnion_subset.2 fun k _ => hP k)

omit [Fintype V] in
lemma sum_edges_parts' {n : ℕ} (Y A : Finset V) (P : Fin n → Finset V) (hP : ∀ k, P k ⊆ A)
    (hd : ∀ k k', k ≠ k' → Disjoint (P k) (P k')) :
    ∑ k, edgesBetween G (P k) Y ≤ edgesBetween G A Y := by
  have := sum_edges_parts (G := G) Y A P hP hd
  simp only [edgesBetween_comm (G := G) _ Y]
  simpa only [edgesBetween_comm (G := G) Y] using this

omit [Fintype V] [DecidableEq V] in
/-- Markov: the vertices of `X` with at least `t` neighbours in `Y` number at most `e(X, Y)/t` -/
lemma card_high_deg (X Y : Finset V) (t : ℝ) :
    t * ((X.filter (fun w => t ≤ ((nbrs G w Y).card : ℝ))).card : ℝ) ≤ edgesBetween G X Y := by
  rw [edgesBetween_eq_sum_left]
  push_cast
  calc t * ((X.filter (fun w => t ≤ ((nbrs G w Y).card : ℝ))).card : ℝ)
      = ∑ w ∈ X.filter (fun w => t ≤ ((nbrs G w Y).card : ℝ)), t := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ w ∈ X.filter (fun w => t ≤ ((nbrs G w Y).card : ℝ)), ((nbrs G w Y).card : ℝ) :=
        sum_le_sum fun w hw => (mem_filter.1 hw).2
    _ ≤ ∑ w ∈ X, ((nbrs G w Y).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)

omit [Fintype V] [DecidableEq V] in
lemma edges_le_of_sparseTo {x : ℝ} {B A : Finset V} (h : SparseTo G x B A) :
    (edgesBetween G B A : ℝ) ≤ B.card * (x * A.card) := by
  rw [edgesBetween_eq_sum_left]
  push_cast
  calc ∑ w ∈ B, ((nbrs G w A).card : ℝ) ≤ ∑ w ∈ B, x * A.card := sum_le_sum fun w hw => h w hw
    _ = B.card * (x * A.card) := by rw [sum_const, nsmul_eq_mul]

end EHP6
