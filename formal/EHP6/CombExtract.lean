import EHP6.Pair
import EHP6.Imported
import EHP6.NSSL42
import EHP6.CombNum

/-!
# Lemma 3.1, part A: extracting a comb (NSS VII Claim 5.2.1, relative to a vertex set `S`)
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
lemma sum_nbrs_comm (A B : Finset V) :
    ∑ a ∈ A, ((nbrs G a B).card : ℝ) = ∑ b ∈ B, ((nbrs G b A).card : ℝ) := by
  have h1 := edgesBetween_eq_sum G B A
  have h2 := edgesBetween_eq_sum G A B
  have h3 : edgesBetween G A B = edgesBetween G B A := by
    unfold edgesBetween
    rw [← card_map ⟨Prod.swap, Prod.swap_injective⟩]
    congr 1; ext ⟨p, q⟩
    simp only [mem_map, mem_filter, mem_product, Function.Embedding.coeFn_mk, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl, rfl⟩; exact ⟨⟨hb, ha⟩, G.adj_symm hab⟩
    · rintro ⟨⟨hp, hq⟩, hpq⟩; exact ⟨q, p, ⟨⟨hq, hp⟩, G.adj_symm hpq⟩, rfl, rfl⟩
  have e1 : ∀ b, (A.filter (fun a => G.Adj a b)) = nbrs G b A := fun b => by
    unfold nbrs; exact filter_congr fun a _ => ⟨fun h => G.adj_symm h, fun h => G.adj_symm h⟩
  have e2 : ∀ a, (B.filter (fun b => G.Adj b a)) = nbrs G a B := fun a => by
    unfold nbrs; exact filter_congr fun b _ => ⟨fun h => G.adj_symm h, fun h => G.adj_symm h⟩
  simp only [e1] at h2; simp only [e2] at h1
  have : (∑ a ∈ A, (nbrs G a B).card : ℕ) = ∑ b ∈ B, (nbrs G b A).card := by
    rw [← h1, ← h2, h3]
  exact_mod_cast this

/-- the output of the comb extraction -/
structure CombData (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (x y : ℝ) where
  v : V
  hv : v ∈ S
  ℓ : ℕ
  a : Fin ℓ → V
  C : Fin ℓ → Finset V
  hℓy : 1 / y ≤ (ℓ : ℝ)
  hℓx : (ℓ : ℝ) ≤ 1 / x ^ 2
  ha : ∀ i, a i ∈ S ∧ ¬ G.Adj v (a i)
  hC : ∀ i, C i ⊆ nbrs G v S
  hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j)
  hsize : ∀ i, y ^ 4 * S.card / (ℓ : ℝ) ^ 2 ≤ (C i).card
  hcomp : ∀ i, ∀ c ∈ C i, G.Adj (a i) c
  hanti : ∀ i j, i ≠ j → ∀ c ∈ C j, ¬ G.Adj (a i) c

/-- outcome (iii) of Lemma 3.1 -/
def Outcome3 (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (x y : ℝ) : Prop :=
  ∃ X ⊆ S, ∃ Y ⊆ S, Disjoint X Y ∧ y ^ 4 * S.card ≤ X.card ∧ (1 - 4 * y) * S.card ≤ Y.card ∧
    SparseTo G x Y X

omit [Fintype V] in
lemma card_nbrs_le (v : V) (A : Finset V) : (nbrs G v A).card ≤ A.card := card_filter_le _ _

omit [Fintype V] in
lemma nbrs_mono {v : V} {A B : Finset V} (h : A ⊆ B) : nbrs G v A ⊆ nbrs G v B :=
  fun w hw => mem_filter.2 ⟨h (mem_filter.1 hw).1, (mem_filter.1 hw).2⟩

/-- **Comb extraction** (NSS VII Claim 5.2.1): if `G[S]` is `y³`-sparse, not `2y⁴`-sparse and
outcome (iii) fails, a comb with at least `1/y` teeth sits inside the neighbourhood of a vertex. -/
theorem comb_extract (hcomb : NssComb) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2 ^ 64) (S : Finset V)
    (hsp : Sparse G (y ^ 3) S) (hS : 1 / x ^ 18 ≤ (S.card : ℝ)) :
    Sparse G (2 * y ^ 4) S ∨ Outcome3 G S x y ∨ Nonempty (CombData G S x y) := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hy1 : y ≤ 1 / 40 := hy.trans (by norm_num)
  have hx1 : x ≤ 1 / 2 := (hxy.trans hy).trans (by norm_num)
  -- |S| ≥ 2/y
  have hSy : 2 / y ≤ (S.card : ℝ) := ce_Sy hx hxy hy hS
  by_cases hsp2 : Sparse G (2 * y ^ 4) S
  · exact Or.inl hsp2
  right
  unfold Sparse at hsp2; push Not at hsp2
  obtain ⟨v, hvS, hvN⟩ := hsp2
  set N := nbrs G v S with hNdef
  have hNS : N ⊆ S := filter_subset _ _
  have hNle : (N.card : ℝ) ≤ y ^ 3 * S.card := hsp v hvS
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hSy
  have hNpos : (0 : ℝ) < N.card := lt_of_le_of_lt (by positivity) hvN
  -- A'
  set A' := (S \ (N ∪ {v})).filter (fun w => y ^ 2 * N.card / 2 ≤ ((nbrs G w N).card : ℝ))
  have hA'le : (A'.card : ℝ) ≤ 2 * y * S.card := by
    have h1 : (A'.card : ℝ) * (y ^ 2 * N.card / 2) ≤ ∑ w ∈ A', ((nbrs G w N).card : ℝ) := by
      rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum fun w hw => (mem_filter.1 hw).2
    have h2 : ∑ u ∈ N, ((nbrs G u A').card : ℝ) ≤ N.card * (y ^ 3 * S.card) := by
      rw [← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum fun u hu => le_trans ?_ (hsp u (hNS hu))
      exact_mod_cast card_le_card (nbrs_mono ((filter_subset _ _).trans sdiff_subset))
    rw [sum_nbrs_comm] at h1
    have h3 : (A'.card : ℝ) * (y ^ 2 * N.card / 2) ≤ N.card * (y ^ 3 * S.card) := h1.trans h2
    exact ce_A'le hNpos hy0 h3
  -- A
  set A := S \ (N ∪ A' ∪ {v}) with hAdef
  have hAS : A ⊆ S := sdiff_subset
  have hAN : Disjoint A N := by
    rw [disjoint_left]; intro a ha haN
    exact (mem_sdiff.1 ha).2 (mem_union_left _ (mem_union_left _ haN))
  have hAcard : (1 - 3 * y) * S.card ≤ (A.card : ℝ) := by
    have h1 : (S.card : ℝ) ≤ A.card + (N ∪ A' ∪ {v}).card := by
      have := card_le_card_sdiff_add_card (s := S) (t := N ∪ A' ∪ {v}); exact_mod_cast this
    have h2 : ((N ∪ A' ∪ {v}).card : ℝ) ≤ N.card + A'.card + 1 := by
      have := card_union_le (N ∪ A') {v}
      have := card_union_le N A'
      have : ((N ∪ A' ∪ {v}).card : ℕ) ≤ N.card + A'.card + 1 := by
        simp only [card_singleton] at *; omega
      exact_mod_cast this
    exact ce_Acard (by linarith) hNle hA'le hSy hy0 hy1
  -- every vertex of A has few neighbours in N
  have hAfew : ∀ a ∈ A, ((nbrs G a N).card : ℝ) < y ^ 2 * N.card / 2 := by
    intro a ha
    obtain ⟨haS, haU⟩ := mem_sdiff.1 ha
    by_contra hc; push Not at hc
    exact haU (mem_union_left _ (mem_union_right _ (mem_filter.2
      ⟨mem_sdiff.2 ⟨haS, fun h => haU (by
        rcases mem_union.1 h with h' | h'
        · exact mem_union_left _ (mem_union_left _ h')
        · exact mem_union_right _ h')⟩, hc⟩)))
  -- N', B
  set N' := N.filter (fun w => ((nbrs G w A).card : ℝ) ≤ x ^ 2 * A.card) with hN'def
  set B := N \ N' with hBdef
  by_cases hN'big : y ^ 4 * S.card ≤ (N'.card : ℝ)
  · -- outcome (iii)
    left
    obtain ⟨Yc, hYcdef⟩ : ∃ Yc, Yc = A.filter (fun a => ((nbrs G a N').card : ℝ) ≤ x * N'.card) :=
      ⟨_, rfl⟩
    have hN'pos : (0 : ℝ) < N'.card := lt_of_lt_of_le (mul_pos (pow_pos hy0 4) hSpos) hN'big
    have hbad : ((A.filter (fun a => ¬ ((nbrs G a N').card : ℝ) ≤ x * N'.card)).card : ℝ) ≤
        x * A.card := by
      set Bad := A.filter (fun a => ¬ ((nbrs G a N').card : ℝ) ≤ x * N'.card)
      have h1 : (Bad.card : ℝ) * (x * N'.card) ≤ ∑ a ∈ Bad, ((nbrs G a N').card : ℝ) := by
        rw [← nsmul_eq_mul, ← sum_const]
        exact sum_le_sum fun a ha => le_of_lt (not_le.1 (mem_filter.1 ha).2)
      have h2 : ∑ a ∈ Bad, ((nbrs G a N').card : ℝ) ≤ ∑ a ∈ A, ((nbrs G a N').card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
      have h3 : ∑ w ∈ N', ((nbrs G w A).card : ℝ) ≤ N'.card * (x ^ 2 * A.card) := by
        rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum fun w hw => (mem_filter.1 hw).2
      rw [sum_nbrs_comm (G := G) A N'] at h2
      have h4 : (Bad.card : ℝ) * (x * N'.card) ≤ N'.card * (x ^ 2 * A.card) := h1.trans (h2.trans h3)
      exact ce_bad hN'pos hx h4
    have hYc : (1 - x) * A.card ≤ (Yc.card : ℝ) := by
      have := card_filter_add_card_filter_not (s := A)
        (fun a => ((nbrs G a N').card : ℝ) ≤ x * N'.card)
      rw [← hYcdef] at this
      have h' : (Yc.card : ℝ) + ((A.filter (fun a => ¬ ((nbrs G a N').card : ℝ) ≤
          x * N'.card)).card : ℝ) = A.card := by exact_mod_cast this
      linarith
    have hYcA : Yc ⊆ A := by rw [hYcdef]; exact filter_subset _ _
    refine ⟨N', (filter_subset _ _).trans hNS, Yc, hYcA.trans hAS, ?_, hN'big, ?_,
      fun a ha => by rw [hYcdef] at ha; exact (mem_filter.1 ha).2⟩
    · rw [disjoint_left]; intro w hw hwY
      exact disjoint_left.1 hAN (hYcA hwY) ((filter_subset _ _) hw)
    · exact ce_final hYc hAcard hxy hx hSpos.le hy1
  push Not at hN'big
  right
  -- B is large
  have hBcard : (N.card : ℝ) = B.card + N'.card := by
    have := card_sdiff_add_card_eq_card (filter_subset (fun w => ((nbrs G w A).card : ℝ) ≤
      x ^ 2 * A.card) N)
    exact_mod_cast this.symm
  have hBbig : y ^ 4 * S.card < (B.card : ℝ) := by linarith
  have hBhalf : (N.card : ℝ) / 2 ≤ B.card := by linarith
  have hBpos : (0 : ℝ) < B.card :=
    lt_of_le_of_lt (mul_nonneg (pow_nonneg hy0.le 4) (Nat.cast_nonneg _)) hBbig
  have hBN : B ⊆ N := sdiff_subset
  have hAB : Disjoint A B := disjoint_of_subset_right hBN hAN
  have hAB' : ∀ a ∈ A, ((nbrs G a B).card : ℝ) ≤ y ^ 2 * B.card := by
    intro a ha
    have h1 : ((nbrs G a B).card : ℝ) ≤ (nbrs G a N).card := by
      exact_mod_cast card_le_card (nbrs_mono hBN)
    exact ce_AB' h1 (hAfew a ha) hBhalf hy0.le
  have hBA : ∀ b ∈ B, x ^ 2 * A.card ≤ ((nbrs G b A).card : ℝ) := by
    intro b hb
    obtain ⟨hbN, hbN'⟩ := mem_sdiff.1 hb
    by_contra hc; push Not at hc
    exact hbN' (mem_filter.2 ⟨hbN, hc.le⟩)
  -- NSS VII Lemma 4.2 (paper Lemma 0.4), then the comb lemma NSS VII Lemma 4.3
  have hAne : A.Nonempty := by
    rw [← card_pos]
    have h3y : (0 : ℝ) < 1 - 3 * y := by linarith [show (3 : ℝ) * (1 / 2 ^ 64) < 1 by norm_num]
    have : (0 : ℝ) < A.card := lt_of_lt_of_le (mul_pos h3y hSpos) hAcard
    exact_mod_cast this
  obtain ⟨S', hS'A, hS'card, hcover⟩ := nss_L42_proof A B (x ^ 2) (by positivity) (by
    have : x ^ 2 ≤ x := by nlinarith
    linarith) hAne hBA
  have hcov' : (B.filter (fun b => ∃ a ∈ S', G.Adj a b)) =
      (B.filter (fun b => ∃ a ∈ S', G.Adj b a)) :=
    filter_congr fun b _ => ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, G.adj_symm h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, G.adj_symm h⟩⟩
  have hS'ne : S'.Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    subst hc
    simp at hcover; linarith
  have hBne : B.Nonempty := card_pos.1 (by exact_mod_cast hBpos)
  have hsqrt : Real.sqrt (B.card * (y ^ 2 * B.card)) = y * B.card := by
    rw [show (B.card : ℝ) * (y ^ 2 * B.card) = (y * B.card) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg hy0.le (Nat.cast_nonneg _))
  rcases hcomb V G S' B (y ^ 2 * B.card) (disjoint_of_subset_left hS'A hAB) hS'ne hBne
      (mul_pos (pow_pos hy0 2) hBpos) (fun a ha => hAB' a (hS'A ha)) with h | ⟨ℓ, hℓ1, a, C, hainj, haS', hCB,
      hCdisj, hCsize, hcomp, hanti⟩
  · exfalso
    rw [hsqrt, hcov'] at h
    have : (B.card : ℝ) / 2 ≤ 20 * (y * B.card) := hcover.trans h
    have hy80 : y ≤ 1 / 80 := hy.trans (by norm_num)
    have : 20 * (y * B.card) ≤ 20 * ((1 / 80) * B.card) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy80 hBpos.le) (by norm_num)
    linarith
  refine ⟨⟨v, hvS, ℓ, a, C, ?_, ?_, fun i => ⟨hAS (hS'A (haS' i)), fun h => ?_⟩,
    fun i => (hCB i).trans hBN, hCdisj, fun i => ?_, hcomp, hanti⟩⟩
  · -- ℓ ≥ 1/y
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
    have i0 : Fin ℓ := ⟨0, hℓ1⟩
    have hCa : C i0 ⊆ nbrs G (a i0) B := fun c hc => mem_filter.2 ⟨hCB i0 hc, hcomp i0 c hc⟩
    have h1 : (B.card : ℝ) / ℓ ^ 2 ≤ y ^ 2 * B.card :=
      (hCsize i0).trans ((by exact_mod_cast card_le_card hCa : ((C i0).card : ℝ) ≤ _).trans
        (hAB' _ (hS'A (haS' i0))))
    exact ce_ell hBpos (by exact_mod_cast hℓ1) hy0 h1
  · -- ℓ ≤ 1/x²
    have : (univ.image a).card = ℓ := by rw [card_image_of_injective _ hainj, card_univ, Fintype.card_fin]
    have hsub : univ.image a ⊆ S' := fun w hw => by
      obtain ⟨i, -, rfl⟩ := mem_image.1 hw; exact haS' i
    have := card_le_card hsub
    have : (ℓ : ℝ) ≤ S'.card := by exact_mod_cast (show ℓ ≤ S'.card by omega)
    linarith
  · -- v ≁ a i
    exact disjoint_left.1 hAN (hS'A (haS' i)) (mem_filter.2 ⟨hAS (hS'A (haS' i)), h⟩)
  · -- sizes
    have hℓpos : (0 : ℝ) < (ℓ : ℝ) ^ 2 := by
      have : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
      positivity
    exact le_trans (div_le_div_of_nonneg_right hBbig.le hℓpos.le) (hCsize i)

end EHP6
