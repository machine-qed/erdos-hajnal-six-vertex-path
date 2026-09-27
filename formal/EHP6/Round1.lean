import EHP6.Comb
import EHP6.Pair
import EHP6.Imported
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Section 4: iterative sparsification, round one (Lemmas 4.1–4.3)
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma exp_five_lt : Real.exp 5 < 256 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp 1 ^ 5 < 3 ^ 5 :=
    pow_lt_pow_left₀ (by norm_num at h1 ⊢; linarith) (Real.exp_pos 1).le (by norm_num)
  rw [h2]; linarith [show (3 : ℝ) ^ 5 = 243 by norm_num]

/-- `(1 − t)^n ≥ 4⁻⁴` when `t ≤ 1/5` and `nt ≤ 4` (used for `|B_n| ≥ (1−4y)^n|G| ≥ 4⁻⁴|G|`) -/
lemma pow_one_sub_ge {t : ℝ} {n : ℕ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 5) (hn : n * t ≤ 4) :
    1 / 256 ≤ (1 - t) ^ n := by
  have h1t : 0 < 1 - t := by linarith
  have hu : 1 / (1 - t) ≤ Real.exp (t / (1 - t)) := by
    have := Real.add_one_le_exp (t / (1 - t))
    have e : t / (1 - t) + 1 = 1 / (1 - t) := by rw [div_add_one h1t.ne']; congr 1; ring
    linarith
  have hpow : (1 / (1 - t)) ^ n ≤ Real.exp (t / (1 - t)) ^ n :=
    pow_le_pow_left₀ (by positivity) hu n
  rw [← Real.exp_nat_mul] at hpow
  have hexp : (n : ℝ) * (t / (1 - t)) ≤ 5 := by
    rw [mul_div_assoc', div_le_iff₀ h1t]; linarith
  have h5 : (1 / (1 - t)) ^ n < 256 :=
    hpow.trans_lt ((Real.exp_le_exp.2 hexp).trans_lt exp_five_lt)
  rw [one_div_pow, div_lt_iff₀ (pow_pos h1t n)] at h5
  linarith

omit [Fintype V] in
lemma sparseTo_mono_left {x : ℝ} {B B' A : Finset V} (h : SparseTo G x B A) (hB : B' ⊆ B) :
    SparseTo G x B' A := fun v hv => h v (hB hv)

omit [Fintype V] in
lemma edgesBetween_comm (A B : Finset V) : edgesBetween G A B = edgesBetween G B A := by
  unfold edgesBetween
  refine card_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
  · intro p hp
    rw [Finset.mem_coe, mem_filter, mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩
  · intro p hp
    rw [Finset.mem_coe, mem_filter, mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩

omit [Fintype V] in
/-- `B` `x`-sparse to `A` implies `(A, B)` weakly `x`-sparse -/
lemma weaklySparse_of_sparseTo {x : ℝ} {A B : Finset V} (h : SparseTo G x B A) :
    WeaklySparse G x A B := by
  unfold WeaklySparse
  rw [edgesBetween_eq_sum]
  push_cast
  calc ∑ b ∈ B, ((A.filter (fun a => G.Adj a b)).card : ℝ) ≤ ∑ b ∈ B, x * A.card :=
        sum_le_sum fun b hb => by
          have e : A.filter (fun a => G.Adj a b) = nbrs G b A :=
            filter_congr fun a _ => ⟨fun h => G.adj_symm h, fun h => G.adj_symm h⟩
          rw [e]; exact h b hb
    _ = x * A.card * B.card := by rw [sum_const, nsmul_eq_mul]; ring

omit [Fintype V] in
lemma weaklySparse_symm {x : ℝ} {A B : Finset V} (h : WeaklySparse G x A B) :
    WeaklySparse G x B A := by
  unfold WeaklySparse at *
  rw [edgesBetween_comm]; linarith [show x * A.card * B.card = x * B.card * A.card by ring]

omit [Fintype V] in
/-- a sparse blockade is semisparse -/
lemma semisparse_of_sparse {S : Finset V} {k w x : ℝ} (β : Blockade S k w) (h : β.IsSparse G x) :
    β.IsSemisparse G x := fun i j hij => by
  right
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact weaklySparse_of_sparseTo (h i j hlt)
  · exact weaklySparse_symm (weaklySparse_of_sparseTo (h j i hlt))

omit [Fintype V] in
/-- sparseness passes to a large subset -/
lemma sparse_sub {a b : ℝ} {S T : Finset V} (h : Sparse G a S) (hT : T ⊆ S)
    (hab : a * S.card ≤ b * T.card) : Sparse G b T := fun v hv => by
  have h1 : (nbrs G v T).card ≤ (nbrs G v S).card := card_le_card (filter_subset_filter _ hT)
  have h2 := h v (hT hv)
  have h1' : ((nbrs G v T).card : ℝ) ≤ (nbrs G v S).card := by exact_mod_cast h1
  linarith

variable (G) in
/-- an `x`-sparse chain `(B₀, …, B_n)` (proof of Lemma 4.1): blocks inside `S`, pairwise disjoint,
later blocks `x`-sparse to earlier ones, the first `n` of size `≥ w`, the last of size `≥ q^n|S|` -/
def SChain (S : Finset V) (x w q : ℝ) (n : ℕ) : Prop :=
  ∃ B : ℕ → Finset V, (∀ i ≤ n, B i ⊆ S) ∧ (∀ i ≤ n, ∀ j ≤ n, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i < j → j ≤ n → SparseTo G x (B j) (B i)) ∧ (∀ i < n, w ≤ ((B i).card : ℝ)) ∧
    q ^ n * S.card ≤ ((B n).card : ℝ)

omit [Fintype V] in
lemma schain_zero (S : Finset V) (x w q : ℝ) : SChain G S x w q 0 :=
  ⟨fun _ => S, fun _ _ => subset_refl _, fun i hi j hj h => absurd (by omega : i = j) h,
    fun i j h h' => absurd h (by omega), fun i h => absurd h (Nat.not_lt_zero i), by simp⟩

omit [Fintype V] in
lemma schain_bound {S : Finset V} {x w q : ℝ} {n : ℕ} (hw : 0 < w) (h : SChain G S x w q n) :
    n ≤ S.card := by
  obtain ⟨B, hsub, hdisj, -, hwid, -⟩ := h
  have hpos : ∀ i ∈ range n, 1 ≤ (B i).card := fun i hi => by
    have h1 : (0 : ℝ) < (B i).card := hw.trans_le (hwid i (mem_range.1 hi))
    have h2 : 0 < (B i).card := by exact_mod_cast h1
    omega
  have hcard : ((range n).biUnion B).card = ∑ i ∈ range n, (B i).card :=
    card_biUnion fun i hi j hj hij =>
      hdisj i (by have := mem_range.1 hi; omega) j (by have := mem_range.1 hj; omega) hij
  have hsubS : (range n).biUnion B ⊆ S :=
    biUnion_subset.2 fun i hi => hsub i (by have := mem_range.1 hi; omega)
  have h1 : n ≤ ∑ i ∈ range n, (B i).card := by
    calc n = ∑ i ∈ range n, 1 := by simp
      _ ≤ _ := sum_le_sum hpos
  have := card_le_card hsubS
  omega

omit [Fintype V] in
lemma schain_extend {S : Finset V} {x w q : ℝ} {n : ℕ} (hq : 0 ≤ q) {B : ℕ → Finset V}
    (hsub : ∀ i ≤ n, B i ⊆ S) (hdisj : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → Disjoint (B i) (B j))
    (hsp : ∀ i j, i < j → j ≤ n → SparseTo G x (B j) (B i)) (hwid : ∀ i < n, w ≤ ((B i).card : ℝ))
    (hlast : q ^ n * S.card ≤ ((B n).card : ℝ))
    {X Y : Finset V} (hX : X ⊆ B n) (hY : Y ⊆ B n) (hXY : Disjoint X Y) (hXw : w ≤ X.card)
    (hYq : q * (B n).card ≤ Y.card) (hYX : SparseTo G x Y X) : SChain G S x w q (n + 1) := by
  obtain ⟨B', hB'⟩ : ∃ B' : ℕ → Finset V, B' = fun i => if i < n then B i else if i = n then X else Y :=
    ⟨_, rfl⟩
  have hlt : ∀ i < n, B' i = B i := fun i hi => by rw [hB']; simp [hi]
  have hn : B' n = X := by rw [hB']; simp
  have hn1 : B' (n + 1) = Y := by rw [hB']; simp
  have hpar : ∀ i ≤ n + 1, n ≤ i → B' i ⊆ B n := fun i hi hni => by
    rcases (by omega : i = n ∨ i = n + 1) with rfl | rfl
    · rw [hn]; exact hX
    · rw [hn1]; exact hY
  refine ⟨B', fun i hi => ?_, fun i hi j hj hij => ?_, fun i j hij hj => ?_, fun i hi => ?_, ?_⟩
  · rcases lt_or_ge i n with h | h
    · rw [hlt i h]; exact hsub i h.le
    · exact (hpar i hi h).trans (hsub n le_rfl)
  · rcases lt_or_ge i n with h | h <;> rcases lt_or_ge j n with h' | h'
    · rw [hlt i h, hlt j h']; exact hdisj i h.le j h'.le hij
    · rw [hlt i h]
      exact disjoint_of_subset_right (hpar j hj h') (hdisj i h.le n le_rfl (by omega))
    · rw [hlt j h']
      exact disjoint_of_subset_left (hpar i hi h) (hdisj n le_rfl j h'.le (by omega))
    · rcases (by omega : (i = n ∧ j = n + 1) ∨ (i = n + 1 ∧ j = n)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hn, hn1]; exact hXY
      · rw [hn, hn1]; exact hXY.symm
  · rcases lt_or_ge j n with h' | h'
    · rw [hlt i (by omega), hlt j h']; exact hsp i j hij h'.le
    · rcases lt_or_ge i n with h | h
      · rw [hlt i h]; exact sparseTo_mono_left (hsp i n h le_rfl) (hpar j hj h')
      · rcases (by omega : i = n ∧ j = n + 1) with ⟨rfl, rfl⟩
        rw [hn, hn1]; exact hYX
  · rcases lt_or_ge i n with h | h
    · rw [hlt i h]; exact hwid i h
    · rcases (by omega : i = n) with rfl
      rw [hn]; exact hXw
  · rw [hn1, pow_succ]
    calc q ^ n * q * S.card = q * (q ^ n * S.card) := by ring
      _ ≤ q * (B n).card := mul_le_mul_of_nonneg_left hlast hq
      _ ≤ Y.card := hYq

lemma nat_ge_16 {K : ℕ} {y : ℝ} (hy : y ≤ 1 / 2 ^ 64) (hK : 1 ≤ y * (K : ℝ) ^ 16) :
    (16 : ℝ) ≤ K := by
  by_contra h
  push Not at h
  have h1 : (K : ℝ) ^ 16 < 16 ^ 16 := pow_lt_pow_left₀ h (Nat.cast_nonneg _) (by norm_num)
  have h2 : (0 : ℝ) ≤ (K : ℝ) ^ 16 := by positivity
  have hy0 : 0 < y := by
    by_contra hy0; push Not at hy0; nlinarith
  have : y * (K : ℝ) ^ 16 < 1 := by
    calc y * (K : ℝ) ^ 16 ≤ 1 / 2 ^ 64 * (K : ℝ) ^ 16 := mul_le_mul_of_nonneg_right hy h2
      _ < 1 / 2 ^ 64 * 16 ^ 16 := by nlinarith
      _ = 1 := by norm_num
  linarith

lemma r1_width {s b K : ℝ} (hK : 16 ≤ K) (hb : s / 2 ^ 8 ≤ b) (hs : 0 ≤ s) :
    s / K ^ 102 ≤ b / K ^ 100 := by
  have hK0 : 0 < K := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hK2 : 256 ≤ K ^ 2 := by nlinarith
  have e : b * K ^ 102 = (b * K ^ 2) * K ^ 100 := by ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hb0 : s ≤ 2 ^ 8 * b := by linarith [show s / 2 ^ 8 * 2 ^ 8 = s by ring]
  have hbs : 0 ≤ b := by linarith
  nlinarith

/-- **Lemma 4.1** (NSS VII Lemma 5.3 with Lemma 3.1). Let `0 < x ≤ y ≤ 2⁻⁶⁴`, `c = 2⁻⁸`, and let
`G[S]` be `cy³`-sparse and P̄6-free with `|S| ≥ 2⁸x⁻¹⁸`. Then (a) some `T ⊆ S` with `|T| ≥ c|S|` has
`G[T]` `2y⁴`-sparse; or (b) there is an `x`-semisparse `(K, |S|/K¹⁰²)`-blockade with
`K ∈ [y^{-1/16}, 1/x]`; or (c) there is an `x`-sparse `(y⁻¹, y⁶|S|)`-blockade. -/
theorem round1_step (hcomb : NssComb) (hfree : Free G P6ᶜ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ 1 / 2 ^ 64) (S : Finset V) (hsp : Sparse G (y ^ 3 / 2 ^ 8) S)
    (hS : 2 ^ 8 / x ^ 18 ≤ (S.card : ℝ)) :
    (∃ T ⊆ S, (S.card : ℝ) / 2 ^ 8 ≤ T.card ∧ Sparse G (2 * y ^ 4) T) ∨
    Outcome2 G S x y 102 ∨
    (∃ β : Blockade S (1 / y) (y ^ 6 * S.card), β.IsSparse G x) := by
  have hy0 : 0 < y := hx.trans_le hxy
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hS
  have hw : 0 < y ^ 6 * S.card := by positivity
  have hy5 : 4 * y ≤ 1 / 5 := by linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 20 by norm_num]
  have hq : 0 ≤ 1 - 4 * y := by linarith
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.findGreatest (SChain G S x (y ^ 6 * S.card) (1 - 4 * y)) S.card :=
    ⟨_, rfl⟩
  have hPn : SChain G S x (y ^ 6 * S.card) (1 - 4 * y) n := by
    rw [hn]; exact Nat.findGreatest_spec (Nat.zero_le _) (schain_zero S _ _ _)
  have hmax : ¬ SChain G S x (y ^ 6 * S.card) (1 - 4 * y) (n + 1) := fun h => by
    have hb := schain_bound hw h
    rw [hn] at h hb
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hb h
  obtain ⟨B, hsub, hdisj, hspB, hwid, hlast⟩ := hPn
  by_cases hn1 : 1 / y ≤ n
  · -- (c): the first `n` blocks
    right; right
    refine ⟨⟨n, fun i => B i, hn1, fun i => hsub i i.2.le, fun i => hwid i i.2,
      fun i j hij => hdisj i i.2.le j j.2.le (fun h => hij (Fin.ext h))⟩, fun i j hij => ?_⟩
    exact hspB i j hij j.2.le
  push Not at hn1
  have hny : (n : ℝ) * (4 * y) ≤ 4 := by
    have := (lt_div_iff₀ hy0).1 hn1
    nlinarith
  have hBn : (S.card : ℝ) / 2 ^ 8 ≤ (B n).card := by
    have := pow_one_sub_ge (by linarith) hy5 hny
    have h2 := mul_le_mul_of_nonneg_right this hSpos.le
    linarith [show (S.card : ℝ) / 2 ^ 8 = 1 / 256 * S.card by ring]
  have hBnS := hsub n le_rfl
  have hsp' : Sparse G (y ^ 3) (B n) := sparse_sub hsp hBnS (by
    have := mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ y ^ 3)
    linarith [show y ^ 3 / 2 ^ 8 * S.card = y ^ 3 * (S.card / 2 ^ 8) by ring])
  have hBbig : 1 / x ^ 18 ≤ ((B n).card : ℝ) := by
    have e : (1 : ℝ) / x ^ 18 = 2 ^ 8 / x ^ 18 / 2 ^ 8 := by ring
    rw [e]; linarith
  rcases comb_lemma hcomb hfree hx hxy hy (B n) hsp' hBbig with h | ⟨K, hK1, hK2, β, hβ⟩ |
      ⟨X, hX, Y, hY, hXY, hXs, hYs, hYX⟩
  · exact Or.inl ⟨B n, hBnS, hBn, h⟩
  · have hK16 : (16 : ℝ) ≤ K := nat_ge_16 hy hK1
    have hwid' : (S.card : ℝ) / (K : ℝ) ^ 102 ≤ ((B n).card : ℝ) / (K : ℝ) ^ 100 :=
      r1_width hK16 hBn hSpos.le
    right; left
    exact ⟨K, hK1, hK2, β.mono hBnS le_rfl hwid', fun i j hij => hβ i j hij⟩
  · exfalso
    refine hmax (schain_extend hq hsub hdisj hspB hwid hlast hX hY hXY ?_ hYs hYX)
    have hy2 : y ^ 2 ≤ 1 / 2 ^ 8 := by
      have : y ^ 2 ≤ (1 / 2 ^ 64) ^ 2 := pow_le_pow_left₀ hy0.le hy 2
      linarith [show ((1 : ℝ) / 2 ^ 64) ^ 2 ≤ 1 / 2 ^ 8 by norm_num]
    have h1 := mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ y ^ 4)
    have h2 : y ^ 6 * S.card ≤ y ^ 4 * ((S.card : ℝ) / 2 ^ 8) := by
      have := mul_le_mul_of_nonneg_left hy2 (by positivity : (0 : ℝ) ≤ y ^ 4 * S.card)
      linarith [show y ^ 4 * S.card * y ^ 2 = y ^ 6 * S.card by ring,
        show y ^ 4 * S.card * (1 / 2 ^ 8) = y ^ 4 * ((S.card : ℝ) / 2 ^ 8) by ring]
    linarith

omit [Fintype V] in
/-- `m` pairwise disjoint subsets of `F` of size exactly `s`, when `ms ≤ |F|` -/
lemma exists_equal_parts (s : ℕ) : ∀ (m : ℕ) (F : Finset V), m * s ≤ F.card →
    ∃ P : Fin m → Finset V, (∀ i, P i ⊆ F) ∧ (∀ i, (P i).card = s) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j))
  | 0, _, _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | m + 1, F, h => by
    obtain ⟨T, hTF, hTc⟩ := exists_subset_card_eq (show s ≤ F.card by nlinarith)
    obtain ⟨P, hP1, hP2, hP3⟩ := exists_equal_parts s m (F \ T) (by
      rw [card_sdiff_of_subset hTF, hTc]
      have : (m + 1) * s = m * s + s := by ring
      omega)
    refine ⟨Fin.cons T P, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simpa using hTF
      · simp only [Fin.cons_succ]; exact (hP1 i).trans sdiff_subset
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simpa using hTc
      · simp only [Fin.cons_succ]; exact hP2 i
    · have hT : ∀ k, Disjoint T (P k) := fun k =>
        disjoint_of_subset_right (hP1 k) disjoint_sdiff
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact absurd rfl hij
      · simp only [Fin.cons_zero, Fin.cons_succ]; exact hT j'
      · simp only [Fin.cons_zero, Fin.cons_succ]; exact (hT i').symm
      · simp only [Fin.cons_succ]
        exact hP3 i' j' (fun e => hij (by rw [e]))

lemma r2_small {x f s : ℝ} (hx : 0 < x) (hx0 : x < 1 / 2 ^ 64) (hS : 2 ^ 16 / x ^ 19 ≤ s)
    (hF : x / 2 ^ 8 * s ≤ f) : 4 / x ≤ f ∧ x ^ 7 * s ≤ x * f / 4 := by
  have hx1 : x ≤ 1 := by linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 by norm_num]
  have hs0 : 0 ≤ s := le_trans (by positivity) hS
  have h1 : 2 ^ 8 / x ^ 18 ≤ f := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ x / 2 ^ 8)
    have e : x / 2 ^ 8 * (2 ^ 16 / x ^ 19) = 2 ^ 8 / x ^ 18 := by field_simp <;> ring
    linarith
  have hx18 : x ^ 18 ≤ x := pow_le_of_le_one hx.le hx1 (by norm_num)
  constructor
  · calc 4 / x ≤ 4 / x ^ 18 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hx18
      _ ≤ 2 ^ 8 / x ^ 18 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ f := h1
  · have hx5 : x ^ 5 ≤ 1 / 2 ^ 10 := by
      have := pow_le_of_le_one hx.le hx1 (show (5 : ℕ) ≠ 0 by norm_num)
      linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 2 ^ 10 by norm_num]
    have h2 : x ^ 7 * s ≤ x ^ 2 * s / 2 ^ 10 := by
      have := mul_le_mul_of_nonneg_left hx5 (by positivity : (0 : ℝ) ≤ x ^ 2 * s)
      linarith [show x ^ 2 * s * x ^ 5 = x ^ 7 * s by ring,
        show x ^ 2 * s * (1 / 2 ^ 10) = x ^ 2 * s / 2 ^ 10 by ring]
    have h3 := mul_le_mul_of_nonneg_left hF hx.le
    linarith [show x * (x / 2 ^ 8 * s) = x ^ 2 * s / 2 ^ 8 by ring]

lemma r2_width {s f y K : ℝ} (hK : 0 < K) (hKy : 1 ≤ y * K ^ 16) (hf : y * s ≤ f) (hs : 0 ≤ s) :
    s / K ^ 118 ≤ f / K ^ 102 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : f * K ^ 118 = (f * K ^ 16) * K ^ 102 := by ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have := mul_le_mul_of_nonneg_left hf (by positivity : (0 : ℝ) ≤ K ^ 16)
  nlinarith

variable (G) in
/-- admissible scales in the proof of Lemma 4.2 (`y_j = y₀ c^j`, discretizing the minimum) -/
def R1Adm (S : Finset V) (x : ℝ) (j : ℕ) : Prop :=
  x / 2 ^ 8 ≤ 1 / 2 ^ 64 * (1 / 2 ^ 8) ^ j ∧ ∃ F ⊆ S,
    Sparse G ((1 / 2 ^ 64 * (1 / 2 ^ 8) ^ j) ^ 3 / 2 ^ 8) F ∧
    1 / 2 ^ 64 * (1 / 2 ^ 8) ^ j * (S.card : ℝ) ≤ F.card

/-- **Lemma 4.2** (NSS VII Lemma 5.4). Let `x ∈ (0, y₀)`, `y₀ = 2⁻⁶⁴`, and let `G[S]` be `cy₀³`-sparse and
P̄6-free with `|S| ≥ 2¹⁶x⁻¹⁹`. Then (1) there is an `x`-semisparse `(K, |S|/K¹¹⁸)`-blockade with
`K ∈ [16, 1/x]`; or (2) for some `y ∈ [x, y₀]` there is an `x`-sparse `(y⁻¹, y⁷|S|)`-blockade. -/
theorem round1 (hcomb : NssComb) (hfree : Free G P6ᶜ) {x : ℝ} (hx : 0 < x) (hx0 : x < 1 / 2 ^ 64) (S : Finset V)
    (hsp : Sparse G ((1 / 2 ^ 64) ^ 3 / 2 ^ 8) S) (hS : 2 ^ 16 / x ^ 19 ≤ (S.card : ℝ)) :
    Outcome2 G S x (1 / 2 ^ 64) 118 ∨
    ∃ y : ℝ, x ≤ y ∧ y ≤ 1 / 2 ^ 64 ∧
      ∃ β : Blockade S (1 / y) (y ^ 7 * S.card), β.IsSparse G x := by
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < x * 2 ^ 56)
    (by norm_num : (1 : ℝ) / 2 ^ 8 < 1)
  have hbound : ∀ j, R1Adm G S x j → j ≤ N := by
    intro j hj
    by_contra hjN; push Not at hjN
    have h1 : ((1 : ℝ) / 2 ^ 8) ^ j ≤ (1 / 2 ^ 8) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hjN.le
    have h2 := hj.1
    have : x / 2 ^ 8 < x / 2 ^ 8 := by
      calc x / 2 ^ 8 ≤ 1 / 2 ^ 64 * (1 / 2 ^ 8) ^ j := h2
        _ ≤ 1 / 2 ^ 64 * (1 / 2 ^ 8) ^ N := by linarith
        _ < 1 / 2 ^ 64 * (x * 2 ^ 56) := by linarith
        _ = x / 2 ^ 8 := by ring
    exact lt_irrefl _ this
  have h0 : R1Adm G S x 0 := by
    refine ⟨?_, S, subset_refl _, ?_, ?_⟩ <;> rw [pow_zero, mul_one]
    · linarith
    · exact hsp
    · exact mul_le_of_le_one_left hS0 (by norm_num)
  obtain ⟨j, hj⟩ : ∃ j, j = Nat.findGreatest (R1Adm G S x) N := ⟨_, rfl⟩
  have hQj : R1Adm G S x j := by rw [hj]; exact Nat.findGreatest_spec (Nat.zero_le _) h0
  have hQj1 : ¬ R1Adm G S x (j + 1) := fun h => by
    have hb := hbound _ h
    rw [hj] at h hb
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hb h
  obtain ⟨hxj, F, hFS, hFsp, hFcard⟩ := hQj
  have hy1 : 1 / 2 ^ 64 * ((1 : ℝ) / 2 ^ 8) ^ (j + 1) = 1 / 2 ^ 64 * (1 / 2 ^ 8) ^ j / 2 ^ 8 := by
    rw [pow_succ]; ring
  generalize hydef : 1 / 2 ^ 64 * ((1 : ℝ) / 2 ^ 8) ^ j = y at hxj hFsp hFcard hy1
  have hy0 : 0 < y := by rw [← hydef]; positivity
  have hyle : y ≤ 1 / 2 ^ 64 := by
    rw [← hydef]
    have : ((1 : ℝ) / 2 ^ 8) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  by_cases hxy : x ≤ y
  · -- Lemma 4.1 applies to `F`
    have hFbig : 2 ^ 8 / x ^ 18 ≤ (F.card : ℝ) := by
      have h1 : x * S.card ≤ F.card := by nlinarith
      have h2 := mul_le_mul_of_nonneg_left hS hx.le
      have e : x * (2 ^ 16 / x ^ 19) = 2 ^ 16 / x ^ 18 := by field_simp <;> ring
      have h3 : (2 : ℝ) ^ 8 / x ^ 18 ≤ 2 ^ 16 / x ^ 18 :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)
      linarith
    rcases round1_step hcomb hfree hx hxy hyle F hFsp hFbig with ⟨T, hTF, hTc, hTsp⟩ |
        ⟨K, hK1, hK2, β, hβ⟩ | ⟨β, hβ⟩
    · exfalso
      refine hQj1 ⟨?_, T, hTF.trans hFS, ?_, ?_⟩ <;> rw [hy1]
      · linarith
      · refine sparse_sub hTsp subset_rfl (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
        rw [show (y / 2 ^ 8) ^ 3 / 2 ^ 8 = y ^ 3 * (1 / 2 ^ 32) by ring,
          show 2 * y ^ 4 = y ^ 3 * (2 * y) by ring]
        exact mul_le_mul_of_nonneg_left
          (by linarith [show (2 : ℝ) * (1 / 2 ^ 64) ≤ 1 / 2 ^ 32 by norm_num]) (by positivity)
      · have := mul_le_mul_of_nonneg_right hFcard (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 8)
        linarith [show y / 2 ^ 8 * S.card = y * S.card * (1 / 2 ^ 8) by ring,
          show (F.card : ℝ) / 2 ^ 8 = F.card * (1 / 2 ^ 8) by ring]
    · have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) (nat_ge_16 hyle hK1)
      have hK1' : 1 ≤ 1 / 2 ^ 64 * (K : ℝ) ^ 16 :=
        hK1.trans (mul_le_mul_of_nonneg_right hyle (by positivity))
      have hwid' : (S.card : ℝ) / (K : ℝ) ^ 118 ≤ (F.card : ℝ) / (K : ℝ) ^ 102 :=
        r2_width hK0 hK1 hFcard hS0
      left
      exact ⟨K, hK1', hK2, β.mono hFS le_rfl hwid', fun i j hij => hβ i j hij⟩
    · have hwid' : y ^ 7 * S.card ≤ y ^ 6 * F.card := by
        have := mul_le_mul_of_nonneg_left hFcard (by positivity : (0 : ℝ) ≤ y ^ 6)
        linarith [show y ^ 6 * (y * S.card) = y ^ 7 * S.card by ring]
      right
      exact ⟨y, hxy, hyle, β.mono hFS le_rfl hwid', fun i j hij => hβ i j hij⟩
  · -- `y < x`: `F` is `x³`-sparse; cut it into `⌈1/x⌉` equal parts
    push Not at hxy
    have hFsp' : Sparse G (x ^ 3) F := sparse_sub hFsp subset_rfl
      (mul_le_mul_of_nonneg_right (by
        have := pow_le_pow_left₀ hy0.le hxy.le 3
        have : 0 ≤ y ^ 3 := by positivity
        linarith) (Nat.cast_nonneg _))
    have hFc : x / 2 ^ 8 * S.card ≤ F.card :=
      (mul_le_mul_of_nonneg_right hxj hS0).trans hFcard
    obtain ⟨hF4, hwidth⟩ := r2_small hx hx0 hS hFc
    have hx1 : x ≤ 1 / 4 := by linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 4 by norm_num]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈1 / x⌉₊ := ⟨_, rfl⟩
    have hm1 : 1 / x ≤ m := by rw [hm]; exact Nat.le_ceil _
    have hxinv : 1 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
    have hm2 : (m : ℝ) ≤ 2 / x := by
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / x)
      rw [← hm] at this
      linarith [show 2 / x = 1 / x + 1 / x by ring]
    have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) (hxinv.trans hm1)
    have hz : x * F.card / 2 ≤ (F.card : ℝ) / m := by
      rw [le_div_iff₀ hmpos]
      have := mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ x * F.card / 2)
      have e : x * F.card / 2 * (2 / x) = F.card := by field_simp
      linarith
    have hz1 : 1 ≤ (F.card : ℝ) / m := by
      have : 2 ≤ x * F.card / 2 := by
        have := mul_le_mul_of_nonneg_left hF4 hx.le
        rw [show x * (4 / x) = 4 by field_simp] at this
        linarith
      linarith
    obtain ⟨sz, hsz⟩ : ∃ sz : ℕ, sz = ⌊(F.card : ℝ) / m⌋₊ := ⟨_, rfl⟩
    have hsz1 : x * F.card / 4 ≤ sz := by
      have := floor_half hz1
      rw [← hsz] at this
      linarith
    have hsz2 : m * sz ≤ F.card := by
      have h1 : (sz : ℝ) ≤ F.card / m := by rw [hsz]; exact Nat.floor_le (by positivity)
      have h2 : (m : ℝ) * sz ≤ F.card := by
        have := mul_le_mul_of_nonneg_left h1 hmpos.le
        rwa [mul_div_cancel₀ _ hmpos.ne'] at this
      exact_mod_cast h2
    obtain ⟨P, hP1, hP2, hP3⟩ := exists_equal_parts sz m F hsz2
    right
    refine ⟨x, le_rfl, hx0.le, ⟨m, P, hm1, fun i => (hP1 i).trans hFS, fun i => ?_, hP3⟩,
      fun i j hij => ?_⟩
    · rw [hP2 i]; linarith
    · intro v hv
      have h1 : (nbrs G v (P i)).card ≤ (nbrs G v F).card :=
        card_le_card (filter_subset_filter _ (hP1 i))
      have h1' : ((nbrs G v (P i)).card : ℝ) ≤ (nbrs G v F).card := by exact_mod_cast h1
      have h2 := hFsp' v (hP1 j hv)
      have h3 : x ^ 3 * F.card ≤ x * (x * F.card / 4) := by
        have := mul_le_mul_of_nonneg_right hx1 (by positivity : (0 : ℝ) ≤ x ^ 2 * F.card)
        linarith [show x * (x ^ 2 * (F.card : ℝ)) = x ^ 3 * F.card by ring,
          show 1 / 4 * (x ^ 2 * (F.card : ℝ)) = x * (x * F.card / 4) by ring]
      have h4 : x * (x * F.card / 4) ≤ x * (P i).card := by
        rw [hP2 i]; exact mul_le_mul_of_nonneg_left hsz1 hx.le
      linarith

/-- an induced P6 in the complement is an induced P̄6 in `G` -/
lemma compl_not_contains (hfree : Free G P6ᶜ) (F : Finset V) : ¬ ContainsInduced Gᶜ P6 F := by
  rintro ⟨f, hinj, -, hadj⟩
  apply hfree
  refine ⟨f, hinj, fun i => mem_univ _, fun i j => ?_⟩
  have h := hadj i j
  rw [SimpleGraph.compl_adj] at h ⊢
  by_cases hij : i = j
  · subst hij
    simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    exact G.irrefl
  · have hf : f i ≠ f j := fun e => hij (hinj e)
    constructor
    · intro hG; exact ⟨hij, fun hp => (h.2 hp).2 hG⟩
    · rintro ⟨-, hnp⟩; by_contra hG; exact hnp (h.1 ⟨hf, hG⟩)

lemma r3_x {x : ℝ} {d : ℕ} (hd : 1 ≤ d) (hx : 0 < x) (hxd : x < 1 / 2 ^ d) :
    (2 : ℝ) ^ d ≤ 1 / x ∧ 1 / x ≤ 1 / x ^ d := by
  rw [lt_div_iff₀ (by positivity)] at hxd
  have h1 : (2 : ℝ) ^ d ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
  refine ⟨h1, ?_⟩
  have hx1 : 1 ≤ 1 / x := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans h1
  rw [← one_div_pow]
  calc 1 / x = (1 / x) ^ 1 := (pow_one _).symm
    _ ≤ (1 / x) ^ d := pow_le_pow_right₀ hx1 hd

lemma r3_c1 {s f θ A : ℝ} (hθA : 2 ^ 200 ≤ θ * A) (hθ0 : 0 < θ) (hA1 : 1 ≤ A) (hsA : A ≤ s)
    (hf : θ * s ≤ f) : s / A ≤ (⌊(1 / 360) ^ 2 * f⌋₊ : ℝ) := by
  have hs0 : 0 ≤ s := by linarith
  have hA0 : 0 < A := by linarith
  have h0 : θ * A ≤ θ * s := mul_le_mul_of_nonneg_left hsA hθ0.le
  have h1 : 1 ≤ (1 / 360) ^ 2 * f := by
    have : (1 : ℝ) ≤ (1 / 360) ^ 2 * 2 ^ 200 := by norm_num
    nlinarith
  have h2 := floor_half h1
  have h3 : 2 ^ 200 * s ≤ A * f := by
    have a1 := mul_le_mul_of_nonneg_left hf hA0.le
    have a2 := mul_le_mul_of_nonneg_right hθA hs0
    linarith [show A * (θ * s) = θ * A * s by ring]
  have h4 : s / A ≤ (1 / 360) ^ 2 * f / 2 := by
    rw [div_le_iff₀ hA0]
    have : (1 : ℝ) ≤ 2 ^ 200 * ((1 / 360) ^ 2 / 2) := by norm_num
    nlinarith
  linarith

lemma r3_F {x θ s f A : ℝ} {d : ℕ} (hd : 20 ≤ d) (hx : 0 < x) (hxA : A ≤ 1 / x) (hA1 : 1 ≤ A)
    (hθA : 2 ^ 200 ≤ θ * A) (hθ0 : 0 < θ) (hs : 1 / x ^ d ≤ s) (hf : θ * s ≤ f) :
    2 ^ 16 / x ^ 19 ≤ f := by
  have hx1 : 1 ≤ 1 / x := hA1.trans hxA
  have hp : (1 / x) ^ 19 * A ≤ 1 / x ^ d := by
    rw [← one_div_pow]
    have e : (1 / x) ^ d = (1 / x) ^ 19 * (1 / x) ^ (d - 19) := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc A ≤ 1 / x := hxA
      _ = (1 / x) ^ 1 := (pow_one _).symm
      _ ≤ (1 / x) ^ (d - 19) := pow_le_pow_right₀ hx1 (by omega)
  have h19 : (0 : ℝ) ≤ (1 / x) ^ 19 := by positivity
  have h2 : 2 ^ 200 * (1 / x) ^ 19 ≤ θ * A * (1 / x) ^ 19 := mul_le_mul_of_nonneg_right hθA h19
  have h3 : θ * ((1 / x) ^ 19 * A) ≤ θ * s := mul_le_mul_of_nonneg_left (hp.trans hs) hθ0.le
  have e2 : (2 : ℝ) ^ 16 / x ^ 19 = 2 ^ 16 * (1 / x) ^ 19 := by rw [one_div_pow]; ring
  rw [e2]
  linarith [show θ * A * (1 / x) ^ 19 = θ * ((1 / x) ^ 19 * A) by ring,
    show (2 : ℝ) ^ 16 * (1 / x) ^ 19 ≤ 2 ^ 200 * (1 / x) ^ 19 from
      mul_le_mul_of_nonneg_right (by norm_num) h19]

lemma r3_w1 {s f θ K : ℝ} {L : ℕ} (hK : 16 ≤ K) (hθ : 1 ≤ θ * 2 ^ L) (hθ0 : 0 < θ)
    (hf : θ * s ≤ f) (hs : 0 ≤ s) : s / K ^ (L + 200) ≤ f / K ^ 118 := by
  have hK0 : 0 < K := by linarith
  have hKL : (2 : ℝ) ^ L ≤ K ^ (L + 82) :=
    (pow_le_pow_left₀ (by norm_num) (by linarith) L).trans (pow_le_pow_right₀ (by linarith) (by omega))
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : f * K ^ (L + 200) = (f * K ^ (L + 82)) * K ^ 118 := by
    rw [mul_assoc, ← pow_add]
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h1 : θ * s * 2 ^ L ≤ f * K ^ (L + 82) :=
    mul_le_mul hf hKL (by positivity) (le_trans (by positivity) hf)
  nlinarith

lemma r3_w2 {s f θ y : ℝ} {L : ℕ} (hy0 : 0 < y) (hy : y ≤ 1 / 2 ^ 64) (hθ : 1 ≤ θ * 2 ^ L)
    (hθ0 : 0 < θ) (hf : θ * s ≤ f) (hs : 0 ≤ s) :
    2 ≤ (⌊1 / y⌋₊ : ℝ) ∧ s / (⌊1 / y⌋₊ : ℝ) ^ (L + 200) ≤ y ^ 7 * f := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊1 / y⌋₊ := ⟨_, rfl⟩
  rw [← hk]
  have h1y : 2 ^ 64 ≤ 1 / y := by
    rw [le_div_iff₀ (by positivity)] at hy
    rw [le_div_iff₀ hy0]; linarith
  have hk2 : (2 : ℝ) ≤ k := by
    have : 2 ≤ k := by rw [hk]; exact Nat.le_floor (by push_cast; linarith [show (2 : ℝ) ≤ 2 ^ 64 by norm_num])
    exact_mod_cast this
  refine ⟨hk2, ?_⟩
  have hk0 : (0 : ℝ) < k := by linarith
  have hky : 1 ≤ 2 * (k * y) := by
    have := Nat.lt_floor_add_one (1 / y)
    rw [← hk, div_lt_iff₀ hy0] at this
    nlinarith
  have h7 : (1 / 2 : ℝ) ^ 7 ≤ (k * y) ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
  have hkp : (2 : ℝ) ^ L * 2 ^ 193 ≤ (k : ℝ) ^ (L + 193) := by
    rw [← pow_add]; exact pow_le_pow_left₀ (by norm_num) hk2 _
  have key : 1 ≤ y ^ 7 * θ * (k : ℝ) ^ (L + 200) := by
    have e : y ^ 7 * θ * (k : ℝ) ^ (L + 200) = θ * ((k * y) ^ 7 * (k : ℝ) ^ (L + 193)) := by ring
    rw [e]
    have a1 : (1 / 2 : ℝ) ^ 7 * (2 ^ L * 2 ^ 193) ≤ (k * y) ^ 7 * (k : ℝ) ^ (L + 193) :=
      mul_le_mul h7 hkp (by positivity) (by positivity)
    have a2 : θ * ((1 / 2 : ℝ) ^ 7 * (2 ^ L * 2 ^ 193)) ≤ θ * ((k * y) ^ 7 * (k : ℝ) ^ (L + 193)) :=
      mul_le_mul_of_nonneg_left a1 hθ0.le
    have a3 : θ * ((1 / 2 : ℝ) ^ 7 * (2 ^ L * 2 ^ 193)) = θ * 2 ^ L * 2 ^ 186 := by ring
    have a4 : (1 : ℝ) ≤ θ * 2 ^ L * 2 ^ 186 := by
      have : (1 : ℝ) ≤ 2 ^ 186 := by norm_num
      nlinarith
    linarith
  rw [div_le_iff₀ (by positivity)]
  have b1 := mul_le_mul_of_nonneg_left hf (by positivity : (0 : ℝ) ≤ y ^ 7 * (k : ℝ) ^ (L + 200))
  have b2 := mul_le_mul_of_nonneg_left key hs
  nlinarith

/-- **Lemma 4.3** (NSS VII Lemma 5.5). There is `d ≥ 200` such that for every `x ∈ (0, 2⁻ᵈ)` and every
P̄6-free `G[S]` with `|S| ≥ x⁻ᵈ` there is, for some real `k ∈ [2, 1/x]`, an `x`-semisparse
`(k, |S|/kᵈ)`-blockade. -/
theorem round1_blockade (hR : RodlCoP6) (hP : NssPath6) (hcomb : NssComb) : ∃ d : ℕ, 200 ≤ d ∧ ∀ x : ℝ, 0 < x → x < 1 / 2 ^ d →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Free H P6ᶜ → ∀ S : Finset W, 1 / x ^ d ≤ (S.card : ℝ) →
        ∃ k : ℝ, 2 ≤ k ∧ k * x ≤ 1 ∧ ∃ β : Blockade S k (S.card / k ^ d), β.IsSemisparse H x := by
  obtain ⟨δ, hδ0, hR⟩ := hR (1 / 2 ^ 200) (by norm_num) (by norm_num)
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (1 / δ) (by norm_num : (1 : ℝ) < 2)
  have hδL : 1 ≤ δ * 2 ^ L := by rw [div_lt_iff₀ hδ0] at hL; linarith
  refine ⟨L + 200, by omega, fun x hx hxd W _ _ H _ hfree S hS => ?_⟩
  obtain ⟨F, hFS, hFc, hFr⟩ := hR W H hfree S
  obtain ⟨hA, hxA⟩ := r3_x (by omega) hx hxd
  have hA1 : (1 : ℝ) ≤ 2 ^ (L + 200) := one_le_pow₀ (by norm_num)
  have hθA : (2 : ℝ) ^ 200 ≤ δ * 2 ^ (L + 200) := by
    rw [pow_add]
    have : (0 : ℝ) ≤ 2 ^ 200 := by positivity
    nlinarith
  have hsA : (2 : ℝ) ^ (L + 200) ≤ S.card := hA.trans (hxA.trans hS)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hx2 : 2 * x ≤ 1 := by
    have : (2 : ℝ) ≤ 2 ^ (L + 200) := le_self_pow₀ (by norm_num) (by omega)
    have h := (le_div_iff₀ hx).1 (this.trans hA)
    linarith
  rcases hFr with hsp | hspc
  · -- `F` is sparse: round one (Lemma 4.2)
    have hsp' : Sparse H ((1 / 2 ^ 64) ^ 3 / 2 ^ 8) F := by
      rw [show ((1 : ℝ) / 2 ^ 64) ^ 3 / 2 ^ 8 = 1 / 2 ^ 200 by norm_num]; exact hsp
    have hx64 : x < 1 / 2 ^ 64 := by
      refine hxd.trans_le (div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hF16 := r3_F (d := L + 200) (by omega) hx hA hA1 hθA hδ0 hS hFc
    rcases round1 hcomb hfree hx hx64 F hsp' hF16 with ⟨K, hK1, hK2, β, hβ⟩ | ⟨y, hxy, hy, β, hβ⟩
    · have hK16 : (16 : ℝ) ≤ K := nat_ge_16 le_rfl hK1
      exact ⟨K, by linarith, hK2, β.mono hFS le_rfl (r3_w1 hK16 hδL hδ0 hFc hS0),
        fun i j hij => hβ i j hij⟩
    · have hy0 : 0 < y := hx.trans_le hxy
      obtain ⟨hk2, hw⟩ := r3_w2 hy0 hy hδL hδ0 hFc hS0
      have hk1 : (⌊1 / y⌋₊ : ℝ) ≤ 1 / y := Nat.floor_le (by positivity)
      have hkx : (⌊1 / y⌋₊ : ℝ) * x ≤ 1 := by
        have h1 : 1 / y ≤ 1 / x := div_le_div_of_nonneg_left (by norm_num) hx hxy
        have h2 := (le_div_iff₀ hx).1 (hk1.trans h1)
        linarith
      exact ⟨_, hk2, hkx, β.mono hFS hk1 hw, fun i j hij => semisparse_of_sparse β hβ i j hij⟩
  · -- the complement of `F` is sparse: NSS V 3.1 in the complement gives a complete blockade
    have hnot := compl_not_contains hfree F
    have hspc' : Sparse Hᶜ ((1 / 360) ^ 2) F :=
      sparse_sub hspc subset_rfl (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))
    obtain ⟨β, hβ⟩ := hP (1 / 360) (by norm_num) le_rfl W Hᶜ F hspc' hnot
    have hw := r3_c1 hθA hδ0 hA1 hsA hFc
    refine ⟨2, le_rfl, hx2, β.mono hFS (by norm_num) hw, fun i j hij => Or.inl ?_⟩
    intro a ha b hb
    have hab : a ≠ b := fun e => disjoint_left.1 (β.disj i j hij) ha (e ▸ hb)
    by_contra hn
    exact hβ i j hij a ha b hb ((SimpleGraph.compl_adj H a b).2 ⟨hab, hn⟩)

end EHP6
