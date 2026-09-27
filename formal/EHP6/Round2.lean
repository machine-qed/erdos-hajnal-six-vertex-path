import EHP6.Round2Hom
import EHP6.Round2Num
import EHP6.Nice

/-!
# Lemma 6.1 (NSS VII Lemma 7.1 for P̄6-free graphs)
-/

namespace EHP6

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma complete_symm {A B : Finset V} (h : Complete G A B) : Complete G B A :=
  fun b hb a ha => G.adj_symm (h a ha b hb)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma double_count {α β : Type} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → Finset β)
    (hf : ∀ a ∈ s, f a ⊆ t) :
    ∑ a ∈ s, (f a).card = ∑ b ∈ t, (s.filter (fun a => b ∈ f a)).card := by
  have h1 : ∀ a ∈ s, (f a).card = ∑ b ∈ t, if b ∈ f a then 1 else 0 := fun a ha => by
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 (hf a ha)]; simp
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [card_eq_sum_ones, sum_filter]

set_option maxHeartbeats 1000000 in
/-- **Lemma 6.1** (NSS VII Lemma 7.1 for P̄6-free graphs). Let `d` be as in Lemma 5.2, `κ` the
EH(P5) exponent, `M ≥ 5/κ + 4` and `A₁ = M(10d² + 3)`. Let `y ∈ (0, 1/8]` and `G[S]` `y`-sparse and
P̄6-free. Then (a) some `T ⊆ S` with `|T| ≥ y^{A₁}|S|` is `y⁴`-sparse; or (b) there is a complete
`(y⁻¹, y^{A₁}|S|)`-blockade; or (c) there are disjoint `X, Y ⊆ S`, `|X| ≥ y^{A₁}|S|`,
`|Y| ≥ (1 − 4y)|S|`, with `X` anticomplete to `Y`. -/
theorem round2_step (hfree : Free G P6ᶜ) {d : ℕ} (hd : 200 ≤ d)
    (hnice : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ S : Finset V, 1 / ε ^ (10 * d ^ 2) ≤ (S.card : ℝ) →
        ∃ β : Blockade S (1 / ε) (ε ^ (10 * d ^ 2) * S.card), β.IsSemisparse G (ε ^ d))
    {κ : ℝ} (hκ : 0 < κ) (hEH : EHP5 κ) {M : ℕ} (hM : 5 / κ + 4 ≤ M)
    {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 8) (S : Finset V) (hsp : Sparse G y S) :
    (∃ T ⊆ S, y ^ (M * (10 * d ^ 2 + 3)) * S.card ≤ T.card ∧ Sparse G (y ^ 4) T) ∨
    (∃ β : Blockade S (1 / y) (y ^ (M * (10 * d ^ 2 + 3)) * S.card), β.IsComplete G) ∨
    (∃ X ⊆ S, ∃ Y ⊆ S, Disjoint X Y ∧ y ^ (M * (10 * d ^ 2 + 3)) * S.card ≤ X.card ∧
      (1 - 4 * y) * S.card ≤ Y.card ∧ Anticomplete G X Y) := by
  obtain ⟨N, hN⟩ : ∃ N, N = 10 * d ^ 2 := ⟨_, rfl⟩
  rw [← hN] at hnice ⊢
  have hM5 : 5 ≤ M := by
    have : (4 : ℝ) < M := by linarith [show 0 < 5 / κ by positivity]
    have : 4 < M := by exact_mod_cast this
    omega
  obtain ⟨hε0, hε12, hε5, hε8⟩ := n61_eps hy0 hy hM5
  have hεy : y ^ M ≤ y := by
    calc y ^ M ≤ y ^ 1 := pow_le_pow_of_le_one hy0.le (by linarith) (by omega)
      _ = y := pow_one y
  have hℓy : 1 / y ^ M ≤ ⌈1 / y ^ M⌉₊ := Nat.le_ceil _
  rw [pow_mul]
  generalize hεdef : y ^ M = ε at hε0 hε12 hε5 hε8 hεy hℓy ⊢
  have hε1 : ε ≤ 1 := hε12.trans (by norm_num)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  -- small `S`: a single vertex
  by_cases hsmall : (S.card : ℝ) ≤ 1 / ε ^ (N + 3)
  · left
    rcases S.eq_empty_or_nonempty with hSe | ⟨v, hv⟩
    · subst hSe
      exact ⟨∅, subset_refl _, by simp, fun u hu => absurd hu (notMem_empty u)⟩
    · refine ⟨{v}, singleton_subset_iff.2 hv, ?_, ?_⟩
      · rw [card_singleton, Nat.cast_one]
        rw [le_div_iff₀ (by positivity)] at hsmall; linarith
      · intro u hu
        rw [mem_singleton.1 hu]
        have : nbrs G v {v} = ∅ := by
          apply filter_eq_empty_iff.2; intro w hw; rw [mem_singleton.1 hw]; exact G.irrefl
        rw [this, card_empty, Nat.cast_zero]; positivity
  push Not at hsmall
  have hSpos : (0 : ℝ) < S.card := lt_of_le_of_lt (by positivity) hsmall
  -- parameters
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = ⌈1 / ε⌉₊ := ⟨_, rfl⟩
  obtain ⟨hℓ1, hℓ2, hℓ2'⟩ := n61_ell hε0 hε12 hℓ
  obtain ⟨m, hm⟩ : ∃ m, m = ⌈ε ^ N * S.card⌉₊ := ⟨_, rfl⟩
  obtain ⟨hmN, hm2, hm3, hm0⟩ := n61_m hε0 hε1 hsmall hm
  obtain ⟨b, hb⟩ : ∃ b, b = ⌈ε ^ 2 * m⌉₊ := ⟨_, rfl⟩
  obtain ⟨hb1, hb2, hb1', hbm, hbD, hDm⟩ := n61_b hε0 hε12 hm3 hℓ2 (by omega) hb
  obtain ⟨hK, hK2, hθ, hθ2, hθε, hθ₁0, hθ₂0⟩ := n61_consts hε0 hε12 hd hℓ2
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hyℓ : 1 / y ≤ ℓ := (div_le_div_of_nonneg_left (by norm_num) hε0 hεy).trans hℓ1
  -- Lemma 5.2
  have hSN : 1 / ε ^ N ≤ (S.card : ℝ) := by
    refine le_trans ?_ hsmall.le
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_of_le_one hε0.le hε1 (by omega)
  obtain ⟨β, hβ⟩ := hnice ε hε0 (by linarith [show (1 : ℝ) / 2 ^ 12 < 1 / 2 by norm_num]) S hSN
  have hℓm : ℓ ≤ β.m := by rw [hℓ]; exact Nat.ceil_le.2 β.len
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Finset V,
      A = fun i => if h : i < ℓ then β.B ⟨i, lt_of_lt_of_le h hℓm⟩ else ∅ := ⟨_, rfl⟩
  have hAeq : ∀ i (h : i < ℓ), A i = β.B ⟨i, lt_of_lt_of_le h hℓm⟩ := fun i h => by
    rw [hA]; simp only [dif_pos h]
  have hAS : ∀ i < ℓ, A i ⊆ S := fun i h => by rw [hAeq i h]; exact β.sub _
  have hAm : ∀ i < ℓ, m ≤ (A i).card := fun i h => by
    rw [hAeq i h, hm]; exact Nat.ceil_le.2 (β.wid _)
  have hAd : ∀ i < ℓ, ∀ j < ℓ, i ≠ j → Disjoint (A i) (A j) := fun i hi j hj hij => by
    rw [hAeq i hi, hAeq j hj]; exact β.disj _ _ (fun e => hij (congrArg Fin.val e))
  have hws : ∀ p < ℓ, ∀ q < ℓ, p < q → ¬ Complete G (A p) (A q) →
      WeaklySparse G (ε ^ d) (A p) (A q) := fun p hp q hq hpq hnc => by
    rw [hAeq p hp, hAeq q hq] at hnc ⊢
    exact (hβ _ _ (fun e => by have := congrArg Fin.val e; simp at this; omega)).resolve_left hnc
  -- pass 1: equal-size blocks
  obtain ⟨X, hX1, hX2, hX3⟩ := pass1_full (G := G) (c := ε ^ d) (K₁ := 2 * ℓ * ε ^ d)
    (K₂ := ε ^ (d - 3)) hm0 (pow_pos hε0 d) le_rfl hK hAm hws ℓ le_rfl
  have hθb : ε ^ (d - 5) * m ≤ ε ^ (d - 7) * b := by
    have := mul_le_mul_of_nonneg_left hb1 hθ₂0.le
    have e : ε ^ (d - 5) * m ≤ ε ^ 2 * ε ^ (d - 7) * m :=
      mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _)
    nlinarith
  -- pass 2: anticonnected sub-blocks
  rcases pass2_full (A := A) (X := X) (b := b) (K₂ := ε ^ (d - 3)) (θ₁ := ε ^ (d - 5))
      (θ₂ := ε ^ (d - 7)) (ρ := ε ^ 2) hX1 (fun p' p h1 h2 h3 => hX3 p' p h1 h2 h3) hℓ2' hm0 hb1'
      hθ₁0 hθ₂0 hK2 hθ hθb hDm hbD ℓ le_rfl with ⟨j, hj, D, hDX, hDc, γ, hγ⟩ | ⟨B, hB1, hB2, hB3⟩
  · -- a complete blockade: outcome (b)
    right; left
    exact ⟨γ.mono (hDX.trans ((hX1 j hj).1.trans (hAS j hj))) hyℓ
      (n61_cw hε0 (hε12.trans (by norm_num)) hS0 hm2 hmN hDc hℓ2 hℓr), fun a a' h => hγ a a' h⟩
  -- the block system
  obtain ⟨B', hB'⟩ : ∃ B' : Fin ℓ → Finset V, B' = fun j => B j.val := ⟨_, rfl⟩
  have hB'A : ∀ j : Fin ℓ, B' j ⊆ A j := fun j => by
    rw [hB']; exact (hB1 j j.2).1.trans (hX1 j j.2).1
  have hB'S : ∀ j : Fin ℓ, B' j ⊆ S := fun j => (hB'A j).trans (hAS j j.2)
  have hdisj' : ∀ j j' : Fin ℓ, j ≠ j' → Disjoint (B' j) (B' j') := fun j j' h =>
    disjoint_of_subset_left (hB'A j) (disjoint_of_subset_right (hB'A j')
      (hAd j j.2 j' j'.2 (fun e => h (Fin.ext e))))
  have hBS : BlockSystem G B' b (ε ^ (d - 7)) := by
    refine ⟨fun j => by rw [hB']; exact (hB1 j j.2).2.1, fun j => by rw [hB']; exact (hB1 j j.2).2.2,
      fun j j' hjj' => ?_, hθ₂0, hθ2⟩
    by_cases hc : Complete G (A j) (A j')
    · exact Or.inl fun a ha a' ha' => hc a (hB'A j ha) a' (hB'A j' ha')
    · right
      rw [hB']
      rcases lt_or_gt_of_ne (fun e => hjj' (Fin.ext e)) with h | h
      · obtain ⟨s1, s2⟩ := hB3 j j' h j'.2 hc; exact ⟨s2, s1⟩
      · exact hB3 j' j h j.2 (fun h' => hc (complete_symm h'))
  have hwb : ε ^ (N + 3) * S.card ≤ b := n61_wb hε0 hε1 hS0 hmN hb1
  -- the Claim of Step 4
  by_cases hex : ∃ v ∈ S, y * ℓ ≤ ((lightIdx G B' b v).card : ℝ)
  · obtain ⟨v, -, hv⟩ := hex
    have hr := n61_thr hy0 hy hκ hM (by rw [hεdef]; exact hℓ1) hv
    rcases light_small hfree hBS hdisj' hB'S v hEH hy0 (by linarith) hr (hθε.trans hε5) hwb with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  push Not at hex
  -- the rest `R₀`
  obtain ⟨U, hU⟩ : ∃ U, U = univ.biUnion B' := ⟨_, rfl⟩
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ = S \ U := ⟨_, rfl⟩
  have hR₀S : R₀ ⊆ S := by rw [hR₀]; exact sdiff_subset
  have hUc : (U.card : ℝ) ≤ ℓ * b := by
    have h1 : U.card ≤ ∑ j, (B' j).card := by rw [hU]; exact card_biUnion_le
    have h2 : ∑ j, (B' j).card = ℓ * b := by
      simp only [hBS.card, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    rw [h2] at h1; exact_mod_cast h1
  have hUy := n61_union hε0 hε1 hS0 hℓ2 hℓr.le hb2 (Nat.cast_nonneg b) hm2 hε8
  have hR₀c : (1 - y ^ 2) * S.card ≤ R₀.card := by
    have : S.card ≤ R₀.card + U.card := by rw [hR₀]; exact card_le_card_sdiff_add_card
    have : (S.card : ℝ) ≤ R₀.card + U.card := by exact_mod_cast this
    linarith [show (1 - y ^ 2) * (S.card : ℝ) = S.card - y ^ 2 * S.card by ring]
  have hR₀ne : R₀.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < R₀.card := by
      have h1 : y ^ 2 < 1 := by
        have : y ^ 2 ≤ (1 / 8) ^ 2 := pow_le_pow_left₀ hy0.le hy 2
        linarith [show ((1 : ℝ) / 8) ^ 2 < 1 by norm_num]
      have h2 : 0 < (1 - y ^ 2) * (S.card : ℝ) := mul_pos (by linarith) hSpos
      linarith
    exact_mod_cast this
  -- averaging: a block `i` on which few vertices of `R₀` are lightly mixed
  have hsum : ∑ v ∈ R₀, ((lightIdx G B' b v).card : ℝ) < ∑ v ∈ R₀, y * ℓ :=
    sum_lt_sum_of_nonempty hR₀ne fun v hv => hex v (hR₀S hv)
  have hdc : ∑ v ∈ R₀, ((lightIdx G B' b v).card : ℝ) =
      ∑ i : Fin ℓ, ((R₀.filter (fun v => i ∈ lightIdx G B' b v)).card : ℝ) := by
    have := double_count R₀ univ (fun v => lightIdx G B' b v) (fun _ _ => subset_univ _)
    exact_mod_cast this
  have hsum' : ∑ i : Fin ℓ, ((R₀.filter (fun v => i ∈ lightIdx G B' b v)).card : ℝ) <
      ∑ _i : Fin ℓ, y * R₀.card := by
    rw [← hdc]
    calc ∑ v ∈ R₀, ((lightIdx G B' b v).card : ℝ) < ∑ v ∈ R₀, y * ℓ := hsum
      _ = ∑ _i : Fin ℓ, y * R₀.card := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  obtain ⟨i, -, hi⟩ := exists_lt_of_sum_lt hsum'
  -- few vertices have many neighbours in `B' i`
  obtain ⟨H, hH⟩ : ∃ H, H = S.filter (fun v => (b : ℝ) / 2 ≤ ((nbrs G v (B' i)).card : ℝ)) :=
    ⟨_, rfl⟩
  have hHc : (H.card : ℝ) ≤ 2 * y * S.card := by
    have a1 := card_high_deg (G := G) S (B' i) ((b : ℝ) / 2)
    rw [← hH] at a1
    have a2 : (edgesBetween G S (B' i) : ℝ) ≤ b * (y * S.card) := by
      rw [edgesBetween_comm]
      have := edges_le_of_sparseTo (G := G) (x := y) (B := B' i) (A := S)
        (fun v hv => hsp v (hB'S i hv))
      rwa [hBS.card] at this
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have : (b : ℝ) / 2 * H.card ≤ (b : ℝ) / 2 * (2 * y * S.card) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  -- the anticomplete pair
  obtain ⟨Y, hY⟩ : ∃ Y, Y = R₀.filter (fun v => nbrs G v (B' i) = ∅) := ⟨_, rfl⟩
  have hcover : R₀ ⊆ Y ∪ R₀.filter (fun v => i ∈ lightIdx G B' b v) ∪ H := by
    intro v hv
    by_cases hn : nbrs G v (B' i) = ∅
    · exact mem_union_left _ (mem_union_left _ (by rw [hY]; exact mem_filter.2 ⟨hv, hn⟩))
    · have hpos : 0 < (nbrs G v (B' i)).card := card_pos.2 (nonempty_iff_ne_empty.2 hn)
      by_cases hl : ((nbrs G v (B' i)).card : ℝ) < b / 2
      · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hv,
          mem_filter.2 ⟨mem_univ _, hpos, hl⟩⟩))
      · push Not at hl
        exact mem_union_right _ (by rw [hH]; exact mem_filter.2 ⟨hR₀S hv, hl⟩)
  have hcard : (R₀.card : ℝ) ≤ Y.card + (R₀.filter (fun v => i ∈ lightIdx G B' b v)).card + H.card := by
    have := (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    exact_mod_cast this
  have hYc := n61_final hy0 hy hS0 hR₀c hcard hi.le hHc
  right; right
  refine ⟨B' i, hB'S i, Y, (by rw [hY]; exact (filter_subset _ _).trans hR₀S), ?_, ?_, hYc, ?_⟩
  · rw [disjoint_left]
    intro a ha haY
    rw [hY] at haY
    have := (mem_filter.1 haY).1
    rw [hR₀] at this
    exact (mem_sdiff.1 this).2 (by rw [hU]; exact mem_biUnion.2 ⟨i, mem_univ _, ha⟩)
  · rw [hBS.card]; exact hwb
  · intro a ha v hv hav
    rw [hY] at hv
    have hn := (mem_filter.1 hv).2
    have : a ∈ nbrs G v (B' i) := mem_filter.2 ⟨ha, G.adj_symm hav⟩
    rw [hn] at this
    exact notMem_empty a this

end EHP6
