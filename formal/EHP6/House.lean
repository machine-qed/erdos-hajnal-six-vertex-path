import EHP6.Certificate

/-!
# §1.2 Diagonal lemma, house lemma, Corollary 1.4 (house-free mixed patterns)

Setting: blocks `B : Fin ℓ → Finset V`, anticonnected, of equal size `W`, and every two blocks complete
or `x`-sparse to each other in both directions, with `x < ½`.
-/

namespace EHP6

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The standing hypotheses of §1.2 on a block system. -/
structure BlockSystem {ℓ : ℕ} (B : Fin ℓ → Finset V) (W : ℕ) (x : ℝ) : Prop where
  card : ∀ i, (B i).card = W
  anti : ∀ i, AntiConnected G (B i)
  pairs : ∀ i j, i ≠ j → Complete G (B i) (B j) ∨ (SparseTo G x (B i) (B j) ∧ SparseTo G x (B j) (B i))
  hx : 0 < x
  hx2 : x < 1 / 2

omit [Fintype V] in
/-- a vertex with at most `x|A|` neighbours in `A` (x < 1, A nonempty) has a non-neighbour there -/
lemma exists_nonnbr {v : V} {A : Finset V} {x : ℝ} (hx : x < 1) (hA : A.Nonempty)
    (h : ((nbrs G v A).card : ℝ) ≤ x * A.card) : ∃ a ∈ A, ¬ G.Adj v a := by
  by_contra hc
  push Not at hc
  have : nbrs G v A = A := filter_true_of_mem hc
  rw [this] at h
  have : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  nlinarith

omit [Fintype V] in
/-- two vertices each with at most `x|A|` neighbours in `A` (`2x < 1`) have a common non-neighbour -/
lemma exists_common_nonnbr {v w : V} {A : Finset V} {x : ℝ} (hx : 2 * x < 1) (hA : A.Nonempty)
    (hv : ((nbrs G v A).card : ℝ) ≤ x * A.card) (hw : ((nbrs G w A).card : ℝ) ≤ x * A.card) :
    ∃ a ∈ A, ¬ G.Adj v a ∧ ¬ G.Adj w a := by
  by_contra hc
  push Not at hc
  have hsub : A ⊆ nbrs G v A ∪ nbrs G w A := by
    intro a ha
    by_cases hva : G.Adj v a
    · exact mem_union_left _ (mem_filter.2 ⟨ha, hva⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨ha, hc a ha hva⟩)
  have h1 : (A.card : ℝ) ≤ (nbrs G v A).card + (nbrs G w A).card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  nlinarith

omit [Fintype V] in
/-- anticonnectivity: if `v` has a neighbour and a non-neighbour in an anticonnected `K`, there are
`p ∈ N(v) ∩ K`, `q ∈ K \ N(v)` with `p ≁ q`. -/
lemma mixed_pair {v : V} {K : Finset V} (hK : AntiConnected G K) {p₀ q₀ : V} (hp₀ : p₀ ∈ K)
    (hvp : G.Adj v p₀) (hq₀ : q₀ ∈ K) (hvq : ¬ G.Adj v q₀) :
    ∃ p ∈ K, ∃ q ∈ K, G.Adj v p ∧ ¬ G.Adj v q ∧ ¬ G.Adj p q := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hK (K.filter (G.Adj v)) (filter_subset _ _)
    ⟨p₀, mem_filter.2 ⟨hp₀, hvp⟩⟩ ⟨q₀, mem_sdiff.2 ⟨hq₀, fun h => hvq (mem_filter.1 h).2⟩⟩
  obtain ⟨hpK, hvp'⟩ := mem_filter.1 hp
  obtain ⟨hqK, hqP⟩ := mem_sdiff.1 hq
  exact ⟨p, hpK, q, hqK, hvp', fun h => hqP (mem_filter.2 ⟨hqK, h⟩), hpq⟩

variable {G}

lemma BlockSystem.sparse_of_not_complete {ℓ : ℕ} {B : Fin ℓ → Finset V} {W : ℕ} {x : ℝ}
    (hS : BlockSystem G B W x) {i j : Fin ℓ} (hij : i ≠ j) (hc : ¬ Complete G (B i) (B j)) :
    SparseTo G x (B i) (B j) ∧ SparseTo G x (B j) (B i) :=
  (hS.pairs i j hij).resolve_left hc

/-- **Lemma 1.2 (diagonal lemma).** -/
theorem diagonal_lemma (hfree : Free G P6ᶜ) {ℓ : ℕ} {B : Fin ℓ → Finset V} {W : ℕ} {x : ℝ}
    (hS : BlockSystem G B W x) (hW : 0 < W) {b c d e f : Fin ℓ}
    (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f)
    (cbd : Complete G (B b) (B d)) (cbe : Complete G (B b) (B e)) (cbf : Complete G (B b) (B f))
    (cce : Complete G (B c) (B e)) (ccf : Complete G (B c) (B f)) (cdf : Complete G (B d) (B f))
    (nbc : ¬ Complete G (B b) (B c)) (ncd : ¬ Complete G (B c) (B d))
    (nde : ¬ Complete G (B d) (B e)) (nef : ¬ Complete G (B e) (B f)) :
    Anticomplete G (B e) (B f) := by
  intro x₀ hx₀ p₀ hp₀
  by_contra hxp
  have hne : ∀ i, (B i).Nonempty := fun i => card_pos.1 (by rw [hS.card i]; exact hW)
  have hx1 : x < 1 := by linarith [hS.hx2]
  -- x₀ has a non-neighbour in B_f, then a non-adjacent pair p ∈ N(x₀), q ∉ N(x₀) in B_f
  obtain ⟨q₀, hq₀, hxq₀⟩ := exists_nonnbr G hx1 (hne f)
    ((hS.sparse_of_not_complete hef nef).1 x₀ hx₀)
  obtain ⟨p, hp, q, hq, hxp', hxq, hpq⟩ := mixed_pair G (hS.anti f) hp₀ hxp hq₀ hxq₀
  obtain ⟨ub, hub⟩ := hne b
  obtain ⟨uc, huc, hbc'⟩ := exists_nonnbr G hx1 (hne c)
    ((hS.sparse_of_not_complete hbc nbc).1 ub hub)
  obtain ⟨ud, hud, hxd, hcd'⟩ := exists_common_nonnbr G (by linarith [hS.hx2]) (hne d)
    ((hS.sparse_of_not_complete hde.symm (fun h => nde (fun a ha b hb => G.adj_symm (h b hb a ha)))).1
      x₀ hx₀)
    ((hS.sparse_of_not_complete hcd ncd).1 uc huc)
  apply hfree
  -- complement path p – q – x₀ – u_d – u_c – u_b
  exact coP6_of_facts G p q x₀ ud uc ub (G.adj_symm hxp') (G.adj_symm (cdf ud hud p hp))
    (G.adj_symm (ccf uc huc p hp)) (G.adj_symm (cbf ub hub p hp)) (G.adj_symm (cdf ud hud q hq))
    (G.adj_symm (ccf uc huc q hq)) (G.adj_symm (cbf ub hub q hq)) (G.adj_symm (cce uc huc x₀ hx₀))
    (G.adj_symm (cbe ub hub x₀ hx₀)) (G.adj_symm (cbd ub hub ud hud))
    hpq (fun h => hxq (G.adj_symm h)) hxd (fun h => hcd' (G.adj_symm h)) (fun h => hbc' (G.adj_symm h))

/-- **Lemma 1.3 (house lemma).** No vertex has: a neighbour and a non-neighbour in `B_b`, a neighbour in
`B_e`, a neighbour in `B_f`, and more than `xW` non-neighbours in `B_d`. -/
theorem house_lemma (hfree : Free G P6ᶜ) {ℓ : ℕ} {B : Fin ℓ → Finset V} {W : ℕ} {x : ℝ}
    (hS : BlockSystem G B W x) (hW : 0 < W) {b c d e f : Fin ℓ}
    (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f)
    (cbd : Complete G (B b) (B d)) (cbe : Complete G (B b) (B e)) (cbf : Complete G (B b) (B f))
    (cce : Complete G (B c) (B e)) (ccf : Complete G (B c) (B f)) (cdf : Complete G (B d) (B f))
    (nbc : ¬ Complete G (B b) (B c)) (ncd : ¬ Complete G (B c) (B d))
    (nde : ¬ Complete G (B d) (B e)) (nef : ¬ Complete G (B e) (B f))
    (v : V) {pb qb xe xf : V} (hpb : pb ∈ B b) (hvpb : G.Adj v pb) (hqb : qb ∈ B b) (hvqb : ¬ G.Adj v qb)
    (hxe : xe ∈ B e) (hvxe : G.Adj v xe) (hxf : xf ∈ B f) (hvxf : G.Adj v xf)
    (hd : x * W < (((B d).filter (fun u => ¬ G.Adj v u)).card : ℝ)) : False := by
  have hanti := diagonal_lemma hfree hS hW hbc hcd hde hef cbd cbe cbf cce ccf cdf nbc ncd nde nef
  have hxexf : ¬ G.Adj xe xf := hanti xe hxe xf hxf
  obtain ⟨p, hp, q, hq, hvp, hvq, hpq⟩ := mixed_pair G (hS.anti b) hpb hvpb hqb hvqb
  -- u_d ∈ B_d, non-adjacent to v and to x_e
  have hsp : ((nbrs G xe (B d)).card : ℝ) ≤ x * W := by
    have := (hS.sparse_of_not_complete hde.symm
      (fun h => nde (fun a ha b hb => G.adj_symm (h b hb a ha)))).1 xe hxe
    rwa [hS.card d] at this
  obtain ⟨ud, hud, hvud, hxud⟩ : ∃ u ∈ B d, ¬ G.Adj v u ∧ ¬ G.Adj xe u := by
    by_contra hc
    push Not at hc
    have hsub : (B d).filter (fun u => ¬ G.Adj v u) ⊆ nbrs G xe (B d) := by
      intro u hu
      obtain ⟨huB, hvu⟩ := mem_filter.1 hu
      exact mem_filter.2 ⟨huB, hc u huB hvu⟩
    have := (card_le_card hsub)
    have : (((B d).filter (fun u => ¬ G.Adj v u)).card : ℝ) ≤ (nbrs G xe (B d)).card := by
      exact_mod_cast this
    linarith
  apply hfree
  -- complement path p_b – q_b – v – u_d – x_e – x_f
  exact coP6_of_facts G p q v ud xe xf (G.adj_symm hvp) (cbd p hp ud hud) (cbe p hp xe hxe)
    (cbf p hp xf hxf) (cbd q hq ud hud) (cbe q hq xe hxe) (cbf q hq xf hxf) hvxe hvxf
    (cdf ud hud xf hxf) hpq (fun h => hvq (G.adj_symm h)) hvud (fun h => hxud (G.adj_symm h)) hxexf

/-- the pattern graph of a block system: `i ~ j` iff `B_i` is complete to `B_j` -/
def patternGraph {ℓ : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (B : Fin ℓ → Finset V) :
    SimpleGraph (Fin ℓ) where
  Adj i j := i ≠ j ∧ Complete G (B i) (B j) ∧ Complete G (B j) (B i)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- the blocks on which `v` is lightly mixed: `0 < |N(v) ∩ B_i| < W/2` -/
noncomputable def lightIdx {ℓ : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (B : Fin ℓ → Finset V) (W : ℕ)
    (v : V) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun i => 0 < (nbrs G v (B i)).card ∧ ((nbrs G v (B i)).card : ℝ) < W / 2)

/-- **Corollary 1.4 (first part).** The pattern of blocks on which `v` is lightly mixed is house-free:
no five light indices induce a house (the complement of P5) in the pattern graph. -/
theorem light_pattern_house_free (hfree : Free G P6ᶜ) {ℓ : ℕ} {B : Fin ℓ → Finset V} {W : ℕ} {x : ℝ}
    (hS : BlockSystem G B W x) (v : V) :
    ¬ ∃ g : Fin 5 → Fin ℓ, Function.Injective g ∧ (∀ t, g t ∈ lightIdx G B W v) ∧
      ∀ s t, (patternGraph G B).Adj (g s) (g t) ↔ P5ᶜ.Adj s t := by
  rintro ⟨g, hg, hlight, hadj⟩
  have hP : ∀ s t : Fin 5, P5ᶜ.Adj s t ↔ (s.val + 2 ≤ t.val ∨ t.val + 2 ≤ s.val) := by decide
  have comp : ∀ s t : Fin 5, s.val + 2 ≤ t.val → Complete G (B (g s)) (B (g t)) := fun s t h =>
    (((hadj s t).2 ((hP s t).2 (Or.inl h))).2.1)
  have ncomp : ∀ s t : Fin 5, t.val = s.val + 1 → ¬ Complete G (B (g s)) (B (g t)) := by
    intro s t h hc
    have hst : g s ≠ g t := fun h' => by have := hg h'; subst this; omega
    have hsym : Complete G (B (g t)) (B (g s)) := by
      rcases hS.pairs (g s) (g t) hst with h1 | h1
      · exact fun a ha b hb => G.adj_symm (h1 b hb a ha)
      · -- a complete pair cannot also be x-sparse (blocks nonempty, x < 1)
        exact fun a ha b hb => G.adj_symm (hc b hb a ha)
    have := (hadj s t).1 ⟨hst, hc, hsym⟩
    rw [hP] at this; omega
  have hmem := fun t => mem_filter.1 (hlight t)
  -- v's neighbourhoods
  have hWpos : 0 < W := by
    have h0 := (hmem 0).2
    have h1 : (nbrs G v (B (g 0))).card ≤ (B (g 0)).card := card_le_card (filter_subset _ _)
    rw [hS.card] at h1; omega
  obtain ⟨xb, hxb⟩ := card_pos.1 (hmem 0).2.1
  obtain ⟨hxbB, hvxb⟩ := mem_filter.1 hxb
  obtain ⟨xe, hxe⟩ := card_pos.1 (hmem 3).2.1
  obtain ⟨hxeB, hvxe⟩ := mem_filter.1 hxe
  obtain ⟨xf, hxf⟩ := card_pos.1 (hmem 4).2.1
  obtain ⟨hxfB, hvxf⟩ := mem_filter.1 hxf
  have hnb : ((nbrs G v (B (g 0))).card : ℝ) < W / 2 := (hmem 0).2.2
  obtain ⟨qb, hqb, hvqb⟩ : ∃ q ∈ B (g 0), ¬ G.Adj v q := by
    apply exists_nonnbr G (x := 1 / 2) (by norm_num)
    · exact card_pos.1 (by rw [hS.card]; exact hWpos)
    · rw [hS.card]; linarith
  have hd : x * W < (((B (g 2)).filter (fun u => ¬ G.Adj v u)).card : ℝ) := by
    have hsplit := card_filter_add_card_filter_not (s := B (g 2)) (fun u => G.Adj v u)
    have hlt : ((nbrs G v (B (g 2))).card : ℝ) < W / 2 := (hmem 2).2.2
    have hc2 : ((B (g 2)).filter (fun u => G.Adj v u)).card + ((B (g 2)).filter
        (fun u => ¬ G.Adj v u)).card = W := by rw [hsplit, hS.card]
    have hc2' : (((B (g 2)).filter (fun u => G.Adj v u)).card : ℝ) + (((B (g 2)).filter
        (fun u => ¬ G.Adj v u)).card : ℝ) = W := by exact_mod_cast hc2
    have : (W : ℝ) > 0 := by exact_mod_cast hWpos
    have := hS.hx2
    unfold nbrs at hlt
    nlinarith
  have ne : ∀ s t : Fin 5, s ≠ t → g s ≠ g t := fun s t h h' => h (hg h')
  exact house_lemma hfree hS hWpos (b := g 0) (c := g 1) (d := g 2) (e := g 3) (f := g 4)
    (ne 0 1 (by decide)) (ne 1 2 (by decide)) (ne 2 3 (by decide)) (ne 3 4 (by decide))
    (comp 0 2 (by decide)) (comp 0 3 (by decide)) (comp 0 4 (by decide)) (comp 1 3 (by decide))
    (comp 1 4 (by decide)) (comp 2 4 (by decide))
    (ncomp 0 1 rfl) (ncomp 1 2 rfl) (ncomp 2 3 rfl) (ncomp 3 4 rfl)
    v hxbB hvxb hqb hvqb hxeB hvxe hxfB hvxf hd

end EHP6
