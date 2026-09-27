import EHP6.Imported

/-!
# Three cited results, asserted as axioms

The proof itself (`EHP6.erdos_hajnal_P6_of_cited`) takes three propositions of `EHP6/Imported.lean` as
hypotheses; the fourth, `NssPath6`, is proved in `EHP6/NSSPath.lean`. This file asserts the three, on the
authority of the cited papers, so that the unconditional theorem `EHP6.erdos_hajnal_P6 : EHforP6` can be
stated. `#print axioms` for that theorem lists exactly these three axioms besides Lean's standard ones.
-/

namespace EHP6

/-- Rödl's theorem for H = P̄6 (Rödl 1986; NSS VII, Theorem 1.3). -/
axiom rodl_coP6 : RodlCoP6

/-- The Erdős–Hajnal property of P5 (Nguyen–Scott–Seymour, *Induced subgraph density VII*,
Theorem 1.2). -/
axiom eh_P5 : EhP5

/-- The comb lemma (NSS VII, Lemma 4.3). -/
axiom nss_comb : NssComb

end EHP6
