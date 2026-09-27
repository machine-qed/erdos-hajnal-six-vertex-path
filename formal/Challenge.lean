import EHP6.Imported

/-!
# Comparator challenge

The statement to be checked, with no proof. It depends only on `EHP6/Defs.lean` (the definitions of
P6-free, clique, stable set and `EHforP6`) and `EHP6/Imported.lean` (the four cited results, as
propositions). Comparator checks that `Solution` proves exactly this statement, using no axioms beyond
`propext`, `Quot.sound` and `Classical.choice`, and replays the proof in the Lean kernel and in the
independent nanoda kernel. See `VERIFICATION.md`.
-/

namespace EHP6

theorem erdos_hajnal_P6_of_imported (hR : RodlCoP6) (hP : NssPath6) (hE : EhP5) (hC : NssComb) :
    EHforP6 := by
  sorry

theorem erdos_hajnal_P6_of_cited (hR : RodlCoP6) (hE : EhP5) (hC : NssComb) : EHforP6 := by
  sorry

end EHP6
