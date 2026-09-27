# Release v1.0-proof

The git tag `v1.0-proof` marks the first complete version: the paper and the Lean proof of the
Erdős–Hajnal property for P6. `git rev-list -n 1 v1.0-proof` shows the commit it marks.

| item | value |
|---|---|
| paper | `paper/erdos-hajnal-p6.pdf`, built with pdfTeX from `paper/erdos-hajnal-p6.tex` |
| main theorems | `EHP6.erdos_hajnal_P6_of_imported : RodlCoP6 → NssPath6 → EhP5 → NssComb → EHforP6` and `EHP6.erdos_hajnal_P6_of_cited : RodlCoP6 → EhP5 → NssComb → EHforP6` in `formal/EHP6/Final.lean`; `NssPath6` is proved (`EHP6.nss_path6_proof`) |
| their axioms | `propext`, `Classical.choice`, `Quot.sound` |
| unconditional form | `EHP6.erdos_hajnal_P6 : EHforP6`, which adds the axioms `EHP6.rodl_coP6`, `EHP6.eh_P5`, `EHP6.nss_comb` (the three cited results still assumed) |
| Lean | `leanprover/lean4:v4.34.1` (`formal/lean-toolchain`) |
| Mathlib | tag `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (`formal/lake-manifest.json`) |
| independent checks | `leanchecker --fresh`; comparator `v4.34.0` with the Lean kernel and nanoda; see `VERIFICATION.md` |
| checksums | `SHA256SUMS` (SHA-256 of every file in the repository except `SHA256SUMS` itself) |
| check outputs | `audit.txt`, `defscheck.txt`, `leanchecker.txt` and `comparator.txt` from the CI run on the release commit, attached to the GitHub release |

To verify a copy of the release:

```
sha256sum -c SHA256SUMS
cd formal
lake exe cache get && lake build
lake env lean Audit.lean
lake env leanchecker --fresh EHP6.Final
```

`Audit.lean` must list only `propext`, `Classical.choice` and `Quot.sound` for every result except
`EHP6.erdos_hajnal_P6`, which also uses `EHP6.rodl_coP6`, `EHP6.eh_P5` and `EHP6.nss_comb`, and no
`sorryAx` anywhere. `VERIFICATION.md` describes the comparator
and nanoda checks, which the CI workflow also runs.

The paper has not been refereed. Corrections will be published as new tags; this tag will not be moved.
