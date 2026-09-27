import Lake
open Lake DSL

package «ehp6» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

@[default_target]
lean_lib «EHP6» where

-- used only by the comparator check (see VERIFICATION.md)
lean_lib Challenge where

lean_lib Solution where
