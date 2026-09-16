import Lake
open Lake DSL

package «tablet» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Tablet» where
  srcDir := "."

-- The advertised statement surface a mathematical reader audits (deliberate `sorry`s).
@[default_target]
lean_lib «Challenge» where
  srcDir := "."
  roots := #[`Challenge]

-- The same declarations, proved from `Tablet`.
@[default_target]
lean_lib «Solution» where
  srcDir := "."
  roots := #[`Solution]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "db584cd6d46c92f209a44c0f1c829460d327499d"
