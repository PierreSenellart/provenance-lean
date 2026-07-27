import Lake
open Lake DSL

package "provenance" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    -- The library's carriers (`Tuple`, `Relation`, `KTensor`, …) are deliberately
    -- opaque `def`s; since Lean v4.31 instance search and rewriting respect
    -- transparency and cannot see through them, so restore the pre-4.31
    -- behaviour (as Mathlib does in similar situations).
    ⟨`backward.isDefEq.respectTransparency, false⟩
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ git "v4.33.0-rc1"

require "descriptive-complexity" from git
  "https://github.com/PierreSenellart/descriptive-complexity" @ "v4.33.0-rc1"

@[default_target]
lean_lib «Provenance» where
  -- add any library configuration options here
