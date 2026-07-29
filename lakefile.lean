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

-- descriptive-complexity versions are its own semver, independent of the Lean
-- toolchain: the `~1.0.0` range (patch releases only) is exactly the set of
-- releases cut against the Mathlib pin above; `v1.0.0` is its current member.
require "descriptive-complexity" from git
  "https://github.com/PierreSenellart/descriptive-complexity" @ "v1.0.0"

@[default_target]
lean_lib «Provenance» where
  -- add any library configuration options here
