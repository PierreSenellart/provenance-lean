import Lake
open Lake DSL

package "provenance" where
  version := v!"1.1.0"
  description := "Database provenance in Lean 4: the semiring framework, an annotated relational algebra with difference and aggregation, ProvSQL's provenance-aware query rewriting, and HAVING provenance"
  keywords := #["provenance", "semirings", "databases", "relational algebra",
    "probabilistic databases", "ProvSQL"]
  homepage := "https://provsql.org/lean-docs/Provenance.html"
  license := "MIT"
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

require "leanprover-community" / "mathlib" @ git "v4.33.0"

-- descriptive-complexity versions are its own semver, independent of the Lean
-- toolchain: `v1.1.0` is cut against the Mathlib pin above, and is the floor,
-- since the complexity results import its `Encoding.BinarySubsetSum`, added
-- there. Later releases stay compatible as long as they keep that Mathlib pin.
require "descriptive-complexity" from git
  "https://github.com/PierreSenellart/descriptive-complexity" @ "v1.2.0"

@[default_target]
lean_lib «Provenance» where
  -- add any library configuration options here
