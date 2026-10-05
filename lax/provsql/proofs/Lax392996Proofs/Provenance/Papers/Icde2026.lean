/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Lax392996Proofs.Provenance.QueryRewriting
import Lax392996Proofs.Provenance.Semirings.Why
import Lax392996.AnnotatedDatabases
import Lax392996.AnnotatedSemantics
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.MultisetSemantics
import Lax392996.ProbabilisticDatabases
import Lax392996.RelationalAlgebra
import Lax392996.RewritingRules
import Lax392996.SemiringsWithMonus
import Lax392996.WhyProvenance

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace Lax392996.AnnotatedSemantics.Selection
end Lax392996.AnnotatedSemantics.Selection

namespace Lax392996.MultisetSemantics.Query
end Lax392996.MultisetSemantics.Query

namespace Lax392996.RewritingRules.Query
end Lax392996.RewritingRules.Query

namespace Lax392996Proofs.Foreign.Icde2026
end Lax392996Proofs.Foreign.Icde2026

namespace Lax392996.RelationalAlgebra.Query
export Lax392996.MultisetSemantics.Query (evaluate)
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query
export Lax392996.RewritingRules.Query (rewriting)
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Selection
export Lax392996.AnnotatedSemantics.Selection (evalDecidableAnnotated)
end Lax392996.RelationalAlgebra.Selection

/-!
# Frozen restatement of the claims of a published paper

[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*, ICDE 2026][sen2026provsql] links to this
library: eight of its definitions and results carry a hyperlink to a declaration
page under <https://provsql.org/lean-docs/>, and the paper as a whole links to
the landing page. Those links are in a PDF and cannot be fixed after the fact.

There is one published documentation tree, and it tracks `main`, so the paper's
links deliberately reach material that has grown *beyond* the paper. What has to
be guaranteed is therefore narrower, and sharper, than "the docs still match the
paper":

1. the anchors still exist – checked by `scripts/check-anchors.sh`, which reads
   the `Anchor:` lines below;
2. the declarations they land on still **subsume** the paper's claims – checked
   by this file.

This module is what makes the second half mechanical. Each claim the paper makes
is restated here *in the paper's own form* and proved by applying the library
declaration the paper cites. If the library generalizes – a wider fragment, an
extra hypothesis discharged, a fused operator – the proof still goes through,
which is the right answer: the paper's claim is still there, subsumed. If a
statement is ever *weakened*, this file stops compiling and `lake build` fails.
No textual or anchor-level check distinguishes those two cases.

The statements below are therefore **frozen**: they were fixed when the paper
was published and are never edited to follow the library. Only the proof terms
may be re-plumbed. `scripts/release.sh check` compares this file against the
hash in `scripts/icde2026.sha256`, so an edit is a deliberate act that shows up
in a diff rather than a silent drift.

## Scope

Two places where the library and the paper are not literally coextensive, both
recorded here rather than papered over:

* The paper's relational algebra has an aggregation former
  `γ_{i₁,…,i_m}[t₁:f₁,…,t_n:f_n]`, and its rewriting has a rule (R5) for it.
  `Query`, the declaration the paper's grammar links to, is the *classical*
  syntax: it carries the operators of RA⁺(∖) plus `ProvSum`, the ⊕-aggregation
  that rules (R1)–(R4) emit. General aggregation, and the rewriting rule for it,
  live on the kind-indexed syntax (`AggQuery.Gamma`, and the bare-grouping
  rewriting of `Provenance.AggQueryGroupRewriting`), which did not exist when
  the paper was written. This module deliberately does not import those: a
  frozen file should depend on as little as possible, and what it must pin is
  what the paper's anchors name.
* Accordingly, the rewriting correctness theorem restated below carries the
  hypothesis `q.source`, the fragment (R1)–(R4) covers.

Anchor: Provenance.html
-/

namespace Icde2026

set_option linter.unusedSectionVars false

variable {T : Type} [Lax392996.Databases.ValueType T] {K : Type} {α : Type} {n n₁ n₂ k k₁ k₂ : ℕ}

/-! ## Semirings with monus

The paper defines an m-semiring by three equations. In the library the monus is
axiomatized instead by its Galois connection `a ⊖ b ≤ c ↔ a ≤ b ⊕ c`, which is
strictly stronger: the three equations are theorems. That is exactly the shape
of drift this file is meant to allow – a *generalization* of the cited
declaration keeps these proofs one-liners.
-/

open Lax392996Proofs.Foreign.Icde2026 in
/-- The paper's m-semiring axiom (i): `a ⊕ (b ⊖ a) = b ⊕ (a ⊖ b)`.

Anchor: Provenance/SemiringWithMonus.html#SemiringWithMonus -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.msemiring_axiom_i [Lax392996.SemiringsWithMonus.SemiringWithMonus K] (a b : K) :
    a + (b - a) = b + (a - b) :=
  Lax392996Proofs.Foreign.add_monus a b

export Lax392996Proofs.Foreign.Icde2026 (msemiring_axiom_i)

open Lax392996Proofs.Foreign.Icde2026 in
/-- The paper's m-semiring axiom (ii): `(a ⊖ b) ⊖ c = a ⊖ (b ⊕ c)`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.msemiring_axiom_ii [Lax392996.SemiringsWithMonus.SemiringWithMonus K] (a b c : K) :
    ((a - b) - c) = (a - (b + c)) :=
  (Lax392996Proofs.Foreign.monus_add a b c).symm

export Lax392996Proofs.Foreign.Icde2026 (msemiring_axiom_ii)

open Lax392996Proofs.Foreign.Icde2026 in
/-- The paper's m-semiring axiom (iii): `a ⊖ a = 𝟘 ⊖ a = 𝟘`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.msemiring_axiom_iii [Lax392996.SemiringsWithMonus.SemiringWithMonus K] (a : K) :
    ((a - a) = 0) ∧ (((0 : K) - a) = 0) :=
  ⟨Lax392996Proofs.Foreign.monus_self a, Lax392996Proofs.Foreign.zero_monus a⟩

export Lax392996Proofs.Foreign.Icde2026 (msemiring_axiom_iii)

open Lax392996Proofs.Foreign.Icde2026 in
/-- The paper's δ-semiring axiom (i): `δ(𝟘) = 𝟘`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.delta_axiom_i [Lax392996.SemiringsWithMonus.SemiringWithMonus K] :
    Lax392996.SemiringsWithMonus.SemiringWithMonus.delta (0 : K) = 0 :=
  Lax392996.SemiringsWithMonus.SemiringWithMonus.delta_zero

export Lax392996Proofs.Foreign.Icde2026 (delta_axiom_i)

open Lax392996Proofs.Foreign.Icde2026 in
/-- The paper's δ-semiring axiom (ii): `δ(𝟙 ⊕ ⋯ ⊕ 𝟙) = 𝟙`, whatever the number
of `𝟙`s. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.delta_axiom_ii [Lax392996.SemiringsWithMonus.SemiringWithMonus K] {j : ℕ} (hj : 0 < j) :
    Lax392996.SemiringsWithMonus.SemiringWithMonus.delta ((j : K)) = 1 :=
  Lax392996.SemiringsWithMonus.SemiringWithMonus.delta_natCast_pos hj

export Lax392996Proofs.Foreign.Icde2026 (delta_axiom_ii)

/-! ## Why-provenance

The paper's proposition: for a set `X`, the structure
`(2^(2^X), ∅, {∅}, ∪, ⋓, ∖)` is an m-semiring. Exhibiting the instance is only
half of that – the operations have to be the stated ones – so each of the six is
pinned separately.
-/

open Lax392996Proofs.Foreign.Icde2026 in
/-- Why-provenance: `𝟘` is `∅`.

Anchor: Provenance/Semirings/Why.html#instSemiringWithMonusWhy -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.why_zero : (0 : Lax392996.WhyProvenance.Why α).carrier = ∅ := rfl

export Lax392996Proofs.Foreign.Icde2026 (why_zero)

open Lax392996Proofs.Foreign.Icde2026 in
/-- Why-provenance: `𝟙` is `{∅}`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.why_one : (1 : Lax392996.WhyProvenance.Why α).carrier = {∅} := rfl

export Lax392996Proofs.Foreign.Icde2026 (why_one)

open Lax392996Proofs.Foreign.Icde2026 in
/-- Why-provenance: `⊕` is union of families. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.why_add (a b : Lax392996.WhyProvenance.Why α) : (a + b).carrier = a.carrier ∪ b.carrier := rfl

export Lax392996Proofs.Foreign.Icde2026 (why_add)

open Lax392996Proofs.Foreign.Icde2026 in
/-- Why-provenance: `⊗` is `⋓`, the pairwise union of witnesses. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.why_mul (a b : Lax392996.WhyProvenance.Why α) :
    (a * b).carrier
      = {z : Set α | ∃ x y : Set α, x ∈ a.carrier ∧ y ∈ b.carrier ∧ z = x ∪ y} :=
  rfl

export Lax392996Proofs.Foreign.Icde2026 (why_mul)

open Lax392996Proofs.Foreign.Icde2026 in
/-- Why-provenance: `⊖` is set difference of families. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.why_monus (a b : Lax392996.WhyProvenance.Why α) : (a - b).carrier = a.carrier \ b.carrier := rfl

export Lax392996Proofs.Foreign.Icde2026 (why_monus)

open Lax392996Proofs.Foreign.Icde2026 in
/-- Why-provenance is an m-semiring under exactly those operations. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.why_isMSemiring : Nonempty (Lax392996.SemiringsWithMonus.SemiringWithMonus (Lax392996.WhyProvenance.Why α)) :=
  ⟨Lax392996.WhyProvenance.instSemiringWithMonusWhy⟩

export Lax392996Proofs.Foreign.Icde2026 (why_isMSemiring)

/-! ## Annotated databases

The paper: a `K`-relation of arity `k` is a finite multiset of `k`-tuples each
carrying an annotation from `K`, and a `K`-instance over a schema `D` maps each
relation name `R` to a `K`-relation of arity `D(R)`.
-/

/-! ## The relational algebra `RA_k`

Each clause of the paper's grammar, as the typing rule it is. Each is proved by
exhibiting the corresponding constructor of `Query`.

Anchor: Provenance/Query.html#Query
-/

/-! ## Plain multiset semantics

The paper's `⟦·⟧_I`, clause by clause.

Anchor: Provenance/Query.html#Query.evaluate
-/

open Lax392996Proofs.Foreign.Icde2026 in
/-- **relation**: `⟦R⟧_I ≝ I(R)`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.eval_rel (R : String) (d : Lax392996.Databases.Database T) :
    (Lax392996.RelationalAlgebra.Query.Rel n R).evaluate d = (d.find n R).getD (∅ : Multiset (Lax392996.Databases.Tuple T n)) := by
  rw [Lax392996.MultisetSemantics.Query.evaluate]; cases d.find n R <;> rfl

export Lax392996Proofs.Foreign.Icde2026 (eval_rel)

open Lax392996Proofs.Foreign.Icde2026 in
/-- **projection**: `⟦Π_{t₁,…,t_n}(q)⟧_I ≝ {|(t₁(u),…,t_n(u)) | u ∈ ⟦q⟧_I|}`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.eval_proj (ts : Lax392996.Databases.Tuple (Lax392996.RelationalAlgebra.Term T k) n) (q : Lax392996.RelationalAlgebra.Query T k) (d : Lax392996.Databases.Database T) :
    (Lax392996.RelationalAlgebra.Query.Proj ts q).evaluate d = (q.evaluate d).map (fun u l => (ts l).eval u) := by
  rw [Lax392996.MultisetSemantics.Query.evaluate]

export Lax392996Proofs.Foreign.Icde2026 (eval_proj)

open Lax392996Proofs.Foreign.Icde2026 in
/-- **selection**: `⟦σ_φ(q)⟧_I ≝ {|u | u ∈ ⟦q⟧_I, φ(u)|}`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.eval_sel (φ : Lax392996.RelationalAlgebra.Selection T n) (q : Lax392996.RelationalAlgebra.Query T n) (d : Lax392996.Databases.Database T) :
    (Lax392996.RelationalAlgebra.Query.Sel φ q).evaluate d
      = @Multiset.filter _ φ.eval φ.evalDecidable (q.evaluate d) := by
  rw [Lax392996.MultisetSemantics.Query.evaluate]

export Lax392996Proofs.Foreign.Icde2026 (eval_sel)

open Lax392996Proofs.Foreign.Icde2026 in
/-- **cross product**: `⟦q₁ × q₂⟧_I ≝ ⟦q₁⟧_I × ⟦q₂⟧_I`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.eval_prod {hn : k₁ + k₂ = n} (q₁ : Lax392996.RelationalAlgebra.Query T k₁) (q₂ : Lax392996.RelationalAlgebra.Query T k₂) (d : Lax392996.Databases.Database T) :
    (Lax392996.RelationalAlgebra.Query.Prod (hn := hn) q₁ q₂).evaluate d
      = ((q₁.evaluate d) * (q₂.evaluate d)).cast hn := by
  rw [Lax392996.MultisetSemantics.Query.evaluate]

export Lax392996Proofs.Foreign.Icde2026 (eval_prod)

open Lax392996Proofs.Foreign.Icde2026 in
/-- **multiset sum**: `⟦q₁ ⊎ q₂⟧_I ≝ ⟦q₁⟧_I ⊎ ⟦q₂⟧_I`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.eval_sum (q₁ q₂ : Lax392996.RelationalAlgebra.Query T n) (d : Lax392996.Databases.Database T) :
    (Lax392996.RelationalAlgebra.Query.Sum q₁ q₂).evaluate d = q₁.evaluate d + q₂.evaluate d := by
  rw [Lax392996.MultisetSemantics.Query.evaluate]

export Lax392996Proofs.Foreign.Icde2026 (eval_sum)

open Lax392996Proofs.Foreign.Icde2026 in
/-- **duplicate elimination**: `⟦ε(q)⟧_I` maps `t` to `1` when `⟦q⟧_I(t) > 0`
and to `0` otherwise. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.eval_dedup (q : Lax392996.RelationalAlgebra.Query T n) (d : Lax392996.Databases.Database T) :
    (Lax392996.RelationalAlgebra.Query.Dedup q).evaluate d = (q.evaluate d).dedup := by
  rw [Lax392996.MultisetSemantics.Query.evaluate]

export Lax392996Proofs.Foreign.Icde2026 (eval_dedup)

open Lax392996Proofs.Foreign.Icde2026 in
/-- **multiset difference**: every copy of a tuple occurring at all in `⟦q₂⟧_I`
is removed from `⟦q₁⟧_I`. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.eval_diff (q₁ q₂ : Lax392996.RelationalAlgebra.Query T n) (d : Lax392996.Databases.Database T) (r₂ : Multiset (Lax392996.Databases.Tuple T n))
    (hr : r₂ = q₂.evaluate d) :
    (Lax392996.RelationalAlgebra.Query.Diff q₁ q₂).evaluate d = (q₁.evaluate d).filter (fun u => u ∉ r₂) := by
  subst hr; rw [Lax392996.MultisetSemantics.Query.evaluate]

export Lax392996Proofs.Foreign.Icde2026 (eval_diff)

/-! ## Semantics over annotated databases

The paper's `⟪·⟫_Î`: the same operators, with `⊕` on multiset sum and duplicate
elimination, `⊗` on cross product, and `⊖` on difference.

Anchor: Provenance/QueryAnnotatedDatabase.html#Query.evaluateAnnotated
-/

section Annotated

variable [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K]

end Annotated

/-! ## The rewriting rules (R1)–(R4)

The paper gives five rules; (R5), aggregation, is not part of this classical
rewriting (see *Scope* above). Each rule below is stated as the equation it is:
applying the rewriting to an operator produces exactly the paper's right-hand
side. The annotation lives in the last column, so a query of arity `n` rewrites
to one of arity `n+1`.

Anchor: Provenance/QueryRewriting.html#query.Rewriting
-/

open Lax392996Proofs.Foreign.Icde2026 in
open Lax392996.RelationalAlgebra.Query in
/-- **(R1) projection.** `Π_{t₁,…,t_n}(q)` is rewritten to
`Π_{t₁,…,t_n,#(k+1)}(q̂)`: the terms are carried over unchanged and the
annotation column of the rewritten argument is appended. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.rule_projection (ts : Lax392996.Databases.Tuple (Lax392996.RelationalAlgebra.Term T k) n) (q : Lax392996.RelationalAlgebra.Query T k)
    (hq : (Lax392996.RelationalAlgebra.Query.Proj ts q).source) :
    (Lax392996.RelationalAlgebra.Query.Proj ts q).rewriting (K := K) hq
      = Lax392996.RelationalAlgebra.Query.Proj
          (fun l : Fin (n + 1) =>
            if h : (l : ℕ) < n then (ts ⟨l, h⟩).castToAnnotatedTuple
            else Lax392996.RelationalAlgebra.Term.index (Fin.last q.arity))
          (q.rewriting (Lax392996Proofs.Foreign.Query.sourceProj hq rfl)) :=
  rfl

export Lax392996Proofs.Foreign.Icde2026 (rule_projection)

open Lax392996Proofs.Foreign.Icde2026 in
open Lax392996.RelationalAlgebra.Query in
/-- **(R2) cross product.** `q₁ × q₂` is rewritten to
`Π_{#1,…,#k₁,#(k₁+2),…,#(k₁+k₂+1),#(k₁+1) ⊗ #(k₁+k₂+2)}(q̂₁ × q̂₂)`: the two
data blocks are kept, the two annotation columns are multiplied. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.rule_product {hn : n₁ + n₂ = n} (q₁ : Lax392996.RelationalAlgebra.Query T n₁) (q₂ : Lax392996.RelationalAlgebra.Query T n₂)
    (hq : (Lax392996.RelationalAlgebra.Query.Prod (hn := hn) q₁ q₂).source) :
    (Lax392996.RelationalAlgebra.Query.Prod (hn := hn) q₁ q₂).rewriting (K := K) hq
      = Lax392996.RelationalAlgebra.Query.Proj
          (fun l : Fin (n + 1) =>
            if (l : ℕ) < n₁ then #(l.castLE (by simp))
            else if ((l : ℕ) < n : Prop) then #(Fin.ofNat _ ((l : ℕ) + 1))
            else Lax392996.RelationalAlgebra.Term.mul #(Fin.ofNat _ n₁) #(Fin.ofNat _ (n + 1)))
          (@Lax392996.RelationalAlgebra.Query.Prod (T ⊕ K) (n₁ + 1) (n₂ + 1) (n + 2) (by omega)
            (q₁.rewriting (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).left)
            (q₂.rewriting (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).right)) :=
  rfl

export Lax392996Proofs.Foreign.Icde2026 (rule_product)

open Lax392996Proofs.Foreign.Icde2026 in
open Lax392996.RelationalAlgebra.Query in
/-- **(R3) duplicate elimination.** `ε(q)` is rewritten to
`γ_{1,…,k}[#(k+1) : ⊕](q̂)`: group by the data columns and `⊕`-sum the
annotation column. This is the rule that makes duplicate elimination the
`⊕`-gate creator, and `ProvSum` is its target operator. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.rule_dupelim (q : Lax392996.RelationalAlgebra.Query T n) (hq : (Lax392996.RelationalAlgebra.Query.Dedup q).source) :
    (Lax392996.RelationalAlgebra.Query.Dedup q).rewriting (K := K) hq
      = Lax392996.RelationalAlgebra.Query.ProvSum (fun l : Fin n => l.castLE (by simp)) #(Fin.last n)
          (q.rewriting (Lax392996Proofs.Foreign.Query.sourceDedup hq rfl)) :=
  rfl

export Lax392996Proofs.Foreign.Icde2026 (rule_dupelim)

open Lax392996Proofs.Foreign.Icde2026 in
open Lax392996.RelationalAlgebra.Query in
/-- **(R4) multiset difference.** `q₁ - q₂` is rewritten to the multiset sum of
two branches: the tuples of `q̂₁` whose data part survives the set difference of
the two data projections, carrying their annotation unchanged; and the tuples of
`q̂₁` matched against the `⊕`-aggregated `q̂₂`, carrying `α ⊖ Σβ`. Both branches
are joins on the `k` data columns. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.rule_difference (q₁ q₂ : Lax392996.RelationalAlgebra.Query T n) (hq : (Lax392996.RelationalAlgebra.Query.Diff q₁ q₂).source) :
    (Lax392996.RelationalAlgebra.Query.Diff q₁ q₂).rewriting (K := K) hq
      = (let q'₁ := q₁.rewriting (K := K) (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).left
         let q'₂ := q₂.rewriting (K := K) (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).right
         let joinCond₁ :=
           ((List.range n).map
             (fun j => @Lax392996.RelationalAlgebra.Selection.BT (T ⊕ K) (2 * n + 1)
               (#(Fin.ofNat _ j) == #(Fin.ofNat _ (j + n + 1))))).foldr
             (fun t t' => Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True
         let prod₁t := fun r => Lax392996.RelationalAlgebra.Query.Sel joinCond₁ (@Lax392996.RelationalAlgebra.Query.Prod _ (n + 1) n (2 * n + 1) (by omega) q'₁ r)
         let prod₁r :=
           Lax392996.RelationalAlgebra.Query.Dedup (Lax392996.RelationalAlgebra.Query.Diff (Lax392996.RelationalAlgebra.Query.Proj (fun j : Fin n => Lax392996.RelationalAlgebra.Term.index (j.castLE (Nat.le_succ _))) q'₁)
                       (Lax392996.RelationalAlgebra.Query.Proj (fun j : Fin n => Lax392996.RelationalAlgebra.Term.index (j.castLE (Nat.le_succ _))) q'₂))
         let prod₁ := prod₁t prod₁r
         let joinCond₂ :=
           ((List.range n).map
             (fun j => @Lax392996.RelationalAlgebra.Selection.BT (T ⊕ K) (2 * n + 2)
               (#(Fin.ofNat _ j) == #(Fin.ofNat _ (j + n + 1))))).foldr
             (fun t t' => Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True
         let prod₂t := fun r => Lax392996.RelationalAlgebra.Query.Sel joinCond₂ (@Lax392996.RelationalAlgebra.Query.Prod _ (n + 1) (n + 1) (2 * n + 2) (by omega) q'₁ r)
         let prod₂r := Lax392996.RelationalAlgebra.Query.ProvSum (fun j : Fin n => j.castLE (by simp)) #(Fin.last n) q'₂
         let prod₂ := prod₂t prod₂r
         let ts₁ := fun j : Fin (n + 1) => #(j.castLE (by omega))
         let ts₂ := fun j : Fin (n + 1) =>
           if (j : ℕ) < n then #(j.castLE (by omega))
           else Lax392996.RelationalAlgebra.Term.sub #(Fin.ofNat _ n) #(Fin.last (2 * n + 1))
         Sum (Lax392996.RelationalAlgebra.Query.Proj ts₁ prod₁) (Lax392996.RelationalAlgebra.Query.Proj ts₂ prod₂)) :=
  rfl

export Lax392996Proofs.Foreign.Icde2026 (rule_difference)

/-! ## Correctness of the rewriting

The paper's theorem: let `D` be a schema, `q` a query over `D`, `K` an
appropriate algebraic structure, `Î` a `K`-instance over `D`, and `q̂` the query
obtained by applying the rewriting rules recursively bottom up. Then
`⟪q⟫_Î = ⟦q̂⟧_Î`.

The equality is between an annotated relation and a plain one, so it is stated
through the encoding that puts the annotation in the last column
(`toComposite`), which is what "the same relation" means once the rewriting has
moved the annotation into the data.

Anchor: Provenance/QueryRewriting.html#Query.rewriting_valid
-/

open Lax392996Proofs.Foreign.Icde2026 in
/-- `⟪q⟫_Î = ⟦q̂⟧_Î`, for `q` in the fragment the rules (R1)–(R4) cover. -/
theorem _root_.Lax392996Proofs.Foreign.Icde2026.rewriting_valid [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] [Lax392996.SemiringsWithMonus.HasAltLinearOrder K]
    (q : Lax392996.RelationalAlgebra.Query T n) (hq : q.source) (d : Lax392996.AnnotatedDatabases.AnnotatedDatabase T K) :
    (q.evaluateAnnotated hq d).toComposite = (q.rewriting hq).evaluate d.toComposite :=
  Lax392996Proofs.Foreign.Query.rewriting_valid q hq d

export Lax392996Proofs.Foreign.Icde2026 (rewriting_valid)

end Icde2026


