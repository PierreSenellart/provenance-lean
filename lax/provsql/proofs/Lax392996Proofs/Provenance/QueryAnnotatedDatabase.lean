import Std.Data.HashMap.Lemmas

import Lax392996Proofs.Provenance.AnnotatedDatabase
import Lax392996Proofs.Provenance.Query
import Lax392996Proofs.Provenance.Util.KeyAccValueList
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

namespace Lax392996.RelationalAlgebra.Query
end Lax392996.RelationalAlgebra.Query

namespace Lax392996Proofs.Foreign
end Lax392996Proofs.Foreign

namespace Lax392996Proofs.Foreign.Query
end Lax392996Proofs.Foreign.Query

namespace Lax392996.RelationalAlgebra.Selection
export Lax392996.AnnotatedSemantics.Selection (evalDecidableAnnotated)
end Lax392996.RelationalAlgebra.Selection

/-!
# Query semantics over annotated databases

This file defines the evaluation of relational algebra queries over annotated databases.
Query operators are lifted to annotated relations using the m-semiring operations of the
annotation domain `K`: addition corresponds to union, multiplication to join, and
monus to difference. This is the algebra of Section IV-B of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*][sen2026provsql], itself an adaptation of
[Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance] to
multiset semantics with explicit duplicate elimination and multiset difference.

## Main definitions

* `Query.evaluateAnnotated` – evaluates a query over an `AnnotatedDatabase T K`,
  propagating annotations through each relational operator according to the semiring
  structure of `K`

## References

* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Section IV-B)
* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
-/

variable {T: Type} [Lax392996.Databases.ValueType T]

variable {K: Type} [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K]

def _root_.Lax392996Proofs.Foreign.groupByKey (m : Multiset (Lax392996.Databases.Tuple T n × K)) :=
  m.foldr Lax392996Proofs.Foreign.KeyValueList.addKVFold ⟨[], by simp[Lax392996Proofs.Foreign.KeyValueList]⟩

export Lax392996Proofs.Foreign (groupByKey)

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
/-- Annotated (m-semiring) semantics of a non-aggregation query.

The `Diff` case follows ProvSQL: every tuple slot `(u, α)` of `r₁` is *kept*,
with its annotation rewritten to `α ⊖ Σ β` where `Σ β` is the semiring sum of
the annotations of all copies of `u` in `r₂`. Two consequences worth noting:

* difference never removes tuple slots (only annotations change, possibly to
  `0`), so the data part of the result is insensitive to `Diff` – this is
  made precise in `Provenance.QueryAdequacy`;
* each copy of `u` in `r₁` separately gets the full grouped sum subtracted,
  so the result is not invariant under regrouping extensionally equal
  annotated relations: over `ℕ`, `{(t,1),(t,1)} ∖ {(t,1)}` has total
  annotation `0` while `{(t,2)} ∖ {(t,1)}` has total annotation `1`. As a
  consequence, over `ℕ` the annotated semantics agrees with the
  all-or-nothing plain difference of `Query.evaluate` on `0`/`1`-annotated
  inputs, but not once `Dedup` has accumulated annotations
  (see `Nat.counterexample_diff_adequacy`). -/
def _root_.Lax392996Proofs.Foreign.Query.evaluateAnnotated (q: Lax392996.RelationalAlgebra.Query T n) (hq: q.source) (d: Lax392996.AnnotatedDatabases.AnnotatedDatabase T K) : Lax392996.AnnotatedDatabases.AnnotatedRelation T K n := match q with
| Rel   n  s  =>
  match h : d.find n s with
  | none => (∅: Multiset (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n))
  | some rn => rn
| @Proj _ n m ts q' =>
  let r := Lax392996Proofs.Foreign.Query.evaluateAnnotated q' (Lax392996Proofs.Foreign.Query.sourceProj hq rfl) d
  r.map (λ t ↦ ⟨λ k ↦ (ts k).eval t.fst, t.snd⟩)
| Sel   φ  q  =>
  let r := Lax392996Proofs.Foreign.Query.evaluateAnnotated q (Lax392996Proofs.Foreign.Query.sourceSel hq rfl) d
  @Multiset.filter _ (λ ta ↦ φ.eval ta.fst) φ.evalDecidableAnnotated r
| @Prod _ n₁ n₂ n hn q₁ q₂ =>
  let r₁ := Lax392996Proofs.Foreign.Query.evaluateAnnotated q₁ (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).left d
  let r₂ := Lax392996Proofs.Foreign.Query.evaluateAnnotated q₂ (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).right d
  Multiset.map (λ (x,y) ↦ ⟨
    Eq.mp (by simp[hn]; rfl)
    (Fin.append x.fst y.fst),
    x.snd*y.snd
  ⟩) (Multiset.product r₁ r₂)
| Sum   q₁ q₂ =>
  let r₁ := Lax392996Proofs.Foreign.Query.evaluateAnnotated q₁ (Lax392996Proofs.Foreign.Query.sourceSum hq rfl).left d
  let r₂ := Lax392996Proofs.Foreign.Query.evaluateAnnotated q₂ (Lax392996Proofs.Foreign.Query.sourceSum hq rfl).right d
  r₁+r₂
| Dedup q     =>
  let r := Lax392996Proofs.Foreign.Query.evaluateAnnotated q (Lax392996Proofs.Foreign.Query.sourceDedup hq rfl) d
  Multiset.ofList ((Lax392996Proofs.Foreign.groupByKey r).val)
| Diff  q₁ q₂ =>
  let r₁ := Lax392996Proofs.Foreign.Query.evaluateAnnotated q₁ (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).left d
  let r₂ := Lax392996Proofs.Foreign.Query.evaluateAnnotated q₂ (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).right d
  let grouped₂ := Lax392996Proofs.Foreign.groupByKey r₂
  r₁.map
    λ (u,α) ↦ ⟨u, α - (((grouped₂.val.find? (·.1=u)).map Prod.snd).getD 0)⟩
| ProvSum _ _ _ => False.elim (by
  simp[Lax392996.RelationalAlgebra.Query.source] at hq
)

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (evaluateAnnotated)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (evaluateAnnotated)
end Query


