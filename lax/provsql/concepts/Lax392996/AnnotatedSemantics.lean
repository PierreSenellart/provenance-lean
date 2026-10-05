import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Bind
import Lax392996.SemiringsWithMonus
import Lax392996.Databases
import Lax392996.AnnotatedDatabases
import Lax392996.RelationalAlgebra

/-!
---
title: Annotated semantics of the relational algebra
type: definition
---
The semantics $\langle\!\langle q \rangle\!\rangle_{\hat I}$ of a source query
$q$ on a $\mathbb{K}$-instance $\hat I$, for an m-semiring $\mathbb{K}$, clause by
clause: $\langle\!\langle R \rangle\!\rangle_{\hat
I} = \hat I(R)$; projection and selection act on the data part and carry the
annotation along; the cross product annotates $(u_1, u_2)$ by $\alpha_1
\otimes \alpha_2$; the multiset sum adds the two annotated relations;
duplicate elimination collapses the copies of a tuple into one, annotated by
the $\oplus$-sum of their annotations; and difference keeps every tuple
$(u, \alpha)$ of the left argument, annotated by $\alpha \ominus \beta$
where $\beta$ is the $\oplus$-sum of the annotations of the copies of $u$ in
the right argument. The seven claims are the clauses of the paper.
-/

namespace Lax392996.AnnotatedSemantics

open Lax392996.SemiringsWithMonus Lax392996.Databases Lax392996.AnnotatedDatabases
open Lax392996.RelationalAlgebra

variable {T : Type} [ValueType T]
variable {K : Type} [SemiringWithMonus K]

@[reducible] def Selection.evalDecidableAnnotated {n : ℕ} (φ : Selection T n) :
  DecidablePred (λ (ta: AnnotatedTuple T K n) ↦ φ.eval ta.fst) :=
    λ t => match φ.evalDecidable t.fst with
      | isTrue h  => isTrue (by simp [h])
      | isFalse h => isFalse  (by simp [h])

/-- The `⊕`-sum of the annotations of the copies of the data part `u` in an
annotated relation. -/
def annotationSum {n : ℕ} (r : Multiset (Tuple T n × K)) (u : Tuple T n) : K :=
  (Multiset.map Prod.snd
    (@Multiset.filter _ (fun p : Tuple T n × K => p.1 = u)
      (fun p => instDecidableEqTuple p.1 u) r)).sum

/-- Grouping of annotated tuples by their data part: each distinct data
part once, with the `⊕`-sum of the annotations of its copies. -/
def groupByKey {n : ℕ} (r : Multiset (Tuple T n × K)) : Multiset (Tuple T n × K) :=
  Multiset.map (fun u => (u, annotationSum r u)) (Multiset.dedup (Multiset.map Prod.fst r))

/-- Annotated (m-semiring) semantics of a source query.

The `Diff` case follows ProvSQL: every tuple slot `(u, α)` of `r₁` is kept,
with its annotation rewritten to `α ⊖ Σ β` where `Σ β` is the semiring sum of
the annotations of all copies of `u` in `r₂`. Duplicate elimination keeps
each data part once, annotated by the `⊕`-sum of the annotations of its
copies. -/
def Query.evaluateAnnotated {n : ℕ} (q: Query T n) (hq: q.source) (d: AnnotatedDatabase T K) :
    AnnotatedRelation T K n := match q with
| Query.Rel   n  s  =>
  match h : d.find n s with
  | none => (∅: Multiset (AnnotatedTuple T K n))
  | some rn => rn
| @Query.Proj _ n m ts q' =>
  let r := evaluateAnnotated q' (Query.source_proj hq rfl) d
  r.map (λ t ↦ ⟨λ k ↦ (ts k).eval t.fst, t.snd⟩)
| Query.Sel   φ  q  =>
  let r := evaluateAnnotated q (Query.source_sel hq rfl) d
  @Multiset.filter _ (λ ta ↦ φ.eval ta.fst) (Selection.evalDecidableAnnotated φ) r
| @Query.Prod _ n₁ n₂ n hn q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ (Query.source_prod hq rfl).left d
  let r₂ := evaluateAnnotated q₂ (Query.source_prod hq rfl).right d
  Multiset.map (λ (x,y) ↦ ⟨
    Eq.mp (by simp[hn]; rfl)
    (Fin.append x.fst y.fst),
    x.snd*y.snd
  ⟩) (Multiset.product r₁ r₂)
| Query.Sum   q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ (Query.source_sum hq rfl).left d
  let r₂ := evaluateAnnotated q₂ (Query.source_sum hq rfl).right d
  r₁+r₂
| Query.Dedup q     =>
  let r := evaluateAnnotated q (Query.source_dedup hq rfl) d
  groupByKey r
| Query.Diff  q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ (Query.source_diff hq rfl).left d
  let r₂ := evaluateAnnotated q₂ (Query.source_diff hq rfl).right d
  r₁.map
    λ (u,α) ↦ ⟨u, α - annotationSum r₂ u⟩
| Query.ProvSum _ _ _ => False.elim (by
  simp[Query.source] at hq
)

/-- **relation**: `⟪R⟫_Î ≝ Î(R)`. -/
axiom aeval_rel : ∀ {n : ℕ} (R : String) (hq : (Query.Rel n R).source) (d : AnnotatedDatabase T K),
  Query.evaluateAnnotated (Query.Rel n R) hq d
    = (d.find n R).getD (∅ : Multiset (AnnotatedTuple T K n))

/-- **projection**: the annotation rides along unchanged. -/
axiom aeval_proj : ∀ {n k : ℕ} (ts : Tuple (Term T k) n) (q : Query T k)
    (hq : (Query.Proj ts q).source) (d : AnnotatedDatabase T K),
  Query.evaluateAnnotated (Query.Proj ts q) hq d
    = (Query.evaluateAnnotated q (Query.source_proj hq rfl) d).map
        (fun p => ⟨fun l => (ts l).eval p.fst, p.snd⟩)

/-- **selection**: the predicate reads the data part only. -/
axiom aeval_sel : ∀ {n : ℕ} (φ : Selection T n) (q : Query T n) (hq : (Query.Sel φ q).source)
    (d : AnnotatedDatabase T K),
  Query.evaluateAnnotated (Query.Sel φ q) hq d
    = @Multiset.filter _ (fun p => φ.eval p.fst) (Selection.evalDecidableAnnotated φ)
        (Query.evaluateAnnotated q (Query.source_sel hq rfl) d)

/-- **cross product**: annotations multiply, `α ⊗ β`. -/
axiom aeval_prod : ∀ {n k₁ k₂ : ℕ} {hn : k₁ + k₂ = n} (q₁ : Query T k₁) (q₂ : Query T k₂)
    (hq : (Query.Prod (hn := hn) q₁ q₂).source) (d : AnnotatedDatabase T K),
  Query.evaluateAnnotated (Query.Prod (hn := hn) q₁ q₂) hq d
    = Multiset.map
        (fun (xy : AnnotatedTuple T K k₁ × AnnotatedTuple T K k₂) =>
          (⟨Eq.mp (by simp [hn]; rfl) (Fin.append xy.1.fst xy.2.fst), xy.1.snd * xy.2.snd⟩ :
            AnnotatedTuple T K n))
        (Multiset.product (Query.evaluateAnnotated q₁ (Query.source_prod hq rfl).left d)
          (Query.evaluateAnnotated q₂ (Query.source_prod hq rfl).right d))

/-- **multiset sum**: the two annotated relations are added. -/
axiom aeval_sum : ∀ {n : ℕ} (q₁ q₂ : Query T n) (hq : (Query.Sum q₁ q₂).source)
    (d : AnnotatedDatabase T K),
  Query.evaluateAnnotated (Query.Sum q₁ q₂) hq d
    = Query.evaluateAnnotated q₁ (Query.source_sum hq rfl).left d
      + Query.evaluateAnnotated q₂ (Query.source_sum hq rfl).right d

/-- **duplicate elimination**: the copies of a tuple are collapsed into one,
annotated by the `⊕`-sum of their annotations. -/
axiom aeval_dedup : ∀ {n : ℕ} (q : Query T n) (hq : (Query.Dedup q).source)
    (d : AnnotatedDatabase T K),
  Query.evaluateAnnotated (Query.Dedup q) hq d
    = groupByKey (Query.evaluateAnnotated q (Query.source_dedup hq rfl) d)

/-- **multiset difference**: a tuple of the left argument keeps its slot, with
annotation `α ⊖ Σβ` where `Σβ` is the `⊕`-sum of the annotations of its copies
in the right argument. -/
axiom aeval_diff : ∀ {n : ℕ} (q₁ q₂ : Query T n) (hq : (Query.Diff q₁ q₂).source)
    (d : AnnotatedDatabase T K),
  Query.evaluateAnnotated (Query.Diff q₁ q₂) hq d
    = (Query.evaluateAnnotated q₁ (Query.source_diff hq rfl).left d).map
        (fun (u, a) =>
          (u, a - annotationSum (Query.evaluateAnnotated q₂ (Query.source_diff hq rfl).right d) u))

end Lax392996.AnnotatedSemantics
