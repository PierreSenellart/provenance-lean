import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Prod.Lex

import Lax392996Proofs.Provenance.Algorithms.CompOp
import Lax392996Proofs.Provenance.Database
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

namespace Lax392996.MultisetSemantics.Query
end Lax392996.MultisetSemantics.Query

namespace Lax392996.MultisetSemantics.Relation
end Lax392996.MultisetSemantics.Relation

namespace Lax392996.RelationalAlgebra.BoolTerm
end Lax392996.RelationalAlgebra.BoolTerm

namespace Lax392996.RelationalAlgebra.Query
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Selection
end Lax392996.RelationalAlgebra.Selection

namespace Lax392996.RelationalAlgebra.Term
end Lax392996.RelationalAlgebra.Term

namespace Lax392996Proofs.Foreign.BoolTerm
end Lax392996Proofs.Foreign.BoolTerm

namespace Lax392996Proofs.Foreign.Query
end Lax392996Proofs.Foreign.Query

namespace Lax392996Proofs.Foreign.Selection
end Lax392996Proofs.Foreign.Selection

namespace Lax392996Proofs.Foreign.SeqAggFunc
end Lax392996Proofs.Foreign.SeqAggFunc

namespace Lax392996Proofs.Foreign.Term
end Lax392996Proofs.Foreign.Term

namespace Lax392996.RelationalAlgebra.Query
export Lax392996.MultisetSemantics.Query (evaluate)
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.Databases.Relation
export Lax392996.MultisetSemantics.Relation (groupSeq)
end Lax392996.Databases.Relation

/-!
# Relational algebra

This file defines the abstract syntax and semantics of relational algebra queries over
plain (unannotated) databases. The language is the *extended relational algebra*
described in Section III of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*][sen2026provsql], with multiset semantics,
explicit duplicate elimination, multiset difference, and aggregation.

## Main definitions

* `Term T n` – an expression that evaluates to a value of type `T` in the context of
  a tuple of arity `n` (constants, tuple projections, and arithmetic operations)
* `Query T` – a relational algebra query: selection, projection, union, join,
  difference, and renaming
* `Query.evaluate` – the standard set semantics of queries over `Database T`

## References

* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Section III)
-/

variable {T: Type} [Lax392996.Databases.ValueType T]

namespace Lax392996.RelationalAlgebra.Term

open Lax392996Proofs.Foreign.Term in
theorem _root_.Lax392996Proofs.Foreign.Term.castToAnnotatedTuple_eval [Lax392996.SemiringsWithMonus.HasAltLinearOrder K] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] (t: Lax392996.RelationalAlgebra.Term T n) (tuple: Lax392996.Databases.Tuple T n) :
∀ α: K,
  t.castToAnnotatedTuple.eval (Fin.append (λ k ↦ Sum.inl (tuple k)) ![Sum.inr α]) = Sum.inl (t.eval tuple) := by
  intro α
  induction t with
  | const c =>
    unfold Lax392996.RelationalAlgebra.Term.castToAnnotatedTuple Lax392996.RelationalAlgebra.Term.eval
    simp
  | index k =>
    unfold Lax392996.RelationalAlgebra.Term.castToAnnotatedTuple Lax392996.RelationalAlgebra.Term.eval
    have hk : k.castLT (lt_trans k.isLt (lt_add_one n)) = Fin.castAdd 1 k := rfl
    rw[hk]
    rw[Fin.append_left]
  | add t₁ t₂ ih₁ ih₂ =>
    unfold Lax392996.RelationalAlgebra.Term.castToAnnotatedTuple Lax392996.RelationalAlgebra.Term.eval
    rw[ih₁, ih₂]
    simp[(·+·),Add.add]
  | sub t₁ t₂ ih₁ ih₂ =>
    unfold Lax392996.RelationalAlgebra.Term.castToAnnotatedTuple Lax392996.RelationalAlgebra.Term.eval
    rw[ih₁, ih₂]
    simp[(·-·),Sub.sub]
  | mul t₁ t₂ ih₁ ih₂ =>
    unfold Lax392996.RelationalAlgebra.Term.castToAnnotatedTuple Lax392996.RelationalAlgebra.Term.eval
    rw[ih₁, ih₂]
    simp[(·*·),Mul.mul]

end Lax392996.RelationalAlgebra.Term

namespace Lax392996.RelationalAlgebra.Term

export Lax392996Proofs.Foreign.Term (castToAnnotatedTuple_eval)

end Lax392996.RelationalAlgebra.Term

namespace Term
export Lax392996Proofs.Foreign.Term (castToAnnotatedTuple_eval)
end Term

instance _root_.Lax392996Proofs.Foreign.instCoeTerm : Coe T (Lax392996.RelationalAlgebra.Term T n) where
  coe a:= Lax392996.RelationalAlgebra.Term.const a

instance _root_.Lax392996Proofs.Foreign.instOfNatTermNat : OfNat (Lax392996.RelationalAlgebra.Term ℕ n) (a: ℕ) where
  ofNat := Lax392996.RelationalAlgebra.Term.const a

namespace Lax392996Proofs
prefix:max "#" => Lax392996.RelationalAlgebra.Term.index
end Lax392996Proofs

namespace Lax392996Proofs
infix:20 " == " => λ x y ↦ Lax392996.RelationalAlgebra.BoolTerm.EQ x y
end Lax392996Proofs

namespace Lax392996Proofs
infix:20 " != " => λ x y ↦ Lax392996.RelationalAlgebra.BoolTerm.NE x y
end Lax392996Proofs

namespace Lax392996Proofs
infix:20 " <= " => λ x y ↦ Lax392996.RelationalAlgebra.BoolTerm.LE x y
end Lax392996Proofs

namespace Lax392996Proofs
infix:20 " < " => λ x y ↦ Lax392996.RelationalAlgebra.BoolTerm.LT x y
end Lax392996Proofs

namespace Lax392996Proofs
infix:20 " >= " => λ x y ↦ Lax392996.RelationalAlgebra.BoolTerm.GE x y
end Lax392996Proofs

namespace Lax392996Proofs
infix:20 " > " => λ x y ↦ Lax392996.RelationalAlgebra.BoolTerm.GT x y
end Lax392996Proofs

namespace Lax392996.RelationalAlgebra.BoolTerm

open Lax392996Proofs.Foreign.BoolTerm in
theorem _root_.Lax392996Proofs.Foreign.BoolTerm.castToAnnotatedTuple_eval [Lax392996.SemiringsWithMonus.HasAltLinearOrder K] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] (t: Lax392996.RelationalAlgebra.BoolTerm T n) (tuple: Lax392996.Databases.Tuple T n) :
  ∀ α: K, t.castToAnnotatedTuple.eval (Fin.append (λ k ↦ Sum.inl (tuple k)) ![Sum.inr α]) = t.eval tuple := by
    intro α
    induction t with
    | EQ t₁ t₂ =>
      unfold Lax392996.RelationalAlgebra.BoolTerm.eval Lax392996.RelationalAlgebra.BoolTerm.castToAnnotatedTuple
      simp
      repeat rw[Lax392996Proofs.Foreign.Term.castToAnnotatedTuple_eval]
      simp
    | NE t₁ t₂ =>
      unfold Lax392996.RelationalAlgebra.BoolTerm.eval Lax392996.RelationalAlgebra.BoolTerm.castToAnnotatedTuple
      simp
      repeat rw[Lax392996Proofs.Foreign.Term.castToAnnotatedTuple_eval]
      simp
    | LE t₁ t₂ =>
      unfold Lax392996.RelationalAlgebra.BoolTerm.eval Lax392996.RelationalAlgebra.BoolTerm.castToAnnotatedTuple
      simp
      repeat rw[Lax392996Proofs.Foreign.Term.castToAnnotatedTuple_eval]
      exact ge_iff_le
    | LT t₁ t₂ =>
      unfold Lax392996.RelationalAlgebra.BoolTerm.eval Lax392996.RelationalAlgebra.BoolTerm.castToAnnotatedTuple
      simp
      repeat rw[Lax392996Proofs.Foreign.Term.castToAnnotatedTuple_eval]
      simp[LT.lt]
      exact le_of_lt
    | GE t₁ t₂ =>
      unfold Lax392996.RelationalAlgebra.BoolTerm.eval Lax392996.RelationalAlgebra.BoolTerm.castToAnnotatedTuple
      simp
      repeat rw[Lax392996Proofs.Foreign.Term.castToAnnotatedTuple_eval]
      exact ge_iff_le
    | GT t₁ t₂ =>
      unfold Lax392996.RelationalAlgebra.BoolTerm.eval Lax392996.RelationalAlgebra.BoolTerm.castToAnnotatedTuple
      simp
      repeat rw[Lax392996Proofs.Foreign.Term.castToAnnotatedTuple_eval]
      simp[LT.lt]
      exact le_of_lt

end Lax392996.RelationalAlgebra.BoolTerm

namespace Lax392996.RelationalAlgebra.BoolTerm

export Lax392996Proofs.Foreign.BoolTerm (castToAnnotatedTuple_eval)

end Lax392996.RelationalAlgebra.BoolTerm

namespace BoolTerm
export Lax392996Proofs.Foreign.BoolTerm (castToAnnotatedTuple_eval)
end BoolTerm

namespace Lax392996.RelationalAlgebra.Selection

open Lax392996Proofs.Foreign.Selection in
theorem _root_.Lax392996Proofs.Foreign.Selection.castToAnnotatedTuple_eval [Lax392996.SemiringsWithMonus.HasAltLinearOrder K] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] (φ: Lax392996.RelationalAlgebra.Selection T n) (tuple: Lax392996.Databases.Tuple T n) :
∀ α: K,
  φ.castToAnnotatedTuple.eval (Fin.append (λ k ↦ Sum.inl (tuple k)) ![Sum.inr α]) = φ.eval tuple := by
    intro α
    induction φ with
    | BT t =>
      simp[Lax392996.RelationalAlgebra.Selection.eval,Lax392996.RelationalAlgebra.Selection.castToAnnotatedTuple]
      rw[Lax392996Proofs.Foreign.BoolTerm.castToAnnotatedTuple_eval]
    | Not φ ih =>
      simp[Lax392996.RelationalAlgebra.Selection.eval,Lax392996.RelationalAlgebra.Selection.castToAnnotatedTuple]
      rw[ih]
    | And φ₁ φ₂ ih₁ ih₂ =>
      simp[Lax392996.RelationalAlgebra.Selection.eval,Lax392996.RelationalAlgebra.Selection.castToAnnotatedTuple]
      rw[ih₁,ih₂]
    | Or φ₁ φ₂ ih₁ ih₂ =>
      simp[Lax392996.RelationalAlgebra.Selection.eval,Lax392996.RelationalAlgebra.Selection.castToAnnotatedTuple]
      rw[ih₁,ih₂]
    | True => trivial

end Lax392996.RelationalAlgebra.Selection

namespace Lax392996.RelationalAlgebra.Selection

export Lax392996Proofs.Foreign.Selection (castToAnnotatedTuple_eval)

end Lax392996.RelationalAlgebra.Selection

namespace Selection
export Lax392996Proofs.Foreign.Selection (castToAnnotatedTuple_eval)
end Selection

instance _root_.Lax392996Proofs.Foreign.instCoeBoolTermSelection : Coe (Lax392996.RelationalAlgebra.BoolTerm T n) (Lax392996.RelationalAlgebra.Selection T n) where
  coe bt := Lax392996.RelationalAlgebra.Selection.BT bt

namespace SeqAggFunc

end SeqAggFunc

set_option linter.unusedSectionVars false

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
@[simp]
theorem _root_.Lax392996Proofs.Foreign.Query.sourceProd {q: Lax392996.RelationalAlgebra.Query T n} :
  q.source → ∀ {n₁} {q₁: Lax392996.RelationalAlgebra.Query T n₁} {q₂: Lax392996.RelationalAlgebra.Query T n₂} {hn: n₁+n₂=n}
    (_: q = @Lax392996.RelationalAlgebra.Query.Prod T n₁ n₂ n hn q₁ q₂), q₁.source ∧ q₂.source  := by
    intro hna n₁ q₁ q₂ hn₁ hq
    unfold Lax392996.RelationalAlgebra.Query.source at hna
    simp[hq] at hna
    assumption

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (sourceProd)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (sourceProd)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
@[simp]
theorem _root_.Lax392996Proofs.Foreign.Query.sourceSum {q: Lax392996.RelationalAlgebra.Query T n} :
  q.source → ∀ {q₁: Lax392996.RelationalAlgebra.Query T n} {q₂: Lax392996.RelationalAlgebra.Query T n} (_: q = Lax392996.RelationalAlgebra.Query.Sum q₁ q₂), q₁.source ∧ q₂.source  := by
    intro hna q₁ q₂ hq
    unfold Lax392996.RelationalAlgebra.Query.source at hna
    simp[hq] at hna
    assumption

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (sourceSum)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (sourceSum)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
@[simp]
theorem _root_.Lax392996Proofs.Foreign.Query.sourceDiff {q: Lax392996.RelationalAlgebra.Query T n} :
  q.source → ∀ {q₁: Lax392996.RelationalAlgebra.Query T n} {q₂: Lax392996.RelationalAlgebra.Query T n} (_: q = Lax392996.RelationalAlgebra.Query.Diff q₁ q₂), q₁.source ∧ q₂.source  := by
    intro hna q₁ q₂ hq
    unfold Lax392996.RelationalAlgebra.Query.source at hna
    simp[hq] at hna
    assumption

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (sourceDiff)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (sourceDiff)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
@[simp]
theorem _root_.Lax392996Proofs.Foreign.Query.sourceProj {q: Lax392996.RelationalAlgebra.Query T n} :
  q.source → ∀ {m} {t} {q': Lax392996.RelationalAlgebra.Query T m} (_: q = Lax392996.RelationalAlgebra.Query.Proj t q'), q'.source := by
    intro hna m t q' hq
    unfold Lax392996.RelationalAlgebra.Query.source at hna
    rw[hq] at hna
    assumption

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (sourceProj)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (sourceProj)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
@[simp]
theorem _root_.Lax392996Proofs.Foreign.Query.sourceSel {q: Lax392996.RelationalAlgebra.Query T n} :
  q.source → ∀ {φ} {q': Lax392996.RelationalAlgebra.Query T n} (_: q = Lax392996.RelationalAlgebra.Query.Sel φ q'), q'.source := by
    intro hna φ q' hq
    unfold Lax392996.RelationalAlgebra.Query.source at hna
    rw[hq] at hna
    assumption

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (sourceSel)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (sourceSel)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
@[simp]
theorem _root_.Lax392996Proofs.Foreign.Query.sourceDedup {q: Lax392996.RelationalAlgebra.Query T n} :
  q.source → ∀ {q': Lax392996.RelationalAlgebra.Query T n} (_: q = Lax392996.RelationalAlgebra.Query.Dedup q'), q'.source := by
    intro hna q' hq
    unfold Lax392996.RelationalAlgebra.Query.source at hna
    rw[hq] at hna
    assumption

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (sourceDedup)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (sourceDedup)
end Query

namespace Lax392996Proofs
prefix:max "Π " => Lax392996.RelationalAlgebra.Query.Proj
end Lax392996Proofs

namespace Lax392996Proofs
prefix:max "σ " => Lax392996.RelationalAlgebra.Query.Sel
end Lax392996Proofs

namespace Lax392996Proofs
infix:80 " × " => Lax392996.RelationalAlgebra.Query.Prod
end Lax392996Proofs

namespace Lax392996Proofs
infix:50 " ⊎ " => Lax392996.RelationalAlgebra.Query.Sum
end Lax392996Proofs

namespace Lax392996Proofs
prefix:max "ε " => Lax392996.RelationalAlgebra.Query.Dedup
end Lax392996Proofs

namespace Lax392996Proofs
infix:50 " - " => Lax392996.RelationalAlgebra.Query.Diff
end Lax392996Proofs

namespace Lax392996Proofs
infix:1020 " ⋈ " => λ q₁ φ ↦ λ q₂ ↦ (σ φ) (q₁ × q₂)
end Lax392996Proofs

namespace Lax392996Proofs
infix:50 " ∪ " => λ q₁ q₂ ↦ ε (q₁ ⊎ q₂)
end Lax392996Proofs


