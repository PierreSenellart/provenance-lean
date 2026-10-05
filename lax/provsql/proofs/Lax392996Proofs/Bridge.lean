import Lax392996.SemiringsWithMonus
import Lax392996.WhyProvenance
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.AnnotatedDatabases
import Lax392996.RelationalAlgebra
import Lax392996.MultisetSemantics
import Lax392996.AnnotatedSemantics
import Lax392996.RewritingRules
import Lax392996.RewritingCorrectness
import Lax392996.ProbabilisticDatabases
import Lax392996.ProbabilisticEvaluation
import Lax392996Proofs.Provenance.Papers.Icde2026
import Lax392996Proofs.Provenance.Probability
import Lax392996Proofs.Provenance.QueryRewriting

/-!
# The paper's statements, from the library's theorems

Each claim is proved from the library's theorem of the same content: the
frozen restatement of the paper's claims that the library carries, the
theorem on probabilistic evaluation formalized after the paper, and and the agreement
of the concept's annotated semantics with the library's, whose grouping of
duplicates goes through a key-value list. The concepts restate the
library's other definitions, so each remaining proof is an application of
the library's theorem.
-/

universe u

namespace Lax392996Proofs.Bridge

open Lax392996.SemiringsWithMonus Lax392996.WhyProvenance Lax392996.BooleanFunctions
open Lax392996.Databases Lax392996.AnnotatedDatabases Lax392996.RelationalAlgebra
open Lax392996.MultisetSemantics Lax392996.AnnotatedSemantics
open Lax392996.RewritingRules Lax392996.RewritingCorrectness
open Lax392996.ProbabilisticDatabases Lax392996.ProbabilisticEvaluation

/-! ### Semirings with monus -/

/--
---
conclusion: Lax392996.SemiringsWithMonus.msemiring_axiom_i
---
The first equation of the paper's definition, from the library's `add_monus`.
-/
theorem msemiring_axiom_i : ∀ {K : Type} [SemiringWithMonus K] (a b : K),
    a + (b - a) = b + (a - b) :=
  fun a b => Foreign.Icde2026.msemiring_axiom_i a b

/--
---
conclusion: Lax392996.SemiringsWithMonus.msemiring_axiom_ii
---
The second equation, from the library's `monus_add`.
-/
theorem msemiring_axiom_ii : ∀ {K : Type} [SemiringWithMonus K] (a b c : K),
    ((a - b) - c) = (a - (b + c)) :=
  fun a b c => Foreign.Icde2026.msemiring_axiom_ii a b c

/--
---
conclusion: Lax392996.SemiringsWithMonus.msemiring_axiom_iii
---
The third equation, from the library's `monus_self` and `zero_monus`.
-/
theorem msemiring_axiom_iii : ∀ {K : Type} [SemiringWithMonus K] (a : K),
    ((a - a) = 0) ∧ (((0 : K) - a) = 0) :=
  fun a => Foreign.Icde2026.msemiring_axiom_iii a

/--
---
conclusion: Lax392996.SemiringsWithMonus.delta_axiom_i
---
The field `delta_zero` of the class.
-/
theorem delta_axiom_i : ∀ {K : Type} [SemiringWithMonus K],
    SemiringWithMonus.delta (0 : K) = 0 :=
  Foreign.Icde2026.delta_axiom_i

/--
---
conclusion: Lax392996.SemiringsWithMonus.delta_axiom_ii
---
The field `delta_natCast_pos` of the class.
-/
theorem delta_axiom_ii : ∀ {K : Type} [SemiringWithMonus K] {j : ℕ}, (0 < j) →
    SemiringWithMonus.delta ((j : K)) = 1 :=
  fun hj => Foreign.Icde2026.delta_axiom_ii hj

/-! ### Why-provenance -/

/--
---
conclusion: Lax392996.WhyProvenance.Why.zero_carrier
---
By definition of the instance.
-/
theorem why_zero : ∀ {α : Type}, (0 : Why α).carrier = ∅ :=
  Foreign.Icde2026.why_zero

/--
---
conclusion: Lax392996.WhyProvenance.Why.one_carrier
---
By definition of the instance.
-/
theorem why_one : ∀ {α : Type}, (1 : Why α).carrier = {∅} :=
  Foreign.Icde2026.why_one

/--
---
conclusion: Lax392996.WhyProvenance.Why.add_carrier
---
By definition of the instance.
-/
theorem why_add : ∀ {α : Type} (a b : Why α), (a + b).carrier = a.carrier ∪ b.carrier :=
  fun a b => Foreign.Icde2026.why_add a b

/--
---
conclusion: Lax392996.WhyProvenance.Why.mul_carrier
---
By definition of the instance.
-/
theorem why_mul : ∀ {α : Type} (a b : Why α),
    (a * b).carrier = {z : Set α | ∃ x y : Set α, x ∈ a.carrier ∧ y ∈ b.carrier ∧ z = x ∪ y} :=
  fun a b => Foreign.Icde2026.why_mul a b

/--
---
conclusion: Lax392996.WhyProvenance.Why.monus_carrier
---
By definition of the instance.
-/
theorem why_monus : ∀ {α : Type} (a b : Why α), (a - b).carrier = a.carrier \ b.carrier :=
  fun a b => Foreign.Icde2026.why_monus a b

/--
---
conclusion: Lax392996.WhyProvenance.Why.isMSemiring
---
The instance exhibited in the concept, whose fields verify the laws: the
Galois connection of the monus with inclusion, and the laws of a commutative
semiring under union and pairwise union.
-/
theorem why_isMSemiring : ∀ {α : Type}, Nonempty (SemiringWithMonus (Why α)) :=
  Foreign.Icde2026.why_isMSemiring

/-! ### Annotated databases -/

/--
---
conclusion: Lax392996.AnnotatedDatabases.annotated_relation_eq
---
By definition of the concept.
-/
theorem annotated_relation_eq : ∀ {T : Type} {K : Type} {n : ℕ},
    AnnotatedRelation T K n = Multiset (Tuple T n ×ₗ K) :=
  rfl

/--
---
conclusion: Lax392996.AnnotatedDatabases.annotated_database_lookup
---
By definition.
-/
theorem annotated_database_lookup : ∀ {T : Type} {K : Type} {n : ℕ}
    (R : String) (d : AnnotatedDatabase T K),
    (AnnotatedDatabase.find n R d : Option (AnnotatedRelation T K n)) = d.find n R :=
  fun _ _ => rfl

/-! ### Multiset semantics, clause by clause -/

/--
---
conclusion: Lax392996.MultisetSemantics.eval_rel
---
By unfolding the semantics.
-/
theorem eval_rel : ∀ {T : Type} [ValueType T] {n : ℕ} (R : String) (d : Database T),
    Query.evaluate (Query.Rel n R) d = (d.find n R).getD (∅ : Multiset (Tuple T n)) :=
  fun R d => Foreign.Icde2026.eval_rel R d

/--
---
conclusion: Lax392996.MultisetSemantics.eval_proj
---
By unfolding the semantics.
-/
theorem eval_proj : ∀ {T : Type} [ValueType T] {n k : ℕ} (ts : Tuple (Term T k) n) (q : Query T k)
    (d : Database T),
    Query.evaluate (Query.Proj ts q) d = (Query.evaluate q d).map (fun u l => (ts l).eval u) :=
  fun ts q d => Foreign.Icde2026.eval_proj ts q d

/--
---
conclusion: Lax392996.MultisetSemantics.eval_sel
---
By unfolding the semantics.
-/
theorem eval_sel : ∀ {T : Type} [ValueType T] {n : ℕ} (φ : Selection T n) (q : Query T n)
    (d : Database T),
    Query.evaluate (Query.Sel φ q) d = @Multiset.filter _ φ.eval φ.evalDecidable (Query.evaluate q d) :=
  fun φ q d => Foreign.Icde2026.eval_sel φ q d

/--
---
conclusion: Lax392996.MultisetSemantics.eval_prod
---
By unfolding the semantics.
-/
theorem eval_prod : ∀ {T : Type} [ValueType T] {n k₁ k₂ : ℕ} {hn : k₁ + k₂ = n}
    (q₁ : Query T k₁) (q₂ : Query T k₂) (d : Database T),
    Query.evaluate (Query.Prod (hn := hn) q₁ q₂) d
      = ((Query.evaluate q₁ d) * (Query.evaluate q₂ d)).cast hn :=
  fun q₁ q₂ d => Foreign.Icde2026.eval_prod q₁ q₂ d

/--
---
conclusion: Lax392996.MultisetSemantics.eval_sum
---
By unfolding the semantics.
-/
theorem eval_sum : ∀ {T : Type} [ValueType T] {n : ℕ} (q₁ q₂ : Query T n) (d : Database T),
    Query.evaluate (Query.Sum q₁ q₂) d = Query.evaluate q₁ d + Query.evaluate q₂ d :=
  fun q₁ q₂ d => Foreign.Icde2026.eval_sum q₁ q₂ d

/--
---
conclusion: Lax392996.MultisetSemantics.eval_dedup
---
By unfolding the semantics.
-/
theorem eval_dedup : ∀ {T : Type} [ValueType T] {n : ℕ} (q : Query T n) (d : Database T),
    Query.evaluate (Query.Dedup q) d = (Query.evaluate q d).dedup :=
  fun q d => Foreign.Icde2026.eval_dedup q d

/--
---
conclusion: Lax392996.MultisetSemantics.eval_diff
---
By unfolding the semantics.
-/
theorem eval_diff : ∀ {T : Type} [ValueType T] {n : ℕ} (q₁ q₂ : Query T n) (d : Database T)
    (r₂ : Multiset (Tuple T n)), r₂ = Query.evaluate q₂ d →
    Query.evaluate (Query.Diff q₁ q₂) d = (Query.evaluate q₁ d).filter (fun u => u ∉ r₂) :=
  fun q₁ q₂ d r₂ hr => Foreign.Icde2026.eval_diff q₁ q₂ d r₂ hr

/-! ### Annotated semantics, clause by clause -/

/--
---
conclusion: Lax392996.AnnotatedSemantics.aeval_rel
---
By unfolding the definition.
-/
theorem aeval_rel : ∀ {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K]
    {n : ℕ} (R : String) (hq : (Query.Rel n R).source) (d : AnnotatedDatabase T K),
    Lax392996.AnnotatedSemantics.Query.evaluateAnnotated (Query.Rel n R) hq d
      = (d.find n R).getD (∅ : Multiset (AnnotatedTuple T K n)) :=
  by
    intro T _ K _ n R hq d
    rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated]; cases d.find n R <;> rfl

/--
---
conclusion: Lax392996.AnnotatedSemantics.aeval_proj
---
By unfolding the definition.
-/
theorem aeval_proj : ∀ {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K]
    {n k : ℕ} (ts : Tuple (Term T k) n) (q : Query T k)
    (hq : (Query.Proj ts q).source) (d : AnnotatedDatabase T K),
    Lax392996.AnnotatedSemantics.Query.evaluateAnnotated (Query.Proj ts q) hq d
      = (Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q (Query.source_proj hq rfl) d).map
          (fun p => ⟨fun l => (ts l).eval p.fst, p.snd⟩) :=
  fun ts q hq d => by rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated]

/--
---
conclusion: Lax392996.AnnotatedSemantics.aeval_sel
---
By unfolding the definition.
-/
theorem aeval_sel : ∀ {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K]
    {n : ℕ} (φ : Selection T n) (q : Query T n) (hq : (Query.Sel φ q).source)
    (d : AnnotatedDatabase T K),
    Lax392996.AnnotatedSemantics.Query.evaluateAnnotated (Query.Sel φ q) hq d
      = @Multiset.filter _ (fun p => φ.eval p.fst) (Selection.evalDecidableAnnotated φ)
          (Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q (Query.source_sel hq rfl) d) :=
  fun φ q hq d => by rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated]

/--
---
conclusion: Lax392996.AnnotatedSemantics.aeval_prod
---
By unfolding the definition.
-/
theorem aeval_prod : ∀ {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K]
    {n k₁ k₂ : ℕ} {hn : k₁ + k₂ = n} (q₁ : Query T k₁) (q₂ : Query T k₂)
    (hq : (Query.Prod (hn := hn) q₁ q₂).source) (d : AnnotatedDatabase T K),
    Lax392996.AnnotatedSemantics.Query.evaluateAnnotated (Query.Prod (hn := hn) q₁ q₂) hq d
      = Multiset.map
          (fun (xy : AnnotatedTuple T K k₁ × AnnotatedTuple T K k₂) =>
            (⟨Eq.mp (by simp [hn]; rfl) (Fin.append xy.1.fst xy.2.fst), xy.1.snd * xy.2.snd⟩ :
              AnnotatedTuple T K n))
          (Multiset.product (Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q₁ (Query.source_prod hq rfl).left d)
            (Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q₂ (Query.source_prod hq rfl).right d)) :=
  fun q₁ q₂ hq d => by rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated]; rfl

/--
---
conclusion: Lax392996.AnnotatedSemantics.aeval_sum
---
By unfolding the definition.
-/
theorem aeval_sum : ∀ {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K]
    {n : ℕ} (q₁ q₂ : Query T n) (hq : (Query.Sum q₁ q₂).source) (d : AnnotatedDatabase T K),
    Lax392996.AnnotatedSemantics.Query.evaluateAnnotated (Query.Sum q₁ q₂) hq d
      = Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q₁ (Query.source_sum hq rfl).left d
        + Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q₂ (Query.source_sum hq rfl).right d :=
  fun q₁ q₂ hq d => by rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated]

/--
---
conclusion: Lax392996.AnnotatedSemantics.aeval_dedup
---
By unfolding the definition.
-/
theorem aeval_dedup : ∀ {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K]
    {n : ℕ} (q : Query T n) (hq : (Query.Dedup q).source) (d : AnnotatedDatabase T K),
    Lax392996.AnnotatedSemantics.Query.evaluateAnnotated (Query.Dedup q) hq d
      = Lax392996.AnnotatedSemantics.groupByKey (Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q (Query.source_dedup hq rfl) d) :=
  fun q hq d => by rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated]

/--
---
conclusion: Lax392996.AnnotatedSemantics.aeval_diff
---
By unfolding the definition.
-/
theorem aeval_diff : ∀ {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K]
    {n : ℕ} (q₁ q₂ : Query T n) (hq : (Query.Diff q₁ q₂).source) (d : AnnotatedDatabase T K),
    Lax392996.AnnotatedSemantics.Query.evaluateAnnotated (Query.Diff q₁ q₂) hq d
      = (Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q₁ (Query.source_diff hq rfl).left d).map
          (fun (u, a) =>
            (u, a - Lax392996.AnnotatedSemantics.annotationSum (Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q₂ (Query.source_diff hq rfl).right d) u)) :=
  fun q₁ q₂ hq d => by rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated]; rfl

/-! ### The rewriting rules -/

/--
---
conclusion: Lax392996.RewritingRules.rule_projection
---
By unfolding the rewriting.
-/
theorem rule_projection : ∀ {T : Type} [ValueType T] {K : Type} {n k : ℕ} (ts : Tuple (Term T k) n)
    (q : Query T k) (hq : (Query.Proj ts q).source),
    Query.rewriting (K := K) (Query.Proj ts q) hq
      = Query.Proj
          (fun l : Fin (n + 1) =>
            if h : (l : ℕ) < n then (ts ⟨l, h⟩).castToAnnotatedTuple
            else Term.index (Fin.last q.arity))
          (Query.rewriting q (Query.source_proj hq rfl)) :=
  fun ts q hq => Foreign.Icde2026.rule_projection ts q hq

/--
---
conclusion: Lax392996.RewritingRules.rule_product
---
By unfolding the rewriting.
-/
theorem rule_product : ∀ {T : Type} [ValueType T] {K : Type} {n n₁ n₂ : ℕ} {hn : n₁ + n₂ = n}
    (q₁ : Query T n₁) (q₂ : Query T n₂) (hq : (Query.Prod (hn := hn) q₁ q₂).source),
    Query.rewriting (K := K) (Query.Prod (hn := hn) q₁ q₂) hq
      = Query.Proj
          (fun l : Fin (n + 1) =>
            if (l : ℕ) < n₁ then Term.index (l.castLE (by simp))
            else if ((l : ℕ) < n : Prop) then Term.index (Fin.ofNat _ ((l : ℕ) + 1))
            else Term.mul (Term.index (Fin.ofNat _ n₁)) (Term.index (Fin.ofNat _ (n + 1))))
          (@Query.Prod (T ⊕ K) (n₁ + 1) (n₂ + 1) (n + 2) (by omega)
            (Query.rewriting q₁ (Query.source_prod hq rfl).left)
            (Query.rewriting q₂ (Query.source_prod hq rfl).right)) :=
  fun q₁ q₂ hq => Foreign.Icde2026.rule_product q₁ q₂ hq

/--
---
conclusion: Lax392996.RewritingRules.rule_dupelim
---
By unfolding the rewriting.
-/
theorem rule_dupelim : ∀ {T : Type} [ValueType T] {K : Type} {n : ℕ} (q : Query T n)
    (hq : (Query.Dedup q).source),
    Query.rewriting (K := K) (Query.Dedup q) hq
      = Query.ProvSum (fun l : Fin n => l.castLE (by simp)) (Term.index (Fin.last n))
          (Query.rewriting q (Query.source_dedup hq rfl)) :=
  fun q hq => Foreign.Icde2026.rule_dupelim q hq

/--
---
conclusion: Lax392996.RewritingRules.rule_difference
---
By unfolding the rewriting.
-/
theorem rule_difference : ∀ {T : Type} [ValueType T] {K : Type} {n : ℕ} (q₁ q₂ : Query T n)
    (hq : (Query.Diff q₁ q₂).source),
    Query.rewriting (K := K) (Query.Diff q₁ q₂) hq
      = (let q'₁ := Query.rewriting (K := K) q₁ (Query.source_diff hq rfl).left
         let q'₂ := Query.rewriting (K := K) q₂ (Query.source_diff hq rfl).right
         let joinCond₁ :=
           ((List.range n).map
             (fun j => @Selection.BT (T ⊕ K) (2 * n + 1)
               (BoolTerm.EQ (Term.index (Fin.ofNat _ j)) (Term.index (Fin.ofNat _ (j + n + 1)))))).foldr
             (fun t t' => Selection.And t t') Selection.True
         let prod₁t := fun r => Query.Sel joinCond₁ (@Query.Prod _ (n + 1) n (2 * n + 1) (by omega) q'₁ r)
         let prod₁r :=
           Query.Dedup (Query.Diff
             (Query.Proj (fun j : Fin n => Term.index (j.castLE (Nat.le_succ _))) q'₁)
             (Query.Proj (fun j : Fin n => Term.index (j.castLE (Nat.le_succ _))) q'₂))
         let prod₁ := prod₁t prod₁r
         let joinCond₂ :=
           ((List.range n).map
             (fun j => @Selection.BT (T ⊕ K) (2 * n + 2)
               (BoolTerm.EQ (Term.index (Fin.ofNat _ j)) (Term.index (Fin.ofNat _ (j + n + 1)))))).foldr
             (fun t t' => Selection.And t t') Selection.True
         let prod₂t := fun r => Query.Sel joinCond₂ (@Query.Prod _ (n + 1) (n + 1) (2 * n + 2) (by omega) q'₁ r)
         let prod₂r := Query.ProvSum (fun j : Fin n => j.castLE (by simp)) (Term.index (Fin.last n)) q'₂
         let prod₂ := prod₂t prod₂r
         let ts₁ := fun j : Fin (n + 1) => Term.index (j.castLE (by omega))
         let ts₂ := fun j : Fin (n + 1) =>
           if (j : ℕ) < n then Term.index (j.castLE (by omega))
           else Term.sub (Term.index (Fin.ofNat _ n)) (Term.index (Fin.last (2 * n + 1)))
         Query.Sum (Query.Proj ts₁ prod₁) (Query.Proj ts₂ prod₂)) :=
  fun q₁ q₂ hq => Foreign.Icde2026.rule_difference q₁ q₂ hq

/-! ### The concept's annotated semantics is the library's

The concept groups the copies of a data part directly, by a map over the
distinct data parts; the library folds the annotated tuples into a
key-value list. The two agree, by the library's own characterization of
its key-value list as a multiset. -/

/-- The concept's grouping is the library's key-value list, as a multiset. -/
theorem groupByKey_eq {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K] [DecidableEq K]
    {n : ℕ} (r : AnnotatedRelation T K n) :
    Lax392996.AnnotatedSemantics.groupByKey r = Multiset.ofList (Foreign.groupByKey r).val := by
  rw [show (Multiset.ofList (Foreign.groupByKey r).val : Multiset (Tuple T n × K)) = _ from
    Foreign.groupByKey_multiset_eq r]
  rfl

/-- The concept's annotation sum is the value the library's key-value list
holds at a data part, `0` when it holds none. -/
theorem annotationSum_eq {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K] [DecidableEq K]
    {n : ℕ} (r : AnnotatedRelation T K n) (u : Tuple T n) :
    Lax392996.AnnotatedSemantics.annotationSum r u
      = (((Foreign.groupByKey r).val.find? (·.1 = u)).map Prod.snd).getD 0 := by
  rw [Foreign.Query.rewriting_valid_find_getD_eq_sum]
  rfl

/-- The two annotated semantics agree on every source query. -/
theorem evaluateAnnotated_eq {T : Type} [ValueType T] {K : Type} [SemiringWithMonus K]
    [DecidableEq K] : ∀ {n : ℕ} (q : Query T n) (hq : q.source) (d : AnnotatedDatabase T K),
    Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q hq d
      = Foreign.Query.evaluateAnnotated q hq d := by
  intro n q
  induction q with
  | Rel n s =>
    intro hq d
    rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated, Foreign.Query.evaluateAnnotated]
    rfl
  | Proj ts q ih =>
    intro hq d
    rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated, Foreign.Query.evaluateAnnotated, ih]
  | Sel φ q ih =>
    intro hq d
    rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated, Foreign.Query.evaluateAnnotated, ih]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq d
    rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated, Foreign.Query.evaluateAnnotated,
      ih₁, ih₂]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq d
    rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated, Foreign.Query.evaluateAnnotated,
      ih₁, ih₂]
  | Dedup q ih =>
    intro hq d
    rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated, Foreign.Query.evaluateAnnotated,
      ih, groupByKey_eq]
    rfl
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq d
    rw [Lax392996.AnnotatedSemantics.Query.evaluateAnnotated, Foreign.Query.evaluateAnnotated,
      ih₁, ih₂]
    simp only [annotationSum_eq]
    rfl
  | ProvSum _ _ _ =>
    intro hq
    simp [Query.source] at hq
  | Having _ _ _ _ _ _ _ =>
    intro hq
    simp [Query.source] at hq

/-! ### Correctness of the rewriting, and probabilistic evaluation -/

/--
---
conclusion: Lax392996.RewritingCorrectness.rewriting_valid
---
The library's theorem, by structural induction on the query: each rule is
shown to commute with the composite reading of the annotated semantics,
the difference rule through the two semijoin identities of the library.
-/
theorem rewriting_valid : ∀ {T : Type} [ValueType T] {K : Type} {n : ℕ}
    [SemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
    (q : Query T n) (hq : q.source) (d : AnnotatedDatabase T K),
    (Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q hq d).toComposite
      = Query.evaluate (Query.rewriting q hq) d.toComposite :=
  fun q hq d => by rw [evaluateAnnotated_eq]; exact Foreign.Icde2026.rewriting_valid q hq d

/--
---
conclusion: Lax392996.ProbabilisticEvaluation.theorem_12
---
The library's theorem: the random world of the annotated answer is the
answer on the random world, by induction on the query, and the
disjunctive annotation of a tuple holds at a valuation exactly when the
tuple belongs to that random world.
-/
theorem theorem_12 : ∀ {X : Type} [Fintype X] [DecidableEq X] {T : Type} [ValueType T]
    (P : ProbAssignment X) {n : ℕ} (q : Query T n) (hq : q.source)
    (Î : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n),
    ProbAssignment.marginalProb P q Î t
      = ProbAssignment.funcProb P (tupleAnnotation (Lax392996.AnnotatedSemantics.Query.evaluateAnnotated q hq Î) t) :=
  by intro X _ _ T _ P n q hq Î t; rw [evaluateAnnotated_eq]; exact Foreign.ProbAssignment.theorem_12 P q hq Î t

end Lax392996Proofs.Bridge
