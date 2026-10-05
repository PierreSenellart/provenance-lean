import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Fin.VecNotation
import Lax392996.Databases
import Lax392996.RelationalAlgebra

/-!
---
title: Multiset semantics of the relational algebra
type: definition
---
The semantics $[\![q]\!]_I$ of a query $q$ on a database $I$, clause by
clause: $[\![R]\!]_I = I(R)$; $[\![\Pi_{t_1, \dots, t_n}(q)]\!]_I =
\{\!|(t_1(u), \dots, t_n(u)) \mid u \in [\![q]\!]_I|\!\}$;
$[\![\sigma_\varphi(q)]\!]_I = \{\!|u \in [\![q]\!]_I \mid \varphi(u)|\!\}$;
$[\![q_1 \times q_2]\!]_I = [\![q_1]\!]_I \times [\![q_2]\!]_I$; $[\![q_1
\uplus q_2]\!]_I = [\![q_1]\!]_I \uplus [\![q_2]\!]_I$; $[\![\varepsilon(q)]\!]_I$
keeps one copy of each tuple of $[\![q]\!]_I$; and $[\![q_1 - q_2]\!]_I$
removes from $[\![q_1]\!]_I$ every copy of a tuple occurring in
$[\![q_2]\!]_I$. The definition also interprets the two extra operators:
the provenance aggregation $\gamma$ sums its term over each group of the
key columns, and the fused `HAVING` operator computes its aggregates over
each group read in the canonical tuple order. The seven claims are the
clauses of the paper.
-/

namespace Lax392996.MultisetSemantics

open Lax392996.Databases Lax392996.RelationalAlgebra

variable {T : Type} [ValueType T]

/-- Addition as a binary function, the fold of the `⊕`-sum performed by
the provenance aggregation `Query.ProvSum`. -/
def addFn (a b : T) := a + b

instance instCommutativeAddFn : @Std.Commutative T addFn where
  comm := add_comm

instance instAssociativeAddFn : @Std.Associative T addFn where
  assoc := add_assoc

/-- The occurrences of the group of key `g` in relation `r`: the multiset of
matching tuples, as a list sorted by the canonical linear order on tuples.
The sort order plays the role of the ordering along which
non-commutative sequence aggregates read the occurrences of a group; for
commutative aggregates it is irrelevant. -/
def Relation.groupSeq {m n₁ : ℕ} (is : Tuple (Fin m) n₁) (r : Relation T m) (g : Tuple T n₁) :
    List (Tuple T m) :=
  Multiset.sort
    (@Multiset.filter _ (fun u => ∀ k' : Fin n₁, u (is k') = g k')
      (fun u => @Nat.decidableForallFin n₁ (fun k' => u (is k') = g k') (fun _ => inferInstance)) r)
    (· ≤ ·)

/-- Multiset semantics of a query over a plain database.

The `Diff` case is all-or-nothing difference: every copy of a tuple that
occurs at all in `r₂` is removed from `r₁`, which is what the monus-based
annotated semantics of difference gives on `0`/`1`-annotated inputs. -/
def Query.evaluate {n : ℕ} (q: Query T n) (d: Database T): Relation T n := match q with
| Query.Rel   n  s  =>
  match d.find n s with
  | none => (∅: Multiset (Tuple T n))
  | some rn => rn
| Query.Proj ts q => let r := evaluate q d; Multiset.map (λ t ↦ λ k ↦ (ts k).eval t) r
| Query.Sel   φ  q  => let r := evaluate q d; @Multiset.filter _ φ.eval φ.evalDecidable r
| @Query.Prod _ n₁ n₂ n hn q₁ q₂ =>
  let r₁ := evaluate q₁ d
  let r₂ := evaluate q₂ d
  (r₁ * r₂).cast hn
| Query.Sum   q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ + r₂
| Query.Dedup q     => let r := evaluate q d; Multiset.dedup r
| Query.Diff  q₁ q₂ =>
  let r₁ := evaluate q₁ d
  let r₂ : Multiset (Tuple T _) := evaluate q₂ d
  r₁.filter (fun t ↦ t ∉ r₂)
| @Query.ProvSum _ m n₁ is t q =>
    let r := evaluate (Query.Dedup (Query.Proj (λ (k: Fin n₁) ↦ Term.index (is k)) q)) d
    let s := evaluate q d
    r.map (λ g ↦ Fin.append g (
      λ _: Fin 1 ↦ (
        (@Multiset.filter _ (λ u ↦ ∀ k': Fin n₁, u (is k') = g k')
          (fun u => @Nat.decidableForallFin n₁ (fun k' => u (is k') = g k') (fun _ => inferInstance))
          s).map (λ u ↦ t.eval u)
      ).fold addFn 0
    ))
| @Query.Having _ m n₁ n₂ is ts fs op l s q =>
    let keys := evaluate (Query.Dedup (Query.Proj (λ (k: Fin n₁) ↦ Term.index (is k)) q)) d
    let r := evaluate q d
    Multiset.map
      (λ g ↦ Fin.append g
        (λ (k: Fin n₂) ↦ (fs k) ((Relation.groupSeq is r g).map (ts k).eval)))
      (@Multiset.filter _
        (λ g ↦ op.eval ((fs l) ((Relation.groupSeq is r g).map (ts l).eval)) (s.eval g))
        (fun g => instDecidableEval op _ _)
        keys)
termination_by q.aggdepth2_plus_depth
decreasing_by
  all_goals simp[Query.aggdepth2_plus_depth]
  any_goals refine Nat.lt_add_one_of_le ?_
  any_goals exact Nat.le_max_left _ _
  any_goals exact Nat.le_max_right _ _

/-- **relation**: `⟦R⟧_I ≝ I(R)`. -/
axiom eval_rel : ∀ {n : ℕ} (R : String) (d : Database T),
  Query.evaluate (Query.Rel n R) d = (d.find n R).getD (∅ : Multiset (Tuple T n))

/-- **projection**: `⟦Π_{t₁,…,t_n}(q)⟧_I ≝ {|(t₁(u),…,t_n(u)) | u ∈ ⟦q⟧_I|}`. -/
axiom eval_proj : ∀ {n k : ℕ} (ts : Tuple (Term T k) n) (q : Query T k) (d : Database T),
  Query.evaluate (Query.Proj ts q) d = (Query.evaluate q d).map (fun u l => (ts l).eval u)

/-- **selection**: `⟦σ_φ(q)⟧_I ≝ {|u | u ∈ ⟦q⟧_I, φ(u)|}`. -/
axiom eval_sel : ∀ {n : ℕ} (φ : Selection T n) (q : Query T n) (d : Database T),
  Query.evaluate (Query.Sel φ q) d = @Multiset.filter _ φ.eval φ.evalDecidable (Query.evaluate q d)

/-- **cross product**: `⟦q₁ × q₂⟧_I ≝ ⟦q₁⟧_I × ⟦q₂⟧_I`. -/
axiom eval_prod : ∀ {n k₁ k₂ : ℕ} {hn : k₁ + k₂ = n} (q₁ : Query T k₁) (q₂ : Query T k₂) (d : Database T),
  Query.evaluate (Query.Prod (hn := hn) q₁ q₂) d = ((Query.evaluate q₁ d) * (Query.evaluate q₂ d)).cast hn

/-- **multiset sum**: `⟦q₁ ⊎ q₂⟧_I ≝ ⟦q₁⟧_I ⊎ ⟦q₂⟧_I`. -/
axiom eval_sum : ∀ {n : ℕ} (q₁ q₂ : Query T n) (d : Database T),
  Query.evaluate (Query.Sum q₁ q₂) d = Query.evaluate q₁ d + Query.evaluate q₂ d

/-- **duplicate elimination**: `⟦ε(q)⟧_I` maps `t` to `1` when `⟦q⟧_I(t) > 0`
and to `0` otherwise. -/
axiom eval_dedup : ∀ {n : ℕ} (q : Query T n) (d : Database T),
  Query.evaluate (Query.Dedup q) d = (Query.evaluate q d).dedup

/-- **multiset difference**: every copy of a tuple occurring at all in `⟦q₂⟧_I`
is removed from `⟦q₁⟧_I`. -/
axiom eval_diff : ∀ {n : ℕ} (q₁ q₂ : Query T n) (d : Database T) (r₂ : Multiset (Tuple T n)),
  r₂ = Query.evaluate q₂ d →
    Query.evaluate (Query.Diff q₁ q₂) d = (Query.evaluate q₁ d).filter (fun u => u ∉ r₂)

end Lax392996.MultisetSemantics
