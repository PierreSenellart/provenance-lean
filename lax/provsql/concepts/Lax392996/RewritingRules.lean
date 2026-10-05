import Mathlib.Data.Fin.VecNotation
import Lax392996.Databases
import Lax392996.RelationalAlgebra

/-!
---
title: The provenance-aware rewriting of queries
type: definition
---
The rewriting $\hat q$ of a source query $q$ of arity $k$ into a query of
arity $k+1$ over $\mathcal{V} \uplus \mathbb{K}$ whose last column carries
the annotation, defined bottom up by the rules of the paper: (R1) a
projection $\Pi_{t_1, \dots, t_n}(q)$ becomes $\Pi_{t_1, \dots, t_n,
\#(k+1)}(\hat q)$; (R2) a cross product $q_1 \times q_2$ becomes
$\Pi_{\#1, \dots, \#k_1, \#(k_1+2), \dots, \#(k_1+k_2+1), \#(k_1+1) \otimes
\#(k_1+k_2+2)}(\hat q_1 \times \hat q_2)$; (R3) a duplicate elimination
$\varepsilon(q)$ becomes $\gamma_{1, \dots, k}[\#(k+1) : \oplus](\hat q)$, the
grouping by the data columns with the $\oplus$-sum of the annotation column;
(R4) a difference $q_1 - q_2$ becomes the multiset sum of the tuples of
$\hat q_1$ whose data part survives the set difference of the data
projections, annotation unchanged, and the tuples of $\hat q_1$ joined with
the $\oplus$-aggregated $\hat q_2$ on the data columns, annotated by $\alpha
\ominus \sum \beta$. Relation names, selections and multiset sums are rewritten
homomorphically. The four claims are the rules as the equations they are.
-/

namespace Lax392996.RewritingRules

open Lax392996.Databases Lax392996.RelationalAlgebra

variable {T : Type}

/-- The rewriting of a source query, rules (R1) to (R4) applied bottom up. -/
def Query.rewriting {n : ℕ} {K : Type} [ValueType T] (q: Query T n) (hq: q.source) :
    Query (T⊕K) (n+1) := match q with
| Query.Rel   n  s  => Query.Rel (n+1) s
| Query.Proj  ts q  =>
  let ts :=
    (λ (k: Fin (n+1)) => if h : ↑k<n then (ts ⟨k,h⟩).castToAnnotatedTuple
                         else Term.index (Fin.last q.arity))
  Query.Proj ts (rewriting q (Query.source_proj hq rfl))
| Query.Sel   φ  q  => Query.Sel φ.castToAnnotatedTuple (rewriting q (Query.source_sel hq rfl))
| @Query.Prod T n₁ n₂ n hn q₁ q₂ =>
  let tmp :=
    @Query.Prod (T⊕K) (n₁+1) (n₂+1) (n+2) (by omega) (rewriting q₁ (Query.source_prod hq rfl).left)
  let product := tmp (rewriting q₂ (Query.source_prod hq rfl).right)
  let ts : Tuple (Term (T⊕K) (n+2)) (n+1) :=
    (λ k: Fin (n+1) =>
      if ↑k<n₁ then Term.index (k.castLE (by simp))
    else if (↑k<n: Prop) then Term.index (Fin.ofNat _ (↑k+1))
    else Term.mul (Term.index (Fin.ofNat _ n₁)) (Term.index (Fin.ofNat _ (n+1))))
  Query.Proj ts product
| Query.Sum   q₁ q₂ =>
  Query.Sum (rewriting q₁ (Query.source_sum hq rfl).left) (rewriting q₂ (Query.source_sum hq rfl).right)
| Query.Dedup q     =>
  let q' := rewriting q (Query.source_dedup hq rfl)
  Query.ProvSum (λ (k: Fin n) ↦ k.castLE (by simp)) (Term.index (Fin.last n)) q'
| Query.Diff  q₁ q₂ =>
  let q'₁ := rewriting q₁ (Query.source_diff hq rfl).left
  let q'₂ := rewriting q₂ (Query.source_diff hq rfl).right
  let joinCond₁ :=
    ((List.range n).map
      (λ k ↦ @Selection.BT (T⊕K) (2*n+1)
        (BoolTerm.EQ (Term.index (Fin.ofNat _ k)) (Term.index (Fin.ofNat _ (k+n+1)))))).foldr
      (λ t t' ↦ Selection.And t t') Selection.True
  let prod₁t := λ r ↦ Query.Sel joinCond₁ (@Query.Prod _ (n+1) n (2*n+1) (by omega) q'₁ r)
  let prod₁r := Query.Dedup (Query.Diff
    (Query.Proj (λ (k: Fin n) ↦ (Term.index (k.castLE (Nat.le_succ _)))) q'₁)
    (Query.Proj (λ (k: Fin n) ↦ (Term.index (k.castLE (Nat.le_succ _)))) q'₂))
  let prod₁ := prod₁t (prod₁r)
  let joinCond₂ :=
    ((List.range n).map
      (λ k ↦ @Selection.BT (T⊕K) (2*n+2)
        (BoolTerm.EQ (Term.index (Fin.ofNat _ k)) (Term.index (Fin.ofNat _ (k+n+1)))))).foldr
      (λ t t' ↦ Selection.And t t') Selection.True
  have h₂ : (2*n+2 - (n+1): ℕ) = n+1  := by omega
  let prod₂t := λ r ↦ Query.Sel joinCond₂ (@Query.Prod _ (n+1) (n+1) (2*n+2) (by omega) q'₁ r)
  let prod₂r := Query.ProvSum (λ (k: Fin n) ↦ (k.castLE (by simp))) (Term.index (Fin.last n)) q'₂
  let prod₂ := prod₂t (prod₂r)
  let ts₁ := (λ (k: Fin (n+1)) ↦ Term.index (k.castLE (by omega)))
  let ts₂ := (λ (k: Fin (n+1)) ↦ if ↑k<n then Term.index (k.castLE (by omega))
                                 else Term.sub (Term.index (Fin.ofNat _ n)) (Term.index (Fin.last (2*n+1))))
  Query.Sum (Query.Proj ts₁ prod₁) (Query.Proj ts₂ prod₂)
| Query.ProvSum _ _ _ => by simp[Query.source] at hq
| Query.Having _ _ _ _ _ _ _ => by simp[Query.source] at hq

/-- **(R1) projection.** `Π_{t₁,…,t_n}(q)` is rewritten to
`Π_{t₁,…,t_n,#(k+1)}(q̂)`: the terms are carried over unchanged and the
annotation column of the rewritten argument is appended. -/
axiom rule_projection : ∀ [ValueType T] {K : Type} {n k : ℕ} (ts : Tuple (Term T k) n) (q : Query T k)
    (hq : (Query.Proj ts q).source),
  Query.rewriting (K := K) (Query.Proj ts q) hq
    = Query.Proj
        (fun l : Fin (n + 1) =>
          if h : (l : ℕ) < n then (ts ⟨l, h⟩).castToAnnotatedTuple
          else Term.index (Fin.last q.arity))
        (Query.rewriting q (Query.source_proj hq rfl))

/-- **(R2) cross product.** `q₁ × q₂` is rewritten to
`Π_{#1,…,#k₁,#(k₁+2),…,#(k₁+k₂+1),#(k₁+1) ⊗ #(k₁+k₂+2)}(q̂₁ × q̂₂)`: the two
data blocks are kept, the two annotation columns are multiplied. -/
axiom rule_product : ∀ [ValueType T] {K : Type} {n n₁ n₂ : ℕ} {hn : n₁ + n₂ = n}
    (q₁ : Query T n₁) (q₂ : Query T n₂) (hq : (Query.Prod (hn := hn) q₁ q₂).source),
  Query.rewriting (K := K) (Query.Prod (hn := hn) q₁ q₂) hq
    = Query.Proj
        (fun l : Fin (n + 1) =>
          if (l : ℕ) < n₁ then Term.index (l.castLE (by simp))
          else if ((l : ℕ) < n : Prop) then Term.index (Fin.ofNat _ ((l : ℕ) + 1))
          else Term.mul (Term.index (Fin.ofNat _ n₁)) (Term.index (Fin.ofNat _ (n + 1))))
        (@Query.Prod (T ⊕ K) (n₁ + 1) (n₂ + 1) (n + 2) (by omega)
          (Query.rewriting q₁ (Query.source_prod hq rfl).left)
          (Query.rewriting q₂ (Query.source_prod hq rfl).right))

/-- **(R3) duplicate elimination.** `ε(q)` is rewritten to
`γ_{1,…,k}[#(k+1) : ⊕](q̂)`: group by the data columns and `⊕`-sum the
annotation column. -/
axiom rule_dupelim : ∀ [ValueType T] {K : Type} {n : ℕ} (q : Query T n) (hq : (Query.Dedup q).source),
  Query.rewriting (K := K) (Query.Dedup q) hq
    = Query.ProvSum (fun l : Fin n => l.castLE (by simp)) (Term.index (Fin.last n))
        (Query.rewriting q (Query.source_dedup hq rfl))

/-- **(R4) multiset difference.** `q₁ - q₂` is rewritten to the multiset sum of
two branches: the tuples of `q̂₁` whose data part survives the set difference of
the two data projections, carrying their annotation unchanged; and the tuples of
`q̂₁` matched against the `⊕`-aggregated `q̂₂`, carrying `α ⊖ Σβ`. Both branches
are joins on the `k` data columns. -/
axiom rule_difference : ∀ [ValueType T] {K : Type} {n : ℕ} (q₁ q₂ : Query T n)
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
       Query.Sum (Query.Proj ts₁ prod₁) (Query.Proj ts₂ prod₂))

end Lax392996.RewritingRules
