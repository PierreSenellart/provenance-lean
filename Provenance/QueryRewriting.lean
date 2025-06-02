import Mathlib.Data.Fin.VecNotation

import Provenance.Query

variable {T: Type} [ValueType T]
variable {K: Type} [Zero K]

def Query.rewriting (q: Query T n) (hq: q.noAgg) : Query (T⊕K) (n+1) := match q with
| Rel   n  s  => Rel (n+1) s
| Proj  ts q  =>
  let ts :=
    (λ (k: Fin (n+1)) => if h : ↑k<n then (ts ⟨k,h⟩).castToAnnotatedTuple
                         else Term.index q.arity)
  Proj ts (q.rewriting (noAggProj hq rfl))
| Sel   φ  q  => Sel φ.castToAnnotatedTuple (q.rewriting (noAggSel hq rfl))
| @Prod _ n₁ n hn₁ q₁ q₂ =>
  have hrq : (n - n₁) + 1 = (n + 2) - (n₁ + 1) := by omega
  let tmp :=
    @Query.Prod (T⊕K) (n₁+1) (n+2) (by omega) (q₁.rewriting (noAggProd hq rfl).left)
  let product := tmp (Eq.mp (by rw[hrq]) (q₂.rewriting (noAggProd hq rfl).right))
  let ts : Tuple (Term (T⊕K) (n+2)) (n+1) :=
    (λ k: Fin (n+1) =>
      if k<n₁ then #k
      else if (↑k<n: Prop) then #(k+1)
      else Term.mul #n₁ #(n+1))
  Proj ts product
| Sum   q₁ q₂ => Sum (q₁.rewriting (noAggSum hq rfl).left) (rewriting q₂ (noAggSum hq rfl).right)
| Dedup q     =>
  let q' := q.rewriting (noAggDedup hq rfl)
  Agg (λ (k: Fin n) ↦ (k: Fin (n+1))) ![#n] ![AggFunc.sum] q'
| Diff  q₁ q₂ =>
  let q'₁ := q₁.rewriting (noAggDiff hq rfl).left
  let q'₂ := q₂.rewriting (noAggDiff hq rfl).right
  let joinCond₁ :=
    ((List.range n).map
      (λ k ↦ @Filter.BT (T⊕K) (2*n+1) (#k==#(k+n+1)))).foldr
      (λ t t' ↦ Filter.And t t') Filter.True
  have h₁ : (2*n+1 - (n+1): ℕ) = n  := by omega
  let prod₁t := λ r ↦ Sel joinCond₁ (@Query.Prod _ (n+1) (2*n+1) (by omega) q'₁ r)
  let prod₁r := Dedup (Diff (Proj (λ (k: Fin n) ↦ (Term.index (k: Fin (n+1)))) q'₁)
                            (Proj (λ (k: Fin n) ↦ (Term.index (k: Fin (n+1)))) q'₂))
  let prod₁ := prod₁t (Eq.mp (by rw[h₁]) prod₁r)
  let joinCond₂ :=
    ((List.range n).map
      (λ k ↦ @Filter.BT (T⊕K) (2*n+2) (#k==#(k+n+1)))).foldr
      (λ t t' ↦ Filter.And t t') Filter.True
  have h₂ : (2*n+2 - (n+1): ℕ) = n+1  := by omega
  let prod₂t := λ r ↦ Sel joinCond₂ (@Query.Prod _ (n+1) (2*n+2) (by omega) q'₁ r)
  let prod₂r := Agg (λ (k: Fin n) ↦ (k: Fin (n+1))) ![#n] ![AggFunc.sum] q'₂
  let prod₂ := prod₂t (Eq.mp (by rw[h₂]) prod₂r)
  let ts₁ := (λ (k: Fin (n+1)) ↦ #(k: Fin (2*n+1)))
  let ts₂ := (λ (k: Fin (n+1)) ↦ if ↑k<n then #(k: Fin (2*n+2))
                                 else Term.sub #n #(2*n+1))
  Sum (Proj ts₁ prod₁) (Proj ts₂ prod₂)
| Agg _ _ _ _ => by simp[noAgg] at hq
