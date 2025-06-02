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
| @Prod _ n n₁ q₁ q₂ =>
  have hrq₁: (n₁: ℕ) + 1 = (n₁+1: Fin (n+2)) := by
    rw[Fin.add_def]
    have h₁ : (n₁+1) % (n+2) = n₁+1 := by
      apply Nat.mod_eq_of_lt
      exact Nat.add_lt_add_right (Nat.lt_add_right 1 n₁.isLt) 1
    have h₂: (((n₁: ℕ) : Fin (n+2)): ℕ) = (n₁: ℕ) :=
      Fin.val_cast_of_lt (Nat.lt_add_right 2 n₁.isLt)
    rw[h₂]
    exact id (Eq.symm h₁)
  have hrq₂ : (n - (n₁: ℕ)) + 1 = (n + 2) - ↑((↑n₁: Fin (n+2)) + 1) := by
    have : n₁<n := n₁.isLt
    omega
  let tmp: Query (T⊕K) ((n+2)-(n₁+1: Fin (n+2))) → Query (T⊕K) (n+2) :=
    @Query.Prod (T⊕K) (n+2) (n₁+1: Fin (n+2)) (Eq.mp (by rw[hrq₁]) (q₁.rewriting (noAggProd hq rfl).left))
  let product := tmp (Eq.mp (by rw[hrq₂]) (q₂.rewriting (noAggProd hq rfl).right))
  let ts : Tuple (Term (T⊕K) (n+2)) (n+1) :=
    (λ k: Fin (n+1) =>
      if (↑k<n₁.castLE (Nat.le_add_right n 1) : Prop) then #k
      else if (↑k<n: Prop) then #(k+1)
      else Term.mul #n₁ #n)
  Proj ts product
| Sum   q₁ q₂ => Sum (q₁.rewriting (noAggSum hq rfl).left) (rewriting q₂ (noAggSum hq rfl).right)
| Dedup q     =>
  let q' := q.rewriting (noAggDedup hq rfl)
  Agg (λ (k: Fin n) ↦ (k: Fin (n+1))) ![#n] ![AggFunc.sum] q'
| Diff  q₁ q₂ =>
  let q'₁ := q₁.rewriting (noAggDiff hq rfl).left
  let q'₂ := q₂.rewriting (noAggDiff hq rfl).right
  let prod₁r := Dedup (Diff (Proj (λ (k: Fin n) ↦ (Term.index (k: Fin (n+1)))) q'₁)
                            (Proj (λ (k: Fin n) ↦ (Term.index (k: Fin (n+1)))) q'₂))
  let prod₂r := Agg (λ (k: Fin n) ↦ (k: Fin (n+1))) ![#n] ![AggFunc.sum] q'₂
  sorry
| Agg _ _ _ _ => by simp[noAgg] at hq
