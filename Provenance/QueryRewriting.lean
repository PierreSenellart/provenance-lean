import Mathlib.Data.Fin.VecNotation

import Provenance.Query

variable {T: Type} [ValueType T]
variable {K: Type} [Zero K]

def Query.rewriting (q: Query T n): Query (T⊕K) (n+1) := match q with
| Rel   n  s  => Rel (n+1) s
| Proj  ts q  =>
  let ts :=
    (λ (k: Fin (n+1)) => if h : ↑k<n then (ts ⟨k,h⟩).castToAnnotatedTuple
                         else Term.index q.arity)
  Proj ts (rewriting q)
| Sel   φ  q  => Sel φ.castToAnnotatedTuple (rewriting q)
| @Prod _ n n₁ q₁ q₂ =>
  have hrq₁: (↑n₁ + (1:ℕ)) = ↑(((↑n₁): Fin (n+2)) + 1) := by
    apply?
  let tmp: Query (T⊕K) ((n+2)-(n₁+1: Fin (n+2))) → Query (T⊕K) (n+2) :=
    @Query.Prod (T⊕K) (n+2) (n₁+1: Fin (n+2)) (Eq.mp (by
      rw[hrq₁]
    ) q₁.rewriting)
  let p := tmp (q₂.rewriting)
  let ts : Tuple (Term (T⊕K) (n+2)) (n+1) :=
    (λ k: Fin (n+1) =>
      if (↑k<n₁.castLE (Nat.le_add_right n 1) : Prop) then #k
      else if (↑k<n: Prop) then #(k+1)
      else Term.mul #n₁ #n)
  Proj ts p
| Sum   q₁ q₂ => Sum (rewriting q₁) (rewriting q₂)
| Dedup q     => sorry
| Diff  q₁ q₂ => sorry
| Agg _ _ _ _ => sorry
