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
| @Prod _ n₁ n₂ q₁ q₂ =>
  -- Even though the output type of Prod is defined to be n=n₁+n₂,
  -- Lean cannot prove it. :-(
  have hn : n=n₁+n₂ := by admit
  let p := Query.Prod (rewriting q₁) (rewriting q₂)
  let ts : Tuple (Term (T⊕K) (n+2)) (n+1) :=
    (λ k: Fin (n+1) =>
      if ↑k<n₁ then #k
      else if ↑k<n then #(k+1)
      else Term.mul #n₁ #n)
  Proj (Eq.mp (by
    have h₁ : (n₁+1+(n₂+1)) = n+2 := by omega
    have h₂ : (n₁+n₂+1) = n+1 := by omega
    rw[←h₁,←h₂]
  ) ts) p
| Sum   q₁ q₂ => Sum (rewriting q₁) (rewriting q₂)
| Dedup q     => sorry
| Diff  q₁ q₂ => sorry
| Agg _ _ _ _ => sorry
