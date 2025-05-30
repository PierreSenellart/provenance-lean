import Mathlib.Data.Fin.VecNotation

import Provenance.Query

variable {T: Type} [ValueType T]
variable {K: Type} [Zero K]

def Query.rewriting (q: Query T n) : Query (T⊕K) (n+1) := match q with
| Rel   n  s  => Rel (n+1) s
| Proj  ts q  =>
  let ts :=
    (λ (k: Fin (n+1)) => if h : ↑k<n then (ts ⟨k,h⟩).castToAnnotatedTuple
    else Term.Index (n+2))
  Proj ts (rewriting q)
| Sel   φ  q  => Sel φ.castToAnnotatedTuple (rewriting q)
| Prod  q₁ q₂ =>
  let prod := Prod (rewriting q₁) (rewriting q₂)
  let ts :=
    (λ k: Fin (n+1) =>
      if ↑k<q₁.arity then Term.Index k
      else if ↑k<n then Term.Index (k+1)
      else sorry)
  Proj ts prod
| Sum   q₁ q₂ => Sum (rewriting q₁) (rewriting q₂)
| Dedup q     => sorry
| Diff  q₁ q₂ => sorry
