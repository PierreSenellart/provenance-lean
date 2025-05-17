import Provenance.Database
import Provenance.SemiringWithMonus

section AnnotatedDatabase

variable {α: Type} [Zero α] [DecidableEq α]
variable {K: Type} [Zero K]

abbrev AnnotatedTuple (α K) (n: ℕ) := Vector α n × K

instance : Zero (AnnotatedTuple α K n) := ⟨0,0⟩

def AnnotatedRelation (α K) (arity: ℕ) := Multiset (AnnotatedTuple α K arity)

instance : Add (AnnotatedRelation α K arity) := inferInstanceAs (Add (Multiset (AnnotatedTuple α K arity)))

instance : Zero (AnnotatedRelation α K n) where zero := (∅: Multiset (AnnotatedTuple α K n))
instance : Zero ((n : ℕ) × AnnotatedRelation α K n) where zero := ⟨0,(∅: Multiset (AnnotatedTuple α K 0))⟩

structure AnnotatedDatabase (α K) where
  db : (ℕ × String) →₀ (Σ n, AnnotatedRelation α K n)
  wf : ∀ (n: ℕ) (s: String), (db (n,s)).fst = n

instance : FunLike (AnnotatedDatabase α K) (ℕ × String) (Σ n, AnnotatedRelation α K n) where
  coe := λ d ↦ (λ (n, s) ↦ d.db (n, s))
  coe_injective' := by
    intro d₁ d₂ h
    simp at h
    cases d₁; cases d₂
    congr

end AnnotatedDatabase
