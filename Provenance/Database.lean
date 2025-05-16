import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Multiset.AddSub

section Database

variable {α: Type} [Zero α] [DecidableEq α]

abbrev Tuple (α : Type) (n: ℕ) := Vector α n

instance : Zero (Tuple α n) := ⟨Vector.replicate n 0⟩

def Relation (α) (arity: ℕ) := Multiset (Tuple α arity)

instance : Add (Relation α arity) := inferInstanceAs (Add (Multiset (Tuple α arity)))
instance : Sub (Relation α arity) := inferInstanceAs (Sub (Multiset (Tuple α arity)))

instance : Zero (Relation α n) where zero := (∅: Multiset (Tuple α n))
instance : Zero ((n : ℕ) × Relation α n) where zero := ⟨0,(∅: Multiset (Tuple α 0))⟩

structure Database (α) where
  db : (ℕ × String) →₀ (Σ n, Relation α n)
  wf : ∀ (n: ℕ) (s: String), (db (n,s)).fst = n

instance : FunLike (Database α) (ℕ × String) (Σ n, Relation α n) where
  coe := λ d ↦ (λ (n, s) ↦ d.db (n, s))
  coe_injective' := by
    intro d₁ d₂ h
    simp at h
    cases d₁; cases d₂
    congr

end Database
