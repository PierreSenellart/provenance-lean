import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Bind

section Database

variable {T: Type} [Zero T] [DecidableEq T] [Hashable T]

abbrev Tuple (T : Type) (n: ℕ) := Vector T n

instance : Zero (Tuple T n) := ⟨Vector.replicate n 0⟩

instance : Hashable (Tuple T n) where hash t := hash t.toArray

def Relation (T) (arity: ℕ) := Multiset (Tuple T arity)

instance : Add (Relation T arity) := inferInstanceAs (Add (Multiset (Tuple T arity)))
instance : Sub (Relation T arity) := inferInstanceAs (Sub (Multiset (Tuple T arity)))
instance : HMul (Relation T a₁) (Relation T a₂) (Relation T (a₁+a₂)) where
  hMul r s :=
    Multiset.map (λ (x,y) ↦ Vector.append x y) (Multiset.product r s)

instance : Zero (Relation T n) where zero := (∅: Multiset (Tuple T n))
instance : Zero ((n : ℕ) × Relation T n) where zero := ⟨0,(∅: Multiset (Tuple T 0))⟩

structure Database (T) where
  db : (ℕ × String) →₀ (Σ n, Relation T n)
  wf : ∀ (n: ℕ) (s: String), (db (n,s)).fst = n

instance : FunLike (Database T) (ℕ × String) (Σ n, Relation T n) where
  coe := λ d ↦ (λ (n, s) ↦ d.db (n, s))
  coe_injective' := by
    intro d₁ d₂ h
    simp at h
    cases d₁; cases d₂
    congr

end Database
