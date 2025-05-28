import Provenance.Database
import Provenance.SemiringWithMonus

variable {T: Type} [ValueType T]
variable {K: Type} [Zero K]

abbrev AnnotatedTuple (T K) (n: ℕ) := Tuple T n × K

/-
instance [LinearOrder K] : LinearOrder (AnnotatedTuple T K n) where
  le t₁ t₂ :=
    if t₁.fst < t₂.fst then
      true
    else if t₁.fst = t₂.fst ∧ t₁.snd ≤ t₂.snd then
      true
    else false

  le_refl t := by simp

  le_antisymm t₁ t₂ := by
    by_cases hlt₁ : t₁.fst < t₂.fst <;>
    by_cases hlt₂ : t₂.fst < t₁.fst <;>
    simp[hlt₁,hlt₂]
    . have := lt_of_lt_of_le hlt₁ (le_of_lt hlt₂)
      simp at this
    . intro heq
      simp[heq] at hlt₁
    . intro heq
      simp[heq] at hlt₂
    . intro heq
      sorry
      -/






instance [ToString T] [ToString K] : ToString (AnnotatedTuple T K n) where
  toString t :=
    "(" ++ String.intercalate ", " (List.ofFn (fun i => toString (t.fst i)))
        ++ ";" ++ (toString t.snd) ++ ")"

instance : Zero (AnnotatedTuple T K n) := ⟨0,0⟩

def AnnotatedRelation (T K) (arity: ℕ) := Multiset (AnnotatedTuple T K arity)

/-
instance [ToString T] [ToString K] : ToString (AnnotatedRelation T K n) where
  toString r :=
    String.intercalate "\n" ((r.foldr sortedInsert ⟨[],by simp⟩).val.map toString) ++ "\n"
-/

def Relation.annotate (f: Tuple T n → K) (r: Relation T n) :
  AnnotatedRelation T K n
    :=
  r.map (λ t ↦ ⟨t, f t⟩)

instance : Add (AnnotatedRelation T K arity) := inferInstanceAs (Add (Multiset (AnnotatedTuple T K arity)))

instance : Zero (AnnotatedRelation T K n) where zero := (∅: Multiset (AnnotatedTuple T K n))
instance : Zero ((n : ℕ) × AnnotatedRelation T K n) where zero := ⟨0,(∅: Multiset (AnnotatedTuple T K 0))⟩

structure AnnotatedDatabase (T K) where
  db : (ℕ × String) →₀ (Σ n, AnnotatedRelation T K n)
  wf : ∀ (n: ℕ) (s: String), (db (n,s)).fst = n

instance : FunLike (AnnotatedDatabase T K) (ℕ × String) (Σ n, AnnotatedRelation T K n) where
  coe := λ d ↦ (λ (n, s) ↦ d.db (n, s))
  coe_injective' := by
    intro d₁ d₂ h
    simp at h
    cases d₁; cases d₂
    congr
