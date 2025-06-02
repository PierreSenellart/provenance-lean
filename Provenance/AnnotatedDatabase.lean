import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fin.VecNotation

import Provenance.Database
import Provenance.SemiringWithMonus

variable {T: Type} [ValueType T]
variable {K: Type} [Zero K]

abbrev AnnotatedTuple (T K) (n: ℕ) := Tuple T n ×ₗ K

instance [LinearOrder K] : LinearOrder (AnnotatedTuple T K n) := inferInstance

instance [ToString T] [ToString K] : ToString (AnnotatedTuple T K n) where
  toString t :=
    "(" ++ String.intercalate ", " (List.ofFn (fun i => toString (t.fst i)))
        ++ ";" ++ (toString t.snd) ++ ")"

instance : Zero (AnnotatedTuple T K n) := ⟨0,0⟩

def AnnotatedRelation (T K) (arity: ℕ) := Multiset (AnnotatedTuple T K arity)

instance [ToString T] [ToString K] [LinearOrder K] : ToString (AnnotatedRelation T K n) where
  toString r :=
    String.intercalate "\n" ((r.foldr sortedInsert ⟨[],by simp⟩).val.map toString) ++ "\n"

def Relation.annotate (f: Tuple T n → K) (r: Relation T n) :
  AnnotatedRelation T K n :=
    r.map (λ t ↦ ⟨t, f t⟩)

instance : Add (AnnotatedRelation T K arity) := inferInstanceAs (Add (Multiset (AnnotatedTuple T K arity)))

instance : Zero (AnnotatedRelation T K n) where zero := (∅: Multiset (AnnotatedTuple T K n))
instance : Zero ((n : ℕ) × AnnotatedRelation T K n) where zero := ⟨0,(∅: Multiset (AnnotatedTuple T K 0))⟩

def AnnotatedRelation.toCompositeRelation (ar: AnnotatedRelation T K n):
  Relation (T⊕K) (n+1) :=
  ar.map λ p ↦ Fin.append (λ k: Fin n ↦ Sum.inl (p.fst k)) ![Sum.inr p.snd]

def AnnotatedDatabase (T K) := List (ℕ × String × Σ n, AnnotatedRelation T K n)

def AnnotatedDatabase.find (n: ℕ) (s: String) (d: AnnotatedDatabase T K) : Option (Σ n, AnnotatedRelation T K n) :=
  let rec f
  | [] => none
  | (n',s',rn)::tl => if (n,s) = (n',s') then some rn else f tl
  f d

instance : CoeFun (AnnotatedDatabase T K) (fun _ => (ℕ × String) → Option (Σ n, AnnotatedRelation T K n)) where
  coe := λ d (n,s) ↦ d.find n s

def AnnotatedDatabase.Wf (d: AnnotatedDatabase T K) : Prop :=
  ∀ (n: ℕ) (s: String) (rn: Σ n, AnnotatedRelation T K n), d.find n s = some rn → rn.fst = n

structure WFAnnotatedDatabase (T K) where
  db : AnnotatedDatabase T K
  wf: AnnotatedDatabase.Wf db
