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

def AnnotatedDatabase (T K) := List (String × Σ n, AnnotatedRelation T K n)

def AnnotatedDatabase.find (n: ℕ) (s: String) (d: AnnotatedDatabase T K) : Option (AnnotatedRelation T K n) :=
  let rec f
  | [] => none
  | (s',rn)::tl => if h: n = rn.fst ∧ s =s' then some (Eq.mp (by rw[h.left]) rn.snd) else f tl
  f d

instance : CoeFun (AnnotatedDatabase T K) (fun _ => (ℕ × String) → Option (Σ n, AnnotatedRelation T K n)) where
  coe := λ d (n,s) ↦ match d.find n s with | some val => some ⟨n,val⟩ | none => none

def AnnotatedRelation.toComposite (ar: AnnotatedRelation T K n):
  Relation (T⊕K) (n+1) :=
  ar.map λ p ↦ Fin.append (λ k: Fin n ↦ Sum.inl (p.fst k)) ![Sum.inr p.snd]

def AnnotatedDatabase.toComposite (d: AnnotatedDatabase T K): Database (T⊕K) :=
  d.map λ (s, ⟨n',r⟩) ↦ (s, ⟨n'+1,r.toComposite⟩)
