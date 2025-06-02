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

def AnnotatedRelation.toComposite (ar: AnnotatedRelation T K n):
  Relation (T⊕K) (n+1) :=
  ar.map λ p ↦ Fin.append (λ k: Fin n ↦ Sum.inl (p.fst k)) ![Sum.inr p.snd]

def AnnotatedDatabase.toComposite (d: AnnotatedDatabase T K): Database (T⊕K) :=
  d.map λ (s, ⟨n',r⟩) ↦ (s, ⟨n'+1,r.toComposite⟩)

theorem AnnotatedDatabase.find_toComposite_none {T: Type} {K: Type} (n: ℕ) (s: String) (d: AnnotatedDatabase T K):
  d.find n s = none ↔ d.toComposite.find (n+1) s = none := by
    induction d with
    | nil =>
      unfold find find.f Database.find Database.find.f toComposite
      simp
    | cons hd tl ih =>
      unfold find find.f Database.find Database.find.f toComposite
      by_cases hhd: n=hd.snd.fst ∧ s=hd.fst
      . simp[hhd]
      . simp[hhd]
        exact ih

theorem AnnotatedDatabase.find_toComposite_some {T: Type} {K: Type} (n: ℕ) (s: String) (d: AnnotatedDatabase T K):
  ∀ r: AnnotatedRelation T K n, d.find n s = some r ↔ d.toComposite.find (n+1) s = some r.toComposite := by
    induction d with
    | nil =>
      unfold find find.f Database.find Database.find.f toComposite
      simp
    | cons hd tl ih =>
      unfold find find.f Database.find Database.find.f toComposite
      by_cases hhd: n=hd.snd.fst ∧ s=hd.fst
      . simp[hhd]
        intro rn
        unfold AnnotatedRelation.toComposite
        apply Iff.intro
        . intro h
          have : hd.snd.snd = Eq.mp (by rw[hhd.left]) rn := by
            sorry
          rw[this]
          simp
        . sorry
      . simp[hhd]
        exact ih
