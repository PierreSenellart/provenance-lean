import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Multiset.MapFold

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

def AnnotatedRelation.cast (heq : n=m) (r: AnnotatedRelation T K n): AnnotatedRelation T K m := by
  subst heq
  exact r

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

@[simp]
theorem AnnotatedRelation.toComposite_add {T: Type} {K: Type} (ar₁ ar₂: AnnotatedRelation T K n):
   (ar₁ + ar₂).toComposite = ar₁.toComposite + ar₂.toComposite := by
     unfold toComposite
     rw[Multiset.map_add]

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
        have := hhd.left
        subst n
        apply Iff.intro
        . intro h
          have : hd.snd.snd = Eq.mp (by rw[hhd.left]) rn := by
            exact h
          rw[this]
          simp
        . intro h
          let f := fun (p: Tuple T hd.2.1 × K) ↦ Fin.append (fun k ↦ Sum.inl (p.1 k)) ![Sum.inr p.2]
          have hf : Function.Injective f := by
            intro a b hf
            unfold f at hf
            unfold Fin.append Fin.addCases at hf
            simp at hf
            have h1 : ∀ (i: Fin hd.snd.fst), a.1 i = b.1 i := by
              intro i
              have hfi := congrFun hf i
              simp at hfi
              assumption
            have h2 : a.2=b.2 := by
              have := congrFun hf (hd.snd.fst)
              simp at this
              assumption
            exact Prod.ext (funext h1) h2
          have map_eq : Multiset.map (f) hd.2.2 = Multiset.map (f) rn := h
          rw[Multiset.map_eq_map hf] at map_eq
          exact map_eq
      . simp[hhd]
        exact ih

theorem AnnotatedRelation.toComposite_map_product {K: Type}
  [DecidableEq (T⊕K)] [DecidableEq T] [Mul K] [Mul (T⊕K)]
  (ar₁: AnnotatedRelation T K n₁) (ar₂: AnnotatedRelation T K n₂) :
  AnnotatedRelation.toComposite (
    Multiset.map (fun x ↦ ((Fin.append x.1.1 x.2.1), x.1.2 * x.2.2)) (Multiset.product ar₁ ar₂)) =
  Multiset.map
    (fun x ↦ fun (k: Fin (n₁+n₂+1)) ↦ if ↑k<n₁ then x.1 k else if ↑k<n₁+n₂ then x.2 (k-n₁:ℕ) else (x.1 n₁ * x.2 n₂))
    (Multiset.product ar₁.toComposite ar₂.toComposite) := by
  unfold toComposite Multiset.product
  repeat rw[Multiset.map_map]
  repeat rw[Multiset.map_bind]
  rw[Multiset.ext]
  intro t
  repeat rw[Multiset.count_bind]
  apply congrArg
  rw[Multiset.ext]
  intro t'
  repeat rw[Multiset.count_map]
  simp
  sorry













theorem AnnotatedRelation.cast_toComposite {T: Type} {K: Type}
  (ar: AnnotatedRelation T K n) (h': n+1=m+1) (h: n = m) :
  ar.toComposite.cast h' = (ar.cast h).toComposite := by
  subst h
  congr
