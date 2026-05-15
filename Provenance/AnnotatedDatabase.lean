import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Count

import Provenance.Database
import Provenance.SemiringWithMonus

/-!
# Annotated databases

This file extends the relational model with provenance annotations drawn from an
m-semiring `K`. Annotated relations are the data model of Section IV-A of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*][sen2026provsql] (a multiset variant of the
`K`-relations of [Green, Karvounarakis & Tannen][green2007provenance]).

## Main definitions

* `AnnotatedTuple T K n` — a tuple of arity `n` paired with an annotation in `K`
* `AnnotatedRelation T K n` — a multiset of annotated tuples of arity `n`
* `AnnotatedDatabase T K` — a mapping from relation names to annotated relations

## References

* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Section IV-A)
* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
-/

variable {T: Type} [ValueType T]
variable {K: Type} [Zero K]

abbrev AnnotatedTuple (T K) (n: ℕ) := Tuple T n ×ₗ K

instance [LinearOrder T] [LinearOrder K] : LinearOrder (AnnotatedTuple T K n) := inferInstance

instance [ToString T] [ToString K] : ToString (AnnotatedTuple T K n)
where
  toString t :=
    "(" ++ String.intercalate ", " (List.ofFn (fun i => toString (t.fst i)))
        ++ ";" ++ (toString t.snd) ++ ")"

instance : Zero (AnnotatedTuple T K n) := ⟨0,0⟩

def AnnotatedRelation (T K) (arity: ℕ) := Multiset (AnnotatedTuple T K arity)

def AnnotatedRelation.cast (heq : n=m) (r: AnnotatedRelation T K n): AnnotatedRelation T K m := by
  subst heq
  exact r

instance [LinearOrder T] [ToString T] [ToString K] [LinearOrder K] :
    ToString (AnnotatedRelation T K n) where
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

def AnnotatedTuple.toComposite (p: AnnotatedTuple T K n) :=
  Fin.append (λ k: Fin n ↦ Sum.inl (p.fst k)) ![Sum.inr p.snd]

def Tuple.fromComposite (t: Tuple (T⊕K) (n+1)) : AnnotatedTuple T K n :=
  (
    λ (k: Fin n) ↦ match t (k.castLE (by simp)) with | Sum.inl x => x | Sum.inr _ => 0,
                   match t (Fin.last n)         with | Sum.inl _ => 0 | Sum.inr x => x
  )

def AnnotatedRelation.toComposite (ar: AnnotatedRelation T K n):
  Relation (T⊕K) (n+1) :=
  ar.map λ p ↦ p.toComposite

@[simp]
theorem AnnotatedRelation.toComposite_add {T: Type} {K: Type} (ar₁ ar₂: AnnotatedRelation T K n):
   (ar₁ + ar₂).toComposite = ar₁.toComposite + ar₂.toComposite :=
  Multiset.map_add _ ar₁ ar₂

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
              have hfi := congrFun hf (i.castLE (by simp))
              simp at hfi
              assumption
            have h2 : a.2=b.2 := by
              have := congrFun hf (Fin.last hd.snd.fst)
              simp at this
              assumption
            exact Prod.ext (funext h1) h2
          have map_eq : Multiset.map (f) hd.2.2 = Multiset.map (f) rn := h
          rw[Multiset.map_eq_map hf] at map_eq
          exact map_eq
      . simp[hhd]
        exact ih

lemma AnnotatedTuple.toComposite_join {K: Type} {T: Type}
  [ValueType T] [HasAltLinearOrder K] [SemiringWithMonus K]
    (ta₁: AnnotatedTuple T K n₁)
    (ta₂: AnnotatedTuple T K n₂):
  AnnotatedTuple.toComposite (Fin.append ta₁.1 ta₂.1, ta₁.2 * ta₂.2) = fun (k: Fin (n₁+n₂+1)) ↦
    if h: ↑k < n₁ then ta₁.toComposite (k.castLT (Nat.lt_add_right 1 h))
    else if ↑k < n₁ + n₂ then ta₂.toComposite (@Fin.ofNat (n₂+1) _ (k.toNat - n₁))
    else ta₁.toComposite (Fin.last n₁) * ta₂.toComposite (Fin.last n₂) := by
    unfold AnnotatedTuple.toComposite
    funext k
    by_cases hlt₁₂: ↑k<n₁+n₂
    . simp[Fin.append,Fin.addCases,hlt₁₂]
      by_cases hlt₁: ↑k<n₁
      . simp[hlt₁]
        apply congrArg
        apply Fin.eq_of_val_eq
        simp
      . simp[hlt₁]
        have h: (↑k-n₁)%(n₂+1) = ↑k-n₁ := by
          refine Nat.mod_eq_of_lt ?_
          omega
        have h': ↑k-n₁<n₂ := by omega
        simp[h,h']
        apply congrArg
        apply Fin.eq_of_val_eq
        simp[h]
    . simp[Fin.append,Fin.addCases,hlt₁₂]
      have : ¬↑k<n₁ := by omega
      simp[this]
      simp[(·*·),Mul.mul]

lemma eq_imp_eq_equiv_eq:
  y=z → (x=y ↔ x=z) := by
    intro heq
    subst heq
    tauto

theorem AnnotatedRelation.toComposite_map_product {K: Type} {T: Type}
  [ValueType T] [HasAltLinearOrder K] [SemiringWithMonus K]
  (ar₁: AnnotatedRelation T K n₁) (ar₂: AnnotatedRelation T K n₂) :
  AnnotatedRelation.toComposite (
    Multiset.map (fun x ↦ ((Fin.append x.1.1 x.2.1), x.1.2 * x.2.2)) (Multiset.product ar₁ ar₂)) =
  Multiset.map
    (fun x ↦ fun (k: Fin (n₁+n₂+1)) ↦
      if h: ↑k<n₁ then x.1 (k.castLT (Nat.lt_add_right 1 h))
      else if ↑k<n₁+n₂ then x.2 (@Fin.ofNat (n₂+1) _ (k.toNat - n₁))
      else (x.1 (Fin.last n₁) * x.2 (Fin.last n₂)))
    (Multiset.product ar₁.toComposite ar₂.toComposite) := by
  -- Induction on ar₁ to reduce the product, then map_congr element-wise on ar₂.
  induction ar₁ using Multiset.induction_on with
  | empty =>
    unfold AnnotatedRelation.toComposite Multiset.product
    simp
    rfl
  | @cons p tl ih =>
    unfold AnnotatedRelation.toComposite Multiset.product at *
    rw [Multiset.cons_bind, Multiset.map_add, Multiset.map_add, Multiset.map_cons,
        Multiset.cons_bind, Multiset.map_add]
    congr 1
    -- For the head `p`: show maps are equal element-wise over `ar₂`.
    · simp only [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro q _
      simp only [Function.comp]
      exact AnnotatedTuple.toComposite_join p q

theorem AnnotatedRelation.cast_toComposite {T: Type} {K: Type}
  (ar: AnnotatedRelation T K n) (h': n+1=m+1) (h: n = m) :
  ar.toComposite.cast h' = (ar.cast h).toComposite := by
  subst h
  congr
