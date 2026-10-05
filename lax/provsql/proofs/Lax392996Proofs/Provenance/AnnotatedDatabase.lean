import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Count

import Lax392996Proofs.Provenance.Database
import Lax392996Proofs.Provenance.SemiringWithMonus
import Lax392996.AnnotatedDatabases
import Lax392996.AnnotatedSemantics
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.MultisetSemantics
import Lax392996.ProbabilisticDatabases
import Lax392996.RelationalAlgebra
import Lax392996.RewritingRules
import Lax392996.SemiringsWithMonus
import Lax392996.WhyProvenance

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase
end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation
end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple
end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace Lax392996.Databases.Tuple
end Lax392996.Databases.Tuple

namespace Lax392996Proofs.Foreign.AnnotatedDatabase
end Lax392996Proofs.Foreign.AnnotatedDatabase

namespace Lax392996Proofs.Foreign.AnnotatedRelation
end Lax392996Proofs.Foreign.AnnotatedRelation

namespace Lax392996Proofs.Foreign.AnnotatedTuple
end Lax392996Proofs.Foreign.AnnotatedTuple

namespace Lax392996Proofs.Foreign.Relation
end Lax392996Proofs.Foreign.Relation

namespace Lax392996Proofs.Foreign.Tuple
end Lax392996Proofs.Foreign.Tuple

/-!
# Annotated databases

This file extends the relational model with provenance annotations drawn from an
m-semiring `K`. Annotated relations are the data model of Section IV-A of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*][sen2026provsql] (a multiset variant of the
`K`-relations of [Green, Karvounarakis & Tannen][green2007provenance]).

## Main definitions

* `AnnotatedTuple T K n` – a tuple of arity `n` paired with an annotation in `K`
* `AnnotatedRelation T K n` – a multiset of annotated tuples of arity `n`
* `AnnotatedDatabase T K` – a mapping from relation names to annotated relations

## References

* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Section IV-A)
* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
-/

variable {T: Type} [Lax392996.Databases.ValueType T]

variable {K: Type} [Zero K]

instance _root_.Lax392996Proofs.Foreign.instLinearOrderAnnotatedTuple [LinearOrder K] : LinearOrder (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n) := inferInstance

instance _root_.Lax392996Proofs.Foreign.instToStringAnnotatedTuple [ToString T] [ToString K] : ToString (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n)
where
  toString t :=
    "(" ++ String.intercalate ", " (List.ofFn (fun i => toString (t.fst i)))
        ++ ";" ++ (toString t.snd) ++ ")"

instance _root_.Lax392996Proofs.Foreign.instZeroAnnotatedTuple : Zero (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n) := ⟨0,0⟩

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

open Lax392996Proofs.Foreign.AnnotatedRelation in
def _root_.Lax392996Proofs.Foreign.AnnotatedRelation.cast (heq : n=m) (r: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n): Lax392996.AnnotatedDatabases.AnnotatedRelation T K m := by
  subst heq
  exact r

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

export Lax392996Proofs.Foreign.AnnotatedRelation (cast)

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace AnnotatedRelation
export Lax392996Proofs.Foreign.AnnotatedRelation (cast)
end AnnotatedRelation

instance _root_.Lax392996Proofs.Foreign.instZeroAnnotatedRelation : Zero (Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) where zero := (∅: Multiset (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n))

instance _root_.Lax392996Proofs.Foreign.instZeroSigmaNatAnnotatedRelation : Zero ((n : ℕ) × Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) where zero := ⟨0,(∅: Multiset (Lax392996.AnnotatedDatabases.AnnotatedTuple T K 0))⟩

namespace Lax392996.Databases.Tuple

open Lax392996Proofs.Foreign.Tuple in
def _root_.Lax392996Proofs.Foreign.Tuple.fromComposite (t: Lax392996.Databases.Tuple (T⊕K) (n+1)) : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n :=
  (
    λ (k: Fin n) ↦ match t (k.castLE (by simp)) with | Sum.inl x => x | Sum.inr _ => 0,
                   match t (Fin.last n)         with | Sum.inl _ => 0 | Sum.inr x => x
  )

end Lax392996.Databases.Tuple

namespace Lax392996.Databases.Tuple

export Lax392996Proofs.Foreign.Tuple (fromComposite)

end Lax392996.Databases.Tuple

namespace Tuple
export Lax392996Proofs.Foreign.Tuple (fromComposite)
end Tuple

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

open Lax392996Proofs.Foreign.AnnotatedRelation in
@[simp]
theorem _root_.Lax392996Proofs.Foreign.AnnotatedRelation.toComposite_add {T: Type} {K: Type} (ar₁ ar₂: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n):
   (ar₁ + ar₂).toComposite = ar₁.toComposite + ar₂.toComposite :=
  Multiset.map_add _ ar₁ ar₂

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

export Lax392996Proofs.Foreign.AnnotatedRelation (toComposite_add)

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace AnnotatedRelation
export Lax392996Proofs.Foreign.AnnotatedRelation (toComposite_add)
end AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase

open Lax392996Proofs.Foreign.AnnotatedDatabase in
theorem _root_.Lax392996Proofs.Foreign.AnnotatedDatabase.find_toComposite_none {T: Type} {K: Type} (n: ℕ) (s: String) (d: Lax392996.AnnotatedDatabases.AnnotatedDatabase T K):
  d.find n s = none ↔ d.toComposite.find (n+1) s = none := by
    induction d with
    | nil =>
      unfold Lax392996.AnnotatedDatabases.AnnotatedDatabase.find Lax392996.Databases.Database.find Lax392996.AnnotatedDatabases.AnnotatedDatabase.toComposite
      simp [Lax392996.AnnotatedDatabases.AnnotatedDatabase.find.f, Lax392996.Databases.Database.find.f]
    | cons hd tl ih =>
      unfold Lax392996.AnnotatedDatabases.AnnotatedDatabase.find Lax392996.Databases.Database.find Lax392996.AnnotatedDatabases.AnnotatedDatabase.toComposite
      by_cases hhd: n=hd.snd.fst ∧ s=hd.fst
      . simp[Lax392996.AnnotatedDatabases.AnnotatedDatabase.find.f, Lax392996.Databases.Database.find.f, hhd]
      . simp[Lax392996.AnnotatedDatabases.AnnotatedDatabase.find.f, Lax392996.Databases.Database.find.f, hhd]
        exact ih

end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase

export Lax392996Proofs.Foreign.AnnotatedDatabase (find_toComposite_none)

end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace AnnotatedDatabase
export Lax392996Proofs.Foreign.AnnotatedDatabase (find_toComposite_none)
end AnnotatedDatabase

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase

open Lax392996Proofs.Foreign.AnnotatedDatabase in
theorem _root_.Lax392996Proofs.Foreign.AnnotatedDatabase.find_toComposite_some {T: Type} {K: Type} (n: ℕ) (s: String) (d: Lax392996.AnnotatedDatabases.AnnotatedDatabase T K):
  ∀ r: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n, d.find n s = some r ↔ d.toComposite.find (n+1) s = some r.toComposite := by
    induction d with
    | nil =>
      unfold Lax392996.AnnotatedDatabases.AnnotatedDatabase.find Lax392996.Databases.Database.find Lax392996.AnnotatedDatabases.AnnotatedDatabase.toComposite
      simp [Lax392996.AnnotatedDatabases.AnnotatedDatabase.find.f, Lax392996.Databases.Database.find.f]
    | cons hd tl ih =>
      unfold Lax392996.AnnotatedDatabases.AnnotatedDatabase.find Lax392996.Databases.Database.find Lax392996.AnnotatedDatabases.AnnotatedDatabase.toComposite
      by_cases hhd: n=hd.snd.fst ∧ s=hd.fst
      . simp[Lax392996.AnnotatedDatabases.AnnotatedDatabase.find.f, Lax392996.Databases.Database.find.f, hhd]
        intro rn
        unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
        have := hhd.left
        subst n
        apply Iff.intro
        . intro h
          have : hd.snd.snd = Eq.mp (by rw[hhd.left]) rn := by
            exact h
          rw[this]
          simp
        . intro h
          let f := fun (p: Lax392996.Databases.Tuple T hd.2.1 × K) ↦ Fin.append (fun k ↦ Sum.inl (p.1 k)) ![Sum.inr p.2]
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
      . simp[Lax392996.AnnotatedDatabases.AnnotatedDatabase.find.f, Lax392996.Databases.Database.find.f, hhd]
        exact ih

end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase

export Lax392996Proofs.Foreign.AnnotatedDatabase (find_toComposite_some)

end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace AnnotatedDatabase
export Lax392996Proofs.Foreign.AnnotatedDatabase (find_toComposite_some)
end AnnotatedDatabase

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple

open Lax392996Proofs.Foreign.AnnotatedTuple in
lemma _root_.Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_join {K: Type} {T: Type}
  [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.HasAltLinearOrder K] [Lax392996.SemiringsWithMonus.SemiringWithMonus K]
    (ta₁: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n₁)
    (ta₂: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n₂):
  Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite (Fin.append ta₁.1 ta₂.1, ta₁.2 * ta₂.2) = fun (k: Fin (n₁+n₂+1)) ↦
    if h: ↑k < n₁ then ta₁.toComposite (k.castLT (Nat.lt_add_right 1 h))
    else if ↑k < n₁ + n₂ then ta₂.toComposite (@Fin.ofNat (n₂+1) _ (k.toNat - n₁))
    else ta₁.toComposite (Fin.last n₁) * ta₂.toComposite (Fin.last n₂) := by
    unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
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

end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple

export Lax392996Proofs.Foreign.AnnotatedTuple (toComposite_join)

end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace AnnotatedTuple
export Lax392996Proofs.Foreign.AnnotatedTuple (toComposite_join)
end AnnotatedTuple

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

open Lax392996Proofs.Foreign.AnnotatedRelation in
theorem _root_.Lax392996Proofs.Foreign.AnnotatedRelation.toComposite_map_product {K: Type} {T: Type}
  [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.HasAltLinearOrder K] [Lax392996.SemiringsWithMonus.SemiringWithMonus K]
  (ar₁: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n₁) (ar₂: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n₂) :
  Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite (
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
    unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite Multiset.product
    simp
  | @cons p tl ih =>
    unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite Multiset.product at *
    rw [Multiset.cons_bind, Multiset.map_add, Multiset.map_add, Multiset.map_cons,
        Multiset.cons_bind, Multiset.map_add]
    congr 1
    -- For the head `p`: show maps are equal element-wise over `ar₂`.
    · simp only [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro q _
      simp only [Function.comp]
      exact Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_join p q

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

export Lax392996Proofs.Foreign.AnnotatedRelation (toComposite_map_product)

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace AnnotatedRelation
export Lax392996Proofs.Foreign.AnnotatedRelation (toComposite_map_product)
end AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

open Lax392996Proofs.Foreign.AnnotatedRelation in
theorem _root_.Lax392996Proofs.Foreign.AnnotatedRelation.cast_toComposite {T: Type} {K: Type}
  (ar: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) (h': n+1=m+1) (h: n = m) :
  ar.toComposite.cast h' = (ar.cast h).toComposite := by
  subst h
  congr

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

export Lax392996Proofs.Foreign.AnnotatedRelation (cast_toComposite)

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace AnnotatedRelation
export Lax392996Proofs.Foreign.AnnotatedRelation (cast_toComposite)
end AnnotatedRelation


