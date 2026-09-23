/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AnnotatedDatabase

/-!
# Relations read as families of occurrences

An annotated relation is a multiset of annotated tuples, so two copies of a
tuple carrying the same annotation are one element with multiplicity two:
nothing tells them apart. That is the right reading for most of the algebra,
where an operator treats equal rows equally.

Three things need more. An operator may give two equal rows *different*
results – a window frame that excludes the row it is computed for reads its
twin and not itself, so the two rows get different aggregate values from the
same relation. A comparison may read two aggregate values whose occurrence
families overlap, and then the worlds it sums over are subfamilies of their
union, which needs an occurrence of one family to be recognisable as an
occurrence of the other. And a statement *about* an operator may quantify
over the ways equal rows could be told apart, which is how one shows that no
operator selecting rows can have the behaviour of `EXCEPT ALL`.

This module gives the finer reading: a relation as a family indexed by
occurrences, where the index is the identity a multiset discards. It does not
replace `AnnotatedRelation`; it sits beside it, with `toRelation` forgetting
the index. An operator defined on families is meaningful exactly when its
result does not depend on which indexing was chosen, which is what
`Congr` below expresses.
-/

variable {T K : Type} {n : ℕ}

/-- An annotated relation read as a family of occurrences: `size` of them,
each an annotated tuple. Two copies of a tuple are two occurrences, told
apart by their index, and an aggregate value built from this relation names
its occurrences by the same index – which is what lets two such values speak
of the same occurrence. -/
structure OccRel (T K : Type) (n : ℕ) where
  /-- How many occurrences the relation has. -/
  size : ℕ
  /-- The occurrence at each index. -/
  row : Fin size → AnnotatedTuple T K n

namespace OccRel

/-- Forgetting the index: the annotated relation the family stands for. -/
def toRelation (r : OccRel T K n) : AnnotatedRelation T K n :=
  (Finset.univ : Finset (Fin r.size)).val.map r.row

/-- The empty family. -/
def nil : OccRel T K n := ⟨0, fun i => i.elim0⟩

@[simp] theorem toRelation_nil : (nil : OccRel T K n).toRelation = 0 := rfl

@[simp] theorem card_toRelation (r : OccRel T K n) :
    Multiset.card r.toRelation = r.size := by
  simp [toRelation, AnnotatedRelation]

/-- Two families index the same relation when a bijection of their indices
matches their occurrences. This is the relation an operator on families has
to respect: the choice of index is not data, only the occurrences are. -/
def Congr (r r' : OccRel T K n) : Prop :=
  ∃ e : Fin r.size ≃ Fin r'.size, ∀ i, r'.row (e i) = r.row i

theorem Congr.refl (r : OccRel T K n) : Congr r r :=
  ⟨Equiv.refl _, fun _ => rfl⟩

theorem Congr.symm {r r' : OccRel T K n} (h : Congr r r') : Congr r' r := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun i => by rw [← he (e.symm i), Equiv.apply_symm_apply]⟩

theorem Congr.trans {r r' r'' : OccRel T K n}
    (h : Congr r r') (h' : Congr r' r'') : Congr r r'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun i => by rw [Equiv.trans_apply, he' (e i), he i]⟩

/-- Congruent families stand for the same relation: re-indexing is invisible
once the index is forgotten. -/
theorem toRelation_congr {r r' : OccRel T K n} (h : Congr r r') :
    r.toRelation = r'.toRelation := by
  obtain ⟨e, he⟩ := h
  show Multiset.map r.row _ = Multiset.map r'.row _
  rw [show Multiset.map r.row (Finset.univ : Finset (Fin r.size)).val
        = Multiset.map (fun i => r'.row (e i)) Finset.univ.val from
      Multiset.map_congr rfl (fun i _ => (he i).symm),
    show (fun i => r'.row (e i)) = r'.row ∘ ⇑e from rfl, ← Multiset.map_map]
  congr 1
  rw [show Multiset.map (⇑e) (Finset.univ : Finset (Fin r.size)).val
        = ((Finset.univ : Finset (Fin r.size)).map e.toEmbedding).val from rfl,
    Finset.map_univ_equiv]

end OccRel
