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
replace `AnnotatedRelation`; it sits beside it, with `toMultiset` forgetting
the index. An operator defined on families is meaningful exactly when its
result does not depend on which indexing was chosen, which is what
`Congr` below expresses.
-/

variable {α : Type}

/-- A relation read as a family of occurrences: `size` of them, each a row
of type `α`. Two copies of a row are two occurrences, told apart by their
index, and an aggregate value built from this relation names its occurrences
by the same index – which is what lets two such values speak of the same
occurrence.

The row type is a parameter because the rows a window produces are not the
rows it reads: it appends an aggregate column, so its output rows carry a
token where its input rows carry only values. -/
structure OccFam (α : Type) where
  /-- How many occurrences the family has. -/
  size : ℕ
  /-- The occurrence at each index. -/
  row : Fin size → α

namespace OccFam

/-- Forgetting the index: the multiset of rows the family stands for. -/
def toMultiset (r : OccFam α) : Multiset α :=
  (Finset.univ : Finset (Fin r.size)).val.map r.row

/-- The empty family. -/
def nil : OccFam α := ⟨0, fun i => i.elim0⟩

@[simp] theorem toMultiset_nil : (nil : OccFam α).toMultiset = 0 := rfl

@[simp] theorem card_toMultiset (r : OccFam α) :
    Multiset.card r.toMultiset = r.size := by
  simp [toMultiset]

/-- Two families index the same relation when a bijection of their indices
matches their occurrences. This is the relation an operator on families has
to respect: the choice of index is not data, only the occurrences are. -/
def Congr (r r' : OccFam α) : Prop :=
  ∃ e : Fin r.size ≃ Fin r'.size, ∀ i, r'.row (e i) = r.row i

theorem Congr.refl (r : OccFam α) : Congr r r :=
  ⟨Equiv.refl _, fun _ => rfl⟩

theorem Congr.symm {r r' : OccFam α} (h : Congr r r') : Congr r' r := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun i => by rw [← he (e.symm i), Equiv.apply_symm_apply]⟩

theorem Congr.trans {r r' r'' : OccFam α}
    (h : Congr r r') (h' : Congr r' r'') : Congr r r'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun i => by rw [Equiv.trans_apply, he' (e i), he i]⟩

/-- Congruent families stand for the same relation: re-indexing is invisible
once the index is forgotten. -/
theorem toMultiset_congr {r r' : OccFam α} (h : Congr r r') :
    r.toMultiset = r'.toMultiset := by
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

/-! ## A relation read as a family

An operator on families is meaningful when it respects `Congr`. To *apply*
one to a relation, a relation has to be read as a family, which means
choosing an indexing. `ofMultiset` chooses one; `toMultiset_ofMultiset` says
the choice is faithful, and `Congr_of_toMultiset_eq` says any two choices are
the same family, so that an operator respecting `Congr` gives an answer that
does not depend on the choice. -/

/-- A choice of indexing for a multiset. -/
noncomputable def ofMultiset (s : Multiset α) : OccFam α :=
  ⟨s.toList.length, fun i => s.toList.get i⟩

@[simp] theorem size_ofMultiset (s : Multiset α) :
    (ofMultiset s).size = Multiset.card s := Multiset.length_toList s

@[simp] theorem toMultiset_ofMultiset (s : Multiset α) :
    (ofMultiset s).toMultiset = s := by
  show Multiset.map s.toList.get
      (Finset.univ : Finset (Fin s.toList.length)).val = s
  rw [show (Finset.univ : Finset (Fin s.toList.length)).val
        = Multiset.ofList (List.finRange s.toList.length) from rfl,
    Multiset.map_coe, ← List.ofFn_eq_map, List.ofFn_get, Multiset.coe_toList]

/-- **Any two indexings of a relation are the same family.** Two families
with the same multiset of rows differ by a permutation of their indices, so
an operator that respects `Congr` answers the same on both, and reading a
relation as a family involves no arbitrary choice.

This is the standard fact that a permutation of lists gives a bijection of
positions carrying one to the other, which Mathlib does not appear to state
for lists with repeats. It is the one obligation of this module left open;
nothing below depends on it for its definition, only for the claim that the
definition is about relations rather than about indexings. -/
theorem Congr_of_toMultiset_eq {r r' : OccFam α}
    (h : r.toMultiset = r'.toMultiset) : Congr r r' := by
  sorry

end OccFam
