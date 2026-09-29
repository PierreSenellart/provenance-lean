/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Normalize

/-!
# Aggregate columns read as keys: the alternatives

An operator reads a column either as a *value*, in a term, or as a
*key*, compared syntactically – the grouping indices of `γ`, the
partition and order of a window, the tuples `ε` merges and the
difference matches. Over a plain relation an aggregate value is a
value and both readings are the ordinary ones. Over an annotated
relation a key is read in each world, and an occurrence whose column
`i` holds an aggregate value `a` is read through its **alternatives**,
one for each value `a` takes:

    (u[i ↦ v], α ⊗ [a ≐ v])   for v ∈ Val(a),

where `[a ≐ v]` is the predicate provenance of the atom `a = v` –
`AggValue.altProv`, read with SQL's null-safe equality so that the case
`v = NULL` is the atom `a IS NULL` and needs no separate clause. The
column of an alternative is regular, and the operator applies to the
alternatives. A `GROUP BY` on a count has thus one group per count the
groups can take, and a `DISTINCT`, a difference or a union over an
aggregate column is read likewise.

Two facts make the reading a reading of the worlds and not a way of
enumerating values. `AggValue.sum_altProv`: the alternatives' shares
add up to the whole of what the aggregate value's worlds carry, so
nothing is lost and nothing is invented. `AggValue.altProv_mul_eq_zero`:
distinct alternatives of one occurrence exclude each other where `K` is
exclusive, since distinct values come from distinct worlds – which is
the remark that in `𝔹[X]` exactly one alternative of a present
occurrence holds under each valuation, and that over `ℕ[X]`, where
exclusivity fails, an operator combining two alternatives of one
occurrence counts worlds that do not exist.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]



/-! ## The alternatives of an occurrence -/

/-- An alternative's column is regular, which is what lets the operator
compare it as a key. -/
theorem GenRow.alternativesAt_reg {n : ℕ} (r : GenRow T K n) (i : Fin n)
    (a : AggValue T K) (h : r.fst i = Sum.inr a) :
    ∀ s ∈ r.alternativesAt i, ∃ v : T, s.fst i = Sum.inl v := by
  intro s hs
  rw [GenRow.alternativesAt, h] at hs
  obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hs
  exact ⟨v, Function.update_self i (Sum.inl v) r.fst⟩

/-- **What the alternatives carry between them**: the occurrence's
concrete part times the whole of what the aggregate value's worlds
carry. Where that mass is `𝟙` – and a group row's existence factor is
what makes it so – the alternatives carry exactly the occurrence. -/
theorem GenRow.sum_alternativesAt_base {n : ℕ} (r : GenRow T K n) (i : Fin n)
    (a : AggValue T K) (h : r.fst i = Sum.inr a) :
    ((r.alternativesAt i).map (fun s => s.snd.base)).sum
      = r.snd.base * ∑ W ∈ a.worlds, Having.worldAnn a.anns W := by
  rw [GenRow.alternativesAt, h, Multiset.map_map, ← AggValue.sum_altProv,
    Finset.mul_sum]
  rfl
