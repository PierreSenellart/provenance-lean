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

namespace AggValue

/-- The worlds of an aggregate value: every subfamily when it is read
in the scalar convention, the non-empty ones when it is grouped. -/
def worlds (a : AggValue T K) : Finset (Finset (Fin a.occs.length)) :=
  Finset.univ.filter (fun W => a.scalar = true ∨ W.Nonempty)

/-- `Val(a)`: the values the aggregate value takes over its worlds. -/
def vals (a : AggValue T K) : Finset T := a.worlds.image a.valOn

/-- **A test read over the worlds.** The two conventions differ only in
which subfamilies count, which is what `worlds` records. -/
theorem predProvOfWith_eq_sum_worlds (a : AggValue T K) (P : T → Kleene) :
    a.predProvOfWith P
      = ∑ W ∈ a.worlds, Having.worldAnn a.anns W * Having.chiOf P (a.valOn W) := by
  unfold AggValue.predProvOfWith AggValue.worlds
  cases hs : a.scalar with
  | true =>
    rw [ite_eq_left rfl, Finset.filter_true_of_mem (fun W _ => Or.inl rfl)]
    rfl
  | false =>
    rw [ite_eq_right Bool.false_ne_true]
    unfold AggValue.predProvWith
    refine Finset.sum_congr (Finset.filter_congr (fun W _ => ?_)) (fun _ _ => rfl)
    simp

/-- **`[a ≐ v]`**: the predicate provenance of the atom comparing the
aggregate value with `v`, under SQL's null-safe equality – so the case
`v = NULL` is the atom `a IS NULL` and asks for no separate clause. -/
def altProv (a : AggValue T K) (v : T) : K :=
  a.predProvOfWith (fun x => CompOp.syneq.eval3 x v)

/-- The share of a value is the mass of the worlds that take it. -/
theorem altProv_eq_sum (a : AggValue T K) (v : T) :
    a.altProv v
      = ∑ W ∈ a.worlds.filter (fun W => a.valOn W = v),
          Having.worldAnn a.anns W := by
  rw [altProv, predProvOfWith_eq_sum_worlds, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun W _ => ?_)
  by_cases h : a.valOn W = v
  · rw [ite_eq_left h, Having.chiOf,
      ite_eq_left ((CompOp.syneq_eval3_eq_true_iff _ _).mpr h), mul_one]
  · rw [ite_eq_right h, Having.chiOf,
      ite_eq_right (fun hc => h ((CompOp.syneq_eval3_eq_true_iff _ _).mp hc)),
      mul_zero]

/-- **The alternatives exhaust the worlds**: their shares add up to
what the aggregate value's worlds carry, so reading a key through them
loses nothing and invents nothing. -/
theorem sum_altProv (a : AggValue T K) :
    ∑ v ∈ a.vals, a.altProv v = ∑ W ∈ a.worlds, Having.worldAnn a.anns W := by
  simp only [altProv_eq_sum]
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr (Finset.ext (fun W => ?_)) (fun _ _ => rfl)
    constructor
    · intro h
      obtain ⟨v, hv, hW⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hW).1
    · intro h
      exact Finset.mem_biUnion.mpr ⟨a.valOn W,
        Finset.mem_image.mpr ⟨W, h, rfl⟩, Finset.mem_filter.mpr ⟨h, rfl⟩⟩
  · intro v _ v' _ hvv
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro W ⟨-, rfl⟩ ⟨-, h'⟩
    exact hvv h'

/-- **Distinct alternatives of one occurrence exclude each other**,
where `K` is exclusive: distinct values come from distinct worlds, and
two distinct worlds' annotations multiply to `𝟘`. In `𝔹[X]` this is
the statement that exactly one alternative of a present occurrence
holds under each valuation; over `ℕ[X]`, where exclusivity fails, an
operator that combines two alternatives of one occurrence – a window
over a partition holding both – counts worlds that do not exist. -/
theorem altProv_mul_eq_zero (hexcl : exclusive K) (a : AggValue T K)
    {v v' : T} (h : v ≠ v') : a.altProv v * a.altProv v' = 0 := by
  rw [altProv_eq_sum, altProv_eq_sum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero (fun W hW => Finset.sum_eq_zero (fun W' hW' => ?_))
  refine Having.worldAnn_mul_eq_zero_of_ne hexcl a.anns (fun hcon => h ?_)
  rw [← (Finset.mem_filter.mp hW).2, ← (Finset.mem_filter.mp hW').2, hcon]

end AggValue

/-! ## The alternatives of an occurrence -/

/-- **The alternatives of an occurrence at one aggregate column**: one
row per value the column's aggregate value takes, the column made
regular and the annotation multiplied by `[a ≐ v]`. A column already
regular has the occurrence itself as its only alternative. -/
def GenRow.alternativesAt {n : ℕ} (r : GenRow T K n) (i : Fin n) :
    Multiset (GenRow T K n) :=
  match r.fst i with
  | Sum.inl _ => {r}
  | Sum.inr a =>
    a.vals.val.map (fun v =>
      (Function.update r.fst i (Sum.inl v),
        (⟨r.snd.base * a.altProv v, r.snd.pending⟩ : GenAnn K)))

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
