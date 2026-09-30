/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggValue

/-!
# Nested aggregate values

When the term of an aggregation or a window reads an aggregate column,
the aggregate value it builds is **nested**: what it aggregates, at
each of its occurrences, is not a value of the domain but another
aggregate value. Its occurrences are those of its own family `U`
*together with* those of the inner values, and its value in a world is
the outer aggregate applied to the inner values read in that world.

An `AggValue` cannot hold this: its reading consults its own occurrence
list alone. `NestedValue` carries, per outer occurrence, the inner
aggregate value the term reads there, and a `World` chooses which outer
occurrences are present *and* which occurrences of each inner value
are.

## Which worlds count

A world meets the family of each grouped inner value **that it reads**,
which is to say each inner value at an outer occurrence the world keeps
– `World.IsWorld`. The condition is on the inner values read and not on
all of them: an outer occurrence absent from the world contributes
nothing to the value there, and asking its inner family to be met would
ask a group to be non-empty while the row carrying it is absent.

This is not the condition a *predicate*'s worlds satisfy, which meet
every grouped family the predicate mentions with no such conditionality
– and the difference is structural rather than an oversight. A
predicate's families all belong to one tuple, which exists or does not,
so demanding all of them demands that the tuple exist. A nested value's
inner families each belong to a *different* outer occurrence, and the
world is choosing which of those occurrences are present, so a blanket
condition would quantify over occurrences the world has already
excluded.

Whether a world should also be *barred* from meeting the family of an
inner value it does not read is open, and the predicate is a parameter
of everything below (`World.IsWorldWith`) so that either answer is a
substitution. No instance realizes such a world – the outer occurrence
is annotated `δ(β)` for the very family at issue, and in an exclusive
semiring the complement factor annihilates them – so the choice is
between imposing the coherence and letting exclusivity dispose of it.
-/

variable {T K : Type} [ValueType T]

/-- **A nested aggregate value**: an outer aggregate over occurrences
that carry aggregate values rather than values. -/
structure NestedValue (T K : Type) where
  /-- The outer aggregate. -/
  agg : SeqAggFunc T
  /-- Per outer occurrence, the inner aggregate value the term reads
  there and the occurrence's own annotation. -/
  occs : List (AggValue T K × K)
  /-- Whether the outer reading is scalar – whether the empty world is
  one of its worlds. -/
  scalar : Bool

namespace NestedValue

/-- The inner aggregate value at an outer occurrence. -/
def innerAt (a : NestedValue T K) (i : Fin a.occs.length) : AggValue T K :=
  (a.occs.get i).1

/-- The annotation of an outer occurrence. -/
def outerAnn (a : NestedValue T K) (i : Fin a.occs.length) : K :=
  (a.occs.get i).2

/-- **A world of a nested value**: which outer occurrences are present,
and which occurrences of each inner value are. -/
structure World (a : NestedValue T K) where
  /-- The outer occurrences present. -/
  outer : Finset (Fin a.occs.length)
  /-- For each outer occurrence, the occurrences of its inner value
  that are present. -/
  inner : (i : Fin a.occs.length) → Finset (Fin (a.innerAt i).occs.length)

/-- **Admissibility, with the coherence condition as a parameter.**
`extra` is the clause `q:nestedcoherent` leaves open – whether a world
is barred from meeting the family of an inner value it does not read.
The document's reading is `IsWorld`, which takes `extra` to be
vacuous. -/
def World.IsWorldWith {a : NestedValue T K}
    (extra : a.World → Prop) (W : a.World) : Prop :=
  (a.scalar = true ∨ W.outer.Nonempty)
    ∧ (∀ i ∈ W.outer, (a.innerAt i).scalar = false → (W.inner i).Nonempty)
    ∧ extra W

/-- **The worlds the document commits to**: the outer family met unless
the reading is scalar, and the family of each grouped inner value *that
the world reads* met. -/
def World.IsWorld {a : NestedValue T K} (W : a.World) : Prop :=
  World.IsWorldWith (fun _ => True) W

/-- The reading that bars a world from meeting the family of an inner
value it does not read – the other answer to `q:nestedcoherent`. -/
def World.IsWorldCoherent {a : NestedValue T K} (W : a.World) : Prop :=
  World.IsWorldWith (fun W => ∀ i ∉ W.outer, W.inner i = ∅) W

/-- **The value of a nested aggregate in a world**: the outer aggregate
of the inner values read there, in the order of the outer
occurrences. -/
def valOn {a : NestedValue T K} (W : a.World) : T :=
  a.agg (((List.finRange a.occs.length).filter (fun i => i ∈ W.outer)).map
    (fun i => (a.innerAt i).valOn (W.inner i)))

/-- The world in which every occurrence, outer and inner, is present. -/
def World.full (a : NestedValue T K) : a.World :=
  ⟨Finset.univ, fun _ => Finset.univ⟩

/-- **The deterministic reading**: the outer aggregate of the inner
collapses. -/
def collapse (a : NestedValue T K) : T :=
  a.agg (a.occs.map (fun o => o.1.collapse))

omit [ValueType T] in
/-- **Everything present reads as the collapse.** -/
theorem valOn_full (a : NestedValue T K) :
    valOn (World.full a) = a.collapse := by
  unfold valOn collapse World.full
  refine congrArg a.agg ?_
  rw [List.filter_eq_self.mpr (fun i _ => by simp)]
  refine List.ext_get (by simp) (fun i h₁ h₂ => ?_)
  simp only [List.get_eq_getElem, List.getElem_map, NestedValue.innerAt,
    List.get_eq_getElem]
  rw [show ((List.finRange a.occs.length)[i]'(by simpa using h₁) : Fin a.occs.length)
      = ⟨i, by simpa using h₂⟩ from by simp]
  exact (AggValue.collapse_eq_valOn_univ _).symm

/-! ## What a world of a nested value is annotated

The annotation is the one every family gets: the product of what is
present times `𝟙 ⊖` the sum of what is absent. It does not depend on
`q:nestedcoherent`, which is about *which* worlds are admitted and not
about how a given one is weighed – so it can be written now. The inner
products range over every outer occurrence, which is the literal
reading of "the occurrences present in `W`"; under the coherent reading
they collapse to the occurrences the world actually reads
(`World.presentProd_eq_of_coherent`). -/

section Annotation

variable [CommSemiringWithMonus K]

/-- The product of the annotations a world keeps: the outer occurrences
it keeps and, for each outer occurrence, the inner ones it keeps. -/
def World.presentProd {a : NestedValue T K} (W : a.World) : K :=
  (∏ i ∈ W.outer, a.outerAnn i)
    * ∏ i : Fin a.occs.length, ∏ j ∈ W.inner i, (a.innerAt i).anns j

/-- The sum of the annotations a world leaves out. -/
def World.absentSum {a : NestedValue T K} (W : a.World) : K :=
  (∑ i ∈ W.outerᶜ, a.outerAnn i)
    + ∑ i : Fin a.occs.length, ∑ j ∈ (W.inner i)ᶜ, (a.innerAt i).anns j

/-- **The annotation of a world of a nested value.** -/
def World.ann {a : NestedValue T K} (W : a.World) : K :=
  W.presentProd * (1 - W.absentSum)

omit [ValueType T] in
/-- Nothing is absent from the full world. -/
@[simp] theorem World.absentSum_full (a : NestedValue T K) :
    (World.full a).absentSum = 0 := by
  unfold World.absentSum World.full
  simp

omit [ValueType T] in
/-- **The full world is annotated by the product of everything.** -/
theorem World.ann_full (a : NestedValue T K) :
    (World.full a).ann = (World.full a).presentProd := by
  rw [World.ann, World.absentSum_full, monus_zero, mul_one]

omit [ValueType T] in
/-- **Under the coherent reading the inner products are over the
occurrences the world reads**: an outer occurrence the world drops
keeps no inner occurrence, so its factor is empty. -/
theorem World.presentProd_eq_of_coherent {a : NestedValue T K}
    {W : a.World} (h : ∀ i ∉ W.outer, W.inner i = ∅) :
    W.presentProd
      = (∏ i ∈ W.outer, a.outerAnn i)
        * ∏ i ∈ W.outer, ∏ j ∈ W.inner i, (a.innerAt i).anns j := by
  have hp : (∏ i : Fin a.occs.length, ∏ j ∈ W.inner i, (a.innerAt i).anns j)
      = ∏ i ∈ W.outer, ∏ j ∈ W.inner i, (a.innerAt i).anns j :=
    (Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
      rw [h i hi, Finset.prod_empty])).symm
  rw [World.presentProd, hp]

end Annotation

omit [ValueType T] in
/-- A world of the document's reading is one of the coherent reading's
as soon as it keeps no inner occurrence it does not read. -/
theorem World.isWorld_of_isWorldCoherent {a : NestedValue T K}
    {W : a.World} (h : W.IsWorldCoherent) : W.IsWorld :=
  ⟨h.1, h.2.1, trivial⟩



/-! ## The readings over the nested worlds

With the world set fixed – the coherence clause not imposed – the two
readings a nested value owes can be written: the predicate provenance
of a test of its value, and the world-faithful reading under a
valuation of the annotations. Both are the `AggValue` ones with
`World` in place of a subfamily and `World.ann` in place of
`Having.worldAnn`.

Summing over the worlds needs them to be finitely many, which they are:
a world is a subfamily of the outer occurrences together with one of
each inner family. -/

section Readings

variable [CommSemiringWithMonus K] [DecidableEq K]

/-- A world is an outer subfamily together with one subfamily per inner
value. -/
def World.equivSigma (a : NestedValue T K) :
    a.World ≃ (Finset (Fin a.occs.length)
      × ((i : Fin a.occs.length) → Finset (Fin (a.innerAt i).occs.length))) where
  toFun W := (W.outer, W.inner)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (a : NestedValue T K) : Fintype a.World :=
  Fintype.ofEquiv _ (World.equivSigma a).symm

instance (a : NestedValue T K) : DecidableEq a.World :=
  fun _ _ => decidable_of_iff _ (World.equivSigma a).apply_eq_iff_eq

instance {a : NestedValue T K} : DecidablePred (World.IsWorld (a := a)) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The predicate provenance of a test of a nested value**: the `⊕`
over its worlds of the world's annotation times the truth of the test
there. -/
def predProvWith (a : NestedValue T K) (P : T → Kleene) : K :=
  ∑ W ∈ Finset.univ.filter (fun W : a.World => W.IsWorld),
    W.ann * Having.chiOf P (valOn W)

/-- The comparison case. -/
def predProvOf (a : NestedValue T K) (op : CompOp) (c : T) : K :=
  a.predProvWith (fun v => op.eval3 v c)

/-- **The world a valuation of the annotations realizes**: every
occurrence, outer or inner, whose annotation the valuation makes
true. -/
def realizedWorld (a : NestedValue T K) (ν : K → Bool) : a.World :=
  ⟨Finset.univ.filter (fun i => ν (a.outerAnn i)),
    fun i => Finset.univ.filter (fun j => ν ((a.innerAt i).anns j))⟩

/-- **The world-faithful reading**: the value in the realized world. -/
def specialize (a : NestedValue T K) (ν : K → Bool) : T :=
  valOn (a.realizedWorld ν)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A valuation that keeps every occurrence realizes the full world. -/
theorem realizedWorld_of_forall (a : NestedValue T K) (ν : K → Bool)
    (h : ∀ x : K, ν x = true) : a.realizedWorld ν = World.full a := by
  unfold realizedWorld World.full
  refine congrArg₂ World.mk (Finset.filter_true_of_mem (fun i _ => h _)) ?_
  funext i
  exact Finset.filter_true_of_mem (fun j _ => h _)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **Where every occurrence is realized the reading is the
collapse**, so the world-faithful reading and the deterministic one
agree on the database as it is. -/
theorem specialize_of_forall (a : NestedValue T K) (ν : K → Bool)
    (h : ∀ x : K, ν x = true) : a.specialize ν = a.collapse := by
  rw [specialize, realizedWorld_of_forall a ν h, valOn_full]

omit [ValueType T] [DecidableEq K] in
/-- **A test no value satisfies annotates `𝟘`.** -/
theorem predProvWith_of_never (a : NestedValue T K) {P : T → Kleene}
    (h : ∀ v : T, P v ≠ Kleene.true) : a.predProvWith P = 0 := by
  refine Finset.sum_eq_zero (fun W _ => ?_)
  rw [Having.chiOf, ite_eq_right (h _), mul_zero]

end Readings

/-! ## Nothing nested: the degenerate case

A nested value whose inner values read nothing is an ordinary aggregate
value, and it had better be annotated like one. `constInner v` is the
inner value that reads no occurrence and returns `v`; `ofAggValue`
builds the nested value of a token by putting one at each of its
occurrences, and `ann_worldOf` says a world of it carries exactly
`Having.worldAnn` of the token's own family. -/

/-- The inner value that reads nothing and returns `v`. Its only world
is the empty one, and it contributes no occurrence. -/
def constInner (v : T) : AggValue T K := ⟨fun _ => v, [], true⟩

/-- **The nested value of an ordinary token**: nothing is nested, each
occurrence carrying a value rather than a family. -/
def ofAggValue (a : AggValue T K) : NestedValue T K :=
  ⟨a.agg, a.occs.map (fun o => (constInner o.fst, o.snd)), a.scalar⟩

omit [ValueType T] in
theorem length_ofAggValue (a : AggValue T K) :
    a.occs.length = (ofAggValue a).occs.length := (List.length_map _).symm

omit [ValueType T] in
@[simp] theorem outerAnn_ofAggValue (a : AggValue T K)
    (i : Fin a.occs.length) :
    (ofAggValue a).outerAnn (finCongr (length_ofAggValue a) i) = a.anns i := by
  show ((a.occs.map (fun o => (constInner o.fst, o.snd))).get
    (finCongr (length_ofAggValue a) i)).snd = _
  simp [AggValue.anns]

/-- A world of the token, as a world of its nested form. -/
def worldOf (a : AggValue T K) (W : Finset (Fin a.occs.length)) :
    (ofAggValue a).World :=
  ⟨W.map (finCongr (length_ofAggValue a)).toEmbedding, fun _ => ∅⟩

section DegenerateAnn

variable [CommSemiringWithMonus K]

omit [ValueType T] in
/-- **A world of an unnested value is annotated as the token's own
family annotates it.** -/
theorem ann_worldOf (a : AggValue T K) (W : Finset (Fin a.occs.length)) :
    (worldOf a W).ann = Having.worldAnn a.anns W := by
  have hinner : ∀ i : Fin (ofAggValue a).occs.length,
      ((ofAggValue a).innerAt i).occs.length = 0 := by
    intro i
    simp only [NestedValue.innerAt, ofAggValue, List.get_eq_getElem,
      List.getElem_map]
    rfl
  unfold World.ann World.presentProd World.absentSum worldOf Having.worldAnn
  have h1 : (∏ i ∈ W.map (finCongr (length_ofAggValue a)).toEmbedding,
        (ofAggValue a).outerAnn i) = ∏ i ∈ W, a.anns i := by
    rw [Finset.prod_map]
    exact Finset.prod_congr rfl (fun i _ => outerAnn_ofAggValue a i)
  have h3 : (∑ i ∈ (W.map (finCongr (length_ofAggValue a)).toEmbedding)ᶜ,
        (ofAggValue a).outerAnn i) = ∑ i ∈ Wᶜ, a.anns i := by
    have hcompl : ((W.map (finCongr (length_ofAggValue a)).toEmbedding))ᶜ
        = Wᶜ.map (finCongr (length_ofAggValue a)).toEmbedding := by
      ext j
      rw [Finset.mem_compl, Finset.mem_map_equiv, Finset.mem_map_equiv,
        Finset.mem_compl]
    rw [hcompl, Finset.sum_map]
    exact Finset.sum_congr rfl (fun i _ => outerAnn_ofAggValue a i)
  have h2 : (∏ i : Fin (ofAggValue a).occs.length,
        ∏ j ∈ (∅ : Finset (Fin ((ofAggValue a).innerAt i).occs.length)),
          ((ofAggValue a).innerAt i).anns j) = 1 :=
    Finset.prod_eq_one (fun i _ => Finset.prod_empty)
  have h4 : (∑ i : Fin (ofAggValue a).occs.length,
        ∑ j ∈ (∅ : Finset (Fin ((ofAggValue a).innerAt i).occs.length))ᶜ,
          ((ofAggValue a).innerAt i).anns j) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    have hj := j.isLt
    exact absurd (hinner i) (by omega)
  rw [h1, h2, h3, h4, mul_one, add_zero]

end DegenerateAnn

end NestedValue
