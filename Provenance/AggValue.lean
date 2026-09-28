/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.HavingSemantics

/-!
# Symbolic aggregate tokens

`AggValue T K` is the symbolic aggregate token of the general HAVING
semantics: an aggregate function together with the ≼-sorted occurrence
payload of the originating group, projected to pairs (value of the
aggregated term, occurrence annotation) – exactly the data of
`Having.havingGroup` that the possible-world semantics of an aggregate
comparison consumes. It is the one-level analogue of `KTensor`
(deliberately un-quotiented, so the possible worlds of the group can be
read off the token); there is no recursion: ProvSQL rejects aggregation,
grouping and ordering *over* aggregate values, and likewise rejects
deduplication and difference on token-carrying relations, so no linear
order or decidable equality on tokens is required by any permitted
downstream operator (`SeqAggFunc` being a function type, structural
decidable equality would not be available anyway).

## Readings of a token

* `valOn` – the aggregate value in one possible world of the group,
  matching `Having.aggValOn` on the originating group (`valOn_ofGroup`);
* `specialize` – the world-faithful reading: restrict to the occurrences
  whose annotation is realized by a valuation and aggregate those;
* `collapse` – the deterministic reading: aggregate the whole sequence.
  This is the value ProvSQL displays for an uncompared aggregate (the
  actual-world value, rendered `v (*)`), and the reading through which
  the data-part adequacy of the general evaluator is stated;
* `predProv` – the predicate provenance of a comparison against the
  token: the `⊕`-sum, over the non-empty possible worlds of the group,
  of the world annotation times the characteristic value of the
  comparison. On a token built from a group it coincides with the fused
  semantics' `Having.havingProv` (`predProv_ofGroup`) – the seed of the
  regression bridge between the general and the fused evaluators.

`mapAnn` pushes a function `K → K'` through the annotations of a token:
value-only readings are unchanged (`collapse_mapAnn`) and `specialize`
composes with the pushforward (`specialize_mapAnn`). This is the token
layer of the hom-commutation metatheorem for the general evaluator.

## Lifted column values

A column of a token-carrying relation holds either a regular value or a
token: `T ⊕ AggValue T K`. `AggValue.mapAnnSum` and `AggValue.collapseSum`
extend the pushforward and the deterministic reading to such lifted
values; the kind-indexed syntax of the general evaluator governs
statically which columns hold which arm.
-/

/-- A symbolic aggregate token: an aggregate function together with the
(≼-sorted) occurrence payload of the originating group – for each
occurrence, the value of the aggregated term paired with the occurrence
annotation. -/
structure AggValue (T K : Type) where
  /-- The sequence aggregate applied by every reading of the token. -/
  agg : SeqAggFunc T
  /-- The occurrence payload: values of the aggregated term paired with
  the occurrence annotations, in the group's ≼-order. -/
  occs : List (T × K)
  /-- Whether the empty world is one of this token's worlds.

  A token whose row exists only because its group does is never read where
  the group is empty, and the reading skips that world. A token whose row
  exists on its own – an aggregation with no grouping, whose single row
  survives an empty input, or a window frame that may exclude the row it is
  computed for – is read there too, and the aggregate then sees the empty
  sequence. The flag travels with the token because a comparison may be far
  from the operator that built it, past projections and joins, and cannot
  otherwise tell which reading applies. -/
  scalar : Bool := false

namespace AggValue

variable {T K K' : Type} {m : ℕ}

/-- The token of a group with occurrence sequence `U`, aggregating the
term `t` with `f`: the projection of the group payload. -/
def ofGroup [ValueType T] {c : ℕ} (f : SeqAggFunc T) (t : TermIn T c m)
    (U : List (AnnotatedTuple T K m))
    (γ : Fin c → T := fun _ => 0) : AggValue T K :=
  ⟨f, U.map (fun p => (t.eval p.fst γ, p.snd)), false⟩

/-- The occurrence annotations of a token, as a function on positions. -/
def anns (a : AggValue T K) : Fin a.occs.length → K :=
  fun i => (a.occs.get i).snd

/-- The aggregate value of the token in the possible world `W` of its
group: the aggregate of the values of the kept occurrences, in order. -/
def valOn (a : AggValue T K) (W : Finset (Fin a.occs.length)) : T :=
  a.agg ((Having.seqOf a.occs W).map Prod.fst)

/-- The deterministic reading: the aggregate of the whole occurrence
sequence. -/
def collapse (a : AggValue T K) : T :=
  a.agg (a.occs.map Prod.fst)

/-! ### Merging the occurrences of equal value

A `DISTINCT` window aggregate reads one occurrence per class of equal
values in its frame, annotated by the `⊕` of the class's members. That
is a transformation of the occurrence payload, and it has to be decided
where the token is built: no reading of a token recovers it, the
deterministic reading having already collapsed the sequence.

The operator that would carry it is not here yet. Over the whole
relation the merged reading and `SeqAggFunc.distinct` agree
(`collapse_mergeByValue`), but *in a world* they need not: the merged
token orders the classes as the whole frame orders them – by each
class's last occurrence – while the distinct reading of a world dedups
that world's own sequence, and the two orders differ once a value's
last occurrence is absent from the world. They agree for a symmetric
aggregate, so a `DISTINCT` window is world-faithful exactly there, and
that is a condition the operator will have to carry. -/

/-- Merge the occurrences of equal value, summing their annotations and
keeping one occurrence per value. The convention is `List.dedup`'s: the
*last* occurrence of a value is the one kept, so that the values of the
merged list are the deduplicated values of the original
(`map_fst_mergeOccs`). -/
def mergeOccs [ValueType T] [Add K] : List (T × K) → List (T × K)
  | [] => []
  | (v, α) :: t =>
      if v ∈ t.map Prod.fst then
        (mergeOccs t).map (fun p => if p.1 = v then (p.1, α + p.2) else p)
      else (v, α) :: mergeOccs t

@[simp] theorem map_fst_mergeOccs [ValueType T] [Add K] :
    ∀ l : List (T × K), (mergeOccs l).map Prod.fst = (l.map Prod.fst).dedup
  | [] => rfl
  | (v, α) :: t => by
    rw [mergeOccs, List.map_cons, List.dedup_cons]
    by_cases h : v ∈ t.map Prod.fst
    · rw [ite_eq_left h, ite_eq_left h, List.map_map]
      rw [show (Prod.fst ∘ fun p : T × K => if p.1 = v then (p.1, α + p.2) else p)
          = Prod.fst from funext (fun p => by by_cases hp : p.1 = v <;> simp [hp])]
      exact map_fst_mergeOccs t
    · rw [ite_eq_right h, ite_eq_right h, List.map_cons]
      exact congrArg _ (map_fst_mergeOccs t)

@[simp] theorem map_fst_map_snd [Add K] {K' : Type} (h : K → K')
    (l : List (T × K)) :
    ((l.map (fun p => (p.1, h p.2))).map Prod.fst) = l.map Prod.fst := by
  rw [List.map_map]
  rfl

/-- **The merge commutes with a pushforward of the annotations**, the
classes being determined by the values and an additive map carrying the
sum of a class to the sum of its images. -/
theorem mergeOccs_map [ValueType T] [Add K] {K' : Type} [Add K'] (h : K → K')
    (hadd : ∀ x y : K, h (x + y) = h x + h y) :
    ∀ l : List (T × K),
      mergeOccs (l.map (fun p => (p.1, h p.2)))
        = (mergeOccs l).map (fun p => (p.1, h p.2))
  | [] => rfl
  | (v, α) :: t => by
    rw [List.map_cons, mergeOccs, mergeOccs, map_fst_map_snd]
    by_cases hv : v ∈ t.map Prod.fst
    · rw [ite_eq_left hv, ite_eq_left hv, mergeOccs_map h hadd t,
        List.map_map, List.map_map]
      refine congrArg (fun g => List.map g (mergeOccs t)) (funext fun p => ?_)
      by_cases hp : p.1 = v <;> simp [hp, hadd]
    · rw [ite_eq_right hv, ite_eq_right hv, List.map_cons,
        mergeOccs_map h hadd t]

/-- **A token read over its distinct values**: the same aggregate, with
the occurrences of equal value merged into one carrying the `⊕` of their
annotations. This is what a `DISTINCT` window aggregate reads – one
occurrence per class of the frame, annotated by the sum of its
members. -/
def mergeByValue [ValueType T] [Add K] (a : AggValue T K) : AggValue T K :=
  ⟨a.agg, mergeOccs a.occs, a.scalar⟩

@[simp] theorem scalar_mergeByValue [ValueType T] [Add K] (a : AggValue T K) :
    (mergeByValue a).scalar = a.scalar := rfl

/-- **The merged token reads the distinct values.** Its deterministic
reading is the aggregate over the deduplicated value sequence, which is
`SeqAggFunc.distinct` of the original – so a window that merges its
frame by value agrees, over plain relations, with the same window under
the distinct aggregate. -/
theorem collapse_mergeByValue [ValueType T] [Add K] (a : AggValue T K) :
    (mergeByValue a).collapse = a.agg.distinct (a.occs.map Prod.fst) := by
  rw [collapse, mergeByValue, map_fst_mergeOccs]
  rfl

/-- **A symmetric aggregate reads its token as a multiset**: two tokens
with the same aggregate and the same occurrences in a different order
collapse to the same value. This is what makes the order a group or a frame
is sequenced in immaterial, and `PICKFIRST` is where it is not. -/
theorem collapse_congr_of_symmetric {a b : AggValue T K}
    (hf : a.agg.Symmetric) (hagg : b.agg = a.agg)
    (hocc : a.occs.Perm b.occs) : a.collapse = b.collapse := by
  unfold collapse
  rw [hagg]
  exact hf (hocc.map Prod.fst)

/-- The world-faithful reading under a valuation `ν` of the annotations:
restrict to the occurrences whose annotation `ν` realizes, and aggregate
those in order. -/
def specialize (a : AggValue T K) (ν : K → Bool) : T :=
  a.agg ((a.occs.filter (fun o => ν o.snd)).map Prod.fst)

/-- Pushforward of `h : K → K'` through the annotations of a token; the
values are untouched. -/
def mapAnn (h : K → K') (a : AggValue T K) : AggValue T K' :=
  ⟨a.agg, a.occs.map (fun o => (o.fst, h o.snd)), a.scalar⟩

/-- **Predicate provenance of an atomic comparison against a token**: the
`⊕`-sum, over the non-empty possible worlds of the token's group, of the
world annotation times the characteristic value of the comparison between
the world's aggregate value and the regular value `c`. Non-empty worlds
only: the predicate provenance already enforces group existence, exactly
as in the fused semantics `Having.havingProv`. -/
def predProv [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (a : AggValue T K) (op : CompOp) (c : T) : K :=
  ∑ W ∈ Finset.univ.filter (fun W : Finset (Fin a.occs.length) => W.Nonempty),
    Having.worldAnn a.anns W * Having.chi op (a.valOn W) c

/-- **Predicate provenance in the scalar convention**: the same `⊕`-sum as
`predProv`, but over *all* worlds of the occurrence payload, the empty one
included, where the aggregate reads the empty sequence (`valOn_empty`).

The two conventions answer to two situations. Where a row exists only
because its group does – a `GROUP BY` key – the comparison is never read in
a world without occurrences, and `predProv` is the reading. Where the row
exists on its own and the aggregate may range over nothing – an aggregation
with no grouping, whose single row survives an empty input, or a frame that
may exclude the row it is computed for – the empty world is a world, and the
comparison must be given a value there. `predProvScalar` is that reading;
the two differ by exactly the empty world's term
(`predProvScalar_eq_predProv_add`). -/
def predProvScalar [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (a : AggValue T K) (op : CompOp) (c : T) : K :=
  ∑ W : Finset (Fin a.occs.length),
    Having.worldAnn a.anns W * Having.chi op (a.valOn W) c

/-- The token of a group, read in the scalar convention: the same payload,
with the empty world among its worlds. This is what an aggregation with no
grouping produces, and what a window frame that may exclude its current row
produces. -/
def ofScalarGroup [ValueType T] {c : ℕ} (f : SeqAggFunc T) (t : TermIn T c m)
    (U : List (AnnotatedTuple T K m))
    (γ : Fin c → T := fun _ => 0) : AggValue T K :=
  { ofGroup f t U γ with scalar := true }

/-- **Predicate provenance in the token's own convention.** A comparison
reads a token by the flag it carries, so that an operator settles the
convention once, where the token is built, and every comparison downstream
follows it. -/
def predProvOf [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (a : AggValue T K) (op : CompOp) (c : T) : K :=
  if a.scalar then a.predProvScalar op c else a.predProv op c

@[simp] theorem predProvOf_of_grouped [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] {a : AggValue T K} (h : a.scalar = false) (op : CompOp) (c : T) :
    a.predProvOf op c = a.predProv op c := by
  simp [predProvOf, h]

@[simp] theorem predProvOf_of_scalar [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] {a : AggValue T K} (h : a.scalar = true) (op : CompOp) (c : T) :
    a.predProvOf op c = a.predProvScalar op c := by
  simp [predProvOf, h]

/-! ### Two atoms on one token

A selection whose predicate conjoins two comparisons of the same token –
a truncation's `m < #(k+1) ≤ m+c`, a `HAVING` such as `count(*) > 2 AND
count(*) < 5` – multiplies the two atoms' provenances, each summed over
the worlds of the token separately. That is not in general the sum over
the worlds where both comparisons hold, and the definitions below name
the joint reading so that the difference can be stated. -/

/-- The predicate provenance of two aggregate atoms on one token, read
*jointly*: the `⊕`-sum over the worlds in which both comparisons hold. -/
def predProvAnd [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (a : AggValue T K) (op₁ : CompOp) (c₁ : T)
    (op₂ : CompOp) (c₂ : T) : K :=
  ∑ W ∈ Finset.univ.filter (fun W : Finset (Fin a.occs.length) => W.Nonempty),
    Having.worldAnn a.anns W
      * (Having.chi op₁ (a.valOn W) c₁ * Having.chi op₂ (a.valOn W) c₂)

/-- **When the conjunction of two atoms on one token reads jointly.** The
algebra's conjunction multiplies the two atoms' provenances, each summed
over the worlds of the token separately. Exclusivity kills the terms
where the two sums pick different worlds, and multiplicative idempotence
collapses the diagonal, leaving the joint sum. Neither holds of every
m-semiring: `𝔹[X]` has both, `ℕ` is exclusive and not idempotent, and an
absorptive domain such as Viterbi is not exclusive. -/
theorem predProv_mul_predProv [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (hexcl : exclusive K) (hidem : mulIdempotent K)
    (a : AggValue T K) (op₁ : CompOp) (c₁ : T) (op₂ : CompOp) (c₂ : T) :
    a.predProv op₁ c₁ * a.predProv op₂ c₂ = a.predProvAnd op₁ c₁ op₂ c₂ := by
  unfold predProv predProvAnd
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun W hW => ?_)
  rw [Finset.sum_eq_single W]
  · rw [mul_mul_mul_comm, hidem]
  · intro W' _ hne
    rw [mul_mul_mul_comm,
      Having.worldAnn_mul_eq_zero_of_ne hexcl _ (Ne.symm hne), zero_mul]
  · intro h
    exact absurd hW h

/-- The scalar-convention counterpart of `predProvAnd`: the same joint
sum, over all worlds of the token, the empty one included. This is the
reading a window's token needs, its frame being allowed to exclude the
row it is computed for. -/
def predProvScalarAnd [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (a : AggValue T K) (op₁ : CompOp) (c₁ : T)
    (op₂ : CompOp) (c₂ : T) : K :=
  ∑ W : Finset (Fin a.occs.length),
    Having.worldAnn a.anns W
      * (Having.chi op₁ (a.valOn W) c₁ * Having.chi op₂ (a.valOn W) c₂)

/-- The scalar-convention counterpart of `predProv_mul_predProv`. -/
theorem predProvScalar_mul_predProvScalar [ValueType T]
    [CommSemiringWithMonus K] [DecidableEq K] (hexcl : exclusive K)
    (hidem : mulIdempotent K) (a : AggValue T K)
    (op₁ : CompOp) (c₁ : T) (op₂ : CompOp) (c₂ : T) :
    a.predProvScalar op₁ c₁ * a.predProvScalar op₂ c₂
      = a.predProvScalarAnd op₁ c₁ op₂ c₂ := by
  unfold predProvScalar predProvScalarAnd
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun W _ => ?_)
  rw [Finset.sum_eq_single W]
  · rw [mul_mul_mul_comm, hidem]
  · intro W' _ hne
    rw [mul_mul_mul_comm,
      Having.worldAnn_mul_eq_zero_of_ne hexcl _ (Ne.symm hne), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ W) h

/-- The joint reading in the token's own convention. -/
def predProvOfAnd [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (a : AggValue T K) (op₁ : CompOp) (c₁ : T)
    (op₂ : CompOp) (c₂ : T) : K :=
  if a.scalar then a.predProvScalarAnd op₁ c₁ op₂ c₂
  else a.predProvAnd op₁ c₁ op₂ c₂

/-- **A range test on one token reads jointly exactly under these two
properties.** A selection whose predicate conjoins two comparisons of the
same token – a truncation's `m < #(k+1) ≤ m+c`, a `HAVING` such as
`count(*) > 2 AND count(*) < 5` – multiplies the two provenances, each
summed over the worlds separately. That is the joint sum over the worlds
where both hold when the m-semiring is exclusive and its multiplication
is idempotent, and not otherwise. -/
theorem predProvOf_mul_predProvOf [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (hexcl : exclusive K)
    (hidem : mulIdempotent K) (a : AggValue T K)
    (op₁ : CompOp) (c₁ : T) (op₂ : CompOp) (c₂ : T) :
    a.predProvOf op₁ c₁ * a.predProvOf op₂ c₂
      = a.predProvOfAnd op₁ c₁ op₂ c₂ := by
  unfold predProvOf predProvOfAnd
  cases a.scalar
  · exact predProv_mul_predProv hexcl hidem a op₁ c₁ op₂ c₂
  · exact predProvScalar_mul_predProvScalar hexcl hidem a op₁ c₁ op₂ c₂

/-! ### A test in place of a comparison

An atom that carries a three-valued *test* on the token's value rather
than a comparison against a term reads the same way – one sum over the
worlds, weighted by whether the test holds there – and a range is then
one atom. The `∧` rule becomes a decomposition of that sum, which is
what the hypotheses above are for. -/

/-- The predicate provenance of an arbitrary three-valued test on the
token's value: the `⊕`-sum, over the worlds of the group, of the world's
annotation weighted by whether the test holds there. `predProv` is the
case of a comparison against a term, and a range is the case of the
conjunction of two – one atom, and not a product of two. -/
def predProvWith [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (a : AggValue T K) (P : T → Kleene) : K :=
  ∑ W ∈ Finset.univ.filter (fun W : Finset (Fin a.occs.length) => W.Nonempty),
    Having.worldAnn a.anns W * Having.chiOf P (a.valOn W)

/-- The scalar-convention counterpart: the same sum over all worlds, the
empty one included. -/
def predProvScalarWith [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (a : AggValue T K) (P : T → Kleene) : K :=
  ∑ W : Finset (Fin a.occs.length),
    Having.worldAnn a.anns W * Having.chiOf P (a.valOn W)

/-- The test read in the token's own convention. -/
def predProvOfWith [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (a : AggValue T K) (P : T → Kleene) : K :=
  if a.scalar then a.predProvScalarWith P else a.predProvWith P

theorem predProv_eq_predProvWith [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (a : AggValue T K) (op : CompOp) (c : T) :
    a.predProv op c = a.predProvWith (fun v => op.eval3 v c) := rfl

theorem predProvScalar_eq_predProvScalarWith [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (a : AggValue T K)
    (op : CompOp) (c : T) :
    a.predProvScalar op c = a.predProvScalarWith (fun v => op.eval3 v c) := rfl

theorem predProvOf_eq_predProvOfWith [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (a : AggValue T K) (op : CompOp)
    (c : T) : a.predProvOf op c = a.predProvOfWith (fun v => op.eval3 v c) := by
  unfold predProvOf predProvOfWith
  cases a.scalar <;> rfl

/-- **A range is one atom, not a product of two.** The joint reading of
two tests is the reading of their conjunction. -/
theorem predProvAnd_eq_predProvWith [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (a : AggValue T K) (op₁ : CompOp) (c₁ : T)
    (op₂ : CompOp) (c₂ : T) :
    a.predProvAnd op₁ c₁ op₂ c₂
      = a.predProvWith (fun v => (op₁.eval3 v c₁).and (op₂.eval3 v c₂)) := by
  refine Finset.sum_congr rfl (fun W _ => ?_)
  rw [← Having.chiOf_mul_chiOf]
  rfl

theorem predProvScalarAnd_eq_predProvScalarWith [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (a : AggValue T K)
    (op₁ : CompOp) (c₁ : T) (op₂ : CompOp) (c₂ : T) :
    a.predProvScalarAnd op₁ c₁ op₂ c₂
      = a.predProvScalarWith (fun v => (op₁.eval3 v c₁).and (op₂.eval3 v c₂)) := by
  refine Finset.sum_congr rfl (fun W _ => ?_)
  rw [← Having.chiOf_mul_chiOf]
  rfl

theorem predProvOfAnd_eq_predProvOfWith [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (a : AggValue T K)
    (op₁ : CompOp) (c₁ : T) (op₂ : CompOp) (c₂ : T) :
    a.predProvOfAnd op₁ c₁ op₂ c₂
      = a.predProvOfWith (fun v => (op₁.eval3 v c₁).and (op₂.eval3 v c₂)) := by
  unfold predProvOfAnd predProvOfWith
  cases a.scalar
  · exact predProvAnd_eq_predProvWith a op₁ c₁ op₂ c₂
  · exact predProvScalarAnd_eq_predProvScalarWith a op₁ c₁ op₂ c₂

/-- **The product of two atoms on one token is the single atom that
conjoins their tests**, when the m-semiring is exclusive and its
multiplication is idempotent. This is the form the `∧` rule takes once
an atom may carry a test rather than a comparison: not a rule of the
semantics but a decomposition of one sum into two, valid there and not
in general. -/
theorem predProvOf_mul_predProvOf_with [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (hexcl : exclusive K)
    (hidem : mulIdempotent K) (a : AggValue T K)
    (op₁ : CompOp) (c₁ : T) (op₂ : CompOp) (c₂ : T) :
    a.predProvOf op₁ c₁ * a.predProvOf op₂ c₂
      = a.predProvOfWith (fun v => (op₁.eval3 v c₁).and (op₂.eval3 v c₂)) := by
  rw [predProvOf_mul_predProvOf hexcl hidem, predProvOfAnd_eq_predProvOfWith]


/-- A token built from a group is grouped. -/
@[simp] theorem scalar_ofGroup [ValueType T] {c : ℕ} (f : SeqAggFunc T)
    (t : TermIn T c m) (U : List (AnnotatedTuple T K m)) {γ : Fin c → T} :
    (ofGroup f t U γ).scalar = false := rfl

/-- A token built from a group in the scalar convention is scalar. -/
@[simp] theorem scalar_ofScalarGroup [ValueType T] {c : ℕ} (f : SeqAggFunc T)
    (t : TermIn T c m) (U : List (AnnotatedTuple T K m)) {γ : Fin c → T} :
    (ofScalarGroup f t U γ).scalar = true := rfl

/-! ## Reindexing bridges

The occurrence payload of `ofGroup` is a `List.map` image of the group
sequence, so worlds over the token and worlds over the group live over
propositionally – not definitionally – equal position types. The bridges
below transport `seqOf`, `worldAnn` and the two readings along the
length-preserving equivalence `finCongr`. -/

section Reindex

variable {β γ : Type}

/-- `seqOf` commutes with mapping the underlying list, up to reindexing
the world along the length equality. -/
theorem seqOf_map (g : β → γ) :
    ∀ (U : List β) (h : U.length = (U.map g).length)
      (W : Finset (Fin U.length)),
      Having.seqOf (U.map g) (W.map (finCongr h).toEmbedding)
        = (Having.seqOf U W).map g
  | [], _, _ => rfl
  | b :: U, h, W => by
    have h' : U.length = (U.map g).length := by simp
    show (if (0 : Fin ((U.map g).length + 1)) ∈ W.map (finCongr h).toEmbedding
            then [g b] else [])
          ++ Having.seqOf (U.map g) (Finset.univ.filter
              (fun i => i.succ ∈ W.map (finCongr h).toEmbedding))
        = ((if (0 : Fin (U.length + 1)) ∈ W then [b] else [])
            ++ Having.seqOf U
              (Finset.univ.filter (fun i => i.succ ∈ W))).map g
    have hzero : ((0 : Fin ((U.map g).length + 1))
        ∈ W.map (finCongr h).toEmbedding)
        ↔ (0 : Fin (U.length + 1)) ∈ W := by
      rw [Finset.mem_map_equiv]
      exact Iff.of_eq (congrArg (· ∈ W) (Fin.ext rfl))
    have hfilter : (Finset.univ.filter
          (fun i : Fin (U.map g).length =>
            i.succ ∈ W.map (finCongr h).toEmbedding))
        = (Finset.univ.filter (fun i : Fin U.length => i.succ ∈ W)).map
            (finCongr h').toEmbedding := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_map_equiv, Finset.mem_univ,
        true_and]
      exact Iff.of_eq (congrArg (· ∈ W) (Fin.ext rfl))
    rw [List.map_append, hfilter, seqOf_map g U h']
    congr 1
    by_cases h0 : (0 : Fin (U.length + 1)) ∈ W
    · rw [ite_eq_left h0, ite_eq_left (hzero.mpr h0)]; rfl
    · rw [ite_eq_right h0, ite_eq_right (fun hc => h0 (hzero.mp hc))]; rfl

/-- The whole-sequence world: `seqOf` over `univ` is the identity. -/
theorem seqOf_univ : ∀ (U : List β), Having.seqOf U Finset.univ = U
  | [] => rfl
  | b :: U => by
    rw [Having.seqOf]
    have : (Finset.univ.filter
        (fun i : Fin U.length => i.succ ∈ (Finset.univ : Finset (Fin (U.length + 1)))))
        = Finset.univ := by
      ext i; simp
    rw [this, seqOf_univ U]
    simp

/-- The empty world selects nothing. -/
theorem seqOf_empty : ∀ (U : List β), Having.seqOf U (∅ : Finset (Fin U.length)) = []
  | [] => rfl
  | b :: U => by
    rw [Having.seqOf]
    have hf : (Finset.univ.filter
        (fun i : Fin U.length => i.succ ∈ (∅ : Finset (Fin (U.length + 1)))))
        = (∅ : Finset (Fin U.length)) := by
      ext i; simp
    rw [hf, seqOf_empty U]
    simp

/-- Filtering a list is taking the subsequence of the positions whose
element satisfies the predicate. -/
theorem filter_eq_seqOf (p : β → Bool) :
    ∀ (U : List β),
      U.filter p = Having.seqOf U (Finset.univ.filter (fun i => p (U.get i)))
  | [] => rfl
  | b :: U => by
    rw [List.filter_cons, Having.seqOf]
    have hzero : ((0 : Fin (U.length + 1))
        ∈ Finset.univ.filter (fun i => p ((b :: U).get i))) ↔ p b := by
      simp
    have hfilter : (Finset.univ.filter
          (fun i : Fin U.length =>
            i.succ ∈ Finset.univ.filter (fun j => p ((b :: U).get j))))
        = Finset.univ.filter (fun i => p (U.get i)) := by
      ext i; simp
    rw [hfilter, ← filter_eq_seqOf p U]
    by_cases hp : p b
    · rw [ite_eq_left hp, ite_eq_left (hzero.mpr hp)]; rfl
    · rw [ite_eq_right (by simpa using hp), ite_eq_right (fun hc => hp (hzero.mp hc))]
      rfl

end Reindex

/-! ## The readings, related -/

/-- `collapse` is the aggregate value of the whole-group world. -/
theorem collapse_eq_valOn_univ (a : AggValue T K) :
    a.collapse = a.valOn Finset.univ := by
  unfold collapse valOn
  rw [seqOf_univ]

/-- The deterministic reading is the world-faithful one under the valuation
that realizes every occurrence. So `specialize` is the general form of the
*displayed* value of an aggregate – its value in the family of occurrences a
given valuation realizes – and `collapse` is the case where every occurrence
is realized. The two part company as soon as a token carries occurrences that
hold in no world: those a difference or a rejected comparison leaves behind. -/
theorem collapse_eq_specialize_true (a : AggValue T K) :
    a.collapse = a.specialize (fun _ => true) := by
  unfold collapse specialize
  simp

/-- `specialize` is the aggregate value of the world of realized
occurrences. -/
theorem specialize_eq_valOn (a : AggValue T K) (ν : K → Bool) :
    a.specialize ν = a.valOn (Finset.univ.filter (fun i => ν (a.anns i))) := by
  unfold specialize valOn
  rw [filter_eq_seqOf (fun o => ν o.snd) a.occs]
  rfl

/-- The empty world reads the aggregate over no occurrence: `f` of the empty
sequence. This is the value a comparison sees where the group exists in no
world. -/
theorem valOn_empty (a : AggValue T K) : a.valOn ∅ = a.agg [] := by
  unfold valOn
  rw [seqOf_empty]
  rfl

/-- The same splitting for an arbitrary test: the scalar reading is the
grouped one plus the empty world's term. -/
theorem predProvScalarWith_eq_predProvWith_add [ValueType T]
    [CommSemiringWithMonus K] [DecidableEq K] (a : AggValue T K)
    (P : T → Kleene) :
    a.predProvScalarWith P
      = a.predProvWith P
        + Having.worldAnn a.anns ∅ * Having.chiOf P (a.agg []) := by
  rw [predProvScalarWith, predProvWith]
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin a.occs.length)))
    (fun W => W.Nonempty)]
  congr 1
  have hempty : (Finset.univ.filter
      (fun W : Finset (Fin a.occs.length) => ¬ W.Nonempty)) = {∅} := by
    ext W
    simp [Finset.not_nonempty_iff_eq_empty]
  rw [hempty, Finset.sum_singleton, valOn_empty]

/-- The scalar convention adds exactly one term to the grouped one: the
empty world, annotated `𝟙 ⊖ ⊕ᵢ αᵢ` and reading `f` of the empty sequence. In
particular the two agree whenever that term vanishes – when the comparison
fails on `f []`, and in any semiring where no world is empty of annotation. -/
theorem predProvScalar_eq_predProv_add [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (a : AggValue T K) (op : CompOp) (c : T) :
    a.predProvScalar op c
      = a.predProv op c + Having.worldAnn a.anns ∅ * Having.chi op (a.agg []) c := by
  rw [predProvScalar, predProv]
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin a.occs.length)))
    (fun W => W.Nonempty)]
  congr 1
  have hempty : (Finset.univ.filter
      (fun W : Finset (Fin a.occs.length) => ¬ W.Nonempty)) = {∅} := by
    ext W
    simp [Finset.not_nonempty_iff_eq_empty]
  rw [hempty, Finset.sum_singleton, valOn_empty]

/-- **A comparison that holds in the empty world and in no other has a
single-term predicate provenance**: the empty world's annotation
`𝟙 ⊖ ⊕ᵢ αᵢ`.

No absorptivity and no distributivity of `⊗` over `⊖` are used, and none
could be: there is no family of worlds to collapse, only one term. This is
what makes `COUNT(κ) = 0` cheap in the scalar convention, where the empty
world is a world – `COUNT` of nothing is `0`, and a non-empty world of
occurrences whose `κ` is never null counts at least one. -/
theorem predProvScalar_of_only_empty [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (a : AggValue T K) (op : CompOp) (c : T)
    (hempty : Having.chi (K := K) op (a.agg []) c = 1)
    (hne : ∀ W : Finset (Fin a.occs.length), W.Nonempty →
      Having.chi (K := K) op (a.valOn W) c = 0) :
    a.predProvScalar op c = 1 - ∑ i, a.anns i := by
  have hgrouped : a.predProv op c = 0 := by
    unfold predProv
    refine Finset.sum_eq_zero (fun W hW => ?_)
    rw [hne W (Finset.mem_filter.mp hW).2, mul_zero]
  rw [predProvScalar_eq_predProv_add, hgrouped, zero_add, hempty, mul_one,
    Having.worldAnn_empty]

/-- **`COUNT(κ) = 0` in the scalar convention is `𝟙 ⊖ ⊕ᵢ αᵢ`.** Where the
counted values are never null, a non-empty world counts at least one, so
the comparison holds in the empty world alone. This is an antijoin's
annotation, and no hypothesis on `K` enters it: not absorptivity, not
distributivity of `⊗` over `⊖`. -/
theorem predProvScalar_count_eq_zero [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (a : AggValue T K) (hc : SeqAggFunc.Counts a.agg)
    (hnn : ∀ o ∈ a.occs, ValueType.isNull o.fst = false) :
    a.predProvScalar CompOp.eq 0 = 1 - ∑ i, a.anns i := by
  have hnil : a.agg [] = 0 := (hc.eq_zero []).mpr (fun _ h => absurd h (by simp))
  refine predProvScalar_of_only_empty a CompOp.eq 0 ?_ (fun W hW => ?_)
  · show (if CompOp.eq.eval3 (a.agg []) 0 = Kleene.true then (1 : K) else 0) = 1
    refine ite_eq_left ?_
    rw [hnil, CompOp.eval3_eq_true_iff CompOp.eq ValueType.isNull_zero
      ValueType.isNull_zero]
    rfl
  · show (if CompOp.eq.eval3 (a.valOn W) 0 = Kleene.true then (1 : K) else 0) = 0
    refine ite_eq_right (fun hcon => ?_)
    rw [show a.valOn W = a.agg ((Having.seqOf a.occs W).map Prod.fst) from rfl,
      CompOp.eval3_eq_true_iff CompOp.eq (hc.not_null _)
        ValueType.isNull_zero] at hcon
    -- the world counts at least one occurrence, all of whose values are
    -- non-null, so its count is not zero
    have hmem : ∀ x ∈ (Having.seqOf a.occs W).map Prod.fst,
        ValueType.isNull x = false := by
      intro x hx
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
      exact hnn o ((Having.mem_seqOf a.occs W o).mp ho |>.elim
        (fun i hi => hi.2 ▸ List.get_mem _ _))
    obtain ⟨i, hi⟩ := hW
    have hne : ((Having.seqOf a.occs W).map Prod.fst) ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_map, Having.seqOf_length]
      exact Finset.card_pos.mpr ⟨i, hi⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    have := ((hc.eq_zero _).mp hcon) x hx
    rw [hmem x hx] at this
    exact Bool.noConfusion this

/-- **`COUNT(κ) ≥ 1` is the `⊕`-sum of the occurrence annotations.** Where
the counted values are never null, every non-empty world counts at least
one and the empty world counts none, so the comparison holds in exactly the
non-empty worlds – an upward-closed family, which `Having.sum_ann_meet`
collapses. Absorptivity is what that collapse needs; distributivity of `⊗`
over `⊖` is not used. -/
theorem predProvScalar_count_ne_zero [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (h_abs : absorptive K) (a : AggValue T K)
    (hc : SeqAggFunc.Counts a.agg)
    (hnn : ∀ o ∈ a.occs, ValueType.isNull o.fst = false) :
    a.predProvScalar CompOp.ne 0 = ∑ i, a.anns i := by
  have hnil : a.agg [] = 0 := (hc.eq_zero []).mpr (fun _ h => absurd h (by simp))
  -- every non-empty world has a non-null value to count
  have hpos : ∀ W : Finset (Fin a.occs.length), W.Nonempty → a.valOn W ≠ 0 := by
    intro W hW hcon
    have hmem : ∀ x ∈ (Having.seqOf a.occs W).map Prod.fst,
        ValueType.isNull x = false := by
      intro x hx
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
      exact hnn o ((Having.mem_seqOf a.occs W o).mp ho |>.elim
        (fun i hi => hi.2 ▸ List.get_mem _ _))
    obtain ⟨i, hi⟩ := hW
    have hne : ((Having.seqOf a.occs W).map Prod.fst) ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_map, Having.seqOf_length]
      exact Finset.card_pos.mpr ⟨i, hi⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    have := ((hc.eq_zero _).mp hcon) x hx
    rw [hmem x hx] at this
    exact Bool.noConfusion this
  -- the empty world contributes nothing, the others contribute their annotation
  have hempty : Having.chi (K := K) CompOp.ne (a.agg []) 0 = 0 := by
    show (if CompOp.ne.eval3 (a.agg []) 0 = Kleene.true then (1 : K) else 0) = 0
    refine ite_eq_right (fun hcon => ?_)
    rw [hnil, CompOp.eval3_eq_true_iff CompOp.ne ValueType.isNull_zero
      ValueType.isNull_zero] at hcon
    exact hcon rfl
  have hone : ∀ W : Finset (Fin a.occs.length), W.Nonempty →
      Having.chi (K := K) CompOp.ne (a.valOn W) 0 = 1 := by
    intro W hW
    show (if CompOp.ne.eval3 (a.valOn W) 0 = Kleene.true then (1 : K) else 0) = 1
    refine ite_eq_left ?_
    rw [show a.valOn W = a.agg ((Having.seqOf a.occs W).map Prod.fst) from rfl,
      CompOp.eval3_eq_true_iff CompOp.ne (hc.not_null _) ValueType.isNull_zero]
    exact hpos W hW
  rw [predProvScalar_eq_predProv_add, hempty, mul_zero, add_zero]
  unfold predProv
  rw [Finset.sum_congr rfl (fun W hW => by
    rw [hone W (Finset.mem_filter.mp hW).2, mul_one,
      Having.worldAnn_eq_ann])]
  refine Eq.trans ?_ (Having.sum_ann_meet h_abs a.anns
    (U := Finset.univ) (H := Finset.univ) (Finset.subset_univ _))
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext W
  simp [Finset.inter_univ]

/-! ## `ofGroup` bridges to the fused semantics -/

section OfGroup

variable [ValueType T]

/-- The occurrence payload of `ofGroup` has the length of the group
sequence. -/
theorem length_ofGroup_occs (f : SeqAggFunc T) (t : Term T m)
    (U : List (AnnotatedTuple T K m)) :
    U.length = (ofGroup f t U).occs.length := by
  simp [ofGroup]

/-- The world value of the token of a group is the aggregate value of the
fused semantics on that world. -/
theorem valOn_ofGroup (f : SeqAggFunc T) (t : Term T m)
    (U : List (AnnotatedTuple T K m)) (W : Finset (Fin U.length)) :
    (ofGroup f t U).valOn
        (W.map (finCongr (length_ofGroup_occs f t U)).toEmbedding)
      = Having.aggValOn U t f W := by
  show f ((Having.seqOf (U.map (fun p => (t.eval p.fst, p.snd)))
      (W.map (finCongr (length_ofGroup_occs f t U)).toEmbedding)).map Prod.fst)
    = Having.aggValOn U t f W
  rw [seqOf_map (fun p => (t.eval p.fst, p.snd)) U _ W, List.map_map]
  rfl

/-- The annotations of the token of a group are the occurrence
annotations. -/
theorem anns_ofGroup (f : SeqAggFunc T) (t : Term T m)
    (U : List (AnnotatedTuple T K m)) (i : Fin U.length) :
    (ofGroup f t U).anns (finCongr (length_ofGroup_occs f t U) i)
      = (U.get i).snd := by
  unfold anns ofGroup
  simp

variable [CommSemiringWithMonus K] [DecidableEq K]

omit [ValueType T] [DecidableEq K] in
/-- The world annotation transports along the reindexing. -/
theorem worldAnn_map_finCongr {N M : ℕ} (h : N = M) (α : Fin M → K)
    (W : Finset (Fin N)) :
    Having.worldAnn α (W.map (finCongr h).toEmbedding)
      = Having.worldAnn (fun i => α (finCongr h i)) W := by
  unfold Having.worldAnn
  have hcompl : (W.map (finCongr h).toEmbedding)ᶜ
      = Wᶜ.map (finCongr h).toEmbedding := by
    ext j
    rw [Finset.mem_compl, Finset.mem_map_equiv, Finset.mem_map_equiv,
      Finset.mem_compl]
  rw [Finset.prod_map, hcompl, Finset.sum_map]
  rfl

/-- **Regression bridge, token side.** The predicate provenance of a
comparison against the token of a group is the fused semantics' predicate
provenance of the same comparison on that group. -/
theorem predProv_ofGroup (f : SeqAggFunc T) (t : Term T m)
    (U : List (AnnotatedTuple T K m)) (op : CompOp) (c : T) :
    (ofGroup f t U).predProv op c = Having.havingProv U t f op c := by
  unfold predProv Having.havingProv
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv
    (finCongr (length_ofGroup_occs f t U)).finsetCongr
    (fun W => if W.Nonempty
      then Having.worldAnn (fun i => (U.get i).snd) W
        * Having.chi op (Having.aggValOn U t f W) c else 0)
    _ (fun W => ?_)).symm
  rw [Equiv.finsetCongr_apply]
  by_cases hne : W.Nonempty
  · rw [ite_eq_left hne, ite_eq_left (by rwa [Finset.map_nonempty]),
      valOn_ofGroup, worldAnn_map_finCongr,
      show (fun i => (ofGroup f t U).anns
          (finCongr (length_ofGroup_occs f t U) i))
        = fun i => (U.get i).snd from funext (anns_ofGroup f t U)]
  · rw [ite_eq_right hne, ite_eq_right (by rwa [Finset.map_nonempty])]

end OfGroup

/-! ## Pushforward lemmas -/

section MapAnn

/-- The deterministic reading is unchanged by the pushforward. -/
@[simp] theorem collapse_mapAnn (h : K → K') (a : AggValue T K) :
    (a.mapAnn h).collapse = a.collapse := by
  unfold collapse mapAnn
  rw [List.map_map]
  rfl

/-- The world-faithful reading composes with the pushforward. -/
@[simp] theorem specialize_mapAnn (h : K → K') (a : AggValue T K)
    (ν : K' → Bool) :
    (a.mapAnn h).specialize ν = a.specialize (fun k => ν (h k)) := by
  unfold specialize mapAnn
  rw [List.filter_map, List.map_map]
  rfl

end MapAnn

/-! ## Lifted column values -/

/-- Pushforward of `h : K → K'` on a lifted column value: data is
untouched, a token maps its annotations. -/
def mapAnnSum (h : K → K') : T ⊕ AggValue T K → T ⊕ AggValue T K' :=
  Sum.map id (mapAnn h)

/-- Deterministic reading of a lifted column value: data is itself, a
token collapses. -/
def collapseSum : T ⊕ AggValue T K → T :=
  Sum.elim id collapse

/-- The deterministic reading of a lifted value is unchanged by the
pushforward. -/
@[simp] theorem collapseSum_mapAnnSum (h : K → K') (x : T ⊕ AggValue T K) :
    collapseSum (mapAnnSum h x) = collapseSum x := by
  cases x <;> simp [collapseSum, mapAnnSum]

end AggValue
