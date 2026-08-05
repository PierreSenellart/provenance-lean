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

namespace AggValue

variable {T K K' : Type} {m : ℕ}

/-- The token of a group with occurrence sequence `U`, aggregating the
term `t` with `f`: the projection of the group payload. -/
def ofGroup [ValueType T] (f : SeqAggFunc T) (t : Term T m)
    (U : List (AnnotatedTuple T K m)) : AggValue T K :=
  ⟨f, U.map (fun p => (t.eval p.fst, p.snd))⟩

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

/-- The world-faithful reading under a valuation `ν` of the annotations:
restrict to the occurrences whose annotation `ν` realizes, and aggregate
those in order. -/
def specialize (a : AggValue T K) (ν : K → Bool) : T :=
  a.agg ((a.occs.filter (fun o => ν o.snd)).map Prod.fst)

/-- Pushforward of `h : K → K'` through the annotations of a token; the
values are untouched. -/
def mapAnn (h : K → K') (a : AggValue T K) : AggValue T K' :=
  ⟨a.agg, a.occs.map (fun o => (o.fst, h o.snd))⟩

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
    · rw [if_pos h0, if_pos (hzero.mpr h0)]; rfl
    · rw [if_neg h0, if_neg (fun hc => h0 (hzero.mp hc))]; rfl

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
    · rw [if_pos hp, if_pos (hzero.mpr hp)]; rfl
    · rw [if_neg (by simpa using hp), if_neg (fun hc => hp (hzero.mp hc))]
      rfl

end Reindex

/-! ## The readings, related -/

/-- `collapse` is the aggregate value of the whole-group world. -/
theorem collapse_eq_valOn_univ (a : AggValue T K) :
    a.collapse = a.valOn Finset.univ := by
  unfold collapse valOn
  rw [seqOf_univ]

/-- `specialize` is the aggregate value of the world of realized
occurrences. -/
theorem specialize_eq_valOn (a : AggValue T K) (ν : K → Bool) :
    a.specialize ν = a.valOn (Finset.univ.filter (fun i => ν (a.anns i))) := by
  unfold specialize valOn
  rw [filter_eq_seqOf (fun o => ν o.snd) a.occs]
  rfl

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
  · rw [if_pos hne, if_pos (by rwa [Finset.map_nonempty]),
      valOn_ofGroup, worldAnn_map_finCongr,
      show (fun i => (ofGroup f t U).anns
          (finCongr (length_ofGroup_occs f t U) i))
        = fun i => (U.get i).snd from funext (anns_ofGroup f t U)]
  · rw [if_neg hne, if_neg (by rwa [Finset.map_nonempty])]

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
