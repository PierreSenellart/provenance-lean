/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Tactic.Ring
import Provenance.AggQuery
import Provenance.AggValueCongr
import Provenance.QueryAnnotatedDatabaseHom
import Provenance.AggQueryBridges
import Provenance.JointHom
import Provenance.Coherence

/-!
# Hom commutation, token and annotation layer

The value-level content of “compile once, evaluate many” for the general
evaluator: every ingredient of a row's annotation is an
`⊕`/`⊗`/`⊖`/`δ`-polynomial in the occurrence annotations, so it commutes
with every `SemiringWithMonusHom`:

* `GenAnn.finalize_mapHom` – the finalized factored annotation commutes
  (this is where `map_delta` enters, for the pending group factors);
* `AggValue.predProv_mapAnn` – the predicate provenance of a comparison
  against a token commutes: the world annotations are `⊗`/`⊖`-polynomials
  and the characteristic values `χ` are `{𝟘,𝟙}`-valued, with the
  aggregate values themselves untouched by the pushforward;
* `NestedValue.predProvWith_mapAnn` – the same for a nested column: its
  occurrences are a bag and its worlds are read off that bag, so the
  worlds of the pushforward *are* the pushforwards of the worlds
  (`worlds_mapAnn`), each carrying the pushed annotation
  (`World.ann_mapAnn`) and reading the same value;
* `GenPredIn.predsem_mapAnn` – the predicate provenance of a whole
  generalized predicate commutes (`∧ ↦ ⊗`, `∨ ↦ ⊕` through `map_mul`
  and `map_add`, `¬` by polarity), whichever kind of token its aggregate
  atoms read.

These are unconditional, but they do not by themselves give the
*evaluator-level* commutation `AggQueryIn.evaluateAnnotated_hom` at the
bottom of this file: the evaluator's supersede and cashing decisions
compare annotation lists for equality, which a non-injective hom can
conflate (licensing supersedes on the target side that the source side
does not take), and the `≼`-order's annotation tie-break in
`havingGroup` need not be preserved. Both divergences are
value-neutral, so the theorem holds with no hypothesis on the hom, the
query or the m-semiring:

* an extra supersede only drops a group guard standing next to an
  annotation that already contains an occurrence of that group, which
  `delta_absorb` makes redundant;
* a changed tie-break only permutes occurrences carrying the same tuple
  part, hence the same aggregated-term value, and the tie-block
  congruence of `Provenance.AggValueCongr` shows such a permutation
  leaves the predicate provenance alone. `GenRow.Sim` below carries that
  slack row by row through the evaluator, and
  `GenRow.Sim.toAnnotated_eq` cashes it into an equality of finalized
  annotated tuples.
-/

variable {T : Type} [ValueType T]
variable {K K' : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [CommSemiringWithMonus K'] [DecidableEq K']
variable {m : ℕ}

/-! ## The annotation pushforward -/

/-- Pushforward of a factored annotation along `h`. -/
def GenAnn.mapHom (h : SemiringWithMonusHom K K') (a : GenAnn K) :
    GenAnn K' :=
  ⟨h.toRingHom a.base, a.pending.map (List.map ⇑h.toRingHom)⟩

omit [DecidableEq K] [DecidableEq K'] in
/-- The characteristic value of a comparison commutes with any hom
(`χ` is `{𝟘,𝟙}`-valued). -/
theorem chi_hom (h : SemiringWithMonusHom K K') (op : CompOp)
    (a b : T) :
    h.toRingHom (Having.chi op a b : K) = (Having.chi op a b : K') := by
  unfold Having.chi
  by_cases hab : op.eval3 a b = Kleene.true
  · rw [ite_eq_left hab, ite_eq_left hab, map_one]
  · rw [ite_eq_right hab, ite_eq_right hab, map_zero]

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- The factored world annotation commutes with any hom: it is an
`⊗`/`⊖`-polynomial in the occurrence annotations. -/
theorem worldAnn_hom (h : SemiringWithMonusHom K K') {N : ℕ}
    (α : Fin N → K) (W : Finset (Fin N)) :
    h.toRingHom (Having.worldAnn α W)
      = Having.worldAnn (fun i => h.toRingHom (α i)) W := by
  unfold Having.worldAnn
  rw [map_mul, map_prod, SemiringWithMonusHom.map_sub, map_one, map_sum]

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- The finalized factored annotation commutes with any hom (the pending
group factors through `map_delta`). -/
theorem GenAnn.finalize_mapHom (h : SemiringWithMonusHom K K')
    (a : GenAnn K) :
    (a.mapHom h).finalize = h.toRingHom a.finalize := by
  show h.toRingHom a.base
      * ((a.pending.map (List.map ⇑h.toRingHom)).map
          (fun l => SemiringWithMonus.delta l.sum)).prod
    = h.toRingHom (a.base
      * (a.pending.map (fun l => SemiringWithMonus.delta l.sum)).prod)
  rw [map_mul, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun l _ => ?_)
  show SemiringWithMonus.delta (l.map ⇑h.toRingHom).sum
    = h.toRingHom (SemiringWithMonus.delta l.sum)
  rw [SemiringWithMonusHom.map_delta, map_list_sum]

/-! ## The token pushforward -/

namespace AggValue

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- The occurrence payload keeps its length under the pushforward. -/
theorem length_mapAnn_occs (h : SemiringWithMonusHom K K')
    (a : AggValue T K) :
    a.occs.length = (a.mapAnn ⇑h.toRingHom).occs.length := by
  simp [AggValue.mapAnn]

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- The pushed-forward annotations, along the reindexing. -/
theorem anns_mapAnn (h : SemiringWithMonusHom K K')
    (a : AggValue T K) (i : Fin a.occs.length) :
    (a.mapAnn ⇑h.toRingHom).anns (finCongr (length_mapAnn_occs h a) i)
      = h.toRingHom (a.anns i) := by
  unfold anns mapAnn
  simp

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- The per-world aggregate value is untouched by the pushforward. -/
theorem valOn_mapAnn (h : SemiringWithMonusHom K K')
    (a : AggValue T K) (W : Finset (Fin a.occs.length)) :
    (a.mapAnn ⇑h.toRingHom).valOn
        (W.map (finCongr (length_mapAnn_occs h a)).toEmbedding)
      = a.valOn W := by
  show (a.mapAnn ⇑h.toRingHom).agg ((Having.seqOf
      (a.occs.map (fun o => (o.fst, h.toRingHom o.snd)))
      (W.map (finCongr (length_mapAnn_occs h a)).toEmbedding)).map Prod.fst)
    = a.valOn W
  rw [seqOf_map (fun o => (o.fst, h.toRingHom o.snd)) a.occs _ W,
    List.map_map]
  rfl

/-- **Token-level hom commutation.** The predicate provenance of a
comparison against a token commutes with every `SemiringWithMonusHom`:
it is an `⊕`/`⊗`/`⊖`-polynomial in the occurrence annotations, and the
aggregate values compared are untouched by the pushforward. -/
theorem predProv_mapAnn (h : SemiringWithMonusHom K K')
    (a : AggValue T K) (op : CompOp) (c : T) :
    (a.mapAnn ⇑h.toRingHom).predProv op c
      = h.toRingHom (a.predProv op c) := by
  unfold predProv
  rw [map_sum, Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv (finCongr (length_mapAnn_occs h a)).finsetCongr
    (fun W => if W.Nonempty
      then h.toRingHom (Having.worldAnn a.anns W
        * Having.chi op (a.valOn W) c) else 0)
    _ (fun W => ?_)).symm
  rw [Equiv.finsetCongr_apply]
  by_cases hne : W.Nonempty
  · rw [ite_eq_left hne, ite_eq_left (by rwa [Finset.map_nonempty]),
      valOn_mapAnn h a W, worldAnn_map_finCongr, map_mul, worldAnn_hom,
      chi_hom,
      show (fun i => (a.mapAnn ⇑h.toRingHom).anns
          (finCongr (length_mapAnn_occs h a) i))
        = fun i => h.toRingHom (a.anns i) from funext (anns_mapAnn h a)]
  · rw [ite_eq_right hne, ite_eq_right (by rwa [Finset.map_nonempty])]

/-- **Token-level hom commutation, scalar convention.** As
`predProv_mapAnn`, for the reading in which the empty world is a world: the
sum ranges over every world instead of the non-empty ones, and the argument
loses its case split. -/
theorem predProvScalar_mapAnn (h : SemiringWithMonusHom K K')
    (a : AggValue T K) (op : CompOp) (c : T) :
    (a.mapAnn ⇑h.toRingHom).predProvScalar op c
      = h.toRingHom (a.predProvScalar op c) := by
  unfold predProvScalar
  rw [map_sum]
  refine (Fintype.sum_equiv (finCongr (length_mapAnn_occs h a)).finsetCongr
    (fun W => h.toRingHom (Having.worldAnn a.anns W
      * Having.chi op (a.valOn W) c))
    _ (fun W => ?_)).symm
  rw [Equiv.finsetCongr_apply, valOn_mapAnn h a W, worldAnn_map_finCongr,
    map_mul, worldAnn_hom, chi_hom,
    show (fun i => (a.mapAnn ⇑h.toRingHom).anns
        (finCongr (length_mapAnn_occs h a) i))
      = fun i => h.toRingHom (a.anns i) from funext (anns_mapAnn h a)]

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
theorem chiOf_hom (h : SemiringWithMonusHom K K') (P : T → Kleene) (v : T) :
    h.toRingHom (Having.chiOf P v : K) = (Having.chiOf P v : K') := by
  unfold Having.chiOf
  split <;> simp

/-- **Token-level hom commutation for a test.** As `predProv_mapAnn`,
with an arbitrary three-valued test in place of the comparison: the test
reads the aggregate values, which the pushforward leaves alone. -/
theorem predProvWith_mapAnn (h : SemiringWithMonusHom K K')
    (a : AggValue T K) (P : T → Kleene) :
    (a.mapAnn ⇑h.toRingHom).predProvWith P
      = h.toRingHom (a.predProvWith P) := by
  unfold predProvWith
  rw [map_sum, Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv (finCongr (length_mapAnn_occs h a)).finsetCongr
    (fun W => if W.Nonempty
      then h.toRingHom (Having.worldAnn a.anns W
        * Having.chiOf P (a.valOn W)) else 0)
    _ (fun W => ?_)).symm
  rw [Equiv.finsetCongr_apply]
  by_cases hne : W.Nonempty
  · rw [ite_eq_left hne, ite_eq_left (by rwa [Finset.map_nonempty]),
      valOn_mapAnn h a W, worldAnn_map_finCongr, map_mul, worldAnn_hom,
      chiOf_hom,
      show (fun i => (a.mapAnn ⇑h.toRingHom).anns
          (finCongr (length_mapAnn_occs h a) i))
        = fun i => h.toRingHom (a.anns i) from funext (anns_mapAnn h a)]
  · rw [ite_eq_right hne, ite_eq_right (by rwa [Finset.map_nonempty])]

/-- The scalar-convention counterpart. -/
theorem predProvScalarWith_mapAnn (h : SemiringWithMonusHom K K')
    (a : AggValue T K) (P : T → Kleene) :
    (a.mapAnn ⇑h.toRingHom).predProvScalarWith P
      = h.toRingHom (a.predProvScalarWith P) := by
  unfold predProvScalarWith
  rw [map_sum]
  refine (Fintype.sum_equiv (finCongr (length_mapAnn_occs h a)).finsetCongr
    (fun W => h.toRingHom (Having.worldAnn a.anns W
      * Having.chiOf P (a.valOn W)))
    _ (fun W => ?_)).symm
  rw [Equiv.finsetCongr_apply, valOn_mapAnn h a W, worldAnn_map_finCongr,
    map_mul, worldAnn_hom, chiOf_hom,
    show (fun i => (a.mapAnn ⇑h.toRingHom).anns
        (finCongr (length_mapAnn_occs h a) i))
      = fun i => h.toRingHom (a.anns i) from funext (anns_mapAnn h a)]

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- The pushforward keeps a token's convention. -/
@[simp] theorem scalar_mapAnn (h : SemiringWithMonusHom K K') (a : AggValue T K) :
    (a.mapAnn ⇑h.toRingHom).scalar = a.scalar := rfl

/-- **Token-level hom commutation, in the token's own convention.** Whichever
reading the token carries, the predicate provenance of a comparison against
it commutes with every `SemiringWithMonusHom`. -/
theorem predProvOf_mapAnn (h : SemiringWithMonusHom K K')
    (a : AggValue T K) (op : CompOp) (c : T) :
    (a.mapAnn ⇑h.toRingHom).predProvOf op c
      = h.toRingHom (a.predProvOf op c) := by
  unfold AggValue.predProvOf
  rw [scalar_mapAnn]
  cases a.scalar
  · simpa using predProv_mapAnn h a op c
  · simpa using predProvScalar_mapAnn h a op c

/-- Whichever convention the token carries. -/
theorem predProvOfWith_mapAnn (h : SemiringWithMonusHom K K')
    (a : AggValue T K) (P : T → Kleene) :
    (a.mapAnn ⇑h.toRingHom).predProvOfWith P
      = h.toRingHom (a.predProvOfWith P) := by
  unfold AggValue.predProvOfWith
  rw [scalar_mapAnn]
  cases a.scalar
  · simpa using predProvWith_mapAnn h a P
  · simpa using predProvScalarWith_mapAnn h a P

end AggValue

/-! ## The nested token pushforward

A nested value's occurrences are a bag and its worlds are read off that
bag, so the pushforward needs no reindexing: the worlds of the
pushforward are the pushforwards of the worlds (`worlds_mapAnn`), each
carrying the pushed annotation and reading the same value. That is what
lets the predicate provenance of a nested column commute like an ordinary
token's, with no exclusion. -/

namespace NestedValue

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- **A product over a transported world, factor by factor**: what the
four factors of a world annotation have in common. -/
theorem prod_map_mapAnn (h : SemiringWithMonusHom K K') (W : World T K)
    {g : WorldOcc T K → K} {g' : WorldOcc T K' → K'}
    (hg : ∀ d : WorldOcc T K,
      g' (d.mapAnn ⇑h.toRingHom) = h.toRingHom (g d)) :
    ((W.mapAnn ⇑h.toRingHom).occs.map g').prod
      = h.toRingHom ((W.occs.map g).prod) := by
  rw [map_multiset_prod]
  show (Multiset.map g' (W.occs.map (WorldOcc.mapAnn ⇑h.toRingHom))).prod
    = (Multiset.map _ (W.occs.map g)).prod
  rw [Multiset.map_map, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl (fun d _ => hg d))

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- The additive counterpart. -/
theorem sum_map_mapAnn (h : SemiringWithMonusHom K K') (W : World T K)
    {g : WorldOcc T K → K} {g' : WorldOcc T K' → K'}
    (hg : ∀ d : WorldOcc T K,
      g' (d.mapAnn ⇑h.toRingHom) = h.toRingHom (g d)) :
    ((W.mapAnn ⇑h.toRingHom).occs.map g').sum
      = h.toRingHom ((W.occs.map g).sum) := by
  rw [map_multiset_sum]
  show (Multiset.map g' (W.occs.map (WorldOcc.mapAnn ⇑h.toRingHom))).sum
    = (Multiset.map _ (W.occs.map g)).sum
  rw [Multiset.map_map, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl (fun d _ => hg d))

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- The annotation of an occurrence the world keeps, pushed forward (and
`𝟙` where it keeps it not). -/
theorem keptAnn_mapAnn (h : SemiringWithMonusHom K K') (d : WorldOcc T K) :
    (if (d.mapAnn ⇑h.toRingHom).present = true
        then (d.mapAnn ⇑h.toRingHom).occ.2 else 1)
      = h.toRingHom (if d.present = true then d.occ.2 else 1) := by
  by_cases hd : d.present = true
  · rw [ite_eq_left hd,
      ite_eq_left (show (d.mapAnn ⇑h.toRingHom).present = true from hd)]
    rfl
  · rw [ite_eq_right hd,
      ite_eq_right (show ¬ (d.mapAnn ⇑h.toRingHom).present = true from hd),
      map_one]

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- And the one it leaves out (and `𝟘` where it keeps it). -/
theorem dropAnn_mapAnn (h : SemiringWithMonusHom K K') (d : WorldOcc T K) :
    (if (d.mapAnn ⇑h.toRingHom).present = true
        then 0 else (d.mapAnn ⇑h.toRingHom).occ.2)
      = h.toRingHom (if d.present = true then 0 else d.occ.2) := by
  by_cases hd : d.present = true
  · rw [ite_eq_left hd,
      ite_eq_left (show (d.mapAnn ⇑h.toRingHom).present = true from hd),
      map_zero]
  · rw [ite_eq_right hd,
      ite_eq_right (show ¬ (d.mapAnn ⇑h.toRingHom).present = true from hd)]
    rfl

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- The subfamily an occurrence keeps is the same one, so its product of
inner annotations pushes forward. -/
theorem innerProd_mapAnn (h : SemiringWithMonusHom K K') (d : WorldOcc T K) :
    (∏ j ∈ (d.mapAnn ⇑h.toRingHom).sub,
        (d.mapAnn ⇑h.toRingHom).occ.1.anns j)
      = h.toRingHom (∏ j ∈ d.sub, d.occ.1.anns j) := by
  rw [map_prod]
  show (∏ j ∈ d.sub.map (finCongr
      (AggExpr.length_map_occs ⇑h.toRingHom d.occ.1)).toEmbedding,
      (d.occ.1.mapAnn ⇑h.toRingHom).anns j) = _
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl (fun j _ => AggExpr.anns_mapAnn ⇑h.toRingHom d.occ.1 j)

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- And so does its sum over the inner occurrences it leaves out. -/
theorem innerSum_mapAnn (h : SemiringWithMonusHom K K') (d : WorldOcc T K) :
    (∑ j ∈ ((d.mapAnn ⇑h.toRingHom).sub)ᶜ,
        (d.mapAnn ⇑h.toRingHom).occ.1.anns j)
      = h.toRingHom (∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j) := by
  rw [map_sum]
  show (∑ j ∈ (d.sub.map (finCongr
      (AggExpr.length_map_occs ⇑h.toRingHom d.occ.1)).toEmbedding)ᶜ,
      (d.occ.1.mapAnn ⇑h.toRingHom).anns j) = _
  rw [show (d.sub.map (finCongr
        (AggExpr.length_map_occs ⇑h.toRingHom d.occ.1)).toEmbedding)ᶜ
      = (d.sub)ᶜ.map (finCongr
        (AggExpr.length_map_occs ⇑h.toRingHom d.occ.1)).toEmbedding
      from by
    ext j
    rw [Finset.mem_compl, Finset.mem_map_equiv, Finset.mem_map_equiv,
      Finset.mem_compl],
    Finset.sum_map]
  exact Finset.sum_congr rfl (fun j _ => AggExpr.anns_mapAnn ⇑h.toRingHom d.occ.1 j)

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- **A transported world carries the pushed annotation**: the world
annotation is an `⊗`/`⊖`-polynomial in the occurrence annotations, over
the bag of occurrences rather than over an indexing of it. -/
theorem World.ann_mapAnn (h : SemiringWithMonusHom K K') (W : World T K) :
    (W.mapAnn ⇑h.toRingHom).ann = h.toRingHom W.ann := by
  rw [World.ann, World.ann, World.presentProd, World.presentProd,
    World.absentSum, World.absentSum,
    prod_map_mapAnn h W (keptAnn_mapAnn h),
    prod_map_mapAnn h W (innerProd_mapAnn h),
    sum_map_mapAnn h W (dropAnn_mapAnn h),
    sum_map_mapAnn h W (innerSum_mapAnn h),
    map_mul, map_mul, SemiringWithMonusHom.map_sub, map_one, map_add]

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- **Predicate provenance commutes with a homomorphism** for a nested
value as for an ordinary token: the worlds correspond, each carries the
pushed annotation and reads the same value, and `χ` is `{𝟘,𝟙}`-valued. -/
theorem predProvWith_mapAnn (h : SemiringWithMonusHom K K')
    (a : NestedValue T K) (P : T → Kleene) :
    (a.mapAnn ⇑h.toRingHom).predProvWith P
      = h.toRingHom (a.predProvWith P) := by
  have hfil : Multiset.filter
      ((fun W : World T K' => W.IsWorld (a.mapAnn ⇑h.toRingHom))
        ∘ World.mapAnn ⇑h.toRingHom) a.worlds
      = Multiset.filter (fun W => W.IsWorld a) a.worlds :=
    Multiset.filter_congr
      (fun W _ => World.isWorld_mapAnn (a := a) ⇑h.toRingHom W)
  rw [predProvWith, predProvWith, map_multiset_sum, Multiset.map_map,
    worlds_mapAnn, Multiset.filter_map, hfil, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun W _ => ?_))
  show (World.mapAnn ⇑h.toRingHom W).ann
      * Having.chiOf P ((a.mapAnn ⇑h.toRingHom).valOn
        (World.mapAnn ⇑h.toRingHom W))
    = h.toRingHom (W.ann * Having.chiOf P (a.valOn W))
  rw [map_mul, World.ann_mapAnn, valOn_mapAnn, AggValue.chiOf_hom]

end NestedValue

namespace AggTok

/-- **The predicate provenance of an aggregate column commutes with the
pushforward**, whichever kind of token the column holds: on an ordinary
token through `AggValue.predProvOfWith_mapAnn`, on a nested one through
`NestedValue.predProvWith_mapAnn`, on an expression through
`AggExpr.predProvWith_mapAnn`. -/
theorem predProvOfWith_mapAnn (h : SemiringWithMonusHom K K')
    (x : AggTok T K) (P : T → Kleene) :
    (x.mapAnn ⇑h.toRingHom).predProvOfWith P
      = h.toRingHom (x.predProvOfWith P) := by
  cases x with
  | tok a => exact AggValue.predProvOfWith_mapAnn h a P
  | nest a =>
    show (NestedValue.mapAnn ⇑h.toRingHom a).predProvWith P = _
    exact NestedValue.predProvWith_mapAnn h a P
  | expr e => exact (AggExpr.predProvWith_mapAnn h e P).symm

/-- A comparison is one such test. -/
theorem predProvOf_mapAnn (h : SemiringWithMonusHom K K')
    (x : AggTok T K) (op : CompOp) (c : T) :
    (x.mapAnn ⇑h.toRingHom).predProvOf op c
      = h.toRingHom (x.predProvOf op c) :=
  predProvOfWith_mapAnn h x _

/-- So is the alternative test. -/
theorem altProv_mapAnn (h : SemiringWithMonusHom K K')
    (x : AggTok T K) (v : T) :
    (x.mapAnn ⇑h.toRingHom).altProv v = h.toRingHom (x.altProv v) :=
  predProvOfWith_mapAnn h x _

end AggTok

/-! ## The predicate pushforward -/

omit [DecidableEq K] [DecidableEq K'] in
/-- Terms over regular columns are untouched by the pushforward (their
token reads collapse, and `collapse` is annotation-independent). -/
theorem TermGIn.eval_mapAnnSum {c n : ℕ} {κ : Fin n → ColKind}
    (h : SemiringWithMonusHom K K') (t : TermGIn T c κ) {γ : Fin c → T}
    (u : Tuple (GenValue T K) n) :
    t.eval (fun k => AggValue.mapAnnSum ⇑h.toRingHom (u k)) γ = t.eval u γ := by
  induction t with
  | const a => rfl
  | outer k => rfl
  | index k hk =>
    show AggValue.collapseSum (AggValue.mapAnnSum ⇑h.toRingHom (u k))
      = AggValue.collapseSum (u k)
    exact AggValue.collapseSum_mapAnnSum ⇑h.toRingHom (u k)
  | provIndex k hk =>
    show AggValue.collapseSum (AggValue.mapAnnSum ⇑h.toRingHom (u k))
      = AggValue.collapseSum (u k)
    exact AggValue.collapseSum_mapAnnSum ⇑h.toRingHom (u k)
  | cmpAgg k hk op c ih => rfl
  | chiGate op t₁ t₂ ih₁ ih₂ => rfl
  | add t₁ t₂ ih₁ ih₂ => rw [TermGIn.eval, TermGIn.eval, ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => rw [TermGIn.eval, TermGIn.eval, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => rw [TermGIn.eval, TermGIn.eval, ih₁, ih₂]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    rw [TermGIn.eval, TermGIn.eval, ih₁, ih₂, ih₃, ih₄]
  | coalesce t₁ t₂ ih₁ ih₂ => rw [TermGIn.eval, TermGIn.eval, ih₁, ih₂]

/-- **Predicate-level hom commutation.** The predicate provenance of a
generalized predicate commutes with every `SemiringWithMonusHom`:
regular atoms through `χ`, aggregate atoms through the token-level
commutation – whichever kind of token the column holds, a nested one
included – `∧ ↦ ⊗` and `∨ ↦ ⊕` through `map_mul` and `map_add`, and
`¬` by polarity. -/
theorem GenPredIn.predsem_mapAnn {c n : ℕ} {κ : Fin n → ColKind}
    (h : SemiringWithMonusHom K K') (φ : GenPredIn T c κ) {γ : Fin c → T} (neg : Bool)
    (u : Tuple (GenValue T K) n) :
    φ.predsem neg (fun k => AggValue.mapAnnSum ⇑h.toRingHom (u k)) γ
      = h.toRingHom (φ.predsem neg u γ) := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ =>
    show Having.chi _ _ _ = _
    rw [show ((GenPredIn.cmp op t₁ t₂).predsem neg (K := K) u γ)
        = Having.chi (if neg then op.negate else op)
            (t₁.eval u γ) (t₂.eval u γ) from rfl,
      TermGIn.eval_mapAnnSum h t₁ u, TermGIn.eval_mapAnnSum h t₂ u, chi_hom]
  | aggCmp k hk op t =>
    cases hu : u k with
    | inl w =>
      have hred : AggValue.mapAnnSum (⇑h.toRingHom) (Sum.inl w : GenValue T K)
          = (Sum.inl w : GenValue T K') := rfl
      simp only [GenPredIn.predsem, hu, hred, map_zero]
    | inr x =>
      have hred : AggValue.mapAnnSum (⇑h.toRingHom) (Sum.inr x : GenValue T K)
          = Sum.inr (x.mapAnn ⇑h.toRingHom) := rfl
      simp only [GenPredIn.predsem, hu, hred]
      rw [TermGIn.eval_mapAnnSum h t u,
        AggTok.predProvOf_mapAnn h x]
  | aggRange k hk op₁ t₁ op₂ t₂ =>
    cases hu : u k with
    | inl w =>
      have hred : AggValue.mapAnnSum (⇑h.toRingHom) (Sum.inl w : GenValue T K)
          = (Sum.inl w : GenValue T K') := rfl
      simp only [GenPredIn.predsem, hu, hred, map_zero]
    | inr x =>
      have hred : AggValue.mapAnnSum (⇑h.toRingHom) (Sum.inr x : GenValue T K)
          = Sum.inr (x.mapAnn ⇑h.toRingHom) := rfl
      simp only [GenPredIn.predsem, hu, hred]
      rw [TermGIn.eval_mapAnnSum h t₁ u, TermGIn.eval_mapAnnSum h t₂ u,
        AggTok.predProvOfWith_mapAnn h x]
  | and φ ψ ihφ ihψ =>
    cases neg with
    | false =>
      show φ.predsem false _ γ * ψ.predsem false _ γ = _
      rw [ihφ false, ihψ false,
        show ((GenPredIn.and φ ψ).predsem false u γ)
          = φ.predsem false u γ * ψ.predsem false u γ from rfl, map_mul]
    | true =>
      show φ.predsem true _ γ + ψ.predsem true _ γ = _
      rw [ihφ true, ihψ true,
        show ((GenPredIn.and φ ψ).predsem true u γ)
          = φ.predsem true u γ + ψ.predsem true u γ from rfl, map_add]
  | or φ ψ ihφ ihψ =>
    cases neg with
    | false =>
      show φ.predsem false _ γ + ψ.predsem false _ γ = _
      rw [ihφ false, ihψ false,
        show ((GenPredIn.or φ ψ).predsem false u γ)
          = φ.predsem false u γ + ψ.predsem false u γ from rfl, map_add]
    | true =>
      show φ.predsem true _ γ * ψ.predsem true _ γ = _
      rw [ihφ true, ihψ true,
        show ((GenPredIn.or φ ψ).predsem true u γ)
          = φ.predsem true u γ * ψ.predsem true u γ from rfl, map_mul]
  | not φ ih =>
    show φ.predsem (!neg) _ γ = _
    rw [ih (!neg),
      show ((GenPredIn.not φ).predsem neg u γ)
        = φ.predsem (!neg) u γ from rfl]

/-! ## The group sequence under the pushforward

`Having.havingGroup` sorts the group by the tuple part and breaks ties on
equal tuple parts by the alternative order on the annotations. The
pushforward changes the tie-break order, so the hom-side group sequence
coincides with the mapped base-side group sequence only up to a
permutation inside blocks of equal tuple parts – a `TiePerm`, which the
congruence layer of `Provenance.AggValueCongr` renders invisible to every
reading of the resulting tokens. -/

section HavingGroupHom

variable {n₁ : ℕ} [HasAltLinearOrder K] [HasAltLinearOrder K']

omit [DecidableEq K] in
/-- The hom-side group sequence is a tie-block permutation of the mapped
base-side group sequence: both are sorted by the tuple part and carry the
same multiset of annotated occurrences. -/
theorem havingGroup_tiePerm (h : SemiringWithMonusHom K K')
    (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    TiePerm (fun p q : AnnotatedTuple T K' m => p.fst = q.fst)
      ((Having.havingGroup is r g).map
        (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m)))
      (Having.havingGroup is
        (r.map (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m)))
        g) := by
  classical
  refine tiePerm_of_perm_of_sorted Prod.fst ?_ ?_ ?_
  · refine Multiset.coe_eq_coe.mp ?_
    rw [← Multiset.map_coe, Having.havingGroup_coe, Having.havingGroup_coe,
      Multiset.filter_map]
    refine congrArg _ (Multiset.filter_congr fun p _ => ?_)
    exact Iff.rfl
  · exact List.pairwise_map.mpr ((Having.havingGroup_pairwise is r g).imp
      (fun hpq => hpq.elim le_of_lt le_of_eq))
  · exact (Having.havingGroup_pairwise is _ g).imp
      (fun hpq => hpq.elim le_of_lt le_of_eq)

omit [DecidableEq K] in
/-- **And in the order the aggregation asks for**: pushing a group
forward and reading it in the clause's order gives a tie-block
permutation of reading the pushed-forward group, because the clause reads
the rows, which the pushforward keeps, and both readings are sorted by
it. -/
theorem havingGroupOrd_tiePerm (h : SemiringWithMonusHom K K')
    (is : Tuple (Fin m) n₁) (ord : GroupOrder T m)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    TiePerm (fun p q : AnnotatedTuple T K' m => p.fst = q.fst)
      ((Having.havingGroupOrd is ord r g).map
        (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m)))
      (Having.havingGroupOrd is ord
        (r.map (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m)))
        g) := by
  classical
  cases ord with
  | unord => exact havingGroup_tiePerm h is r g
  | byCols cols spec =>
    have hperm : ((Having.havingGroup is r g).map
          (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))).Perm
        (Having.havingGroup is
          (r.map (fun p =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g) := by
      refine Multiset.coe_eq_coe.mp ?_
      rw [← Multiset.map_coe, Having.havingGroup_coe, Having.havingGroup_coe,
        Multiset.filter_map]
      exact congrArg _ (Multiset.filter_congr fun p _ => Iff.rfl)
    show TiePerm (fun p q : AnnotatedTuple T K' m => p.fst = q.fst)
      (List.map (fun p : AnnotatedTuple T K m =>
          ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))
        (OrderSpec.sortSeq (Tuple.key cols) Prod.fst spec
          (Having.havingGroup is r g)))
      (OrderSpec.sortSeq (Tuple.key cols) Prod.fst spec
        (Having.havingGroup is (r.map (fun p =>
          ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g))
    rw [ValueFrame.sortSeq_mapAnn cols spec ⇑h.toRingHom]
    exact OrderSpec.sortSeq_tiePerm hperm

omit [DecidableEq K] in
/-- The occurrence payloads of the two group tokens – base-side pushed
forward, and hom-side – differ by a tie-block permutation on equal values:
occurrences with equal tuple parts have equal aggregated-term values. -/
theorem ofGroup_mapAnn_tiePerm (h : SemiringWithMonusHom K K')
    (f : SeqAggFunc T) {c : ℕ} (t : TermIn T c m) {γ : Fin c → T}
    (is : Tuple (Fin m) n₁)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    TiePerm (fun p q : T × K' => p.1 = q.1)
      ((AggValue.ofGroup f t (Having.havingGroup is r g) γ).mapAnn
        ⇑h.toRingHom).occs
      (AggValue.ofGroup f t
        (Having.havingGroup is
          (r.map (fun p =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g) γ).occs := by
  have hocc₁ : ((AggValue.ofGroup f t (Having.havingGroup is r g) γ).mapAnn
      ⇑h.toRingHom).occs
      = ((Having.havingGroup is r g).map
          (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))).map
          (fun p => (t.eval p.fst γ, p.snd)) := by
    simp only [AggValue.ofGroup, AggValue.mapAnn, List.map_map]
    rfl
  rw [hocc₁]
  exact (havingGroup_tiePerm h is r g).map
    (eqv' := fun p q : T × K' => p.1 = q.1)
    (fun p : AnnotatedTuple T K' m => (t.eval p.fst γ, p.snd))
    (fun hpq => congrArg (fun z => t.eval z γ) hpq)

omit [DecidableEq K] in
/-- The same, for an aggregation reading its group in a clause's order. -/
theorem ofGroupOrd_mapAnn_tiePerm (h : SemiringWithMonusHom K K')
    (f : SeqAggFunc T) {c : ℕ} (t : TermIn T c m) {γ : Fin c → T}
    (is : Tuple (Fin m) n₁) (ord : GroupOrder T m)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    TiePerm (fun p q : T × K' => p.1 = q.1)
      ((AggValue.ofGroup f t (Having.havingGroupOrd is ord r g) γ).mapAnn
        ⇑h.toRingHom).occs
      (AggValue.ofGroup f t
        (Having.havingGroupOrd is ord
          (r.map (fun p =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g) γ).occs := by
  have hocc₁ : ((AggValue.ofGroup f t
        (Having.havingGroupOrd is ord r g) γ).mapAnn ⇑h.toRingHom).occs
      = ((Having.havingGroupOrd is ord r g).map
          (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))).map
          (fun p => (t.eval p.fst γ, p.snd)) := by
    simp only [AggValue.ofGroup, AggValue.mapAnn, List.map_map]
    rfl
  rw [hocc₁]
  exact (havingGroupOrd_tiePerm h is ord r g).map
    (eqv' := fun p q : T × K' => p.1 = q.1)
    (fun p : AnnotatedTuple T K' m => (t.eval p.fst γ, p.snd))
    (fun hpq => congrArg (fun z => t.eval z γ) hpq)

/-- **Group-token hom commutation.** The predicate provenance of a
comparison against the token of a group of the pushed-forward relation is
the image under the hom of the base-side predicate provenance: the two
tokens differ by a tie-block permutation of the payload, which
`AggValue.predProv_congr` makes invisible. -/
theorem ofGroup_predProv_hom (h : SemiringWithMonusHom K K')
    (f : SeqAggFunc T) {c : ℕ} (t : TermIn T c m) {γ : Fin c → T}
    (is : Tuple (Fin m) n₁)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) (op : CompOp) (c : T) :
    (AggValue.ofGroup f t
        (Having.havingGroup is
          (r.map (fun p =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g)
          γ).predProv op c
      = h.toRingHom
          ((AggValue.ofGroup f t (Having.havingGroup is r g) γ).predProv op c) := by
  rw [← AggValue.predProv_mapAnn]
  refine (AggValue.predProv_congr ?_ (ofGroup_mapAnn_tiePerm h f t is r g)
    op c).symm
  rfl

omit [DecidableEq K] in
/-- The pending group factor – the sum of the occurrence annotations of the
group – commutes with the pushforward, the tie-block permutation being
invisible to a sum. -/
theorem havingGroup_annSum_hom (h : SemiringWithMonusHom K K')
    (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    ((Having.havingGroup is
        (r.map (fun p =>
          ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g).map
        Prod.snd).sum
      = h.toRingHom (((Having.havingGroup is r g).map Prod.snd).sum) := by
  have hperm : ((Having.havingGroup is
      (r.map (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m)))
      g).map Prod.snd).Perm
      (((Having.havingGroup is r g).map
        (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))).map
        Prod.snd) :=
    List.Perm.map Prod.snd ((havingGroup_tiePerm h is r g).perm).symm
  rw [map_list_sum h.toRingHom ((Having.havingGroup is r g).map Prod.snd),
    List.map_map]
  exact hperm.sum_eq.trans (by rw [List.map_map]; rfl)

omit [DecidableEq K] in
/-- **The group's existence factor does not read the aggregation's
order**: it is the sum of the occurrences' annotations, and the ordered
reading is a listing of the same occurrences. -/
theorem havingGroupOrd_annSum_hom (h : SemiringWithMonusHom K K')
    (is : Tuple (Fin m) n₁) (ord : GroupOrder T m)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    ((Having.havingGroupOrd is ord
        (r.map (fun p =>
          ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g).map
        Prod.snd).sum
      = h.toRingHom (((Having.havingGroupOrd is ord r g).map Prod.snd).sum) := by
  rw [((Having.havingGroupOrd_perm is ord
      (r.map (fun p => ((p.fst, h.toRingHom p.snd)
        : AnnotatedTuple T K' m))) g).map Prod.snd).sum_eq,
    ((Having.havingGroupOrd_perm is ord r g).map Prod.snd).sum_eq]
  exact havingGroup_annSum_hom h is r g

/-! ## The window's frame under the pushforward

A frame is read off the values, so the pushforward carries it unchanged;
what it changes is the order the frame's occurrences are read in, and only
inside blocks of equal tuple parts – a `TiePerm`, as for a group. -/

omit [DecidableEq K] in
/-- The sorted reading of a pushed-forward relation is a tie-block
permutation of the pushed-forward sorted reading: the pushforward keeps the
tuple part, so only the tie-break between equal tuples can move. -/
theorem sortList_hom_tiePerm (h : SemiringWithMonusHom K K') {n' : ℕ}
    (M : Multiset (AnnotatedTuple T K n')) :
    TiePerm (fun a b : AnnotatedTuple T K' n' => a.fst = b.fst)
      ((sortList M).map
        (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')))
      (sortList (α := AnnotatedTuple T K' n')
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) M)) := by
  refine tiePerm_of_perm_of_sorted
    (fun q : AnnotatedTuple T K' n' => q.fst) ?_ ?_ ?_
  · refine Multiset.coe_eq_coe.mp ?_
    rw [← Multiset.map_coe, sortList_coe, sortList_coe]
  · exact List.pairwise_map.mpr
      ((sortList_pairwise M).imp (fun hab => ValueFrame.le_fst_of_le hab))
  · exact (sortList_pairwise (α := AnnotatedTuple T K' n')
      (Multiset.map (fun q : AnnotatedTuple T K n' =>
        ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) M)).imp
      (fun hab => ValueFrame.le_fst_of_le hab)

omit [DecidableEq K] in
/-- **The frame itself is carried by the pushforward up to a tie-block
permutation**: the frame is the same rows – `ValueFrame.frameOf_map` – and
each side sorts them by its own clause, so only the order inside a block
of equal tuples can differ. This is the step every reading of a window's
column rests on, whether the column is a token or an expression. -/
theorem frameListOf_mapAnn_tiePerm (h : SemiringWithMonusHom K K')
    {n' m' p' : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') (w : ValueFrame T p')
    (X : Multiset (AnnotatedTuple T K n')) {x : AnnotatedTuple T K n'}
    (hx : x ∈ X) :
    TiePerm (fun a b : AnnotatedTuple T K' n' => a.fst = b.fst)
      ((ValueFrame.frameListOf (α := AnnotatedTuple T K n') Prod.fst P O o w
          X x).map
        (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')))
      (ValueFrame.frameListOf (α := AnnotatedTuple T K' n') Prod.fst P O o w
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
        ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n')) := by
  have hframe : ValueFrame.frameOf (α := AnnotatedTuple T K' n') Prod.fst P O w
      (Multiset.map (fun q : AnnotatedTuple T K n' =>
        ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
      ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n')
      = Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n'))
        (ValueFrame.frameOf (α := AnnotatedTuple T K n') Prod.fst P O w X x) :=
    ValueFrame.frameOf_map _ (fun _ => rfl) P O w X hx
  have h1 : ((ValueFrame.frameListOf (α := AnnotatedTuple T K n') Prod.fst P O o w
        X x).map
      (fun q : AnnotatedTuple T K n' =>
        ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')))
      = OrderSpec.sortSeq (Tuple.key O) Prod.fst o
        ((sortList (ValueFrame.frameOf (α := AnnotatedTuple T K n')
            Prod.fst P O w X x)).map
          (fun q : AnnotatedTuple T K n' =>
            ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n'))) := by
    rw [ValueFrame.frameListOf, ← ValueFrame.sortSeq_mapAnn O o ⇑h.toRingHom]
  have h2 : ValueFrame.frameListOf (α := AnnotatedTuple T K' n') Prod.fst P O o w
      (Multiset.map (fun q : AnnotatedTuple T K n' =>
        ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
      ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n')
      = OrderSpec.sortSeq (Tuple.key O) Prod.fst o
        (sortList (α := AnnotatedTuple T K' n')
          (Multiset.map (fun q : AnnotatedTuple T K n' =>
            ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n'))
            (ValueFrame.frameOf (α := AnnotatedTuple T K n')
              Prod.fst P O w X x))) := by
    rw [ValueFrame.frameListOf, hframe]
  rw [h1, h2]
  exact OrderSpec.sortSeq_tiePerm (key := Tuple.key O)
    (val := (Prod.fst : AnnotatedTuple T K' n' → Tuple T n')) (o := o)
    (sortList_hom_tiePerm h _).perm

omit [DecidableEq K] in
/-- The occurrence payloads of a window's token – base-side pushed forward,
and hom-side – differ by a tie-block permutation on equal values: the frame
itself is carried unchanged, only the order inside a block of equal tuples
can move. -/
theorem tokenOf_mapAnn_tiePerm (h : SemiringWithMonusHom K K')
    {n' m' p' : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') (w : ValueFrame T p') {c : ℕ} (t : TermIn T c n')
    {γ : Fin c → T} (f : SeqAggFunc T)
    (X : Multiset (AnnotatedTuple T K n')) {x : AnnotatedTuple T K n'}
    (hx : x ∈ X) :
    TiePerm (fun a b : T × K' => a.1 = b.1)
      ((ValueFrame.tokenOf P O o w t f X x γ).mapAnn ⇑h.toRingHom).occs
      (ValueFrame.tokenOf P O o w t f
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
        ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ).occs := by
  have hframe : ValueFrame.frameOf (α := AnnotatedTuple T K' n') Prod.fst P O w
      (Multiset.map (fun q : AnnotatedTuple T K n' =>
        ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
      ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n')
      = Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n'))
        (ValueFrame.frameOf (α := AnnotatedTuple T K n') Prod.fst P O w X x) :=
    ValueFrame.frameOf_map _ (fun _ => rfl) P O w X hx
  have hocc1 : ((ValueFrame.tokenOf P O o w t f X x γ).mapAnn ⇑h.toRingHom).occs
      = (OrderSpec.sortSeq (Tuple.key O) Prod.fst o
          ((sortList (ValueFrame.frameOf (α := AnnotatedTuple T K n')
              Prod.fst P O w X x)).map
            (fun q : AnnotatedTuple T K n' =>
              ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')))).map
          (fun q : AnnotatedTuple T K' n' => (t.eval q.fst γ, q.snd)) := by
    show ((ValueFrame.tokenOf P O o w t f X x γ).occs).map
        (fun z => (z.fst, h.toRingHom z.snd)) = _
    rw [ValueFrame.tokenOf_occs, List.map_map]
    rw [← ValueFrame.sortSeq_mapAnn O o ⇑h.toRingHom, List.map_map]
    rfl
  have hocc2 : (ValueFrame.tokenOf P O o w t f
      (Multiset.map (fun q : AnnotatedTuple T K n' =>
        ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
      ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ).occs
      = (OrderSpec.sortSeq (Tuple.key O) Prod.fst o
          (sortList (α := AnnotatedTuple T K' n')
            (Multiset.map (fun q : AnnotatedTuple T K n' =>
              ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n'))
              (ValueFrame.frameOf (α := AnnotatedTuple T K n')
                Prod.fst P O w X x)))).map
          (fun q : AnnotatedTuple T K' n' => (t.eval q.fst γ, q.snd)) := by
    rw [ValueFrame.tokenOf_occs, ValueFrame.frameListOf, hframe]
  rw [hocc1, hocc2]
  exact (OrderSpec.sortSeq_tiePerm (key := Tuple.key O)
      (val := (Prod.fst : AnnotatedTuple T K' n' → Tuple T n')) (o := o)
      (sortList_hom_tiePerm h _).perm).map
    (eqv' := fun a b : T × K' => a.1 = b.1)
    (fun q : AnnotatedTuple T K' n' => (t.eval q.fst γ, q.snd))
    (fun hpq => congrArg (fun z => t.eval z γ) hpq)

end HavingGroupHom

/-! ## The simulation relation

The evaluator-level commutation cannot be a per-row equality: the hom side
may supersede more pending factors (a non-injective hom conflates the
annotation-list equality tests) and its group sequences are only tie-block
permutations of the mapped base-side ones. The right invariant is a
row-wise simulation: regular values equal, aggregate columns reading as
the pushed-forward ones do, and the *finalized* annotation equal to the
image of the base-side finalized annotation. Both discrepancies are value-
neutral at that level: extra supersedes by guard absorption
(`delta_absorb`), tie-breaks by the congruence layer. -/

section Simulation

/-- **Equivalence of lifted values**: equal regular values, or aggregate
columns that read the same. On an ordinary token that is the same
aggregate over tie-block-permuted payloads; on an expression and on a
nested value it is the four readings the metatheory takes – the collapse,
the convention, the values over the worlds and the predicate provenance
of every test – since neither family is compared as a family: an
expression's is listed by occurrence index, where a tie-block permutation
of it is not an equality, and a nested value's is a bag, where the
occurrences carry tokens that nothing orders.

The occurrence *annotations* are deliberately not compared: on either
kind the two sides' families agree only up to a tie-block permutation,
and the evaluator's own group bookkeeping travels in `GenRow.Sim`'s
second component rather than here. -/
def GenValue.Equiv : GenValue T K → GenValue T K → Prop
  | Sum.inl v', Sum.inl v => v' = v
  | Sum.inr (AggTok.tok a'), Sum.inr (AggTok.tok a) =>
      a'.agg = a.agg ∧ a'.scalar = a.scalar ∧
        TiePerm (fun p q : T × K => p.1 = q.1) a'.occs a.occs
  | Sum.inr (AggTok.nest b'), Sum.inr (AggTok.nest b) =>
      b'.collapse = b.collapse ∧ b'.scalar = b.scalar
        ∧ b'.vals = b.vals
        ∧ ∀ P : T → Kleene, b'.predProvWith P = b.predProvWith P
  | Sum.inr (AggTok.expr e'), Sum.inr (AggTok.expr e) =>
      e'.collapse = e.collapse ∧ e'.isScalar = e.isScalar
        ∧ e'.vals = e.vals
        ∧ (∀ P : T → Kleene, e'.predProvWith P = e.predProvWith P)
        ∧ e'.worldStats = e.worldStats
  | _, _ => False

/-- **The equivalence does not read the family** a value is stamped
with. -/
theorem GenValue.Equiv.setFam {x' x : AggTok T K}
    (h : GenValue.Equiv (Sum.inr x') (Sum.inr x)) (φ' φ : FamId T) :
    GenValue.Equiv (Sum.inr (x'.setFam φ')) (Sum.inr (x.setFam φ)) := by
  cases x' <;> cases x <;> exact h

/-- A regular value is equivalent to no token. -/
theorem GenValue.Equiv.not_inl_inr {w : T} {x : AggTok T K} :
    ¬ GenValue.Equiv (Sum.inl w) (Sum.inr x) := by
  cases x <;> exact not_false

/-- And a token to no regular value. -/
theorem GenValue.Equiv.not_inr_inl {w : T} {x : AggTok T K} :
    ¬ GenValue.Equiv (Sum.inr x) (Sum.inl w) := by
  cases x <;> exact not_false

/-! ### What the equivalence gives

Downstream never cases on the kind of token: it reads an aggregate
column through its collapse, its convention, its values and its
predicate provenance, and each of those is equal on the two sides. -/

/-- **Equivalent columns hold the same kind of token.** -/
theorem GenValue.Equiv.isNested_eq {x' x : AggTok T K}
    (h : GenValue.Equiv (Sum.inr x') (Sum.inr x)) :
    x'.isNested = x.isNested := by
  cases x' with
  | tok a' => cases x with
    | tok a => rfl
    | nest b => exact absurd h not_false
    | expr e => exact absurd h not_false
  | nest b' => cases x with
    | nest b => rfl
    | tok a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | expr e' => cases x with
    | expr e => rfl
    | tok a => exact absurd h not_false
    | nest b => exact absurd h not_false

/-- Equivalent columns are read in the same convention. -/
theorem GenValue.Equiv.scalar_eq {x' x : AggTok T K}
    (h : GenValue.Equiv (Sum.inr x') (Sum.inr x)) : x'.scalar = x.scalar := by
  cases x' with
  | nest b' =>
    cases x with
    | nest b => exact h.2.1
    | tok a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | tok a' =>
    cases x with
    | tok a => exact h.2.1
    | nest a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | expr e' =>
    cases x with
    | expr e => exact h.2.1
    | tok a => exact absurd h not_false
    | nest a => exact absurd h not_false

/-- They collapse to the same regular value. -/
theorem GenValue.Equiv.collapse_eq {x' x : AggTok T K}
    (h : GenValue.Equiv (Sum.inr x') (Sum.inr x)) :
    x'.collapse = x.collapse := by
  cases x' with
  | nest b' =>
    cases x with
    | nest b => exact h.1
    | tok a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | tok a' =>
    cases x with
    | tok a => exact AggValue.collapse_congr h.1 h.2.2
    | nest a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | expr e' =>
    cases x with
    | expr e => exact h.1
    | tok a => exact absurd h not_false
    | nest a => exact absurd h not_false

/-- They take the same values over their worlds, so they read as the same
key. -/
theorem GenValue.Equiv.vals_eq {x' x : AggTok T K}
    (h : GenValue.Equiv (Sum.inr x') (Sum.inr x)) : x'.vals = x.vals := by
  cases x' with
  | nest b' =>
    cases x with
    | nest b => exact h.2.2.1
    | tok a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | tok a' =>
    cases x with
    | tok a => exact AggValue.vals_congr h.1 h.2.1 h.2.2
    | nest a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | expr e' =>
    cases x with
    | expr e => exact h.2.2.1
    | tok a => exact absurd h not_false
    | nest a => exact absurd h not_false

/-- **And every three-valued test of them has the same provenance** –
the congruence layer on an ordinary token, the expression's own
conjunct on an expression. This is what carries the simulation through
`GenPredIn.predsem`. -/
theorem GenValue.Equiv.predProvOfWith_eq {x' x : AggTok T K}
    (h : GenValue.Equiv (Sum.inr x') (Sum.inr x)) (P : T → Kleene) :
    x'.predProvOfWith P = x.predProvOfWith P := by
  cases x' with
  | nest b' =>
    cases x with
    | nest b => exact h.2.2.2 P
    | tok a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | tok a' =>
    cases x with
    | tok a => exact AggValue.predProvOfWith_congr h.1 h.2.1 h.2.2 P
    | nest a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | expr e' =>
    cases x with
    | expr e => exact h.2.2.2.1 P
    | tok a => exact absurd h not_false
    | nest a => exact absurd h not_false

/-- A comparison is one such test. -/
theorem GenValue.Equiv.predProvOf_eq {x' x : AggTok T K}
    (h : GenValue.Equiv (Sum.inr x') (Sum.inr x)) (op : CompOp) (c : T) :
    x'.predProvOf op c = x.predProvOf op c :=
  h.predProvOfWith_eq _

/-- So is the alternative test `[a ≐ v]`. -/
theorem GenValue.Equiv.altProv_eq {x' x : AggTok T K}
    (h : GenValue.Equiv (Sum.inr x') (Sum.inr x)) (v : T) :
    x'.altProv v = x.altProv v :=
  h.predProvOfWith_eq _

/-- **Two expression columns over tie-permuted families are
equivalent**: the four readings `GenValue.Equiv` asks of them are
exactly `AggExpr.readings_congr`'s bundle. -/
theorem GenValue.Equiv.of_expr_tiePerm {q : ℕ} {φ₁ φ₂ : FamId T}
    {occs₁ occs₂ : List ((Fin q → T) × K × (Fin q → Bool) × (Fin q → Bool))}
    (aggs : Fin q → SeqAggFunc T) {sc₁ sc₂ : Fin q → Bool} (hsc : sc₁ = sc₂)
    (g : (Fin q → T) → T)
    (h : TiePerm (fun z z' => z.fst = z'.fst ∧ z.snd.snd = z'.snd.snd)
      occs₁ occs₂) :
    GenValue.Equiv
      (Sum.inr (AggTok.expr (AggExpr.mk q occs₁ aggs sc₁ g φ₁)) : GenValue T K)
      (Sum.inr (AggTok.expr (AggExpr.mk q occs₂ aggs sc₂ g φ₂))) := by
  subst hsc
  obtain ⟨hcol, hsc', hvals, hprov⟩ := AggExpr.readings_congr (φ₁ := φ₁) (φ₂ := φ₂) aggs sc₁ g h
  exact ⟨hcol, hsc', hvals, hprov, AggExpr.worldStats_congr (φ₁ := φ₁) (φ₂ := φ₂) aggs sc₁ g h⟩

/-- **Equivalent columns give a nested value the same statistics.** The
inner reading of a column is its own expression where it holds one, the
token's own where it holds a token, and its collapse where it holds a
nested value – and in each case what a nested value reads of it is fixed
by the equivalence: by the statistics it now carries for an expression,
by the tie-block permutation for a token, and by the collapse for a
nested value or a regular one. -/
theorem GenValue.Equiv.innerValue_worldStats {v' v : GenValue T K}
    (h : GenValue.Equiv v' v) :
    (GenValue.innerValue v').worldStats = (GenValue.innerValue v).worldStats := by
  cases v' with
  | inl w' =>
    cases v with
    | inl w => rw [show w' = w from h]
    | inr x => exact absurd h GenValue.Equiv.not_inl_inr
  | inr x' =>
    cases v with
    | inl w => exact absurd h GenValue.Equiv.not_inr_inl
    | inr x =>
      cases x' with
      | tok a' =>
        cases x with
        | tok a =>
          have hagg : a'.agg = a.agg := h.1
          have hsc : a'.scalar = a.scalar := h.2.1
          show (AggExpr.ofValue a').worldStats = (AggExpr.ofValue a).worldStats
          unfold AggExpr.ofValue
          rw [hagg, hsc]
          refine AggExpr.worldStats_congr (fun _ => a.agg) (fun _ => a.scalar)
            (fun v => v 0) ?_
          exact h.2.2.map
            (eqv' := fun z z' : (Fin 1 → T) × K × (Fin 1 → Bool) × (Fin 1 → Bool) =>
              z.fst = z'.fst ∧ z.snd.snd = z'.snd.snd)
            (fun o => ((fun _ : Fin 1 => o.fst), o.snd,
              (fun _ : Fin 1 => true), (fun _ : Fin 1 => true)))
            (fun hpq => ⟨funext (fun _ => hpq), rfl⟩)
        | nest b => exact absurd h not_false
        | expr e => exact absurd h not_false
      | nest b' =>
        cases x with
        | nest b =>
          show (NestedValue.constInner b'.collapse).worldStats
            = (NestedValue.constInner b.collapse).worldStats
          rw [show b'.collapse = b.collapse from h.1]
        | tok a => exact absurd h not_false
        | expr e => exact absurd h not_false
      | expr e' =>
        cases x with
        | expr e => exact h.2.2.2.2
        | tok a => exact absurd h not_false
        | nest b => exact absurd h not_false

/-- **Reading an aggregate column through a function preserves the
equivalence**: a term over one aggregate column moves `g` and leaves
the family, the convention and the worlds alone. -/
theorem GenValue.Equiv.postcomp {x' x : AggTok T K} (gf : T → T)
    (h : GenValue.Equiv (Sum.inr x') (Sum.inr x)) :
    GenValue.Equiv (Sum.inr (x'.postcomp gf) : GenValue T K)
      (Sum.inr (x.postcomp gf)) := by
  cases x' with
  | nest b' =>
    cases x with
    | nest b =>
      refine ⟨congrArg gf h.1, h.2.1, ?_, fun P => ?_⟩
      · rw [NestedValue.vals_postcomp, NestedValue.vals_postcomp, h.2.2.1]
      · rw [NestedValue.predProvWith_postcomp,
          NestedValue.predProvWith_postcomp, h.2.2.2]
    | tok a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | tok a' =>
    cases x with
    | tok a =>
      exact ⟨congrArg (fun f => fun L => gf (f L)) h.1, h.2.1, h.2.2⟩
    | nest a => exact absurd h not_false
    | expr e => exact absurd h not_false
  | expr e' =>
    cases x with
    | expr e =>
      refine ⟨congrArg gf h.1, h.2.1, ?_, (fun P => ?_), ?_⟩
      · rw [AggExpr.vals_postcomp, AggExpr.vals_postcomp, h.2.2.1]
      · rw [AggExpr.predProvWith_postcomp, AggExpr.predProvWith_postcomp,
          h.2.2.2.1]
      · rw [AggExpr.worldStats_postcomp, AggExpr.worldStats_postcomp,
          h.2.2.2.2]
    | tok a => exact absurd h not_false
    | nest a => exact absurd h not_false

/-- Equivalent lifted values collapse to the same regular value. -/
theorem GenValue.Equiv.collapseSum_eq {v' v : GenValue T K}
    (h : GenValue.Equiv v' v) :
    AggValue.collapseSum v' = AggValue.collapseSum v := by
  cases v' with
  | inl w' =>
    cases v with
    | inl w => exact congrArg Sum.inl h ▸ rfl
    | inr a => exact absurd h GenValue.Equiv.not_inl_inr
  | inr x' =>
    cases v with
    | inl w => exact absurd h GenValue.Equiv.not_inr_inl
    | inr x => exact h.collapse_eq

/-- Terms evaluate equally on pointwise-equivalent tuples. -/
theorem TermGIn.eval_equiv {c n : ℕ} {κ : Fin n → ColKind} (t : TermGIn T c κ) {γ : Fin c → T}
    {u' u : Tuple (GenValue T K) n}
    (hu : ∀ k, GenValue.Equiv (u' k) (u k)) :
    t.eval u' γ = t.eval u γ := by
  induction t with
  | const a => rfl
  | outer k => rfl
  | index k hk => exact (hu k).collapseSum_eq
  | provIndex k hk => exact (hu k).collapseSum_eq
  | cmpAgg k hk op c ih => rfl
  | chiGate op t₁ t₂ ih₁ ih₂ => rfl
  | add t₁ t₂ ih₁ ih₂ => simp only [TermGIn.eval]; rw [ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => simp only [TermGIn.eval]; rw [ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => simp only [TermGIn.eval]; rw [ih₁, ih₂]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    simp only [TermGIn.eval]; rw [ih₁, ih₂, ih₃, ih₄]
  | coalesce t₁ t₂ ih₁ ih₂ => simp only [TermGIn.eval]; rw [ih₁, ih₂]

/-- The three-valued reading of a predicate is invariant on
pointwise-equivalent tuples. -/
theorem GenPredIn.eval3_equiv {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} {u' u : Tuple (GenValue T K) n}
    (hu : ∀ k, GenValue.Equiv (u' k) (u k)) :
    φ.eval3 u' γ = φ.eval3 u γ := by
  induction φ with
  | cmp op t₁ t₂ =>
    simp only [GenPredIn.eval3]
    rw [TermGIn.eval_equiv t₁ hu, TermGIn.eval_equiv t₂ hu]
  | aggCmp k hk op t =>
    simp only [GenPredIn.eval3]
    rw [(hu k).collapseSum_eq, TermGIn.eval_equiv t hu]
  | aggRange k hk op₁ t₁ op₂ t₂ =>
    simp only [GenPredIn.eval3]
    rw [(hu k).collapseSum_eq, TermGIn.eval_equiv t₁ hu,
      TermGIn.eval_equiv t₂ hu]
  | and φ ψ ihφ ihψ => simp only [GenPredIn.eval3, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [GenPredIn.eval3, ihφ, ihψ]
  | not φ ih => simp only [GenPredIn.eval3, ih]

/-- Truth of a predicate is invariant on pointwise-equivalent tuples. -/
theorem GenPredIn.holds_equiv {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} {u' u : Tuple (GenValue T K) n}
    (hu : ∀ k, GenValue.Equiv (u' k) (u k)) :
    φ.holds u' γ ↔ φ.holds u γ := by
  unfold GenPredIn.holds
  rw [GenPredIn.eval3_equiv φ hu]

/-- The predicate provenance is invariant on pointwise-equivalent tuples:
tokens are read only through their predicate provenance
(`AggValue.predProv_congr`) and their collapse. -/
theorem GenPredIn.predsem_equiv {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} (neg : Bool) {u' u : Tuple (GenValue T K) n}
    (hu : ∀ k, GenValue.Equiv (u' k) (u k)) :
    φ.predsem neg u' γ = φ.predsem neg u γ := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ =>
    simp only [GenPredIn.predsem]
    rw [TermGIn.eval_equiv t₁ hu, TermGIn.eval_equiv t₂ hu]
  | aggCmp k hk op t =>
    have hk' := hu k
    simp only [GenPredIn.predsem]
    cases hu'k : u' k with
    | inl w' =>
      cases huk : u k with
      | inl w => rfl
      | inr a =>
        rw [hu'k, huk] at hk'
        exact absurd hk' GenValue.Equiv.not_inl_inr
    | inr x' =>
      cases huk : u k with
      | inl w =>
        rw [hu'k, huk] at hk'
        exact absurd hk' GenValue.Equiv.not_inr_inl
      | inr x =>
        rw [hu'k, huk] at hk'
        rw [TermGIn.eval_equiv t hu]
        exact hk'.predProvOf_eq _ _
  | aggRange k hk op₁ t₁ op₂ t₂ =>
    have hk' := hu k
    simp only [GenPredIn.predsem]
    cases hu'k : u' k with
    | inl w' =>
      cases huk : u k with
      | inl w => rfl
      | inr a =>
        rw [hu'k, huk] at hk'
        exact absurd hk' GenValue.Equiv.not_inl_inr
    | inr x' =>
      cases huk : u k with
      | inl w =>
        rw [hu'k, huk] at hk'
        exact absurd hk' GenValue.Equiv.not_inr_inl
      | inr x =>
        rw [hu'k, huk] at hk'
        rw [TermGIn.eval_equiv t₁ hu, TermGIn.eval_equiv t₂ hu]
        exact hk'.predProvOfWith_eq _
  | and φ ψ ihφ ihψ =>
    simp only [GenPredIn.predsem]
    rw [ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.predsem]
    rw [ihφ, ihψ]
  | not φ ih => exact ih (!neg)

/-- **The joint reading of a predicate commutes with the pushforward**
on a row whose compared families are presented on both sides
(`FamPres`): the joint worlds correspond (`jointWorlds_of_famPres`), the
annotations pushed forward, and the predicate reads the same values
there, the terms reading the regular columns the simulation keeps. -/
theorem GenPredIn.predsemJ_hom_famPres (h : SemiringWithMonusHom K K') {c n : ℕ}
    {κ : Fin n → ColKind} (φ : GenPredIn T c κ) (neg : Bool) {γ : Fin c → T}
    {u' : Tuple (GenValue T K') n} {u : Tuple (GenValue T K) n}
    (hu : ∀ k, GenValue.Equiv (u' k) (AggValue.mapAnnSum ⇑h.toRingHom (u k)))
    (hF : FamPres h.toRingHom (fun p => ∃ k, u' k = Sum.inr p.1 ∧ u k = Sum.inr p.2)) :
    φ.predsemJ neg u' γ = h.toRingHom (φ.predsemJ neg u γ) := by
  have hterm : ∀ t : TermGIn T c κ, t.eval u' γ = t.eval u γ := fun t =>
    (TermGIn.eval_equiv t hu).trans (TermGIn.eval_mapAnnSum h t u)
  have hagg : ∀ k, (∃ x, u k = Sum.inr x) ↔ (∃ x', u' k = Sum.inr x') := by
    intro k
    have hk := hu k
    cases huk : u k with
    | inl w =>
      rw [huk] at hk
      cases hu'k : u' k with
      | inl w' => simp
      | inr x' => rw [hu'k] at hk; exact absurd hk GenValue.Equiv.not_inr_inl
    | inr x =>
      rw [huk] at hk
      cases hu'k : u' k with
      | inl w' => rw [hu'k] at hk; exact absurd hk GenValue.Equiv.not_inl_inr
      | inr x' => simp
  unfold GenPredIn.predsemJ
  rw [jointWorlds_of_famPres h.toRingHom u u' _ (fun k _ => hagg k)
    (hF.mono (fun p ⟨k, _, h1, h2⟩ => ⟨k, h1, h2⟩)), Multiset.map_map,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun w _ => ?_))
  simp only [Function.comp, GenPredIn.eval3W_congr_terms φ _ hterm]
  rw [map_mul, map_mul, SemiringWithMonusHom.map_sub, map_one]
  split_ifs <;> simp

/-- The row-wise simulation relation underlying the evaluator-level hom
commutation: regular columns equal, aggregate columns reading as the
pushed-forward base-side ones do, and the finalized annotation the image
of the base-side finalized annotation. -/
def GenRow.Sim (h : SemiringWithMonusHom K K') {n : ℕ}
    (r' : GenRow T K' n) (r : GenRow T K n) : Prop :=
  (∀ k, GenValue.Equiv (r'.fst k)
      (AggValue.mapAnnSum ⇑h.toRingHom (r.fst k)))
    ∧ r'.snd.finalize = h.toRingHom r.snd.finalize

omit [DecidableEq K] in
/-- Simulated rows finalize to pushed-forward annotated tuples. -/
theorem GenRow.Sim.toAnnotated_eq (h : SemiringWithMonusHom K K') {n : ℕ}
    {r' : GenRow T K' n} {r : GenRow T K n} (hs : GenRow.Sim h r' r) :
    GenRow.toAnnotated r'
      = SemiringWithMonusHom.mapAnnotatedTuple h (GenRow.toAnnotated r) := by
  refine Prod.ext ?_ hs.2
  funext k
  show AggValue.collapseSum (r'.fst k) = AggValue.collapseSum (r.fst k)
  rw [(hs.1 k).collapseSum_eq, AggValue.collapseSum_mapAnnSum]

omit [DecidableEq K] in
/-- **What a window reads of simulated rows corresponds**: it reads the
regular columns, which the simulation keeps, and nothing of the aggregate
ones – so the relation a window reads of one side is the pushed-forward
relation it reads of the other. -/
theorem GenRow.Sim.readAnnotated_eq (h : SemiringWithMonusHom K K') {n : ℕ}
    (κ : Fin n → ColKind) {r' : GenRow T K' n} {r : GenRow T K n}
    (hs : GenRow.Sim h r' r) :
    GenRow.readAnnotated κ r'
      = SemiringWithMonusHom.mapAnnotatedTuple h (GenRow.readAnnotated κ r) := by
  refine Prod.ext ?_ hs.2
  show ColKind.readTuple κ (GenRow.plainTuple r'.fst)
      = ColKind.readTuple κ (GenRow.plainTuple r.fst)
  exact congrArg (ColKind.readTuple κ)
    (congrArg Prod.fst (GenRow.Sim.toAnnotated_eq h hs))

end Simulation

/-! ## Per-side finalize identities

The three row transformations of the evaluator that rearrange the factored
annotation are finalize-equivalent *on each side separately*: cashing a
group factor moves `δ` between `pending` and `base` (projection), the
supersede drop is licensed exactly by the guard-absorption condition of
its filter (selection), and the product splits multiplicatively. -/

section FinalizeIdentities

variable {c n : ℕ} {κ : Fin n → ColKind}

/-- Cashing any sub-multiset of pending factors does not change the
finalized annotation. -/
theorem GenAnn.finalize_cash (b : K) (P kept : Multiset (List K))
    (hle : kept ≤ P) :
    GenAnn.finalize ⟨b * ((P - kept).map
        (fun l => SemiringWithMonus.delta l.sum)).prod, kept⟩
      = GenAnn.finalize ⟨b, P⟩ := by
  show b * _ * _ = b * _
  rw [mul_assoc, ← Multiset.prod_add, ← Multiset.map_add,
    tsub_add_cancel_of_le hle]

omit [DecidableEq K] in
/-- The product annotation finalizes to the product of the finalized
annotations. -/
theorem GenAnn.finalize_prod (b₁ b₂ : K) (P₁ P₂ : Multiset (List K)) :
    GenAnn.finalize ⟨b₁ * b₂, P₁ + P₂⟩
      = GenAnn.finalize ⟨b₁, P₁⟩ * GenAnn.finalize ⟨b₂, P₂⟩ := by
  show b₁ * b₂ * _ = b₁ * _ * (b₂ * _)
  rw [Multiset.map_add, Multiset.prod_add]
  rw [mul_mul_mul_comm]

end FinalizeIdentities

/-! ## Multiset relation plumbing -/

section RelPlumbing

variable {α β γ δ' : Type}

/-- Mapping a multiset with two functions related pointwise yields related
multisets. -/
theorem rel_map_of_forall {R : γ → δ' → Prop} {s : Multiset α}
    {f : α → γ} {g : α → δ'} (hfg : ∀ x ∈ s, R (f x) (g x)) :
    Multiset.Rel R (s.map f) (s.map g) :=
  Multiset.rel_map.mpr (Multiset.rel_refl_of_refl_on hfg)

/-- **Two indexed families whose occurrences correspond under a
bijection of indices are related occurrence by occurrence.** This is how
an operator indexed by its occurrence family is compared across a change
of annotation semiring, which re-sorts the indexing. -/
theorem rel_occFam_of_equiv {R : α → β → Prop} {N N' : ℕ}
    (f' : Fin N' → α) (f : Fin N → β) (e : Fin N ≃ Fin N')
    (hR : ∀ i, R (f' (e i)) (f i)) :
    Multiset.Rel R (OccFam.mk N' f').toMultiset (OccFam.mk N f).toMultiset := by
  rw [← OccFam.toMultiset_congr (r := OccFam.mk N (fun i => f' (e i)))
    (r' := OccFam.mk N' f') ⟨e, fun i => rfl⟩]
  exact rel_map_of_forall (fun i _ => hR i)

/-- Push a relation through maps of related multisets. -/
theorem rel_map_of_rel {R : α → β → Prop} {S : γ → δ' → Prop}
    {s : Multiset α} {t : Multiset β} {f : α → γ} {g : β → δ'}
    (hst : Multiset.Rel R s t) (hfg : ∀ x y, R x y → S (f x) (g y)) :
    Multiset.Rel S (s.map f) (t.map g) :=
  Multiset.rel_map.mpr (hst.mono (fun x _ y _ hxy => hfg x y hxy))

/-- Binding related multisets by pointwise-related functions preserves
the relation. -/
theorem rel_bind_of_rel {R : α → β → Prop} {S : γ → δ' → Prop}
    {s : Multiset α} {t : Multiset β}
    {f : α → Multiset γ} {g : β → Multiset δ'}
    (hst : Multiset.Rel R s t)
    (hfg : ∀ x y, R x y → Multiset.Rel S (f x) (g y)) :
    Multiset.Rel S (s.bind f) (t.bind g) := by
  induction hst with
  | zero => exact Multiset.Rel.zero
  | cons hab _ ih =>
    rw [Multiset.cons_bind, Multiset.cons_bind]
    exact Multiset.Rel.add (hfg _ _ hab) ih

/-- Related multisets mapped by pointwise-equal-on-related-pairs functions
are equal. -/
theorem map_eq_of_rel {R : α → β → Prop} {s : Multiset α} {t : Multiset β}
    {f : α → γ} {g : β → γ} (hst : Multiset.Rel R s t)
    (hfg : ∀ x y, R x y → f x = g y) :
    s.map f = t.map g :=
  Multiset.rel_eq.mp (rel_map_of_rel hst hfg)

/-- Filtering related multisets by predicates that agree on related pairs
preserves the relation. -/
theorem rel_filter_of_iff {R : α → β → Prop} {s : Multiset α}
    {t : Multiset β} {p : α → Prop} {q : β → Prop} [DecidablePred p]
    [DecidablePred q] (hst : Multiset.Rel R s t)
    (hpq : ∀ x y, R x y → (p x ↔ q y)) :
    Multiset.Rel R (s.filter p) (t.filter q) := by
  induction hst with
  | zero =>
    rw [Multiset.filter_zero, Multiset.filter_zero]
    exact Multiset.Rel.zero
  | @cons a b s t hab hst ih =>
    rw [Multiset.filter_cons, Multiset.filter_cons]
    by_cases hpa : p a
    · rw [ite_eq_left hpa, ite_eq_left ((hpq a b hab).mp hpa)]
      exact Multiset.Rel.add (Multiset.Rel.cons hab Multiset.Rel.zero) ih
    · rw [ite_eq_right hpa, ite_eq_right (fun hqb => hpa ((hpq a b hab).mpr hqb)),
        zero_add, zero_add]
      exact ih

/-- **Two nested values whose occurrences correspond read alike.** The
annotations agree, so the data at each occurrence agree
(`NestedValue.occStats_eq`), and what a nested value reads is a function
of those where `K` is complemented
(`NestedValue.predProvWith_congr_of_occStats`). The collapses agree
because they are the occurrences' own. -/
theorem GenValue.Equiv.of_nest_rel (hc : complemented K)
    {a' a : NestedValue T K} (hagg : a'.agg = a.agg)
    (hsc : a'.scalar = a.scalar)
    (h : Multiset.Rel (fun o' o : AggExpr T K × K =>
      o'.snd = o.snd ∧ o'.fst.worldStats = o.fst.worldStats
        ∧ o'.fst.collapse = o.fst.collapse) a'.occs a.occs) :
    GenValue.Equiv (Sum.inr (AggTok.nest a') : GenValue T K)
      (Sum.inr (AggTok.nest a)) := by
  have hst : a'.occs.map NestedValue.occStats
      = a.occs.map NestedValue.occStats :=
    map_eq_of_rel h (fun o' o ho => by
      rw [NestedValue.occStats_eq, NestedValue.occStats_eq, ho.1, ho.2.1])
  have hcol : a'.collapse = a.collapse := by
    show a'.agg _ = a.agg _
    rw [hagg]
    exact congrArg a.agg (map_eq_of_rel h (fun o' o ho => ho.2.2))
  exact ⟨hcol, hsc,
    NestedValue.vals_congr_of_occStats hagg hsc hst,
    fun P => NestedValue.predProvWith_congr_of_occStats hc hagg hsc hst P⟩

/-- Products of related multisets are related pairwise. -/
theorem rel_bind {R : α → β → Prop} {S : γ → δ' → Prop}
    {s : Multiset α} {t : Multiset β} {F : α → Multiset γ}
    {G : β → Multiset δ'} (hst : Multiset.Rel R s t)
    (hFG : ∀ a b, R a b → Multiset.Rel S (F a) (G b)) :
    Multiset.Rel S (s.bind F) (t.bind G) := by
  induction hst with
  | zero =>
    rw [Multiset.zero_bind, Multiset.zero_bind]
    exact Multiset.Rel.zero
  | @cons a b s t hab hst ih =>
    rw [Multiset.cons_bind, Multiset.cons_bind]
    exact Multiset.Rel.add (hFG a b hab) ih

theorem rel_product {R : α → β → Prop} {S : γ → δ'  → Prop}
    {s : Multiset α} {t : Multiset β} {s' : Multiset γ} {t' : Multiset δ'}
    (hst : Multiset.Rel R s t) (hst' : Multiset.Rel S s' t') :
    Multiset.Rel (fun (x : α × γ) (y : β × δ') => R x.1 y.1 ∧ S x.2 y.2)
      (s.product s') (t.product t') := by
  induction hst with
  | zero =>
    show Multiset.Rel _ (Multiset.bind 0 _) (Multiset.bind 0 _)
    rw [Multiset.zero_bind, Multiset.zero_bind]
    exact Multiset.Rel.zero
  | @cons a b s t hab hst ih =>
    show Multiset.Rel _ (Multiset.bind (a ::ₘ s) _) (Multiset.bind (b ::ₘ t) _)
    rw [Multiset.cons_bind, Multiset.cons_bind]
    exact Multiset.Rel.add
      (rel_map_of_rel hst' (fun x y hxy => ⟨hab, hxy⟩)) ih

end RelPlumbing

/-! ## The evaluator-level commutation

The query syntax mentions no annotation values, so the same query
evaluates over any annotation semiring; the database argument determines
it. The main theorem relates the evaluation on the pushed-forward
database to the base-side evaluation, row by row, through `GenRow.Sim`;
finalizing both sides then yields the hypothesis-free hom commutation of
`evaluateAnnotated`. -/

section EvaluatorHom

variable [HasAltLinearOrder K] [HasAltLinearOrder K']

omit [DecidableEq K] in
/-- **A token read over the frame's distinct values is carried by the
pushforward too**: the merge commutes with it, and is blind to the
tie-block permutation the two unmerged tokens differ by. -/
theorem tokenOfDist_mapAnn_equiv (h : SemiringWithMonusHom K K')
    {n' m' p' : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') (w : ValueFrame T p') {c : ℕ} (t : TermIn T c n')
    (γ : Fin c → T) (f : SeqAggFunc T) (dist : Bool)
    (X : Multiset (AnnotatedTuple T K n')) {x : AnnotatedTuple T K n'}
    (hx : x ∈ X) :
    GenValue.Equiv
      (Sum.inr (AggTok.tok (ValueFrame.tokenOfDist P O o w t f dist
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
        ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ)))
      (Sum.inr (AggTok.tok ((ValueFrame.tokenOfDist P O o w t f dist X x γ).mapAnn
        ⇑h.toRingHom))) := by
  have hagg : (ValueFrame.tokenOf P O o w t f
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
        ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ).agg
      = ((ValueFrame.tokenOf P O o w t f X x γ).mapAnn ⇑h.toRingHom).agg := by
    rw [ValueFrame.tokenOf_agg]
    exact (ValueFrame.tokenOf_agg P O o w t f X x).symm
  have hsc : (ValueFrame.tokenOf P O o w t f
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
        ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ).scalar
      = ((ValueFrame.tokenOf P O o w t f X x γ).mapAnn ⇑h.toRingHom).scalar := by
    show _ = (ValueFrame.tokenOf P O o w t f X x γ).scalar
    rw [ValueFrame.tokenOf_scalar, ValueFrame.tokenOf_scalar]
  have htie := TiePerm.symm (fun e => e.symm)
    (tokenOf_mapAnn_tiePerm h P O o w t (γ := γ) f X hx)
  unfold ValueFrame.tokenOfDist
  cases dist
  · exact ⟨hagg, hsc, htie⟩
  · simp only [ite_true]
    rw [AggValue.mergeByValue_congr hagg hsc
        ((ValueFrame.tokenOf_fam ..).trans (ValueFrame.tokenOf_fam P O o w t f X x γ).symm) htie,
      AggValue.mergeByValue_map (map_zero h.toRingHom)
        (fun x y => map_add h.toRingHom x y)]
    exact ⟨rfl, rfl, TiePerm.refl _ _⟩

omit [DecidableEq K] [DecidableEq K'] [HasAltLinearOrder K]
  [HasAltLinearOrder K'] in
/-- The three-valued reading is invariant under the pushforward of the
tuple. -/
theorem GenPredIn.eval3_mapAnnSum {c n : ℕ} {κ : Fin n → ColKind}
    (h : SemiringWithMonusHom K K') (φ : GenPredIn T c κ) {γ : Fin c → T}
    (u : Tuple (GenValue T K) n) :
    φ.eval3 (fun k => AggValue.mapAnnSum ⇑h.toRingHom (u k)) γ = φ.eval3 u γ := by
  induction φ with
  | cmp op t₁ t₂ =>
    simp only [GenPredIn.eval3]
    rw [TermGIn.eval_mapAnnSum h t₁ u, TermGIn.eval_mapAnnSum h t₂ u]
  | aggCmp k hk op t =>
    simp only [GenPredIn.eval3]
    rw [AggValue.collapseSum_mapAnnSum, TermGIn.eval_mapAnnSum h t u]
  | aggRange k hk op₁ t₁ op₂ t₂ =>
    simp only [GenPredIn.eval3]
    rw [AggValue.collapseSum_mapAnnSum, TermGIn.eval_mapAnnSum h t₁ u,
      TermGIn.eval_mapAnnSum h t₂ u]
  | and φ ψ ihφ ihψ => simp only [GenPredIn.eval3, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [GenPredIn.eval3, ihφ, ihψ]
  | not φ ih => simp only [GenPredIn.eval3, ih]

omit [DecidableEq K] [DecidableEq K'] [HasAltLinearOrder K]
  [HasAltLinearOrder K'] in
/-- Truth is invariant under the pushforward of the tuple. -/
theorem GenPredIn.holds_mapAnnSum {c n : ℕ} {κ : Fin n → ColKind}
    (h : SemiringWithMonusHom K K') (φ : GenPredIn T c κ) {γ : Fin c → T}
    (u : Tuple (GenValue T K) n) :
    φ.holds (fun k => AggValue.mapAnnSum ⇑h.toRingHom (u k)) γ
      ↔ φ.holds u γ := by
  unfold GenPredIn.holds
  rw [GenPredIn.eval3_mapAnnSum h φ u]

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- Embedded pushed-forward annotated tuples simulate the embedded
base-side tuples. -/
theorem GenRow.sim_ofAnnotated (h : SemiringWithMonusHom K K') {n : ℕ}
    (p : AnnotatedTuple T K n) :
    GenRow.Sim h
      (GenRow.ofAnnotated (SemiringWithMonusHom.mapAnnotatedTuple h p))
      (GenRow.ofAnnotated p) := by
  refine ⟨fun k => rfl, ?_⟩
  show GenAnn.finalize ⟨(SemiringWithMonusHom.mapAnnotatedTuple h p).snd, 0⟩
    = h.toRingHom (GenAnn.finalize ⟨p.snd, 0⟩)
  rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero]
  rfl

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- Embedding a pushed-forward annotated relation yields rows simulating
the embedded base-side rows. -/
theorem rel_ofAnnotated_map (h : SemiringWithMonusHom K K') {n : ℕ}
    (X : AnnotatedRelation T K n) :
    Multiset.Rel (GenRow.Sim h)
      ((SemiringWithMonusHom.mapAnnotatedRelation h X).map GenRow.ofAnnotated)
      (X.map GenRow.ofAnnotated) := by
  unfold SemiringWithMonusHom.mapAnnotatedRelation
  rw [Multiset.map_map]
  exact rel_map_of_forall (fun p _ => GenRow.sim_ofAnnotated h p)

omit [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- `groupByKey` commutes with the annotation pushforward: keys are
data-only and group values are annotation sums. -/
theorem groupByKey_mapAnnotatedRelation (h : SemiringWithMonusHom K K')
    {n : ℕ} (X : AnnotatedRelation T K n) :
    (Multiset.ofList
        (groupByKey (SemiringWithMonusHom.mapAnnotatedRelation h X)).val
      : Multiset (AnnotatedTuple T K' n))
      = SemiringWithMonusHom.mapAnnotatedRelation h
          (Multiset.ofList (groupByKey X).val) := by
  rw [groupByKey_multiset_eq, groupByKey_multiset_eq,
    SemiringWithMonusHom.map_fst_mapAnnotatedRelation]
  unfold SemiringWithMonusHom.mapAnnotatedRelation
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun v _ => ?_)
  refine Prod.ext rfl ?_
  exact SemiringWithMonusHom.sum_filter_map_snd_mapAnnotatedRelation h v X

omit [ValueType T] [DecidableEq K] [DecidableEq K']
  [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- The annotation pushforward is additive on relations. -/
theorem mapAnnotatedRelation_add (h : SemiringWithMonusHom K K') {n : ℕ}
    (x y : AnnotatedRelation T K n) :
    SemiringWithMonusHom.mapAnnotatedRelation h (x + y)
      = SemiringWithMonusHom.mapAnnotatedRelation h x
        + SemiringWithMonusHom.mapAnnotatedRelation h y :=
  Multiset.map_add _ x y

omit [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- The annotation pushforward commutes with duplicate elimination – the
rounds of `MuSet` read through it. -/
theorem dedupAnn_mapAnnotatedRelation (h : SemiringWithMonusHom K K') {n : ℕ}
    (X : AnnotatedRelation T K n) :
    SemiringWithMonusHom.mapAnnotatedRelation h (AnnotatedRelation.dedupAnn X)
      = AnnotatedRelation.dedupAnn
          (SemiringWithMonusHom.mapAnnotatedRelation h X) :=
  (groupByKey_mapAnnotatedRelation h X).symm

omit [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- **Reading an aggregate column as a key commutes with a
homomorphism**: the values the column takes are untouched by the
pushforward and by tie-block equivalence, so the two occurrences have
the same alternatives, and each pair of them is again simulated. -/
theorem sim_alternativesAt (h : SemiringWithMonusHom K K') {n : ℕ}
    {r' : GenRow T K' n} {r : GenRow T K n} (hs : GenRow.Sim h r' r)
    (k : Fin n) :
    Multiset.Rel (GenRow.Sim h) (r'.alternativesAt k) (r.alternativesAt k) := by
  have hk := hs.1 k
  cases hrk : r.fst k with
  | inl w =>
    rw [hrk] at hk
    cases hr'k : r'.fst k with
    | inl w' =>
      rw [hr'k] at hk
      simp only [GenRow.alternativesAt, hrk, hr'k]
      exact Multiset.Rel.cons hs Multiset.Rel.zero
    | inr a' => rw [hr'k] at hk; exact absurd hk GenValue.Equiv.not_inr_inl
  | inr x =>
    rw [hrk] at hk
    cases hr'k : r'.fst k with
    | inl w' => rw [hr'k] at hk; exact absurd hk GenValue.Equiv.not_inl_inr
    | inr x' =>
      rw [hr'k] at hk
      have hvals : x'.vals = x.vals := by
        rw [hk.vals_eq]
        exact AggTok.vals_mapAnn _ x
      have hprov : ∀ v : T, x'.altProv v = h.toRingHom (x.altProv v) := by
        intro v
        rw [hk.altProv_eq, AggTok.altProv_mapAnn h x]
      simp only [GenRow.alternativesAt, hrk, hr'k, hvals]
      refine rel_map_of_forall (fun v _ => ⟨fun j => ?_, ?_⟩)
      · by_cases hj : j = k
        · subst hj
          show GenValue.Equiv (Function.update r'.fst j (Sum.inl v) j)
            (AggValue.mapAnnSum _ (Function.update r.fst j (Sum.inl v) j))
          rw [Function.update_self, Function.update_self]
          rfl
        · show GenValue.Equiv (Function.update r'.fst k (Sum.inl v) j)
            (AggValue.mapAnnSum _ (Function.update r.fst k (Sum.inl v) j))
          rw [Function.update_of_ne hj, Function.update_of_ne hj]
          exact hs.1 j
      · show GenAnn.finalize ⟨r'.snd.base * x'.altProv v, r'.snd.pending⟩
          = h.toRingHom (GenAnn.finalize ⟨r.snd.base * x.altProv v, r.snd.pending⟩)
        show (r'.snd.base * x'.altProv v) * _
          = h.toRingHom ((r.snd.base * x.altProv v) * _)
        rw [mul_right_comm, mul_right_comm (r.snd.base), map_mul, hprov v]
        exact congrArg (fun y => y * h.toRingHom (x.altProv v)) hs.2

omit [DecidableEq K] in
/-- **The expression a multi-frame window builds is carried by the
pushforward too.** Each side lists the shared family by its own sorted
order, and the pushforward only permutes that order inside blocks of
equal rows. Under `ContainsSelf` a leaf's flag is its frame's test on
the tuple and not a test on the index (`ValueFrame.occs_exprOf`), so the
two families differ by a tie-block permutation and every reading of the
column survives it. -/
theorem exprOf_mapAnn_equiv (h : SemiringWithMonusHom K K')
    {n' m' p' qq : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') {ws : Fin qq → ValueFrame T p'}
    (hcs : ∀ l, (ws l).ContainsSelf) {c : ℕ} (ts : Fin qq → TermIn T c n')
    (fs : Fin qq → SeqAggFunc T) (g : (Fin qq → T) → T) (γ : Fin c → T)
    {r' : OccFam (AnnotatedTuple T K' n')} {r : OccFam (AnnotatedTuple T K n')}
    {i' : Fin r'.size} {i : Fin r.size}
    (hi : (r'.row i').fst = (r.row i).fst)
    (hX : r'.toMultiset = Multiset.map (fun y : AnnotatedTuple T K n' =>
        ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' n')) r.toMultiset) :
    GenValue.Equiv
      (Sum.inr (AggTok.expr (ValueFrame.exprOf P O o ws ts fs g r' i' γ))
        : GenValue T K')
      (Sum.inr (AggTok.expr
        ((ValueFrame.exprOf P O o ws ts fs g r i γ).mapAnn ⇑h.toRingHom))) := by
  have hcu : (ValueFrame.unionFrame ws).ContainsSelf :=
    ValueFrame.containsSelf_unionFrame hcs
  set gh : AnnotatedTuple T K n' → AnnotatedTuple T K' n' :=
    fun y => ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' n') with hghdef
  set Lb : List (AnnotatedTuple T K n') :=
    (ValueFrame.exprIdx (α := AnnotatedTuple T K n') Prod.fst P O o ws r i).map
      r.row with hLb
  set L' : List (AnnotatedTuple T K' n') :=
    (ValueFrame.exprIdx (α := AnnotatedTuple T K' n') Prod.fst P O o ws r' i').map
      r'.row with hL'
  -- the two orderings hold the same rows
  have hperm : L'.Perm (Lb.map gh) := by
    refine Multiset.coe_eq_coe.mp ?_
    rw [← Multiset.map_coe gh Lb, hL', hLb, ← Multiset.map_coe r'.row,
      ← Multiset.map_coe r.row,
      ValueFrame.exprIdx_rows_coe (α := AnnotatedTuple T K' n')
        Prod.fst P O o ws r' i',
      ValueFrame.exprIdx_rows_coe (α := AnnotatedTuple T K n')
        Prod.fst P O o ws r i,
      ← ValueFrame.frameOf_map (α := AnnotatedTuple T K n')
        (β := AnnotatedTuple T K' n') (valα := Prod.fst) (valβ := Prod.fst) gh
        (fun _ => rfl) P O (ValueFrame.unionFrame ws) r.toMultiset
        (OccFam.row_mem_toMultiset r i),
      ← hX]
    exact ValueFrame.frameOf_congr_val (α := AnnotatedTuple T K' n')
      Prod.fst P O hcu r'.toMultiset
      (OccFam.row_mem_toMultiset r' i')
      (hX ▸ Multiset.mem_map_of_mem gh (OccFam.row_mem_toMultiset r i)) hi
  -- and each is sorted by the clause's order
  have hs' : L'.Pairwise (fun x y =>
      OrderSpec.readLe (Tuple.key O) Prod.fst o x y = true) :=
    ValueFrame.exprIdx_rows_pairwise (α := AnnotatedTuple T K' n')
      Prod.fst P O o ws r' i'
  have hs : (Lb.map gh).Pairwise (fun x y =>
      OrderSpec.readLe (Tuple.key O) Prod.fst o x y = true) := by
    rw [List.pairwise_map]
    exact (ValueFrame.exprIdx_rows_pairwise (α := AnnotatedTuple T K n')
      Prod.fst P O o ws r i).imp (fun hab => hab)
  have htp : TiePerm (fun a b : AnnotatedTuple T K' n' => a.fst = b.fst)
      L' (Lb.map gh) :=
    tiePerm_of_perm_of_sorted_by _ Prod.fst
      (fun hxy hyx => OrderSpec.val_eq_of_readLe hxy hyx)
      (fun hv => OrderSpec.readLe_of_val_eq hv) hperm hs' hs
  -- both families are the same reading of their rows
  have hocc' : (ValueFrame.exprOf P O o ws ts fs g r' i' γ).occs
      = L'.map (fun y : AnnotatedTuple T K' n' =>
        ((fun l => (ts l).eval y.fst γ), y.snd,
          (fun l => decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
            && (ws l).ρ (Tuple.key O y.fst)
              (Tuple.key O (r.row i).fst)),
          fun _ => true)) := by
    rw [ValueFrame.occs_exprOf P O o hcs ts fs g r' i' γ, hi]
  have hoccb : ((ValueFrame.exprOf P O o ws ts fs g r i γ).mapAnn
        ⇑h.toRingHom).occs
      = (Lb.map gh).map (fun y : AnnotatedTuple T K' n' =>
        ((fun l => (ts l).eval y.fst γ), y.snd,
          (fun l => decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
            && (ws l).ρ (Tuple.key O y.fst)
              (Tuple.key O (r.row i).fst)),
          fun _ => true)) := by
    show ((ValueFrame.exprOf P O o ws ts fs g r i γ).occs.map
        (fun z => (z.fst, h.toRingHom z.snd.fst, z.snd.snd))) = _
    rw [ValueFrame.occs_exprOf P O o hcs ts fs g r i γ, hLb]
    simp only [List.map_map]
    rfl
  rw [AggExpr.eq_mk_of_occs hocc', AggExpr.eq_mk_of_occs hoccb]
  refine GenValue.Equiv.of_expr_tiePerm (q := qq) fs ?_ g
    (htp.map _ (fun hab => ⟨by rw [hab], by rw [hab]⟩))
  funext l
  show (!(ws l).s (Tuple.key O (r'.row i').fst))
    = (!(ws l).s (Tuple.key O (r.row i).fst))
  rw [hi]

omit [DecidableEq K] in
/-- **The same under `FILTER` clauses.** Each side lists the shared family by its own sorted
order, and the pushforward only permutes that order inside blocks of
equal rows. Under `ContainsSelf` a leaf's flag is its frame's test on
the tuple and not a test on the index (`ValueFrame.occs_exprOf`), so the
two families differ by a tie-block permutation and every reading of the
column survives it. -/
theorem exprOfWhen_mapAnn_equiv (h : SemiringWithMonusHom K K')
    {n' m' p' qq : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') {ws : Fin qq → ValueFrame T p'}
    (hcs : ∀ l, (ws l).ContainsSelf) {c : ℕ} (ts : Fin qq → TermIn T c n')
    (fs : Fin qq → SeqAggFunc T) (g : (Fin qq → T) → T)
    (keeps : Fin qq → Option (Selection T n')) (γ : Fin c → T)
    {r' : OccFam (AnnotatedTuple T K' n')} {r : OccFam (AnnotatedTuple T K n')}
    {i' : Fin r'.size} {i : Fin r.size}
    (hi : (r'.row i').fst = (r.row i).fst)
    (hX : r'.toMultiset = Multiset.map (fun y : AnnotatedTuple T K n' =>
        ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' n')) r.toMultiset) :
    GenValue.Equiv
      (Sum.inr (AggTok.expr (ValueFrame.exprOfWhen P O o ws ts fs g keeps r' i' γ))
        : GenValue T K')
      (Sum.inr (AggTok.expr
        ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).mapAnn ⇑h.toRingHom))) := by
  have hcu : (ValueFrame.unionFrame ws).ContainsSelf :=
    ValueFrame.containsSelf_unionFrame hcs
  set gh : AnnotatedTuple T K n' → AnnotatedTuple T K' n' :=
    fun y => ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' n') with hghdef
  set Lb : List (AnnotatedTuple T K n') :=
    (ValueFrame.exprIdx (α := AnnotatedTuple T K n') Prod.fst P O o ws r i).map
      r.row with hLb
  set L' : List (AnnotatedTuple T K' n') :=
    (ValueFrame.exprIdx (α := AnnotatedTuple T K' n') Prod.fst P O o ws r' i').map
      r'.row with hL'
  -- the two orderings hold the same rows
  have hperm : L'.Perm (Lb.map gh) := by
    refine Multiset.coe_eq_coe.mp ?_
    rw [← Multiset.map_coe gh Lb, hL', hLb, ← Multiset.map_coe r'.row,
      ← Multiset.map_coe r.row,
      ValueFrame.exprIdx_rows_coe (α := AnnotatedTuple T K' n')
        Prod.fst P O o ws r' i',
      ValueFrame.exprIdx_rows_coe (α := AnnotatedTuple T K n')
        Prod.fst P O o ws r i,
      ← ValueFrame.frameOf_map (α := AnnotatedTuple T K n')
        (β := AnnotatedTuple T K' n') (valα := Prod.fst) (valβ := Prod.fst) gh
        (fun _ => rfl) P O (ValueFrame.unionFrame ws) r.toMultiset
        (OccFam.row_mem_toMultiset r i),
      ← hX]
    exact ValueFrame.frameOf_congr_val (α := AnnotatedTuple T K' n')
      Prod.fst P O hcu r'.toMultiset
      (OccFam.row_mem_toMultiset r' i')
      (hX ▸ Multiset.mem_map_of_mem gh (OccFam.row_mem_toMultiset r i)) hi
  -- and each is sorted by the clause's order
  have hs' : L'.Pairwise (fun x y =>
      OrderSpec.readLe (Tuple.key O) Prod.fst o x y = true) :=
    ValueFrame.exprIdx_rows_pairwise (α := AnnotatedTuple T K' n')
      Prod.fst P O o ws r' i'
  have hs : (Lb.map gh).Pairwise (fun x y =>
      OrderSpec.readLe (Tuple.key O) Prod.fst o x y = true) := by
    rw [List.pairwise_map]
    exact (ValueFrame.exprIdx_rows_pairwise (α := AnnotatedTuple T K n')
      Prod.fst P O o ws r i).imp (fun hab => hab)
  have htp : TiePerm (fun a b : AnnotatedTuple T K' n' => a.fst = b.fst)
      L' (Lb.map gh) :=
    tiePerm_of_perm_of_sorted_by _ Prod.fst
      (fun hxy hyx => OrderSpec.val_eq_of_readLe hxy hyx)
      (fun hv => OrderSpec.readLe_of_val_eq hv) hperm hs' hs
  -- both families are the same reading of their rows
  have hocc' : (ValueFrame.exprOfWhen P O o ws ts fs g keeps r' i' γ).occs
      = L'.map (fun y : AnnotatedTuple T K' n' =>
        ((fun l => (ts l).eval y.fst γ), y.snd,
          (fun l => decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
            && (ws l).ρ (Tuple.key O y.fst)
              (Tuple.key O (r.row i).fst)),
          fun l => match keeps l with
            | none => true
            | some φ => φ.keeps y.fst)) := by
    rw [ValueFrame.occs_exprOfWhen P O o hcs ts fs g keeps r' i' γ, hi, hL']
    rfl
  have hoccb : ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).mapAnn
        ⇑h.toRingHom).occs
      = (Lb.map gh).map (fun y : AnnotatedTuple T K' n' =>
        ((fun l => (ts l).eval y.fst γ), y.snd,
          (fun l => decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
            && (ws l).ρ (Tuple.key O y.fst)
              (Tuple.key O (r.row i).fst)),
          fun l => match keeps l with
            | none => true
            | some φ => φ.keeps y.fst)) := by
    show ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).occs.map
        (fun z => (z.fst, h.toRingHom z.snd.fst, z.snd.snd))) = _
    rw [ValueFrame.occs_exprOfWhen P O o hcs ts fs g keeps r i γ, hLb]
    simp only [List.map_map]
    rfl
  rw [AggExpr.eq_mk_of_occs hocc', AggExpr.eq_mk_of_occs hoccb]
  refine GenValue.Equiv.of_expr_tiePerm (q := qq) fs ?_ g
    (htp.map _ (fun hab => ⟨by rw [hab], by rw [hab]⟩))
  funext l
  show (!(ws l).s (Tuple.key O (r'.row i').fst))
    = (!(ws l).s (Tuple.key O (r.row i).fst))
  rw [hi]

omit [DecidableEq K] in
/-- **The same at the level of the expression a filtered aggregate
builds.** There the family is the whole group on both sides, the clause
living in the occurrence's own flags, so the tie-block permutation of
the groups carries straight over – and the two columns are equivalent,
since the clause and the value both read the tuple part a tie-block
permutation does not move. -/
theorem exprGroupWhen_mapAnn_equiv (h : SemiringWithMonusHom K K')
    (f : SeqAggFunc T) {c : ℕ} (t : TermIn T c m) {γ : Fin c → T}
    (keep : Tuple T m → Bool) (is : Tuple (Fin m) n₁)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    GenValue.Equiv
      (Sum.inr (AggTok.expr (AggExpr.ofGroupWhen f t keep
        (Having.havingGroup is
          (r.map (fun p =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g) γ))
        : GenValue T K')
      (Sum.inr (AggTok.expr ((AggExpr.ofGroupWhen f t keep
        (Having.havingGroup is r g) γ).mapAnn ⇑h.toRingHom))) := by
  set U : List (AnnotatedTuple T K m) := Having.havingGroup is r g with hU
  set U' : List (AnnotatedTuple T K' m) :=
    Having.havingGroup is
      (r.map (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g
    with hU'
  set occOf : AnnotatedTuple T K' m →
      (Fin 1 → T) × K' × (Fin 1 → Bool) × (Fin 1 → Bool) :=
    fun p => ((fun _ : Fin 1 => t.eval p.fst γ), p.snd,
      (fun _ : Fin 1 => true), (fun _ : Fin 1 => keep p.fst)) with hoccOf
  -- both families are the same reading of their rows
  have hocc' : (AggExpr.ofGroupWhen f t keep U' γ).occs = U'.map occOf := rfl
  have hoccb : ((AggExpr.ofGroupWhen f t keep U γ).mapAnn ⇑h.toRingHom).occs
      = (U.map (fun p =>
          ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))).map occOf := by
    show ((AggExpr.ofGroupWhen f t keep U γ).occs.map
        (fun z => (z.fst, h.toRingHom z.snd.fst, z.snd.snd))) = _
    rw [AggExpr.occs_ofGroupWhen]
    simp only [List.map_map]
    rfl
  rw [AggExpr.eq_mk_of_occs hocc', AggExpr.eq_mk_of_occs hoccb]
  refine GenValue.Equiv.of_expr_tiePerm (q := 1) _ rfl _ ?_
  refine TiePerm.symm (fun e => ⟨e.1.symm, e.2.symm⟩) ?_
  exact (havingGroup_tiePerm h is r g).map
    (eqv' := fun z z' : (Fin 1 → T) × K' × (Fin 1 → Bool) × (Fin 1 → Bool) =>
      z.fst = z'.fst ∧ z.snd.snd = z'.snd.snd)
    occOf
    (fun hpq => ⟨funext (fun _ => congrArg (fun z => t.eval z γ) hpq),
      by rw [hoccOf]; dsimp only; rw [hpq]⟩)

omit [DecidableEq K] in
/-- The same for an aggregation that reads its group in a clause's
order: the two readings are tie-permuted (`havingGroupOrd_tiePerm`), and
an expression's readings are blind to that. -/
theorem exprGroupWhenOrd_mapAnn_equiv (h : SemiringWithMonusHom K K')
    (f : SeqAggFunc T) {c : ℕ} (t : TermIn T c m) {γ : Fin c → T}
    (keep : Tuple T m → Bool) (is : Tuple (Fin m) n₁)
    (ord : GroupOrder T m) (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    GenValue.Equiv
      (Sum.inr (AggTok.expr (AggExpr.ofGroupWhen f t keep
        (Having.havingGroupOrd is ord
          (r.map (fun p =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g) γ))
        : GenValue T K')
      (Sum.inr (AggTok.expr ((AggExpr.ofGroupWhen f t keep
        (Having.havingGroupOrd is ord r g) γ).mapAnn ⇑h.toRingHom))) := by
  set U : List (AnnotatedTuple T K m) := Having.havingGroupOrd is ord r g
    with hU
  set U' : List (AnnotatedTuple T K' m) :=
    Having.havingGroupOrd is ord
      (r.map (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g
    with hU'
  set occOf : AnnotatedTuple T K' m →
      (Fin 1 → T) × K' × (Fin 1 → Bool) × (Fin 1 → Bool) :=
    fun p => ((fun _ : Fin 1 => t.eval p.fst γ), p.snd,
      (fun _ : Fin 1 => true), (fun _ : Fin 1 => keep p.fst)) with hoccOf
  have hocc' : (AggExpr.ofGroupWhen f t keep U' γ).occs = U'.map occOf := rfl
  have hoccb : ((AggExpr.ofGroupWhen f t keep U γ).mapAnn ⇑h.toRingHom).occs
      = (U.map (fun p =>
          ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))).map occOf := by
    show ((AggExpr.ofGroupWhen f t keep U γ).occs.map
        (fun z => (z.fst, h.toRingHom z.snd.fst, z.snd.snd))) = _
    rw [AggExpr.occs_ofGroupWhen]
    simp only [List.map_map]
    rfl
  rw [AggExpr.eq_mk_of_occs hocc', AggExpr.eq_mk_of_occs hoccb]
  refine GenValue.Equiv.of_expr_tiePerm (q := 1) _ rfl _ ?_
  refine TiePerm.symm (fun e => ⟨e.1.symm, e.2.symm⟩) ?_
  exact (havingGroupOrd_tiePerm h is ord r g).map
    (eqv' := fun z z' : (Fin 1 → T) × K' × (Fin 1 → Bool) × (Fin 1 → Bool) =>
      z.fst = z'.fst ∧ z.snd.snd = z'.snd.snd)
    occOf
    (fun hpq => ⟨funext (fun _ => congrArg (fun z => t.eval z γ) hpq),
      by rw [hoccOf]; dsimp only; rw [hpq]⟩)

omit [DecidableEq K] in
/-- **The column a filtered window builds is carried by the
pushforward.** The frame is the same rows up to a tie-block permutation
(`frameListOf_mapAnn_tiePerm`), the clause and the classes read the
values, and the family is built from the rows – so the two columns differ
by a tie-block permutation of their families, which every reading of an
expression is blind to. -/
theorem exprWhenOf_mapAnn_equiv (h : SemiringWithMonusHom K K')
    {n' m' p' : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') (w : ValueFrame T p') {c : ℕ} (t : TermIn T c n')
    (γ : Fin c → T) (f : SeqAggFunc T) (dist : Bool)
    (keep : Tuple T n' → Bool) (X : Multiset (AnnotatedTuple T K n'))
    {x : AnnotatedTuple T K n'} (hx : x ∈ X) :
    GenValue.Equiv
      (Sum.inr (AggTok.expr (ValueFrame.exprWhenOf P O o w t f dist keep
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
        ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ))
        : GenValue T K')
      (Sum.inr (AggTok.expr
        ((ValueFrame.exprWhenOf P O o w t f dist keep X x γ).mapAnn
          ⇑h.toRingHom))) := by
  have htie := frameListOf_mapAnn_tiePerm h P O o w X hx
  unfold ValueFrame.exprWhenOf
  cases dist
  · simp only [Bool.false_eq_true, ite_false]
    rw [AggExpr.ofSeqWhen_mapAnn]
    refine GenValue.Equiv.of_expr_tiePerm (q := 1) _ rfl _ ?_
    exact TiePerm.symm (fun e => ⟨e.1.symm, e.2.symm⟩)
      (AggExpr.ofSeqWhen_tiePerm_occs f t keep
        (!w.s (Tuple.key O x.fst)) γ htie)
  · simp only [ite_true]
    rw [AggExpr.ofSeqDistWhen_mapAnn _ _ _ _ _ _ (map_zero h.toRingHom)
      (fun a b => map_add h.toRingHom a b)]
    refine GenValue.Equiv.of_expr_tiePerm (q := 1) _ rfl _ ?_
    exact TiePerm.symm (fun e => ⟨e.1.symm, e.2.symm⟩)
      (AggExpr.ofSeqDistWhen_tiePerm_occs f t keep
        (!w.s (Tuple.key O x.fst)) γ htie)

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- **A projection column reads simulated rows alike**: a term reads the
regular values the simulation keeps, a token column is carried as it is,
and a term over an aggregate column moves the function and leaves the
family (`GenValue.Equiv.postcomp`). -/
theorem ProjColIn.equiv_eval_of_sim (h : SemiringWithMonusHom K K')
    {cI mI : ℕ} {κ : Fin mI → ColKind} (pc : ProjColIn T cI κ)
    {γ : Fin cI → T} {r' : GenRow T K' mI} {r : GenRow T K mI}
    (hcol : ∀ k, GenValue.Equiv (r'.fst k)
      (AggValue.mapAnnSum ⇑h.toRingHom (r.fst k))) :
    GenValue.Equiv (pc.eval r'.fst γ)
      (AggValue.mapAnnSum ⇑h.toRingHom (pc.eval r.fst γ)) := by
  cases pc with
  | term t =>
    simp only [ProjColIn.eval]
    show t.eval r'.fst γ = t.eval r.fst γ
    calc t.eval r'.fst γ
        = t.eval (fun k => AggValue.mapAnnSum ⇑h.toRingHom (r.fst k)) γ :=
          TermGIn.eval_equiv t hcol
      _ = t.eval r.fst γ := TermGIn.eval_mapAnnSum h t r.fst
  | provTerm t =>
    simp only [ProjColIn.eval]
    show t.eval r'.fst γ = t.eval r.fst γ
    calc t.eval r'.fst γ
        = t.eval (fun k => AggValue.mapAnnSum ⇑h.toRingHom (r.fst k)) γ :=
          TermGIn.eval_equiv t hcol
      _ = t.eval r.fst γ := TermGIn.eval_mapAnnSum h t r.fst
  | token k hk =>
    simp only [ProjColIn.eval]
    exact hcol k
  | aggTerm k hk gf =>
    -- reading an aggregate column through a function leaves its
    -- family and its convention alone, so the simulation carries
    -- over (`GenValue.Equiv.postcomp`)
    simp only [ProjColIn.eval]
    have hk' := hcol k
    cases hx' : r'.fst k with
    | inl v' =>
      cases hx : r.fst k with
      | inl v =>
        rw [hx', hx] at hk'
        exact congrArg gf hk'
      | inr a =>
        rw [hx', hx] at hk'
        exact absurd hk' GenValue.Equiv.not_inl_inr
    | inr x' =>
      cases hx : r.fst k with
      | inl v =>
        rw [hx', hx] at hk'
        exact absurd hk' GenValue.Equiv.not_inr_inl
      | inr x =>
        rw [hx', hx] at hk'
        show GenValue.Equiv (Sum.inr (x'.postcomp gf))
          (Sum.inr ((x.postcomp gf).mapAnn ⇑h.toRingHom))
        rw [AggTok.mapAnn_postcomp ⇑h.toRingHom gf x]
        exact hk'.postcomp gf
  | aggTermOf k hk gf =>
    -- reading an aggregate column through a function leaves its
    -- family and its convention alone, so the simulation carries
    -- over (`GenValue.Equiv.postcomp`)
    simp only [ProjColIn.eval]
    have hk' := hcol k
    cases hx' : r'.fst k with
    | inl v' =>
      cases hx : r.fst k with
      | inl v =>
        rw [hx', hx] at hk'
        exact congrArg gf.unary hk'
      | inr a =>
        rw [hx', hx] at hk'
        exact absurd hk' GenValue.Equiv.not_inl_inr
    | inr x' =>
      cases hx : r.fst k with
      | inl v =>
        rw [hx', hx] at hk'
        exact absurd hk' GenValue.Equiv.not_inr_inl
      | inr x =>
        rw [hx', hx] at hk'
        show GenValue.Equiv (Sum.inr ((x'.postcomp gf.unary).setFam _))
          (Sum.inr (((x.postcomp gf.unary).setFam _).mapAnn ⇑h.toRingHom))
        rw [AggTok.mapAnn_setFam, AggTok.mapAnn_postcomp ⇑h.toRingHom gf.unary x]
        exact (hk'.postcomp gf.unary).setFam _ _

/-! ### Families across the rows of an evaluation

What the joint reading of a selection needs of a row is that its
families be presented on both sides. What a row carries for that is
stated over the pairs of corresponding values it holds (`rowPairs`), and
established for the whole evaluation at once below (`RowG`,
`AggQueryIn.evaluate_hom_univ`). -/

/-- The pairs of corresponding aggregate values two rows hold. -/
def rowPairs {n : ℕ} (u' : Tuple (GenValue T K') n) (u : Tuple (GenValue T K) n) :
    AggTok T K' × AggTok T K → Prop :=
  fun p => ∃ k, u' k = Sum.inr p.1 ∧ u k = Sum.inr p.2

omit [CommSemiringWithMonus K] [DecidableEq K] [CommSemiringWithMonus K'] [DecidableEq K']
  [HasAltLinearOrder K] [HasAltLinearOrder K'] in
omit [ValueType T] in
theorem rowPairs_append {n₁ n₂ : ℕ} (x' : Tuple (GenValue T K') n₁) (y' : Tuple (GenValue T K') n₂)
    (x : Tuple (GenValue T K) n₁) (y : Tuple (GenValue T K) n₂) (p : AggTok T K' × AggTok T K) :
    rowPairs (Fin.append x' y') (Fin.append x y) p ↔ rowPairs x' x p ∨ rowPairs y' y p := by
  constructor
  · rintro ⟨k, h1, h2⟩
    refine Fin.addCases (fun i h1 h2 => ?_) (fun j h1 h2 => ?_) k h1 h2
    · rw [Fin.append_left] at h1 h2
      exact Or.inl ⟨i, h1, h2⟩
    · rw [Fin.append_right] at h1 h2
      exact Or.inr ⟨j, h1, h2⟩
  · rintro (⟨i, h1, h2⟩ | ⟨j, h1, h2⟩)
    · exact ⟨Fin.castAdd _ i, by rw [Fin.append_left]; exact h1, by rw [Fin.append_left]; exact h2⟩
    · exact ⟨Fin.natAdd _ j, by rw [Fin.append_right]; exact h1, by rw [Fin.append_right]; exact h2⟩

/-- **Two environments related by a homomorphism**: the context columns
are equivalent at the arity read, and the rounds bound to each name
simulate each other row for row. -/
def EvalEnv.HomSim (h : SemiringWithMonusHom K K') (E' : EvalEnv T K') (E : EvalEnv T K)
    {c : ℕ} (γ : Fin c → T) : Prop :=
  (∀ k, GenValue.Equiv (E'.ctxAt c γ k) (AggValue.mapAnnSum ⇑h.toRingHom (E.ctxAt c γ k)))
    ∧ ∀ (s : String) (n : ℕ), Multiset.Rel (GenRow.Sim h) (E'.holes s n) (E.holes s n)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- Equivalent values have the same kind. -/
theorem GenValue.Equiv.kindOf_eq {h : K → K'} {x' : GenValue T K'} {x : GenValue T K}
    (hx : GenValue.Equiv x' (AggValue.mapAnnSum h x)) :
    GenValue.kindOf x' = GenValue.kindOf x := by
  cases x' with
  | inl a' => cases x with
    | inl a => rfl
    | inr a => exact absurd hx GenValue.Equiv.not_inl_inr
  | inr a' => cases x with
    | inl a => exact absurd hx GenValue.Equiv.not_inr_inl
    | inr a => rfl

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
theorem EvalEnv.homSim_empty (h : SemiringWithMonusHom K K') {c : ℕ} (γ : Fin c → T) :
    ({} : EvalEnv T K').HomSim h ({} : EvalEnv T K) γ := by
  refine ⟨fun k => ?_, fun _ _ => Multiset.Rel.zero⟩
  rw [EvalEnv.empty_ctxAt, EvalEnv.empty_ctxAt]
  exact (rfl : γ k = γ k)

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
theorem EvalEnv.HomSim.assignHole {h : SemiringWithMonusHom K K'} {E' : EvalEnv T K'}
    {E : EvalEnv T K} {c : ℕ} {γ : Fin c → T} (hE : E'.HomSim h E γ) (s : String) {n : ℕ}
    {X' : Multiset (GenRow T K' n)} {X : Multiset (GenRow T K n)}
    (hX : Multiset.Rel (GenRow.Sim h) X' X) :
    (E'.assignHole s X').HomSim h (E.assignHole s X) γ := by
  refine ⟨hE.1, fun s' m => ?_⟩
  simp only [EvalEnv.assignHole]
  by_cases hs : s' = s ∧ m = n
  · obtain ⟨rfl, rfl⟩ := hs
    rw [dite_eq_left ⟨rfl, rfl⟩, dite_eq_left ⟨rfl, rfl⟩]
    exact hX
  · rw [dite_eq_right hs, dite_eq_right hs]
    exact hE.2 s' m

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- **Entering an apply's right side** at two simulating rows keeps the
environments related. -/
theorem EvalEnv.HomSim.enter {h : SemiringWithMonusHom K K'} {E' : EvalEnv T K'}
    {E : EvalEnv T K} {c : ℕ} {γ : Fin c → T} (hE : E'.HomSim h E γ) {n₁ : ℕ}
    {x' : Tuple (GenValue T K') n₁} {x : Tuple (GenValue T K) n₁}
    (hx : ∀ k, GenValue.Equiv (x' k) (AggValue.mapAnnSum ⇑h.toRingHom (x k)))
    (γ₁ : Fin (n₁ + c) → T) :
    (E'.withCtx (Fin.append x' (E'.ctxAt c γ))).HomSim h
      (E.withCtx (Fin.append x (E.ctxAt c γ))) γ₁ := by
  refine ⟨fun k => ?_, hE.2⟩
  rw [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_withCtx]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left, Fin.append_left]; exact hx i
  · rw [Fin.append_right, Fin.append_right]; exact hE.1 j

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- The parameter leaf reads simulating rows off related environments. -/
theorem EvalEnv.HomSim.paramRows {h : SemiringWithMonusHom K K'} {E' : EvalEnv T K'}
    {E : EvalEnv T K} {c : ℕ} {γ : Fin c → T} (hE : E'.HomSim h E γ) {m : ℕ}
    (pv : Fin m → T ⊕ Fin c) (ρ : Fin m → ColKind) :
    Multiset.Rel (GenRow.Sim h) (E'.paramRows γ pv ρ) (E.paramRows γ pv ρ) := by
  have hu : ∀ k, GenValue.Equiv (_root_.Sum.elim Sum.inl (E'.ctxAt c γ) (pv k))
      (AggValue.mapAnnSum ⇑h.toRingHom (_root_.Sum.elim Sum.inl (E.ctxAt c γ) (pv k))) := by
    intro k
    cases pv k with
    | inl a => exact (rfl : a = a)
    | inr j => exact hE.1 j
  have hc : GenRow.Conforms ρ (fun k => _root_.Sum.elim Sum.inl (E'.ctxAt c γ) (pv k))
      ↔ GenRow.Conforms ρ (fun k => _root_.Sum.elim Sum.inl (E.ctxAt c γ) (pv k)) :=
    forall_congr' fun k => by rw [(hu k).kindOf_eq]
  simp only [EvalEnv.paramRows]
  by_cases hcc : GenRow.Conforms ρ (fun k => _root_.Sum.elim Sum.inl (E.ctxAt c γ) (pv k))
  · rw [ite_eq_left (hc.mpr hcc), ite_eq_left hcc]
    refine Multiset.Rel.cons ⟨hu, ?_⟩ Multiset.Rel.zero
    show GenAnn.finalize ⟨1, 0⟩ = h.toRingHom (GenAnn.finalize ⟨1, 0⟩)
    rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero, map_one]
  · rw [ite_eq_right (fun h' => hcc (hc.mp h')), ite_eq_right hcc]
    exact Multiset.Rel.zero

/-! ### The joint simulation -/

omit [CommSemiringWithMonus K] [DecidableEq K] [CommSemiringWithMonus K'] [DecidableEq K']
  [HasAltLinearOrder K] [HasAltLinearOrder K'] in
omit [ValueType T] in
/-- An annotated tuple read back holds no aggregate value. -/
theorem rowPairs_ofAnnotated {n : ℕ} (p' : AnnotatedTuple T K' n) (p : AnnotatedTuple T K n)
    (q : AggTok T K' × AggTok T K) :
    ¬ rowPairs (GenRow.ofAnnotated p').fst (GenRow.ofAnnotated p).fst q := by
  rintro ⟨k, h1, -⟩
  exact Sum.inl_ne_inr h1

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- An alternative of a row holds an aggregate value only where the row
does. -/
theorem GenRow.inr_of_mem_alternativesAt {K₀ : Type} [CommSemiringWithMonus K₀] [DecidableEq K₀]
    {n : ℕ}
    {r a : GenRow T K₀ n} {k : Fin n} (ha : a ∈ r.alternativesAt k) {j : Fin n} {x : AggTok T K₀}
    (hj : a.fst j = Sum.inr x) : r.fst j = Sum.inr x := by
  unfold GenRow.alternativesAt at ha
  split at ha
  · rw [Multiset.mem_singleton.mp ha] at hj
    exact hj
  · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
    by_cases hjk : j = k
    · subst hjk
      simp at hj
    · dsimp only at hj
      erw [Function.update_of_ne hjk] at hj
      exact hj

/-- **The value a grouping's aggregate builds over its group**: an
ordinary token, or, under a `FILTER` clause, the one-leaf expression over
the whole group whose clause cuts what it reads. -/
def groupTok {K₀ : Type} {c m : ℕ} (f : SeqAggFunc T) (t : TermIn T c m)
    (kp : Option (Selection T m)) (sc : Bool) (U₀ : List (AnnotatedTuple T K₀ m))
    (γ : Fin c → T) : AggTok T K₀ :=
  match kp with
  | none => .tok { AggValue.ofGroup f t U₀ γ with scalar := sc }
  | some φ => .expr (AggExpr.ofSeqWhen f t φ.keeps U₀ sc γ)

/-- How a grouping's aggregate reads a row of its group. -/
def groupSpec {c m : ℕ} (f : SeqAggFunc T) (t : TermIn T c m) (γ : Fin c → T) (sc : Bool)
    (kp : Option (Selection T m)) : LeafSpec (Tuple T m) T :=
  ⟨1, fun r _ => t.eval r γ, fun _ _ => true,
    fun r _ => match kp with | none => true | some φ => φ.keeps r,
    fun _ => f, fun _ => sc, fun v => v 0⟩

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
theorem flatExpr_groupTok {K₀ : Type} {c m : ℕ} (f : SeqAggFunc T) (t : TermIn T c m)
    (kp : Option (Selection T m)) (sc : Bool) (U₀ : List (AnnotatedTuple T K₀ m))
    (γ : Fin c → T) (ψ : FamId T) :
    ((groupTok f t kp sc U₀ γ).setFam ψ).flatExpr
      = (groupSpec f t γ sc kp).build U₀ Prod.snd Prod.fst ψ := by
  cases kp <;>
    simp [groupTok, groupSpec, AggTok.setFam, AggTok.flatExpr, AggExpr.ofValue,
      AggValue.ofGroup, LeafSpec.build, AggExpr.ofSeqWhen, List.map_map]

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
theorem classKey_groupTok {K₀ : Type} [CommSemiringWithMonus K₀] {c m : ℕ} (f : SeqAggFunc T)
    (t : TermIn T c m) (kp : Option (Selection T m)) (sc : Bool)
    (U₀ : List (AnnotatedTuple T K₀ m)) (γ : Fin c → T) (ψ : FamId T) :
    ((groupTok f t kp sc U₀ γ).setFam ψ).classKey = (ψ.family, U₀.map Prod.snd, none) := by
  cases kp <;>
    simp [groupTok, AggTok.setFam, AggTok.classKey, AggTok.annList, AggTok.fam,
      AggValue.ofGroup, AggExpr.annList, AggExpr.ofSeqWhen, List.map_map]

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [ValueType T] [DecidableEq K'] in
/-- **Two bags of nested occurrences carrying corresponding statistics**:
occurrence by occurrence the pushed-forward annotation and the pushed
world statistics. -/
theorem nestRel_of_rel (h : SemiringWithMonusHom K K') {O' : Multiset (AggExpr T K' × K')}
    {O : Multiset (AggExpr T K × K)}
    (hr : Multiset.Rel (fun o' o : AggExpr T K' × K' =>
        o'.snd = o.snd ∧ o'.fst.worldStats = o.fst.worldStats ∧ o'.fst.collapse = o.fst.collapse)
      O' (O.map (fun o => (o.fst.mapAnn ⇑h.toRingHom, h.toRingHom o.snd)))) :
    NestRel h.toRingHom O' O := by
  unfold NestRel
  rw [map_eq_of_rel hr (g := NestedValue.occStatsU) (fun o' o ho => by
      rw [NestedValue.occStatsU_eq, NestedValue.occStatsU_eq, ho.1, ho.2.1]),
    Multiset.map_map]
  refine Multiset.map_congr rfl (fun o _ => ?_)
  simp only [Function.comp, NestedValue.occStatsU_eq]
  erw [AggExpr.worldStats_mapAnn h.toRingHom o.fst]
  simp only [Multiset.map_add, Multiset.map_map, Function.comp, map_mul, map_add]

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- **A token presented by its own occurrences**, from the equivalence
of the two sides' tokens. -/
theorem ListingRel.exists_of_tokEquiv (h : SemiringWithMonusHom K K') {a' : AggValue T K'}
    {a : AggValue T K}
    (he : GenValue.Equiv (Sum.inr (AggTok.tok a') : GenValue T K')
      (Sum.inr (AggTok.tok (a.mapAnn ⇑h.toRingHom))))
    (φ φ' : FamId T) :
    ∃ D : ListingRel h.toRingHom T,
      D.Member ((AggTok.tok a').setFam φ') ((AggTok.tok a).setFam φ) := by
  obtain ⟨hagg, hsc, htie⟩ := he
  have htie' : TiePerm (fun z z' : (Fin 1 → T) × K' × (Fin 1 → Bool) × (Fin 1 → Bool) =>
        z.1 = z'.1 ∧ z.2.2 = z'.2.2)
      (a'.occs.map (fun o => ((fun _ : Fin 1 => o.1), o.2, (fun _ : Fin 1 => true),
        (fun _ : Fin 1 => true))))
      ((a.occs.map (fun o => ((fun _ : Fin 1 => o.1), o.2, (fun _ : Fin 1 => true),
        (fun _ : Fin 1 => true)))).map (fun z => (z.1, h.toRingHom z.2.1, z.2.2))) := by
    rw [List.map_map]
    have hm : (a.mapAnn ⇑h.toRingHom).occs = a.occs.map (fun o => (o.1, h.toRingHom o.2)) := rfl
    rw [hm] at htie
    have h2 := htie.map (eqv' := fun z z' : (Fin 1 → T) × K' × (Fin 1 → Bool) × (Fin 1 → Bool) =>
        z.1 = z'.1 ∧ z.2.2 = z'.2.2)
      (fun o : T × K' => ((fun _ : Fin 1 => o.1), o.2, (fun _ : Fin 1 => true),
        (fun _ : Fin 1 => true))) (fun hpq => ⟨funext fun _ => hpq, rfl⟩)
    rw [List.map_map] at h2
    exact h2
  obtain ⟨D, hD⟩ := ListingRel.exists_of_tie h.toRingHom (fun _ => a.agg) (fun _ => a.scalar)
    (fun v => v 0) htie'
  refine ⟨D, hD _ _ φ φ' rfl rfl rfl ?_⟩
  show AggExpr.ofValue { a' with fam := φ' } = _
  unfold AggExpr.ofValue
  rw [show a'.agg = a.agg from hagg, show a'.scalar = a.scalar from hsc]

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [ValueType T] [DecidableEq K'] in
/-- **An expression presented by its own occurrences**, from a tie-block
permutation of its family. -/
theorem ListingRel.exists_of_exprTie (h : SemiringWithMonusHom K K') (e : AggExpr T K)
    {occs' : List ((Fin e.arity → T) × K' × (Fin e.arity → Bool) × (Fin e.arity → Bool))}
    (htie : TiePerm (fun z z' => z.1 = z'.1 ∧ z.2.2 = z'.2.2) occs'
      (e.occs.map (fun z => (z.1, h.toRingHom z.2.1, z.2.2))))
    (φ φ' : FamId T) :
    ∃ D : ListingRel h.toRingHom T,
      D.Member (AggTok.expr ⟨e.arity, occs', e.aggs, e.scalar, e.g, φ'⟩)
        ((AggTok.expr e).setFam φ) := by
  obtain ⟨D, hD⟩ := ListingRel.exists_of_tie h.toRingHom e.aggs e.scalar e.g htie
  exact ⟨D, hD _ _ φ φ' rfl rfl rfl rfl⟩

omit [DecidableEq K] in
/-- **The column a filtered window builds is presented by its own
occurrences**: the two sides' families differ by a tie-block permutation
(`frameListOf_mapAnn_tiePerm`), the clause and the classes reading the
values. -/
theorem ListingRel.exists_exprWhenOf (h : SemiringWithMonusHom K K')
    {n' m' p' : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') (w : ValueFrame T p') {c : ℕ} (t : TermIn T c n')
    (γ : Fin c → T) (f : SeqAggFunc T) (dist : Bool)
    (keep : Tuple T n' → Bool) (X : Multiset (AnnotatedTuple T K n'))
    {x : AnnotatedTuple T K n'} (hx : x ∈ X) (φ φ' : FamId T) :
    ∃ D : ListingRel h.toRingHom T,
      D.Member ((AggTok.expr (ValueFrame.exprWhenOf P O o w t f dist keep
          (Multiset.map (fun q : AnnotatedTuple T K n' =>
            ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
          ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ)).setFam φ')
        ((AggTok.expr (ValueFrame.exprWhenOf P O o w t f dist keep X x γ)).setFam φ) := by
  have htie := frameListOf_mapAnn_tiePerm h P O o w X hx
  unfold ValueFrame.exprWhenOf
  cases dist
  · simp only [Bool.false_eq_true, ite_false]
    have hm := AggExpr.ofSeqWhen_mapAnn f t keep
      (ValueFrame.frameListOf (α := AnnotatedTuple T K n') Prod.fst P O o w X x) γ
      (!w.s (Tuple.key O x.fst)) ⇑h.toRingHom
    have ht := TiePerm.symm (fun e => ⟨e.1.symm, e.2.symm⟩)
      (AggExpr.ofSeqWhen_tiePerm_occs f t keep (!w.s (Tuple.key O x.fst)) γ htie)
    refine ListingRel.exists_of_exprTie h _ ?_ φ φ'
    have hm' : List.map (fun z => (z.1, h.toRingHom z.2.1, z.2.2)) (AggExpr.ofSeqWhen f t keep
          (ValueFrame.frameListOf (α := AnnotatedTuple T K n') Prod.fst P O o w X x)
          (!w.s (Tuple.key O x.fst)) γ).occs
        = (AggExpr.ofSeqWhen f t keep
          (List.map (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' n'))
            (ValueFrame.frameListOf (α := AnnotatedTuple T K n') Prod.fst P O o w X x))
          (!w.s (Tuple.key O x.fst)) γ).occs :=
      eq_of_heq (congr_arg_heq AggExpr.occs hm)
    rw [hm']
    exact ht
  · simp only [ite_true]
    have hm := AggExpr.ofSeqDistWhen_mapAnn (hm := ⇑h.toRingHom)
      f t keep (ValueFrame.frameListOf (α := AnnotatedTuple T K n') Prod.fst P O o w X x)
      (!w.s (Tuple.key O x.fst)) γ (map_zero h.toRingHom) (fun a b => map_add h.toRingHom a b)
    have ht := TiePerm.symm (fun e => ⟨e.1.symm, e.2.symm⟩)
      (AggExpr.ofSeqDistWhen_tiePerm_occs f t keep (!w.s (Tuple.key O x.fst)) γ htie)
    refine ListingRel.exists_of_exprTie h _ ?_ φ φ'
    have hm' : List.map (fun z => (z.1, h.toRingHom z.2.1, z.2.2)) (AggExpr.ofSeqDistWhen f t keep
          (ValueFrame.frameListOf (α := AnnotatedTuple T K n') Prod.fst P O o w X x)
          (!w.s (Tuple.key O x.fst)) γ).occs
        = (AggExpr.ofSeqDistWhen f t keep
          (List.map (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' n'))
            (ValueFrame.frameListOf (α := AnnotatedTuple T K n') Prod.fst P O o w X x))
          (!w.s (Tuple.key O x.fst)) γ).occs :=
      eq_of_heq (congr_arg_heq AggExpr.occs hm)
    rw [hm']
    exact ht

omit [DecidableEq K] in
theorem ListingRel.exists_exprOfWhen (h : SemiringWithMonusHom K K')
    {n' m' p' qq : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') {ws : Fin qq → ValueFrame T p'}
    (hcs : ∀ l, (ws l).ContainsSelf) {c : ℕ} (ts : Fin qq → TermIn T c n')
    (fs : Fin qq → SeqAggFunc T) (g : (Fin qq → T) → T)
    (keeps : Fin qq → Option (Selection T n')) (γ : Fin c → T)
    {r' : OccFam (AnnotatedTuple T K' n')} {r : OccFam (AnnotatedTuple T K n')}
    {i' : Fin r'.size} {i : Fin r.size}
    (hi : (r'.row i').fst = (r.row i).fst)
    (hX : r'.toMultiset = Multiset.map (fun y : AnnotatedTuple T K n' =>
        ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' n')) r.toMultiset)
    (φ φ' : FamId T) :
    ∃ D : ListingRel h.toRingHom T,
      D.Member ((AggTok.expr (ValueFrame.exprOfWhen P O o ws ts fs g keeps r' i' γ)).setFam φ')
        ((AggTok.expr (ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ)).setFam φ) := by
  have hcu : (ValueFrame.unionFrame ws).ContainsSelf :=
    ValueFrame.containsSelf_unionFrame hcs
  set gh : AnnotatedTuple T K n' → AnnotatedTuple T K' n' :=
    fun y => ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' n') with hghdef
  set Lb : List (AnnotatedTuple T K n') :=
    (ValueFrame.exprIdx (α := AnnotatedTuple T K n') Prod.fst P O o ws r i).map
      r.row with hLb
  set L' : List (AnnotatedTuple T K' n') :=
    (ValueFrame.exprIdx (α := AnnotatedTuple T K' n') Prod.fst P O o ws r' i').map
      r'.row with hL'
  -- the two orderings hold the same rows
  have hperm : L'.Perm (Lb.map gh) := by
    refine Multiset.coe_eq_coe.mp ?_
    rw [← Multiset.map_coe gh Lb, hL', hLb, ← Multiset.map_coe r'.row,
      ← Multiset.map_coe r.row,
      ValueFrame.exprIdx_rows_coe (α := AnnotatedTuple T K' n')
        Prod.fst P O o ws r' i',
      ValueFrame.exprIdx_rows_coe (α := AnnotatedTuple T K n')
        Prod.fst P O o ws r i,
      ← ValueFrame.frameOf_map (α := AnnotatedTuple T K n')
        (β := AnnotatedTuple T K' n') (valα := Prod.fst) (valβ := Prod.fst) gh
        (fun _ => rfl) P O (ValueFrame.unionFrame ws) r.toMultiset
        (OccFam.row_mem_toMultiset r i),
      ← hX]
    exact ValueFrame.frameOf_congr_val (α := AnnotatedTuple T K' n')
      Prod.fst P O hcu r'.toMultiset
      (OccFam.row_mem_toMultiset r' i')
      (hX ▸ Multiset.mem_map_of_mem gh (OccFam.row_mem_toMultiset r i)) hi
  -- and each is sorted by the clause's order
  have hs' : L'.Pairwise (fun x y =>
      OrderSpec.readLe (Tuple.key O) Prod.fst o x y = true) :=
    ValueFrame.exprIdx_rows_pairwise (α := AnnotatedTuple T K' n')
      Prod.fst P O o ws r' i'
  have hs : (Lb.map gh).Pairwise (fun x y =>
      OrderSpec.readLe (Tuple.key O) Prod.fst o x y = true) := by
    rw [List.pairwise_map]
    exact (ValueFrame.exprIdx_rows_pairwise (α := AnnotatedTuple T K n')
      Prod.fst P O o ws r i).imp (fun hab => hab)
  have htp : TiePerm (fun a b : AnnotatedTuple T K' n' => a.fst = b.fst)
      L' (Lb.map gh) :=
    tiePerm_of_perm_of_sorted_by _ Prod.fst
      (fun hxy hyx => OrderSpec.val_eq_of_readLe hxy hyx)
      (fun hv => OrderSpec.readLe_of_val_eq hv) hperm hs' hs
  -- both families are the same reading of their rows
  have hocc' : (ValueFrame.exprOfWhen P O o ws ts fs g keeps r' i' γ).occs
      = L'.map (fun y : AnnotatedTuple T K' n' =>
        ((fun l => (ts l).eval y.fst γ), y.snd,
          (fun l => decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
            && (ws l).ρ (Tuple.key O y.fst)
              (Tuple.key O (r.row i).fst)),
          fun l => match keeps l with
            | none => true
            | some φ => φ.keeps y.fst)) := by
    rw [ValueFrame.occs_exprOfWhen P O o hcs ts fs g keeps r' i' γ, hi, hL']
    rfl
  have hoccb : ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).mapAnn
        ⇑h.toRingHom).occs
      = (Lb.map gh).map (fun y : AnnotatedTuple T K' n' =>
        ((fun l => (ts l).eval y.fst γ), y.snd,
          (fun l => decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
            && (ws l).ρ (Tuple.key O y.fst)
              (Tuple.key O (r.row i).fst)),
          fun l => match keeps l with
            | none => true
            | some φ => φ.keeps y.fst)) := by
    show ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).occs.map
        (fun z => (z.fst, h.toRingHom z.snd.fst, z.snd.snd))) = _
    rw [ValueFrame.occs_exprOfWhen P O o hcs ts fs g keeps r i γ, hLb]
    simp only [List.map_map]
    rfl
  have hsc : (ValueFrame.exprOfWhen P O o ws ts fs g keeps r' i' γ).scalar
      = (ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).scalar := by
    funext l
    show (!(ws l).s (Tuple.key O (r'.row i').fst))
      = (!(ws l).s (Tuple.key O (r.row i).fst))
    rw [hi]
  have htie : TiePerm (fun z z' => z.1 = z'.1 ∧ z.2.2 = z'.2.2)
      (ValueFrame.exprOfWhen P O o ws ts fs g keeps r' i' γ).occs
      ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).occs.map
        (fun z => (z.1, h.toRingHom z.2.1, z.2.2))) := by
    rw [hocc']
    change TiePerm _ _ ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).mapAnn
      ⇑h.toRingHom).occs
    rw [hoccb]
    exact htp.map _ (fun hab => ⟨by rw [hab], by rw [hab]⟩)
  obtain ⟨D, hD⟩ := ListingRel.exists_of_tie h.toRingHom
    (ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).aggs
    (ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).scalar
    (ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).g htie
  refine ⟨D, hD _ _ φ φ' rfl rfl rfl ?_⟩
  show AggExpr.mk qq _ fs (ValueFrame.exprOfWhen P O o ws ts fs g keeps r' i' γ).scalar g φ' = _
  rw [hsc]
  rfl

/-! ### One presentation for the whole evaluation

Every aggregate value an evaluation holds is built by an operator of the
query, at one of the situations the evaluation passes through, or is
provided by the environment, up to terms (`AggQueryIn.rowToks`); and two
values carrying one identifier are one value, two of one family carry one
class (`AggQueryIn.builds_coherent`). So a family is presented once, by the
listing of the operator row that built it, for the whole evaluation: what a
row carries is that each of its pairs records one identifier on both sides
and that its class is so presented (`ClassPres`). Rows then merge with
nothing to check, and a selection reads the families of a row jointly
(`famPres_of_good`). -/

/-- A pair of values of the two universes carrying one identifier. -/
def GPair (𝒰₀ : AggTok T K → Prop) (𝒰₀' : AggTok T K' → Prop)
    (p : AggTok T K' × AggTok T K) : Prop :=
  TermCl 𝒰₀' p.1 ∧ TermCl 𝒰₀ p.2 ∧ p.1.fam = p.2.fam

/-- **The class of `x` is presented** across the two universes: one
listing on each side presents every pair of the class. -/
def ClassPres (h : SemiringWithMonusHom K K') (𝒰₀ : AggTok T K → Prop)
    (𝒰₀' : AggTok T K' → Prop) (x : AggTok T K) : Prop :=
  (∃ D : ListingRel h.toRingHom T, ∀ q, GPair 𝒰₀ 𝒰₀' q → q.2.classKey = x.classKey →
      D.Member q.1 q.2)
    ∨ (∃ O O', NestRel h.toRingHom O' O ∧ ∀ q, GPair 𝒰₀ 𝒰₀' q → q.2.classKey = x.classKey →
      NestMember O' O q.1 q.2)

/-- **What a row carries**: each pair of corresponding values records one
identifier, and its class is presented. -/
def RowG (h : SemiringWithMonusHom K K') (𝒰₀ : AggTok T K → Prop) (𝒰₀' : AggTok T K' → Prop)
    {n : ℕ} (r' : GenRow T K' n) (r : GenRow T K n) : Prop :=
  ∀ p, rowPairs r'.fst r.fst p → p.1.fam = p.2.fam ∧ ClassPres h 𝒰₀ 𝒰₀' p.2

/-- **The universes of an evaluation**: what the two sides build, with no
term recorded; one value per identifier and one class per family; each
operator, of label `l`, building fewer columns than its width in `W`. -/
structure HomUniv (𝒰₀ : AggTok T K → Prop) (𝒰₀' : AggTok T K' → Prop) (W : List (ℕ × ℕ)) :
    Prop where
  t : ∀ x, 𝒰₀ x → x.fam.terms' = []
  t' : ∀ x, 𝒰₀' x → x.fam.terms' = []
  fn : FamFun (TermCl 𝒰₀)
  fn' : FamFun (TermCl 𝒰₀')
  key : FamKeyed (TermCl 𝒰₀)
  key' : FamKeyed (TermCl 𝒰₀')
  col : ∀ x, 𝒰₀ x → ∀ w, (x.lab, w) ∈ W → x.fam.col < w

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- **The families of pairs drawn from the universes, each class
presented, are presented together.** -/
theorem famPres_of_good {h : SemiringWithMonusHom K K'} {𝒰₀ : AggTok T K → Prop}
    {𝒰₀' : AggTok T K' → Prop} {W : List (ℕ × ℕ)} (hU : HomUniv 𝒰₀ 𝒰₀' W)
    {S : AggTok T K' × AggTok T K → Prop}
    (hS : ∀ p, S p → GPair 𝒰₀ 𝒰₀' p ∧ ClassPres h 𝒰₀ 𝒰₀' p.2) : FamPres h.toRingHom S := by
  refine ⟨fun p q hp hq => ?_, fun p₀ hp₀ => ?_⟩
  · obtain ⟨⟨hp1, hp2, hpf⟩, -⟩ := hS p hp
    obtain ⟨⟨hq1, hq2, hqf⟩, -⟩ := hS q hq
    constructor
    · intro hk
      have hf : p.1.fam.family = q.1.fam.family := congrArg (fun z => z.1) hk
      rw [hpf, hqf] at hf
      exact hU.key p.2 q.2 hp2 hq2 hf
    · intro hk
      have hf : p.2.fam.family = q.2.fam.family := congrArg (fun z => z.1) hk
      rw [← hpf, ← hqf] at hf
      exact hU.key' p.1 q.1 hp1 hq1 hf
  · rcases (hS p₀ hp₀).2 with ⟨D, hD⟩ | ⟨O, O', hO, hN⟩
    · exact Or.inl ⟨D, fun q hq hk => hD q (hS q hq).1 hk⟩
    · exact Or.inr ⟨O, O', hO, fun q hq hk => hN q (hS q hq).1 hk⟩

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
theorem ListingRel.Member.postcompTerms {f : K →+* K'} {D : ListingRel f T}
    {y' : AggTok T K'} {y : AggTok T K} (hm : D.Member y' y) :
    ∀ ts, D.Member (y'.postcompTerms ts) (y.postcompTerms ts)
  | [] => hm
  | t :: ts => by
    obtain ⟨hn, hn', ok, val, hP, hP'⟩ := hm
    exact ListingRel.Member.postcompTerms (y' := y'.postcompTerm t) (y := y.postcompTerm t)
      ⟨by rw [AggTok.isNested_postcompTerm]; exact hn,
        by rw [AggTok.isNested_postcompTerm]; exact hn', ok, fun s => t.unary (val s),
        hP.postcompTerm hn t, hP'.postcompTerm hn' t⟩ ts

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K']
  [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
theorem NestMember.postcompTerms {O' : Multiset (AggExpr T K' × K')}
    {O : Multiset (AggExpr T K × K)} {y' : AggTok T K'} {y : AggTok T K}
    (hm : NestMember O' O y' y) : ∀ ts, NestMember O' O (y'.postcompTerms ts) (y.postcompTerms ts)
  | [] => hm
  | t :: ts => by
    obtain ⟨b, b', h₁, h₂, ho, ho', hagg, hsc⟩ := hm
    subst h₁ h₂
    refine NestMember.postcompTerms (y' := (AggTok.nest b').postcompTerm t)
      (y := (AggTok.nest b).postcompTerm t)
      ⟨{ b.postcomp t.unary with fam := (AggTok.nest b).fam.addTerm t },
        { b'.postcomp t.unary with fam := (AggTok.nest b').fam.addTerm t }, rfl, rfl, ho, ho',
        ?_, hsc⟩ ts
    show (fun s => t.unary (b'.agg s)) = (fun s => t.unary (b.agg s))
    rw [hagg]

omit [ValueType T] in
theorem FamId.eq_mk_of {φ : FamId T} {l : ℕ} {k : List T} {p : List (T ⊕ FamId T)} {c : ℕ}
    {ts : List (TermIn T 1 0)} (hf : φ.family = (l, k, p)) (hc : φ.col = c)
    (ht : φ.terms' = ts) : φ = .mk l k p c ts := by
  cases φ with
  | mk l' k' p' c' ts' =>
    simp only [FamId.family, Prod.mk.injEq] at hf
    simp only [FamId.col] at hc
    simp only [FamId.terms'] at ht
    obtain ⟨rfl, rfl, rfl⟩ := hf
    rw [hc, ht]

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- **The class of a fresh row is presented**: an operator row of width
`w` – its columns `col j` holding the values of one family, the `j`-th
recording column `j` – whose pairs one listing presents. Every pair of
the universes in that class is a term over one of its columns: one
identifier, one value (`HomUniv.fn`), and the columns its operator builds
are the row's (`HomUniv.col`). -/
theorem classPres_row {h : SemiringWithMonusHom K K'} {𝒰₀ : AggTok T K → Prop}
    {𝒰₀' : AggTok T K' → Prop} {W : List (ℕ × ℕ)} (hU : HomUniv 𝒰₀ 𝒰₀' W)
    {n w : ℕ} (r' : GenRow T K' n) (r : GenRow T K n) (col : Fin w → Fin n) (lab : ℕ)
    (key : List T) (ps : List (T ⊕ FamId T)) (hW : w ≠ 0 → (lab, w) ∈ W)
    (hz : ∀ j, ∃ x, r.fst (col j) = Sum.inr x ∧ 𝒰₀ x ∧ x.fam = .mk lab key ps j [])
    (hz' : ∀ j, ∃ x', r'.fst (col j) = Sum.inr x' ∧ 𝒰₀' x')
    (heq : ∀ j x' x, r'.fst (col j) = Sum.inr x' → r.fst (col j) = Sum.inr x → x'.fam = x.fam)
    (hD : (∃ D : ListingRel h.toRingHom T, ∀ j x' x, r'.fst (col j) = Sum.inr x' →
        r.fst (col j) = Sum.inr x → D.Member x' x)
      ∨ (∃ O O', NestRel h.toRingHom O' O ∧ ∀ j x' x, r'.fst (col j) = Sum.inr x' →
        r.fst (col j) = Sum.inr x → NestMember O' O x' x))
    (j₀ : Fin w) {x₀ : AggTok T K} (hx₀ : r.fst (col j₀) = Sum.inr x₀) :
    ClassPres h 𝒰₀ 𝒰₀' x₀ := by
  -- every pair of the class is a term over one of the row's pairs
  have hcls : ∀ q, GPair 𝒰₀ 𝒰₀' q → q.2.classKey = x₀.classKey →
      ∃ j z' z, r'.fst (col j) = Sum.inr z' ∧ r.fst (col j) = Sum.inr z ∧
        q = (z'.postcompTerms q.2.fam.terms', z.postcompTerms q.2.fam.terms') := by
    intro q ⟨hq1, hq2, hqf⟩ hk
    obtain ⟨y₀, hy₀, hry, hey⟩ := hq2.root hU.t
    obtain ⟨y₀', hy₀', hry', hey'⟩ := hq1.root hU.t'
    obtain ⟨z₀, hz₀, -, hz₀f⟩ := hz j₀
    rw [hx₀, Sum.inr.injEq] at hz₀
    subst hz₀
    have hfam : y₀.fam.family = (lab, key, ps) := by
      rw [hry, FamId.family_root]
      have : q.2.fam.family = x₀.fam.family := congrArg (fun z => z.1) hk
      rw [this, hz₀f]
      rfl
    have hlab : y₀.lab = lab := by
      unfold AggTok.lab
      cases hy : y₀.fam with
      | mk l k p c ts => rw [hy] at hfam; simp only [FamId.family, Prod.mk.injEq] at hfam
                         exact hfam.1
    have hcol := hU.col y₀ hy₀ w (by rw [hlab]; exact hW (Fin.pos j₀).ne')
    obtain ⟨z, hz1, hz2, hz3⟩ := hz ⟨y₀.fam.col, hcol⟩
    obtain ⟨z', hz1', hz2'⟩ := hz' ⟨y₀.fam.col, hcol⟩
    have hyz : y₀ = z := hU.fn y₀ z (TermCl.base hy₀) (TermCl.base hz2) (by
      rw [hz3]; exact FamId.eq_mk_of hfam rfl (hU.t y₀ hy₀))
    have hyz' : y₀' = z' := hU.fn' y₀' z' (TermCl.base hy₀') (TermCl.base hz2') (by
      rw [heq _ z' z hz1' hz1, ← hyz, hry', hry, hqf])
    refine ⟨⟨y₀.fam.col, hcol⟩, z', z, hz1', hz1, Prod.ext ?_ ?_⟩
    · exact hey'.trans (by rw [hyz', hqf])
    · exact hey.trans (by rw [hyz])
  rcases hD with ⟨D, hD⟩ | ⟨O, O', hO, hN⟩
  · refine Or.inl ⟨D, fun q hq hk => ?_⟩
    obtain ⟨j, z', z, h1, h2, he⟩ := hcls q hq hk
    rw [he]
    exact (hD j z' z h1 h2).postcompTerms _
  · refine Or.inr ⟨O, O', hO, fun q hq hk => ?_⟩
    obtain ⟨j, z', z, h1, h2, he⟩ := hcls q hq hk
    rw [he]
    exact (hN j z' z h1 h2).postcompTerms _

/-- **An environment of the evaluation**: its context's values carry one
identifier on both sides with their class presented, its rounds simulate
each other with their rows carrying the same, and what it provides is
drawn from the universes. -/
structure EnvG (h : SemiringWithMonusHom K K') (𝒰₀ : AggTok T K → Prop)
    (𝒰₀' : AggTok T K' → Prop) {c : ℕ} (γ : Fin c → T) (E' : EvalEnv T K') (E : EvalEnv T K)
    (l : List (String × ℕ)) : Prop where
  ctx : ∀ k x' x, E'.ctxAt c γ k = Sum.inr x' → E.ctxAt c γ k = Sum.inr x →
    x'.fam = x.fam ∧ ClassPres h 𝒰₀ 𝒰₀' x
  holes : ∀ s m, (s, m) ∈ l → Multiset.Rel (fun r' r => GenRow.Sim h r' r
    ∧ RowG h 𝒰₀ 𝒰₀' r' r) (E'.holes s m) (E.holes s m)
  toks : ∀ x, E.Toks γ l x → TermCl 𝒰₀ x
  toks' : ∀ x, E'.Toks γ l x → TermCl 𝒰₀' x

omit [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K] in
theorem EnvG.sub {h : SemiringWithMonusHom K K'} {𝒰₀ : AggTok T K → Prop}
    {𝒰₀' : AggTok T K' → Prop} {c : ℕ} {γ : Fin c → T} {E' : EvalEnv T K'} {E : EvalEnv T K}
    {l l' : List (String × ℕ)} (hJ : EnvG h 𝒰₀ 𝒰₀' γ E' E l) (hl : l' ⊆ l) :
    EnvG h 𝒰₀ 𝒰₀' γ E' E l' :=
  ⟨hJ.ctx, fun s m hsm => hJ.holes s m (hl hsm), fun x hx => hJ.toks x (hx.mono hl),
    fun x hx => hJ.toks' x (hx.mono hl)⟩

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- **The two sides stamp the same parameters.** -/
theorem EvalEnv.paramKey_eq_of_envG {h : SemiringWithMonusHom K K'}
    {𝒰₀ : AggTok T K → Prop} {𝒰₀' : AggTok T K' → Prop} {c : ℕ} {γ : Fin c → T}
    {E' : EvalEnv T K'} {E : EvalEnv T K} {l : List (String × ℕ)} (hE : E'.HomSim h E γ)
    (hJ : EnvG h 𝒰₀ 𝒰₀' γ E' E l) (rd : Fin c → Bool) :
    E'.paramKey rd γ = E.paramKey rd γ := by
  unfold EvalEnv.paramKey
  congr 1
  funext k
  have hk := hE.1 k
  cases hc : E.ctxAt c γ k with
  | inl v =>
    rw [hc] at hk
    cases hc' : E'.ctxAt c γ k with
    | inl v' => rw [hc'] at hk; simp only [GenValue.paramId]; exact congrArg Sum.inl hk
    | inr x' => rw [hc'] at hk; exact absurd hk GenValue.Equiv.not_inr_inl
  | inr x =>
    rw [hc] at hk
    cases hc' : E'.ctxAt c γ k with
    | inl v' => rw [hc'] at hk; exact absurd hk GenValue.Equiv.not_inl_inr
    | inr x' =>
      simp only [GenValue.paramId]
      exact congrArg Sum.inr (hJ.ctx k x' x hc' hc).1

/-- **The values of the rows of an evaluation are in the universe**: built
by the query or provided by the environment, up to terms. -/
theorem AggQueryIn.rowToks_in {K₀ : Type} [CommSemiringWithMonus K₀] [DecidableEq K₀]
    [HasAltLinearOrder K₀] {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (hsc : q.sourceCols) (d : AnnotatedDatabase T K₀)
    (γ : Fin c → T) (E : EvalEnv T K₀) (𝒰₀ : AggTok T K₀ → Prop)
    (hb : ∀ x, q.Builds d γ E x → 𝒰₀ x) (ht : ∀ x, E.Toks γ l x → TermCl 𝒰₀ x) :
    ∀ r ∈ q.evaluate d γ E, ∀ k x, r.fst k = Sum.inr x → TermCl 𝒰₀ x :=
  fun r hr k x hk => ((q.rowToks hsc d γ E r hr k x hk).mono (fun z hz =>
    hz.elim (fun h => TermCl.base (hb z h)) (fun h => ht z h))).idem

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- A row holding no aggregate value carries nothing. -/
theorem RowG.of_noPairs {h : SemiringWithMonusHom K K'} {𝒰₀ : AggTok T K → Prop}
    {𝒰₀' : AggTok T K' → Prop} {n : ℕ} {r' : GenRow T K' n} {r : GenRow T K n}
    (hr : ∀ p, ¬ rowPairs r'.fst r.fst p) : RowG h 𝒰₀ 𝒰₀' r' r :=
  fun p hp => absurd hp (hr p)

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
theorem ClassPres.congr {h : SemiringWithMonusHom K K'} {𝒰₀ : AggTok T K → Prop}
    {𝒰₀' : AggTok T K' → Prop} {x y : AggTok T K} (hk : x.classKey = y.classKey)
    (hx : ClassPres h 𝒰₀ 𝒰₀' x) : ClassPres h 𝒰₀ 𝒰₀' y := by
  unfold ClassPres at hx ⊢
  rw [← hk]
  exact hx

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- **What a row carries survives a term over a value.** -/
theorem pairG_postcompTerm {h : SemiringWithMonusHom K K'} {𝒰₀ : AggTok T K → Prop}
    {𝒰₀' : AggTok T K' → Prop} {x' : AggTok T K'} {x : AggTok T K} (t : TermIn T 1 0)
    (hp : x'.fam = x.fam ∧ ClassPres h 𝒰₀ 𝒰₀' x) :
    (x'.postcompTerm t).fam = (x.postcompTerm t).fam
      ∧ ClassPres h 𝒰₀ 𝒰₀' (x.postcompTerm t) :=
  ⟨by simp [AggTok.postcompTerm, hp.1],
    hp.2.congr (AggTok.classKey_postcompTerm t x).symm⟩

omit [DecidableEq K] [DecidableEq K'] [HasAltLinearOrder K] [HasAltLinearOrder K']
  [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
/-- **A projection column of the source language holds one of its row's
values, or a term over one**, on both sides alike. -/
theorem ProjColIn.pair_eval {cI mI : ℕ} {κ : Fin mI → ColKind} (pc : ProjColIn T cI κ)
    (hpc : pc.sourceCol = true) (P : AggTok T K' × AggTok T K → Prop)
    (hP : ∀ x' x t, P (x', x) → P (x'.postcompTerm t, x.postcompTerm t))
    {γ : Fin cI → T} {u' : Tuple (GenValue T K') mI} {u : Tuple (GenValue T K) mI}
    (hrow : ∀ p, rowPairs u' u p → P p)
    {y' : AggTok T K'} {y : AggTok T K} (h1 : pc.eval u' γ = Sum.inr y')
    (h2 : pc.eval u γ = Sum.inr y) : P (y', y) := by
  cases pc with
  | term t => exact absurd h2 (by simp [ProjColIn.eval])
  | provTerm t => exact absurd h2 (by simp [ProjColIn.eval])
  | token k hk => exact hrow _ ⟨k, h1, h2⟩
  | aggTerm k hk gf => exact absurd hpc (by simp [ProjColIn.sourceCol])
  | aggTermOf k hk t =>
    simp only [ProjColIn.eval] at h1 h2
    rcases hu : u k with v | x <;> rcases hu' : u' k with v' | x'
    all_goals rw [hu] at h2; rw [hu'] at h1
    all_goals simp only [Sum.map_inl, Sum.map_inr, reduceCtorEq, Sum.inr.injEq] at h1 h2
    subst h1 h2
    exact hP x' x t (hrow _ ⟨k, hu', hu⟩)

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- Annotated tuples read back carry nothing. -/
theorem rel_ofAnnotated_mapG (h : SemiringWithMonusHom K K') (𝒰₀ : AggTok T K → Prop)
    (𝒰₀' : AggTok T K' → Prop) {n : ℕ} (X : AnnotatedRelation T K n) :
    Multiset.Rel (fun r' r => GenRow.Sim h r' r ∧ RowG h 𝒰₀ 𝒰₀' r' r)
      ((SemiringWithMonusHom.mapAnnotatedRelation h X).map GenRow.ofAnnotated)
      (X.map GenRow.ofAnnotated) := by
  refine (rel_ofAnnotated_map h X).mono (fun r' hr' r hr hs => ⟨hs, RowG.of_noPairs ?_⟩)
  intro q hq
  obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨p', -, rfl⟩ := Multiset.mem_map.mp hr'
  exact rowPairs_ofAnnotated p' p q hq

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
theorem RowG.append {h : SemiringWithMonusHom K K'} {𝒰₀ : AggTok T K → Prop}
    {𝒰₀' : AggTok T K' → Prop} {n₁ n₂ : ℕ} {x' : GenRow T K' n₁} {x : GenRow T K n₁}
    {y' : GenRow T K' n₂} {y : GenRow T K n₂} (hx : RowG h 𝒰₀ 𝒰₀' x' x)
    (hy : RowG h 𝒰₀ 𝒰₀' y' y) (b' : GenAnn K') (b : GenAnn K) :
    RowG h 𝒰₀ 𝒰₀' ((Fin.append x'.fst y'.fst, b') : GenRow T K' (n₁ + n₂))
      ((Fin.append x.fst y.fst, b) : GenRow T K (n₁ + n₂)) := fun p hp =>
  ((rowPairs_append _ _ _ _ p).mp hp).elim (hx p) (hy p)

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K']
  [CommSemiringWithMonus K] [CommSemiringWithMonus K'] [ValueType T] in
/-- `muSumFix_rel`, with the step asked only at the rounds themselves. -/
theorem muSumFix_rel_it {α β : Type} {R : β → α → Prop} {step : Multiset α → Multiset α}
    {step' : Multiset β → Multiset β} {M : Multiset α} {M' : Multiset β}
    (hM : Multiset.Rel R M' M)
    (hstep : ∀ k : ℕ, Multiset.Rel R (step'^[k] M') (step^[k] M) →
      Multiset.Rel R (step' (step'^[k] M')) (step (step^[k] M))) :
    Multiset.Rel R (muSumFix step' M') (muSumFix step M) := by
  have hit : ∀ k, Multiset.Rel R (step'^[k] M') (step^[k] M) := by
    intro k
    induction k with
    | zero => exact hM
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hstep k ih
  have hz : ∀ k, step'^[k] M' = 0 ↔ step^[k] M = 0 := by
    intro k
    constructor
    · intro h0
      have := hit k
      rw [h0] at this
      exact Multiset.rel_zero_left.mp this
    · intro h0
      have := hit k
      rw [h0] at this
      exact Multiset.rel_zero_right.mp this
  have hr : muRounds step' M' = muRounds step M := by
    unfold muRounds
    congr 1
    ext k
    exact hz (k + 1)
  unfold muSumFix
  rw [hr]
  generalize muRounds step M = b
  induction b with
  | zero => exact hM
  | succ b ih =>
    rw [muSum_succ, muSum_succ]
    exact ih.add (hit (b + 1))

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- **The fresh columns of an operator row carry what a row carries.** -/
theorem freshG {h : SemiringWithMonusHom K K'} {𝒰₀ : AggTok T K → Prop}
    {𝒰₀' : AggTok T K' → Prop} {W : List (ℕ × ℕ)} (hU : HomUniv 𝒰₀ 𝒰₀' W)
    {n w : ℕ} (r' : GenRow T K' n) (r : GenRow T K n) (col : Fin w → Fin n) (lab : ℕ)
    (hW : w ≠ 0 → (lab, w) ∈ W) (key : List T) (ps : List (T ⊕ FamId T))
    (hz : ∀ j, ∃ x, r.fst (col j) = Sum.inr x ∧ 𝒰₀ x ∧ x.fam = .mk lab key ps j [])
    (hz' : ∀ j, ∃ x', r'.fst (col j) = Sum.inr x' ∧ 𝒰₀' x')
    (hD : (∃ D : ListingRel h.toRingHom T, ∀ j x' x, r'.fst (col j) = Sum.inr x' →
        r.fst (col j) = Sum.inr x → D.Member x' x ∧ x'.fam = x.fam)
      ∨ (∃ O O', NestRel h.toRingHom O' O ∧ ∀ j x' x, r'.fst (col j) = Sum.inr x' →
        r.fst (col j) = Sum.inr x → NestMember O' O x' x ∧ x'.fam = x.fam)) :
    ∀ j x' x, r'.fst (col j) = Sum.inr x' → r.fst (col j) = Sum.inr x →
      x'.fam = x.fam ∧ ClassPres h 𝒰₀ 𝒰₀' x := by
  have heq : ∀ j x' x, r'.fst (col j) = Sum.inr x' → r.fst (col j) = Sum.inr x →
      x'.fam = x.fam := by
    rcases hD with ⟨D, hD⟩ | ⟨O, O', -, hN⟩
    · exact fun j x' x h1 h2 => (hD j x' x h1 h2).2
    · exact fun j x' x h1 h2 => (hN j x' x h1 h2).2
  intro j x' x h1 h2
  refine ⟨heq j x' x h1 h2, classPres_row hU r' r col lab key ps hW hz hz' heq ?_ j h2⟩
  rcases hD with ⟨D, hD⟩ | ⟨O, O', hO, hN⟩
  · exact Or.inl ⟨D, fun j x' x h1 h2 => (hD j x' x h1 h2).1⟩
  · exact Or.inr ⟨O, O', hO, fun j x' x h1 h2 => (hN j x' x h1 h2).1⟩

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- **The columns of one group of a grouping are presented by one
listing.** -/
theorem ListingRel.group_D (h : SemiringWithMonusHom K K') {c m n₂ : ℕ}
    (fs : Fin n₂ → SeqAggFunc T) (ts : Fin n₂ → TermIn T c m)
    (keep : Fin n₂ → Option (Selection T m)) (sc : Bool) (γ : Fin c → T)
    (U₀ : List (AnnotatedTuple T K m)) (U₀' : List (AnnotatedTuple T K' m))
    (hp : TiePerm (fun p q : AnnotatedTuple T K' m => p.fst = q.fst)
      (U₀.map (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) U₀') :
    ∃ D : ListingRel h.toRingHom T, ∀ (j : Fin n₂) (φ φ' : FamId T),
      D.Member ((groupTok (fs j) (ts j) (keep j) sc U₀' γ).setFam φ')
        ((groupTok (fs j) (ts j) (keep j) sc U₀ γ).setFam φ) := by
  obtain ⟨D, hD⟩ := ListingRel.exists_group h.toRingHom U₀ U₀' hp
  exact ⟨D, fun j φ φ' => hD _ _ (groupSpec (fs j) (ts j) γ sc (keep j)) _ _
    (by cases keep j <;> rfl) (by cases keep j <;> rfl)
    (flatExpr_groupTok _ _ _ _ _ _ _) (flatExpr_groupTok _ _ _ _ _ _ _)⟩

omit [DecidableEq K'] [HasAltLinearOrder K'] [CommSemiringWithMonus K'] [DecidableEq K] in
/-- The column a window adds holds the value it builds. -/
theorem ValueFrame.windowGenRow_last {c n m p : ℕ} (lab : ℕ) (ck : List (T ⊕ FamId T))
    (κ : Fin n → ColKind) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T) (keep : Option (Selection T n))
    (X : AnnotatedRelation T K n) (x : GenRow T K n) (γ : Fin c → T) (dist : Bool) :
    ∃ y, (ValueFrame.windowGenRow lab ck κ P O o w t f keep X x γ dist).fst (Fin.last n)
        = Sum.inr y ∧ y.fam = .mk lab (List.ofFn (GenRow.readAnnotated κ x).fst) ck 0 [] := by
  unfold ValueFrame.windowGenRow
  exact ⟨_, Fin.snoc_last (α := fun _ => GenValue T K) _ _, AggTok.fam_setFam _ _⟩

/-- **The joint row-wise simulation, over the universes of the
evaluation.** -/
theorem AggQueryIn.evaluate_hom_univ (h : SemiringWithMonusHom K K') {𝒰₀ : AggTok T K → Prop}
    {𝒰₀' : AggTok T K' → Prop} {W : List (ℕ × ℕ)} (hU : HomUniv 𝒰₀ 𝒰₀' W) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (d : AnnotatedDatabase T K) (γ : Fin c → T) (E' : EvalEnv T K') (E : EvalEnv T K),
      E'.HomSim h E γ → EnvG h 𝒰₀ 𝒰₀' γ E' E l →
      (∀ x, q.Builds d γ E x → 𝒰₀ x) →
      (∀ x, q.Builds (h.mapAnnotatedDatabase d) γ E' x → 𝒰₀' x) →
      (∀ e ∈ q.labWidths, e ∈ W) →
      q.framesContainSelf → q.nestInComplemented (K := K') → q.sourceCols →
      q.AnnSettlesAt d γ E →
      Multiset.Rel (fun r' r => GenRow.Sim h r' r ∧ RowG h 𝒰₀ 𝒰₀' r' r)
        (q.evaluate (h.mapAnnotatedDatabase d) γ E')
        (q.evaluate d γ E) := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate, SemiringWithMonusHom.find_mapAnnotatedDatabase]
    cases hf : d.find n s with
    | none =>
      simp only [Option.map_none]
      exact Multiset.Rel.zero
    | some rn =>
      simp only [Option.map_some]
      exact rel_ofAnnotated_mapG h 𝒰₀ 𝒰₀' rn
  | Hole n s κ =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    exact rel_filter_of_iff (hJ.holes s n (List.mem_singleton_self _))
      (fun r' r hs => forall_congr' fun k => by rw [(hs.1.1 k).kindOf_eq])
  | Param pv ρ =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    refine (hE.paramRows pv ρ).mono (fun r' hr' r hr hs => ⟨hs, fun q hq => ?_⟩)
    obtain ⟨k, h1, h2⟩ := hq
    simp only [EvalEnv.paramRows] at hr hr'
    split_ifs at hr hr' <;> simp only [Multiset.mem_singleton, Multiset.notMem_zero] at hr hr'
    subst hr hr'
    dsimp only at h1 h2
    cases hpv : pv k with
    | inl a => rw [hpv] at h2; exact absurd h2 (by simp)
    | inr j =>
      rw [hpv] at h1 h2
      exact hJ.ctx j _ _ h1 h2
  | Empty =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    exact Multiset.Rel.zero
  | Proj ps q ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    refine rel_map_of_rel (ih d γ E' E hE hJ hb hb' hW hw hn hsc.2 hrec)
      (fun r' r hs => ⟨⟨fun j => (ps j).equiv_eval_of_sim h hs.1.1, ?_⟩, ?_⟩)
    · rw [GenAnn.finalize_cash _ _ _ Multiset.inter_le_left,
        GenAnn.finalize_cash _ _ _ Multiset.inter_le_left]
      exact hs.1.2
    · exact fun p ⟨j, h1, h2⟩ => (ps j).pair_eval (hsc.1 j) _
        (fun x' x t hp => pairG_postcompTerm t hp) hs.2 h1 h2
  | Sel φ q hφ ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    by_cases hagg : φ.hasAggAtom
    · rw [ite_eq_left hagg, ite_eq_left hagg]
      refine Multiset.rel_map.mpr ((ih d γ E' E hE hJ hb hb' hW hw hn hsc hrec).mono
        (fun r' hr' r hr hs => ⟨⟨hs.1.1, ?_⟩, hs.2⟩))
      dsimp only
      rw [GenAnn.finalize_sel φ r'.fst r'.snd.base r'.snd.pending _ _
          (fun k hk a hka => (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [hka]⟩)
          (fun k hk a hka hsc => (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [hka, hsc]⟩)
          ?_,
        GenAnn.finalize_sel φ r.fst r.snd.base r.snd.pending _ _
          (fun k hk a hka => (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [hka]⟩)
          (fun k hk a hka hsc => (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [hka, hsc]⟩)
          ?_]
      · have hin := q.rowToks_in hsc d γ E 𝒰₀ hb hJ.toks
        have hin' := q.rowToks_in hsc (h.mapAnnotatedDatabase d) γ E' 𝒰₀' hb' hJ.toks'
        rw [GenPredIn.predsemJ_hom_famPres h φ false hs.1.1
          (famPres_of_good hU (S := rowPairs r'.fst r.fst) (fun p ⟨k, h1, h2⟩ =>
            ⟨⟨hin' r' hr' k _ h1, hin r hr k _ h2, (hs.2 p ⟨k, h1, h2⟩).1⟩,
              (hs.2 p ⟨k, h1, h2⟩).2⟩)), hs.1.2, ← map_mul]
      all_goals
        intro l hl
        obtain ⟨k, hk, hkl⟩ := (Multiset.mem_filterMap _ _).mp hl
        refine ⟨k, Finset.mem_val.mp hk, ?_⟩
        split at hkl
        · exact absurd hkl (by simp)
        · exact ⟨_, by assumption⟩
    · rw [ite_eq_right hagg, ite_eq_right hagg]
      refine rel_filter_of_iff (ih d γ E' E hE hJ hb hb' hW hw hn hsc hrec)
        (fun r' r hs => ?_)
      calc φ.holds r'.fst γ
          ↔ φ.holds (fun k => AggValue.mapAnnSum ⇑h.toRingHom (r.fst k)) γ :=
            GenPredIn.holds_equiv _ hs.1.1
        _ ↔ φ.holds r.fst γ := GenPredIn.holds_mapAnnSum h φ r.fst
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    refine rel_map_of_rel (rel_product
      (ih₁ d γ E' E hE (hJ.sub (List.subset_append_left _ _)) (fun x h => hb x (Or.inl h))
        (fun x h => hb' x (Or.inl h)) (fun e he => hW e (List.mem_append_left _ he))
        hw.1 hn.1 hsc.1 hrec.1)
      (ih₂ d γ E' E hE (hJ.sub (List.subset_append_right _ _)) (fun x h => hb x (Or.inr h))
        (fun x h => hb' x (Or.inr h)) (fun e he => hW e (List.mem_append_right _ he))
        hw.2 hn.2 hsc.2 hrec.2)) ?_
    rintro ⟨x', y'⟩ ⟨x, y⟩ ⟨hx, hy⟩
    refine ⟨⟨?_, ?_⟩, RowG.append hx.2 hy.2 _ _⟩
    · intro k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · show GenValue.Equiv (Fin.append x'.fst y'.fst (Fin.castAdd _ j))
          (AggValue.mapAnnSum ⇑h.toRingHom
            (Fin.append x.fst y.fst (Fin.castAdd _ j)))
        rw [Fin.append_left, Fin.append_left]
        exact hx.1.1 j
      · show GenValue.Equiv (Fin.append x'.fst y'.fst (Fin.natAdd _ j))
          (AggValue.mapAnnSum ⇑h.toRingHom
            (Fin.append x.fst y.fst (Fin.natAdd _ j)))
        rw [Fin.append_right, Fin.append_right]
        exact hy.1.1 j
    · show GenAnn.finalize ⟨x'.snd.base * y'.snd.base,
          x'.snd.pending + y'.snd.pending⟩ = _
      rw [GenAnn.finalize_prod, GenAnn.finalize_prod, hx.1.2, hy.1.2, ← map_mul]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    exact Multiset.Rel.add
      (ih₁ d γ E' E hE (hJ.sub (List.subset_append_left _ _)) (fun x h => hb x (Or.inl h))
        (fun x h => hb' x (Or.inl h)) (fun e he => hW e (List.mem_append_left _ he))
        hw.1 hn.1 hsc.1 hrec.1)
      (ih₂ d γ E' E hE (hJ.sub (List.subset_append_right _ _)) (fun x h => hb x (Or.inr h))
        (fun x h => hb' x (Or.inr h)) (fun e he => hW e (List.mem_append_right _ he))
        hw.2 hn.2 hsc.2 hrec.2)
  | Dedup q ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    rw [show (q.evaluate
          (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q.evaluate d γ E).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih d γ E' E hE hJ hb hb' hW hw hn hsc hrec)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)]
    rw [groupByKey_mapAnnotatedRelation]
    exact rel_ofAnnotated_mapG h 𝒰₀ 𝒰₀' _
  | Explode k hk q ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    refine rel_bind_of_rel (ih d γ E' E hE hJ hb hb' hW hw hn hsc hrec)
      (fun r' r hs => (sim_alternativesAt h hs.1 k).mono (fun a' ha' a ha hsa =>
        ⟨hsa, fun p ⟨j, h1, h2⟩ => hs.2 p ⟨j, GenRow.inr_of_mem_alternativesAt ha' h1,
          GenRow.inr_of_mem_alternativesAt ha h2⟩⟩))
  | Retag hκ q ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    exact ih d γ E' E hE hJ hb hb' hW hw hn hsc hrec
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    rw [show (q₁.evaluate
          (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q₁.evaluate d γ E).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih₁ d γ E' E hE hJ (fun x h => hb x (Or.inl h))
          (fun x h => hb' x (Or.inl h)) (fun e he => hW e (List.mem_append_left _ he))
          hw.1 hn.1 hsc.1 hrec.1)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)]
    rw [show (q₂.evaluate
          (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q₂.evaluate d γ E).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih₂ d γ E' E hE hJ (fun x h => hb x (Or.inr h))
          (fun x h => hb' x (Or.inr h)) (fun e he => hW e (List.mem_append_right _ he))
          hw.2 hn.2 hsc.2 hrec.2)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)]
    set X₁ : AnnotatedRelation T K _ := (q₁.evaluate d γ E).map GenRow.toAnnotated
    set X₂ : AnnotatedRelation T K _ := (q₂.evaluate d γ E).map GenRow.toAnnotated
    clear_value X₁ X₂
    rw [show SemiringWithMonusHom.mapAnnotatedRelation h X₁
        = X₁.map (SemiringWithMonusHom.mapAnnotatedTuple h) from rfl]
    simp only [Multiset.map_map]
    refine rel_map_of_forall (fun p _ => ?_)
    obtain ⟨u, α⟩ := p
    refine ⟨⟨fun k => rfl, ?_⟩, RowG.of_noPairs (fun q ⟨k, _, h2⟩ => Sum.inl_ne_inr h2)⟩
    dsimp only [Function.comp, GenRow.ofAnnotated,
      SemiringWithMonusHom.mapAnnotatedTuple]
    rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero,
      SemiringWithMonusHom.map_sub]
    congr 1
    rw [groupByKey_find_eq_filter_sum, groupByKey_find_eq_filter_sum]
    exact SemiringWithMonusHom.sum_filter_map_snd_mapAnnotatedRelation h u X₂
  | @ProvSum cI m n₁ κ' is his t q ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    rw [show (q.evaluate (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q.evaluate d γ E).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih d γ E' E hE hJ hb hb' hW hw hn hsc hrec)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)]
    set X : AnnotatedRelation T K m := (q.evaluate d γ E).map GenRow.toAnnotated
    clear_value X
    rw [show SemiringWithMonusHom.mapAnnotatedRelation h X
        = X.map (SemiringWithMonusHom.mapAnnotatedTuple h) from rfl]
    rw [show ((X.map (SemiringWithMonusHom.mapAnnotatedTuple h)).map
          (fun p => (fun k => p.fst (is k) : Tuple T n₁))).dedup
        = ((X.map (fun p => (fun k => p.fst (is k) : Tuple T n₁)))).dedup from by
      rw [Multiset.map_map]
      exact congrArg Multiset.dedup
        (Multiset.map_congr rfl (fun p _ => rfl))]
    refine rel_map_of_forall (fun g _ => ⟨⟨?_, ?_⟩, RowG.of_noPairs ?_⟩)
    · intro k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · dsimp only
        rw [Fin.append_left, Fin.append_left]
        rfl
      · dsimp only
        rw [Fin.append_right, Fin.append_right]
        rw [show Multiset.filter
              (fun p : AnnotatedTuple T K' m =>
                ∀ k' : Fin n₁, p.fst (is k') = g k')
              (X.map (SemiringWithMonusHom.mapAnnotatedTuple h))
            = (X.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
                (SemiringWithMonusHom.mapAnnotatedTuple h) from by
          rw [Multiset.filter_map]
          exact congrArg _ (Multiset.filter_congr (fun p _ => Iff.rfl))]
        rw [Multiset.map_map]
        rw [show Multiset.map ((fun p : AnnotatedTuple T K' m =>
              t.evalPlain p.fst γ) ∘ SemiringWithMonusHom.mapAnnotatedTuple h)
              (X.filter (fun p : AnnotatedTuple T K m =>
                ∀ k' : Fin n₁, p.fst (is k') = g k'))
            = Multiset.map
              (fun p : AnnotatedTuple T K m => t.evalPlain p.fst γ)
              (X.filter (fun p : AnnotatedTuple T K m =>
                ∀ k' : Fin n₁, p.fst (is k') = g k'))
            from Multiset.map_congr rfl (fun p _ => rfl)]
        rfl
    · show GenAnn.finalize ⟨_, 0⟩ = h.toRingHom (GenAnn.finalize ⟨_, 0⟩)
      rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero]
      rw [show Multiset.filter
            (fun p : AnnotatedTuple T K' m =>
              ∀ k' : Fin n₁, p.fst (is k') = g k')
            (X.map (SemiringWithMonusHom.mapAnnotatedTuple h))
          = (X.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
              (SemiringWithMonusHom.mapAnnotatedTuple h) from by
        rw [Multiset.filter_map]
        exact congrArg _ (Multiset.filter_congr (fun p _ => Iff.rfl))]
      rw [Multiset.map_map]
      rw [show Multiset.map (Prod.snd ∘ SemiringWithMonusHom.mapAnnotatedTuple h)
            (X.filter (fun p : AnnotatedTuple T K m =>
              ∀ k' : Fin n₁, p.fst (is k') = g k'))
          = Multiset.map (⇑h.toRingHom ∘ Prod.snd)
            (X.filter (fun p : AnnotatedTuple T K m =>
              ∀ k' : Fin n₁, p.fst (is k') = g k'))
          from Multiset.map_congr rfl (fun p _ => rfl)]
      rw [← Multiset.map_map]
      exact Multiset.sum_hom _ h.toRingHom
    · rintro p ⟨k, -, h2⟩
      dsimp only at h2
      refine Fin.addCases (fun i h2 => ?_) (fun j h2 => ?_) k h2
      · rw [Fin.append_left] at h2; exact Sum.inl_ne_inr h2
      · rw [Fin.append_right] at h2; exact Sum.inl_ne_inr h2
  | @Apply cA nA₁ nA₂ κA₁ κA₂ lA q₁ q₂ ih₁ ih₂ =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    have hin₁ := q₁.rowToks_in hsc.1 d γ E 𝒰₀ (fun x h => hb x (Or.inl h)) hJ.toks
    have hin₁' := q₁.rowToks_in hsc.1 (h.mapAnnotatedDatabase d) γ E' 𝒰₀'
      (fun x h => hb' x (Or.inl h)) hJ.toks'
    refine rel_bind ((ih₁ d γ E' E hE hJ (fun x h => hb x (Or.inl h))
        (fun x h => hb' x (Or.inl h)) (fun e he => hW e (List.mem_append_left _ he))
        hw.1 hn.1 hsc.1 hrec.1).mono
      (p := fun x' x => (GenRow.Sim h x' x ∧ RowG h 𝒰₀ 𝒰₀' x' x)
        ∧ x' ∈ q₁.evaluate (h.mapAnnotatedDatabase d) γ E' ∧ x ∈ q₁.evaluate d γ E)
      (fun x' hx' x hx hs => ⟨hs, hx', hx⟩)) (fun x' x hxx' => ?_)
    obtain ⟨hxx, hxm', hxm⟩ := hxx'
    have hplain : GenRow.plainTuple x'.fst = GenRow.plainTuple x.fst := by
      funext k
      exact (hxx.1.1 k).collapseSum_eq.trans
        (AggValue.collapseSum_mapAnnSum ⇑h.toRingHom (x.fst k))
    -- the right side reads the left row's values as its context
    have hJx : EnvG h 𝒰₀ 𝒰₀' (Fin.append (GenRow.plainTuple x.fst) γ)
        (E'.withCtx (Fin.append x'.fst (E'.ctxAt _ γ)))
        (E.withCtx (Fin.append x.fst (E.ctxAt _ γ))) [] := by
      refine ⟨fun k y' y h1 h2 => ?_, fun _ _ h' => absurd h' (by simp), fun z hz => ?_,
        fun z hz => ?_⟩
      · rw [EvalEnv.ctxAt_withCtx] at h1 h2
        revert h1 h2
        refine Fin.addCases (fun i h1 h2 => ?_) (fun j h1 h2 => ?_) k
        · rw [Fin.append_left] at h1 h2; exact hxx.2 (y', y) ⟨i, h1, h2⟩
        · rw [Fin.append_right] at h1 h2; exact hJ.ctx j _ _ h1 h2
      · rcases hz with ⟨k, hk⟩ | ⟨p, hp, -⟩
        · rw [EvalEnv.ctxAt_withCtx] at hk
          revert hk
          refine Fin.addCases (fun i hk => ?_) (fun j hk => ?_) k
          · rw [Fin.append_left] at hk; exact hin₁ x hxm i z hk
          · rw [Fin.append_right] at hk; exact hJ.toks z (Or.inl ⟨j, hk⟩)
        · exact absurd hp List.not_mem_nil
      · rcases hz with ⟨k, hk⟩ | ⟨p, hp, -⟩
        · rw [EvalEnv.ctxAt_withCtx] at hk
          revert hk
          refine Fin.addCases (fun i hk => ?_) (fun j hk => ?_) k
          · rw [Fin.append_left] at hk; exact hin₁' x' hxm' i z hk
          · rw [Fin.append_right] at hk; exact hJ.toks' z (Or.inl ⟨j, hk⟩)
        · exact absurd hp List.not_mem_nil
    rw [hplain]
    refine rel_map_of_rel
      (ih₂ d (Fin.append (GenRow.plainTuple x.fst) γ) _ _ (hE.enter hxx.1.1 _) hJx
        (fun z hz => hb z (Or.inr ⟨x, hxm, hz⟩))
        (fun z hz => hb' z (Or.inr ⟨x', hxm', by rw [hplain]; exact hz⟩))
        (fun e he => hW e (List.mem_append_right _ he)) hw.2 hn.2 hsc.2 (hrec.2 x hxm))
      (fun y' y hy => ⟨⟨?_, ?_⟩, RowG.append hxx.2 hy.2 _ _⟩)
    · intro k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · show GenValue.Equiv (Fin.append x'.fst y'.fst (Fin.castAdd _ j))
          (AggValue.mapAnnSum ⇑h.toRingHom
            (Fin.append x.fst y.fst (Fin.castAdd _ j)))
        rw [Fin.append_left, Fin.append_left]
        exact hxx.1.1 j
      · show GenValue.Equiv (Fin.append x'.fst y'.fst (Fin.natAdd _ j))
          (AggValue.mapAnnSum ⇑h.toRingHom
            (Fin.append x.fst y.fst (Fin.natAdd _ j)))
        rw [Fin.append_right, Fin.append_right]
        exact hy.1.1 j
    · show GenAnn.finalize ⟨x'.snd.base * y'.snd.base,
          x'.snd.pending + y'.snd.pending⟩ = _
      rw [GenAnn.finalize_prod, GenAnn.finalize_prod, hxx.1.2, hy.1.2, ← map_mul]
  | @Mu cM nM κM s q₀ q₁ ih₀ ih₁ =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    simp only [AggQueryIn.evaluate]
    refine muSumFix_rel_it
      (ih₀ d γ E' E hE hJ (fun x h => hb x (Or.inl h)) (fun x h => hb' x (Or.inl h))
        (fun e he => hW e (List.mem_append_left _ he)) hw.1 hn.1 hsc.1 hrec.1)
      (fun k hX => ?_)
    have hJk : EnvG h 𝒰₀ 𝒰₀' γ
        (E'.assignHole s ((AggQueryIn.muStep s q₁ (h.mapAnnotatedDatabase d) γ E')^[k]
          (q₀.evaluate (h.mapAnnotatedDatabase d) γ E')))
        (E.assignHole s ((AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E)))
        [(s, nM)] := by
      refine ⟨fun j x' x h1 h2 => ?_, fun s' m' hsm => ?_, fun z hz => ?_, fun z hz => ?_⟩
      · rw [EvalEnv.ctxAt_assignHole] at h1 h2
        exact hJ.ctx j x' x h1 h2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hsm)
        simp only [EvalEnv.assignHole, and_self, ↓reduceDIte]
        exact hX
      · rcases hz with ⟨j, hj⟩ | ⟨p, hp, r, hr, j, hj⟩
        · rw [EvalEnv.ctxAt_assignHole] at hj
          exact hJ.toks z (Or.inl ⟨j, hj⟩)
        · obtain rfl := List.mem_singleton.mp hp
          simp only [EvalEnv.assignHole, and_self, ↓reduceDIte] at hr
          exact ((q₀.muRoundToks s q₁ hsc d γ E k r hr j z hj).mono (fun w hw' =>
            hw'.elim (fun h' => TermCl.base (hb w h')) (fun h' => hJ.toks w h'))).idem
      · rcases hz with ⟨j, hj⟩ | ⟨p, hp, r, hr, j, hj⟩
        · rw [EvalEnv.ctxAt_assignHole] at hj
          exact hJ.toks' z (Or.inl ⟨j, hj⟩)
        · obtain rfl := List.mem_singleton.mp hp
          simp only [EvalEnv.assignHole, and_self, ↓reduceDIte] at hr
          exact ((q₀.muRoundToks s q₁ hsc (h.mapAnnotatedDatabase d) γ E' k r hr j z
            hj).mono (fun w hw' =>
              hw'.elim (fun h' => TermCl.base (hb' w h')) (fun h' => hJ.toks' w h'))).idem
    exact ih₁ d γ _ _ (hE.assignHole s (hX.mono (fun _ _ _ _ h' => h'.1))) hJk
      (fun x h' => hb x (Or.inr ⟨k, h'⟩)) (fun x h' => hb' x (Or.inr ⟨k, h'⟩))
      (fun e he => hW e (List.mem_append_right _ he)) hw.2 hn.2 hsc.2 (hrec.2.2.2.1 k)
  | @MuSet cM nM s q₀ q₁ ih₀ ih₁ =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    show Multiset.Rel _
      ((muFix (AggQueryIn.muSetStep s q₀ q₁ (h.mapAnnotatedDatabase d) γ E')).map
        GenRow.ofAnnotated)
      ((muFix (AggQueryIn.muSetStep s q₀ q₁ d γ E)).map GenRow.ofAnnotated)
    have e₀ : q₀.evaluateAnnotated (h.mapAnnotatedDatabase d) γ E'
        = SemiringWithMonusHom.mapAnnotatedRelation h (q₀.evaluateAnnotated d γ E) :=
      (map_eq_of_rel (ih₀ d γ E' E hE hJ (fun x h => hb x (Or.inl h))
          (fun x h => hb' x (Or.inl h)) (fun e he => hW e (List.mem_append_left _ he))
          hw.1 hn.1 hsc.1 hrec.1)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)).trans
        (Multiset.map_map (SemiringWithMonusHom.mapAnnotatedTuple h) GenRow.toAnnotated
          (q₀.evaluate d γ E)).symm
    have hJX : ∀ X : AnnotatedRelation T K nM, EnvG h 𝒰₀ 𝒰₀' γ
        (E'.assignHole s ((SemiringWithMonusHom.mapAnnotatedRelation h X).map
          GenRow.ofAnnotated))
        (E.assignHole s (X.map GenRow.ofAnnotated)) [(s, nM)] := by
      intro X
      refine ⟨fun j x' x h1 h2 => ?_, fun s' m' hsm => ?_, fun z hz => ?_, fun z hz => ?_⟩
      · rw [EvalEnv.ctxAt_assignHole] at h1 h2
        exact hJ.ctx j x' x h1 h2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hsm)
        simp only [EvalEnv.assignHole, and_self, ↓reduceDIte]
        exact rel_ofAnnotated_mapG h 𝒰₀ 𝒰₀' X
      · rcases hz with ⟨j, hj⟩ | ⟨p, hp, r, hr, j, hj⟩
        · rw [EvalEnv.ctxAt_assignHole] at hj
          exact hJ.toks z (Or.inl ⟨j, hj⟩)
        · obtain rfl := List.mem_singleton.mp hp
          simp only [EvalEnv.assignHole, and_self, ↓reduceDIte] at hr
          obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hr
          exact absurd hj (by simp [GenRow.ofAnnotated])
      · rcases hz with ⟨j, hj⟩ | ⟨p, hp, r, hr, j, hj⟩
        · rw [EvalEnv.ctxAt_assignHole] at hj
          exact hJ.toks' z (Or.inl ⟨j, hj⟩)
        · obtain rfl := List.mem_singleton.mp hp
          simp only [EvalEnv.assignHole, and_self, ↓reduceDIte] at hr
          obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hr
          exact absurd hj (by simp [GenRow.ofAnnotated])
    have hstepOf : ∀ k, SemiringWithMonusHom.mapAnnotatedRelation h
          (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)
          = muIter (AggQueryIn.muSetStep s q₀ q₁ (h.mapAnnotatedDatabase d) γ E') k →
        SemiringWithMonusHom.mapAnnotatedRelation h
          (AggQueryIn.muSetStep s q₀ q₁ d γ E
            (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k))
        = AggQueryIn.muSetStep s q₀ q₁ (h.mapAnnotatedDatabase d) γ E'
            (SemiringWithMonusHom.mapAnnotatedRelation h
              (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)) := by
      intro k hik
      have e₁ : q₁.evaluateAnnotated (h.mapAnnotatedDatabase d) γ (E'.assignHole s
            ((SemiringWithMonusHom.mapAnnotatedRelation h
              (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)).map GenRow.ofAnnotated))
          = SemiringWithMonusHom.mapAnnotatedRelation h
            (q₁.evaluateAnnotated d γ (E.assignHole s
              ((muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k).map GenRow.ofAnnotated))) :=
        (map_eq_of_rel (ih₁ d γ _ _ (hE.assignHole s (rel_ofAnnotated_map h _)) (hJX _)
            (fun x h' => hb x (Or.inr ⟨k, h'⟩))
            (fun x h' => hb' x (Or.inr ⟨k, by rw [← hik]; exact h'⟩))
            (fun e he => hW e (List.mem_append_right _ he)) hw.2 hn.2 hsc.2 (hrec.2.2 k))
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)).trans
          (Multiset.map_map (SemiringWithMonusHom.mapAnnotatedTuple h) GenRow.toAnnotated _).symm
      clear hik
      generalize muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k = X at e₁ ⊢
      unfold AggQueryIn.muSetStep
      rw [dedupAnn_mapAnnotatedRelation, mapAnnotatedRelation_add, e₀, e₁]
    have hiter : ∀ k, SemiringWithMonusHom.mapAnnotatedRelation h
          (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)
          = muIter (AggQueryIn.muSetStep s q₀ q₁ (h.mapAnnotatedDatabase d) γ E') k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [muIter, muIter, hstepOf k ih, ih]
    rw [← muFix_map_rounds (h := SemiringWithMonusHom.mapAnnotatedRelation h) rfl
      (fun k => hstepOf k (hiter k)) hrec.2.1]
    exact rel_ofAnnotated_mapG h 𝒰₀ 𝒰₀' _
  | @Gamma cI mI nI₁ nI₂ lab rd is ts fs q keep ord ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    have hpk := EvalEnv.paramKey_eq_of_envG hE hJ rd
    have hsim : Multiset.Rel (fun r' r => GenRow.Sim h r' r ∧ ∃ D : ListingRel h.toRingHom T,
        ∀ j x' x, r'.fst (Fin.natAdd nI₁ j) = Sum.inr x' → r.fst (Fin.natAdd nI₁ j) = Sum.inr x →
          D.Member x' x ∧ x'.fam = x.fam)
        ((AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).evaluate
          (h.mapAnnotatedDatabase d) γ E')
        ((AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).evaluate d γ E) := by
      simp only [AggQueryIn.evaluate]
      rw [show (q.evaluate
            (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
          = ((q.evaluate d γ E).map GenRow.toAnnotated).map
              (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI))
          from by
        have h1 : (q.evaluate
              (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
            = ((q.evaluate d γ E).map GenRow.toAnnotated).map
                (SemiringWithMonusHom.mapAnnotatedTuple h) := by
          rw [Multiset.map_map]
          exact map_eq_of_rel (ih d γ E' E hE hJ (fun x h => hb x (Or.inr h))
            (fun x h => hb' x (Or.inr h))
            (fun e he => hW e
                (by rw [AggQueryIn.labWidths]; exact mem_labCons_of_mem he)) hw hn hsc hrec)
            (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)
        exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))]
      set X : AnnotatedRelation T K mI := (q.evaluate d γ E).map GenRow.toAnnotated
      clear_value X
      rw [show (X.map (fun p =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI))).map
            (fun p => (fun k => p.fst (is k), p.snd)
              : AnnotatedTuple T K' mI → AnnotatedTuple T K' nI₁)
          = (X.map (fun p => (fun k => p.fst (is k), p.snd)
              : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁)).map
              (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI₁))
          from by
        rw [Multiset.map_map, Multiset.map_map]
        exact Multiset.map_congr rfl (fun p _ => rfl)]
      rw [show (Multiset.ofList (groupByKey ((X.map
            (fun p => (fun k => p.fst (is k), p.snd)
              : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁)).map
            (fun p => ((p.fst, h.toRingHom p.snd)
              : AnnotatedTuple T K' nI₁)))).val
            : Multiset (AnnotatedTuple T K' nI₁))
          = (Multiset.ofList (groupByKey (X.map
              (fun p => (fun k => p.fst (is k), p.snd)
                : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁))).val).map
              (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI₁))
          from by
        rw [show (X.map (fun p => (fun k => p.fst (is k), p.snd)
              : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁)).map
              (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI₁))
            = SemiringWithMonusHom.mapAnnotatedRelation h (X.map
                (fun p => (fun k => p.fst (is k), p.snd)
                  : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁))
            from Multiset.map_congr rfl (fun p _ => rfl),
          groupByKey_mapAnnotatedRelation]
        exact Multiset.map_congr rfl (fun p _ => rfl)]
      rw [Multiset.map_map]
      refine rel_map_of_forall (fun kv _ => ?_)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro k
        dsimp only [Function.comp]
        refine Fin.addCases (fun j => ?_) (fun j => ?_) k
        · rw [Fin.append_left, Fin.append_left]
          rfl
        · rw [Fin.append_right, Fin.append_right]
          cases hkj : keep j with
          | none =>
            exact ⟨rfl, rfl, TiePerm.symm (fun e => e.symm)
              (ofGroupOrd_mapAnn_tiePerm h (fs j) (ts j) is ord X kv.fst)⟩
          | some φ =>
            -- a filtered aggregate's column is an expression over the whole
            -- group, and the two groups are tie-permuted
            exact exprGroupWhenOrd_mapAnn_equiv h (fs j) (ts j) φ.keeps is ord X
              kv.fst
      · dsimp only [Function.comp]
        rw [GenAnn.finalize_gamma, GenAnn.finalize_gamma,
          havingGroupOrd_annSum_hom h is ord X kv.fst,
          SemiringWithMonusHom.map_delta]
      · dsimp only [Function.comp]
        rw [hpk]
        obtain ⟨D, hD⟩ := ListingRel.group_D h fs ts keep false γ _ _
          (havingGroupOrd_tiePerm h is ord X kv.fst)
        refine ⟨D, fun j x' x h1 h2 => ?_⟩
        rw [Fin.append_right] at h1 h2
        have e1 := (Sum.inr_injective h1).symm
        have e2 := (Sum.inr_injective h2).symm
        subst e1 e2
        refine ⟨?_, by simp only [AggTok.fam_setFam]⟩
        convert hD j _ _ using 2 <;> cases keep j <;> rfl
    refine hsim.mono (fun r' hr' r hr hs => ⟨hs.1, ?_⟩)
    obtain ⟨key, hkey0, hkey⟩ := AggQueryIn.newRow_Gamma is ts fs q keep ord d γ E hr
    obtain ⟨key', -, hkey'⟩ := AggQueryIn.newRow_Gamma is ts fs q keep ord _ γ E' hr'
    have hfr := freshG hU r' r (Fin.natAdd nI₁) lab
      (fun hne => hW _ (by
        rw [AggQueryIn.labWidths, labCons_of_ne hne]; exact List.mem_cons_self)) key
      (E.paramKey rd γ)
      (fun j => let ⟨x, h1, h2⟩ := hkey j; ⟨x, h1, hb x (Or.inl ⟨r, hr, j, h1⟩), h2⟩)
      (fun j => let ⟨x, h1, _⟩ := hkey' j; ⟨x, h1, hb' x (Or.inl ⟨r', hr', j, h1⟩)⟩)
      (Or.inl hs.2)
    intro p ⟨k, h1, h2⟩
    revert h1 h2
    refine Fin.addCases (fun i h1 h2 => ?_) (fun j h1 h2 => hfr j _ _ h1 h2) k
    obtain ⟨v, hv⟩ := hkey0 i
    rw [hv] at h2
    exact absurd h2 (by simp)
  | @GammaTok cI mI nI₁ nI₂ κ' lab rd is his ts fs a q keep ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    have hpk := EvalEnv.paramKey_eq_of_envG hE hJ rd
    have hsim : Multiset.Rel (fun r' r => GenRow.Sim h r' r ∧ ∃ D : ListingRel h.toRingHom T,
        ∀ j x' x, r'.fst (Fin.castAdd 1 (Fin.natAdd nI₁ j)) = Sum.inr x' →
          r.fst (Fin.castAdd 1 (Fin.natAdd nI₁ j)) = Sum.inr x → D.Member x' x ∧ x'.fam = x.fam)
        ((AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).evaluate
          (h.mapAnnotatedDatabase d) γ E')
        ((AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).evaluate d γ E) := by
      simp only [AggQueryIn.evaluate]
      rw [show (q.evaluate
            (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
          = ((q.evaluate d γ E).map GenRow.toAnnotated).map
              (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI))
          from by
        have h1 : (q.evaluate
              (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
            = ((q.evaluate d γ E).map GenRow.toAnnotated).map
                (SemiringWithMonusHom.mapAnnotatedTuple h) := by
          rw [Multiset.map_map]
          exact map_eq_of_rel (ih d γ E' E hE hJ (fun x h => hb x (Or.inr h))
            (fun x h => hb' x (Or.inr h))
            (fun e he => hW e
                (by rw [AggQueryIn.labWidths]; exact mem_labCons_of_mem he)) hw hn hsc hrec)
            (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)
        exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))]
      set X : AnnotatedRelation T K mI := (q.evaluate d γ E).map GenRow.toAnnotated
      clear_value X
      rw [show (X.map (fun p =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI))).map
            (fun p => (fun k => p.fst (is k), p.snd)
              : AnnotatedTuple T K' mI → AnnotatedTuple T K' nI₁)
          = (X.map (fun p => (fun k => p.fst (is k), p.snd)
              : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁)).map
              (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI₁))
          from by
        rw [Multiset.map_map, Multiset.map_map]
        exact Multiset.map_congr rfl (fun p _ => rfl)]
      rw [show (Multiset.ofList (groupByKey ((X.map
            (fun p => (fun k => p.fst (is k), p.snd)
              : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁)).map
            (fun p => ((p.fst, h.toRingHom p.snd)
              : AnnotatedTuple T K' nI₁)))).val
            : Multiset (AnnotatedTuple T K' nI₁))
          = (Multiset.ofList (groupByKey (X.map
              (fun p => (fun k => p.fst (is k), p.snd)
                : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁))).val).map
              (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI₁))
          from by
        rw [show (X.map (fun p => (fun k => p.fst (is k), p.snd)
              : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁)).map
              (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI₁))
            = SemiringWithMonusHom.mapAnnotatedRelation h (X.map
                (fun p => (fun k => p.fst (is k), p.snd)
                  : AnnotatedTuple T K mI → AnnotatedTuple T K nI₁))
            from Multiset.map_congr rfl (fun p _ => rfl),
          groupByKey_mapAnnotatedRelation]
        exact Multiset.map_congr rfl (fun p _ => rfl)]
      rw [Multiset.map_map]
      refine rel_map_of_forall (fun kv _ => ?_)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro k
        dsimp only [Function.comp]
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · rw [Fin.append_left, Fin.append_left]
          refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
          · rw [Fin.append_left, Fin.append_left]
            rfl
          · rw [Fin.append_right, Fin.append_right]
            cases hkj : keep j' with
            | none =>
              exact ⟨rfl, rfl, TiePerm.symm (fun e => e.symm)
                (ofGroup_mapAnn_tiePerm h (fs j') (ts j') is X kv.fst)⟩
            | some φ =>
              -- as under `Gamma`: a filtered aggregate's column is an
              -- expression over the whole group, tie-permuted on both sides
              exact exprGroupWhen_mapAnn_equiv h (fs j') (ts j') φ.keeps is X
                kv.fst
        · rw [Fin.append_right, Fin.append_right]
          rw [show Multiset.filter
                (fun p : AnnotatedTuple T K' mI =>
                  ∀ k' : Fin nI₁, p.fst (is k') = kv.fst k')
                (X.map (fun p =>
                  ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI)))
              = (X.filter (fun p => ∀ k' : Fin nI₁, p.fst (is k') = kv.fst k')).map
                  (fun p =>
                    ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI)) from by
            rw [Multiset.filter_map]
            exact congrArg _ (Multiset.filter_congr (fun p _ => Iff.rfl))]
          rw [Multiset.map_map]
          rw [show Multiset.map ((fun p : AnnotatedTuple T K' mI =>
                a.evalPlain p.fst γ) ∘ (fun p : AnnotatedTuple T K mI =>
                  ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI)))
                (X.filter (fun p : AnnotatedTuple T K mI =>
                  ∀ k' : Fin nI₁, p.fst (is k') = kv.fst k'))
              = Multiset.map (fun p : AnnotatedTuple T K mI =>
                  a.evalPlain p.fst γ)
                (X.filter (fun p : AnnotatedTuple T K mI =>
                  ∀ k' : Fin nI₁, p.fst (is k') = kv.fst k'))
              from Multiset.map_congr rfl (fun p _ => rfl)]
          rfl
      · dsimp only [Function.comp]
        rw [GenAnn.finalize_gamma, GenAnn.finalize_gamma,
          havingGroup_annSum_hom h is X kv.fst,
          SemiringWithMonusHom.map_delta]
      · dsimp only [Function.comp]
        rw [hpk]
        obtain ⟨D, hD⟩ := ListingRel.group_D h fs ts keep false γ _ _
          (havingGroup_tiePerm h is X kv.fst)
        refine ⟨D, fun j x' x h1 h2 => ?_⟩
        rw [Fin.append_left, Fin.append_right] at h1 h2
        have e1 := (Sum.inr_injective h1).symm
        have e2 := (Sum.inr_injective h2).symm
        subst e1 e2
        refine ⟨?_, by simp only [AggTok.fam_setFam]⟩
        convert hD j _ _ using 2 <;> cases keep j <;> rfl
    refine hsim.mono (fun r' hr' r hr hs => ⟨hs.1, ?_⟩)
    obtain ⟨key, hkey0, hkey1, hkey⟩ := AggQueryIn.newRow_GammaTok is his ts fs a q keep d γ E hr
    obtain ⟨key', -, -, hkey'⟩ := AggQueryIn.newRow_GammaTok is his ts fs a q keep _ γ E' hr'
    have hfr := freshG hU r' r (fun j => Fin.castAdd 1 (Fin.natAdd nI₁ j)) lab
      (fun hne => hW _ (by
        rw [AggQueryIn.labWidths, labCons_of_ne hne]; exact List.mem_cons_self))
      key (E.paramKey rd γ)
      (fun j => let ⟨x, h1, h2⟩ := hkey j; ⟨x, h1, hb x (Or.inl ⟨r, hr, j, h1⟩), h2⟩)
      (fun j => let ⟨x, h1, _⟩ := hkey' j; ⟨x, h1, hb' x (Or.inl ⟨r', hr', j, h1⟩)⟩)
      (Or.inl hs.2)
    intro p ⟨k, h1, h2⟩
    revert h1 h2
    refine Fin.addCases (fun i h1 h2 => ?_) (fun i h1 h2 => ?_) k
    · revert h1 h2
      refine Fin.addCases (fun i' h1 h2 => ?_) (fun j h1 h2 => hfr j _ _ h1 h2) i
      obtain ⟨v, hv⟩ := hkey0 i'
      rw [hv] at h2
      exact absurd h2 (by simp)
    · obtain ⟨v, hv⟩ := hkey1 i
      rw [hv] at h2
      exact absurd h2 (by simp)
  | @GammaScalar cI mI nI₂ lab rd ts fs q ord ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    have hpk := EvalEnv.paramKey_eq_of_envG hE hJ rd
    have hsim : Multiset.Rel (fun r' r => GenRow.Sim h r' r ∧ ∃ D : ListingRel h.toRingHom T,
        ∀ j x' x, r'.fst j = Sum.inr x' → r.fst j = Sum.inr x → D.Member x' x ∧ x'.fam = x.fam)
        ((AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).evaluate
          (h.mapAnnotatedDatabase d) γ E')
        ((AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).evaluate d γ E) := by
      simp only [AggQueryIn.evaluate]
      rw [show (q.evaluate
            (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
          = ((q.evaluate d γ E).map GenRow.toAnnotated).map
              (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI))
          from by
        have h1 : (q.evaluate
              (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
            = ((q.evaluate d γ E).map GenRow.toAnnotated).map
                (SemiringWithMonusHom.mapAnnotatedTuple h) := by
          rw [Multiset.map_map]
          exact map_eq_of_rel (ih d γ E' E hE hJ (fun x h => hb x (Or.inr h))
            (fun x h => hb' x (Or.inr h))
            (fun e he => hW e
                (by rw [AggQueryIn.labWidths]; exact mem_labCons_of_mem he)) hw hn hsc hrec)
            (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)
        exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))]
      set X : AnnotatedRelation T K mI := (q.evaluate d γ E).map GenRow.toAnnotated
      clear_value X
      -- one row on each side, annotated `𝟙`, with nothing pending
      refine Multiset.Rel.cons ?_ Multiset.Rel.zero
      refine ⟨⟨fun k => ?_, by simp [GenAnn.finalize]⟩, ?_⟩
      exact ⟨rfl, rfl, TiePerm.symm (fun e => e.symm)
        (ofGroupOrd_mapAnn_tiePerm h (fs k) (ts k) (fun i : Fin 0 => i.elim0)
          ord X (fun i : Fin 0 => i.elim0))⟩
      · rw [hpk]
        obtain ⟨D, hD⟩ := ListingRel.group_D h fs ts (fun _ => none) true γ _ _
          (havingGroupOrd_tiePerm h (fun i : Fin 0 => i.elim0) ord X (fun i : Fin 0 => i.elim0))
        refine ⟨D, fun j x' x h1 h2 => ?_⟩
        have e1 := (Sum.inr_injective h1).symm
        have e2 := (Sum.inr_injective h2).symm
        subst e1 e2
        exact ⟨hD j _ _, by simp only [AggTok.fam_setFam]⟩
    refine hsim.mono (fun r' hr' r hr hs => ⟨hs.1, ?_⟩)
    obtain ⟨key, hkey⟩ := AggQueryIn.newRow_GammaScalar ts fs q ord d γ E hr
    obtain ⟨key', hkey'⟩ := AggQueryIn.newRow_GammaScalar ts fs q ord _ γ E' hr'
    have hfr := freshG hU r' r id lab
      (fun hne => hW _ (by
        rw [AggQueryIn.labWidths, labCons_of_ne hne]; exact List.mem_cons_self))
      key (E.paramKey rd γ)
      (fun j => let ⟨x, h1, h2⟩ := hkey j; ⟨x, h1, hb x (Or.inl ⟨r, hr, j, h1⟩), h2⟩)
      (fun j => let ⟨x, h1, _⟩ := hkey' j; ⟨x, h1, hb' x (Or.inl ⟨r', hr', j, h1⟩)⟩)
      (Or.inl hs.2)
    exact fun p ⟨k, h1, h2⟩ => hfr k _ _ h1 h2
  | @GammaNest cI mI nI₁ κ' lab rd is his p f q ih =>
    -- one output row per key, and the keys are the columns' deterministic
    -- values, which a simulation keeps. For one key the two groups are
    -- related row for row, so their occurrences carry pushed annotations
    -- and columns whose statistics agree – which is all a nested value
    -- reads of them (`GenValue.Equiv.of_nest_rel`), the weight splitting
    -- per occurrence because `K'` is complemented
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    have hpk := EvalEnv.paramKey_eq_of_envG hE hJ rd
    have hsim : Multiset.Rel (fun r' r => GenRow.Sim h r' r ∧ ∃ O O', NestRel h.toRingHom O' O ∧
        ∀ j x' x, r'.fst (Fin.natAdd nI₁ j) = Sum.inr x' → r.fst (Fin.natAdd nI₁ j) = Sum.inr x →
          NestMember O' O x' x ∧ x'.fam = x.fam)
        ((AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q).evaluate
          (h.mapAnnotatedDatabase d) γ E')
        ((AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q).evaluate d γ E) := by
      simp only [AggQueryIn.evaluate]
      have hrel := (ih d γ E' E hE hJ (fun x h => hb x (Or.inr h))
        (fun x h => hb' x (Or.inr h)) (fun e he => hW e (List.mem_cons_of_mem _ he)) hw hn.2
        hsc.2 hrec).mono
        (fun _ _ _ _ hs => hs.1)
      have hkey : ∀ (r' : GenRow T K' mI) (r : GenRow T K mI),
          GenRow.Sim h r' r →
          (fun k => AggValue.collapseSum (r'.fst (is k)) : Tuple T nI₁)
            = (fun k => AggValue.collapseSum (r.fst (is k))) := by
        intro r' r hs
        funext k
        rw [GenValue.Equiv.collapseSum_eq (hs.1 (is k)),
          AggValue.collapseSum_mapAnnSum]
      rw [show ((q.evaluate (h.mapAnnotatedDatabase d) γ E').map
            (fun row => (fun k => AggValue.collapseSum (row.fst (is k))
              : Tuple T nI₁))).dedup
          = ((q.evaluate d γ E).map
            (fun row => (fun k => AggValue.collapseSum (row.fst (is k))
              : Tuple T nI₁))).dedup
          from congrArg Multiset.dedup (map_eq_of_rel hrel hkey)]
      refine rel_map_of_forall (fun g _ => ?_)
      -- the group's rows are related row for row
      have hgroup := rel_filter_of_iff
        (p := fun row : GenRow T K' mI =>
          (fun k => AggValue.collapseSum (row.fst (is k)) : Tuple T nI₁) = g)
        (q := fun row : GenRow T K mI =>
          (fun k => AggValue.collapseSum (row.fst (is k)) : Tuple T nI₁) = g)
        hrel (fun r' r hs => by rw [hkey r' r hs])
      -- and so are the occurrences they become
      have hocc : Multiset.Rel (fun o' o : AggExpr T K' × K' =>
          o'.snd = o.snd ∧ o'.fst.worldStats = o.fst.worldStats
            ∧ o'.fst.collapse = o.fst.collapse)
          (((q.evaluate (h.mapAnnotatedDatabase d) γ E').filter
              (fun row => (fun k => AggValue.collapseSum (row.fst (is k))
                : Tuple T nI₁) = g)).map
            (fun row => (GenValue.innerValue (p.eval row.fst γ),
              row.snd.finalize)))
          ((((q.evaluate d γ E).filter
              (fun row => (fun k => AggValue.collapseSum (row.fst (is k))
                : Tuple T nI₁) = g)).map
            (fun row => (GenValue.innerValue (p.eval row.fst γ),
              row.snd.finalize))).map
            (fun o => (o.fst.mapAnn ⇑h.toRingHom, h.toRingHom o.snd))) := by
        rw [Multiset.map_map]
        refine rel_map_of_rel hgroup (fun r' r hs => ⟨hs.2, ?_, ?_⟩)
        · show (GenValue.innerValue (p.eval r'.fst γ)).worldStats
            = ((GenValue.innerValue (p.eval r.fst γ)).mapAnn
              ⇑h.toRingHom).worldStats
          rw [← GenValue.innerValue_mapAnnSum]
          exact (p.equiv_eval_of_sim h hs.1).innerValue_worldStats
        · show (GenValue.innerValue (p.eval r'.fst γ)).collapse
            = ((GenValue.innerValue (p.eval r.fst γ)).mapAnn
              ⇑h.toRingHom).collapse
          rw [← GenValue.innerValue_mapAnnSum, NestedValue.collapse_innerValue,
            NestedValue.collapse_innerValue]
          exact GenValue.Equiv.collapseSum_eq (p.equiv_eval_of_sim h hs.1)
      refine ⟨⟨fun k => ?_, ?_⟩, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · dsimp only
          rw [Fin.append_left, Fin.append_left]
          rfl
        · dsimp only
          rw [Fin.append_right, Fin.append_right]
          refine GenValue.Equiv.of_nest_rel hn.1 rfl rfl ?_
          dsimp only [NestedValue.mapAnn]
          exact hocc
      · dsimp only
        rw [GenAnn.finalize_gamma, GenAnn.finalize_gamma,
          SemiringWithMonusHom.map_delta]
        refine congrArg SemiringWithMonus.delta ?_
        rw [List.sum_singleton, List.sum_singleton]
        rw [show (((q.evaluate (h.mapAnnotatedDatabase d) γ E').filter
              (fun row => (fun k => AggValue.collapseSum (row.fst (is k))
                : Tuple T nI₁) = g)).map
              (fun row => (GenValue.innerValue (p.eval row.fst γ),
                row.snd.finalize))).map Prod.snd
            = ((((q.evaluate d γ E).filter
                (fun row => (fun k => AggValue.collapseSum (row.fst (is k))
                  : Tuple T nI₁) = g)).map
                (fun row => (GenValue.innerValue (p.eval row.fst γ),
                  row.snd.finalize))).map Prod.snd).map ⇑h.toRingHom from by
          rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
          exact map_eq_of_rel hgroup (fun r' r hs => hs.2)]
        exact (map_multiset_sum h.toRingHom _).symm
      · rw [hpk]
        refine ⟨_, _, nestRel_of_rel h hocc, fun j x' x h1 h2 => ?_⟩
        dsimp only at h1 h2
        rw [Fin.append_right] at h1 h2
        have e1 := (Sum.inr_injective h1).symm
        have e2 := (Sum.inr_injective h2).symm
        subst e1 e2
        exact ⟨⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    refine hsim.mono (fun r' hr' r hr hs => ⟨hs.1, ?_⟩)
    obtain ⟨key, hkey0, hkey⟩ := AggQueryIn.newRow_GammaNest is his p f q d γ E hr
    obtain ⟨key', -, hkey'⟩ := AggQueryIn.newRow_GammaNest is his p f q _ γ E' hr'
    have hfr := freshG hU r' r (Fin.natAdd nI₁) lab (fun _ => hW _ List.mem_cons_self) key
      (E.paramKey rd γ)
      (fun j => let ⟨x, h1, h2⟩ := hkey j
        ⟨x, h1, hb x (Or.inl ⟨r, hr, Fin.fin_one_eq_zero j ▸ h1⟩), h2⟩)
      (fun j => let ⟨x, h1, _⟩ := hkey' j
        ⟨x, h1, hb' x (Or.inl ⟨r', hr', Fin.fin_one_eq_zero j ▸ h1⟩)⟩)
      (Or.inr hs.2)
    intro p ⟨k, h1, h2⟩
    revert h1 h2
    refine Fin.addCases (fun i h1 h2 => ?_) (fun j h1 h2 => hfr j _ _ h1 h2) k
    obtain ⟨v, hv⟩ := hkey0 i
    rw [hv] at h2
    exact absurd h2 (by simp)
  | @Win cI nI mI pI κw lab rd P O o w t f q hrr dist keep ih =>
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    have hpk := EvalEnv.paramKey_eq_of_envG hE hJ rd
    have hsim := ih d γ E' E hE hJ (fun x h => hb x (Or.inr h)) (fun x h => hb' x (Or.inr h))
      (fun e he => hW e (List.mem_cons_of_mem _ he)) hw hn hsc hrec
    have hread : (q.evaluate (h.mapAnnotatedDatabase d) γ E').map
          (GenRow.readAnnotated κw)
        = ((q.evaluate d γ E).map (GenRow.readAnnotated κw)).map
            (fun p : AnnotatedTuple T K nI =>
              ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI)) := by
      rw [Multiset.map_map]
      exact map_eq_of_rel hsim
        (fun r' r hs => GenRow.Sim.readAnnotated_eq h κw hs.1)
    -- the rows of the two evaluations, as the window builds them
    have hev : ∀ x ∈ q.evaluate d γ E, ValueFrame.windowGenRow lab (E.paramKey rd γ) κw P O o
        w t f keep ((q.evaluate d γ E).map (GenRow.readAnnotated κw)) x γ dist
        ∈ (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q hrr dist keep).evaluate
          d γ E := by
      intro x hx
      simp only [AggQueryIn.evaluate]
      exact Multiset.mem_map_of_mem _ hx
    have hev' : ∀ x' ∈ q.evaluate (h.mapAnnotatedDatabase d) γ E',
        ValueFrame.windowGenRow lab (E.paramKey rd γ) κw P O o w t f keep
          (((q.evaluate d γ E).map (GenRow.readAnnotated κw)).map
            (fun p : AnnotatedTuple T K nI =>
              ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI))) x' γ dist
        ∈ (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q hrr dist keep).evaluate
          (h.mapAnnotatedDatabase d) γ E' := by
      intro x' hx'
      simp only [AggQueryIn.evaluate]
      rw [← hread, ← hpk]
      exact Multiset.mem_map_of_mem _ hx'
    -- the fresh value of a pair of related rows
    have hfresh : ∀ x' ∈ q.evaluate (h.mapAnnotatedDatabase d) γ E', ∀ x ∈ q.evaluate d γ E,
        GenRow.Sim h x' x → RowG h 𝒰₀ 𝒰₀' x' x →
        (∃ D : ListingRel h.toRingHom T, ∀ y' y,
          (ValueFrame.windowGenRow lab (E.paramKey rd γ) κw P O o w t f keep
            (((q.evaluate d γ E).map (GenRow.readAnnotated κw)).map
              (fun p : AnnotatedTuple T K nI =>
                ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI))) x' γ dist).fst
              (Fin.last nI) = Sum.inr y' →
          (ValueFrame.windowGenRow lab (E.paramKey rd γ) κw P O o w t f keep
            ((q.evaluate d γ E).map (GenRow.readAnnotated κw)) x γ dist).fst (Fin.last nI)
              = Sum.inr y → D.Member y' y ∧ y'.fam = y.fam) →
        RowG h 𝒰₀ 𝒰₀'
          (ValueFrame.windowGenRow lab (E.paramKey rd γ) κw P O o w t f keep
            (((q.evaluate d γ E).map (GenRow.readAnnotated κw)).map
              (fun p : AnnotatedTuple T K nI =>
                ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI))) x' γ dist)
          (ValueFrame.windowGenRow lab (E.paramKey rd γ) κw P O o w t f keep
            ((q.evaluate d γ E).map (GenRow.readAnnotated κw)) x γ dist) := by
      intro x' hx' x hx hs hrow ⟨D, hD⟩
      obtain ⟨y, hy, hyf⟩ := ValueFrame.windowGenRow_last lab (E.paramKey rd γ) κw P O o w t f
        keep ((q.evaluate d γ E).map (GenRow.readAnnotated κw)) x γ dist
      obtain ⟨y', hy', -⟩ := ValueFrame.windowGenRow_last lab (E.paramKey rd γ) κw P O o w t f
        keep (((q.evaluate d γ E).map (GenRow.readAnnotated κw)).map
          (fun p : AnnotatedTuple T K nI =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI))) x' γ dist
      have hfr := freshG hU _ _ (fun _ : Fin 1 => Fin.last nI) lab
          (fun _ => hW _ List.mem_cons_self)
        (List.ofFn (GenRow.readAnnotated κw x).fst) (E.paramKey rd γ)
        (fun j => ⟨y, hy, hb _ (Or.inl ⟨_, hev x hx, hy⟩),
          by rw [Fin.fin_one_eq_zero j]; exact hyf⟩)
        (fun j => ⟨y', hy', hb' _ (Or.inl ⟨_, hev' x' hx', hy'⟩)⟩)
        (Or.inl ⟨D, fun _ y' y h1 h2 => hD y' y h1 h2⟩)
      intro p ⟨k, h1, h2⟩
      revert h1 h2
      refine Fin.lastCases (fun h1 h2 => hfr 0 _ _ h1 h2) (fun i h1 h2 => ?_) k
      simp only [ValueFrame.windowGenRow, Fin.snoc_castSucc] at h1 h2
      exact hrow _ ⟨i, h1, h2⟩
    cases hk : keep with
    | some φ =>
      subst hk
      rw [AggQueryIn.evaluate_Win_eq_when, AggQueryIn.evaluate_Win_eq_when, hread, hpk]
      refine Multiset.rel_map.mpr (hsim.mono (fun x' hx' x hx hs => ?_))
      have hmem : GenRow.readAnnotated κw x
          ∈ Multiset.map (GenRow.readAnnotated κw) (q.evaluate d γ E) :=
        Multiset.mem_map_of_mem _ hx
      have hrd := GenRow.Sim.readAnnotated_eq h κw hs.1
      refine ⟨⟨fun k => ?_, hs.1.2⟩, hfresh x' hx' x hx hs.1 hs.2 ?_⟩
      · simp only [ValueFrame.windowGenRow]
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · rw [Fin.snoc_last, Fin.snoc_last, hrd]
          exact exprWhenOf_mapAnn_equiv h P O o w t γ f dist φ.keeps _ hmem
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hs.1.1 k'
      · obtain ⟨D, hD⟩ := ListingRel.exists_exprWhenOf h P O o w t γ f dist φ.keeps _ hmem
          (.mk lab (List.ofFn (GenRow.readAnnotated κw x).fst) (E.paramKey rd γ) 0 [])
          (.mk lab (List.ofFn (GenRow.readAnnotated κw x).fst) (E.paramKey rd γ) 0 [])
        refine ⟨D, fun y' y h1 h2 => ?_⟩
        simp only [ValueFrame.windowGenRow, Fin.snoc_last, hrd] at h1 h2
        rw [← Sum.inr_injective h1, ← Sum.inr_injective h2]
        exact ⟨hD, by simp only [AggTok.fam_setFam]; rfl⟩
    | none =>
      subst hk
      rw [AggQueryIn.evaluate_Win_eq, AggQueryIn.evaluate_Win_eq, hread, hpk]
      refine Multiset.rel_map.mpr (hsim.mono (fun x' hx' x hx hs => ?_))
      have hmem : GenRow.readAnnotated κw x
          ∈ Multiset.map (GenRow.readAnnotated κw) (q.evaluate d γ E) :=
        Multiset.mem_map_of_mem _ hx
      have hrd := GenRow.Sim.readAnnotated_eq h κw hs.1
      refine ⟨⟨fun k => ?_, hs.1.2⟩, hfresh x' hx' x hx hs.1 hs.2 ?_⟩
      · simp only [ValueFrame.windowGenRow]
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · rw [Fin.snoc_last, Fin.snoc_last, hrd]
          exact tokenOfDist_mapAnn_equiv h P O o w t γ f dist _ hmem
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hs.1.1 k'
      · obtain ⟨D, hD⟩ := ListingRel.exists_of_tokEquiv h
          (tokenOfDist_mapAnn_equiv h P O o w t γ f dist _ hmem)
          (.mk lab (List.ofFn (GenRow.readAnnotated κw x).fst) (E.paramKey rd γ) 0 [])
          (.mk lab (List.ofFn (GenRow.readAnnotated κw x).fst) (E.paramKey rd γ) 0 [])
        refine ⟨D, fun y' y h1 h2 => ?_⟩
        simp only [ValueFrame.windowGenRow, Fin.snoc_last, hrd] at h1 h2
        rw [← Sum.inr_injective h1, ← Sum.inr_injective h2]
        exact ⟨hD, by simp only [AggTok.fam_setFam]; rfl⟩
  | @WinExpr cI nI mI pI qI lab rd P O o ws ts fs g q keeps ih =>
    -- one output row per occurrence of the shared family. The two sides
    -- index that family by their own sorted order, so they are compared
    -- through a bijection of indices rather than index by index; the
    -- frames read the tuple (`hw.1`), which is what makes each pair of
    -- corresponding expression columns equivalent.
    intro d γ E' E hE hJ hb hb' hW hw hn hsc hrec
    have hpk := EvalEnv.paramKey_eq_of_envG hE hJ rd
    have hsim : Multiset.Rel (fun r' r => GenRow.Sim h r' r ∧ ∃ D : ListingRel h.toRingHom T,
        ∀ j : Fin 1, ∀ x' x, r'.fst (Fin.last nI) = Sum.inr x' → r.fst (Fin.last nI) = Sum.inr x →
          D.Member x' x ∧ x'.fam = x.fam)
        ((AggQueryIn.WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q keeps).evaluate
          (h.mapAnnotatedDatabase d) γ E')
        ((AggQueryIn.WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q keeps).evaluate d γ E) := by
      simp only [AggQueryIn.evaluate]
      have hY : Multiset.map GenRow.toAnnotated
            (q.evaluate (h.mapAnnotatedDatabase d) γ E')
          = Multiset.map (fun y : AnnotatedTuple T K nI =>
              ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' nI))
            (Multiset.map GenRow.toAnnotated (q.evaluate d γ E)) := by
        have h1 : Multiset.map GenRow.toAnnotated
              (q.evaluate (h.mapAnnotatedDatabase d) γ E')
            = Multiset.map (SemiringWithMonusHom.mapAnnotatedTuple h)
              (Multiset.map GenRow.toAnnotated (q.evaluate d γ E)) := by
          rw [Multiset.map_map]
          exact map_eq_of_rel (ih d γ E' E hE hJ (fun x h => hb x (Or.inr h))
            (fun x h => hb' x (Or.inr h)) (fun e he => hW e (List.mem_cons_of_mem _ he)) hw.2 hn
            hsc hrec)
            (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)
        exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))
      rw [hY]
      set gh : AnnotatedTuple T K nI → AnnotatedTuple T K' nI :=
        fun y => ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' nI)
        with hghdef
      set X : Multiset (AnnotatedTuple T K nI) :=
        Multiset.map GenRow.toAnnotated (q.evaluate d γ E) with hXdef
      clear_value X
      -- the two indexings hold the same occurrences, pushed forward
      have hmul : (OccFam.mk (OccFam.ofSorted X).size
            (fun i => gh ((OccFam.ofSorted X).row i))).toMultiset
          = (OccFam.ofSorted (Multiset.map gh X)).toMultiset :=
        (OccFam.toMultiset_map gh (OccFam.ofSorted X)).symm.trans (by
          rw [OccFam.toMultiset_ofSorted, OccFam.toMultiset_ofSorted])
      obtain ⟨e, he⟩ := OccFam.Congr_of_toMultiset_eq hmul
      have hmul' : (OccFam.ofSorted (Multiset.map gh X)).toMultiset
          = Multiset.map gh (OccFam.ofSorted X).toMultiset := by
        rw [OccFam.toMultiset_ofSorted, OccFam.toMultiset_ofSorted]
      refine rel_occFam_of_equiv _ _ e (fun i => ⟨⟨fun k => ?_, ?_⟩, ?_⟩)
      · dsimp only
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · rw [Fin.snoc_last, Fin.snoc_last]
          exact (exprOfWhen_mapAnn_equiv h P O o hw.1 ts fs g keeps γ
            (congrArg Prod.fst (he i)) hmul').setFam _ _
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact congrArg (fun y : AnnotatedTuple T K' nI => y.fst k') (he i)
      · dsimp only
        rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero,
          he i]
      · obtain ⟨D, hD⟩ := ListingRel.exists_exprOfWhen h P O o hw.1 ts fs g keeps γ
            (congrArg Prod.fst (he i)) hmul'
            (FamId.mk lab (List.ofFn (OccFam.ofSorted X |>.row i).fst)
              (E.paramKey rd γ) 0 [])
            (FamId.mk lab (List.ofFn ((OccFam.ofSorted (Multiset.map gh X)).row (e i)).fst)
              (E'.paramKey rd γ) 0 [])
        refine ⟨D, fun _ x' x h1 h2 => ?_⟩
        dsimp only at h1 h2
        rw [Fin.snoc_last] at h1 h2
        rw [← Sum.inr_injective h1, ← Sum.inr_injective h2]
        refine ⟨hD, ?_⟩
        simp only [AggTok.fam_setFam, hpk, congrArg Prod.fst (he i)]
        rfl
    refine hsim.mono (fun r' hr' r hr hs => ⟨hs.1, ?_⟩)
    obtain ⟨key, hkey0, hkey⟩ := AggQueryIn.newRow_WinExpr P O o ws ts fs g q keeps d γ E hr
    obtain ⟨key', -, hkey'⟩ := AggQueryIn.newRow_WinExpr P O o ws ts fs g q keeps _ γ E' hr'
    have hfr := freshG hU r' r (fun _ : Fin 1 => Fin.last nI) lab
        (fun _ => hW _ List.mem_cons_self) key
      (E.paramKey rd γ)
      (fun j => let ⟨x, h1, h2⟩ := hkey j; ⟨x, h1, hb x (Or.inl ⟨r, hr, h1⟩), h2⟩)
      (fun j => let ⟨x, h1, _⟩ := hkey' j; ⟨x, h1, hb' x (Or.inl ⟨r', hr', h1⟩)⟩)
      (Or.inl hs.2)
    intro p ⟨k, h1, h2⟩
    revert h1 h2
    refine Fin.lastCases (fun h1 h2 => hfr 0 _ _ h1 h2) (fun i h1 h2 => ?_) k
    obtain ⟨v, hv⟩ := hkey0 i
    rw [hv] at h2
    exact absurd h2 (by simp)

omit [ValueType T] in
theorem List.snd_eq_of_mem_of_nodup_map {α β : Type} {L : List (α × β)}
    (hL : (L.map Prod.fst).Nodup) {a : α} {b c : β} (hb : (a, b) ∈ L) (hc : (a, c) ∈ L) :
    b = c := by
  have := List.inj_on_of_nodup_map hL hb hc rfl
  exact (Prod.mk.inj this).2

/-- **The universes of a query evaluated from scratch.** -/
theorem AggQueryIn.homUniv_of (h : SemiringWithMonusHom K K') {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (hld : q.labelsDistinct) (hrr : q.readsRecorded)
    (hsc : q.sourceCols) (hfc : q.allFramesContainSelf) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) :
    HomUniv (q.Builds d γ {}) (q.Builds (h.mapAnnotatedDatabase d) γ {}) q.labWidths := by
  obtain ⟨hF, hK⟩ := q.builds_coherent_closed hld hrr hsc hfc d γ
  obtain ⟨hF', hK'⟩ := q.builds_coherent_closed hld hrr hsc hfc (h.mapAnnotatedDatabase d) γ
  have hW : (q.labWidths.map Prod.fst).Nodup := by
    rw [← AggQueryIn.labels_eq_map_labWidths]; exact hld
  refine ⟨fun x hx => (q.builds_spec d γ {} x hx).1,
    fun x hx => (q.builds_spec _ γ {} x hx).1, hF, hF', hK, hK', fun x hx w hw => ?_⟩
  obtain ⟨w₀, hw₀, hc⟩ := q.builds_col d γ {} x hx
  rw [List.snd_eq_of_mem_of_nodup_map hW hw hw₀]
  exact hc

/-- The row-wise simulation for a query read with nothing bound. -/
theorem AggQueryIn.evaluate_hom_rel (h : SemiringWithMonusHom K K') {c n : ℕ}
    {κ : Fin n → ColKind} (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (hn : q.nestInComplemented (K := K'))
    (hld : q.labelsDistinct) (hrr : q.readsRecorded) (hsc : q.sourceCols)
    (hfc : q.allFramesContainSelf) (hrec : q.AnnSettlesAt d γ {}) :
    Multiset.Rel (GenRow.Sim h) (q.evaluate (h.mapAnnotatedDatabase d) γ) (q.evaluate d γ) := by
  have hnone : ∀ {K₀ : Type} [CommSemiringWithMonus K₀] (𝒰 : AggTok T K₀ → Prop) x,
      ({} : EvalEnv T K₀).Toks γ [] x → TermCl 𝒰 x := by
    intro K₀ _ 𝒰 x hx
    rcases hx with ⟨k, hk⟩ | ⟨p, hp, -⟩
    · rw [EvalEnv.empty_ctxAt] at hk
      exact absurd hk (by simp)
    · exact absurd hp List.not_mem_nil
  refine (AggQueryIn.evaluate_hom_univ h (q.homUniv_of h hld hrr hsc hfc d γ) q d γ {} {}
    (EvalEnv.homSim_empty h γ) ⟨fun k x' x _ h2 => ?_, fun _ _ h' => absurd h' (by simp),
      hnone _, hnone _⟩ (fun _ h => h) (fun _ h => h) (fun _ h => h)
    (q.framesContainSelf_of_all hfc) hn hsc hrec).mono (fun _ _ _ _ hs => hs.1)
  rw [EvalEnv.empty_ctxAt] at h2
  exact absurd h2 (by simp)

/-- **Evaluator-level hom commutation**: the final annotated relation
computed by the general evaluator commutes with every
`SemiringWithMonusHom`, over every m-semiring. Nothing is asked of the
hom: the extra supersedes a non-injective one can trigger are
value-neutral by guard absorption (`delta_absorb`), and the annotation
tie-breaks of the group sort are value-neutral by the tie-block
congruence layer.

What is asked of the *query*:

* that every window frame contain its current row
  (`AggQueryIn.allFramesContainSelf`): a multi-frame window lists its
  shared family by occurrence index, which a change of annotation semiring
  re-sorts inside blocks of equal rows, and a window over a frame that
  excludes the current row gives two rows with the same tuple different
  values, which one family identifier cannot tell apart. Every window
  function the library derives satisfies it;
* that the *target* semiring be complemented wherever the query
  aggregates a grouping a second time (`AggQueryIn.nestInComplemented`),
  which is how the per-column equivalence of nested values is proved;
  `AggQueryIn.nestInComplemented_of_noGammaNest` discharges it for a query
  with no second-level aggregation;
* that no two operators building aggregate values share a label
  (`AggQueryIn.labelsDistinct`), that every operator record the parameters
  its subtree reads (`AggQueryIn.readsRecorded`), and that no projection
  column apply an arbitrary function to an aggregate value
  (`AggQueryIn.sourceCols`). A selection reads the values of one family in
  one world of that family, and the two sides list the family's
  occurrences each in its own order; what makes the reading commute is
  that every value of a family is built from *one* listing on each side,
  the two tie-block permuted (`FamPres`, `jointWorlds_of_famPres`). Under
  these three conditions a family identifier determines its value across
  every evaluation the query performs, a recursion's rounds included
  (`AggQueryIn.builds_coherent`), so each family is presented once for the
  whole evaluation (`ClassPres`).

These are hypotheses of *this proof* and not of the mathematics: every
output annotation is an expression in the input annotations over `⊕`,
`⊗`, `⊖`, `δ`, `𝟘`, `𝟙`, and a hom commutes with such an expression in
every m-semiring. -/
theorem AggQueryIn.evaluateAnnotated_hom (h : SemiringWithMonusHom K K')
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ)
    (hn : q.nestInComplemented (K := K')) (hld : q.labelsDistinct) (hrr : q.readsRecorded)
    (hsc : q.sourceCols) (hfc : q.allFramesContainSelf)
    (d : AnnotatedDatabase T K) (hrec : q.AnnSettlesAt d (fun _ => 0) {}) :
    q.evaluateAnnotated (h.mapAnnotatedDatabase d)
      = SemiringWithMonusHom.mapAnnotatedRelation h
          (q.evaluateAnnotated d) := by
  unfold AggQueryIn.evaluateAnnotated SemiringWithMonusHom.mapAnnotatedRelation
  rw [Multiset.map_map]
  exact map_eq_of_rel (AggQueryIn.evaluate_hom_rel h q d _ hn hld hrr hsc hfc hrec)
    (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)

end EvaluatorHom
