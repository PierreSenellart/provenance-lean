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
families be presented on both sides. That is carried through the
evaluation together with where a row's values come from: from the
environment – a universe `U` of presented pairs, closed under terms, whose
labels the query does not use – from one round a recursion reads (`H`),
or from an operator of the query, labelled by it. Rows built by
subqueries with disjoint labels then merge (`FamPres.merge`). -/

/-- The pairs of corresponding aggregate values two rows hold. -/
def rowPairs {n : ℕ} (u' : Tuple (GenValue T K') n) (u : Tuple (GenValue T K) n) :
    AggTok T K' × AggTok T K → Prop :=
  fun p => ∃ k, u' k = Sum.inr p.1 ∧ u k = Sum.inr p.2

/-- Corresponding values carry the same family identifier. -/
def EqFamP (S : AggTok T K' × AggTok T K → Prop) : Prop := ∀ p, S p → p.1.fam = p.2.fam

/-- A set of pairs closed under terms. -/
def PClosed (S : AggTok T K' × AggTok T K → Prop) : Prop := ∀ p, PCl S p → S p

/-- **What a row's families are**: presented together with the
environment's universe `U` and the round `H` it was read from, each value
either from those or built by an operator labelled in `L`, and every pair
carrying one family identifier on both sides. -/
def RowJoint (h : SemiringWithMonusHom K K') (U H : AggTok T K' × AggTok T K → Prop)
    (L : List ℕ) {n : ℕ} (r' : GenRow T K' n) (r : GenRow T K n) : Prop :=
  FamPres h.toRingHom (fun p => rowPairs r'.fst r.fst p ∨ U p ∨ H p)
  ∧ (∀ p, rowPairs r'.fst r.fst p → U p ∨ H p ∨ p.2.lab ∈ L)
  ∧ EqFamP (rowPairs r'.fst r.fst)

/-- **What a round read in a recursion contributes**: closed under terms,
one family identifier per pair, and drawn from the environment or built
by an operator labelled in `Lh`. -/
def HoleOK (U H : AggTok T K' × AggTok T K → Prop) (Lh : List ℕ) : Prop :=
  PClosed H ∧ EqFamP H ∧ ∀ p, H p → U p ∨ p.2.lab ∈ Lh

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [CommSemiringWithMonus K]
  [CommSemiringWithMonus K'] [DecidableEq K'] in
theorem PCl.idem {S : AggTok T K' × AggTok T K → Prop} {p} (hp : PCl (PCl S) p) : PCl S p := by
  induction hp with
  | base h => exact h
  | step t _ ih => exact PCl.step t ih
  | stepF gf _ ih => exact PCl.stepF gf ih

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [CommSemiringWithMonus K]
  [CommSemiringWithMonus K'] [DecidableEq K'] in
theorem PClosed.pcl (S : AggTok T K' × AggTok T K → Prop) : PClosed (PCl S) :=
  fun _ hp => hp.idem

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [ValueType T] in
theorem FamId.lab_addTerm (t : TermIn T 1 0) (φ : FamId T) : (φ.addTerm t).lab = φ.lab := by
  cases φ; rfl

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
theorem AggTok.fam_postcomp' {K₀ : Type} (gf : T → T) (x : AggTok T K₀) :
    (x.postcomp gf).fam = x.fam := by
  cases x <;> rfl

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
theorem AggTok.lab_postcompTerm {K₀ : Type} (t : TermIn T 1 0) (x : AggTok T K₀) :
    (x.postcompTerm t).lab = x.lab := by
  simp [AggTok.lab, AggTok.postcompTerm, FamId.lab_addTerm]

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
theorem AggTok.lab_postcomp {K₀ : Type} (gf : T → T) (x : AggTok T K₀) :
    (x.postcomp gf).lab = x.lab := by
  simp [AggTok.lab, AggTok.fam_postcomp']

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [CommSemiringWithMonus K]
  [CommSemiringWithMonus K'] [DecidableEq K'] in
theorem EqFamP.pcl {S : AggTok T K' × AggTok T K → Prop} (hS : EqFamP S) : EqFamP (PCl S) := by
  intro p hp
  induction hp with
  | base h => exact hS _ h
  | step t _ ih => simp [AggTok.postcompTerm, ih]
  | stepF gf _ ih => simp [AggTok.fam_postcomp', ih]

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [CommSemiringWithMonus K]
  [CommSemiringWithMonus K'] [DecidableEq K'] in
/-- A term over a value keeps where it comes from: a closed set it was in,
or the label of the operator that built it. -/
theorem PCl.origin {S C : AggTok T K' × AggTok T K → Prop} {L : List ℕ} (hC : PClosed C)
    (hS : ∀ q, S q → C q ∨ q.2.lab ∈ L) {p} (hp : PCl S p) : C p ∨ p.2.lab ∈ L := by
  induction hp with
  | base h => exact hS _ h
  | @step q t _ ih =>
    rcases ih with hq | hq
    · exact Or.inl (hC _ (PCl.step t (PCl.base hq)))
    · exact Or.inr (by rw [AggTok.lab_postcompTerm]; exact hq)
  | @stepF q gf _ ih =>
    rcases ih with hq | hq
    · exact Or.inl (hC _ (PCl.stepF gf (PCl.base hq)))
    · exact Or.inr (by rw [AggTok.lab_postcomp]; exact hq)

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- **A row whose values are terms over another's keeps its families.** -/
theorem RowJoint.of_pcl {h : SemiringWithMonusHom K K'} {U H : AggTok T K' × AggTok T K → Prop}
    {L : List ℕ} (hU : PClosed U) (hH : PClosed H) {n m : ℕ} {r' : GenRow T K' n}
    {r : GenRow T K n} (hr : RowJoint h U H L r' r) {a' : GenRow T K' m} {a : GenRow T K m}
    (hsub : ∀ p, rowPairs a'.fst a.fst p → PCl (rowPairs r'.fst r.fst) p) :
    RowJoint h U H L a' a := by
  have hUH : PClosed (fun p => U p ∨ H p) := by
    intro p hp
    induction hp with
    | base h => exact h
    | @step q t _ ih =>
      exact Or.imp (fun hq => hU _ (PCl.step t (PCl.base hq)))
        (fun hq => hH _ (PCl.step t (PCl.base hq))) ih
    | @stepF q gf _ ih =>
      exact Or.imp (fun hq => hU _ (PCl.stepF gf (PCl.base hq)))
        (fun hq => hH _ (PCl.stepF gf (PCl.base hq))) ih
  refine ⟨hr.1.pcl.mono (fun p hp => ?_), fun p hp => ?_, ?_⟩
  · rcases hp with hp | hp | hp
    · exact (hsub p hp).mono (fun q hq => Or.inl hq)
    · exact PCl.base (Or.inr (Or.inl hp))
    · exact PCl.base (Or.inr (Or.inr hp))
  · have := PCl.origin hUH (fun q hq => (hr.2.1 q hq).elim (fun h => Or.inl (Or.inl h))
      (fun h => h.elim (fun h => Or.inl (Or.inr h)) Or.inr)) (hsub p hp)
    rcases this with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · exact fun p hp => (EqFamP.pcl hr.2.2) p (hsub p hp)

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [ValueType T] [DecidableEq K'] in
/-- A row holding no aggregate value has the families of the environment. -/
theorem RowJoint.of_noPairs {h : SemiringWithMonusHom K K'} {U : AggTok T K' × AggTok T K → Prop}
    (hU : FamPres h.toRingHom U) (L : List ℕ) {n : ℕ} {r' : GenRow T K' n} {r : GenRow T K n}
    (hr : ∀ p, ¬ rowPairs r'.fst r.fst p) : RowJoint h U (fun _ => False) L r' r :=
  ⟨hU.mono (fun p hp => hp.elim (fun h => absurd h (hr p)) (fun h => h.elim id False.elim)),
    fun p hp => absurd hp (hr p), fun p hp => absurd hp (hr p)⟩

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [ValueType T] [DecidableEq K'] in
/-- A row of values from the environment has its families. -/
theorem RowJoint.of_env {h : SemiringWithMonusHom K K'} {U : AggTok T K' × AggTok T K → Prop}
    (hU : FamPres h.toRingHom U) (hUf : EqFamP U) (L : List ℕ) {n : ℕ} {r' : GenRow T K' n}
    {r : GenRow T K n} (hr : ∀ p, rowPairs r'.fst r.fst p → U p) :
    RowJoint h U (fun _ => False) L r' r :=
  ⟨hU.mono (fun p hp => hp.elim (hr p) (fun h => h.elim id False.elim)),
    fun p hp => Or.inl (hr p hp), fun p hp => hUf p (hr p hp)⟩

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [ValueType T] [DecidableEq K'] in
theorem RowJoint.mono_labels {h : SemiringWithMonusHom K K'} {U H : AggTok T K' × AggTok T K → Prop}
    {L L' : List ℕ} (hL : ∀ l ∈ L, l ∈ L') {n : ℕ} {r' : GenRow T K' n} {r : GenRow T K n}
    (hr : RowJoint h U H L r' r) : RowJoint h U H L' r' r :=
  ⟨hr.1, fun p hp => (hr.2.1 p hp).imp_right (fun h => h.imp_right (hL _)), hr.2.2⟩

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

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- **Two rows built by subqueries with disjoint labels merge**, at most
one of them read from a round of a recursion. -/
theorem RowJoint.append {h : SemiringWithMonusHom K K'} {U H₁ H₂ : AggTok T K' × AggTok T K → Prop}
    {L₁ L₂ Lh : List ℕ} (hUl : ∀ p, U p → p.2.lab ∉ L₁ ∧ p.2.lab ∉ L₂ ∧ p.2.lab ∉ Lh)
    (hdisj : ∀ l ∈ L₁, l ∉ L₂) (hLh₁ : ∀ l ∈ Lh, l ∉ L₁) (hLh₂ : ∀ l ∈ Lh, l ∉ L₂)
    (hH₁ : HoleOK U H₁ Lh) (hH₂ : HoleOK U H₂ Lh) (hone : (∀ p, ¬ H₁ p) ∨ (∀ p, ¬ H₂ p))
    {n₁ n₂ : ℕ} {x' : GenRow T K' n₁} {x : GenRow T K n₁} {y' : GenRow T K' n₂}
    {y : GenRow T K n₂} (hx : RowJoint h U H₁ L₁ x' x) (hy : RowJoint h U H₂ L₂ y' y)
    (b' : GenAnn K') (b : GenAnn K) :
    RowJoint h U (fun p => H₁ p ∨ H₂ p) (L₁ ++ L₂)
      ((Fin.append x'.fst y'.fst, b') : GenRow T K' (n₁ + n₂))
      ((Fin.append x.fst y.fst, b) : GenRow T K (n₁ + n₂)) := by
  have hpairs : ∀ p, rowPairs (Fin.append x'.fst y'.fst) (Fin.append x.fst y.fst) p
      ↔ rowPairs x'.fst x.fst p ∨ rowPairs y'.fst y.fst p := rowPairs_append _ _ _ _
  have hfam : FamPres h.toRingHom (fun p =>
      (rowPairs x'.fst x.fst p ∨ H₁ p) ∨ (rowPairs y'.fst y.fst p ∨ H₂ p) ∨ U p) := by
    have hA : FamPres h.toRingHom (fun p => (rowPairs x'.fst x.fst p ∨ H₁ p) ∨ U p) :=
      hx.1.mono (fun p hp => hp.elim (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h)))
        (fun h => Or.inr (Or.inl h)))
    have hB : FamPres h.toRingHom (fun p => (rowPairs y'.fst y.fst p ∨ H₂ p) ∨ U p) :=
      hy.1.mono (fun p hp => hp.elim (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h)))
        (fun h => Or.inr (Or.inl h)))
    have hfA : ∀ p, (rowPairs x'.fst x.fst p ∨ H₁ p) → p.1.lab = p.2.lab := by
      rintro p (hp | hp)
      · exact congrArg FamId.lab (hx.2.2 p hp)
      · exact congrArg FamId.lab (hH₁.2.1 p hp)
    have hfB : ∀ p, (rowPairs y'.fst y.fst p ∨ H₂ p) → p.1.lab = p.2.lab := by
      rintro p (hp | hp)
      · exact congrArg FamId.lab (hy.2.2 p hp)
      · exact congrArg FamId.lab (hH₂.2.1 p hp)
    have hoA : ∀ (Lx : List ℕ), (∀ l ∈ Lh, l ∈ Lx) → (∀ l ∈ L₁, l ∈ Lx) →
        ∀ p, (rowPairs x'.fst x.fst p ∨ H₁ p) → U p ∨ p.2.lab ∈ Lx := by
      rintro Lx hLx hL₁ p (hp | hp)
      · rcases hx.2.1 p hp with h | h | h
        · exact Or.inl h
        · exact (hH₁.2.2 p h).imp_right (hLx _)
        · exact Or.inr (hL₁ _ h)
      · exact (hH₁.2.2 p hp).imp_right (hLx _)
    have hoB : ∀ (Lx : List ℕ), (∀ l ∈ Lh, l ∈ Lx) → (∀ l ∈ L₂, l ∈ Lx) →
        ∀ p, (rowPairs y'.fst y.fst p ∨ H₂ p) → U p ∨ p.2.lab ∈ Lx := by
      rintro Lx hLx hL₂ p (hp | hp)
      · rcases hy.2.1 p hp with h | h | h
        · exact Or.inl h
        · exact (hH₂.2.2 p h).imp_right (hLx _)
        · exact Or.inr (hL₂ _ h)
      · exact (hH₂.2.2 p hp).imp_right (hLx _)
    rcases hone with hn | hn
    · -- the round, if any, is read on the right
      refine FamPres.merge (La := L₁) (Lb := L₂ ++ Lh) hA hB ?_
        (hoB _ (fun l hl => List.mem_append_right _ hl) (fun l hl => List.mem_append_left _ hl))
        ?_ ?_ hfA hfB
      · rintro p (hp | hp)
        · rcases hx.2.1 p hp with h | h | h
          · exact Or.inl h
          · exact absurd h (hn p)
          · exact Or.inr h
        · exact absurd hp (hn p)
      · intro p hp hl
        rcases List.mem_append.mp hl with hl | hl
        · exact (hUl p hp).2.1 hl
        · exact (hUl p hp).2.2 hl
      · intro l hl hl'
        rcases List.mem_append.mp hl' with hl' | hl'
        · exact hdisj l hl hl'
        · exact hLh₁ l hl' hl
    · -- the round, if any, is read on the left
      have hm := FamPres.merge (La := L₂) (Lb := L₁ ++ Lh) hB hA ?_
        (hoA _ (fun l hl => List.mem_append_right _ hl) (fun l hl => List.mem_append_left _ hl))
        ?_ ?_ hfB hfA
      · exact hm.mono (fun p hp => by tauto)
      · rintro p (hp | hp)
        · rcases hy.2.1 p hp with h | h | h
          · exact Or.inl h
          · exact absurd h (hn p)
          · exact Or.inr h
        · exact absurd hp (hn p)
      · intro p hp hl
        rcases List.mem_append.mp hl with hl | hl
        · exact (hUl p hp).1 hl
        · exact (hUl p hp).2.2 hl
      · intro l hl hl'
        rcases List.mem_append.mp hl' with hl' | hl'
        · exact hdisj l hl' hl
        · exact hLh₂ l hl' hl
  refine ⟨hfam.mono (fun p hp => ?_), fun p hp => ?_, fun p hp => ?_⟩
  · rcases hp with hp | hp | hp | hp
    · rcases (hpairs p).mp hp with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inr hp)
    · exact Or.inl (Or.inr hp)
    · exact Or.inr (Or.inl (Or.inr hp))
  · rcases (hpairs p).mp hp with h | h
    · rcases hx.2.1 p h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inr (List.mem_append_left _ h))
    · rcases hy.2.1 p h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr (List.mem_append_right _ h))
  · rcases (hpairs p).mp hp with h | h
    · exact hx.2.2 p h
    · exact hy.2.2 p h

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

/-- **The environment of a joint simulation**: a universe `U` of
corresponding values, presented, closed under terms, one family
identifier per pair, carrying none of the query's labels nor those `Lh`
of the rounds; the context's aggregate values in it; and the rows bound to
the names the query reads simulating each other, with their families
presented together with `U`. -/
structure JointEnv (h : SemiringWithMonusHom K K') (U : AggTok T K' × AggTok T K → Prop)
    (Lh L : List ℕ) {c : ℕ} (γ : Fin c → T) (E' : EvalEnv T K') (E : EvalEnv T K)
    (l : List (String × ℕ)) : Prop where
  pres : FamPres h.toRingHom U
  closed : PClosed U
  eqf : EqFamP U
  lab : ∀ p, U p → p.2.lab ∉ L ∧ p.2.lab ∉ Lh
  ctx : ∀ k x' x, E'.ctxAt c γ k = Sum.inr x' → E.ctxAt c γ k = Sum.inr x → U (x', x)
  lh : ∀ l ∈ Lh, l ∉ L
  holes : ∀ s m, (s, m) ∈ l → Multiset.Rel (fun r' r => GenRow.Sim h r' r
    ∧ RowJoint h U (fun _ => False) Lh r' r) (E'.holes s m) (E.holes s m)

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
theorem JointEnv.sub {h : SemiringWithMonusHom K K'} {U : AggTok T K' × AggTok T K → Prop}
    {Lh L L' : List ℕ} {c : ℕ} {γ : Fin c → T} {E' : EvalEnv T K'} {E : EvalEnv T K}
    {l l' : List (String × ℕ)} (hJ : JointEnv h U Lh L γ E' E l)
    (hL : ∀ x ∈ L', x ∈ L) (hl : ∀ x ∈ l', x ∈ l) : JointEnv h U Lh L' γ E' E l' :=
  ⟨hJ.pres, hJ.closed, hJ.eqf, fun p hp => ⟨fun h' => (hJ.lab p hp).1 (hL _ h'), (hJ.lab p hp).2⟩,
    hJ.ctx, fun x hx hx' => hJ.lh x hx (hL _ hx'), fun s m hsm => hJ.holes s m (hl _ hsm)⟩

/-- **The joint simulation of two rows**: the row-wise simulation, and the
rows' families presented, read from at most one round, which there is
none of when nothing is bound. -/
def GenRow.SimJ (h : SemiringWithMonusHom K K') (U : AggTok T K' × AggTok T K → Prop)
    (Lh L : List ℕ) (l : List (String × ℕ)) {n : ℕ} (r' : GenRow T K' n) (r : GenRow T K n) :
    Prop :=
  GenRow.Sim h r' r ∧ ∃ H, (l = [] → ∀ p, ¬ H p) ∧ HoleOK U H Lh ∧ RowJoint h U H L r' r

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [CommSemiringWithMonus K]
  [CommSemiringWithMonus K'] [DecidableEq K'] in
theorem HoleOK.empty (U : AggTok T K' × AggTok T K → Prop) (Lh : List ℕ) :
    HoleOK U (fun _ => False) Lh :=
  ⟨fun p hp => by
    induction hp with
    | base h => exact h
    | step _ _ ih => exact ih
    | stepF _ _ ih => exact ih,
   fun _ h => h.elim, fun _ h => h.elim⟩

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- A joint simulation that reads no round. -/
theorem GenRow.SimJ.of_noHole {h : SemiringWithMonusHom K K'} {U : AggTok T K' × AggTok T K → Prop}
    {Lh L : List ℕ} {l : List (String × ℕ)} {n : ℕ} {r' : GenRow T K' n} {r : GenRow T K n}
    (hs : GenRow.Sim h r' r) (hr : RowJoint h U (fun _ => False) L r' r) :
    GenRow.SimJ h U Lh L l r' r :=
  ⟨hs, fun _ => False, fun _ _ h => h, HoleOK.empty U Lh, hr⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [CommSemiringWithMonus K'] [DecidableEq K']
  [HasAltLinearOrder K] [HasAltLinearOrder K'] in
omit [ValueType T] in
/-- An annotated tuple read back holds no aggregate value. -/
theorem rowPairs_ofAnnotated {n : ℕ} (p' : AnnotatedTuple T K' n) (p : AnnotatedTuple T K n)
    (q : AggTok T K' × AggTok T K) :
    ¬ rowPairs (GenRow.ofAnnotated p').fst (GenRow.ofAnnotated p).fst q := by
  rintro ⟨k, h1, -⟩
  exact Sum.inl_ne_inr h1

omit [DecidableEq K] [DecidableEq K'] [HasAltLinearOrder K] [HasAltLinearOrder K']
  [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
/-- **A projection column holds a term over a column of its row**, on
both sides alike. -/
theorem ProjColIn.pcl_eval {cI mI : ℕ} {κ : Fin mI → ColKind} (pc : ProjColIn T cI κ)
    {γ : Fin cI → T} {u' : Tuple (GenValue T K') mI} {u : Tuple (GenValue T K) mI}
    {y' : AggTok T K'} {y : AggTok T K} (h1 : pc.eval u' γ = Sum.inr y')
    (h2 : pc.eval u γ = Sum.inr y) : PCl (rowPairs u' u) (y', y) := by
  cases pc with
  | term t => exact absurd h2 (by simp [ProjColIn.eval])
  | provTerm t => exact absurd h2 (by simp [ProjColIn.eval])
  | token k hk => exact PCl.base ⟨k, h1, h2⟩
  | aggTerm k hk gf =>
    simp only [ProjColIn.eval] at h1 h2
    rcases hu : u k with v | x <;> rcases hu' : u' k with v' | x'
    all_goals rw [hu] at h2; rw [hu'] at h1
    all_goals simp only [Sum.map_inl, Sum.map_inr, reduceCtorEq, Sum.inr.injEq] at h1 h2
    subst h1 h2
    exact PCl.stepF gf (PCl.base (S := rowPairs u' u) (p := (x', x)) ⟨k, hu', hu⟩)
  | aggTermOf k hk t =>
    simp only [ProjColIn.eval] at h1 h2
    rcases hu : u k with v | x <;> rcases hu' : u' k with v' | x'
    all_goals rw [hu] at h2; rw [hu'] at h1
    all_goals simp only [Sum.map_inl, Sum.map_inr, reduceCtorEq, Sum.inr.injEq] at h1 h2
    subst h1 h2
    exact PCl.step t (PCl.base (S := rowPairs u' u) (p := (x', x)) ⟨k, hu', hu⟩)

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
theorem GenRow.SimJ.mono {h : SemiringWithMonusHom K K'} {U : AggTok T K' × AggTok T K → Prop}
    {Lh L L' : List ℕ} {l l' : List (String × ℕ)} (hL : ∀ x ∈ L, x ∈ L')
    (hl : l' = [] → l = []) {n : ℕ} {r' : GenRow T K' n} {r : GenRow T K n}
    (hs : GenRow.SimJ h U Lh L l r' r) : GenRow.SimJ h U Lh L' l' r' r := by
  obtain ⟨hsim, H, hH0, hHok, hrow⟩ := hs
  exact ⟨hsim, H, fun h' => hH0 (hl h'), hHok, hrow.mono_labels hL⟩

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

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [CommSemiringWithMonus K]
  [CommSemiringWithMonus K'] [DecidableEq K'] in
theorem HoleOK.or {U H₁ H₂ : AggTok T K' × AggTok T K → Prop} {Lh : List ℕ}
    (h₁ : HoleOK U H₁ Lh) (h₂ : HoleOK U H₂ Lh) : HoleOK U (fun p => H₁ p ∨ H₂ p) Lh := by
  refine ⟨fun p hp => ?_, fun p hp => hp.elim (h₁.2.1 p) (h₂.2.1 p),
    fun p hp => hp.elim (h₁.2.2 p) (h₂.2.2 p)⟩
  induction hp with
  | base h => exact h
  | @step q t _ ih =>
    exact Or.imp (fun hq => h₁.1 _ (PCl.step t (PCl.base hq)))
      (fun hq => h₂.1 _ (PCl.step t (PCl.base hq))) ih
  | @stepF q gf _ ih =>
    exact Or.imp (fun hq => h₁.1 _ (PCl.stepF gf (PCl.base hq)))
      (fun hq => h₂.1 _ (PCl.stepF gf (PCl.base hq))) ih

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- Annotated tuples read back simulate jointly: they hold no aggregate
value. -/
theorem rel_ofAnnotated_mapJ (h : SemiringWithMonusHom K K') {U : AggTok T K' × AggTok T K → Prop}
    (hU : FamPres h.toRingHom U) (Lh L : List ℕ) (l : List (String × ℕ)) {n : ℕ}
    (X : AnnotatedRelation T K n) :
    Multiset.Rel (GenRow.SimJ h U Lh L l)
      ((SemiringWithMonusHom.mapAnnotatedRelation h X).map GenRow.ofAnnotated)
      (X.map GenRow.ofAnnotated) := by
  refine (rel_ofAnnotated_map h X).mono (fun r' hr' r hr hs => ?_)
  refine GenRow.SimJ.of_noHole hs (RowJoint.of_noPairs hU _ (fun q hq => ?_))
  obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨p', -, rfl⟩ := Multiset.mem_map.mp hr'
  exact rowPairs_ofAnnotated p' p q hq

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- A row read from a round, once the round's own contributions are
counted among the labels. -/
theorem RowJoint.absorb {h : SemiringWithMonusHom K K'} {U H : AggTok T K' × AggTok T K → Prop}
    {L Lh : List ℕ} (hH : HoleOK U H Lh) {n : ℕ} {r' : GenRow T K' n} {r : GenRow T K n}
    (hr : RowJoint h U H L r' r) : RowJoint h U (fun _ => False) (L ++ Lh) r' r := by
  refine ⟨hr.1.mono (fun p hp => hp.elim Or.inl (fun h' => h'.elim (fun h'' => Or.inr (Or.inl h''))
    False.elim)), fun p hp => ?_, hr.2.2⟩
  rcases hr.2.1 p hp with h' | h' | h'
  · exact Or.inl h'
  · rcases hH.2.2 p h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inr (List.mem_append_right _ h''))
  · exact Or.inr (Or.inr (List.mem_append_left _ h'))

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [ValueType T] [DecidableEq K'] in
/-- A row read from no round. -/
theorem RowJoint.of_emptyHole {h : SemiringWithMonusHom K K'}
    {U H : AggTok T K' × AggTok T K → Prop}
    {L : List ℕ} (hH : ∀ p, ¬ H p) {n : ℕ} {r' : GenRow T K' n} {r : GenRow T K n}
    (hr : RowJoint h U H L r' r) : RowJoint h U (fun _ => False) L r' r :=
  ⟨hr.1.mono (fun _ hp => hp.elim Or.inl (fun h' => h'.elim (fun h'' => Or.inr (Or.inl h''))
    False.elim)), fun p hp => (hr.2.1 p hp).imp_right (fun h' => h'.imp_left (fun h'' =>
      absurd h'' (hH p))), hr.2.2⟩

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- **Entering a recursion's body**: the round bound to its name, rows
simulating each other with their families presented, the round's own
labels `Lh'` kept apart from the body's. -/
theorem JointEnv.assignHole {h : SemiringWithMonusHom K K'} {U : AggTok T K' × AggTok T K → Prop}
    {Lh L Lh' L' : List ℕ} {c : ℕ} {γ : Fin c → T} {E' : EvalEnv T K'} {E : EvalEnv T K}
    {l : List (String × ℕ)} (hJ : JointEnv h U Lh L γ E' E l)
    (hUl : ∀ p, U p → p.2.lab ∉ L' ∧ p.2.lab ∉ Lh') (hlh : ∀ x ∈ Lh', x ∉ L')
    (s : String) {m : ℕ} {X' : Multiset (GenRow T K' m)} {X : Multiset (GenRow T K m)}
    (hX : Multiset.Rel (fun r' r => GenRow.Sim h r' r
      ∧ RowJoint h U (fun _ => False) Lh' r' r) X' X) :
    JointEnv h U Lh' L' γ (E'.assignHole s X') (E.assignHole s X) [(s, m)] := by
  refine ⟨hJ.pres, hJ.closed, hJ.eqf, hUl, fun k x' x h1 h2 => ?_, hlh, fun s' m' hsm => ?_⟩
  · rw [EvalEnv.ctxAt_assignHole] at h1 h2
    exact hJ.ctx k x' x h1 h2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hsm)
    simp only [EvalEnv.assignHole, and_self, ↓reduceDIte]
    exact hX

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- **The two sides stamp the same parameters**: the context's regular
values are equal and its aggregate values carry one family identifier. -/
theorem EvalEnv.paramKey_eq_of_joint {h : SemiringWithMonusHom K K'}
    {U : AggTok T K' × AggTok T K → Prop} {Lh L : List ℕ} {c : ℕ} {γ : Fin c → T}
    {E' : EvalEnv T K'} {E : EvalEnv T K} {l : List (String × ℕ)} (hE : E'.HomSim h E γ)
    (hJ : JointEnv h U Lh L γ E' E l) (rd : Fin c → Bool) :
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
      exact congrArg Sum.inr (hJ.eqf _ (hJ.ctx k x' x hc' hc))

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [ValueType T] [DecidableEq K'] in
/-- **A row of fresh values of one family**: values built by one operator,
labelled `lab`, presented together, carrying one family identifier per
pair and one class on each side. -/
theorem RowJoint.fresh_row {h : SemiringWithMonusHom K K'} {U : AggTok T K' × AggTok T K → Prop}
    (hU : FamPres h.toRingHom U) (hUf : EqFamP U) (lab : ℕ) (hUl : ∀ p, U p → p.2.lab ≠ lab)
    {L : List ℕ} (hL : lab ∈ L) {n : ℕ} {r' : GenRow T K' n} {r : GenRow T K n}
    (hfam : ∀ p, rowPairs r'.fst r.fst p → p.1.fam = p.2.fam ∧ p.2.lab = lab)
    (hkeys : ∀ p q, rowPairs r'.fst r.fst p → rowPairs r'.fst r.fst q →
      p.1.classKey = q.1.classKey ∧ p.2.classKey = q.2.classKey)
    (hpres : (∃ D : ListingRel h.toRingHom T, ∀ q, rowPairs r'.fst r.fst q → D.Member q.1 q.2)
      ∨ (∃ O O', NestRel h.toRingHom O' O
        ∧ ∀ q, rowPairs r'.fst r.fst q → NestMember O' O q.1 q.2)) :
    RowJoint h U (fun _ => False) L r' r := by
  refine ⟨(FamPres.fresh lab hU (fun p hp => ⟨hUl p hp, ?_⟩) (fun p hp => ⟨(hfam p hp).2, ?_⟩)
    hkeys hpres).mono (fun p hp => hp.elim Or.inl (fun h' => h'.elim Or.inr False.elim)),
    fun p hp => Or.inr (Or.inr (by rw [(hfam p hp).2]; exact hL)), fun p hp => (hfam p hp).1⟩
  · rw [show p.1.lab = p.2.lab from congrArg FamId.lab (hUf p hp)]; exact hUl p hp
  · rw [show p.1.lab = p.2.lab from congrArg FamId.lab (hfam p hp).1]; exact (hfam p hp).2

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

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [DecidableEq K'] in
/-- **The columns of one group of a grouping are a presented family**:
built from one listing of the group on each side, the two tie-block
permuted. -/
theorem RowJoint.group_cols {h : SemiringWithMonusHom K K'} {U : AggTok T K' × AggTok T K → Prop}
    (hU : FamPres h.toRingHom U) (hUf : EqFamP U) (lab : ℕ) (hUl : ∀ p, U p → p.2.lab ≠ lab)
    {L : List ℕ} (hL : lab ∈ L) {c m n₂ : ℕ} (fs : Fin n₂ → SeqAggFunc T)
    (ts : Fin n₂ → TermIn T c m) (keep : Fin n₂ → Option (Selection T m)) (sc : Bool)
    (γ : Fin c → T) (U₀ : List (AnnotatedTuple T K m)) (U₀' : List (AnnotatedTuple T K' m))
    (hp : TiePerm (fun p q : AnnotatedTuple T K' m => p.fst = q.fst)
      (U₀.map (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) U₀')
    (key : List T) (params : List (T ⊕ FamId T)) {n : ℕ} {r' : GenRow T K' n}
    {r : GenRow T K n}
    (hrow : ∀ p, rowPairs r'.fst r.fst p → ∃ j : Fin n₂,
      p = (((groupTok (fs j) (ts j) (keep j) sc U₀' γ).setFam (.mk lab key params j [])),
        ((groupTok (fs j) (ts j) (keep j) sc U₀ γ).setFam (.mk lab key params j [])))) :
    RowJoint h U (fun _ => False) L r' r := by
  obtain ⟨D, hD⟩ := ListingRel.exists_group h.toRingHom U₀ U₀' hp
  refine RowJoint.fresh_row hU hUf lab hUl hL (fun p hp => ?_) (fun p q hp hq => ?_)
    (Or.inl ⟨D, fun q hq => ?_⟩)
  · obtain ⟨j, rfl⟩ := hrow p hp
    exact ⟨by simp [AggTok.fam_setFam], by simp [AggTok.lab, AggTok.fam_setFam, FamId.lab]⟩
  · obtain ⟨j, rfl⟩ := hrow p hp
    obtain ⟨j', rfl⟩ := hrow q hq
    simp only [classKey_groupTok, FamId.family]
    exact ⟨trivial, trivial⟩
  · obtain ⟨j, rfl⟩ := hrow q hq
    exact hD _ _ (groupSpec (fs j) (ts j) γ sc (keep j)) _ _
      (by cases keep j <;> rfl) (by cases keep j <;> rfl)
      (flatExpr_groupTok _ _ _ _ _ _ _) (flatExpr_groupTok _ _ _ _ _ _ _)

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

omit [CommSemiringWithMonus K] [DecidableEq K] [CommSemiringWithMonus K'] [DecidableEq K']
  [HasAltLinearOrder K] [HasAltLinearOrder K'] in
omit [ValueType T] in
/-- A row of regular values and one aggregate value holds one pair. -/
theorem rowPairs_append_one {n₁ : ℕ} {a' : Fin n₁ → GenValue T K'} {a : Fin n₁ → GenValue T K}
    (ha : ∀ k x, a k ≠ Sum.inr x) {x' : AggTok T K'} {x : AggTok T K}
    {q : AggTok T K' × AggTok T K}
    (hq : rowPairs (Fin.append a' (fun _ : Fin 1 => Sum.inr x'))
      (Fin.append a (fun _ : Fin 1 => Sum.inr x)) q) : q = (x', x) := by
  obtain ⟨k, h1, h2⟩ := hq
  refine Fin.addCases (fun i h1 h2 => ?_) (fun j h1 h2 => ?_) k h1 h2
  · rw [Fin.append_left] at h2; exact absurd h2 (ha i _)
  · rw [Fin.append_right] at h1 h2
    exact Prod.ext (Sum.inr_injective h1).symm (Sum.inr_injective h2).symm

omit [CommSemiringWithMonus K] [DecidableEq K] [CommSemiringWithMonus K'] [DecidableEq K']
  [HasAltLinearOrder K] [HasAltLinearOrder K'] in
omit [ValueType T] in
/-- The same, the aggregate value last. -/
theorem rowPairs_snoc_one {n₁ : ℕ} {a' : Fin n₁ → GenValue T K'} {a : Fin n₁ → GenValue T K}
    (ha : ∀ k x, a k ≠ Sum.inr x) {x' : AggTok T K'} {x : AggTok T K}
    {q : AggTok T K' × AggTok T K}
    (hq : rowPairs (Fin.snoc a' (Sum.inr x') : Fin (n₁ + 1) → GenValue T K')
      (Fin.snoc a (Sum.inr x) : Fin (n₁ + 1) → GenValue T K) q) : q = (x', x) := by
  obtain ⟨k, h1, h2⟩ := hq
  refine Fin.lastCases (fun h1 h2 => ?_) (fun i h1 h2 => ?_) k h1 h2
  · rw [Fin.snoc_last] at h1 h2
    exact Prod.ext (Sum.inr_injective h1).symm (Sum.inr_injective h2).symm
  · rw [Fin.snoc_castSucc] at h2; exact absurd h2 (ha i _)

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

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] [ValueType T] [DecidableEq K'] in
/-- **A row gaining one fresh value**: the row's families stay presented,
and the new value is a family of its own, labelled `lab`. -/
theorem RowJoint.snoc_fresh {h : SemiringWithMonusHom K K'} {U : AggTok T K' × AggTok T K → Prop}
    (hUf : EqFamP U) (lab : ℕ) (hUl : ∀ p, U p → p.2.lab ≠ lab) {L₀ : List ℕ} (hlab : lab ∉ L₀)
    {n : ℕ} {x' : GenRow T K' n} {x : GenRow T K n}
    (hx : RowJoint h U (fun _ => False) L₀ x' x) {y' : AggTok T K'} {y : AggTok T K}
    (hfam : y'.fam = y.fam) (hyl : y.lab = lab)
    (hD : ∃ D : ListingRel h.toRingHom T, D.Member y' y) (b' : GenAnn K') (b : GenAnn K) :
    RowJoint h U (fun _ => False) (lab :: L₀)
      ((Fin.snoc x'.fst (Sum.inr y') : Fin (n + 1) → GenValue T K'), b')
      ((Fin.snoc x.fst (Sum.inr y) : Fin (n + 1) → GenValue T K), b) := by
  have hpairs : ∀ p, rowPairs (Fin.snoc x'.fst (Sum.inr y') : Fin (n + 1) → GenValue T K')
      (Fin.snoc x.fst (Sum.inr y) : Fin (n + 1) → GenValue T K) p
      → rowPairs x'.fst x.fst p ∨ p = (y', y) := by
    rintro p ⟨k, h1, h2⟩
    refine Fin.lastCases (fun h1 h2 => ?_) (fun i h1 h2 => ?_) k h1 h2
    · rw [Fin.snoc_last] at h1 h2
      exact Or.inr (Prod.ext (Sum.inr_injective h1).symm (Sum.inr_injective h2).symm)
    · rw [Fin.snoc_castSucc] at h1 h2
      exact Or.inl ⟨i, h1, h2⟩
  have hyl' : y'.lab = lab := by rw [AggTok.lab, hfam]; exact hyl
  have hCl : ∀ p, (rowPairs x'.fst x.fst p ∨ U p) → p.2.lab ≠ lab ∧ p.1.lab ≠ lab := by
    intro p hp
    have h2 : p.2.lab ≠ lab := by
      rcases hp with hp | hp
      · rcases hx.2.1 p hp with h' | h' | h'
        · exact hUl p h'
        · exact h'.elim
        · exact fun he => hlab (he ▸ h')
      · exact hUl p hp
    refine ⟨h2, ?_⟩
    have : p.1.fam = p.2.fam := hp.elim (hx.2.2 p) (hUf p)
    rw [AggTok.lab, this]; exact h2
  have hF := FamPres.fresh (A := fun p => p = (y', y)) lab
    (hx.1.mono (fun p hp => hp.elim Or.inl (fun h' => Or.inr (Or.inl h')))) hCl
    (fun p hp => by subst hp; exact ⟨hyl, hyl'⟩)
    (fun p q hp hq => by subst hp; subst hq; exact ⟨rfl, rfl⟩)
    (Or.inl (let ⟨D, hD⟩ := hD; ⟨D, fun q hq => by subst hq; exact hD⟩))
  refine ⟨hF.mono (fun p hp => ?_), fun p hp => ?_, fun p hp => ?_⟩
  · rcases hp with hp | hp | hp
    · rcases hpairs p hp with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inl h'
    · exact Or.inr (Or.inr hp)
    · exact hp.elim
  · rcases hpairs p hp with h' | h'
    · rcases hx.2.1 p h' with h'' | h'' | h''
      · exact Or.inl h''
      · exact h''.elim
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h''))
    · subst h'; exact Or.inr (Or.inr (by rw [hyl]; exact List.mem_cons_self))
  · rcases hpairs p hp with h' | h'
    · exact hx.2.2 p h'
    · subst h'; exact hfam

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

/-- **Joint row-wise simulation.** The row-wise simulation, carrying
besides how each row's families are presented on the two sides – which
is what a selection comparing several aggregate values of one family
needs. -/
theorem AggQueryIn.evaluate_hom_rel_env (h : SemiringWithMonusHom K K') :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (d : AnnotatedDatabase T K) (γ : Fin c → T) (E' : EvalEnv T K') (E : EvalEnv T K)
      (U : AggTok T K' × AggTok T K → Prop) (Lh : List ℕ),
      E'.HomSim h E γ → JointEnv h U Lh q.labels γ E' E l → l.length ≤ 1 →
      q.framesContainSelf → q.nestInComplemented (K := K') → q.labelsDistinct →
      q.muBodyTokFree → q.AnnSettlesAt d γ E →
      Multiset.Rel (GenRow.SimJ h U Lh q.labels l)
        (q.evaluate (h.mapAnnotatedDatabase d) γ E')
        (q.evaluate d γ E) := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate, SemiringWithMonusHom.find_mapAnnotatedDatabase]
    cases hf : d.find n s with
    | none =>
      simp only [Option.map_none]
      exact Multiset.Rel.zero
    | some rn =>
      simp only [Option.map_some]
      refine (rel_ofAnnotated_map h rn).mono (fun r' hr' r hr hs => ?_)
      refine GenRow.SimJ.of_noHole hs (RowJoint.of_noPairs hJ.pres _ (fun q hq => ?_))
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      obtain ⟨p', -, rfl⟩ := Multiset.mem_map.mp hr'
      exact rowPairs_ofAnnotated p' p q hq
  | Hole n s κ =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    refine (rel_filter_of_iff (hJ.holes s n (List.mem_singleton_self _))
      (fun r' r hs => forall_congr' fun k => by rw [(hs.1.1 k).kindOf_eq])).mono
      (fun r' _ r _ hs => ⟨hs.1, PCl (rowPairs r'.fst r.fst), fun h => absurd h (by simp), ?_, ?_⟩)
    · refine ⟨PClosed.pcl _, EqFamP.pcl hs.2.2.2, fun p hp => ?_⟩
      exact PCl.origin hJ.closed (fun q hq => (hs.2.2.1 q hq).elim Or.inl
        (fun h => h.elim False.elim Or.inr)) hp
    · refine ⟨hs.2.1.pcl.mono (fun p hp => ?_), fun p hp => Or.inr (Or.inl (PCl.base hp)),
        hs.2.2.2⟩
      rcases hp with hp | hp | hp
      · exact PCl.base (Or.inl hp)
      · exact PCl.base (Or.inr (Or.inl hp))
      · exact hp.mono (fun q hq => Or.inl hq)
  | Param pv ρ =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    refine (hE.paramRows pv ρ).mono (fun r' hr' r hr hs => ?_)
    refine GenRow.SimJ.of_noHole hs (RowJoint.of_env hJ.pres hJ.eqf _ (fun q hq => ?_))
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
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    exact Multiset.Rel.zero
  | Proj ps q ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    refine rel_map_of_rel (ih d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec)
      (fun r' r hs => ⟨⟨fun j => (ps j).equiv_eval_of_sim h hs.1.1, ?_⟩, ?_⟩)
    · rw [GenAnn.finalize_cash _ _ _ Multiset.inter_le_left,
        GenAnn.finalize_cash _ _ _ Multiset.inter_le_left]
      exact hs.1.2
    · obtain ⟨H, hH0, hHok, hrow⟩ := hs.2
      exact ⟨H, hH0, hHok, RowJoint.of_pcl hJ.closed hHok.1 hrow
        (fun p ⟨j, h1, h2⟩ => (ps j).pcl_eval h1 h2)⟩
  | Sel φ q hφ ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    by_cases hagg : φ.hasAggAtom
    · rw [ite_eq_left hagg, ite_eq_left hagg]
      refine rel_map_of_rel (ih d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec)
        (fun r' r hs => ⟨⟨hs.1.1, ?_⟩, hs.2⟩)
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
      · obtain ⟨H, -, -, hrow⟩ := hs.2
        rw [GenPredIn.predsemJ_hom_famPres h φ false hs.1.1
          (hrow.1.mono (fun p hp => Or.inl hp)), hs.1.2, ← map_mul]
      all_goals
        intro l hl
        obtain ⟨k, hk, hkl⟩ := (Multiset.mem_filterMap _ _).mp hl
        refine ⟨k, Finset.mem_val.mp hk, ?_⟩
        split at hkl
        · exact absurd hkl (by simp)
        · exact ⟨_, by assumption⟩
    · rw [ite_eq_right hagg, ite_eq_right hagg]
      refine rel_filter_of_iff (ih d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec)
        (fun r' r hs => ?_)
      calc φ.holds r'.fst γ
          ↔ φ.holds (fun k => AggValue.mapAnnSum ⇑h.toRingHom (r.fst k)) γ :=
            GenPredIn.holds_equiv _ hs.1.1
        _ ↔ φ.holds r.fst γ := GenPredIn.holds_mapAnnSum h φ r.fst
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    rename_i l₁ l₂
    have hl : l₁ = [] ∨ l₂ = [] := by
      rw [List.length_append] at hl1
      rcases l₁ with _ | ⟨a, _ | ⟨b, l₁⟩⟩
      · exact Or.inl rfl
      · rcases l₂ with _ | ⟨c, l₂⟩
        · exact Or.inr rfl
        · simp at hl1
      · simp at hl1; omega
    have hnd := List.nodup_append.mp hlab
    refine rel_map_of_rel (rel_product
      (ih₁ d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_append_left _ hx)
        (fun x hx => List.mem_append_left _ hx)) (by simp at hl1; omega) hw.1 hn.1
        hnd.1 hmu.1 hrec.1)
      (ih₂ d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_append_right _ hx)
        (fun x hx => List.mem_append_right _ hx)) (by simp at hl1; omega) hw.2 hn.2
        hnd.2.1 hmu.2 hrec.2)) ?_
    rintro ⟨x', y'⟩ ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨H₁, hH₁0, hH₁, hrx⟩ := hx.2
    obtain ⟨H₂, hH₂0, hH₂, hry⟩ := hy.2
    refine ⟨⟨?_, ?_⟩, fun p => H₁ p ∨ H₂ p, fun h' p hp => ?_, hH₁.or hH₂, ?_⟩
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
    · obtain ⟨h₁, h₂⟩ := List.append_eq_nil_iff.mp h'
      exact hp.elim (hH₁0 h₁ p) (hH₂0 h₂ p)
    · refine RowJoint.append (fun p hp => ?_) (fun a ha ha' => hnd.2.2 a ha a ha' rfl)
        (fun a ha ha' => hJ.lh a ha (List.mem_append_left _ ha'))
        (fun a ha ha' => hJ.lh a ha (List.mem_append_right _ ha')) hH₁ hH₂
        (hl.imp (fun h' => hH₁0 h') (fun h' => hH₂0 h')) hrx hry _ _
      exact ⟨fun h' => (hJ.lab p hp).1 (List.mem_append_left _ h'),
        fun h' => (hJ.lab p hp).1 (List.mem_append_right _ h'), (hJ.lab p hp).2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    have hnd := List.nodup_append.mp hlab
    refine rel_bind ((ih₁ d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_append_left _ hx)
        (fun x hx => hx)) hl1 hw.1 hn.1 hnd.1 hmu.1 hrec.1).mono
      (p := fun x' x => GenRow.SimJ h U Lh q₁.labels _ x' x ∧ x ∈ q₁.evaluate d γ E)
      (fun _ _ x hx hs => ⟨hs, hx⟩)) (fun x' x hxx' => ?_)
    obtain ⟨hxx, hxm⟩ := hxx'
    obtain ⟨Hx, hHx0, hHx, hrx⟩ := hxx.2
    have hplain : GenRow.plainTuple x'.fst = GenRow.plainTuple x.fst := by
      funext k
      exact (hxx.1.1 k).collapseSum_eq.trans
        (AggValue.collapseSum_mapAnnSum ⇑h.toRingHom (x.fst k))
    rw [hplain]
    -- the right side reads the left row's values as part of its universe
    set Ux : AggTok T K' × AggTok T K → Prop :=
      PCl (fun p => rowPairs x'.fst x.fst p ∨ U p ∨ Hx p) with hUx
    have hUH : HoleOK U (fun p => U p ∨ Hx p) Lh :=
      HoleOK.or (H₁ := U) ⟨hJ.closed, hJ.eqf, fun p hp => Or.inl hp⟩ hHx
    have horig : ∀ p, Ux p → (U p ∨ Hx p) ∨ p.2.lab ∈ q₁.labels := by
      intro p hp
      exact PCl.origin hUH.1 (fun q hq => by
        rcases hq with hq | hq | hq
        · rcases hrx.2.1 q hq with h' | h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
        · exact Or.inl (Or.inl hq)
        · exact Or.inl (Or.inr hq)) hp
    have hJx : JointEnv h Ux [] q₂.labels (Fin.append (GenRow.plainTuple x.fst) γ)
        (E'.withCtx (Fin.append x'.fst (E'.ctxAt _ γ)))
        (E.withCtx (Fin.append x.fst (E.ctxAt _ γ))) [] := by
      refine ⟨hrx.1.pcl, PClosed.pcl _, EqFamP.pcl (fun p hp => ?_), fun p hp => ⟨?_, by simp⟩,
        fun k x₁' x₁ h1 h2 => ?_, fun _ h' => absurd h' (by simp),
        fun _ _ h' => absurd h' (by simp)⟩
      · rcases hp with hp | hp | hp
        · exact hrx.2.2 p hp
        · exact hJ.eqf p hp
        · exact hHx.2.1 p hp
      · intro hl₂
        rcases horig p hp with (h' | h') | h'
        · exact (hJ.lab p h').1 (List.mem_append_right _ hl₂)
        · rcases hHx.2.2 p h' with h'' | h''
          · exact (hJ.lab p h'').1 (List.mem_append_right _ hl₂)
          · exact hJ.lh _ h'' (List.mem_append_right _ hl₂)
        · exact hnd.2.2 _ h' _ hl₂ rfl
      · rw [EvalEnv.ctxAt_withCtx] at h1 h2
        refine Fin.addCases (fun i h1 h2 => ?_) (fun j h1 h2 => ?_) k h1 h2
        · rw [Fin.append_left] at h1 h2
          exact PCl.base (Or.inl ⟨i, h1, h2⟩)
        · rw [Fin.append_right] at h1 h2
          exact PCl.base (Or.inr (Or.inl (hJ.ctx j _ _ h1 h2)))
    refine rel_map_of_rel
      (ih₂ d (Fin.append (GenRow.plainTuple x.fst) γ) _ _ Ux [] (hE.enter hxx.1.1 _) hJx
        (by simp) hw.2 hn.2 hnd.2.1 hmu.2 (hrec.2 x hxm))
      (fun y' y hy => ?_)
    obtain ⟨Hy, hHy0, -, hry⟩ := hy.2
    have hHyE : ∀ p, ¬ Hy p := hHy0 rfl
    refine ⟨⟨?_, ?_⟩, Hx, hHx0, hHx, ?_, ?_, ?_⟩
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
    · refine hry.1.mono (fun p hp => ?_)
      rcases hp with hp | hp | hp
      · rcases (rowPairs_append _ _ _ _ p).mp hp with h' | h'
        · exact Or.inr (Or.inl (PCl.base (Or.inl h')))
        · exact Or.inl h'
      · exact Or.inr (Or.inl (PCl.base (Or.inr (Or.inl hp))))
      · exact Or.inr (Or.inl (PCl.base (Or.inr (Or.inr hp))))
    · intro p hp
      rcases (rowPairs_append _ _ _ _ p).mp hp with h' | h'
      · rcases hrx.2.1 p h' with h'' | h'' | h''
        · exact Or.inl h''
        · exact Or.inr (Or.inl h'')
        · exact Or.inr (Or.inr (List.mem_append_left _ h''))
      · rcases hry.2.1 p h' with h'' | h'' | h''
        · rcases horig p h'' with (h₃ | h₃) | h₃
          · exact Or.inl h₃
          · exact Or.inr (Or.inl h₃)
          · exact Or.inr (Or.inr (List.mem_append_left _ h₃))
        · exact absurd h'' (hHyE p)
        · exact Or.inr (Or.inr (List.mem_append_right _ h''))
    · intro p hp
      rcases (rowPairs_append _ _ _ _ p).mp hp with h' | h'
      · exact hrx.2.2 p h'
      · exact hry.2.2 p h'
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    have hl₁ : _ := List.length_append ▸ hl1
    exact Multiset.Rel.add
      ((ih₁ d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_append_left _ hx)
        (fun x hx => List.mem_append_left _ hx)) (by simp at hl1; omega) hw.1 hn.1
        hlab.of_append_left hmu.1 hrec.1).mono (fun _ _ _ _ hs =>
          hs.mono (fun x hx => List.mem_append_left _ hx)
            (fun h' => (List.append_eq_nil_iff.mp h').1)))
      ((ih₂ d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_append_right _ hx)
        (fun x hx => List.mem_append_right _ hx)) (by simp at hl1; omega) hw.2 hn.2
        hlab.of_append_right hmu.2 hrec.2).mono (fun _ _ _ _ hs =>
          hs.mono (fun x hx => List.mem_append_right _ hx)
            (fun h' => (List.append_eq_nil_iff.mp h').2)))
  | Dedup q ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    rw [show (q.evaluate
          (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q.evaluate d γ E).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)]
    rw [groupByKey_mapAnnotatedRelation]
    exact rel_ofAnnotated_mapJ h hJ.pres _ _ _ _
  | Explode k hk q ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    refine rel_bind_of_rel (ih d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec)
      (fun r' r hs => (sim_alternativesAt h hs.1 k).mono (fun a' ha' a ha hsa => ?_))
    obtain ⟨H, hH0, hHok, hrow⟩ := hs.2
    refine ⟨hsa, H, hH0, hHok, RowJoint.of_pcl hJ.closed hHok.1 hrow (fun p hp => PCl.base ?_)⟩
    obtain ⟨j, h1, h2⟩ := hp
    exact ⟨j, GenRow.inr_of_mem_alternativesAt ha' h1, GenRow.inr_of_mem_alternativesAt ha h2⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    have hnd := List.nodup_append.mp hlab
    simp only [AggQueryIn.evaluate]
    -- the rounds simulate each other, their families those of the base
    have hrounds := muSumFix_rel
      (R := fun r' r => GenRow.Sim h r' r ∧ RowJoint h U (fun _ => False) q₀.labels r' r)
      ((ih₀ d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_append_left _ hx) (fun x hx => hx))
          (by simp) hw.1 hn.1 hnd.1 hmu.1 hrec.1).mono (fun r' _ r _ hs => ⟨hs.1, by
            obtain ⟨H, hH0, -, hr⟩ := hs.2
            exact RowJoint.of_emptyHole (hH0 rfl) hr⟩))
      (fun k X' hX => (ih₁ d γ _ _ U q₀.labels (hE.assignHole s (hX.mono (fun _ _ _ _ h' => h'.1)))
          (hJ.assignHole (fun p hp => ⟨fun h' => (hJ.lab p hp).1 (List.mem_append_right _ h'),
            fun h' => (hJ.lab p hp).1 (List.mem_append_left _ h')⟩)
            (fun x _ h' => by rw [hmu.2.1] at h'; exact absurd h' List.not_mem_nil) s hX)
          (by simp) hw.2 hn.2 hnd.2.1 hmu.2.2 (hrec.2.2.2.1 k)).mono (fun r' _ r _ hs => ⟨hs.1, by
            obtain ⟨H, -, hHok, hr⟩ := hs.2
            exact (RowJoint.absorb hHok hr).mono_labels (fun x hx => by
              rw [hmu.2.1, List.nil_append] at hx; exact hx)⟩))
    exact hrounds.mono (fun r' _ r _ hs =>
      GenRow.SimJ.of_noHole hs.1 (hs.2.mono_labels (fun x hx => List.mem_append_left _ hx)))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    have hnd := List.nodup_append.mp hlab
    have hXJ : ∀ {m : ℕ} (X : AnnotatedRelation T K m), Multiset.Rel (fun r' r => GenRow.Sim h r' r
        ∧ RowJoint h U (fun _ => False) [] r' r)
        ((SemiringWithMonusHom.mapAnnotatedRelation h X).map GenRow.ofAnnotated)
        (X.map GenRow.ofAnnotated) := by
      intro m X
      refine (rel_ofAnnotated_map h X).mono (fun r' hr' r hr hs =>
        ⟨hs, RowJoint.of_noPairs hJ.pres _ (fun q hq => ?_)⟩)
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      obtain ⟨p', -, rfl⟩ := Multiset.mem_map.mp hr'
      exact rowPairs_ofAnnotated p' p q hq
    show Multiset.Rel _
      ((muFix (AggQueryIn.muSetStep s q₀ q₁ (h.mapAnnotatedDatabase d) γ E')).map
        GenRow.ofAnnotated)
      ((muFix (AggQueryIn.muSetStep s q₀ q₁ d γ E)).map GenRow.ofAnnotated)
    have e₀ : q₀.evaluateAnnotated (h.mapAnnotatedDatabase d) γ E'
        = SemiringWithMonusHom.mapAnnotatedRelation h (q₀.evaluateAnnotated d γ E) :=
      (map_eq_of_rel (ih₀ d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_append_left _ hx)
          (fun x hx => hx)) (by simp) hw.1 hn.1 hnd.1 hmu.1 hrec.1)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)).trans
        (Multiset.map_map (SemiringWithMonusHom.mapAnnotatedTuple h) GenRow.toAnnotated
          (q₀.evaluate d γ E)).symm
    have hstep : ∀ k, SemiringWithMonusHom.mapAnnotatedRelation h
          (AggQueryIn.muSetStep s q₀ q₁ d γ E
            (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k))
        = AggQueryIn.muSetStep s q₀ q₁ (h.mapAnnotatedDatabase d) γ E'
            (SemiringWithMonusHom.mapAnnotatedRelation h
              (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)) := by
      intro k
      have hk := hrec.2.2 k
      generalize muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k = X at hk ⊢
      have e₁ : q₁.evaluateAnnotated (h.mapAnnotatedDatabase d) γ (E'.assignHole s
            ((SemiringWithMonusHom.mapAnnotatedRelation h X).map GenRow.ofAnnotated))
          = SemiringWithMonusHom.mapAnnotatedRelation h
            (q₁.evaluateAnnotated d γ (E.assignHole s (X.map GenRow.ofAnnotated))) :=
        (map_eq_of_rel (ih₁ d γ _ _ U [] (hE.assignHole s (rel_ofAnnotated_map h X))
          (hJ.assignHole (fun p hp => ⟨fun h' => (hJ.lab p hp).1 (List.mem_append_right _ h'),
            by simp⟩) (by simp) s (hXJ X)) (by simp) hw.2 hn.2 hnd.2.1 hmu.2 hk)
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)).trans
          (Multiset.map_map (SemiringWithMonusHom.mapAnnotatedTuple h) GenRow.toAnnotated
            (q₁.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated)))).symm
      unfold AggQueryIn.muSetStep
      rw [dedupAnn_mapAnnotatedRelation, mapAnnotatedRelation_add, e₀, e₁]
    rw [← muFix_map_rounds (h := SemiringWithMonusHom.mapAnnotatedRelation h) rfl hstep hrec.2.1]
    exact rel_ofAnnotated_mapJ h hJ.pres _ _ _ _
  | @ProvSum cI m n₁ κ' is his t q ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    simp only [AggQueryIn.evaluate]
    rw [show (q.evaluate (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q.evaluate d γ E).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec)
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
    refine rel_map_of_forall (fun g _ => GenRow.SimJ.of_noHole ⟨?_, ?_⟩
      (RowJoint.of_noPairs hJ.pres _ ?_))
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
  | Retag hκ q ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    exact ih d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
  | @Win cI nI mI pI κw lab rd P O o w t f q hrr dist keep ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    have hpk := EvalEnv.paramKey_eq_of_joint hE hJ rd
    have hnd := List.nodup_cons.mp hlab
    have hsim := ih d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_cons_of_mem _ hx)
      (fun x hx => hx)) hl1 hw hn hnd.2 hmu hrec
    have hread : (q.evaluate (h.mapAnnotatedDatabase d) γ E').map
          (GenRow.readAnnotated κw)
        = ((q.evaluate d γ E).map (GenRow.readAnnotated κw)).map
            (fun p : AnnotatedTuple T K nI =>
              ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI)) := by
      rw [Multiset.map_map]
      exact map_eq_of_rel hsim
        (fun r' r hs => GenRow.Sim.readAnnotated_eq h κw hs.1)
    have hUl : ∀ p, U p → p.2.lab ≠ lab :=
      fun p hp h' => (hJ.lab p hp).1 (by rw [h']; exact List.mem_cons_self)
    cases hk : keep with
    | some φ =>
      rw [AggQueryIn.evaluate_Win_eq_when, AggQueryIn.evaluate_Win_eq_when, hread, hpk]
      refine Multiset.rel_map.mpr (hsim.mono (fun x' _ x hx hs => ?_))
      have hmem : GenRow.readAnnotated κw x
          ∈ Multiset.map (GenRow.readAnnotated κw) (q.evaluate d γ E) :=
        Multiset.mem_map_of_mem _ hx
      have hrd := GenRow.Sim.readAnnotated_eq h κw hs.1
      obtain ⟨H, hH0, -, hrow⟩ := hs.2
      refine ⟨⟨fun k => ?_, hs.1.2⟩, fun _ => False, fun _ _ h' => h', HoleOK.empty U Lh, ?_⟩
      · simp only [ValueFrame.windowGenRow]
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · rw [Fin.snoc_last, Fin.snoc_last, hrd]
          exact exprWhenOf_mapAnn_equiv h P O o w t γ f dist φ.keeps _ hmem
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hs.1.1 k'
      · simp only [ValueFrame.windowGenRow]
        rw [hrd]
        exact RowJoint.snoc_fresh hJ.eqf lab hUl hnd.1 (RowJoint.of_emptyHole (hH0 rfl) hrow)
          (by simp only [AggTok.fam_setFam]; rfl)
          (by simp [AggTok.lab, AggTok.fam_setFam, FamId.lab])
          (ListingRel.exists_exprWhenOf h P O o w t γ f dist φ.keeps _ hmem _ _) _ _
    | none =>
      rw [AggQueryIn.evaluate_Win_eq, AggQueryIn.evaluate_Win_eq, hread, hpk]
      refine Multiset.rel_map.mpr (hsim.mono (fun x' _ x hx hs => ?_))
      have hmem : GenRow.readAnnotated κw x
          ∈ Multiset.map (GenRow.readAnnotated κw) (q.evaluate d γ E) :=
        Multiset.mem_map_of_mem _ hx
      have hrd := GenRow.Sim.readAnnotated_eq h κw hs.1
      obtain ⟨H, hH0, -, hrow⟩ := hs.2
      refine ⟨⟨fun k => ?_, hs.1.2⟩, fun _ => False, fun _ _ h' => h', HoleOK.empty U Lh, ?_⟩
      · simp only [ValueFrame.windowGenRow]
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · rw [Fin.snoc_last, Fin.snoc_last, hrd]
          exact tokenOfDist_mapAnn_equiv h P O o w t γ f dist _ hmem
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hs.1.1 k'
      · simp only [ValueFrame.windowGenRow]
        rw [hrd]
        exact RowJoint.snoc_fresh hJ.eqf lab hUl hnd.1 (RowJoint.of_emptyHole (hH0 rfl) hrow)
          (by simp only [AggTok.fam_setFam]; rfl)
          (by simp [AggTok.lab, AggTok.fam_setFam, FamId.lab])
          (ListingRel.exists_of_tokEquiv h (tokenOfDist_mapAnn_equiv h P O o w t γ f dist _ hmem)
            _ _) _ _
  | @GammaTok cI mI nI₁ nI₂ κ' lab rd is his ts fs a q keep ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    have hpk := EvalEnv.paramKey_eq_of_joint hE hJ rd
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
        exact map_eq_of_rel (ih d γ E' E U Lh hE
          (hJ.sub (fun x hx => List.mem_cons_of_mem _ hx) (fun x hx => hx))
          hl1 hw hn (List.nodup_cons.mp hlab).2 hmu hrec)
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
    refine ⟨⟨?_, ?_⟩, fun _ => False, fun _ _ h' => h', HoleOK.empty U Lh, ?_⟩
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
      refine RowJoint.group_cols hJ.pres hJ.eqf lab
        (fun p hp h' => (hJ.lab p hp).1 (by rw [h']; exact List.mem_cons_self))
        List.mem_cons_self fs ts keep false γ _ _ (havingGroup_tiePerm h is X kv.fst)
        (List.ofFn kv.fst) (E.paramKey rd γ) (fun p ⟨k, h1, h2⟩ => ?_)
      dsimp only at h1 h2
      refine Fin.addCases (fun i h1 h2 => ?_) (fun j h1 h2 => ?_) k h1 h2
      · rw [Fin.append_left] at h1 h2
        refine Fin.addCases (fun i' h1 h2 => ?_) (fun j' h1 h2 => ?_) i h1 h2
        · rw [Fin.append_left] at h2; exact absurd h2 (by simp)
        · rw [Fin.append_right] at h1 h2
          refine ⟨j', Prod.ext ?_ ?_⟩
          · rw [← Sum.inr_injective h1]; cases keep j' <;> rfl
          · rw [← Sum.inr_injective h2]; cases keep j' <;> rfl
      · rw [Fin.append_right] at h2; exact absurd h2 (by simp)
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    have hnd := List.nodup_append.mp hlab
    simp only [AggQueryIn.evaluate]
    rw [show (q₁.evaluate
          (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q₁.evaluate d γ E).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih₁ d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_append_left _ hx)
          (fun x hx => hx)) hl1 hw.1 hn.1 hnd.1 hmu.1 hrec.1)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)]
    rw [show (q₂.evaluate
          (h.mapAnnotatedDatabase d) γ E').map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q₂.evaluate d γ E).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih₂ d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_append_right _ hx)
          (fun x hx => hx)) hl1 hw.2 hn.2 hnd.2.1 hmu.2 hrec.2)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)]
    set X₁ : AnnotatedRelation T K _ := (q₁.evaluate d γ E).map GenRow.toAnnotated
    set X₂ : AnnotatedRelation T K _ := (q₂.evaluate d γ E).map GenRow.toAnnotated
    clear_value X₁ X₂
    rw [show SemiringWithMonusHom.mapAnnotatedRelation h X₁
        = X₁.map (SemiringWithMonusHom.mapAnnotatedTuple h) from rfl]
    simp only [Multiset.map_map]
    refine rel_map_of_forall (fun p _ => ?_)
    obtain ⟨u, α⟩ := p
    refine GenRow.SimJ.of_noHole ⟨fun k => rfl, ?_⟩
      (RowJoint.of_noPairs hJ.pres _ (fun q ⟨k, _, h2⟩ => Sum.inl_ne_inr h2))
    dsimp only [Function.comp, GenRow.ofAnnotated,
      SemiringWithMonusHom.mapAnnotatedTuple]
    rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero,
      SemiringWithMonusHom.map_sub]
    congr 1
    rw [groupByKey_find_eq_filter_sum, groupByKey_find_eq_filter_sum]
    exact SemiringWithMonusHom.sum_filter_map_snd_mapAnnotatedRelation h u X₂
  | @GammaScalar cI mI nI₂ lab rd ts fs q ord ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    have hpk := EvalEnv.paramKey_eq_of_joint hE hJ rd
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
        exact map_eq_of_rel (ih d γ E' E U Lh hE
          (hJ.sub (fun x hx => List.mem_cons_of_mem _ hx) (fun x hx => hx))
          hl1 hw hn (List.nodup_cons.mp hlab).2 hmu hrec)
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs.1)
      exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))]
    set X : AnnotatedRelation T K mI := (q.evaluate d γ E).map GenRow.toAnnotated
    clear_value X
    -- one row on each side, annotated `𝟙`, with nothing pending
    refine Multiset.Rel.cons ?_ Multiset.Rel.zero
    refine ⟨⟨fun k => ?_, by simp [GenAnn.finalize]⟩, fun _ => False, fun _ _ h' => h',
      HoleOK.empty U Lh, ?_⟩
    exact ⟨rfl, rfl, TiePerm.symm (fun e => e.symm)
      (ofGroupOrd_mapAnn_tiePerm h (fs k) (ts k) (fun i : Fin 0 => i.elim0)
        ord X (fun i : Fin 0 => i.elim0))⟩
    · rw [hpk]
      refine RowJoint.group_cols hJ.pres hJ.eqf lab
        (fun p hp h' => (hJ.lab p hp).1 (by rw [h']; exact List.mem_cons_self))
        List.mem_cons_self fs ts (fun _ => none) true γ _ _
        (havingGroupOrd_tiePerm h (fun i : Fin 0 => i.elim0) ord X (fun i : Fin 0 => i.elim0))
        [] (E.paramKey rd γ) (fun p ⟨k, h1, h2⟩ => ⟨k, Prod.ext ?_ ?_⟩)
      · exact (Sum.inr_injective h1).symm
      · exact (Sum.inr_injective h2).symm
  | @GammaNest cI mI nI₁ κ' lab rd is his p f q ih =>
    -- one output row per key, and the keys are the columns' deterministic
    -- values, which a simulation keeps. For one key the two groups are
    -- related row for row, so their occurrences carry pushed annotations
    -- and columns whose statistics agree – which is all a nested value
    -- reads of them (`GenValue.Equiv.of_nest_rel`), the weight splitting
    -- per occurrence because `K'` is complemented
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    have hpk := EvalEnv.paramKey_eq_of_joint hE hJ rd
    simp only [AggQueryIn.evaluate]
    have hrel := (ih d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_cons_of_mem _ hx)
      (fun x hx => hx)) hl1 hw hn.2 (List.nodup_cons.mp hlab).2 hmu hrec).mono
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
    refine ⟨⟨fun k => ?_, ?_⟩, fun _ => False, fun _ _ h' => h', HoleOK.empty U Lh, ?_⟩
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
      refine RowJoint.fresh_row hJ.pres hJ.eqf lab
        (fun p hp h' => (hJ.lab p hp).1 (by rw [h']; exact List.mem_cons_self))
        List.mem_cons_self (fun q hq => ?_) (fun q q' hq hq' => ?_)
        (Or.inr ⟨_, _, nestRel_of_rel h hocc, fun q hq => ?_⟩)
      · dsimp only at hq
        rw [rowPairs_append_one (fun _ _ => Sum.inl_ne_inr) hq]
        exact ⟨rfl, rfl⟩
      · dsimp only at hq hq'
        rw [rowPairs_append_one (fun _ _ => Sum.inl_ne_inr) hq,
          rowPairs_append_one (fun _ _ => Sum.inl_ne_inr) hq']
        exact ⟨rfl, rfl⟩
      · dsimp only at hq
        rw [rowPairs_append_one (fun _ _ => Sum.inl_ne_inr) hq]
        exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | @Gamma cI mI nI₁ nI₂ lab rd is ts fs q keep ord ih =>
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    have hpk := EvalEnv.paramKey_eq_of_joint hE hJ rd
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
        exact map_eq_of_rel (ih d γ E' E U Lh hE
          (hJ.sub (fun x hx => List.mem_cons_of_mem _ hx) (fun x hx => hx))
          hl1 hw hn (List.nodup_cons.mp hlab).2 hmu hrec)
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
    refine ⟨⟨?_, ?_⟩, fun _ => False, fun _ _ h' => h', HoleOK.empty U Lh, ?_⟩
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
      refine RowJoint.group_cols hJ.pres hJ.eqf lab
        (fun p hp h' => (hJ.lab p hp).1 (by rw [h']; exact List.mem_cons_self))
        List.mem_cons_self fs ts keep false γ _ _ (havingGroupOrd_tiePerm h is ord X kv.fst)
        (List.ofFn kv.fst) (E.paramKey rd γ) (fun p ⟨k, h1, h2⟩ => ?_)
      dsimp only at h1 h2
      refine Fin.addCases (fun i h1 h2 => ?_) (fun j h1 h2 => ?_) k h1 h2
      · rw [Fin.append_left] at h2; exact absurd h2 (by simp)
      · rw [Fin.append_right] at h1 h2
        refine ⟨j, Prod.ext ?_ ?_⟩
        · rw [← Sum.inr_injective h1]; cases keep j <;> rfl
        · rw [← Sum.inr_injective h2]; cases keep j <;> rfl
  | @WinExpr cI nI mI pI qI lab rd P O o ws ts fs g q keeps ih =>
    -- one output row per occurrence of the shared family. The two sides
    -- index that family by their own sorted order, so they are compared
    -- through a bijection of indices rather than index by index; the
    -- frames read the tuple (`hw.1`), which is what makes each pair of
    -- corresponding expression columns equivalent.
    intro d γ E' E U Lh hE hJ hl1 hw hn hlab hmu hrec
    have hpk := EvalEnv.paramKey_eq_of_joint hE hJ rd
    have hnd := List.nodup_cons.mp hlab
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
        exact map_eq_of_rel (ih d γ E' E U Lh hE (hJ.sub (fun x hx => List.mem_cons_of_mem _ hx)
          (fun x hx => hx)) hl1 hw.2 hn hnd.2 hmu hrec)
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
    refine rel_occFam_of_equiv _ _ e (fun i => ⟨⟨fun k => ?_, ?_⟩, fun _ => False,
      fun _ _ h' => h', HoleOK.empty U Lh, ?_⟩)
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
    · refine RowJoint.fresh_row hJ.pres hJ.eqf lab
        (fun p hp h' => (hJ.lab p hp).1 (by rw [h']; exact List.mem_cons_self))
        List.mem_cons_self (fun p hp => ?_) (fun p p' hp hp' => ?_)
        (Or.inl ?_)
      · dsimp only at hp
        rw [rowPairs_snoc_one (fun _ _ => Sum.inl_ne_inr) hp]
        refine ⟨?_, by simp [AggTok.lab, AggTok.fam_setFam, FamId.lab]⟩
        simp only [AggTok.fam_setFam, hpk, congrArg Prod.fst (he i)]
        rfl
      · dsimp only at hp hp'
        rw [rowPairs_snoc_one (fun _ _ => Sum.inl_ne_inr) hp,
          rowPairs_snoc_one (fun _ _ => Sum.inl_ne_inr) hp']
        exact ⟨rfl, rfl⟩
      · obtain ⟨D, hD⟩ := ListingRel.exists_exprOfWhen h P O o hw.1 ts fs g keeps γ
          (congrArg Prod.fst (he i)) hmul'
          (FamId.mk lab (List.ofFn (OccFam.ofSorted X |>.row i).fst)
            (E.paramKey rd γ) 0 [])
          (FamId.mk lab (List.ofFn ((OccFam.ofSorted (Multiset.map gh X)).row (e i)).fst)
            (E'.paramKey rd γ) 0 [])
        refine ⟨D, fun q hq => ?_⟩
        dsimp only at hq
        rw [rowPairs_snoc_one (fun _ _ => Sum.inl_ne_inr) hq]
        exact hD

omit [DecidableEq K] [HasAltLinearOrder K] [HasAltLinearOrder K'] in
/-- **Nothing is bound**: the empty universe is a joint environment. -/
theorem JointEnv.empty (h : SemiringWithMonusHom K K') (L : List ℕ) {c : ℕ} (γ : Fin c → T) :
    JointEnv h (fun _ => False) [] L γ ({} : EvalEnv T K') ({} : EvalEnv T K) [] := by
  refine ⟨⟨fun p _ hp => hp.elim, fun p hp => hp.elim⟩, fun p hp => ?_, fun p hp => hp.elim,
    fun p hp => hp.elim, fun k x' x _ h2 => ?_, fun _ h' => absurd h' (by simp),
    fun _ _ h' => absurd h' (by simp)⟩
  · induction hp with
    | base h' => exact h'
    | step _ _ ih => exact ih
    | stepF _ _ ih => exact ih
  · rw [EvalEnv.empty_ctxAt] at h2
    exact absurd h2 (by simp)

/-- The row-wise simulation for a query read with nothing bound. -/
theorem AggQueryIn.evaluate_hom_rel (h : SemiringWithMonusHom K K') {c n : ℕ}
    {κ : Fin n → ColKind} (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (hw : q.framesContainSelf) (hn : q.nestInComplemented (K := K'))
    (hlab : q.labelsDistinct) (hmu : q.muBodyTokFree) (hrec : q.AnnSettlesAt d γ {}) :
    Multiset.Rel (GenRow.Sim h) (q.evaluate (h.mapAnnotatedDatabase d) γ) (q.evaluate d γ) :=
  (AggQueryIn.evaluate_hom_rel_env h q d γ {} {} (fun _ => False) [] (EvalEnv.homSim_empty h γ)
    (JointEnv.empty h _ γ) (by simp) hw hn hlab hmu hrec).mono (fun _ _ _ _ hs => hs.1)

/-- **Evaluator-level hom commutation**: the final annotated relation
computed by the general evaluator commutes with every
`SemiringWithMonusHom`, over every m-semiring. Nothing is asked of the
hom: the extra supersedes a non-injective one can trigger are
value-neutral by guard absorption (`delta_absorb`), and the annotation
tie-breaks of the group sort are value-neutral by the tie-block
congruence layer.

What is asked of the *query*:

* that a multi-frame window frame by the tuple
  (`AggQueryIn.framesContainSelf`): such a window lists its shared family
  by occurrence index, and a change of annotation semiring re-sorts that
  index inside blocks of equal rows. Every window function the library
  derives satisfies it, and `AggQueryIn.framesContainSelf_of_noWinExpr`
  discharges it for a query with no multi-frame window;
* that the *target* semiring be complemented wherever the query
  aggregates a grouping a second time (`AggQueryIn.nestInComplemented`),
  which is how the per-column equivalence of nested values is proved;
  `AggQueryIn.nestInComplemented_of_noGammaNest` discharges it for a query
  with no second-level aggregation;
* that no two operators building aggregate values share a label
  (`AggQueryIn.labelsDistinct`), and that a bag recursion's body build
  none (`AggQueryIn.muBodyTokFree`). A selection reads the values of one
  family in one world of that family, and the two sides list the family's
  occurrences each in its own order; what makes the reading commute is
  that every value of a family is built from *one* listing on each side,
  the two tie-block permuted (`FamPres`, `jointWorlds_of_famPres`). The
  labels keep families of different operators apart; a body building
  values would meet, in one row of a round, values of its earlier rounds
  in the same family.

These are hypotheses of *this proof* and not of the mathematics: every
output annotation is an expression in the input annotations over `⊕`,
`⊗`, `⊖`, `δ`, `𝟘`, `𝟙`, and a hom commutes with such an expression in
every m-semiring. -/
theorem AggQueryIn.evaluateAnnotated_hom (h : SemiringWithMonusHom K K')
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ)
    (hw : q.framesContainSelf) (hn : q.nestInComplemented (K := K'))
    (hlab : q.labelsDistinct) (hmu : q.muBodyTokFree)
    (d : AnnotatedDatabase T K) (hrec : q.AnnSettlesAt d (fun _ => 0) {}) :
    q.evaluateAnnotated (h.mapAnnotatedDatabase d)
      = SemiringWithMonusHom.mapAnnotatedRelation h
          (q.evaluateAnnotated d) := by
  unfold AggQueryIn.evaluateAnnotated SemiringWithMonusHom.mapAnnotatedRelation
  rw [Multiset.map_map]
  exact map_eq_of_rel (AggQueryIn.evaluate_hom_rel h q d _ hw hn hlab hmu hrec)
    (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)

end EvaluatorHom
