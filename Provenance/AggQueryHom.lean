/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Tactic.Ring
import Provenance.AggQuery
import Provenance.AggValueCongr
import Provenance.QueryAnnotatedDatabaseHom
import Provenance.AggQueryBridges

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

/-! ## Guard absorption

The first substantive use of the `delta_absorb` axiom: an
existence-entailing predicate provenance algebraically absorbs its
group's `δ`-guard. Every monomial of the possible-world sum contains
some occurrence annotation of the group (the worlds are non-empty), and
`delta_absorb` lets that occurrence swallow `δ` of the whole group
sum. -/

omit [DecidableEq K'] [CommSemiringWithMonus K'] in
/-- A token's predicate provenance absorbs the `δ`-guard of its own
group, for an arbitrary test on its value. -/
theorem AggValue.predProvWith_delta_absorb (a : AggValue T K)
    (P : T → Kleene) :
    a.predProvWith P
        * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)
      = a.predProvWith P := by
  unfold AggValue.predProvWith
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun W hW => ?_
  obtain ⟨-, hne⟩ := Finset.mem_filter.mp hW
  obtain ⟨i₀, hi₀⟩ := hne
  have hmem : a.anns i₀ ∈ (↑(a.occs.map Prod.snd) : Multiset K) :=
    Multiset.mem_coe.mpr
      (List.mem_map.mpr ⟨a.occs.get i₀, List.get_mem _ _, rfl⟩)
  have hr : (a.occs.map Prod.snd).sum
      = a.anns i₀ + ((↑(a.occs.map Prod.snd) : Multiset K).erase
          (a.anns i₀)).sum := by
    rw [← Multiset.sum_coe, ← Multiset.sum_cons, Multiset.cons_erase hmem]
  have key : a.anns i₀
      * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)
      = a.anns i₀ := by
    rw [hr]
    exact SemiringWithMonus.delta_absorb _ _
  have hw : Having.worldAnn a.anns W
      = a.anns i₀ * ((∏ i ∈ W.erase i₀, a.anns i)
          * (1 - ∑ i ∈ Wᶜ, a.anns i)) := by
    unfold Having.worldAnn
    rw [← Finset.mul_prod_erase W a.anns hi₀, mul_assoc]
  rw [hw]
  calc a.anns i₀ * ((∏ i ∈ W.erase i₀, a.anns i)
          * (1 - ∑ i ∈ Wᶜ, a.anns i)) * Having.chiOf P (a.valOn W)
        * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)
      = ((∏ i ∈ W.erase i₀, a.anns i) * (1 - ∑ i ∈ Wᶜ, a.anns i)
          * Having.chiOf P (a.valOn W))
        * (a.anns i₀
          * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)) := by
        rw [mul_rotate (a.anns i₀), mul_assoc]
    _ = ((∏ i ∈ W.erase i₀, a.anns i) * (1 - ∑ i ∈ Wᶜ, a.anns i)
          * Having.chiOf P (a.valOn W)) * a.anns i₀ := by
        rw [key]
    _ = a.anns i₀ * ((∏ i ∈ W.erase i₀, a.anns i)
          * (1 - ∑ i ∈ Wᶜ, a.anns i)) * Having.chiOf P (a.valOn W) :=
        (mul_rotate _ _ _).symm

omit [DecidableEq K'] [CommSemiringWithMonus K'] in
/-- The comparison case. -/
theorem AggValue.predProv_delta_absorb (a : AggValue T K) (op : CompOp)
    (c : T) :
    a.predProv op c
        * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)
      = a.predProv op c :=
  AggValue.predProvWith_delta_absorb a (fun v => op.eval3 v c)

omit [DecidableEq K'] [CommSemiringWithMonus K'] in
/-- **Guard absorption for entailing predicates**: when a predicate
entails existence and all its compared tokens carry the annotation list
`ℓ₀`, its predicate provenance absorbs `δ(⊕ℓ₀)`. -/
theorem GenPredIn.predsem_delta_absorb {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} (neg : Bool) (u : Tuple (GenValue T K) n)
    (ℓ₀ : List K)
    (huni : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀)
    (hent : φ.entailsExistence neg = true) :
    φ.predsem neg u γ * SemiringWithMonus.delta ℓ₀.sum
      = φ.predsem neg u γ := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ => exact absurd hent (by simp [GenPredIn.entailsExistence])
  | aggCmp k h op t =>
    cases hu : u k with
    | inl w => simp only [GenPredIn.predsem, hu, zero_mul]
    | inr x =>
      obtain ⟨hsc, heq⟩ := huni k (Finset.mem_singleton_self k) x hu
      cases x with
      | tok a =>
        simp only [AggTok.scalar_tok] at hsc
        simp only [AggTok.annList_tok] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOf_tok]
        rw [AggValue.predProvOf_of_grouped hsc, ← heq]
        exact AggValue.predProv_delta_absorb a _ _
      | nest b =>
        simp only [AggTok.scalar_nest] at hsc
        simp only [AggTok.annList_nest] at heq
        simp only [GenPredIn.predsem, AggTok.predProvOf, hu,
          AggTok.predProvOfWith]
        rw [← heq, List.sum_singleton]
        exact NestedValue.predProvWith_delta_absorb b hsc _
      | expr e =>
        simp only [AggTok.scalar_expr] at hsc
        simp only [AggTok.annList_expr] at heq
        simp only [GenPredIn.predsem, AggTok.predProvOf, hu,
          AggTok.predProvOfWith_expr]
        rw [← heq]
        exact AggExpr.predProvWith_delta_absorb e
          (AggExpr.exists_grouped_of_not_isScalar hsc) _
  | aggRange k h op₁ t₁ op₂ t₂ =>
    cases hu : u k with
    | inl w => simp only [GenPredIn.predsem, hu, zero_mul]
    | inr x =>
      obtain ⟨hsc, heq⟩ := huni k (Finset.mem_singleton_self k) x hu
      cases x with
      | tok a =>
        simp only [AggTok.scalar_tok] at hsc
        simp only [AggTok.annList_tok] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOfWith_tok]
        rw [AggValue.predProvOfWith, hsc, ite_eq_right Bool.false_ne_true,
          ← heq]
        exact AggValue.predProvWith_delta_absorb a _
      | nest b =>
        simp only [AggTok.scalar_nest] at hsc
        simp only [AggTok.annList_nest] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOfWith]
        rw [← heq, List.sum_singleton]
        exact NestedValue.predProvWith_delta_absorb b hsc _
      | expr e =>
        simp only [AggTok.scalar_expr] at hsc
        simp only [AggTok.annList_expr] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOfWith_expr]
        rw [← heq]
        exact AggExpr.predProvWith_delta_absorb e
          (AggExpr.exists_grouped_of_not_isScalar hsc) _
  | and φ ψ ihφ ihψ =>
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggTok T K,
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPredIn.and φ ψ).predsem false u γ
          = φ.predsem false u γ * ψ.predsem false u γ := rfl
      have hent' : (φ.entailsExistence false || ψ.entailsExistence false)
          = true := hent
      rw [Bool.or_eq_true] at hent'
      rw [he]
      rcases hent' with h | h
      · calc φ.predsem false u γ * ψ.predsem false u γ
              * SemiringWithMonus.delta ℓ₀.sum
            = ψ.predsem false u γ * (φ.predsem false u γ
              * SemiringWithMonus.delta ℓ₀.sum) := by
              rw [mul_comm (φ.predsem false u γ) (ψ.predsem false u γ), mul_assoc]
          _ = ψ.predsem false u γ * φ.predsem false u γ := by
              rw [ihφ false huφ h]
          _ = φ.predsem false u γ * ψ.predsem false u γ := mul_comm _ _
      · calc φ.predsem false u γ * ψ.predsem false u γ
              * SemiringWithMonus.delta ℓ₀.sum
            = φ.predsem false u γ * (ψ.predsem false u γ
              * SemiringWithMonus.delta ℓ₀.sum) := mul_assoc _ _ _
          _ = φ.predsem false u γ * ψ.predsem false u γ := by
              rw [ihψ false huψ h]
    | true =>
      have he : (GenPredIn.and φ ψ).predsem true u γ
          = φ.predsem true u γ + ψ.predsem true u γ := rfl
      have hent' : (φ.entailsExistence true && ψ.entailsExistence true)
          = true := hent
      rw [Bool.and_eq_true] at hent'
      rw [he, add_mul, ihφ true huφ hent'.1, ihψ true huψ hent'.2]
  | or φ ψ ihφ ihψ =>
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggTok T K,
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPredIn.or φ ψ).predsem false u γ
          = φ.predsem false u γ + ψ.predsem false u γ := rfl
      have hent' : (φ.entailsExistence false && ψ.entailsExistence false)
          = true := hent
      rw [Bool.and_eq_true] at hent'
      rw [he, add_mul, ihφ false huφ hent'.1, ihψ false huψ hent'.2]
    | true =>
      have he : (GenPredIn.or φ ψ).predsem true u γ
          = φ.predsem true u γ * ψ.predsem true u γ := rfl
      have hent' : (φ.entailsExistence true || ψ.entailsExistence true)
          = true := hent
      rw [Bool.or_eq_true] at hent'
      rw [he]
      rcases hent' with h | h
      · calc φ.predsem true u γ * ψ.predsem true u γ
              * SemiringWithMonus.delta ℓ₀.sum
            = ψ.predsem true u γ * (φ.predsem true u γ
              * SemiringWithMonus.delta ℓ₀.sum) := by
              rw [mul_comm (φ.predsem true u γ) (ψ.predsem true u γ), mul_assoc]
          _ = ψ.predsem true u γ * φ.predsem true u γ := by
              rw [ihφ true huφ h]
          _ = φ.predsem true u γ * ψ.predsem true u γ := mul_comm _ _
      · calc φ.predsem true u γ * ψ.predsem true u γ
              * SemiringWithMonus.delta ℓ₀.sum
            = φ.predsem true u γ * (ψ.predsem true u γ
              * SemiringWithMonus.delta ℓ₀.sum) := mul_assoc _ _ _
          _ = φ.predsem true u γ * ψ.predsem true u γ := by
              rw [ihψ true huψ h]
  | not φ ih =>
    have he : (GenPredIn.not φ).predsem neg u γ = φ.predsem (!neg) u γ := rfl
    rw [he]
    exact ih (!neg) huni hent

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
/-- The same for a token under a `FILTER` clause: the clause reads the
tuple part, which a tie-block permutation does not move, so it keeps
corresponding occurrences on the two sides (`TiePerm.filter`). -/
theorem ofGroupWhen_mapAnn_tiePerm (h : SemiringWithMonusHom K K')
    (f : SeqAggFunc T) {c : ℕ} (t : TermIn T c m) {γ : Fin c → T}
    (keep : Tuple T m → Bool) (is : Tuple (Fin m) n₁)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    TiePerm (fun p q : T × K' => p.1 = q.1)
      ((AggValue.ofGroupWhen f t keep (Having.havingGroup is r g) γ).mapAnn
        ⇑h.toRingHom).occs
      (AggValue.ofGroupWhen f t keep
        (Having.havingGroup is
          (r.map (fun p =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))) g) γ).occs := by
  have hocc₁ : ((AggValue.ofGroupWhen f t keep
        (Having.havingGroup is r g) γ).mapAnn ⇑h.toRingHom).occs
      = (((Having.havingGroup is r g).map
            (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' m))).filter
          (fun p => keep p.fst)).map (fun p => (t.eval p.fst γ, p.snd)) := by
    simp only [AggValue.ofGroupWhen, AggValue.ofScalarGroup, AggValue.ofGroup,
      AggValue.mapAnn, List.map_map, List.filter_map]
    rfl
  rw [hocc₁]
  exact ((havingGroup_tiePerm h is r g).filter
      (fun hpq => congrArg keep hpq)).map
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

omit [DecidableEq K] in
/-- The same for a token under a `FILTER` clause: the clause reads the
tuple part, which a tie-block permutation does not move, so it keeps
corresponding occurrences on the two sides. -/
theorem tokenOfWhen_mapAnn_tiePerm (h : SemiringWithMonusHom K K')
    {n' m' p' : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') (w : ValueFrame T p') {c : ℕ} (t : TermIn T c n')
    {γ : Fin c → T} (f : SeqAggFunc T) (keep : Tuple T n' → Bool)
    (X : Multiset (AnnotatedTuple T K n')) {x : AnnotatedTuple T K n'}
    (hx : x ∈ X) :
    TiePerm (fun a b : T × K' => a.1 = b.1)
      ((ValueFrame.tokenOfWhen P O o w t f keep X x γ).mapAnn
        ⇑h.toRingHom).occs
      (ValueFrame.tokenOfWhen P O o w t f keep
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
  have hocc1 : ((ValueFrame.tokenOfWhen P O o w t f keep X x γ).mapAnn
        ⇑h.toRingHom).occs
      = ((OrderSpec.sortSeq (Tuple.key O) Prod.fst o
          ((sortList (ValueFrame.frameOf (α := AnnotatedTuple T K n')
              Prod.fst P O w X x)).map
            (fun q : AnnotatedTuple T K n' =>
              ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')))).filter
          (fun q : AnnotatedTuple T K' n' => keep q.fst)).map
          (fun q : AnnotatedTuple T K' n' => (t.eval q.fst γ, q.snd)) := by
    show (((ValueFrame.frameListOf (α := AnnotatedTuple T K n') Prod.fst
        P O o w X x).filter (fun q => keep q.fst)).map
        (fun q => (t.eval q.fst γ, q.snd))).map
        (fun z => (z.fst, h.toRingHom z.snd)) = _
    rw [List.map_map, ValueFrame.frameListOf,
      ← ValueFrame.sortSeq_mapAnn O o ⇑h.toRingHom, List.filter_map,
      List.map_map]
    rfl
  have hocc2 : (ValueFrame.tokenOfWhen P O o w t f keep
      (Multiset.map (fun q : AnnotatedTuple T K n' =>
        ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
      ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ).occs
      = ((OrderSpec.sortSeq (Tuple.key O) Prod.fst o
          (sortList (α := AnnotatedTuple T K' n')
            (Multiset.map (fun q : AnnotatedTuple T K n' =>
              ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n'))
              (ValueFrame.frameOf (α := AnnotatedTuple T K n')
                Prod.fst P O w X x)))).filter
          (fun q : AnnotatedTuple T K' n' => keep q.fst)).map
          (fun q : AnnotatedTuple T K' n' => (t.eval q.fst γ, q.snd)) := by
    rw [ValueFrame.tokenOfWhen]
    show ((ValueFrame.frameListOf (α := AnnotatedTuple T K' n') Prod.fst
        P O o w _ _).filter _).map _ = _
    rw [ValueFrame.frameListOf, hframe]
  rw [hocc1, hocc2]
  exact ((OrderSpec.sortSeq_tiePerm (key := Tuple.key O)
        (val := (Prod.fst : AnnotatedTuple T K' n' → Tuple T n')) (o := o)
        (sortList_hom_tiePerm h _).perm).filter
      (fun hpq => congrArg keep hpq)).map
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
        ∧ ∀ P : T → Kleene, e'.predProvWith P = e.predProvWith P
  | _, _ => False

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
    | expr e => exact h.2.2.2 P
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
theorem GenValue.Equiv.of_expr_tiePerm {q : ℕ}
    {occs₁ occs₂ : List ((Fin q → T) × K × (Fin q → Bool))}
    (aggs : Fin q → SeqAggFunc T) {sc₁ sc₂ : Fin q → Bool} (hsc : sc₁ = sc₂)
    (g : (Fin q → T) → T)
    (h : TiePerm (fun z z' => z.fst = z'.fst ∧ z.snd.snd = z'.snd.snd)
      occs₁ occs₂) :
    GenValue.Equiv
      (Sum.inr (AggTok.expr (AggExpr.mk q occs₁ aggs sc₁ g)) : GenValue T K)
      (Sum.inr (AggTok.expr (AggExpr.mk q occs₂ aggs sc₂ g))) := by
  subst hsc
  exact AggExpr.readings_congr aggs sc₁ g h

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
      refine ⟨congrArg gf h.1, h.2.1, ?_, fun P => ?_⟩
      · rw [AggExpr.vals_postcomp, AggExpr.vals_postcomp, h.2.2.1]
      · rw [AggExpr.predProvWith_postcomp, AggExpr.predProvWith_postcomp,
          h.2.2.2]
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

/-- An existence-entailing predicate provenance absorbs the `δ`-guards of
any collection of pending factors, each of which is the occurrence list of
*every* compared token. -/
theorem GenPredIn.predsem_absorb_prod (φ : GenPredIn T c κ) {γ : Fin c → T}
    (u : Tuple (GenValue T K) n) (hent : φ.entailsExistence false = true)
    (D : Multiset (List K))
    (hD : ∀ l ∈ D, ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.scalar = false ∧ a.annList = l) :
    φ.predsem false u γ
        * (D.map (fun l => SemiringWithMonus.delta l.sum)).prod
      = φ.predsem false u γ := by
  induction D using Multiset.induction_on with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, mul_one]
  | cons l D ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ← mul_assoc,
      GenPredIn.predsem_delta_absorb φ false u l
        (fun k hk a hka => hD l (Multiset.mem_cons_self l D) k hk a hka) hent]
    exact ih (fun l' hl' => hD l' (Multiset.mem_cons_of_mem hl'))

/-- **Selection finalize identity.** On each side separately, the
annotation produced by an aggregate-atom selection finalizes to the
predicate provenance times the input's finalized annotation: kept pending
factors commute out, and each superseded factor is absorbed by the
predicate provenance, its drop condition being exactly the absorption
license. The compared-lists multiset `C` is abstract; the only fact used
is that every compared token's occurrence list belongs to it. -/
theorem GenAnn.finalize_sel (φ : GenPredIn T c κ) {γ : Fin c → T}
    (u : Tuple (GenValue T K) n) (b : K) (P : Multiset (List K))
    (C Cs : Multiset (List K))
    (hC : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.annList ∈ C)
    (hCs : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.scalar = true → a.annList ∈ Cs) :
    GenAnn.finalize ⟨b * φ.predsem false u γ,
      if φ.entailsExistence false then
        P.filter (fun l => ¬(Cs = 0 ∧ C ≠ 0 ∧ ∀ l' ∈ C, l' = l))
      else P⟩
      = φ.predsem false u γ * GenAnn.finalize ⟨b, P⟩ := by
  by_cases hent : φ.entailsExistence false = true
  · rw [ite_eq_left hent]
    show b * φ.predsem false u γ * _ = φ.predsem false u γ * (b * _)
    set dropCond := fun l : List K => (Cs = 0 ∧ C ≠ 0 ∧ ∀ l' ∈ C, l' = l)
      with hdrop
    have habs : φ.predsem false u γ
        * ((P.filter dropCond).map
            (fun l => SemiringWithMonus.delta l.sum)).prod
        = φ.predsem false u γ := by
      refine GenPredIn.predsem_absorb_prod φ u hent _
        (fun l hl k hk a hka => ?_)
      have hcond := (Multiset.mem_filter.mp hl).2
      refine ⟨?_, hcond.2.2 a.annList (hC k hk a hka)⟩
      by_contra hsc
      rw [Bool.not_eq_false] at hsc
      have := hCs k hk a hka hsc
      rw [hcond.1] at this
      exact absurd this (Multiset.notMem_zero _)
    calc b * φ.predsem false u γ
          * ((P.filter (fun l => ¬ dropCond l)).map
              (fun l => SemiringWithMonus.delta l.sum)).prod
        = b * (φ.predsem false u γ
            * (((P.filter (fun l => ¬ dropCond l)).map
                (fun l => SemiringWithMonus.delta l.sum)).prod
              * ((P.filter dropCond).map
                (fun l => SemiringWithMonus.delta l.sum)).prod)) := by
          rw [mul_comm (((P.filter (fun l => ¬ dropCond l)).map
              (fun l => SemiringWithMonus.delta l.sum)).prod),
            ← mul_assoc (φ.predsem false u γ), habs, mul_assoc]
      _ = b * (φ.predsem false u γ
            * ((P.filter (fun l => ¬ dropCond l) + P.filter dropCond).map
                (fun l => SemiringWithMonus.delta l.sum)).prod) := by
          rw [Multiset.map_add, Multiset.prod_add]
      _ = φ.predsem false u γ
            * (b * (P.map (fun l => SemiringWithMonus.delta l.sum)).prod) := by
          have hsplit : P.filter (fun l => ¬ dropCond l) + P.filter dropCond
              = P := by
            rw [add_comm]
            exact Multiset.filter_add_not _ P
          rw [hsplit, mul_left_comm]
  · rw [ite_eq_right hent]
    show b * φ.predsem false u γ * _ = φ.predsem false u γ * (b * _)
    rw [mul_right_comm]
    exact mul_comm _ _

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
    rw [AggValue.mergeByValue_congr hagg hsc htie,
      AggValue.mergeByValue_map (map_zero h.toRingHom)
        (fun x y => map_add h.toRingHom x y)]
    exact ⟨rfl, rfl, TiePerm.refl _ _⟩


omit [DecidableEq K] in
/-- **A filtered window token is carried by the pushforward too**: the
clause keeps corresponding occurrences, and the merge is blind to the
tie-block permutation the two unmerged tokens differ by. -/
theorem tokenOfDistWhen_mapAnn_equiv (h : SemiringWithMonusHom K K')
    {n' m' p' : ℕ} (P : Tuple (Fin n') m') (O : Tuple (Fin n') p')
    (o : OrderSpec p') (w : ValueFrame T p') {c : ℕ} (t : TermIn T c n')
    (γ : Fin c → T) (f : SeqAggFunc T) (dist : Bool)
    (keep : Tuple T n' → Bool) (X : Multiset (AnnotatedTuple T K n'))
    {x : AnnotatedTuple T K n'} (hx : x ∈ X) :
    GenValue.Equiv
      (Sum.inr (AggTok.tok (ValueFrame.tokenOfDistWhen P O o w t f dist keep
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
        ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ)))
      (Sum.inr (AggTok.tok
        ((ValueFrame.tokenOfDistWhen P O o w t f dist keep X x γ).mapAnn
          ⇑h.toRingHom))) := by
  have hagg : (ValueFrame.tokenOfWhen P O o w t f keep
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
        ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ).agg
      = ((ValueFrame.tokenOfWhen P O o w t f keep X x γ).mapAnn
        ⇑h.toRingHom).agg := rfl
  have hsc : (ValueFrame.tokenOfWhen P O o w t f keep
        (Multiset.map (fun q : AnnotatedTuple T K n' =>
          ((q.fst, h.toRingHom q.snd) : AnnotatedTuple T K' n')) X)
        ((x.fst, h.toRingHom x.snd) : AnnotatedTuple T K' n') γ).scalar
      = ((ValueFrame.tokenOfWhen P O o w t f keep X x γ).mapAnn
        ⇑h.toRingHom).scalar := rfl
  have htie := TiePerm.symm (fun e => e.symm)
    (tokenOfWhen_mapAnn_tiePerm h P O o w t f keep X hx (γ := γ))
  unfold ValueFrame.tokenOfDistWhen
  cases dist
  · exact ⟨hagg, hsc, htie⟩
  · simp only [ite_true]
    rw [AggValue.mergeByValue_congr hagg hsc htie,
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
          fun l => decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
            && (ws l).ρ (Tuple.key O y.fst)
              (Tuple.key O (r.row i).fst))) := by
    rw [ValueFrame.occs_exprOf P O o hcs ts fs g r' i' γ, hi]
  have hoccb : ((ValueFrame.exprOf P O o ws ts fs g r i γ).mapAnn
        ⇑h.toRingHom).occs
      = (Lb.map gh).map (fun y : AnnotatedTuple T K' n' =>
        ((fun l => (ts l).eval y.fst γ), y.snd,
          fun l => decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
            && (ws l).ρ (Tuple.key O y.fst)
              (Tuple.key O (r.row i).fst))) := by
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
          fun l => (decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
              && (ws l).ρ (Tuple.key O y.fst)
                (Tuple.key O (r.row i).fst))
            && (match keeps l with
                | none => true
                | some φ => φ.keeps y.fst))) := by
    rw [ValueFrame.occs_exprOfWhen P O o hcs ts fs g keeps r' i' γ, hi, hL']
    rfl
  have hoccb : ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).mapAnn
        ⇑h.toRingHom).occs
      = (Lb.map gh).map (fun y : AnnotatedTuple T K' n' =>
        ((fun l => (ts l).eval y.fst γ), y.snd,
          fun l => (decide (Tuple.key P y.fst = Tuple.key P (r.row i).fst)
              && (ws l).ρ (Tuple.key O y.fst)
                (Tuple.key O (r.row i).fst))
            && (match keeps l with
                | none => true
                | some φ => φ.keeps y.fst))) := by
    show ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).occs.map
        (fun z => (z.fst, h.toRingHom z.snd.fst, z.snd.snd))) = _
    rw [ValueFrame.occs_exprOfWhen P O o hcs ts fs g keeps r i γ, hLb]
    simp only [List.map_map]
    rfl
  rw [AggExpr.eq_mk_of_occs hocc', AggExpr.eq_mk_of_occs hoccb]
  refine GenValue.Equiv.of_expr_tiePerm (q := qq) fs ?_ g
    (htp.map _ (fun hab => ⟨by rw [hab], by rw [hab]⟩))
  funext l
  show ((keeps l).isSome || !(ws l).s (Tuple.key O (r'.row i').fst))
    = ((keeps l).isSome || !(ws l).s (Tuple.key O (r.row i).fst))
  rw [hi]

/-- **Row-wise simulation.** Evaluating the transported query on the
pushed-forward database produces, row for row, simulations of the
base-side rows: same regular values, equivalent aggregate columns, and
the pushed-forward finalized annotation. -/
theorem AggQueryIn.evaluate_hom_rel (h : SemiringWithMonusHom K K') :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (d : AnnotatedDatabase T K) (γ : Fin c → T),
      q.framesContainSelf → q.noGammaNest →
      Multiset.Rel (GenRow.Sim h)
        (q.evaluate (h.mapAnnotatedDatabase d) γ)
        (q.evaluate d γ) := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate,
      SemiringWithMonusHom.find_mapAnnotatedDatabase]
    cases hf : d.find n s with
    | none =>
      simp only [Option.map_none]
      exact Multiset.Rel.zero
    | some rn =>
      simp only [Option.map_some]
      exact rel_ofAnnotated_map h rn
  | Proj ps q ih =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    refine rel_map_of_rel (ih d γ hw hn) (fun r' r hs => ⟨?_, ?_⟩)
    · intro j
      cases hp : ps j with
      | term t =>
        simp only [hp, ProjColIn.eval]
        show t.eval r'.fst γ = t.eval r.fst γ
        calc t.eval r'.fst γ
            = t.eval (fun k => AggValue.mapAnnSum ⇑h.toRingHom (r.fst k)) γ :=
              TermGIn.eval_equiv t hs.1
          _ = t.eval r.fst γ := TermGIn.eval_mapAnnSum h t r.fst
      | provTerm t =>
        simp only [hp, ProjColIn.eval]
        show t.eval r'.fst γ = t.eval r.fst γ
        calc t.eval r'.fst γ
            = t.eval (fun k => AggValue.mapAnnSum ⇑h.toRingHom (r.fst k)) γ :=
              TermGIn.eval_equiv t hs.1
          _ = t.eval r.fst γ := TermGIn.eval_mapAnnSum h t r.fst
      | token k hk =>
        simp only [hp, ProjColIn.eval]
        exact hs.1 k
      | aggTerm k hk gf =>
        -- reading an aggregate column through a function leaves its
        -- family and its convention alone, so the simulation carries
        -- over (`GenValue.Equiv.postcomp`)
        simp only [hp, ProjColIn.eval]
        have hk' := hs.1 k
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
    · rw [GenAnn.finalize_cash _ _ _ Multiset.inter_le_left,
        GenAnn.finalize_cash _ _ _ Multiset.inter_le_left]
      exact hs.2
  | Sel φ q ih =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    by_cases hagg : φ.hasAggAtom
    · rw [ite_eq_left hagg, ite_eq_left hagg]
      refine rel_map_of_rel (ih d γ hw hn) (fun r' r hs => ⟨hs.1, ?_⟩)
      dsimp only
      rw [GenAnn.finalize_sel φ r'.fst r'.snd.base r'.snd.pending _ _
          (fun k hk a hka => (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [hka]⟩)
          (fun k hk a hka hsc => (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [hka, hsc]⟩),
        GenAnn.finalize_sel φ r.fst r.snd.base r.snd.pending _ _
          (fun k hk a hka => (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [hka]⟩)
          (fun k hk a hka hsc => (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [hka, hsc]⟩)]
      rw [GenPredIn.predsem_equiv φ false hs.1,
        GenPredIn.predsem_mapAnn h φ false r.fst, hs.2,
        ← map_mul]
    · rw [ite_eq_right hagg, ite_eq_right hagg]
      refine rel_filter_of_iff (ih d γ hw hn) (fun r' r hs => ?_)
      calc φ.holds r'.fst γ
          ↔ φ.holds (fun k => AggValue.mapAnnSum ⇑h.toRingHom (r.fst k)) γ :=
            GenPredIn.holds_equiv _ hs.1
        _ ↔ φ.holds r.fst γ := GenPredIn.holds_mapAnnSum h φ r.fst
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    refine rel_map_of_rel (rel_product (ih₁ d γ hw.1 hn.1) (ih₂ d γ hw.2 hn.2)) ?_
    rintro ⟨x', y'⟩ ⟨x, y⟩ ⟨hx, hy⟩
    refine ⟨?_, ?_⟩
    · intro k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · show GenValue.Equiv (Fin.append x'.fst y'.fst (Fin.castAdd _ j))
          (AggValue.mapAnnSum ⇑h.toRingHom
            (Fin.append x.fst y.fst (Fin.castAdd _ j)))
        rw [Fin.append_left, Fin.append_left]
        exact hx.1 j
      · show GenValue.Equiv (Fin.append x'.fst y'.fst (Fin.natAdd _ j))
          (AggValue.mapAnnSum ⇑h.toRingHom
            (Fin.append x.fst y.fst (Fin.natAdd _ j)))
        rw [Fin.append_right, Fin.append_right]
        exact hy.1 j
    · show GenAnn.finalize ⟨x'.snd.base * y'.snd.base,
          x'.snd.pending + y'.snd.pending⟩ = _
      rw [GenAnn.finalize_prod, GenAnn.finalize_prod, hx.2, hy.2, ← map_mul]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    refine rel_bind (ih₁ d γ hw.1 hn.1) (fun x' x hxx => ?_)
    have hplain : GenRow.plainTuple x'.fst = GenRow.plainTuple x.fst := by
      funext k
      exact (hxx.1 k).collapseSum_eq.trans
        (AggValue.collapseSum_mapAnnSum ⇑h.toRingHom (x.fst k))
    rw [hplain]
    refine rel_map_of_rel
      (ih₂ d (Fin.append (GenRow.plainTuple x.fst) γ) hw.2 hn.2)
      (fun y' y hy => ?_)
    refine ⟨?_, ?_⟩
    · intro k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · show GenValue.Equiv (Fin.append x'.fst y'.fst (Fin.castAdd _ j))
          (AggValue.mapAnnSum ⇑h.toRingHom
            (Fin.append x.fst y.fst (Fin.castAdd _ j)))
        rw [Fin.append_left, Fin.append_left]
        exact hxx.1 j
      · show GenValue.Equiv (Fin.append x'.fst y'.fst (Fin.natAdd _ j))
          (AggValue.mapAnnSum ⇑h.toRingHom
            (Fin.append x.fst y.fst (Fin.natAdd _ j)))
        rw [Fin.append_right, Fin.append_right]
        exact hy.1 j
    · show GenAnn.finalize ⟨x'.snd.base * y'.snd.base,
          x'.snd.pending + y'.snd.pending⟩ = _
      rw [GenAnn.finalize_prod, GenAnn.finalize_prod, hxx.2, hy.2, ← map_mul]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    exact Multiset.Rel.add (ih₁ d γ hw.1 hn.1) (ih₂ d γ hw.2 hn.2)
  | Dedup q ih =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    rw [show (q.evaluate
          (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q.evaluate d γ).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih d γ hw hn)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)]
    rw [groupByKey_mapAnnotatedRelation]
    exact rel_ofAnnotated_map h _
  | Alt k hk q ih =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    exact rel_bind_of_rel (ih d γ hw hn) (fun r' r hs => sim_alternativesAt h hs k)
  | @Mu cI n' b s q₀ q₁ ih₀ ih₁ =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    have hstep : ∀ X : AnnotatedRelation T K n',
        SemiringWithMonusHom.mapAnnotatedRelation h
            ((q₁.evaluate (d.assign s X) γ).map GenRow.toAnnotated)
          = (q₁.evaluate ((h.mapAnnotatedDatabase d).assign s
              (SemiringWithMonusHom.mapAnnotatedRelation h X)) γ).map
              GenRow.toAnnotated := by
      intro X
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact (map_eq_of_rel (ih₁ (d.assign s X) γ hw.2 hn.2)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)).symm
    have h₀ : SemiringWithMonusHom.mapAnnotatedRelation h
          ((q₀.evaluate d γ).map GenRow.toAnnotated)
        = (q₀.evaluate (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated := by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact (map_eq_of_rel (ih₀ d γ hw.1 hn.1)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)).symm
    rw [← h₀, ← muSum_map (mapAnnotatedRelation_add h)
      (step := fun X => (q₁.evaluate (d.assign s X) γ).map GenRow.toAnnotated)
      (stepP := fun Y => (q₁.evaluate ((h.mapAnnotatedDatabase d).assign s Y)
        γ).map GenRow.toAnnotated) hstep]
    exact rel_ofAnnotated_map h _
  | @MuSet cI n' b s q₀ q₁ ih₀ ih₁ =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    have hstep : ∀ X : AnnotatedRelation T K n',
        SemiringWithMonusHom.mapAnnotatedRelation h
            (AnnotatedRelation.dedupAnn
              ((q₀.evaluate (d.assign s X) γ).map GenRow.toAnnotated
                + (q₁.evaluate (d.assign s X) γ).map GenRow.toAnnotated))
          = AnnotatedRelation.dedupAnn
              ((q₀.evaluate ((h.mapAnnotatedDatabase d).assign s
                  (SemiringWithMonusHom.mapAnnotatedRelation h X)) γ).map
                    GenRow.toAnnotated
                + (q₁.evaluate ((h.mapAnnotatedDatabase d).assign s
                    (SemiringWithMonusHom.mapAnnotatedRelation h X)) γ).map
                      GenRow.toAnnotated) := by
      intro X
      have e₀ : SemiringWithMonusHom.mapAnnotatedRelation h
            ((q₀.evaluate (d.assign s X) γ).map GenRow.toAnnotated)
          = (q₀.evaluate ((h.mapAnnotatedDatabase d).assign s
              (SemiringWithMonusHom.mapAnnotatedRelation h X)) γ).map
              GenRow.toAnnotated := by
        unfold SemiringWithMonusHom.mapAnnotatedRelation
        rw [Multiset.map_map]
        exact (map_eq_of_rel (ih₀ (d.assign s X) γ hw.1 hn.1)
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)).symm
      have e₁ : SemiringWithMonusHom.mapAnnotatedRelation h
            ((q₁.evaluate (d.assign s X) γ).map GenRow.toAnnotated)
          = (q₁.evaluate ((h.mapAnnotatedDatabase d).assign s
              (SemiringWithMonusHom.mapAnnotatedRelation h X)) γ).map
              GenRow.toAnnotated := by
        unfold SemiringWithMonusHom.mapAnnotatedRelation
        rw [Multiset.map_map]
        exact (map_eq_of_rel (ih₁ (d.assign s X) γ hw.2 hn.2)
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)).symm
      rw [dedupAnn_mapAnnotatedRelation, mapAnnotatedRelation_add, e₀, e₁]
    rw [← muIter_map (h := SemiringWithMonusHom.mapAnnotatedRelation h) rfl
      (step := fun X => AnnotatedRelation.dedupAnn
        ((q₀.evaluate (d.assign s X) γ).map GenRow.toAnnotated
          + (q₁.evaluate (d.assign s X) γ).map GenRow.toAnnotated))
      (stepP := fun Y => AnnotatedRelation.dedupAnn
        ((q₀.evaluate ((h.mapAnnotatedDatabase d).assign s Y) γ).map
            GenRow.toAnnotated
          + (q₁.evaluate ((h.mapAnnotatedDatabase d).assign s Y) γ).map
              GenRow.toAnnotated)) hstep]
    exact rel_ofAnnotated_map h _
  | @ProvSum cI m n₁ κ' is his t q ih =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    rw [show (q.evaluate (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q.evaluate d γ).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih d γ hw hn)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)]
    set X : AnnotatedRelation T K m := (q.evaluate d γ).map GenRow.toAnnotated
    clear_value X
    rw [show SemiringWithMonusHom.mapAnnotatedRelation h X
        = X.map (SemiringWithMonusHom.mapAnnotatedTuple h) from rfl]
    rw [show ((X.map (SemiringWithMonusHom.mapAnnotatedTuple h)).map
          (fun p => (fun k => p.fst (is k) : Tuple T n₁))).dedup
        = ((X.map (fun p => (fun k => p.fst (is k) : Tuple T n₁)))).dedup from by
      rw [Multiset.map_map]
      exact congrArg Multiset.dedup
        (Multiset.map_congr rfl (fun p _ => rfl))]
    refine rel_map_of_forall (fun g _ => ⟨?_, ?_⟩)
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
  | Retag hκ q ih =>
    intro d γ hw hn
    exact ih d γ hw hn
  | @Win cI nI mI pI P O o w t f q dist keep ih =>
    -- one output row per input row; the tuple and the annotation are carried
    -- across unchanged, and the token differs only by a tie-block
    -- permutation – which a `FILTER` clause keeps, reading the tuple
    intro d γ hw hn
    cases hk : keep with
    | some φ =>
      rw [AggQueryIn.evaluate_Win_eq_when, AggQueryIn.evaluate_Win_eq_when]
      have hY : q.evaluateAnnotated (h.mapAnnotatedDatabase d) γ
          = Multiset.map (fun p : AnnotatedTuple T K nI =>
              ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI))
            (q.evaluateAnnotated d γ) := by
        have h1 : (q.evaluate (h.mapAnnotatedDatabase d) γ).map
              GenRow.toAnnotated
            = ((q.evaluate d γ).map GenRow.toAnnotated).map
                (SemiringWithMonusHom.mapAnnotatedTuple h) := by
          rw [Multiset.map_map]
          exact map_eq_of_rel (ih d γ hw hn)
            (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)
        exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))
      rw [hY, Multiset.map_map]
      refine rel_map_of_forall (fun x hx => ?_)
      refine ⟨fun k => ?_, ?_⟩
      · simp only [Function.comp_apply, ValueFrame.windowRowWhen]
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · rw [Fin.snoc_last, Fin.snoc_last]
          exact tokenOfDistWhen_mapAnn_equiv h P O o w t γ f dist φ.keeps _ hx
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          rfl
      · simp only [Function.comp_apply, ValueFrame.windowRowWhen]
        show (GenAnn.mk (h.toRingHom x.snd) 0).finalize
          = h.toRingHom ((GenAnn.mk x.snd 0).finalize)
        rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero]
    | none =>
    rw [AggQueryIn.evaluate_Win_eq, AggQueryIn.evaluate_Win_eq]
    have hY : q.evaluateAnnotated (h.mapAnnotatedDatabase d) γ
        = Multiset.map (fun p : AnnotatedTuple T K nI =>
            ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' nI))
          (q.evaluateAnnotated d γ) := by
      have h1 : (q.evaluate (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
          = ((q.evaluate d γ).map GenRow.toAnnotated).map
              (SemiringWithMonusHom.mapAnnotatedTuple h) := by
        rw [Multiset.map_map]
        exact map_eq_of_rel (ih d γ hw hn)
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)
      exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))
    rw [hY, Multiset.map_map]
    refine rel_map_of_forall (fun x hx => ?_)
    refine ⟨fun k => ?_, ?_⟩
    · simp only [Function.comp_apply, ValueFrame.windowRow]
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · rw [Fin.snoc_last, Fin.snoc_last]
        exact tokenOfDist_mapAnn_equiv h P O o w t γ f dist _ hx
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        rfl
    · simp only [Function.comp_apply, ValueFrame.windowRow]
      show (GenAnn.mk (h.toRingHom x.snd) 0).finalize
        = h.toRingHom ((GenAnn.mk x.snd 0).finalize)
      rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero]
  | @GammaTok cI mI nI₁ nI₂ κ' is his ts fs a q ih =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    rw [show (q.evaluate
          (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
        = ((q.evaluate d γ).map GenRow.toAnnotated).map
            (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI))
        from by
      have h1 : (q.evaluate
            (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
          = ((q.evaluate d γ).map GenRow.toAnnotated).map
              (SemiringWithMonusHom.mapAnnotatedTuple h) := by
        rw [Multiset.map_map]
        exact map_eq_of_rel (ih d γ hw hn)
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)
      exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))]
    set X : AnnotatedRelation T K mI := (q.evaluate d γ).map GenRow.toAnnotated
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
    refine ⟨?_, ?_⟩
    · intro k
      dsimp only [Function.comp]
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [Fin.append_left, Fin.append_left]
        refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
        · rw [Fin.append_left, Fin.append_left]
          rfl
        · rw [Fin.append_right, Fin.append_right]
          exact ⟨rfl, rfl, TiePerm.symm (fun e => e.symm)
            (ofGroup_mapAnn_tiePerm h (fs j') (ts j') is X kv.fst)⟩
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
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    rw [show (q₁.evaluate
          (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q₁.evaluate d γ).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih₁ d γ hw.1 hn.1)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)]
    rw [show (q₂.evaluate
          (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
        = SemiringWithMonusHom.mapAnnotatedRelation h
            ((q₂.evaluate d γ).map GenRow.toAnnotated) from by
      unfold SemiringWithMonusHom.mapAnnotatedRelation
      rw [Multiset.map_map]
      exact map_eq_of_rel (ih₂ d γ hw.2 hn.2)
        (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)]
    set X₁ : AnnotatedRelation T K _ := (q₁.evaluate d γ).map GenRow.toAnnotated
    set X₂ : AnnotatedRelation T K _ := (q₂.evaluate d γ).map GenRow.toAnnotated
    clear_value X₁ X₂
    rw [show SemiringWithMonusHom.mapAnnotatedRelation h X₁
        = X₁.map (SemiringWithMonusHom.mapAnnotatedTuple h) from rfl]
    simp only [Multiset.map_map]
    refine rel_map_of_forall (fun p _ => ?_)
    obtain ⟨u, α⟩ := p
    refine ⟨fun k => rfl, ?_⟩
    dsimp only [Function.comp, GenRow.ofAnnotated,
      SemiringWithMonusHom.mapAnnotatedTuple]
    rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero,
      SemiringWithMonusHom.map_sub]
    congr 1
    rw [groupByKey_find_eq_filter_sum, groupByKey_find_eq_filter_sum]
    exact SemiringWithMonusHom.sum_filter_map_snd_mapAnnotatedRelation h u X₂
  | @GammaScalar cI mI nI₂ ts fs q ih =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    rw [show (q.evaluate
          (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
        = ((q.evaluate d γ).map GenRow.toAnnotated).map
            (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI))
        from by
      have h1 : (q.evaluate
            (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
          = ((q.evaluate d γ).map GenRow.toAnnotated).map
              (SemiringWithMonusHom.mapAnnotatedTuple h) := by
        rw [Multiset.map_map]
        exact map_eq_of_rel (ih d γ hw hn)
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)
      exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))]
    set X : AnnotatedRelation T K mI := (q.evaluate d γ).map GenRow.toAnnotated
    clear_value X
    -- one row on each side, annotated `𝟙`, with nothing pending
    refine Multiset.Rel.cons ?_ Multiset.Rel.zero
    refine ⟨fun k => ?_, by simp [GenAnn.finalize]⟩
    exact ⟨rfl, rfl, TiePerm.symm (fun e => e.symm)
      (ofGroup_mapAnn_tiePerm h (fs k) (ts k) (fun i : Fin 0 => i.elim0) X
        (fun i : Fin 0 => i.elim0))⟩
  | @GammaNest cI mI nI₁ κ' is his p f q ih =>
    -- the one operator this does not cover: the two sides' groups are
    -- equal as bags of occurrences whose inner values *read* the same,
    -- and `GenValue.Equiv` at that level is what `noGammaNest` records
    -- as unproved
    intro d γ _ hn
    exact absurd hn not_false
  | @Gamma cI mI nI₁ nI₂ is ts fs q keep ih =>
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    rw [show (q.evaluate
          (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
        = ((q.evaluate d γ).map GenRow.toAnnotated).map
            (fun p => ((p.fst, h.toRingHom p.snd) : AnnotatedTuple T K' mI))
        from by
      have h1 : (q.evaluate
            (h.mapAnnotatedDatabase d) γ).map GenRow.toAnnotated
          = ((q.evaluate d γ).map GenRow.toAnnotated).map
              (SemiringWithMonusHom.mapAnnotatedTuple h) := by
        rw [Multiset.map_map]
        exact map_eq_of_rel (ih d γ hw hn)
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)
      exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))]
    set X : AnnotatedRelation T K mI := (q.evaluate d γ).map GenRow.toAnnotated
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
    refine ⟨?_, ?_⟩
    · intro k
      dsimp only [Function.comp]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · rw [Fin.append_left, Fin.append_left]
        rfl
      · rw [Fin.append_right, Fin.append_right]
        cases hkj : keep j with
        | none =>
          exact ⟨rfl, rfl, TiePerm.symm (fun e => e.symm)
            (ofGroup_mapAnn_tiePerm h (fs j) (ts j) is X kv.fst)⟩
        | some φ =>
          exact ⟨rfl, rfl, TiePerm.symm (fun e => e.symm)
            (ofGroupWhen_mapAnn_tiePerm h (fs j) (ts j) φ.keeps is X kv.fst)⟩
    · dsimp only [Function.comp]
      rw [GenAnn.finalize_gamma, GenAnn.finalize_gamma,
        havingGroup_annSum_hom h is X kv.fst,
        SemiringWithMonusHom.map_delta]
  | @WinExpr cI nI mI pI qI P O o ws ts fs g q keeps ih =>
    -- one output row per occurrence of the shared family. The two sides
    -- index that family by their own sorted order, so they are compared
    -- through a bijection of indices rather than index by index; the
    -- frames read the tuple (`hw.1`), which is what makes each pair of
    -- corresponding expression columns equivalent.
    intro d γ hw hn
    simp only [AggQueryIn.evaluate]
    have hY : Multiset.map GenRow.toAnnotated
          (q.evaluate (h.mapAnnotatedDatabase d) γ)
        = Multiset.map (fun y : AnnotatedTuple T K nI =>
            ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' nI))
          (Multiset.map GenRow.toAnnotated (q.evaluate d γ)) := by
      have h1 : Multiset.map GenRow.toAnnotated
            (q.evaluate (h.mapAnnotatedDatabase d) γ)
          = Multiset.map (SemiringWithMonusHom.mapAnnotatedTuple h)
            (Multiset.map GenRow.toAnnotated (q.evaluate d γ)) := by
        rw [Multiset.map_map]
        exact map_eq_of_rel (ih d γ hw.2 hn)
          (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)
      exact h1.trans (Multiset.map_congr rfl (fun p _ => rfl))
    rw [hY]
    set gh : AnnotatedTuple T K nI → AnnotatedTuple T K' nI :=
      fun y => ((y.fst, h.toRingHom y.snd) : AnnotatedTuple T K' nI)
      with hghdef
    set X : Multiset (AnnotatedTuple T K nI) :=
      Multiset.map GenRow.toAnnotated (q.evaluate d γ) with hXdef
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
    refine rel_occFam_of_equiv _ _ e (fun i => ⟨fun k => ?_, ?_⟩)
    · dsimp only
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · rw [Fin.snoc_last, Fin.snoc_last]
        exact exprOfWhen_mapAnn_equiv h P O o hw.1 ts fs g keeps γ
          (congrArg Prod.fst (he i)) hmul'
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact congrArg (fun y : AnnotatedTuple T K' nI => y.fst k') (he i)
    · dsimp only
      rw [GenAnn.finalize_of_pending_zero, GenAnn.finalize_of_pending_zero,
        he i]

/-- **Evaluator-level hom commutation**: the final annotated relation
computed by the general evaluator commutes with every
`SemiringWithMonusHom`, over every m-semiring. Nothing is asked of the
hom: the extra supersedes a non-injective one can trigger are
value-neutral by guard absorption (`delta_absorb`), and the annotation
tie-breaks of the group sort are value-neutral by the tie-block
congruence layer.

The one thing asked of the *query* is that a multi-frame window frame by
the tuple (`AggQueryIn.framesContainSelf`): such a window lists its
shared family by occurrence index, and a change of annotation semiring
re-sorts that index inside blocks of equal rows. Every window function
the library derives satisfies it, and
`AggQueryIn.framesContainSelf_of_noWinExpr` discharges it for a query
with no multi-frame window at all. -/
theorem AggQueryIn.evaluateAnnotated_hom (h : SemiringWithMonusHom K K')
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ)
    (hw : q.framesContainSelf) (hn : q.noGammaNest)
    (d : AnnotatedDatabase T K) :
    q.evaluateAnnotated (h.mapAnnotatedDatabase d)
      = SemiringWithMonusHom.mapAnnotatedRelation h
          (q.evaluateAnnotated d) := by
  unfold AggQueryIn.evaluateAnnotated SemiringWithMonusHom.mapAnnotatedRelation
  rw [Multiset.map_map]
  exact map_eq_of_rel (AggQueryIn.evaluate_hom_rel h q d _ hw hn)
    (fun r' r hs => GenRow.Sim.toAnnotated_eq h hs)

end EvaluatorHom
