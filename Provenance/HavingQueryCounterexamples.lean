/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryToAgg
import Provenance.Semirings.ChainFive
import Provenance.Semirings.Tropical
import Provenance.Semirings.Nat

/-!
# Query-level counterexamples for the HAVING / JOIN correspondence

The correspondence between the possible-world semantics of `HAVING`
comparisons on `COUNT(*)` and the `JOIN`-based rewriting holds in
commutative m-semirings that are absorptive and whose `⊗` distributes over
`⊖`. This file witnesses, **at the level of queries evaluated on concrete
annotated databases** (not merely of the underlying algebraic identities),
that both hypotheses are needed. All facts are checked by `decide`.

The instances share the base relation `R(g, v)` of arity 2, grouped by the
first column; on the fused side the query is
the general `HAVING` site for `COUNT(*) op C` and on the join side
the queries are

* `Q₂^{≥1} = ε(Π_{#0}(R))`,
* `Q₂^{≥2} = ε(Π_{#0}(σ_{#0=#2 ∧ #1<#3}(R × R)))`, and
* `Q₂^{=1} = Q₂^{≥1} - Q₂^{≥2}`,

the tie-broken comparison of the general construction degenerating to the
plain `<` because the second attributes of the instances are pairwise
distinct. The fused operator's output carries the group key and the
aggregate value while the join queries return the key only, so the
comparison is on the multisets of annotations.

* **Distributivity is needed**
  (`HavingQueryCounterexamples.ChainFive.query_counterexample`): in the
  five-element chain semiring – absorptive, hence idempotent, but not
  `⊗`-over-`⊖` distributive (`ChainFive.not_mul_sub_left_distributive`) –
  with annotations `(mid, hi, hi)` on one group, `COUNT(*) = 1` yields
  annotation `hi` on the fused side but `𝟘` on the join side. On the same
  instance the monotone comparisons `COUNT(*) ≥ 1` and `COUNT(*) ≥ 2` do
  agree with `Q₂^{≥1}` and `Q₂^{≥2}` (`ChainFive.query_ge_agree`,
  `ChainFive.query_ge_two_agree`), as `Query.joinCount_monotone_correct`
  requires: distributivity is needed for `=`, not for `≥`.

* **Absorptivity is needed**
  (`HavingQueryCounterexamples.MinTropicalZ.query_counterexample`): in the
  tropical semiring over `ℤ ∪ {∞}` – idempotent and distributive
  (`MinTropicalZ.mul_sub_left_distributive`) but not absorptive
  (`MinTropicalZ.not_absorptive_witness`) – with two occurrences annotated
  `trop (-1)` in one group, `COUNT(*) ≥ 1` yields annotation `trop (-2)`
  on the fused side but `trop (-1)` on the join side.
-/

namespace HavingQueryCounterexamples

/-- The two-column base relation `R(g, v)`. -/
def qR : Query ℕ 2 := Query.Rel 2 "R"

/-- The same base relation as a general query, for the `HAVING` site. -/
def qgR : AggQuery ℕ 2 (ColKind.allReg 2) := AggQueryIn.Rel 2 "R"

/-- `Q₂^{≥1} = ε(Π_{#0}(R))`. -/
def q2ge1 : Query ℕ 1 := ε (Π ![#0] qR)

/-- `Q₂^{≥2} = ε(Π_{#0}(σ_{#0=#2 ∧ #1<#3}(R × R)))`. -/
def q2ge2 : Query ℕ 1 :=
  ε (Π ![#0]
    (σ (Selection.And (Selection.BT (#0 == #2)) (Selection.BT (#1 < #3)))
      (@Query.Prod ℕ 2 2 4 (by decide) qR qR)))

/-- `Q₂^{=1} = Q₂^{≥1} - Q₂^{≥2}`. -/
def q2eq1 : Query ℕ 1 := q2ge1 - q2ge2

/-! ### Distributivity is needed: the `ChainFive` instance -/

/-- One group with key `0`, values `1, 2, 3`, annotations `mid, hi, hi`. -/
def dC : AnnotatedDatabase ℕ ChainFive :=
  [("R", ⟨2, ({⟨![0, 1], ChainFive.mid⟩, ⟨![0, 2], ChainFive.hi⟩,
      ⟨![0, 3], ChainFive.hi⟩} : Multiset (AnnotatedTuple ℕ ChainFive 2))⟩)]

/-- Fused side: `COUNT(*) = 1` has predicate provenance `hi` (each
singleton world contributes its own annotation, the factored
discarded-occurrence factor `𝟙 ⊖ hi` being `𝟙` in the chain). -/
theorem chainFive_fused :
    ((AggQueryIn.havingSite ![0] ![#1] ![SeqAggFunc.count] CompOp.eq 0
        (TermIn.const 1) qgR).evaluateAnnotated dC).map (fun p => p.snd)
      = {ChainFive.hi} := by
  decide

/-- Join side: `Q₂^{=1}` has annotation `𝟘` (`hi ⊖ hi`). -/
theorem chainFive_join :
    (q2eq1.evaluateAnnotated (by decide) dC).map (fun p => p.snd)
      = {(0 : ChainFive)} := by
  decide

/-- **Query-level part of the distributivity necessity**: in the
absorptive but non-distributive `ChainFive`, the fused `COUNT(*) = 1`
query and its join-based rewriting disagree on a concrete instance. -/
theorem ChainFive.query_counterexample :
    ((AggQueryIn.havingSite ![0] ![#1] ![SeqAggFunc.count] CompOp.eq 0
        (TermIn.const 1) qgR).evaluateAnnotated dC).map (fun p => p.snd)
      ≠ (q2eq1.evaluateAnnotated (by decide) dC).map (fun p => p.snd) := by
  decide

/-- Fused side of `COUNT(*) ≥ 1` on the same instance: `mid ⊕ hi ⊕ hi = hi`
(the worlds of size `≥ 1`, in factored form, sum to the monomials of the
singletons). -/
theorem chainFive_fused_ge_one :
    ((AggQueryIn.havingSite ![0] ![#1] ![SeqAggFunc.count] CompOp.ge 0
        (TermIn.const 1) qgR).evaluateAnnotated dC).map (fun p => p.snd)
      = {ChainFive.hi} := by
  decide

/-- **The monotone case closes in `ChainFive`**: on the very instance
that separates the fused `COUNT(*) = 1` query from its rewriting, the
fused `COUNT(*) ≥ 1` query and `Q₂^{≥1}` agree, as
`Query.joinCount_monotone_correct` predicts for every absorptive
m-semiring, distributive or not. -/
theorem ChainFive.query_ge_agree :
    ((AggQueryIn.havingSite ![0] ![#1] ![SeqAggFunc.count] CompOp.ge 0
        (TermIn.const 1) qgR).evaluateAnnotated dC).map (fun p => p.snd)
      = (q2ge1.evaluateAnnotated (by decide) dC).map (fun p => p.snd) := by
  decide

/-- Likewise for `COUNT(*) ≥ 2` and `Q₂^{≥2}`: both sides give
`mid ⊗ hi ⊕ mid ⊗ hi ⊕ hi ⊗ hi = hi`. -/
theorem ChainFive.query_ge_two_agree :
    ((AggQueryIn.havingSite ![0] ![#1] ![SeqAggFunc.count] CompOp.ge 0
        (TermIn.const 2) qgR).evaluateAnnotated dC).map (fun p => p.snd)
      = (q2ge2.evaluateAnnotated (by decide) dC).map (fun p => p.snd) := by
  decide

/-! ### Absorptivity is needed: the tropical instance over `ℤ ∪ {∞}` -/

/-- The tropical semiring over `ℤ ∪ {∞}` is not absorptive:
`𝟙 ⊕ trop (-1) = trop (-1) ≠ 𝟙`. -/
theorem MinTropicalZ.not_absorptive_witness :
    (1 : MinTropical (WithTop ℤ)) + MinTropical.trop ((-1 : ℤ) : WithTop ℤ)
      ≠ (1 : MinTropical (WithTop ℤ)) := by
  decide

/-- The tropical semiring over `ℤ ∪ {∞}` is `⊗`-over-`⊖` distributive. -/
theorem MinTropicalZ.mul_sub_left_distributive :
    mul_sub_left_distributive (MinTropical (WithTop ℤ)) :=
  MinTropical.mul_sub_left_distributive

/-- One group with key `0`, values `1, 2`, both annotated `trop (-1)`. -/
noncomputable def dZ : AnnotatedDatabase ℕ (MinTropical (WithTop ℤ)) :=
  [("R", ⟨2, ({⟨![0, 1], MinTropical.trop ((-1 : ℤ) : WithTop ℤ)⟩,
      ⟨![0, 2], MinTropical.trop ((-1 : ℤ) : WithTop ℤ)⟩}
      : Multiset (AnnotatedTuple ℕ (MinTropical (WithTop ℤ)) 2))⟩)]

/-- Fused side: `COUNT(*) ≥ 1` has predicate provenance `trop (-2)`: the
two singleton worlds have annotation `trop (-1) ⊗ (𝟙 ⊖ trop (-1)) = 𝟘`,
and only the full world `trop (-1) ⊗ trop (-1) = trop (-2)` survives. -/
theorem tropicalZ_fused :
    ((AggQueryIn.havingSite ![0] ![#1] ![SeqAggFunc.count] CompOp.ge 0
        (TermIn.const 1) qgR).evaluateAnnotated dZ).map (fun p => p.snd)
      = {MinTropical.trop ((-2 : ℤ) : WithTop ℤ)} := by
  decide

/-- Join side: `Q₂^{≥1}` has annotation `trop (-1) ⊕ trop (-1) = trop (-1)`. -/
theorem tropicalZ_join :
    (q2ge1.evaluateAnnotated (by decide) dZ).map (fun p => p.snd)
      = {MinTropical.trop ((-1 : ℤ) : WithTop ℤ)} := by
  decide

/-- **Query-level part of the absorptivity necessity**: in the idempotent
and distributive but non-absorptive tropical semiring over `ℤ ∪ {∞}`, the
fused `COUNT(*) ≥ 1` query and its join-based rewriting disagree on a
concrete instance. Same phenomenon as the algebra-level
`MinTropicalR.F_ne_S`, here at the level of evaluated queries. -/
theorem MinTropicalZ.query_counterexample :
    ((AggQueryIn.havingSite ![0] ![#1] ![SeqAggFunc.count] CompOp.ge 0
        (TermIn.const 1) qgR).evaluateAnnotated dZ).map (fun p => p.snd)
      ≠ (q2ge1.evaluateAnnotated (by decide) dZ).map (fun p => p.snd) := by
  decide

end HavingQueryCounterexamples

/-! ## The collapse of a count needs absorptivity

`AggValue.predProvScalar_count_ne_zero` collapses the possible-world sum of
`COUNT ≥ 1` to the `⊕`-sum of the occurrence annotations, in an absorptive
m-semiring. Outside absorptivity *neither* that reading nor the indicator
one is the sum.

Over `ℕ`, with two occurrences annotated `1` and `2`: a world that omits
the second is weighted `𝟙 ⊖ 2 = 𝟘`, and one that omits the first `𝟙 ⊖ 1 =
𝟘`, so the only world contributing is the one holding both, and the sum is
their product. The reading the collapse gives under absorptivity is
`⊕αᵢ = 3`, and the indicator reading `δ(⊕αᵢ)` is `𝟙`; the sum is `2`, and
is neither. What it counts is "every match present", not "at least one". -/

/-- The token of two occurrences annotated `1` and `2`, counted. -/
def natCountToken : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 1), (1, 2)], true⟩

/-- **The possible-world sum of `COUNT ≥ 1` over `ℕ` is the product of the
two annotations**, not their sum and not `𝟙`. -/
theorem natCountToken_predProvScalar :
    natCountToken.predProvScalar CompOp.ne 0 = 2 := by decide

/-- It is not the `⊕`-sum the absorptive collapse gives. -/
theorem natCountToken_ne_sum :
    natCountToken.predProvScalar CompOp.ne 0 ≠ ∑ i, natCountToken.anns i := by
  decide

/-- Nor is it the indicator reading `δ(⊕ᵢ αᵢ)`. -/
theorem natCountToken_ne_delta :
    natCountToken.predProvScalar CompOp.ne 0
      ≠ SemiringWithMonus.delta (∑ i, natCountToken.anns i) := by
  decide

/-! ## Two comparisons of one token do not read jointly

A selection whose predicate conjoins two comparisons of the same token –
a truncation's `m < #(k+1) ≤ m+c`, a `HAVING` such as
`count(*) > 2 AND count(*) < 5` – multiplies the two atoms' provenances,
each summed over the worlds of the token separately
(`GenPredIn.predsem`). `AggValue.predProvOf_mul_predProvOf` says that
this is the sum over the worlds where *both* comparisons hold when the
m-semiring is exclusive and its multiplication is idempotent. Neither
hypothesis can be dropped, and the *scalar* convention does not rescue
the identity either: `ℕ` is exclusive, the token below is scalar, and the
two readings still differ.

What this divergence needs is an occurrence annotated above `𝟙`: the
same token with its occurrence annotated `𝟙` agrees. A domain whose
carrier is bounded by `𝟙`, Viterbi for one, has no such annotation to
offer, so this instance is out of its reach. -/

/-- One occurrence of multiplicity `2`, counted, read in the scalar
convention. -/
def natRangeToken : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 2)], true⟩

/-- **A range test on one token is not the sum over the worlds in the
range.** The product of the two one-sided provenances is `4`, and the
joint sum is `2`. -/
theorem natRangeToken_mul_ne_and :
    natRangeToken.predProvOf CompOp.gt 0
        * natRangeToken.predProvOf CompOp.le 1
      ≠ natRangeToken.predProvOfAnd CompOp.gt 0 CompOp.le 1 := by decide

/-- The joint reading is the one the paper's truncation asks for. -/
theorem natRangeToken_and :
    natRangeToken.predProvOfAnd CompOp.gt 0 CompOp.le 1 = 2 := by decide

/-- The product is not. -/
theorem natRangeToken_mul :
    natRangeToken.predProvOf CompOp.gt 0
      * natRangeToken.predProvOf CompOp.le 1 = 4 := by decide

/-- The same token with its occurrence annotated `𝟙` agrees. -/
def natUnitToken : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 1)], true⟩

theorem natUnitToken_mul_eq_and :
    natUnitToken.predProvOf CompOp.gt 0
        * natUnitToken.predProvOf CompOp.le 1
      = natUnitToken.predProvOfAnd CompOp.gt 0 CompOp.le 1 := by decide

/-! ## The range closed form needs absorptivity in the difference itself

`Having.range_eq_S_monus_S` reads `HAVING C+1 ≤ count ≤ D` as the
join-side difference `S_{C+1} ⊖ S_{D+1}` under absorptivity and
left-distributivity of `⊗` over `⊖`. The hypotheses are not confined to
the step `F_{C+1} = S_{C+1}` that the proof passes through: the
difference parts company from the possible-world sum over `ℕ`, which is
not absorptive, on the smallest instance there is.

Two occurrences, each annotated `𝟙`, and the range `1 ≤ count ≤ 1`.
Every world of size one has `T_U(W) = 𝟙 ⊖ 𝟙 = 𝟘`, since its one-step
extension is annotated `𝟙` too, so the possible-world sum is `𝟘`; the
join side is `S_1 ⊖ S_2 = 2 ⊖ 1 = 𝟙`. -/

/-- The annotation of the counterexample: two occurrences, each `𝟙`. -/
def natRangeAnn : Fin 2 → ℕ := fun _ => 1

/-- **The range closed form fails over `ℕ`.** -/
theorem Having.natRange_ne :
    ∑ W ∈ (Finset.univ : Finset (Fin 2)).powerset.filter
        (fun W => 0 + 1 ≤ W.card ∧ W.card ≤ 1),
        Having.T natRangeAnn Finset.univ W
      ≠ (Having.S natRangeAnn Finset.univ 1
          - Having.S natRangeAnn Finset.univ 2 : ℕ) := by decide

/-- The possible-world sum is `𝟘` there. -/
theorem Having.natRange_worlds :
    ∑ W ∈ (Finset.univ : Finset (Fin 2)).powerset.filter
        (fun W => 0 + 1 ≤ W.card ∧ W.card ≤ 1),
        Having.T natRangeAnn Finset.univ W = 0 := by decide

/-- The join side is `𝟙`. -/
theorem Having.natRange_join :
    (Having.S natRangeAnn Finset.univ 1
      - Having.S natRangeAnn Finset.univ 2 : ℕ) = 1 := by decide

/-! ## `∨` over disjoint families is not the `⊕` of the two atoms

The `∧` rule is a decomposition of the one-sum reading under hypotheses
(`AggValue.predProvOf_mul_predProvOf`, and `complemented` for disjoint
families). The `∨` rule is not, and its failure is structural rather
than algebraic: it shows already in `𝔹`, which is exclusive, has an
idempotent `⊗` and is complemented, so no capability rescues it.

The reason is which worlds count. A world of a predicate reading two
*grouped* families must meet each of them, so a world in which one of
the two groups is empty is no world of the disjunction – while the
`⊕` of the two atoms fires there, the atom of the non-empty group
holding on its own. A conjunction is unaffected: its product already
demands both groups non-empty.

What makes the `⊕` sound in context is not independence of the families
but that it is multiplied into a row annotation carrying each group's
existence factor, which kills exactly those worlds. That is why a
disjunction may remove a `δ` only when *every* disjunct entails
existence (`GenPredIn.entailsExistence`), and why a disjunction with a
scalar operand – no existence factor to lean on, the empty world being
a world – has nothing to absorb the difference. -/

namespace Having

variable {T K : Type} [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]

/-- The joint reading of a disjunction of two conditions reading two
*disjoint* families: one `⊕`-sum over the worlds of the union, which
must meet each grouped family, weighted by whether either condition
holds there. The annotation of such a world is the product of the two
halves' (`Having.worldAnn_split`, under `complemented`). -/
def jointOr (a b : AggValue T K) (P Q : T → Kleene) : K :=
  ∑ W₁ ∈ Finset.univ.filter
      (fun W : Finset (Fin a.occs.length) => W.Nonempty),
    ∑ W₂ ∈ Finset.univ.filter
        (fun W : Finset (Fin b.occs.length) => W.Nonempty),
      Having.worldAnn a.anns W₁ * Having.worldAnn b.anns W₂
        * (if ((P (a.valOn W₁)).or (Q (b.valOn W₂))) = Kleene.true
            then 1 else 0)

end Having

/-- One occurrence, present. -/
def boolTokenT : AggValue ℕ Bool := ⟨SeqAggFunc.count, [(1, true)], false⟩

/-- One occurrence, absent. -/
def boolTokenF : AggValue ℕ Bool := ⟨SeqAggFunc.count, [(1, false)], false⟩

/-- `count ≠ 0`, true on every non-empty world. -/
def testNe : ℕ → Kleene := fun v => CompOp.ne.eval3 v 0

/-- `count = 5`, false on every world of a one-occurrence family. -/
def testEq : ℕ → Kleene := fun v => CompOp.eq.eval3 v 5

theorem bool_or_ne_joint :
    boolTokenT.predProvWith testNe + boolTokenF.predProvWith testEq
      ≠ Having.jointOr boolTokenT boolTokenF testNe testEq := by decide

theorem bool_or_per_atom : (boolTokenT.predProvWith testNe
    + boolTokenF.predProvWith testEq) = true := by decide

theorem bool_or_joint :
    Having.jointOr boolTokenT boolTokenF testNe testEq = false := by decide
