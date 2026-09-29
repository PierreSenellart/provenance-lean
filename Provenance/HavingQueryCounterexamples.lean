/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.JointFamily
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
joint sum is `2`.

It is also the instance for **two spellings of one selection**: a chain
`σ_{ψ₁}(σ_{ψ₂}(q))` multiplies the two predicates' provenances, while
`σ_{ψ₁ ∧ ψ₂}(q)` reads the conjunction jointly, one sum over the
family. The structural rule makes the two agree (`predsem_and`); the
joint reading does not, so the two spellings of what a SQL user would
call one query part here – `4` against `2`. -/
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

**What a predicate annotates is the joint evaluation of its Boolean
function in every world**: the `⊕`, over the worlds of the union of the
families the function reads, of the world's annotation times the
function's truth there. That is one rule for `∧`, `∨`, `¬`, a
Boolean-valued aggregate column and a searched `CASE` alike, and it is
`AggExpr.predProv` – an expression's occurrences are one shared family
`V = ⋃ⱼ Uⱼ`, a world must meet each *grouped* leaf, and `g` may be any
deterministic function of SQL, a Boolean combination among them.

`GenPredIn.predsem` is not that definition but a short cut for it,
`∧ ↦ ⊗` and `∨ ↦ ⊕`, the computation ProvSQL performs where the
m-semiring's properties license it – the same semantics, computed
cheaply. The question each instance below settles is where the licence
runs out. For `∧` they do under hypotheses
(`Having.sum_mul_sum_of_overlap`, with `complemented` alone for
disjoint families and `AggValue.predProvOf_mul_predProvOf` for one
family). For `∨` there is no such theorem, and the failure is
structural rather than algebraic: it shows already in `𝔹`, which is
exclusive, has an idempotent `⊗` and is complemented, so no capability
rescues it.

The reason is which worlds count. A world of a predicate reading two
*grouped* families must meet each of them, so a world in which one of
the two groups is empty is no world of the disjunction – while the
`⊕` of the two atoms fires there, the atom of the non-empty group
holding on its own. A conjunction is unaffected: its product already
demands both groups non-empty.

Over `𝔹` the row's own factors hide the difference: the `δ` of the
empty group kills the row the `⊕` kept, which is why a disjunction may
remove a `δ` only when *every* disjunct entails existence
(`GenPredIn.entailsExistence`). Over `ℕ` they do not, `δ` recording
support where the difference is a multiplicity – so over `ℕ` the `⊕` is
not a licensed short cut for a disjunction and the sum has to be
computed.

The double sums `joint2` and `joint3` below write the joint reading in
split form, a product of the halves' world annotations. That is the
annotation of a world of the union in a *complemented* `K`
(`Having.worldAnn_split`); `𝔹` and `ℕ` are complemented, so over them
the instances are instances about the union reading. -/

namespace Having

variable {T K : Type} [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]

/-- The joint reading of a disjunction of two conditions reading two
*disjoint* families: one `⊕`-sum over the worlds of the union, which
must meet each grouped family, weighted by whether either condition
holds there. The annotation of such a world is the product of the two
halves' (`Having.worldAnn_split`, under `complemented`). -/
def joint2 (a b : AggValue T K) (χ : T → T → Kleene) : K :=
  ∑ W₁ ∈ Finset.univ.filter
      (fun W : Finset (Fin a.occs.length) => W.Nonempty),
    ∑ W₂ ∈ Finset.univ.filter
        (fun W : Finset (Fin b.occs.length) => W.Nonempty),
      Having.worldAnn a.anns W₁ * Having.worldAnn b.anns W₂
        * (if χ (a.valOn W₁) (b.valOn W₂) = Kleene.true then 1 else 0)

/-- The joint reading of a disjunction of two conditions reading two
*disjoint* families. -/
def jointOr (a b : AggValue T K) (P Q : T → Kleene) : K :=
  joint2 a b (fun x y => (P x).or (Q y))

/-- The joint reading of an atom over three families: one `⊕`-sum over
the worlds of the union, each of which meets all three. -/
def joint3 (a b c : AggValue T K) (χ : T → T → T → Kleene) : K :=
  ∑ W₁ ∈ Finset.univ.filter
      (fun W : Finset (Fin a.occs.length) => W.Nonempty),
    ∑ W₂ ∈ Finset.univ.filter
        (fun W : Finset (Fin b.occs.length) => W.Nonempty),
      ∑ W₃ ∈ Finset.univ.filter
          (fun W : Finset (Fin c.occs.length) => W.Nonempty),
        Having.worldAnn a.anns W₁ * Having.worldAnn b.anns W₂
            * Having.worldAnn c.anns W₃
          * (if χ (a.valOn W₁) (b.valOn W₂) (c.valOn W₃) = Kleene.true
              then 1 else 0)

omit [ValueType T] [DecidableEq K] in
omit [ValueType T] [DecidableEq K] in
/-- **`joint2` is the union reading**: the split double sum is the `⊕`
over the worlds of the concatenated family where `K` is complemented
(`Having.jointPair_eq_split`). `𝔹` and `ℕ` are, so over them the
instances below are instances about the union reading; over a
non-complemented `K` it is `jointPair` that says what a predicate
annotates, and the double sum that does not. -/
theorem joint2_eq_jointPair (hc : complemented K) (a b : AggValue T K)
    (ha : a.scalar = false) (hb : b.scalar = false) (χ : T → T → Kleene) :
    joint2 a b χ = jointPair a b χ := by
  rw [jointPair_eq_split hc]
  simp only [joint2, ha, hb, Bool.false_eq_true, false_or]

omit [ValueType T] [DecidableEq K] in
/-- **The branches of a conditional exclude each other.** Read world by
world, a two-branch case split is the one sum: in each world the guard
either holds or does not, so exactly one branch fires and the `⊕` counts
it once. No property of the m-semiring is used – and the guard of the
second branch is the test that the first is *not true*, not its
negation, which would be `𝟘` in a world where the guard is unknown and
leave that world satisfying neither branch, while SQL falls through.

What the statement needs is that the branches read *one* family. Where
they read different ones the case split and the one sum over the union
part (`natCase_ne`). -/
theorem joint2_branch_split (a b : AggValue T K) (P : T → Kleene)
    (χ₁ χ₂ : T → T → Kleene) :
    joint2 a b (fun x y => if P x = Kleene.true then χ₁ x y else χ₂ x y)
      = joint2 a b (fun x y => (P x).and (χ₁ x y))
        + joint2 a b
            (fun x y => (Kleene.ofBool (!(P x).isTrue)).and (χ₂ x y)) := by
  unfold joint2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun W₁ _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun W₂ _ => ?_)
  rw [← mul_add]
  refine congrArg _ ?_
  cases hP : P (a.valOn W₁) <;>
    cases h₁ : χ₁ (a.valOn W₁) (b.valOn W₂) <;>
    cases h₂ : χ₂ (a.valOn W₁) (b.valOn W₂) <;>
    simp [hP, h₁, h₂, Kleene.and, Kleene.ofBool, Kleene.isTrue]

end Having

/-- One occurrence, present. -/
def boolTokenT : AggValue ℕ Bool := ⟨SeqAggFunc.count, [(1, true)], false⟩

/-- One occurrence, absent. -/
def boolTokenF : AggValue ℕ Bool := ⟨SeqAggFunc.count, [(1, false)], false⟩

/-- `count ≠ 0`, true on every non-empty world. -/
def testNe : ℕ → Kleene := fun v => CompOp.ne.eval3 v 0

/-- `count = 5`, false on every world of a one-occurrence family. -/
def testEq : ℕ → Kleene := fun v => CompOp.eq.eval3 v 5

/-- **The `⊕` claims a provenance for a tuple that is in no world.**
The second family is absent – its one occurrence is annotated `𝟘` – so
every world of the union that meets it carries `𝟘` and the joint
reading is `⊥`, while the structural `⊕` takes the first side's own sum
and gives `⊤`. A tuple carrying both aggregate columns comes from a
join of two groupings and does not exist when one group is empty, so
`⊥` is the right answer and the `⊕` is wrong rather than merely
different. -/
theorem bool_or_ne_joint :
    boolTokenT.predProvWith testNe + boolTokenF.predProvWith testEq
      ≠ Having.jointOr boolTokenT boolTokenF testNe testEq := by decide

theorem bool_or_per_atom : (boolTokenT.predProvWith testNe
    + boolTokenF.predProvWith testEq) = true := by decide

theorem bool_or_joint :
    Having.jointOr boolTokenT boolTokenF testNe testEq = false := by decide

/-! ### The same over `ℕ`, where the existence factors do not absorb it

The `𝔹` instance above parts at predicate level and closes at row level,
the `δ` of the empty group killing the row. Over `ℕ` it does not close:
`δ` records support, and what differs is a multiplicity. Two grouped
families, one row annotated `𝟙` and one annotated `2`, with the first
condition satisfied and the second not, give `𝟙` per atom and `2` for
the one sum over the union – and the row's own factors are
`δ(1) ⊗ δ(2) = 𝟙`, so nothing absorbs the difference.

The extra factor is the *unsatisfied* disjunct's family, which the
satisfied disjunct never reads. That is not a derivation count, so it is
a different kind of error from the multiplicity `⊕` already gives a
disjunction (`p ∨ p` is `2` in `ℕ`), and it is what makes the one-sum
reading over the union the wrong reference for a disjunction. -/

/-- One occurrence of multiplicity `𝟙`. -/
def natTokenOne : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 1)], false⟩

/-- One occurrence of multiplicity `2`. -/
def natTokenTwo : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 2)], false⟩

/-- `count ≥ 1`, satisfied. -/
def testGe1 : ℕ → Kleene := fun v => CompOp.ge.eval3 v 1

/-- `count ≥ 2`, not satisfied on a one-occurrence family. -/
def testGe2 : ℕ → Kleene := fun v => CompOp.ge.eval3 v 2

theorem nat_or_per_atom :
    natTokenOne.predProvWith testGe1 + natTokenTwo.predProvWith testGe2 = 1 := by
  decide

theorem nat_or_joint :
    Having.jointOr natTokenOne natTokenTwo testGe1 testGe2 = 2 := by decide

theorem nat_or_ne_joint :
    natTokenOne.predProvWith testGe1 + natTokenTwo.predProvWith testGe2
      ≠ Having.jointOr natTokenOne natTokenTwo testGe1 testGe2 := by decide

/-- **The same, against the union reading itself.** `ℕ` is
complemented, so the double sum above is `Having.jointPair` – the `⊕`
over the worlds of the concatenated family – and the structural `⊕` of
the two atoms is not it. -/
theorem nat_or_ne_jointPair :
    natTokenOne.predProvWith testGe1 + natTokenTwo.predProvWith testGe2
      ≠ Having.jointPair natTokenOne natTokenTwo
          (fun x y => (testGe1 x).or (testGe2 y)) := by
  rw [← Having.joint2_eq_jointPair Nat.complemented _ _ rfl rfl]
  exact nat_or_ne_joint

/-- And over `𝔹`, which is complemented too. -/
theorem bool_or_ne_jointPair :
    boolTokenT.predProvWith testNe + boolTokenF.predProvWith testEq
      ≠ Having.jointPair boolTokenT boolTokenF
          (fun x y => (testNe x).or (testEq y)) := by
  rw [← Having.joint2_eq_jointPair Bool.complemented _ _ rfl rfl]
  exact bool_or_ne_joint

/-! ### Two alternatives of a Boolean aggregate column

A Boolean combination of aggregate comparisons need not be written as a
predicate: SQL lets it be the value of a column, and an enclosing block
then reads that column through the atom `flag = true` – as a filter, or
as a key. Read structurally, the `true` alternative is the `⊕` of the
disjuncts and the `false` one the `⊗` of their negations, a conjunction
over disjoint families which decomposes under `complemented` alone.

The two alternatives of one occurrence do not then partition the worlds
of the families the column reads. Over `ℕ`, with both disjuncts
satisfied on two families each annotated `𝟙`, they carry `2 ⊕ 𝟘 = 2`,
where the worlds of the two families together carry `𝟙` – which is what
every *non*-Boolean column's alternatives carry, and what `δ` of the
support is. The excess is the worlds where both disjuncts hold, counted
once per disjunct. -/

/-- `count < 1`, the negation of `testGe1`, satisfied by no world of a
one-occurrence family. -/
def testLt1 : ℕ → Kleene := fun v => CompOp.lt.eval3 v 1

theorem nat_or_both_per_atom :
    natTokenOne.predProvWith testGe1 + natTokenOne.predProvWith testGe1
      = 2 := by decide

theorem nat_or_both_joint :
    Having.jointOr natTokenOne natTokenOne testGe1 testGe1 = 1 := by decide

/-- The `false` alternative of the same column is `𝟘` here: neither
disjunct fails. -/
theorem nat_or_false_alt :
    natTokenOne.predProvWith testLt1 * natTokenOne.predProvWith testLt1
      = 0 := by decide

/-- What the worlds of the two families together carry, which is what a
non-Boolean column's alternatives sum to. -/
theorem nat_or_support :
    Having.joint2 natTokenOne natTokenOne (fun _ _ => Kleene.true) = 1 := by
  decide

/-- **The alternatives of a Boolean aggregate column overcount.** -/
theorem nat_or_alternatives_ne_support :
    (natTokenOne.predProvWith testGe1 + natTokenOne.predProvWith testGe1)
        + natTokenOne.predProvWith testLt1 * natTokenOne.predProvWith testLt1
      ≠ Having.joint2 natTokenOne natTokenOne (fun _ _ => Kleene.true) := by
  decide

/-! ### A conditional whose branches read different families

SQL's searched `CASE` puts a Boolean combination inside a term and a
value comes out, so the atom `CASE … END = v` is the disjunction of the
branches, `ψ̄₁ ∧ … ∧ ψ̄ⱼ₋₁ ∧ ψⱼ ∧ eⱼ ≐ v`, with `ψ̄` the test that `ψ` is
not *true* and not its negation – a negated comparison is `𝟘` where the
comparison is unknown, which would leave such a world satisfying no
branch at all, while SQL falls through to the next one.

The branch guards exclude each other, so the `⊕` over the branches
counts no world twice: that is `Having.joint2_branch_split`, which holds
in every m-semiring and asks nothing of it. What it needs is that the
branches read *one* family. As soon as two branches read aggregates
over different occurrence sequences, the case split and the one sum over
the union of all the families part, with no disjunction anywhere in the
query: the union charges the branch that fires for the family the other
branch would have read. -/

/-- `count = 1`, satisfied by the world of a one-occurrence family. -/
def testEq1 : ℕ → Kleene := fun v => CompOp.eq.eval3 v 1

/-- The case split of `CASE WHEN c ≥ 1 THEN d ELSE e END ≐ 1`, with `c`
and `d` annotated `𝟙` and `e` – read by no world, the guard holding –
annotated `2`. Only the first branch fires. -/
theorem natCase_split :
    Having.joint2 natTokenOne natTokenOne
        (fun x y => (testGe1 x).and (testEq1 y))
      + Having.joint2 natTokenOne natTokenTwo
        (fun x y => (Kleene.ofBool (!(testGe1 x).isTrue)).and (testEq1 y))
      = 1 := by decide

/-- The one sum over the union of all three families charges the world
for `e` as well. -/
theorem natCase_joint :
    Having.joint3 natTokenOne natTokenOne natTokenTwo
        (fun x y z => testEq1 (if testGe1 x = Kleene.true then y else z))
      = 2 := by decide

/-- **A conditional parts the two readings with no disjunction in the
query**, as soon as its branches read different families. -/
theorem natCase_ne :
    Having.joint2 natTokenOne natTokenOne
          (fun x y => (testGe1 x).and (testEq1 y))
        + Having.joint2 natTokenOne natTokenTwo
          (fun x y => (Kleene.ofBool (!(testGe1 x).isTrue)).and (testEq1 y))
      ≠ Having.joint3 natTokenOne natTokenOne natTokenTwo
          (fun x y z => testEq1 (if testGe1 x = Kleene.true then y else z)) := by
  decide

/-! ### The same two instances against the definition

The sums above are written family by family. Stated against
`AggExpr.predProv` – the joint evaluation over the worlds of one shared
family, which is the definition – the same numbers come out, and
nothing is assumed of `ℕ` to get them. Two singleton families are two
occurrences of one family that the leaves read one each. -/

/-- `c ≥ 1 ∨ d ≥ 1` over two families each annotated `𝟙`, as the
Boolean function the joint reading evaluates: `𝟙` where the disjunction
holds, `𝟘` where it does not. -/
def natOrExpr : AggExpr ℕ ℕ where
  arity := 2
  occs := [(![1, 1], 1), (![1, 1], 1)]
  reads := ![{0}, {1}]
  aggs := ![SeqAggFunc.count, SeqAggFunc.count]
  scalar := ![false, false]
  g := fun v => if 1 ≤ v 0 ∨ 1 ≤ v 1 then 1 else 0
  covered := by decide

/-- **The joint reading of the disjunction is `𝟙`**: its one world meets
both families and carries `𝟙 ⊗ 𝟙`. -/
theorem natOrExpr_joint : natOrExpr.predProv CompOp.eq 1 = 1 := by decide

/-- **The structural `⊕` is `2`**, counting the world once per disjunct. -/
theorem natOrExpr_ne_structural :
    natTokenOne.predProvWith testGe1 + natTokenOne.predProvWith testGe1
      ≠ natOrExpr.predProv CompOp.eq 1 := by decide

/-- `CASE WHEN c ≥ 1 THEN d ELSE e END`, with `c` and `d` annotated `𝟙`
and `e` – which no world in which the guard holds reads – annotated
`2`. -/
def natCaseExpr : AggExpr ℕ ℕ where
  arity := 3
  occs := [(![1, 1, 1], 1), (![1, 1, 1], 1), (![1, 1, 1], 2)]
  reads := ![{0}, {1}, {2}]
  aggs := ![SeqAggFunc.count, SeqAggFunc.count, SeqAggFunc.count]
  scalar := ![false, false, false]
  g := fun v => if 1 ≤ v 0 then v 1 else v 2
  covered := by decide

/-- **The joint reading of the conditional is `2`**: its one world meets
all three families, `e` among them, though the branch that fires never
reads `e`. -/
theorem natCaseExpr_joint : natCaseExpr.predProv CompOp.eq 1 = 2 := by decide

/-- **The branch decomposition is `𝟙`**, so a conditional whose branches
read different families parts from the definition with no disjunction
anywhere in the query. -/
theorem natCaseExpr_ne_split :
    Having.joint2 natTokenOne natTokenOne
          (fun x y => (testGe1 x).and (testEq1 y))
        + Having.joint2 natTokenOne natTokenTwo
          (fun x y => (Kleene.ofBool (!(testGe1 x).isTrue)).and (testEq1 y))
      ≠ natCaseExpr.predProv CompOp.eq 1 := by decide

/-! ### At the row level: an idempotent `⊕` is not what makes the `⊕` exact

What an implementation reports is not a bare predicate provenance but a
row annotation, a group carrying its existence factor: `δ(β₁) ⊗ δ(β₂) ⊗
predsem(ψ)`. Over `𝔹` those factors close the gap the `∨` rule opens –
`bool_or_ne_joint` is a statement about the *predicate* provenance and
not about the row, and `bool_row_agree` says so.

They do not close it in general, and an idempotent `⊕` is not the
condition. `ChainFive` is absorptive, so its `⊕` is idempotent, and its
`δ` is not the identity: `δ(hi) = 𝟙`. Two singleton grouped families
annotated `hi` and `mid`, the first side's test satisfied and the
second's not, give `hi` for the reported row and `lo` for the joint
reading, the `δ` factors having replaced the second family's `mid` by
`𝟙`. The missing factor is the other side's annotation, and `δ` can
only restore it where `δ` *is* the identity, which `𝔹` and `𝔹[X]` have
and `ChainFive`, Viterbi, `ℕ`, the tropical semirings and `MinMax` do
not. -/

/-- One occurrence annotated `hi`, grouped. -/
def chainTokenHi : AggValue ℕ ChainFive :=
  ⟨SeqAggFunc.count, [(1, ChainFive.hi)], false⟩

/-- One occurrence annotated `mid`, grouped. -/
def chainTokenMid : AggValue ℕ ChainFive :=
  ⟨SeqAggFunc.count, [(1, ChainFive.mid)], false⟩

/-- **The reported row**: the two groups' existence factors times the
structural `⊕` of the two sides. -/
theorem chain_row_structural :
    SemiringWithMonus.delta ChainFive.hi * SemiringWithMonus.delta ChainFive.mid
        * (chainTokenHi.predProvWith testGe1
          + chainTokenMid.predProvWith testGe2)
      = ChainFive.hi := by decide

/-- **The joint reading of the same row.** -/
theorem chain_row_joint :
    Having.jointPair chainTokenHi chainTokenMid
        (fun x y => (testGe1 x).or (testGe2 y)) = ChainFive.lo := by decide

/-- **So the existence factors do not make the `⊕` exact**, in a
semiring whose `⊕` is idempotent. -/
theorem chain_row_ne :
    SemiringWithMonus.delta ChainFive.hi * SemiringWithMonus.delta ChainFive.mid
        * (chainTokenHi.predProvWith testGe1
          + chainTokenMid.predProvWith testGe2)
      ≠ Having.jointPair chainTokenHi chainTokenMid
          (fun x y => (testGe1 x).or (testGe2 y)) := by decide

/-- **Over `𝔹` they do**, which is why the `𝔹` instance above is about
the predicate provenance and not about the row: `δ` is the identity
there, so the factor the `⊕` drops is restored. -/
theorem bool_row_agree :
    SemiringWithMonus.delta true * SemiringWithMonus.delta false
        * (boolTokenT.predProvWith testNe + boolTokenF.predProvWith testEq)
      = Having.jointPair boolTokenT boolTokenF
          (fun x y => (testNe x).or (testEq y)) := by decide

/-! ### Inclusion–exclusion is not the joint reading of a disjunction

Over disjoint families whose totals are `𝟙` – the scalar convention,
where the empty world counts – the joint reading of a disjunction is
sometimes written `S₁ ⊕ S₂ ⊖ S₁ ⊗ S₂`, on the reading of `⊖` as a
subtraction that removes the worlds counted twice. That is an identity
about numbers, not about m-semirings: it holds over `ℕ`, and fails in
`𝔹`, where `⊤ ⊕ ⊤ ⊖ ⊤ ⊗ ⊤` is `⊤ ⊖ ⊤ = ⊥` while both sides of the
disjunction hold. The overlap is not a quantity to be removed; in an
idempotent `⊕` it was never counted twice. -/

/-- One occurrence, present, read in the scalar convention – so the
empty world counts and the family's total is `𝟙`. -/
def boolScalarT : AggValue ℕ Bool := ⟨SeqAggFunc.count, [(1, true)], true⟩

theorem bool_incl_excl_sides :
    boolScalarT.predProvOfWith testNe = true
      ∧ Having.jointPair boolScalarT boolScalarT
          (fun x y => (testNe x).or (testNe y)) = true := by
  constructor <;> decide

/-- **Inclusion–exclusion fails in `𝔹`**: the joint reading is `⊤` and
the formula gives `⊥`. -/
theorem bool_incl_excl_ne :
    Having.jointPair boolScalarT boolScalarT
        (fun x y => (testNe x).or (testNe y))
      ≠ boolScalarT.predProvOfWith testNe + boolScalarT.predProvOfWith testNe
          - boolScalarT.predProvOfWith testNe * boolScalarT.predProvOfWith testNe := by
  decide

/-- One occurrence annotated `𝟙`, scalar – the `ℕ` counterpart, where
the formula does hold. -/
def natScalarOne : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 1)], true⟩

theorem nat_incl_excl_eq :
    Having.jointPair natScalarOne natScalarOne
        (fun x y => (testGe1 x).or (testGe1 y))
      = natScalarOne.predProvOfWith testGe1 + natScalarOne.predProvOfWith testGe1
          - natScalarOne.predProvOfWith testGe1 * natScalarOne.predProvOfWith testGe1 := by
  decide
