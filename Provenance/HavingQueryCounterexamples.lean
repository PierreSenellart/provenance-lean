/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.JointFamily
import Provenance.Nested
import Provenance.QueryToAgg
import Provenance.Semirings.ChainFive
import Provenance.Semirings.Tropical
import Provenance.Semirings.Nat
import Provenance.Semirings.MinMax
import Provenance.Semirings.Viterbi
import Provenance.Derived

/-!
# Query-level counterexamples for the HAVING / JOIN correspondence

The correspondence between the possible-world semantics of `HAVING`
comparisons on `COUNT(*)` and the `JOIN`-based rewriting holds in
commutative m-semirings that are absorptive and whose `⊗` distributes over
`⊖`. This file witnesses, **at the level of queries evaluated on concrete
annotated databases** (not merely of the underlying algebraic identities),
that both hypotheses are needed. All facts are checked by `decide`.

It also witnesses, at that same level, that the `EXCEPT` spelling of
`WHERE NOT EXISTS` is not the antijoin
(`ChainFive.antijoin_query_ne_except`, beside the algebraic
`ChainFive.antijoin_ne_difference`). An operator-level witness and a
query-level one are different statements, not two presentations of one:
the second has to pick the operators the syntax offers, an instance on
which the two spellings mean the same condition, and the place where a
rewriting claims they agree.

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

* **A `FILTER` clause that keeps everything is not the unfiltered
  reading, over a *cut* family** (`chain_count_zero_when_ne`): in
  `ChainFive`, one row annotated `mid` grouped and tested by
  `HAVING count(*) ≐ 0` gives `𝟘`, while the same read over the
  occurrences the clause keeps, in the scalar convention, gives `𝟙`.
  This is why no clause cuts a family any more: a grouping, a window and
  a multi-frame window all read one through `AggExpr`'s two flag families
  (`AggExpr.ofGroupWhen`, `ValueFrame.exprWhen`, `ValueFrame.exprOfWhen`),
  and what the expression reading gives instead is `chainExprNone_zero`,
  `chainExprMixed_zero` and `chainWinMixed_zero`. The empty world
  weighs `𝟙 ⊖ ⊕α` and the group's existence factor does not absorb it
  (`chain_delta_not_absorb_empty`), which `ℕ` hides
  (`nat_delta_absorb_empty`). What the two flag families of `AggExpr`
  give instead – the group fixing the worlds and the clause fixing what
  the leaf reads – is `chainExprNone_zero` and `chainExprMixed_zero`.
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

/-! #### The antijoin and the `EXCEPT` that spells it

`ChainFive.antijoin_ne_difference` is the algebra: `a ⊗ (𝟙 ⊖ b)` and
`a ⊖ a ⊗ b` differ at `a = b = hi`. These are the same two readings as
*queries* on an instance, which is a different statement and not another
presentation of that one: the operators have to be the ones the syntax
offers, the instance has to make the condition they spell the same, and
the two evaluations have to be compared where the rewriting claims they
agree. -/

/-- `R(a)` with one row annotated `hi`, and `Q(b)` with the one row it
matches, also annotated `hi`. -/
def dX : AnnotatedDatabase ℕ ChainFive :=
  [("R", ⟨1, ({⟨![0], ChainFive.hi⟩}
      : Multiset (AnnotatedTuple ℕ ChainFive 1))⟩),
   ("Q", ⟨1, ({⟨![0], ChainFive.hi⟩}
      : Multiset (AnnotatedTuple ℕ ChainFive 1))⟩)]

/-- The left arm, as a general query. -/
def qXR : AggQuery ℕ 1 (ColKind.allReg 1) := AggQueryIn.Rel 1 "R"

/-- The right arm, read once per row of the left. -/
def qXQ : AggQueryIn ℕ 1 1 (ColKind.allReg 1) := AggQueryIn.Rel 1 "Q"

/-- The correlated match `Q.b = R.a`. -/
def phiX : GenPredIn ℕ 1 (ColKind.allReg 1) :=
  GenPredIn.cmp CompOp.eq (TermGIn.index 0 rfl) (TermGIn.outer 0)

/-- `WHERE NOT EXISTS` as the syntax offers it: the derived antijoin,
which counts the matches and keeps the rows whose count is `𝟘`. -/
def qAnti : AggQuery ℕ 1 (ColKind.allReg 1) :=
  AggQueryIn.antijoin SeqAggFunc.count 0 phiX qXR qXQ

/-- `R` as a classical query. -/
def qcR : Query ℕ 1 := Query.Rel 1 "R"

/-- `Q` as a classical query. -/
def qcQ : Query ℕ 1 := Query.Rel 1 "Q"

/-- The `EXCEPT` that spells the same condition:
`R - Π_{#0}(σ_{#0 = #1}(R × Q))`. -/
def qExcept : Query ℕ 1 :=
  qcR - Π ![#0] (σ (Selection.BT (#0 == #1))
    (@Query.Prod ℕ 1 1 2 (by decide) qcR qcQ))

/-- **The antijoin keeps the row**, annotated `hi ⊗ (𝟙 ⊖ hi) = hi`: the
world in which the match is absent weighs `𝟙 ⊖ hi`, which is `𝟙` in the
chain. -/
theorem chainFive_antijoinQuery :
    (qAnti.evaluateAnnotated dX).map (fun p => p.snd)
      = {ChainFive.hi} := by
  decide

/-- **The `EXCEPT` drops it**, annotated `hi ⊖ hi ⊗ hi = 𝟘`: the chain's
monus cancels the row against its own matched copy
(`ChainFive.difference_ann`). -/
theorem chainFive_exceptQuery :
    (qExcept.evaluateAnnotated (by decide) dX).map (fun p => p.snd)
      = {(0 : ChainFive)} := by
  decide

/-- **Query-level witness that the `EXCEPT` spelling of `WHERE NOT
EXISTS` is not the antijoin**: on one row with one match in the
absorptive, non-distributive `ChainFive`, the antijoin keeps the row and
the difference drops it. `ChainFive.antijoin_ne_difference` is the same
fact about the operations; this one is about two queries evaluated on an
instance, and it is what a rewriting that replaces one spelling by the
other has to answer for. -/
theorem ChainFive.antijoin_query_ne_except :
    (qAnti.evaluateAnnotated dX).map (fun p => p.snd)
      ≠ (qExcept.evaluateAnnotated (by decide) dX).map (fun p => p.snd) := by
  decide

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

/-! #### What a `WHERE EXISTS` loses outside absorptivity

`evaluateAnnotated_semijoin` reads a row kept by `WHERE EXISTS (Q)` as its
own annotation times the `⊕`-sum of its witnesses' – the collapse of
`AggValue.predProvScalar_count_ne_zero`, which asks `K` to be absorptive.
Outside absorptivity the annotation is still the sum over the worlds in
which a match is present, and that is not the sum of the matches'
annotations: here it is their *product*, since every world that omits a
match is weighted `𝟙 ⊖ trop(-1) = 𝟘` and only the full world survives.
`MinTropicalZ` isolates the property, being distributive
(`MinTropicalZ.mul_sub_left_distributive`) and not absorptive
(`MinTropicalZ.not_absorptive_witness`). -/

/-- The token a `WHERE EXISTS` reads over two matches, both annotated
`trop (-1)`: counted, in the scalar convention, so that the empty world is
one of its worlds. -/
noncomputable def MinTropicalZ.existsToken :
    AggValue ℕ (MinTropical (WithTop ℤ)) :=
  ⟨SeqAggFunc.count,
    [(1, MinTropical.trop ((-1 : ℤ) : WithTop ℤ)),
      (1, MinTropical.trop ((-1 : ℤ) : WithTop ℤ))], true, (0, [], [])⟩

/-- What the row actually carries: `trop (-1) ⊗ trop (-1) = trop (-2)`,
the annotation of the one world that keeps both matches. -/
theorem MinTropicalZ.existsToken_predProvScalar :
    MinTropicalZ.existsToken.predProvScalar CompOp.ne 0
      = MinTropical.trop ((-2 : ℤ) : WithTop ℤ) := by decide

/-- What the absorptive collapse would give: the `⊕`-sum of the matches'
annotations, `trop (-1) ⊕ trop (-1) = trop (-1)`. -/
theorem MinTropicalZ.existsToken_sum :
    ∑ i, MinTropicalZ.existsToken.anns i
      = MinTropical.trop ((-1 : ℤ) : WithTop ℤ) := by decide

/-- **`WHERE EXISTS` is not "times the sum of the witnesses" outside
absorptivity.** The two differ by a whole `trop (-1)`: the row is read as
asking that *every* match be present, not that at least one is. -/
theorem MinTropicalZ.existsToken_ne_sum :
    MinTropicalZ.existsToken.predProvScalar CompOp.ne 0
      ≠ ∑ i, MinTropicalZ.existsToken.anns i := by decide

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
def natCountToken : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 1), (1, 2)], true, (0, [], [])⟩

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
def natRangeToken : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 2)], true, (0, [], [])⟩

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

/-- The joint reading is the one a truncation asks for. -/
theorem natRangeToken_and :
    natRangeToken.predProvOfAnd CompOp.gt 0 CompOp.le 1 = 2 := by decide

/-- The product is not. -/
theorem natRangeToken_mul :
    natRangeToken.predProvOf CompOp.gt 0
      * natRangeToken.predProvOf CompOp.le 1 = 4 := by decide

/-- The same token with its occurrence annotated `𝟙` agrees. -/
def natUnitToken : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 1)], true, (0, [], [])⟩

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
def boolTokenT : AggValue ℕ Bool := ⟨SeqAggFunc.count, [(1, true)], false, (0, [], [])⟩

/-- One occurrence, absent. -/
def boolTokenF : AggValue ℕ Bool := ⟨SeqAggFunc.count, [(1, false)], false, (0, [], [])⟩

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
def natTokenOne : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 1)], false, (0, [], [])⟩

/-- One occurrence of multiplicity `2`. -/
def natTokenTwo : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 2)], false, (0, [], [])⟩

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
  occs := [(![1, 1], 1, ![true, false], ![true, true]),
    (![1, 1], 1, ![false, true], ![true, true])]
  aggs := ![SeqAggFunc.count, SeqAggFunc.count]
  scalar := ![false, false]
  fam := (0, [], [])
  g := fun v => if 1 ≤ v 0 ∨ 1 ≤ v 1 then 1 else 0

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
  occs := [(![1, 1, 1], 1, ![true, false, false], ![true, true, true]),
    (![1, 1, 1], 1, ![false, true, false], ![true, true, true]),
    (![1, 1, 1], 2, ![false, false, true], ![true, true, true])]
  aggs := ![SeqAggFunc.count, SeqAggFunc.count, SeqAggFunc.count]
  scalar := ![false, false, false]
  fam := (0, [], [])
  g := fun v => if 1 ≤ v 0 then v 1 else v 2

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
only restore it where `δ` *is* the identity, which `𝔹`, `𝔹[X]`, interval
union and min-max have (`delta := id` in each instance) and `ChainFive`,
`ℕ`, `ℕ[X]`, `Lin[X]`, `Why[X]`, the tropical semirings, Viterbi and
Łukasiewicz do not.

Min-max is the instructive one: `δ = id` and `⊕` idempotent are *not*
sufficient either, since it is not exclusive and so not a Boolean
algebra, and whether the row is exact there beyond two singleton
families is open. What is settled is the Boolean case – see
`AggValue.row_agree_of_delta_id` for `𝔹[X]` at every family size. -/

/-- One occurrence annotated `hi`, grouped. -/
def chainTokenHi : AggValue ℕ ChainFive :=
  ⟨SeqAggFunc.count, [(1, ChainFive.hi)], false, (0, [], [])⟩

/-- One occurrence annotated `mid`, grouped. -/
def chainTokenMid : AggValue ℕ ChainFive :=
  ⟨SeqAggFunc.count, [(1, ChainFive.mid)], false, (0, [], [])⟩

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

/-- One occurrence annotated `α`, grouped. -/
def boolTokenOf (α : Bool) : AggValue ℕ Bool :=
  ⟨SeqAggFunc.count, [(1, α)], false, (0, [], [])⟩

/-- **The same agreement as an equation in the annotations**, at this
family shape: for *every* pair of annotations, not just the pair `true`,
`false` that `bool_row_agree` fixes.

The distinction is what decides whether the fact transfers. Both sides
are, at a fixed shape and fixed tests, terms in the annotation variables
over `⊕`, `⊗`, `⊖` and `δ`; where `δ` is the identity those are terms of
the Boolean-algebra signature, so an equation between them that holds
over `𝔹` holds in every Boolean algebra, the two-element one generating
the variety. `bool_row_agree` is not such an equation – its annotations
are the two literals – so it transfers nothing by itself; this one does,
for this shape. What no statement here gives is the family shapes: both
are about two singleton grouped families, and an implementation that
exempts a semiring on the strength of this needs the equation for the
shapes it actually builds. -/
theorem bool_row_agree_all : ∀ α β : Bool,
    SemiringWithMonus.delta α * SemiringWithMonus.delta β
        * ((boolTokenOf α).predProvWith testNe
          + (boolTokenOf β).predProvWith testEq)
      = Having.jointPair (boolTokenOf α) (boolTokenOf β)
          (fun x y => (testNe x).or (testEq y)) := by decide

/-! ### A `FILTER` clause that keeps everything is observable

A filtered aggregate read over the occurrences the clause keeps – a *cut*
family – has to be read in the scalar convention, and the convention is
forced by the clause that keeps nothing: the family is then empty, so only
the empty world can carry the row SQL still emits for a group that exists.
(`AggValue.ofGroupWhen` was that reading; the library now reads a filtered
aggregate as an expression over the whole group.)

Where the clause keeps *everything*, the same recipe is not the unfiltered
reading. The empty world of the uncut family weighs `𝟙 ⊖ ⊕α`, and the
group's existence factor `δ(⊕α)` does not absorb it: `delta_absorb` needs
an occurrence to be present, which is exactly what the empty world denies.
So `HAVING count(*) FILTER (WHERE true) ≐ 0` reports a row that
`HAVING count(*) ≐ 0` rejects, in a semiring where `δ(a) ⊗ (𝟙 ⊖ a) ≠ 𝟘`.

`ChainFive` is such a semiring and `ℕ`, `𝔹` and `𝔹[X]` are not – there
`𝟙 ⊖ a` is `𝟘` wherever `δ(a)` is `𝟙` – which is why the instances above
did not show it. What the pair of readings would have to be to make a
trivially true clause a no-op is an occurrence that stays in the *family*
while the clause takes it out of what the aggregate *reads*: the worlds
and their annotations would then be the group's, as they are with no
clause, and the kept part of a non-empty world could still be empty.
`AggValue` cannot express that – its occurrence carries a value and an
annotation, and nothing else – while `AggExpr` can, which is what
`AggExpr`'s per-leaf `reads` flags are and why an occurrence no leaf reads
is allowed. -/

/-- `count = 0`, false on every non-empty world and true on the empty
one. -/
def testEq0 : ℕ → Kleene := fun v => CompOp.eq.eval3 v 0

/-- One row, annotated `mid`, aggregated by `count(*)`. -/
def chainCount : AggValue ℕ ChainFive :=
  ⟨SeqAggFunc.count, [(1, ChainFive.mid)], false, (0, [], [])⟩

/-- The same group under `FILTER (WHERE true)`: the same occurrences, read
in the scalar convention. The two tokens differ in nothing else, the
clause keeping every occurrence. -/
def chainCountWhen : AggValue ℕ ChainFive :=
  ⟨SeqAggFunc.count, [(1, ChainFive.mid)], true, (0, [], [])⟩

/-- The first is the token the grouping builds with no clause, and the
second is what reading the cut family in the scalar convention gave. -/
theorem chainCount_eq_ofGroup :
    chainCount = AggValue.ofGroup (c := 0) SeqAggFunc.count
      (TermIn.index 0) [(![1], ChainFive.mid)] := rfl

theorem chainCountWhen_eq_scalar :
    chainCountWhen = { chainCount with scalar := true } := rfl

/-- **`HAVING count(*) ≐ 0` rejects the row** of a group the data leaves
non-empty: no world of a grouped token is empty. -/
theorem chain_count_zero :
    SemiringWithMonus.delta ChainFive.mid * chainCount.predProvOfWith testEq0
      = 0 := by decide

/-- **Under `FILTER (WHERE true)` the same test reports it**, and with
`𝟙`: the empty world is a world of the filtered token, and the group's
existence factor does not absorb its weight. -/
theorem chain_count_zero_when :
    SemiringWithMonus.delta ChainFive.mid
        * chainCountWhen.predProvOfWith testEq0
      = 1 := by decide

/-- So a clause that keeps everything is not the unfiltered reading. -/
theorem chain_count_zero_when_ne :
    SemiringWithMonus.delta ChainFive.mid
        * chainCountWhen.predProvOfWith testEq0
      ≠ SemiringWithMonus.delta ChainFive.mid
        * chainCount.predProvOfWith testEq0 := by decide

/-- The root of it, as an identity about the semiring: the existence
factor does not absorb the empty world's weight. -/
theorem chain_delta_not_absorb_empty :
    SemiringWithMonus.delta ChainFive.mid * (1 - ChainFive.mid) = 1 := by
  decide

/-- Over `ℕ` it does, for every annotation a non-empty group can carry,
which is why a numeric instance shows nothing here. -/
theorem nat_delta_absorb_empty (a : ℕ) :
    SemiringWithMonus.delta a * (1 - a) = 0 := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; rfl
  · show (if a = 0 then 0 else 1) * (1 - a) = 0
    rw [show (if a = 0 then (0 : ℕ) else 1) = 1 from by
      simp [Nat.pos_iff_ne_zero.mp h], one_mul]
    exact Nat.sub_eq_zero_of_le h

/-! ### What the two flag families give instead

`AggExpr` carries the group and the clause apart (`AggExpr.inFrame`,
`AggExpr.reads`), which is what a filtered aggregate needs: the worlds
are the group's, every occurrence carrying its annotation to them, and
the clause says what the leaf aggregates there. The three readings below
are the ones the cut family gets wrong, in the semiring that shows it.

A clause that keeps everything needs no test: its flags are the ones no
clause gives, so the expression *is* the unfiltered one. -/

/-- The group of `chainCount` read as a one-leaf aggregate expression:
one occurrence annotated `mid`, in the leaf's group and read by it. -/
def chainExpr : AggExpr ℕ ChainFive where
  arity := 1
  occs := [(![1], ChainFive.mid, ![true], ![true])]
  aggs := ![SeqAggFunc.count]
  scalar := ![false]
  fam := (0, [], [])
  g := fun v => v 0

/-- The same under `FILTER (WHERE false)`: the occurrence stays in the
group and leaves what the leaf reads. -/
def chainExprNone : AggExpr ℕ ChainFive where
  arity := 1
  occs := [(![1], ChainFive.mid, ![true], ![false])]
  aggs := ![SeqAggFunc.count]
  scalar := ![false]
  fam := (0, [], [])
  g := fun v => v 0

/-- Two occurrences, annotated `mid` and `hi`, the clause keeping the
first: `count(*) FILTER (WHERE φ)` where `φ` holds of one row of two. -/
def chainExprMixed : AggExpr ℕ ChainFive where
  arity := 1
  occs := [(![1], ChainFive.mid, ![true], ![true]),
    (![1], ChainFive.hi, ![true], ![false])]
  aggs := ![SeqAggFunc.count]
  scalar := ![false]
  fam := (0, [], [])
  g := fun v => v 0

/-- **`HAVING count(*) ≐ 0` still rejects the row**, as it does for the
token: no world of a grouped leaf is empty. -/
theorem chainExpr_zero : chainExpr.predProvWith testEq0 = 0 := by decide

/-- **Under `FILTER (WHERE false)` the row is reported with the group's
own weight** – `mid`, the annotation of the occurrence that makes the
group exist – and not with `𝟙`, which is what the cut family gives
(`chain_count_zero_when`). SQL emits that row, with `0`. -/
theorem chainExprNone_zero :
    chainExprNone.predProvWith testEq0 = ChainFive.mid := by decide

/-- **And a clause that keeps some of the group reports exactly the
worlds in which it keeps none of the present rows**: `hi ⊗ (𝟙 ⊖ mid)`,
the world holding the rejected occurrence alone. The cut family cannot
express that world at all. -/
theorem chainExprMixed_zero :
    chainExprMixed.predProvWith testEq0
      = ChainFive.hi * (1 - ChainFive.mid) := by decide

/-- Which is `hi` here, so the reading is not `𝟘` either. -/
theorem chainExprMixed_zero_eq : chainExprMixed.predProvWith testEq0
    = ChainFive.hi := by decide

/-! ### What a filtered window reads, and what `DISTINCT` decides

A window's clause cuts what its leaf reads of the frame, exactly as a
grouping's does, so the readings below are the window's counterpart of
the three above. The last pair records the choice `DISTINCT` forces: the
classes of the kept part carry the `⊕` of their occurrences, which is
what a `DISTINCT` aggregate *is*, being defined through `ε`, and not a
deduplication inside each world. The two differ, and `ℕ` shows
it. -/

/-- The family a filtered window builds over a frame of two rows, the
clause keeping the first: `AggExpr.ofSeqWhen`'s, with the frame flag on
both and the clause flag on the first alone. -/
def chainWinMixed : AggExpr ℕ ChainFive where
  arity := 1
  occs := [(![1], ChainFive.mid, ![true], ![true]),
    (![2], ChainFive.hi, ![true], ![false])]
  aggs := ![SeqAggFunc.count]
  scalar := ![false]
  fam := (0, [], [])
  g := fun v => v 0

/-- **The clause keeping one row of the frame reports the worlds holding
none of the kept ones**: `hi ⊗ (𝟙 ⊖ mid)`, the world with the rejected
row alone – which is a world of the frame that a cut family loses. -/
theorem chainWinMixed_zero :
    chainWinMixed.predProvWith testEq0
      = ChainFive.hi * (1 - ChainFive.mid) := by decide

/-- **The merge of two kept occurrences of equal value is one class
carrying their `⊕`.** This is what `AggExpr.ofSeqDistWhen` puts in the
family, and what makes the two readings below differ. -/
theorem mergeOccs_two :
    AggValue.mergeOccs [((5 : ℕ), (1 : ℕ)), (5, 1)] = [(5, 2)] := by
  simp [AggValue.mergeOccs, AggValue.classSum, List.dedup_cons_of_mem]
  rfl

/-- `count(DISTINCT x) FILTER (WHERE true) OVER (w)` over two occurrences
of equal value annotated `𝟙`: by `mergeOccs_two` the family is the one
class annotated `2`. -/
def natWinDistinct : AggExpr ℕ ℕ where
  arity := 1
  occs := [(![5], 2, ![true], ![true])]
  aggs := ![SeqAggFunc.count]
  scalar := ![false]
  fam := (0, [], [])
  g := fun v => v 0

/-- **A distinct count is the length of the deduplicated sequence.**
`SeqAggFunc.distinct` sorts the distinct values, and a count does not read
the order, so the two are the same aggregate. -/
theorem count_distinct_eq_dedup_length :
    SeqAggFunc.count.distinct = fun l : List ℕ => (List.dedup l).length := by
  funext l
  show (sortList ((l.dedup : Multiset ℕ))).length = _
  rw [length_sortList]
  rfl

/-- The same data read **without the merge**, the leaf deduplicating
inside each world instead: the family is one occurrence per row and the
aggregate is `count^distinct` (`count_distinct_eq_dedup_length`). This is
the reading the merge was chosen against. -/
def natWinUnmerged : AggExpr ℕ ℕ where
  arity := 1
  occs := [(![5], 1, ![true], ![true]), (![5], 1, ![true], ![true])]
  aggs := ![fun l => (List.dedup l).length]
  scalar := ![false]
  fam := (0, [], [])
  g := fun v => v 0

/-- **The merge counts the class once, with the `⊕` of its
occurrences**: `𝟙 ⊕ 𝟙 = 2` over `ℕ`. -/
theorem natWinDistinct_one : natWinDistinct.predProvWith testEq1 = 2 := by
  decide

/-- **Deduplicating in the reading gives `𝟙` instead**: the two
one-occurrence worlds weigh `𝟙 ⊗ (𝟙 ⊖ 𝟙) = 𝟘`, and only the full world
weighs anything – where the two equal values are one distinct value, so
the test holds there too. -/
theorem natWinUnmerged_one : natWinUnmerged.predProvWith testEq1 = 1 := by
  decide

/-- So the two readings of a `DISTINCT` aggregate are different
provenances – `2` against `𝟙` – and the merge is the one `ε` defines. -/
theorem natWinDistinct_ne_unmerged :
    natWinDistinct.predProvWith testEq1
      ≠ natWinUnmerged.predProvWith testEq1 := by decide

/-! ### An aggregation's `ORDER BY` is not decoration

`AggQueryIn.Gamma` and `GammaScalar` carry a `GroupOrder`: their
aggregates read the group in that clause's order
(`Relation.groupSeqOrd`, `Having.havingGroupOrd`) rather than in the
domain's canonical one. For a symmetric aggregate that changes nothing,
which is why `count` and `sum` never needed it; for an order-dependent
one it does, so the clause is the aggregate's own and not an order the
library could pick for it. The two rows below differ in the column the
clause reads, and `first_value` of that column comes out `2` under the
clause against `1` without it. -/

/-- Two rows of one group, differing in the column the clause reads. -/
def ordGroupRel : Relation ℕ 2 := Multiset.ofList [![0, 1], ![0, 2]]

/-- `ORDER BY #1 DESC` inside the aggregate. -/
def ordByDesc : GroupOrder ℕ 2 := GroupOrder.byCols ![1] ![OrderCol.DESC]

/-- The whole relation as one group. -/
abbrev noKey : Tuple (Fin 2) 0 := fun k => k.elim0

/-- Under the clause the aggregate reads the larger value first. -/
theorem groupSeqOrd_pickFirst :
    (SeqAggFunc.pickFirst ((Relation.groupSeqOrd noKey ordByDesc ordGroupRel
        (fun k : Fin 0 => k.elim0)).map (fun u => u 1)) : ℕ) = 2 := by decide

/-- Without it, in the domain's canonical order, it reads the smaller. -/
theorem groupSeq_pickFirst :
    (SeqAggFunc.pickFirst ((Relation.groupSeqOrd noKey GroupOrder.unord
        ordGroupRel (fun k : Fin 0 => k.elim0)).map (fun u => u 1)) : ℕ)
      = 1 := by decide

theorem groupSeqOrd_ne_groupSeq :
    (SeqAggFunc.pickFirst ((Relation.groupSeqOrd noKey ordByDesc ordGroupRel
        (fun k : Fin 0 => k.elim0)).map (fun u => u 1)) : ℕ)
      ≠ SeqAggFunc.pickFirst ((Relation.groupSeqOrd noKey GroupOrder.unord
          ordGroupRel (fun k : Fin 0 => k.elim0)).map (fun u => u 1)) := by
  rw [groupSeqOrd_pickFirst, groupSeq_pickFirst]
  decide

/-! ### A window may not read an aggregate column of its input

`AggQueryIn.Win` takes any input kinds, and reads its input through
`ColKind.readTuple`: the regular columns, and nothing of the aggregate
ones – not even to break a tie in the `ORDER BY`. This is why the second
half is needed and `WinReadsReg` alone would not do. The two relations
below hold the same regular columns row for row and differ only in the
middle column, an aggregate one; read *whole*, the determinized peer
order (`OrderSpec.readLe`, whose ties are broken by the row) puts a
different row first, and `first_value` of the regular column the window
does read comes out `2` on one and `1` on the other. An aggregate
column's value is what its token reads in a world, so a window reading
its input whole would order two peers one way in one world and the other
way in the next, and its column would not read in a world what the plain
window reads of that world. -/

/-- Three columns: a key the `ORDER BY` reads, an aggregate column, and
the value the aggregate reads. -/
def peerKinds : Fin 3 → ColKind := ![ColKind.reg, ColKind.agg, ColKind.reg]

/-- Two rows the `ORDER BY` leaves tied, with an aggregate column whose
deterministic reading is `5` and `3`. -/
def peerRelDet : Relation ℕ 3 :=
  Multiset.ofList [![0, 5, 1], ![0, 3, 2]]

/-- The same two rows in a world where that column reads `1` and `9`:
the same regular columns, row for row. -/
def peerRelWorld : Relation ℕ 3 :=
  Multiset.ofList [![0, 1, 1], ![0, 9, 2]]

/-- What a window reads of the two is the same relation. -/
theorem peerRel_readTuple_eq :
    peerRelDet.map (ColKind.readTuple peerKinds)
      = peerRelWorld.map (ColKind.readTuple peerKinds) := by decide

/-- Yet read whole they give `first_value` different values, which is
why the reading cuts the aggregate column out. -/
theorem windowValue_ne_of_agg_column :
    (ValueFrame.windowValue (fun k : Fin 0 => k.elim0) ![0] (OrderSpec.asc 1)
        ValueFrame.whole (TermIn.index (c := 0) 2) SeqAggFunc.pickFirst peerRelDet
        ![0, 5, 1] : ℕ)
      ≠ (ValueFrame.windowValue (fun k : Fin 0 => k.elim0) ![0]
          (OrderSpec.asc 1) ValueFrame.whole (TermIn.index (c := 0) 2)
          SeqAggFunc.pickFirst peerRelWorld ![0, 1, 1] : ℕ) := by decide

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
def boolScalarT : AggValue ℕ Bool := ⟨SeqAggFunc.count, [(1, true)], true, (0, [], [])⟩

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
def natScalarOne : AggValue ℕ ℕ := ⟨SeqAggFunc.count, [(1, 1)], true, (0, [], [])⟩

theorem nat_incl_excl_eq :
    Having.jointPair natScalarOne natScalarOne
        (fun x y => (testGe1 x).or (testGe1 y))
      = natScalarOne.predProvOfWith testGe1 + natScalarOne.predProvOfWith testGe1
          - natScalarOne.predProvOfWith testGe1 * natScalarOne.predProvOfWith testGe1 := by
  decide

/-! ### `jointPair` reads two families as *disjoint*

`Having.jointPair` sums over the worlds of the concatenation of the two
occurrence families, so it reads them as independent. That is the joint
reading when the families genuinely are disjoint – two columns coming
from two different groupings – and it is *not* the joint reading when
they coincide. Two aggregates of one group are one family
(`AggValue.annList_ofGroup`), and reading them as two independent ones
counts a world once per half: over `ℕ`, `4` where the one-family
reading gives `2`. So a conjunction of tests on two aggregate columns
is the column-by-column product exactly where the columns come from
different groupings, and parts from it where they come from one – the
same `4` against `2` that separates a chain of selections from one
selection on the conjunction. -/

/-- `count > 0`, on the range token's worlds. -/
def testGt0 : ℕ → Kleene := fun v => CompOp.gt.eval3 v 0

/-- `count ≤ 1`. -/
def testLe1 : ℕ → Kleene := fun v => CompOp.le.eval3 v 1

/-- **Read as two disjoint families, one family is counted twice.** -/
theorem natRange_jointPair_self :
    Having.jointPair natRangeToken natRangeToken
        (fun x y => (testGt0 x).and (testLe1 y)) = 4 := by decide

/-- The one-family reading of the same conjunction is `2`. -/
theorem natRange_jointPair_ne :
    Having.jointPair natRangeToken natRangeToken
        (fun x y => (testGt0 x).and (testLe1 y))
      ≠ natRangeToken.predProvOfAnd CompOp.gt 0 CompOp.le 1 := by decide

/-! ### Min-max: `δ = id` with no exclusivity, and the row still absorbs

`ChainFive` shows an idempotent `⊕` is not what makes the existence
factors absorb the `∨` rule's difference (`chain_row_ne`); `δ = id` is
necessary, by the identity `a ⊗ δ(b) = a ⊗ b` at `a = 𝟙`. Min-max has
`δ = id` and is *not* exclusive, which is the one place in the catalog
where the two roads to killing an invented world both fail – so whether
it keeps the row-level absorption is exactly whether `δ = id` suffices.
It does, here: `⊗` is `max` and `⊕` is `min`, so
`max(a, b, min(a, b)) = max(a, b)` and the reported row is the joint
one, in each configuration of the two tests. -/

/-- The three-element min-max semiring, `δ` the identity. -/
abbrev MM3 := MinMax (Fin 3)

/-- One occurrence, graded. -/
def mmTokenA : AggValue ℕ MM3 :=
  ⟨SeqAggFunc.count, [(1, MinMax.mk (1 : Fin 3))], false, (0, [], [])⟩

/-- Another, graded differently. -/
def mmTokenB : AggValue ℕ MM3 :=
  ⟨SeqAggFunc.count, [(1, MinMax.mk (2 : Fin 3))], false, (0, [], [])⟩

/-- **One test satisfied**: the configuration `ChainFive` parts on. -/
theorem mm_row_agree_one :
    SemiringWithMonus.delta (MinMax.mk (1 : Fin 3)) * SemiringWithMonus.delta (MinMax.mk (2 : Fin 3))
        * (mmTokenA.predProvWith testGe1 + mmTokenB.predProvWith testGe2)
      = Having.jointPair mmTokenA mmTokenB
          (fun x y => (testGe1 x).or (testGe2 y)) := by decide

/-- **Both satisfied**, where the overlap would be counted twice were
`⊕` not idempotent. -/
theorem mm_row_agree_both :
    SemiringWithMonus.delta (MinMax.mk (1 : Fin 3)) * SemiringWithMonus.delta (MinMax.mk (2 : Fin 3))
        * (mmTokenA.predProvWith testGe1 + mmTokenB.predProvWith testGe1)
      = Having.jointPair mmTokenA mmTokenB
          (fun x y => (testGe1 x).or (testGe1 y)) := by decide

/-- **Neither satisfied.** -/
theorem mm_row_agree_neither :
    SemiringWithMonus.delta (MinMax.mk (1 : Fin 3)) * SemiringWithMonus.delta (MinMax.mk (2 : Fin 3))
        * (mmTokenA.predProvWith testGe2 + mmTokenB.predProvWith testGe2)
      = Having.jointPair mmTokenA mmTokenB
          (fun x y => (testGe2 x).or (testGe2 y)) := by decide

/-! ### An aggregate over an inner grouping's aggregates: min-max invents a world

A nested aggregate's worlds range over the occurrences of the outer
family *and* those of the inner values, so a world may keep an inner
occurrence of an outer occurrence it drops – a combination of rows the
inner grouping could not have produced. Such a world carries
`(⊗ over what it keeps) ⊗ (𝟙 ⊖ α)` for the dropped outer occurrence's
annotation `α`, so it dies exactly where that product is `𝟘`.

Over `ℕ` it dies: `α = 𝟙` and `𝟙 ⊖ 𝟙 = 𝟘`. Over min-max it does not:
`𝟙` is `⊥`, and `⊥ ⊖ g = ⊥ = 𝟙` for any grade `g ≠ 𝟙`, so the
complement factor is `𝟙` and the invented world keeps the weight of the
rows it does hold. That is the one row of the catalog where neither
road – an exclusive `⊕` nor a `δ` saturating to `𝟙` – is open. -/

/-- Two outer occurrences, each carrying a one-occurrence inner
family. -/
abbrev nestOf {K : Type} [CommSemiringWithMonus K] (α₀ α₁ β₀ β₁ : K) :
    NestedValue ℕ K :=
  ⟨SeqAggFunc.count.onBag SeqAggFunc.count_symmetric,
    {(AggExpr.ofValue ⟨SeqAggFunc.count, [(1, β₀)], false, (0, [], [])⟩, α₀),
     (AggExpr.ofValue ⟨SeqAggFunc.count, [(1, β₁)], false, (0, [], [])⟩, α₁)},
    false, (0, [], [])⟩

/-- **The invented world**: it keeps the first outer occurrence and an
inner occurrence of the second, which it drops. -/
abbrev incoherentWorld {K : Type} [CommSemiringWithMonus K]
    (α₀ α₁ β₀ β₁ : K) : NestedValue.World ℕ K :=
  ⟨{⟨(AggExpr.ofValue ⟨SeqAggFunc.count, [(1, β₀)], false, (0, [], [])⟩, α₀),
      true, Finset.univ⟩,
    ⟨(AggExpr.ofValue ⟨SeqAggFunc.count, [(1, β₁)], false, (0, [], [])⟩, α₁),
      false, Finset.univ⟩}⟩

/-- It decides on exactly the occurrences of `nestOf`. -/
theorem isWorldOf_incoherentWorld {K : Type} [CommSemiringWithMonus K]
    (α₀ α₁ β₀ β₁ : K) :
    (incoherentWorld α₀ α₁ β₀ β₁).IsWorldOf (nestOf α₀ α₁ β₀ β₁) := rfl

/-- **It is a world of the nested reading** – an occurrence is kept with
its inner family met – and it is barred by the coherent reading, which is
what makes it the world at issue. -/
theorem isWorld_incoherentWorld {K : Type} [CommSemiringWithMonus K]
    (α₀ α₁ β₀ β₁ : K) :
    (incoherentWorld α₀ α₁ β₀ β₁).IsWorld (nestOf α₀ α₁ β₀ β₁)
      ∧ ¬ (incoherentWorld α₀ α₁ β₀ β₁).IsWorldCoherent
        (nestOf α₀ α₁ β₀ β₁) := by
  have hcard : 0 < (incoherentWorld α₀ α₁ β₀ β₁).kept.card := by
    show 0 < Multiset.card (Multiset.filter _ _)
    rw [show Multiset.filter
        (fun d : NestedValue.WorldOcc ℕ K => d.present = true)
        (incoherentWorld α₀ α₁ β₀ β₁).occs
      = {⟨(AggExpr.ofValue ⟨SeqAggFunc.count, [(1, β₀)], false, (0, [], [])⟩, α₀),
          true, Finset.univ⟩}
      from rfl]
    simp
  refine ⟨⟨Or.inr hcard, fun d hd _ => ?_, trivial⟩, fun hco => ?_⟩
  · have hdd : d = ⟨(AggExpr.ofValue ⟨SeqAggFunc.count, [(1, β₀)], false, (0, [], [])⟩, α₀),
          true, Finset.univ⟩
        ∨ d = ⟨(AggExpr.ofValue ⟨SeqAggFunc.count, [(1, β₁)], false, (0, [], [])⟩, α₁),
          false, Finset.univ⟩ := by
      simpa using hd
    -- each inner reading is a one-occurrence token's expression, and the
    -- world keeps that occurrence
    rcases hdd with rfl | rfl <;>
      exact fun j _ => ⟨⟨0, by simp [AggExpr.ofValue]⟩, by
        simp [AggExpr.inFrame, AggExpr.ofValue]⟩
  · have := hco.2.2 ⟨(AggExpr.ofValue ⟨SeqAggFunc.count, [(1, β₁)], false, (0, [], [])⟩, α₁),
      false, Finset.univ⟩ (by simp) rfl
    -- the dropped occurrence keeps its one inner occurrence, so its
    -- subfamily is not empty
    have hne : (⟨0, by simp [AggExpr.ofValue]⟩
        : Fin (AggExpr.ofValue
          (⟨SeqAggFunc.count, [(1, β₁)], false, (0, [], [])⟩ : AggValue ℕ K)).occs.length)
      ∈ (⟨(AggExpr.ofValue ⟨SeqAggFunc.count, [(1, β₁)], false, (0, [], [])⟩, α₁),
          false, Finset.univ⟩ : NestedValue.WorldOcc ℕ K).sub :=
      Finset.mem_univ _
    rw [this] at hne
    exact absurd hne (Finset.notMem_empty _)

/-- **Over `ℕ` the invented world is annotated `𝟘`.** -/
theorem nat_incoherentWorld_eq_zero :
    (incoherentWorld (1 : ℕ) 1 1 1).ann = 0 := by decide

/-- **Over min-max it is not**: the complement factor is `𝟙`, so the
world keeps the weight of the rows it holds. -/
theorem mm_incoherentWorld_ne_zero :
    (incoherentWorld (MinMax.mk (1 : Fin 3)) (MinMax.mk 1)
      (MinMax.mk 1) (MinMax.mk 1)).ann ≠ 0 := by decide

/-! ## Complementedness is not an m-semiring identity

Every semiring of the catalog is complemented (`complemented`'s
docstring lists the eleven proofs), which is why the hypothesis the
nested homomorphism commutation carries excludes nothing anyone computes
in. It is not, however, a consequence of the axioms: the non-negative
rationals with truncated subtraction are an m-semiring and fail the law
at `a = b = ½`. They are not a provenance semiring – ordinary
multiplication is not `⊗` of any provenance reading – which is what the
counterexample needs them not to be. -/

/-- The non-negative reals with truncated subtraction: an m-semiring,
with the indicator `δ`. The non-negative rationals refute the law just as
well; `ℝ≥0` is the carrier this development already has at hand
(Viterbi's), so the law is refuted over it. -/
noncomputable instance NNReal.instSemiringWithMonus :
    SemiringWithMonus NNReal :=
  { (inferInstance : Semiring NNReal), (inferInstance : PartialOrder NNReal),
    (inferInstance : IsOrderedAddMonoid NNReal),
    (inferInstance : CanonicallyOrderedAdd NNReal),
    (inferInstance : Sub NNReal) with
    monus_spec := fun _ _ _ => tsub_le_iff_left
    delta := fun a => if a = 0 then 0 else 1
    delta_zero := by simp
    delta_natCast_pos := by
      intro n hn
      have hne : ((n : NNReal)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp [hne]
    delta_absorb := by
      intro a b
      by_cases h : a + b = 0
      · have ha : a = 0 := (add_eq_zero.mp h).1
        simp [ha]
      · simp [h] }

/-- **Complementedness is not an m-semiring identity**: over the
non-negative reals it fails at `a = b = ½`, where the left side is
`𝟙 ⊖ 𝟙 = 𝟘` and the right side is `½ ⊗ ½ = ¼`. Every semiring of the
catalog satisfies it (see `complemented`'s docstring), so the hypothesis
the nested homomorphism commutation carries excludes nothing anyone
computes in – but it is a hypothesis and not a theorem. -/
theorem nnreal_not_complemented : ¬ complemented NNReal := by
  intro h
  have h2 := h (1 / 2) (1 / 2)
  have hsum : ((1 : NNReal) / 2 + (1 : NNReal) / 2 : NNReal) = 1 := by
    norm_num
  have hhalf : ((1 : NNReal) - (1 : NNReal) / 2 : NNReal) = (1 : NNReal) / 2 := by
    rw [tsub_eq_iff_eq_add_of_le
      (by norm_num : ((1 : NNReal) / 2 : NNReal) ≤ 1)]
    norm_num
  rw [hsum, tsub_self, hhalf] at h2
  norm_num at h2

/-! ## The coherent reading of a nested world is not a convention

`q:nestedcoherent` asks whether a world of a nested value may keep an
inner occurrence of an outer occurrence it drops. The library's
`NestedValue.World.IsWorld` allows it; `IsWorldCoherent` forbids it. It
would be tempting to close the question by showing the two readings agree
wherever anyone computes – in a Boolean algebra with `δ = id` – and the
argument for that is: an incoherent world keeps an inner `α` while the
outer occurrence's own `β` sits in the monus, so the weight is
`α ⊗ (𝟙 ⊖ (β ⊕ …))`, which exclusivity kills *if* `α ≤ β`.

**Nothing makes `α ≤ β`.** An occurrence's outer annotation and its inner
family's annotations are independent fields, and the evaluator can build
a row whose annotation is `𝟘` while its aggregate column has a realized
occurrence – a selection with an aggregate atom keeps its failing rows
annotated `𝟘`. Over `𝔹`, the two readings then differ: the incoherent
world weighs `⊤ ⊗ (𝟙 ⊖ 𝟘) = ⊤`, so the current reading reports `⊤` where
the coherent one reports `𝟘`. The question is therefore a choice about
the semantics and not a convention that the catalog's semirings make
invisible. -/

/-- An inner expression with one occurrence annotated `α`, grouped. -/
def nestedInner (α : Bool) : AggExpr ℕ Bool :=
  { arity := 1
    occs := [((fun _ => 1), α, (fun _ => true), (fun _ => true))]
    aggs := fun _ => SeqAggFunc.count
    scalar := fun _ => false
    g := fun v => v 0 
    fam := (0, [], []) }

/-- Two outer occurrences, grouped: one annotated `⊤`, one annotated `𝟘`,
each carrying an inner occurrence annotated `⊤`. The second is the row a
selection keeps annotated `𝟘` whose aggregate column is still realized. -/
def nestedIncoherentWitness : NestedValue ℕ Bool :=
  { agg := fun s => s.card
    occs := {(nestedInner true, true), (nestedInner true, false)}
    scalar := false 
    fam := (0, [], []) }

/-- **The current reading admits five worlds, the coherent reading
three.** -/
theorem nestedIncoherentWitness_world_counts :
    (Multiset.card (nestedIncoherentWitness.worlds.filter
        (fun W => W.IsWorld nestedIncoherentWitness)),
      Multiset.card (nestedIncoherentWitness.worlds.filter
        (fun W => W.IsWorld nestedIncoherentWitness
          ∧ ∀ d ∈ W.occs, d.present = false → d.sub = ∅)))
      = (5, 3) := by decide

/-- **And they weigh the row differently over `𝔹`**: `⊤` against `𝟘`. So
`q:nestedcoherent` is not settled by `δ = id` with exclusivity, and the
two readings are not interchangeable in any semiring of the catalog. -/
theorem nestedIncoherent_ne_coherent :
    ((nestedIncoherentWitness.worlds.filter
        (fun W => W.IsWorld nestedIncoherentWitness)).map
      NestedValue.World.ann).sum
      ≠ ((nestedIncoherentWitness.worlds.filter
          (fun W => W.IsWorld nestedIncoherentWitness
            ∧ ∀ d ∈ W.occs, d.present = false → d.sub = ∅)).map
        NestedValue.World.ann).sum := by decide

/-- **The world a valuation realizes is this incoherent one**, which is
what settles the question rather than merely opening it: the realized
world sets an occurrence present exactly when the valuation makes its
*outer* annotation true, and keeps the inner occurrences the valuation
makes true, independently (`NestedValue.realizedOcc`). So where a
selection has brought a row's annotation to `𝟘` while its aggregate
column stays realized, the actual world keeps the inner occurrences of an
absent outer one. -/
theorem realizedWorld_not_coherent :
    ¬ (∀ d ∈ (nestedIncoherentWitness.realizedWorld id).occs,
        d.present = false → d.sub = ∅) := by decide

/-- **And the current reading admits it**, so it is the reading under
which the `𝔹`-sum is the indicator of the actual world. A reading that
forbade it would annotate this value `𝟘` where the world as it is holds
the row, which `NestedValue.World.ann_eval_iff` and the possible-world
results built on it would then contradict. -/
theorem realizedWorld_isWorld :
    (nestedIncoherentWitness.realizedWorld id).IsWorld
      nestedIncoherentWitness := by decide
