/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/

module -- shake: keep-all

/- Three-valued logic and value domains with a null -/
public import Provenance.Util.Kleene
public import Provenance.Util.ValueTypeNull

/- Queries on annotated relations -/
public import Provenance.QueryAnnotatedDatabase
public import Provenance.QueryAnnotatedDatabaseHom

/- Data-part adequacy of the annotated semantics -/
public import Provenance.QueryAdequacy

/- HAVING algebraic identities -/
public import Provenance.Having

/- Possible-world semantics of the fused Having operator -/
public import Provenance.HavingSemantics

/- Symbolic aggregate tokens for the general HAVING semantics -/
public import Provenance.AggValue
public import Provenance.AggExpr
public import Provenance.Nested
public import Provenance.JointFamily
public import Provenance.AggValueCongr
public import Provenance.SubWorlds

/- Kind-indexed general queries and their annotated semantics -/
public import Provenance.AggQuery
public import Provenance.AggQuerySubst
public import Provenance.ReadsCongr

/- Operators that abbreviate a query of the basis -/
public import Provenance.Derived
public import Provenance.DerivedAnn

/- The listing an aggregate reads, and the query that is refused -/
public import Provenance.Determinacy

/- Which operators a query cannot do without -/
public import Provenance.PlainBasis

/- An apply read as a product -/
public import Provenance.Decorrelate

/- Reading every column as a value -/
public import Provenance.AllRegular

/- The basis, assembled -/
public import Provenance.BasisAssembly
public import Provenance.RecursionBasis
public import Provenance.SumByMu
public import Provenance.WinKept
public import Provenance.RecursionBasisPass
public import Provenance.Genericity
public import Provenance.WinRow
public import Provenance.SelRow
public import Provenance.RoundBound
public import Provenance.AnnotatedBasis
public import Provenance.AnnotatedDedup
public import Provenance.AnnotatedProd
public import Provenance.AnnotatedSum
public import Provenance.PathSum
public import Provenance.AnnotatedMuUnion
public import Provenance.AnnotatedChains
public import Provenance.AnnotatedDiffRow
public import Provenance.AnnotatedEpsRow
public import Provenance.AnnotatedBasisClass
public import Provenance.AnnotatedBasisHom
public import Provenance.AnnotatedApproxRows
public import Provenance.AnnotatedWhyRow
public import Provenance.AnnotatedApplyRow
public import Provenance.MuUnion
public import Provenance.RecursionBasisTheorem
public import Provenance.SumByProd
public import Provenance.SymCode
public import Provenance.SymCells
public import Provenance.SymRel
public import Provenance.SymTerms
public import Provenance.SymOps
public import Provenance.SymGamma
public import Provenance.SymWin
public import Provenance.SymMu
public import Provenance.SymTab
public import Provenance.SymCorrect
public import Provenance.SymOrder
public import Provenance.SymEnvBuild
public import Provenance.SymCut
public import Provenance.SymSettle
public import Provenance.SymMatch
public import Provenance.SymApply
public import Provenance.SymStruct
public import Provenance.SymOver
public import Provenance.SymPass
public import Provenance.DiffBasis
public import Provenance.RecursionBases
public import Provenance.RecFreeBasis

/- Relations read as families of occurrences -/
public import Provenance.Occurrence

/- Window frames determined by values -/
public import Provenance.OrderSpec
public import Provenance.Frame

/- The window operator's token -/
public import Provenance.Window

/- Surface syntax for kind-indexed queries -/
public import Provenance.Notation

/- Data-part adequacy of the general evaluator -/
public import Provenance.AggQueryAdequacy

/- Regression bridges: the fused Having recovered from the general syntax -/
/- A window over a whole partition is a join with its grouping -/
public import Provenance.WindowPartition
public import Provenance.AggQueryBridges
public import Provenance.JointHom
public import Provenance.NestedPres
public import Provenance.Coherence
public import Provenance.Normalize
public import Provenance.Alternatives

/- Possible-world foundations for the general evaluator -/
public import Provenance.AggQueryProbability

/- Hom commutation for the general evaluator, token and annotation layer -/
public import Provenance.AggQueryHom
public import Provenance.QueryToAgg
public import Provenance.AggQueryEmbedding

/- Provenance-aware rewriting stated natively on the general syntax -/
public import Provenance.AggQueryRewriting
public import Provenance.AggQueryStrip
public import Provenance.AggQueryRewritingValid

/- The rewritten world's token-bearing evaluator (HAVING rewriting) -/
public import Provenance.AggQueryHavingRewriting

/- The bare-grouping rewriting: aggregate results as output values -/
public import Provenance.AggQueryGroupRewriting

/- Compositional closure of the rewriting rules -/
public import Provenance.AggQueryClosure

/- Scan-computable HAVING provenance for MIN, MAX and PICKFIRST -/
public import Provenance.HavingMinMax

/- Probability distributions over Boolean variables -/
public import Provenance.Probability

/- Support adequacy over 𝔹 and transfer along monus homomorphisms -/
public import Provenance.SupportAdequacy

/- Boolean circuits, read-once and d-D correctness -/
public import Provenance.Circuit

/- Categorical-block probability and deterministic-OR (mulinput) soundness -/
public import Provenance.CategoricalBlock

/- Probability identities for HAVING aggregate comparisons under independence -/
public import Provenance.HavingProbability

/- Worked examples: HAVING provenance collapse and Poisson-binomial probability -/
public import Provenance.HavingExample

/- Query-level correctness of the fused Having operator vs the JOIN rewriting -/
public import Provenance.HavingQueryCorrectness
public import Provenance.HavingJoinCompositional
public import Provenance.HavingMonotone

/- Query-level counterexamples for the HAVING / JOIN correspondence -/
public import Provenance.HavingQueryCounterexamples

/- Tseitin CNF encoding (equisatisfiability) -/
public import Provenance.Tseitin

/- Algorithms (HAVING enumeration) -/
public import Provenance.Algorithms.CountEnum
public import Provenance.Algorithms.SumDP

/- Complexity of the HAVING semantics -/
public import Provenance.HavingComplexity

/- Various semirings -/
public import Provenance.Semirings.BestPath
public import Provenance.Semirings.Bool
public import Provenance.Semirings.BoolFunc
public import Provenance.Semirings.ChainFive
public import Provenance.Semirings.How
public import Provenance.Semirings.IntervalUnion
public import Provenance.Semirings.Lukasiewicz
public import Provenance.Semirings.MinMax
public import Provenance.Semirings.Nat
public import Provenance.Semirings.Regex
public import Provenance.Semirings.Security
public import Provenance.Semirings.Tropical
public import Provenance.Semirings.TropicalPaths
public import Provenance.Semirings.Viterbi
public import Provenance.Semirings.Which
public import Provenance.Semirings.Why

/- Frozen restatements of the claims of published papers -/
public import Provenance.Papers.Icde2026

/- A worked query checked against ProvSQL's own answer -/
public import Provenance.ProvsqlExample

/- Example -/
public import Provenance.DistributionExample
public import Provenance.NestedExample
public import Provenance.Example
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Provenance in databases

This Lean 4 library provides formal definitions and proofs relevant for *provenance in
databases*, following the semiring framework of
[Green, Karvounarakis & Tannen][green2007provenance] and
[Green & Tannen][green2017provenance].

One of the goals of this library is to provide a formal, machine-checked semantics for
the provenance-aware relational database system
[ProvSQL](https://provsql.org/) described in
[Sen, Maniu & Senellart][sen2026provsql].

## Contents

**Core theory**

- `Provenance.SemiringWithMonus` – definition of a *semiring with monus* (m-semiring),
  the algebraic structure underlying annotated database semantics, together with general
  theorems about it
- `Provenance.Util.Kleene` – **Kleene's three-valued logic**: `Kleene` with
  its negation, conjunction and disjunction (the minimum and maximum of
  `false < unknown < true`). Every law of a De Morgan algebra holds; what
  fails is the excluded middle, and exactly at `unknown` – a row on which a
  predicate is unknown is selected by neither the predicate nor its
  negation, which no two-valued reading can imitate
- `Provenance.Util.ValueTypeNull` – **value domains with a null**:
  `ValueTypeNull` extends `ValueType` with a null distinct from the domain's
  zero and null-strict arithmetic, and `WithNull T` adjoins one value to any
  value type, strictness holding by construction. `CompOp.eval3` is the
  three-valued comparison, `unknown` as soon as an operand is null;
  `CompOp.eval3_eq_true_iff` recovers the two-valued reading away from the
  null, and `CompOp.negate_eval3` says the operator negator *is* the
  three-valued negation – unconditionally, since at the null both readings
  are `unknown` and Kleene negation fixes it. A comparison is `strict` when
  a null operand makes it unknown, which `CompOp.syneq` and `CompOp.synne` –
  SQL's `IS [NOT] DISTINCT FROM` – are not: they compare two values of the
  domain, two nulls being identical, and never return `unknown`
  (`CompOp.syneq_eval3_eq_true_iff`). That is the equality grouping,
  partitioning, duplicate elimination and difference use, and the one the
  rewritings join on
- `Provenance.Database` – tuples, relations, and plain databases
- `Provenance.Query` – relational algebra (select, project, join, union,
  difference…), with selections read in **Kleene's three-valued logic**:
  `BoolTerm.eval3` and `Selection.eval3` give the truth value, `eval` keeps
  the rows on which it is *true*, and a row on which a predicate is unknown
  is kept by neither the predicate nor its negation (`Selection.eval_not`).
  Where nothing is null the reading is two-valued
  (`Selection.eval3_ne_unknown`, `Selection.eval_not_iff`). Beside the six
  comparisons the language has `BoolTerm.SYNEQ` and `BoolTerm.SYNNE`,
  SQL's `IS [NOT] DISTINCT FROM`, the first written `≐`: they compare two
  values with two nulls identical, are never unknown, and are what a join
  on a key column needs. A term is an index or a constant combined by
  arithmetic, by SQL's searched `CASE` (`TermIn.caseWhen`, whose `ELSE`
  is a term, so that the constructor asks nothing of the value domain)
  and by `TermIn.coalesce`: with those two, a guard that is a Boolean
  combination of comparisons needs no more – a conjunction is a nested
  `CASE`, a disjunction a `COALESCE`, a negation `CompOp.negate`.
  Also the aggregate catalog `SeqAggFunc` and
  the two of SQL's three **input policies** that a null makes visible:
  `SeqAggFunc.sqlOf`, the *null-skipping* one (`SUM`, `MIN`, `MAX`, `AVG`),
  which drops the nulls and gives `NULL` when nothing is left, and
  `SeqAggFunc.counting`, the *counting* one (`COUNT(t)`), which drops them
  and gives `0` – the third, *null-keeping*, being the aggregate itself.
  `SeqAggFunc.Counts` says what it takes for an aggregate to count – never
  null, and zero exactly over nothing but nulls – and `counts_counting`
  supplies it from the counting policy over a plain count.
  `SeqAggFunc.count` is `COUNT(*)`, `COUNT` over a term that is never null,
  and needs neither. On a domain where nothing is null the counting policy
  is the count itself (`counting_of_noNulls`). That is what
  the scalar convention needed and could not have – an aggregation without
  grouping over an empty input, and a frame excluding the row it is computed
  for, both read their value there, and `SUM`, `MIN`, `MAX` over no row are
  `NULL` and not the zero the domain happened to offer. `COUNT` stays
  unwrapped, being the one aggregate SQL does not read that way, and
  `sqlOf_eq_of_no_null` recovers the results proved over a domain with no
  null. **Which aggregates read their input as a multiset** is settled by
  `SeqAggFunc.Symmetric`: `SUM`, `COUNT`, `MIN` and `MAX` are, `sqlOf`
  preserves it, and `PICKFIRST` is not (`not_symmetric_pickFirst`) – it is
  the aggregate for which the order a group or a frame is read in *is* the
  answer, and the reason the interface is a function on sequences at all
- `Provenance.AnnotatedDatabase` – databases annotated with values in an m-semiring `K`
- `Provenance.QueryAnnotatedDatabase` – semantics of relational algebra over annotated
  databases via m-semiring operations
- `Provenance.QueryAnnotatedDatabaseHom` – evaluation commutes with m-semiring
  homomorphisms ([Green, Karvounarakis & Tannen][green2007provenance],
  Proposition 3.5; [Geerts & Poggi][geerts2010database], Proposition 1)
- `Provenance.QueryAdequacy` – data-part adequacy of the annotated semantics:
  forgetting annotations turns annotated evaluation into plain evaluation of
  the difference-stripped query, exactly on the positive fragment (the
  annotation-generic analogue of the `ℕ`-adequacy theorem of
  [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini][benzaken2021coq])
  and as a sub-multiset inclusion in general
**The general framework** (primary)

The kind-indexed general syntax is the library's primary query
framework. Its three column kinds – regular values, aggregate tokens,
provenance values – mirror the three data types through which ProvSQL
enforces its own discipline (regular SQL values, `agg_token`, uuid), so
the system's scope restrictions on aggregate results (no deduplication,
difference or re-grouping over them) are static typing here, not a
formalization convenience. The classical query layer below remains the
proven engine several general results reuse internally.

- `Provenance.AggValue` – symbolic aggregate tokens for the general (non-fused)
  HAVING semantics: `AggValue T K` packages an aggregate function with the
  ≼-sorted occurrence payload of its originating group, with the
  world-faithful (`specialize`), per-world (`valOn`) and deterministic
  (`collapse`) readings, the predicate provenance of a comparison against
  the token (`predProv`, agreeing with `havingProv` on a group via
  `predProv_ofGroup`), its scalar counterpart `predProvScalar` summing over
  *all* worlds, the empty one included, where the aggregate reads the empty
  sequence (`valOn_empty`) – the reading a row needs when it exists
  independently of its aggregate having anything to range over, the two
  differing by exactly that one term (`predProvScalar_eq_predProv_add`) –
  with the choice between them carried by the token's own `scalar` field,
  since a comparison may be far downstream of the operator that built it:
  `ofGroup` and `ofScalarGroup` settle it, the pushforward and the composite
  transport preserve it, and `predProvOf` reads a token in its own
  convention, commuting with homomorphisms either way
  (`predProvOf_mapAnn`); the annotation pushforward (`mapAnn`), and lifted
  column values `T ⊕ AggValue T K` mixing key and token columns.
  **A count compared to zero collapses to a single reading**:
  `predProvScalar_count_eq_zero` gives `𝟙 ⊖ ⊕ᵢ αᵢ` with no
  hypothesis on `K` at all – the comparison holds in the empty world and in
  no other, so there is no family of worlds to collapse
  (`predProvScalar_of_only_empty`) – and `predProvScalar_count_ne_zero`
  gives `⊕ᵢ αᵢ` under absorptivity, the worlds it sums over being the
  non-empty ones, which `Having.sum_ann_meet` collapses. Both are stated of
  an arbitrary occurrence family, so they hold of a family gathered from
  several sources as well as of one group. **Two comparisons of one
  token** are another matter: a predicate conjoining them multiplies
  their provenances, each summed over the worlds separately, and
  `predProvAnd` (with `predProvScalarAnd`, `predProvOfAnd`) names the
  joint sum over the worlds where both hold instead.
  `predProvOf_mul_predProvOf` says the two agree exactly when `K` is
  exclusive and its multiplication is idempotent – `𝔹[X]` has both, `ℕ`
  is exclusive and not idempotent, and an absorptive domain such as
  Viterbi is not exclusive. It is the shape a truncation's range test
  and a `HAVING` like `count(*) > 2 AND count(*) < 5` have. When the two
  atoms read *disjoint* families instead – several subquery conditions,
  say – what is needed is not that but `complemented`, the De Morgan law
  `𝟙 ⊖ (a ⊕ b) = (𝟙 ⊖ a) ⊗ (𝟙 ⊖ b)`, under which a world's annotation
  splits along a partition of its family (`Having.worldAnn_split`).
  `Having.relAnn` is the relative form that composes, and
  `relAnn_split_union` splits the union of two *overlapping* families
  into the shared part and the two private ones – the third regime,
  whose two known cases are its degenerate ones.
  `Having.sum_mul_sum_of_split` is the disjoint case at the level of the
  sums rather than of one world: the product of the two families'
  world-sums is the single sum over the worlds of their union, needing
  `complemented` and nothing else, on the reindexing `Having.sum_split`
  of the worlds of a family by the pairs of worlds of its halves.
  `Having.sum_mul_sum_of_overlap` settles the third regime, families
  that overlap without being equal: the same equality holds under the
  hypotheses of *both* settled cases, each on the part it governs –
  `complemented` splits the two private parts off
  (`sum_family_split`, `sum_split_of_union3`), and exclusivity with an
  idempotent `⊗` collapses the shared part, which each side reads
  (`relAnn_mul_eq_zero_of_ne`). The disjoint case is where the shared
  part is empty and the same-family case where the private parts are,
  so the two known regimes are its degenerate ones. The
  The `∨` rule is not a decomposition at all: over two *grouped*
  families the `⊕` of the two atoms differs from the one-sum reading
  already in `𝔹` (`bool_or_ne_joint`), because a world of the
  disjunction must meet each family while the `⊕` fires where one group
  is empty – so what makes it sound is the row's group-existence
  factors, not the families' independence.
  The two hypotheses are independent: `ℕ` is complemented and not
  multiplicatively idempotent (`Nat.not_mulIdempotent`), so it separates
  the same-family readings and leaves the disjoint ones alone. The
  domains that satisfy the same-family hypothesis are the exclusive
  ones whose `⊗` is idempotent, which of the catalog are `𝔹`, `𝔹[X]`,
  lineage and interval union (`Bool.mulIdempotent`,
  `BoolFunc.mulIdempotent`, `Which.mulIdempotent`,
  `IntervalUnion.mulIdempotent`) – the lattice-like ones.
  `predProvWith` reads an arbitrary three-valued *test* on the token's
  value in place of a comparison, which is the form an atom takes once
  a range is one atom rather than two; `predProvOf_mul_predProvOf_with`
  is then the `∧` rule in its proper shape, a decomposition of one sum
  into two rather than a definition.
- `Provenance.AggExpr` – **aggregate expressions, and with them what a
  predicate annotates**: the joint evaluation of its Boolean function in
  every world. `AggExpr.predProv` is the `⊕`, over the worlds of the
  union of the families the expression reads, of the world's annotation
  times the truth of the comparison there; since `g` may be any
  deterministic function of SQL, a Boolean combination among them, this
  is one rule for `∧`, `∨`, `¬`, a Boolean-valued aggregate column and a
  searched `CASE` alike, and it is the semantics – ProvSQL's too – that
  the structural rules of `GenPredIn.predsem` are a short cut for:
  agreeing on an atom, a decomposition of the joint reading for `∧`
  under hypotheses, and not a theorem at all for `∨`, where the sum has
  to be computed instead.
  What a term that
  mentions a column of aggregate kind produces: `AggExpr` is the formal
  `g(a₁, …, a_p)` – the function the term computes, applied to the
  aggregate values it reads, the regular ones being constants of `g` –
  over one *shared* occurrence family, which is what makes the leaves
  answer together: two aggregates over the same group are read over the
  same occurrences, so an expression of them is not a function of their
  values separately. A world meets the occurrences of every grouped leaf
  and is free of the scalar ones (`IsWorld`, the case split
  `predProv`/`predProvScalar` already make), the value there is
  `valOn`, and `disp` is the displayed value: the reading in the family
  of occurrences the database as it is keeps, which is what SQL returns
  and is smaller than `collapse` exactly where occurrences come through a
  difference or a rejected comparison. `ofValue` embeds a token as the
  expression of itself and `predProv_ofValue`, `collapse_ofValue`,
  `disp_ofValue` say the embedding changes no reading. A *unary*
  expression is again a token: `AggValue.postcomp` reads a token's
  aggregate through a function, keeping its occurrences and its
  convention, and `valOn_ofUnary` says it reads in each world what
  `g(a)` reads there – which is what a term over one aggregate column
  produces
- `Provenance.Nested` – **nested aggregate values**: what an
  aggregation builds when its term reads an aggregate column. Its
  occurrences are those of its own family together with those of every
  value it reads, at every storey, which an `AggValue` cannot hold – its
  reading consults its own list alone. A nested value is a **tower**:
  `NestInner T K j` is what an occurrence of a value of storey `j` reads
  (an aggregate expression at storey `0`, and at storey `j + 1` either
  something storey `j` reads or a node, `NestNode`, aggregating a bag of
  storey-`j` values), and `NestedValue` is an outer aggregate over a bag
  of such occurrences. Everything is a **bag**: `≼` orders plain tuples,
  and an occurrence of a nested value carries a tuple with an aggregate
  column, so the family a nested value aggregates has no sequence to be
  listed in. Its aggregate is accordingly a function of a bag
  (`SeqAggFunc.onBag` makes one of a symmetric aggregate). An
  occurrence is one object however many times it is read, so a world
  decides each **family** once: its own occurrences (`root`), each
  expression family by its key (`leafKey`) and each inner node by its
  key (`NestNode.key`); `worlds` enumerates the decisions off the bags,
  the steps being left-commutative, so nothing has to list the
  occurrences and nothing has to be proved invariant under relisting
  them. A world meets the family of each grouped inner value **that it
  reads**, which is to say along a path of present occurrences
  (`World.IsWorld`): an absent outer occurrence contributes nothing, and
  asking its inner family to be met would ask a group to be non-empty
  while the row carrying it is absent. The converse, barring a world
  from meeting a family no present occurrence reads
  (`World.IsWorldCoherent`), is refuted: it removes the world a
  valuation realizes, and `World.IsWorldWith` keeps the predicate a
  parameter so that the refuted reading can be stated. `valOn_full` says
  the world with everything present reads as the collapse. A world's
  **annotation** is `World.ann`, the product of what is present at every
  storey times `𝟙 ⊖` the sum of what is absent, the monus taken once.
  The **readings** the value owes are there too:
  `NestedValue.predProvWith` and `predProvOf` for a test of its value,
  and `realizedWorld`/`specialize` for the world-faithful reading under
  a valuation – with `specialize_of_forall` saying the two agree where
  every occurrence is realized, and `predProvWith_of_never` that a test
  no value satisfies annotates `𝟘`. The structure degenerates as it
  should: `ofAggValue` nests an ordinary token – a symmetric one, its
  aggregate becoming the outer one on the bag – by giving each
  occurrence an inner value that reads nothing (`constInner`), and
  `ann_worldOf` says a world of it (`worldOf`, from a subfamily of the
  token's own occurrences) carries exactly `Having.worldAnn` of the
  token's own family – so nesting adds weight only where something is
  actually nested
- `Provenance.JointFamily` – **two occurrence families as one**, which
  is what a predicate reading two aggregate values reads. The two
  families are indexed separately, so the union is built:
  `Having.catAnn` concatenates the annotation functions on
  `Fin (m + n)`, `leftFam`/`rightFam` are the parts inside it,
  `catWorld` pairs a world of each and `leftPart`/`rightPart` read them
  back, with `catWorldEquiv` and `sum_catWorld` re-summing a sum over
  the worlds of the union as the double sum over pairs. Reading a part
  of the concatenation is reading the family it came from and needs
  nothing of `K` (`relAnn_catWorld_left` and its twin); from that, a
  world of the union carries the product of its halves' annotations
  exactly where `K` is complemented (`worldAnn_catWorld`).
  `Having.jointPair` is then **what a predicate reading two tokens
  annotates** – the `⊕` over the worlds of the union that meet each
  grouped family – and `jointPair_eq_split` says it is the split double
  sum in which such a reading is usually written, complementedness being
  what that costs. `jointPair_and_const` says a test that does not
  depend on the world – a regular atom, reading no family – factors out
  of the joint reading, which is what makes a selection on regular
  columns transparent to a chain of aggregate selections.
  `Having.row_absorb_singleton` settles the **row-level** absorption
  for two *singleton* grouped families: where `δ` is the identity and
  `⊕` is idempotent, the existence factors do absorb the `∨` rule's
  difference – `⊗`-idempotence collapsing the repeated factor where
  one test holds, which `δ = id` gives free from `δ(x) ⊗ x = x`, and
  `⊕`-idempotence the two copies where both do. Families of several
  occurrences are not covered, and `ChainFive` shows an idempotent `⊕`
  alone is not enough (`chain_row_ne`)
- `Provenance.SubWorlds` – the subfamilies of a listing as a bag
  (`subWorlds`, equal to the enumeration of the subsets of positions by
  `univ_map_eq_subWorlds`), blind to a tie-block permutation of the
  listing once the selected occurrences are read through a map that
  cannot tell tied ones apart (`subWorlds_tiePerm`), and pushed through a
  map of annotations (`subWorlds_map`); an aggregate expression read off
  the occurrences a world selects (`AggExpr.isWorld_iff_okSeq`,
  `valOn_eq_valSeq`)
- `Provenance.AggValueCongr` – congruence of the token readings under
  tie-block permutations of the payload: `TiePerm`, the guarded analogue
  of `List.Perm` whose swaps only exchange adjacent elements with equal
  sort keys (`tiePerm_of_perm_of_sorted` produces one from two sorted
  permuted lists), a recursion form of the predicate provenance
  (`AggValue.predProvAux`, equal to the world-sum by
  `AggValue.predProvWith_eq_predProvAux`), and the congruences
  (`AggValue.predProv_congr`, `collapse_congr`, `annSum_congr`) making the
  annotation tie-break of the group sort semantically invisible
- `Provenance.AggQuery` – the general (non-fused) HAVING semantics:
  kind-indexed queries `AggQuery` over three column kinds – regular
  values, aggregate tokens, provenance values, ProvSQL's regular /
  `agg_token` / uuid data types – enforcing the scope conditions
  statically (`Gamma` over all-regular inputs only, no `Dedup`/`Diff`
  over token columns, normal-form projections and selections),
  the **empty relation** `Empty` of arity `0` – the one leaf that belongs
  to the query and not to the instance, from which the unit relation
  (`AggQueryIn.unit`, its scalar aggregation with no aggregate: one empty
  tuple annotated `𝟙`, PostgreSQL's `SELECT;`) and SQL's `VALUES`
  (`AggQueryIn.values`, a union of projections of the unit onto constants,
  with `evaluatePlain_values` and `evaluateAnnotated_values` reading
  them) are derived, so a constant relation needs no leaf of its own –
  aggregation without grouping (`GammaScalar`, whose single row survives an
  empty input: annotated `𝟙` with no group-existence factor, its tokens
  read in the scalar convention), **second-level aggregation**
  (`GammaNest`: the term aggregated reads an aggregate column, so the
  column built is a *nested* token whose occurrences are the group's rows
  as a bag, each carrying the aggregate *expression* read there –
  `Provenance.NestedExample` writes it; an occurrence may itself carry a
  nested value, at any storey, a world deciding each inner occurrence
  once (`NestedValue.World`); the random world, the PQE results and the
  hom commutation ask nothing of it, and `noGammaNest` is left excluding
  only
  the two syntactic token fences it is the counterexample to), the
  token-building grouping `GammaTok` and provenance aggregation
  `ProvSum` of rewritten plans, the generalized selection grammar
  `GenPred` mixing regular and aggregate atoms (`∧ ↦ ⊗`, `∨ ↦ ⊕`, `¬` by
  operator complementation – the short cut the joint reading of
  `Provenance.AggExpr` licenses, semiring permitting), and the general evaluator
  `AggQueryIn.evaluate` with factored row annotations `GenAnn`
  implementing the replace-the-δ-factor combination rule: `Gamma` leaves
  its group-existence factor pending, an aggregate selection supersedes
  exactly the compared groups' factors with the predicate provenance, and
  projections cash the factors of dropped token columns. Also the plain
  evaluator `AggQueryIn.evaluatePlain` (classical filtering, aggregates
  computed over the whole group) and the stripping `AggQueryIn.stripAgg`.
  The two **recursions** `Mu` (SQL's `WITH RECURSIVE … UNION ALL`) and
  `MuSet` (`… UNION`) bind a relation name to the previous round –
  `AnnotatedDatabase.assign`, a cons, since a database is searched front
  to back – and iterate: `Mu` sums its rounds, `MuSet` runs the fixpoint
  iteration of `ε(q₀ ⊎ q₁)`. The two operators are **partial**: what
  each denotes is the value its rounds settle at – the sum up to the
  first empty round (`muSumFix`) and the first fixpoint of the iteration
  (`muFix`), both taken through `Nat.sInf` – and a recursion that does
  not settle has no value. Nothing in the syntax bounds the rounds: a
  recursion that stopped at a count rather than at its own rounds would
  not be this operator. Settling is a hypothesis, `AggQueryIn.recSettles`,
  which the four results that evaluate a recursion carry (adequacy, the
  homomorphism commutation, the random world and the PQE results off
  it); it also asks `step 0 = 0` at `Mu`, which is what makes an empty
  round a fixpoint – SQL buys it by requiring the recursive reference to
  occur in the body, and the bare syntax does not. The rounds carry
  their own lemmas (`muSum`, `muIter`, `muSumFix`, `muFix`,
  `muSumFix_map`, `muFix_map`, `muSumFix_congr`, `muFix_congr`), which
  is what carries adequacy, the random-world commutation and the
  homomorphism through them round by round. Taking the fixpoint makes
  the evaluators `noncomputable`, so the worked examples check their
  values by `decide` rather than printing them. Recursion is outside the
  (R1)–(R5) rewriting fragment (`AggQueryIn.classical`): a rewritten body
  carries the provenance column, so the bound name would have to be
  bound to the rewritten relation and the fixpoint would be over another
  schema.
  A projection column may also *compute* over one aggregate column
  (`ProjColIn.aggTerm`), which produces an aggregate column again – the
  unary aggregate expression of `Provenance.AggExpr` – and is what
  `count(*) + 1` and the ranks need; over plain relations it is an
  ordinary term, and its token is the input's read through the
  function, so every reading of it is the input's read through the
  function too.
  Predicates are read three-valuedly throughout – `GenPredIn.eval3`,
  `evalPlain3`, `HavingPred.evalOnSeq`, `GenPredIn.evalRew3` – with `holds`,
  `holdsPlain`, `holdsOnSeq` and `holdsRew` keeping the rows on which the
  predicate is *true*. `Having.chi` contributes `𝟘` to a provenance on an
  unknown comparison, and `predsem` needed no change at all: its polarity
  flag, the `⊗`/`⊕` swap at `∧`/`∨` and the operator negator at the atoms
  were already Kleene's reading (`CompOp.negate_eval3`).
  The window operator `Win` gives every row of its input a further column
  holding the aggregate over that row's frame: it removes no row, merges
  none and changes no annotation, so it creates no group and leaves nothing
  pending. `AggQueryIn.evaluate_Win_eq` and `AggQueryIn.evaluatePlain_Win_eq`
  read its output off the relation – the input mapped row by row, each row
  gaining the token (`ValueFrame.tokenOf`) or the value
  (`ValueFrame.windowValue`) that the relation gives it – which is the form
  every theorem about the operator uses.
  Every aggregating operator carries SQL's `FILTER` clause: `Gamma`'s
  `keep`, one per aggregate, `Win`'s `keep`, `WinExpr`'s `keeps`, one per
  leaf of the expression, and `GammaTok`'s in the rewritten world. A
  clause reads *regular columns only*, SQL forbidding an aggregate inside
  the `FILTER` of an aggregate, so its truth at an occurrence is the same
  in every world and survives any transport that keeps the data columns –
  which is why no result below asks anything about what a clause reads.
  What a clause may change is what its own
  aggregate **reads**, and nothing else: the worlds stay the group's or
  the frame's, every occurrence carrying its annotation to them, so the
  world in which only rejected rows are present is still a world and the
  aggregate reads `f []` there – which is the row SQL emits for a group
  whose rows the clause all rejects. A multi-frame window reads it that
  way: `AggExpr` keeps the group and the clause apart
  (`AggExpr.inFrame`, which `IsWorld` asks about, and `AggExpr.reads`,
  which the value reads), and `ValueFrame.exprOfWhen` cuts only the
  second, so a clause that keeps everything *is* no clause. Every
  reading covers it with no new hypothesis: the deterministic one
  (`ValueFrame.collapse_exprOfWhen`), the pushforward
  (`ValueFrame.occs_exprOfWhen` – a clause tests the occurrence's own
  tuple, which a tie-block permutation does not move) and the random
  world (`exprOfWhen_specialize`, a restriction to a world not moving a
  row). A grouping reads it the same way, through
  `AggExpr.ofGroupWhen`: one leaf over the whole group, whose clause cuts
  what it reads, so `Gamma`'s filtered column is an expression and not an
  ordinary token – which is why `AggQueryIn.evaluate_ordinaryTokens` asks
  for `noFilter`. A single-frame window reads it the same way
  (`ValueFrame.exprWhen`), with the kept part merged by value under
  `DISTINCT` and the rejected occurrences left unmerged and unread, so no
  clause anywhere cuts a family.
  `chain_count_zero_when_ne` measures what a
  cut family cost, against `chainExprNone_zero`, `chainExprMixed_zero`
  and `chainWinMixed_zero` for what the expression reading gives, and
  `natWinDistinct_ne_unmerged` records that a `DISTINCT` aggregate's
  classes carry the `⊕` of their occurrences rather than deduplicating
  inside each world. A filtered
  aggregate builds an expression and not an ordinary token, so
  `AggQueryIn.noFilter` is what `AggQueryIn.evaluate_ordinaryTokens`
  asks
- `Provenance.AggQuerySubst` – **substituting the outer columns**: the
  apply is defined by substitution – its right side is read, for each
  row `u` of the left, as the closed query `q₂[u]` – while the
  evaluators read it under an outer *valuation*, which is what makes
  them structurally recursive. `AggQueryIn.substMap` performs the
  substitution (generally enough to close only the ambient part of a
  nested context, which is what passing under an apply needs) and
  `AggQueryIn.evaluatePlain_substMap` says the two readings agree, so
  that reading the apply by substitution
  (`AggQueryIn.evaluatePlain_Apply_subst`) is a theorem about the
  evaluator rather than a second semantics; in the annotated semantics
  `AggQueryIn.evaluate_substMap` holds for renamings of the outer
  columns, a constant in a parameter's place being no parameter
- `Provenance.Occurrence` – **relations as families of occurrences**:
  `OccFam`, a relation read as an indexed family rather than a multiset, so
  that two copies of a row are two occurrences. The row type is a parameter,
  since the rows a window produces carry a token where the rows it reads
  carry only values. A multiset discards that
  identity, which three things need: an operator that gives equal rows
  different results (a window frame excluding the row it is computed for
  reads its twin, not itself), a comparison reading two aggregate values
  whose occurrence families overlap, and a statement quantifying over the
  ways equal rows could be told apart. `OccFam.toMultiset` forgets the index and
  `Congr` says when two indexings are the same family, so that an operator
  defined on families is meaningful exactly when it respects `Congr`
  (`toMultiset_congr`). It sits beside `AnnotatedRelation` rather than
  replacing it
- `Provenance.Frame` – **window frames determined by values**:
  `ValueFrame`, a frame given by a relation `ρ` between order values and a
  predicate `s` deciding whether an occurrence is in its own frame. Its
  point is `frame_inter`, the restriction property – the frame of an
  occurrence among the present rows is its frame in the whole relation
  intersected with them – which is what a positional frame lacks and what
  lets a window be read world by world. `ContainsSelf` names the condition
  `s o = ρ o o`, under which membership stops mentioning the occurrence
  (`mem_of_containsSelf`) and the frame depends only on the tuple
  (`frame_eq_of_key_eq`); the frames that fail it are exactly `EXCLUDE
  CURRENT ROW` and `EXCLUDE TIES`, which are exactly the ones needing
  occurrences told apart. The frames of SQL that are determined by values
  come in two families. Against the domain's own order on the order values:
  `whole`, `upTo`, `before` (the rows strictly preceding the current row's
  peers) and `excludeCurrent`. Against an explicit `ORDER BY`
  (`Provenance.OrderSpec`): `rangeUpTo`, `rangeBefore`, their mirrors
  `rangeFrom` and `rangeAfter` – which are the first two under the
  reversed clause (`rangeUpTo_reverse`, `rangeBefore_reverse`) –
  `peerGroup` and the
  modifiers `excludeGroup` and `excludeTies`, each classified by
  `ContainsSelf` – and the classification lands where the general theory
  says it must, `EXCLUDE GROUP` keeping a frame readable off the relation
  and `EXCLUDE TIES` not. The two families agree where every column is
  `ASC` and nothing is null (`rangeUpTo_asc`, `rangeBefore_asc`);
  the `ROWS` frames with offsets are not among them and
  cannot be, since which row is the previous one depends on which rows are
  present. `frameOf` reads a frame off the *relation* rather than off an
  indexing – the rows of the partition the frame's relation accepts, the
  row's own copy taken out and put back exactly as `s` says – and
  `frameSeq_eq_sortList` proves the two readings agree, so `tokenOf` gives a
  token to a row of a relation with no indexing in sight. What a token
  actually holds is `frameSeqOn`, that sequence put into the order the
  window's `ORDER BY` asks for (`Provenance.OrderSpec`), the canonical order
  breaking the clause's ties; `sortSeq_map_fst` and `sortSeq_mapAnn` say the
  clause survives forgetting the annotations and changing the semiring,
  since it reads only the rows. What that buys is
  `frameOf_map` (a map keeping the values carries every frame to the image
  of its frame: changing the semiring, or forgetting the annotations) and
  `frameOf_filter` (the restriction property again, on relations),
  which are what the window's metatheorems run on
- `Provenance.Window` – **the token a window gives a row**: the aggregate
  over that row's frame, built as a grouping builds one from its group, with
  the convention decided per row by whether the row is in its own frame
  (`token`, `token_scalar_of_mem`, `token_scalar_of_not_mem`). A row that is
  never reads its aggregate over nothing; a row that is not may have an empty
  frame in a world where it is itself present. The window removes no row,
  merges none and leaves every annotation alone, so no group-existence factor
  arises. `window` is the operator itself, on families: every occurrence
  keeps its row and its annotation and gains its frame's token, and
  `window_congr` proves it **well defined on occurrences rather than on
  indices** – congruent inputs give congruent outputs, so nothing it
  produces depends on which indexing was chosen. That is the obligation the
  family reading exists to impose, and the reason two equal rows may
  legitimately receive different aggregates. `windowRel` applies it to a
  relation by reading one as a family, and `window_toMultiset_congr` says the
  answer is about the relation: exchanging two equal rows exchanges their
  tokens, so which of them receives which is not observable. That rests on
  `OccFam.Congr_of_toMultiset_eq`, proved from `List.Perm.exists_get_equiv` –
  a permutation of rows gives a bijection of positions carrying one to the
  other, which Mathlib states only for lists without repeats.
  `window_toMultiset_eq` cashes the family reading into the relation
  reading the evaluator uses: the output is the input mapped row by row
  through `windowRow`
- `Provenance.Notation` – **surface syntax** for kind-indexed queries:
  a bracketed `RA[ … ]` with categories of its own for terms, predicates and
  queries, so that `∧`, `∨`, `¬`, `<` and `=` are read as the query
  language's and not as their meanings on `Prop`, comparisons elaborate
  straight to `GenPred` atoms, column references `#i` carry their own
  regularity proof, and `ε` and `∖` retag their argument to the all-regular
  kind vector their constructors ask for (`allReg`). A column reference says
  which column and not what is in it: `atomAt` and `projAt` decide by
  computation on the kind vector whether `#i` is a value comparison or an
  aggregate atom, a projected term or a token carried through, so the syntax
  of a query does not change with the kinds of its columns, as it does not
  in SQL. A grouping with no keys, `γ[ ; t : f]`, is aggregation without
  grouping, the absence of a `GROUP BY` being what makes an aggregation
  scalar here as it is there. Grouping reads its keys
  and its aggregated columns as two lists, `γ[#i, … ; t : f, …]`, the
  aggregates being ordinary Lean terms so that the catalog stays open; the
  same term syntax is read into `TermG` under a selection and into the
  classical `Term` under a grouping, which is what the aggregated columns of
  an all-regular input are. A window is written `⊞[#i, … ; #j, … ; w ;
  t : f]`, the three lists before the aggregated column being the partition
  columns, the order columns and the frame – an ordinary Lean term, so that
  the catalog of frames stays open as the catalog of aggregates does. What a
  query costs to write is then the query
- `Provenance.AggQueryAdequacy` – **data-part adequacy of the general
  evaluator**: forgetting the annotations of `Query.evaluateAnnotated` yields
  the plain evaluation of the stripped query
  (`AggQueryIn.evaluateAnnotated_toPlain`), the aggregate tokens
  contributing through their deterministic `collapse` reading and the
  fused group sequence projecting onto the plain one
  (`havingGroup_map_fst`). A window's added column is adequate for the same
  reason: its token collapses to the plain aggregate over the frame
  (`ValueFrame.collapse_token`), the frame projecting onto the plain frame
  because sorting annotated tuples and projecting is sorting the tuples
  (`ValueFrame.sorted_map_fst`)
- `Provenance.OrderSpec` – **what an `ORDER BY` orders by**: a direction
  and a null placement per order column (`OrderCol`, `OrderSpec`), read
  lexicographically down the columns. It is a total preorder
  (`OrderSpec.le_rfl`, `le_trans`, `le_total`) and not an order: the values
  it does not separate are SQL's *peers*, and every null is a peer of every
  other whichever side the clause puts them on. Where every column is `ASC`
  and nothing is null the clause is the library's own tuple order
  (`OrderSpec.asc_le`). Two things are defined from the clause that the
  domain's order cannot supply: the *bound* of a frame, which lives with
  the frames in `Provenance.Frame`, and the order a frame is *read* in –
  `OrderSpec.readLe`, the clause on the order values with the canonical
  order on rows breaking its ties, and `OrderSpec.sortSeq`, which puts a
  listing of a frame into it. `sortSeq_tiePerm` is what makes the second
  usable: two listings of one frame come out related by a tie-block
  permutation whose blocks are the occurrences of one row, which is exactly
  the freedom every reading of a token is invariant under; `map_eq_of_sorted`
  is the working form and `filter_sortSeq_map_eq` says cutting a frame down
  to a possible world and sorting commute on the values read off. A window
  with no `ORDER BY` is `OrderSpec.unordered`, which separates nothing, and
  its frame is read as a group is (`ValueFrame.frameListOf_of_peer`).
  `OrderSpec.reverse` reads the clause backwards, direction and null
  placement together, which is what `last_value` reads its frame in
- `Provenance.Derived` – **the operators that add nothing**: each is an
  abbreviation, a query of the basis, and its semantics – plain and
  annotated – is that of the query it abbreviates, so every theorem proved
  of the basis applies to it as it stands. `pad` replaces columns by the
  null (`padRight`, `padLeft` are what an outer join does to an unmatched
  arm); `inter` is SQL's `INTERSECT`, the two deduplicated arms joined on
  all their columns *syntactically*, which annotates a shared tuple by the
  product of the two `⊕`-sums – the provenance of a conjunction of the two
  memberships, and not what `ε(q₁ - (q₁ - q₂))` would give – all three
  characterized over plain relations (`evaluatePlain_pad`,
  `evaluatePlain_inter`, `evaluatePlain_leftOuter` and its companions,
  with `mem_matchedLeft`/`mem_matchedRight` saying which rows of an arm
  have a match); `leftOuter`,
  `rightOuter` and `fullOuter` add to the matching rows the unmatched ones
  of either arm, padded. `semijoin` and `antijoin` apply the left arm to
  the scalar aggregation `matchCount` of the filtered right one, so that
  each occurrence of the left arm keeps its multiplicity – a grouping on
  its columns would merge duplicates, which `WHERE EXISTS` does not – and
  so that a row with no match still has its row, with count `𝟘`;
  comparing that count against `𝟘` is what tells the two apart.
  `firstValue`, `lastValue`, `lag` and `lead` are the window operator
  with `PICKFIRST`: what tells them apart is the frame and the order it
  is read in, which the operator keeps separate because the frame is an
  argument of its own; `nthValue`, `lagAt` and `leadAt` are the same
  three over `SeqAggFunc.pickNth`, which reads a position of the frame
  other than its end – so `lastValue` reverses the reading clause and
  leaves a clause-bounded frame bounded as it stands. `rank` is one plus
  the count over the rows the clause sorts strictly before the current
  row's peers, the `+ 1` being a term over the window's aggregate column
  (`overWindow`); `evaluatePlain_rank` says so over plain relations.
  `truncate` is `λ`, the rank filtered to a range and the rank column
  dropped again (`truncateFrom` for an infinite count), which keeps a
  row tied with the last one kept – SQL's `FETCH FIRST c ROWS WITH
  TIES`; `evaluatePlain_truncate_noNulls` reads it as the filter on the
  rank it is, and `distinctOn` is `λ^{P,O}_{0,1}`, SQL's `DISTINCT ON`.
  The range it filters on is a single atom, `GenPredIn.aggRange`, so its
  predicate provenance is the one `⊕`-sum over the worlds where the rank
  is in range (`predsem_rankRange`), with no
  hypothesis on the m-semiring – where a conjunction of two atoms would
  give the product of two sums. No `provsql_having` gate carries a range,
  so the site rewriting is stated on range-free predicates
  (`GenPredIn.rangeFree`): the term it would emit denotes the product,
  which an evaluator may resolve back to the range's own sum by
  recognizing that the two gates read one family, but which the term
  itself does not denote.
  `gammaSets` is SQL's `GROUPING SETS`: the union of one
  aggregation per set of the family, each padded back onto the columns
  of the whole key, so that a key column a set drops reads as the null
  (`gsRow` says which row each arm contributes). `filterTerm` is SQL's
  `FILTER` clause: the aggregated term read through a `CASE`, which the
  null-skipping and counting input policies then drop, so that
  `gammaFilter` and `winFilter` read exactly the occurrences the clause
  keeps (`sqlOf_map_filterTerm`, `counting_map_filterTerm`) while the
  group, its key and its annotation stay those of all the occurrences.
  A null-keeping aggregate is not covered: it reads the null as a value
  and so cannot tell a rejected occurrence from a null one. Over
  annotated relations the clause changes only what the token reads in
  each world (`aggValOn_filterTerm_sqlOf`,
  `valOn_ofGroup_filterTerm_sqlOf` and their counting companions in
  `Provenance.DerivedAnn`): the token carries every occurrence of the
  group, so its key and its existence factor are those of all of them.
  `gammaDistinct` and `gammaScalarDistinct` are SQL's `DISTINCT`
  aggregates: deduplicate the key columns together with the aggregated
  term, then aggregate the added column, which annotates each distinct
  value by the `⊕` of the occurrences it stands for;
  `evaluatePlain_gammaDistinct` reads them over plain relations as the
  aggregate over the distinct values (`SeqAggFunc.distinct`), for a
  symmetric aggregate. `distinct` reads the distinct values *sorted*:
  deduplication leaves one value per class and not a sequence, so
  nothing but the values can fix the order, which is SQL's own rule –
  `array_agg(DISTINCT t)` is legal and ordered by the values, while
  `array_agg(DISTINCT t ORDER BY u)` is rejected – and it makes
  `distinct_symmetric` hold of every aggregate.
  The `DISTINCT` of a *window* aggregate is the `dist` flag the `Win`
  operator carries: it merges the occurrences of a frame by value
  (`AggValue.mergeByValue`, one occurrence per class carrying the `⊕`
  of its members, the classes in the domain's order), which no reading
  of a token recovers, so the operator has to say it. Over plain
  relations it is `SeqAggFunc.distinct`
  (`ValueFrame.collapse_tokenDist`), and reading the classes in the
  domain's order is what makes it world-faithful with no condition on
  the aggregate – that order restricted to the classes a world holds is
  the world's own order (`AggValue.specialize_mergeByValue`,
  `tokenOfDist_specialize`). The metatheorems go through on
  `classSum_map` and `mergeByValue_congr`: the merge commutes with the
  annotation pushforward and is blind to a tie-block permutation of the
  payload
- `Provenance.DerivedAnn` – **what the derived operators annotate**, which
  is what the choice of each definition is answerable for. `annSum` is the
  `⊕`-sum of the annotations a query gives one tuple, what duplicate
  elimination accumulates (`evaluate_Dedup`), and
  `evaluateAnnotated_inter` says intersection annotates a shared tuple by
  the product of the two sums – the provenance of a conjunction of the two
  memberships, which `ε(q₁ - (q₁ - q₂))` would not give. The reusable
  step is `evaluateAnnotated_Proj`: **a projection carries the finalized
  annotation across**, what it cashes of the pending group factors coming
  out of the pending part and into the concrete one. From it and
  `evaluate_Diff` – difference subtracts the `⊕`-sum of the annotations a
  tuple carries on the right, and removes no row – come the outer joins:
  a matching pair is annotated by the product, and a padded row by
  `α ⊖ ⊕(α' ⊗ β)` over the matches of *every copy* of its tuple
  (`evaluateAnnotated_leftOuter` and its right and full companions). That
  subtracted form is the definition; `α ⊗ (𝟙 ⊖ ⊕β)` equals it only when
  `⊗` distributes over `⊖` and `K` is absorptive. The semijoin and the
  antijoin read their row off one count site
  (`evaluateAnnotated_countSite`): a semijoin multiplies each occurrence
  of its left arm by the `⊕`-sum of the annotations of the rows it
  matches (`evaluateAnnotated_semijoin`, over an absorptive `K`), an
  antijoin by `𝟙 ⊖` that sum (`evaluateAnnotated_antijoin`, over any
  `K`) – the comparison being read in the scalar convention, so that no
  pending group factor is superseded
- `Provenance.PlainBasis` – **which operators a query cannot do without**:
  `OpKind` names the classes an operator belongs to, `AggQueryIn.usesOnly`
  says a query stays inside a set of them, and `PlainEquiv` is agreement
  of the plain semantics on every instance. Six invariants bound a
  generating set from below, each with a query that breaks it: a query
  over the empty schema that uses no empty relation is impossible
  (`usesEmpty_of_overSchema_empty`), a projection-free query over
  duplicate-free relations has bounded multiplicities
  (`count_le_multBound`), a query with neither selection nor difference is
  empty on every instance or non-empty on every instance whose relations
  are all non-empty (`zero_or_ne_zero_of_noSelDiff`), a query with no
  product and no apply has a size linear in the instance
  (`card_le_sizeBound`), a union-free query over relations of at most one
  row has at most one row (`card_le_one_of_thin`), and an
  aggregation-free query is empty on the all-empty instance
  (`evaluatePlain_eq_zero_of_allEmpty`). Four operators are deliberately outside
  the classification – the two recursions, which the predicate reads as
  `False`, and `GammaTok` and `ProvSum`, which belong to the rewritten
  world rather than to the language a source query is written in. The
  identities that generate the rest are proved as `PlainEquiv`s:
  duplicate elimination from a grouping (`dedup_plainEquiv_gamma`), the
  difference from counts over a tagged union (`diff_plainEquiv_notIn`), a
  selection from two differences (`sel_plainEquiv_selByDiff`), the apply
  from a product where its right side reads no outer column
  (`apply_plainEquiv_prod`), and a window from an apply of a scalar
  aggregation (`plainEquiv_winByApply`). Two of them build their own
  syntax: `GenPredIn.polTerm` reads a predicate whose atoms are
  comparisons as a `CASE` expression over the same comparisons – the
  term the selection-from-difference needs, with both polarities, since
  in Kleene's logic a negation holds where its argument is *false* – and
  `winByApply` writes the window's frame as a selection against the
  current row, which the apply supplies as outer columns. The window's
  frame is asked to contain its current row, which is the hypothesis of
  `evaluatePlain_winByApplyOf` and not of the decorrelation
- `Provenance.Decorrelate` – **an apply read as a product**: the
  construction of Galindo-Legaria and Joshi, proved rather than cited.
  Given a *parameter relation* `P` whose rows are pairwise distinct, a
  query reading `P`'s columns as parameters is turned into a closed query
  over the parameters and its own columns together, whose rows are the
  *slices* `Relation.slices P f = ⊎_{v ∈ P} {v} × f v`
  (`AggQueryIn.HasDecorrelation`). Each operator carries the parameters
  along – a selection reads them as columns (`GenPredIn.lift`), a
  grouping takes them into its key (`groupKey`), a window into its
  partition (`winPart`), with the clause's order and its `FILTER`
  shifted over the block (`GroupOrder.lift`, `Selection.shift`) – and the
  apply itself recurses, with duplicate elimination of its left side's
  decorrelation as the new parameter relation, its two blocks swapped
  into the order the right side reads its context in
  (`Relation.swapBlocks`), joined back on those columns so that the
  multiplicities duplicate elimination dropped are restored
  (`Relation.applyJoin_slices`). `hasDecorrelation_of_usesOnly` assembles
  the cases, and `exists_applyFree_plainEquiv` is the closed-query
  corollary, over the unit as the parameter relation: every query of the
  fragment is plain-equivalent to one with no apply. The *target* class
  set is a parameter throughout (`decorrOps` being what the construction
  itself needs, beyond the classes the query already uses), which is
  what lets the result be composed with the other passes: a query with
  no window decorrelates to one with no window, and a nine-class target
  would not record that
- `Provenance.AllRegular` – **reading every column as a value**: in the
  plain semantics every column holds a value of the domain, the kind
  vector being a syntactic index, and `AggQueryIn.exists_allReg` makes
  that into a theorem – every query is plain-equivalent to one all of
  whose columns are regular, using the same classes and naming the same
  relations. `AggQueryIn.Explode` is the bridge (it reads an aggregate
  column as a key and is the identity over a plain relation) and
  `AggQueryIn.Retag` the one for a provenance column; `explodeBelow` applies
  them column by column. Three readings of an aggregate column have
  exact regular counterparts – `GenPredIn.toReg` takes an aggregate atom
  to the same comparison and a range atom to its two, `ProjColIn.toReg`
  takes a column read as a token to the column – and two things have
  none, which `AggQueryIn.Retypable` fences off: a projection column
  post-composing an aggregate with an arbitrary function
  (`ProjColIn.aggTerm`), and **a non-determinate window over aggregate
  columns**. A window is the one operator whose *plain* semantics reads
  the kind vector: it reads its input through `ColKind.readTuple`,
  nulling the aggregate columns, which is one of the listings of a frame
  that its order clause allows. Reading an aggregate column as a value
  puts it into the tie-break, so the re-typed window lists a block of
  peers in another order – immaterial to a *determinate* window, which
  is all the semantics admits, and visible to one the semantics refuses.
  The fence is therefore determinacy itself, quantified over the
  instance as `AggQueryIn.recSettles` is, or an all-regular input
  (`ValueFrame.windowValueOpt_readTuple_of_det`, with
  `windowValue_readTuple` the symmetric unfiltered case), and a `FILTER`
  clause is carried through on the condition that it read the
  occurrence's regular columns, as a clause does in SQL, which forbids
  an aggregate inside the `FILTER` of an aggregate. What the theorem leaves behind is
  `AggQueryIn.SwapReady`, which is what the two swaps of the basis ask
  for
- `Provenance.Determinacy` – **the listing an aggregate reads, and the
  query that is refused**: an aggregate reads its group, or a window's
  frame, as a sequence that its clause only partly fixes, and a query
  is determinate where the listing cannot matter – each
  aggregate symmetric, or its term constant on the rows the clause
  ties. `ValueFrame.windowValue_eq_of_listing` and
  `Relation.groupSeqOrd_map_eq_of_listing` say the listing is then
  invisible (off `List.map_eq_of_pairwise_of_symm`, two sorted listings
  of one bag reading alike, and `OrderSpec.peer_of_readLe`, mutual
  comparability being peerhood); `AggQueryIn.DeterminateOn` is the
  condition, quantified over the instance as `recSettles` is; and
  `AggQueryIn.evaluateChecked` is the evaluator that answers where it
  holds and refuses where it does not, with
  `windowValue_eq_of_listing_of_determinateOn` and
  `gammaAgg_eq_of_listing_of_determinateOn` saying what its answer
  means. `AggQueryIn.evaluatePlain` keeps its own
  listing – one the condition admits – which is why no result of the
  metatheory asks for determinacy: each relates two readings of one
  listing. The one place two listings meet is the re-typing of
  `Provenance.AllRegular`, whose window fence *is* this condition
- `Provenance.BasisAssembly` – **the basis, assembled**: every plain query is
  equivalent to one over six classes, as three passes over the syntax.
  `AggQueryIn.exists_winFree` replaces every window by an apply of a
  scalar aggregation, `AggQueryIn.exists_applyFree_plainEquiv` (the
  decorrelation) replaces every apply by a product, and
  `AggQueryIn.exists_basisOps_of_dedupDiff` replaces the duplicate
  elimination and the difference the decorrelation leaves behind;
  `AggQueryIn.exists_basisOps_plainEquiv` composes them, so **every
  query of the plain fragment is equivalent to one over the six classes
  `∅`, `Π`, `σ`, `×`, `⊎`, `γ`**. The order of the passes is forced, and
  each is stated with its target class set as a parameter – which is why
  the decorrelation had to be parameterized too: a pass may only be
  composed with the next if what it produces is known not to contain
  what the previous one removed. `GeneratesOn` reads the conclusion as a
  property of a set of classes, `basisOps_generatesOn` says the six have
  it, and the rows below are the converse, from the invariants of
  `Provenance.PlainBasis` and their witnesses.
  Each pass also carries `AggQueryIn.overSchema`: the query it produces
  names the relations the query it is given names, which is what the
  other half needs – two of the six rows (`∅` and `σ`/`−`) are necessary
  only for a query over the schema, a reference to a name the schema
  does not declare reading the empty relation. The six rows are
  `proj_mem_of_generatesOn`, `union_mem_of_generatesOn`,
  `gamma_mem_of_generatesOn`, `prod_or_apply_mem_of_generatesOn`,
  `empty_mem_of_generatesOn` and `sel_or_diff_mem_of_generatesOn`, each
  over the schema its witness lives on. Three of them hold of the whole
  algebra: for `σ`/`−`, `AggQueryIn.NonzeroOn`, the dichotomy relative
  to a set of names forced empty, is what carries the invariant through
  a set recursion; for `Π`, `AggQueryIn.affine_of_body` says that a
  recursive term without a projection reads the recursive relation
  tuple by tuple, so a bag recursion settles only at its base; for
  `×`/apply, `AggQueryIn.pointwise_of_body` says that without them a
  recursive term maps each row to at most one row, and in a signature
  without functions on values (`AggQueryIn.recNoFun`) the orbit of a row
  stays in a box of a size the query fixes (`rowBox`, `recBound`), so
  the rounds a recursion can run are bounded (`optIter_exists_lt`,
  `optIter_ne_none`). In all three, `AggQueryIn.SettlesAt` – the
  recursions settle at this instance – is the one hypothesis a statement
  about a recursion's value needs, and the typing of `AggQueryIn` (a
  recursive term reads its hole once, under `Π`, `σ`, `×`, the left of an
  apply or `⊎`) is the restriction on a recursive term. `GeneratesOn` asks the
  set of classes to hold no recursion, so the query it produces settles
  everywhere, as the plain query it stands for does.
  What a window has to be for the first pass to reach it is
  `AggQueryIn.WinsDerivable`: its frame contains its current row, its
  input is all-regular, a predicate of the language holds exactly where
  its frame condition holds and its `FILTER` clause keeps the row, and
  it is not a multi-frame window – whose column no term expresses.
  `DISTINCT` and the clause themselves are covered, the derived form
  aggregating `f^distinct` where the window does and reading the clause
  in the selection that spells the frame out
  (`evaluatePlain_winByApplyOf`). The predicate itself is built for
  three frames – the whole partition, and the two `RANGE` frames read
  against the clause where nothing is null
  (`AggQueryIn.winsDerivable_win_whole`, `_rangeUpTo`, `_rangeBefore`,
  off `OrderSpec.lePredOn` / `ltPredOn`, the clause's lexicographic
  comparison as a predicate, and `Selection.toPredIn`, a classical
  selection read in a context). What blocks the null branches is that
  the predicate language has comparisons and `IS NOT DISTINCT FROM` but
  no `IS NULL` atom, there being no null constant in `ValueType`.
  The two *swaps* – `−` for `σ`, the apply for `×` – are the passes
  `AggQueryIn.exists_selFree` and `AggQueryIn.exists_prodFree`, which
  ask `AggQueryIn.SwapReady` of their input: a selection's input and a
  product's left factor with regular columns, which
  `Provenance.AllRegular` provides. Composing them gives the three
  **alternative bases**: `AggQueryIn.exists_basisDiffOps_plainEquiv`
  over `{∅, Π, ×, ⊎, γ, −}`,
  `AggQueryIn.exists_basisApplyOps_plainEquiv` over
  `{∅, Π, σ, apply, ⊎, γ}` and – both swaps at once –
  `AggQueryIn.exists_basisApplyDiffOps_plainEquiv` over
  `{∅, Π, apply, ⊎, γ, −}`, each the three passes, then the re-typing,
  then the swap or swaps, with `basisDiffOps_generatesOn`,
  `basisApplyOps_generatesOn` and `basisApplyDiffOps_generatesOn` their
  `GeneratesOn` forms. What lets the two swaps compose is
  `AggQueryIn.swapReady_selByDiff`: the difference a selection becomes
  introduces neither a product nor a selection. None of the three asks
  anything of its input beyond what the six-class statement asks – that
  the columns re-type is part of `AggQueryIn.usesOnly`, which reads a
  column over an aggregate column as a *term* (`ProjColIn.aggTermOf`)
  and refuses the rewritten world's arbitrary function, as it refuses
  `GammaTok` and `ProvSum`.
  **The basis that holds `win`** is
  `AggQueryIn.exists_basisWinOps_plainEquiv` over
  `{∅, Π, σ, ×, ⊎, γ, win}`, two passes and no hypothesis about windows
  at all: nothing has to rewrite one, the decorrelation carrying a
  window of every frame and the third pass keeping it. The window class
  is necessary there (`EXCLUDE CURRENT ROW`,
  `win_mem_of_generatesOnRec`); the six-class statements are the
  stronger claim, about the windows `evaluatePlain_winByApplyOf`
  derives
- `Provenance.RecursionBasis` – **the recursions in a
  basis**: `μ^⊎`, which in the minimal signature is in every basis
  because a bag recursion counts the *derivations* of a tuple.
  The witness is a chain of `n` diamonds – `diamondEdges`, `4n`
  distinct edges over `dChain n`, an instance of `4n + 1` rows with no
  duplicate – and the query `μ^⊎R.(S, Π_{#3}(σ_{#1=#2}(R × E)))`
  (`chainWitness`). `evaluatePlain_reachStep` reads one round as the
  successors of the previous one, `chainStep_iterate_even` and
  `chainStep_iterate_odd` compute the rounds as the layers of the graph
  (the entry node of diamond `i` carrying `2ⁱ` copies, one per path),
  `muSettles_chain` says the rounds end, `count_chainWitness` gives the
  sink `2ⁿ` copies, and `chainWitness_no_polynomial_bound` is the row:
  no `c · (n+1)^k` bounds that. `GeneratesOnRec` is generation over the
  whole algebra **in the minimal universe** `𝒜(∅, {count})`, where a
  query is a partial function of the instance: the query produced
  settles and agrees wherever the given one settles. The rows against
  it are `empty_`, `gamma_`, `sel_or_diff_`, `proj_`,
  `prod_or_apply_` and `muBag_mem_of_generatesOnRec`; `⊎` is **not** a
  row, being derivable (`Provenance.SumByMu`). The
  last rests on `AggQueryIn.exists_polyBound_rec`, which bounds the rows
  of a query without `μ^⊎` polynomially, set recursions included, by one
  induction carrying the card and the values of a result together – a
  set recursion's fixpoint is duplicate-free over a value set of
  polynomial size, and every count inside a recursive term is read off
  the instance the recursion started from.
  The signature the row is stated in is
  `AggQueryIn.inMinimalSig` of `Provenance.PlainBasis`
- `Provenance.SumByMu` – **`⊎` from `μ^⊎`**: with a bag recursion the
  union is a derived operator, so `⊎`, necessary in a basis of the
  recursion-free fragment, is not necessary in one of the whole algebra. `AggQueryIn.sumByMu` is
  the construction (two bag recursions over a one-row driver, each
  reading one operand once through a phase tag; `evaluatePlain_sumByMu`
  says it is `q₁ ⊎ q₂`, `settlesAt_sumByMu` that it settles wherever the
  operands do), and `AggQueryIn.exists_sumFree` the pass: every query
  over the classes of `S` and `⊎` – restricted recursions, in a signature
  `Θ`, every `⊎` all-regular (`sumsAllReg`, what a recursion needs and
  the re-typing produces) – is matched wherever it is defined by one
  over `S` alone, for any `S` holding `sumMuOps` = `{∅, Π, σ, apply, γ, μ^⊎}`,
  with the restriction, the signature, derivable windows and
  well-formedness kept. A `⊎` inside a recursive body is not replaced
  but *split* (`exists_sumFree_aux`'s second half): the body is the sum
  of a body with the non-recursive side of each `⊎` on the recursive
  path dropped and a closed query, which is empty at a bag recursion
  that settles (`mu_of_split`) and moves into the base of a set
  recursion (`muSet_of_split`). The bound names come from an injective
  supply the query does not use, which `exists_freshSupply` gives for a
  schema declaring finitely many names
- `Provenance.WinKept` – **a window kept as a window over an all-regular
  input**: a window reads the regular columns of its rows and nothing of
  the aggregate ones, its peers' tie-break included, so the window over
  a re-typed input is a different query. `AggQueryIn.winKept` writes it
  over the doubled input – each row prefixed by its nulled copy
  (`doubled`), the partition, order, term and clause moved to the first
  block (`castCols`, `TermIn.widen`, `Selection.widen`), the block then
  dropped – and `evaluatePlain_winKept` is the equality: the two listings
  of a frame, sorted by the clause with ties by the row, differ only in
  the order of rows with equal first blocks (`windowValueOpt_blockL`, off
  `readLe_blockL` and `OrderSpec.map_eq_of_sorted`)
- `Provenance.RecursionBasisPass` – **the pass over the whole algebra**:
  one structural induction (`exists_basisRec_aux`) in the manner of the
  union's pass, generalized over its target classes – any set holding
  the construction's six (`AggQueryIn.sumMuOps`) and not `⊎`, with the
  windows kept or derived and the set recursion kept or handed to a
  `MuSetHandler`. Every node is re-typed to regular columns
  (`AggQueryIn.allRegOf`, `toReg`) and rewritten by the local
  identities – a window kept over the doubled input (`winKept`) or, where
  the target has no `win`, written as `winByApply`, duplicate elimination
  as a grouping, the difference as the `NOT IN` form with its product
  written as an apply (`notInDiffA`), a product as an apply (`prodA`, or
  `prodSwap` when the recursive relation is on its right, the apply
  admitting it on the left only), a union through `exists_sumFree_aux` –
  with a second half for recursive bodies. The apply replaces `×` because
  the restriction on recursive terms admits an apply whose left side
  reads the recursive relation, which no decorrelation keeps. Its
  instance over the basis is `basisRecOps_generatesOnRec` in
  `Provenance.MuUnion`
- `Provenance.Genericity` – **a query of the minimal signature commutes
  with a faithful map**, and its counts are polynomially many: a map
  faithful on a set of values (`FaithfulOn`: nulls and the order
  preserved) that fixes the query's constants and the counts it computes
  (`AggQueryIn.countValsAll`) commutes with its evaluation
  (`AggQueryIn.evaluatePlain_faithful`), through every operator and both
  recursions, settling or not. The order type of a context over a finite
  set (`ordType`: each parameter's place among the set's values and
  whether it is one, and the parameters' pairwise comparison) yields such
  a map between two contexts of one type
  (`exists_faithful_of_ordType_eq`), so at an aggregating node the counts
  at a context are those at the representative of its order type
  (`AggQueryIn.countValsAll_subset`, the count types
  `AggQueryIn.countTypes` collecting them over a base set), and there are
  polynomially many order types (`card_ordType`), hence polynomially many
  count types (`AggQueryIn.exists_polyBound_countTypes`, `PolyBounded`).
  `AggQueryIn.exists_card_bound_muSet` is what `Provenance.MuUnion` needs:
  a set recursion's fixpoint, duplicate-free over the base set and the
  count types, has polynomially many rows in the number of values the
  recursion reads, which is what bounds the counter the simulation of a
  set recursion runs; the value lemma
  `AggQueryIn.valsIn_evaluatePlain` (every value of a result is read off
  the instance, the context or the constants, or is a count) is its
  first half
- `Provenance.WinRow` – **the window class is necessary**:
  `win_mem_of_generatesOnRec` says the window class is in every
  generating set over `ℕ` with the counting aggregate. The witness is
  `count(*) OVER (… EXCLUDE CURRENT ROW)` on `n` copies of one row
  (`winWitness`, `dRep`), which writes `n − 1`; the invariant (`sym_aux`,
  `ClosedSym`/`BodySym`) is that a window-free query of the minimal
  universe reads that family, for `n` past a threshold, as a bag of
  *polynomial shapes* (`Shape`, `PolyBag`: a multiplicity and a row of
  polynomials over `ℕ`, instantiated at `n`), its settling being decided
  by one bit. Two polynomials are eventually equal or eventually strictly
  ordered (`Poly.Cmp`, off their real asymptotics), so every comparison a
  predicate, a key or a duplicate elimination makes is decided at the
  threshold (`Decided`, `dedupAt`, `inst_eq_iff_shift`); a count is read
  symbolically (`count_onBag_eq_card`); and the recursions run their
  rounds on bags, the fixpoint index being read off the symbolic rounds.
  The polynomials a query can write are finitely many because the counts
  it reads are (`CountPolys`, off `Provenance.Genericity`'s bound), and
  `n − 1` is `X − 1`, which has no natural constant coefficient
  (`Poly.add_one_ne_X`)
- `Provenance.SelRow` – **the selection is the only operator reading the
  order**: `AggQueryIn.evaluatePlain_orderBlind` says a query with no
  selection, reading no aggregate column as a key (`noExplode`), in a
  signature with no function on values, commutes on its regular columns
  (`ColKind.readTuple`) with every injective map of the values fixing `0`
  and its constants, whatever the map does to the order – the
  faithfulness commutation of `Provenance.Genericity` with the order
  dropped. The windows and the ordered aggregations read the order into
  aggregate columns, which such a query never reads back. The witness
  `σ_{#1<#2}(S)` keeps `{(a, b)}` and not `{(b, a)}` (`ltWitness_breaks`),
  so no selection-free query expresses it (`ltWitness_not_expressible`),
  and `σ` is in every generating set whose produced queries read no
  aggregate column as a key (`sel_mem_of_generatesOnRecNoExplode`, against
  `GeneratesOnRecNoExplode`, the scope of the annotated classification)
- `Provenance.RoundBound` – **a bag recursion that settles does so
  within a bound read off its values**: a recursive term reads its hole
  once, so it is linear in the recursive relation
  (`AggQueryIn.bind_of_body`: a round is the previous round bound through
  a function of the row, plus what the term reads at the empty round); a
  row of round `j` ends a path of `j` steps from the base
  (`exists_path_of_mem_round`), a path over `V^m` longer than `|V|^m`
  repeats a row, and the segment between the two copies pumps a
  non-empty round past every bound (`mem_round_pump`). So a recursion
  that settles has an empty round at `|V|^m`
  (`bindStep_round_eq_zero_of_settles`) and is the sum of that many
  rounds (`AggQueryIn.mu_eq_muSum_of_valsIn`). This is what a bounded
  simulation of a bag recursion rests on – one that settles everywhere
  and agrees with the recursion wherever the recursion settles – which is
  what tabulating an apply's right side over a closed parameter relation
  needs, the table evaluating the right side at parameters the apply never
  reaches
- `Provenance.AnnotatedBasis` – **the basis of the annotated semantics,
  its statement and its inherited rows**: `GeneratesAnn T K sch cnt S`
  says every query of the whole algebra in the minimal universe reading
  no aggregate column as a key is matched over `S`, with the same kinds
  and no aggregate column read as a key, by a query whose annotated
  evaluation (`evaluateAnnotated`) settles and agrees with it on every
  `K`-instance at which the query's does (`AggQueryIn.AnnSettlesAt`, the
  per-instance settling of the annotated recursions, in
  `Provenance.AggQueryAdequacy`, whose data-part adequacy takes it).
  The settling of the recursions transfers both ways between the
  annotated evaluation and the plain evaluation of the stripped query
  (`settlesAt_stripAgg_of_annSettlesAt`; `annSettlesAt_of_settlesAt`
  for a `liftFaithful` query – no aggregate selection, no difference, no
  set recursion – at an instance annotated `𝟙`, `Database.liftOne`), so a
  set generating the annotated algebra over any `K` generates every
  faithful query plainly (`generatesAtNoExplode_of_generatesAnn`), which
  every witness of the plain rows is: `∅`, `Π`, `γ`, `μ^⊎`, `win`, `σ`
  and one of `×`/apply are in every such set
  (`required_mem_of_generatesAnn`), the selection row holding outright
  since the alternatives are out of the language. The trivial generating
  set is every class (`generatesAnn_plainRecOps`); `GeneratesAnn.mono`
  carries generation to supersets
- `Provenance.AnnotatedDedup` – **`ε` is dispensable in the annotated
  algebra**, the first non-trivial sufficient half of the annotated
  classification: `ε(q) = μ^∪s.(q, σ_false(s))` exactly in every
  commutative m-semiring (`evaluate_dedupMu`: the first round is the
  deduplication, the term keeps nothing of the round, the iteration
  settles at the second round, `annSettlesAt_dedupMu`), and the pass
  `dedupFree` replaces every `ε` by that recursion under a fresh name,
  changing no annotated evaluation (`evaluate_dedupFree`), settling
  wherever the query does (`annSettlesAt_dedupFree`) and keeping the
  classes, the signature, the hygiene and the well-formedness. So the
  classes other than `ε` generate the annotated algebra
  (`generatesAnn_dedupFree`)
- `Provenance.AnnotatedProd` – **`×` is dispensable in the annotated
  algebra** too: a product is the apply of its left factor with its right
  factor read under the ambient context (`evaluate_prodApply`, exactly),
  an apply's left side carrying aggregate columns as freely as a
  product's factor does. Where a recursive term's hole is in the right
  factor, which an apply's right side cannot hold, the factors are
  swapped and the columns put back by a projection (`finEq_prodSwap`),
  which cashes some pending group factors and so agrees with the product
  only up to finalization: the same rows, columns and finalized
  annotations (`AggQueryIn.FinEq`), a relation every operator respects
  (the congruences `AggQueryIn.FinEq.proj` … `winExpr`, the selection on
  an aggregate value through `GenAnn.finalize_sel`) and all that the
  annotated evaluation reads. The pass `prodFree` keeps the classes, the
  signature, the well-formedness and the kinds (`AggQueryIn.wellKinded`),
  so the classes other than `ε` and `×` generate the annotated algebra
  (`generatesAnn_dedupProdFree`)
- `Provenance.AnnotatedSum` – **`⊎` is dispensable in the annotated
  algebra** as well: `q₁ ⊎ q₂` is two bag recursions over one driver row
  (`AggQueryIn.sumByMuK`), the first listing `q₁`'s rows behind the
  driver, the second adding `q₂`'s, each round re-tagging an operand's
  rows; the operands may carry aggregate columns, a round of a bag
  recursion being bound in the evaluation's environment, and the driver
  row's aggregate columns hold a padding token that the construction
  drops (`evaluate_sumByMuK_fin`, up to finalization). A `⊎` on the
  recursive path of a body cannot be replaced where it stands, so the
  pass splits such a body into a body and a closed query
  (`AggQueryIn.exists_sumFreeAnn_aux`): at a bag recursion that settles
  the closed part is empty (`mu_of_splitAnn`), at a set recursion it
  moves into the base (`muSet_of_splitAnn`). So the classes other than
  `ε`, `×` and `⊎` generate the annotated algebra
  (`generatesAnn_dedupProdSumFree`)
- `Provenance.PathSum` – **linear recursions over a semiring, read path by
  path**: the iterates of a set recursion `X ↦ ε(B ⊎ X ⊳ G)` are `ε` of the
  truncated sums of its bag rounds (`iterate_stepK_eq`), a round's weights
  are path sums (`y_eq_sum_pathsTo`), and a recursion that settles does so
  within the size of a tuple set closed under its rounds, where the
  semiring is absorptive or cancellative without zero divisors
  (`iterate_succ_eq_of_settles`, and `wt_trunc_settle` on the tuples the
  derivations of non-zero weight live on), and its weights within twice
  that size where `⊗` is `⊕` on non-zero values, as in the lineage
  semiring (`PathSum.UnionLike`, `wt_trunc_settle_lin`); a successor counter over the
  counters annotated `𝟙` pairs each derivation with exactly one counter
  (`SimSpec.dedupK_rounds`),
  and in an absorptive semiring an all-chains counter whose chains absorb
  nothing of the derivations they are paired with gives the same value
  (`ChainSpec.dedupK_rounds`)
- `Provenance.AnnotatedMuUnion` – **`μ^∪` from `μ^⊎` and `ε` in the
  annotated algebra, the construction**: duplicate elimination applies no
  `δ`, so the simulation of `Provenance.MuUnion` carries over once its
  counter neither multiplies nor repeats derivations – a *successor*
  counter, computed by a difference, whose rows are annotated `𝟙` or `𝟘`
  (`AggQueryIn.simResultA`, `evaluate_simResultA`), or an *all-chains*
  one; the pass replacing every set recursion is `AggQueryIn.muSetFreeA`,
  correct wherever its node is (`muSetFreeA_correct`), and composed with
  the passes for `×` and `⊎` the classes `{∅, Π, σ, apply, γ, win, μ^⊎, ε, −}`
  generate the annotated algebra there (`generatesAnnOn_annEpsOps_of`)
- `Provenance.AnnotatedChains` – **the two nodes, over every instance**:
  every row holding a value is within any bound the operators keep
  (`AggQueryIn.rowBd_evaluate`); where `δ` is the support map, a value held
  only by rows annotated `𝟘` makes every row holding it `𝟘`, so the
  successor counter is exact with no fence on the instance, in the
  semirings of `PathSum.SettlesLinear` (`AggQueryIn.muSetSim_correct_succ`,
  `generatesAnn_annEpsOps_of_support`); where `δ` is the identity (the
  Boolean algebras and the min-max semirings), a row is below the weight of
  each value it holds, so the *all-chains* counter absorbs nothing of a
  derivation through distinct tuples (`AggQueryIn.muSetSim_correct_chain`,
  `generatesAnn_annEpsOps_of_delta_id`)
- `Provenance.AnnotatedDiffRow` – **`−` is necessary in the annotated
  algebra**: over `ℕ × ℕ` (`NatPair`), every annotation a query without a
  difference builds – a row's, its tokens' occurrences', a predicate's
  provenance – is zero in one coordinate exactly where it is in the other,
  that being kept by every operator but the difference
  (`annIn_evaluate`, for any property `AnnClosed`
  describes), and `R − S` gives `(0, 1)` (`diff_mem_of_generatesAnn`)
- `Provenance.AnnotatedEpsRow` – **`ε` or `μ^∪` is necessary in the
  annotated algebra**: over `ℕ`, without them every annotation a query of
  the minimal signature builds is at most `𝟙` when the instance's are
  (`le1_evaluate`) – the joint reading of a selection weighs its worlds at
  most `𝟙` together (`GenPredIn.predsemJ_le_one`) – and `ε` of a relation
  holding one tuple twice gives `2` (`dedup_or_muSet_mem_of_generatesAnn`);
  with the other rows, no proper subset of `{∅, Π, σ, apply, γ, win, μ^⊎,
  ε, −}` generates over both `ℕ` and `ℕ × ℕ` (`annEpsOps_minimal`)
- `Provenance.AnnotatedBasisClass` – **the annotated basis theorem over a
  class of semirings**: `{∅, Π, σ, apply, γ, win, μ^⊎, ε, −}` generates
  the annotated algebra over every m-semiring where `δ` is the support map
  and linear set recursions settle within twice the size of their tuple
  set – `ℕ`, `ℕ[X]`, the lineage semiring among them – or `δ` is the
  identity (`AnnBasisClass`), and no proper subset does over all of them
  (`annEpsOps_isBasis_in_class`); the difference's witness inside the class
  is `ℕ[x, y]`, where `R − S` gives `x` and no difference-free query builds
  an annotation with more `x` than `y` (`diff_mem_of_generatesAnn_xy`)
- `Provenance.AnnotatedBasisHom` – **the basis theorem's matches commute
  with homomorphisms**: the construction reads no annotation, so one query
  over the nine classes serves every semiring where its counter simulates a
  set recursion (`exists_annEpsOps_matchU`), and it commutes with every
  homomorphism the source commutes with, wherever the source settles on
  both sides (`exists_annEpsOps_match_hom`, with the support and the
  `δ = id` classes as `_support` and `_delta_id`); nothing is asked of the
  match's own labels or read sets
- `Provenance.AnnotatedApproxRows` – **the necessity rows up to `≈`**,
  rows annotated `𝟘` and occurrences annotated `𝟘` dropped
  (`GeneratesAnnZ`): the rows inherited from the plain basis transfer
  through the Boolean support over `𝔹`, where `≈` keeps the realized world
  and the realized world evaluates plainly
  (`generatesAtNoExplode_of_generatesAnnZ`, with
  `AggQueryIn.settlesAt_randomWorld`), the others keep their witnesses'
  rows; with the positive half, the nine classes are a basis up to `≈`
  over the class (`annEpsOps_isBasis_in_class_approx`)
- `Provenance.AnnotatedApplyRow` – **the apply row up to `≈` with occurrence
  identity**. Ordinary tokens carry the identities of their occurrences
  (`AggValue.oids`, stamped by the grouping and the window), and
  `GenRow.zeqRen` compares results up to `≈` with a one-to-one renaming of
  them, which keeps which aggregate values share which occurrences; aggregate
  expressions carry identities too (`AggExpr.oids`), and so do the
  expressions a nested value reads at every storey, the nested values
  themselves being compared through their families, renamed;
  `GeneratesAnnRen` is the generation predicate up to it. Over Boolean
  functions of two variables a set generating up to it holds the apply
  (`apply_mem_of_generatesAnnRen`): `R ⊳ γ_∅[count](σ_{#1 < u}(S))` gives
  each parameter its own occurrence annotated `y`, while without an apply
  the ordinary tokens holding an occurrence annotated `y` are hit by a set
  of identities bounded by the query (`AggQueryIn.exists_hit`). With it, the
  annotated basis theorem holds up to `≈` with occurrence identity over the
  class (`annEpsOps_isBasis_in_class_ren`): the constructions agree with
  their source row by row, identities included, the rows up to `≈` by value
  transfer (`GeneratesAnnRen.toGeneratesAnnZ`), and no set of classes
  generates without the apply, a product included
- `Provenance.AnnotatedWhyRow` – **the annotated basis theorem: set
  recursion is required**. `{∅, Π, σ, apply, γ, win, μ^⊎, −, μ^∪}`
  generates the annotated algebra over every commutative m-semiring, and no
  proper subset of it does over all of them (`annMuOps_isBasis`). `μ^∪`'s
  row is over the why-provenance semiring (`muSet_mem_of_generatesAnn`): on
  a family of instances sharing their data, a query without `μ^∪` keeps its
  annotations within one grade – witnesses of boundedly many variables
  (`Graded`, `AggQueryIn.exists_grade`) – while a set recursion over an edge
  carrying `m` one-variable witnesses builds one of `m`. So over `Why[X]`
  the set with `ε` in place of `μ^∪` does not generate
  (`not_generatesAnn_annEpsOps_why`). The same holds up to `≈`, nested
  aggregation included (`annMuOps_isBasis_approx`,
  `muSet_mem_of_generatesAnnZ`)
- `Provenance.MuUnion` – **`μ^∪` from `μ^⊎`** (`basisRecOps_generatesOnRec`, for
  every restricted term): a set recursion is simulated by a bag
  recursion over pairs of a tuple and a counter, the base `(q₀ ⊎ C) × E^K` and each
  round applying the term to the tuple part and moving the counter to
  every larger one in the lexicographic order of `E^K` (`AggQueryIn.sim`,
  `simResult` = its tuple parts without duplicates).
  `evaluatePlain_simResult` is the correctness, under `|F| ≤ |E|^K` for
  the fixpoint `F` and a counter relation `E` of non-null values, and
  `settlesAt_simResult` the definedness. The counter relation is
  computed (`counterRel`): the columns of the base, of the relations the
  recursion reads, its constants and the context, with two constants of
  the domain, the non-null rows kept by `x = x`; its width `K` is fixed by
  the query, off `AggQueryIn.exists_card_bound_muSet` of
  `Provenance.Genericity`, which bounds the fixpoint by a polynomial in
  the number of values the counter runs over. The pass of
  `Provenance.RecursionBasisPass` threads the schema; where the target
  holds no `μ^∪` it calls `MuSetHandler`, which `muSetHandler` proves for
  any target holding the union's basis, and `basisRecOps_generatesOnRec`
  is the generation statement: `basisRecOps` = `{∅, Π, σ, apply, γ, win,
  μ^⊎}` generates the whole algebra in the minimal universe
  (`GeneratesOnRec`), with `sumMuOps_generatesOnRec_of_winsDerivable`
  dropping `win` for derivable windows. So `μ^∪` is in no basis of the
  whole algebra in that universe
- `Provenance.RecursionBasisTheorem` – **the classification of the whole
  algebra in the minimal universe, in one place**: `basisRecOps_isBasis`
  says `basisRecOps` generates over every schema
  (`generatesOnRec_of_basisRecOps_subset` extends that to every superset,
  off `GeneratesOnRec.mono`) and that no proper subset does
  (`basisRecOps_minimal`), the rows gathered as
  `required_mem_of_generatesOnRec`: `∅`, `Π`, `γ`, `μ^⊎`, `win`, one of
  `σ`/`−` and one of `×`/apply are in every generating set over `ℕ` with
  the counting aggregate. `−` for `σ` and `×` for the apply each give a
  further basis (`basisRecDiffOps_isBasis`, in `Provenance.DiffBasis`, and
  `Sym.basisProdOps_isBasis`, in `Provenance.SymPass`), and the two
  together do not (`Provenance.RecursionBases`)
- `Provenance.SumByProd` – **`⊎` and `−` with products**: `sumByMuX` is
  `sumByMu` with each round's apply written as the product it stands for,
  and `notInDiffX` the `NOT IN` difference over it, both over the classes
  `{∅, Π, σ, ×, γ, μ^⊎}`
- `Provenance.SymCode`, `Provenance.SymCells`, `Provenance.SymRel`,
  `Provenance.SymTerms`, `Provenance.SymOps`, `Provenance.SymGamma`,
  `Provenance.SymWin`, `Provenance.SymMu`, `Provenance.SymTab`,
  `Provenance.SymCorrect`, `Provenance.SymOrder`, `Provenance.SymEnvBuild`,
  `Provenance.SymCut`, `Provenance.SymSettle`, `Provenance.SymMatch`,
  `Provenance.SymApply`, `Provenance.SymStruct`, `Provenance.SymOver`,
  `Provenance.SymPass` –
  **evaluating a query at the types of its parameter row**: a parameter
  value is coded relative to a finite cut of values (a value of the cut,
  or a gap with a rank, `Sym.code`), equal codes standing for equal values
  and the order of codes being the order of values (`Sym.Code.lt_iff`);
  a code is stored in `7 + k` columns, and a comparison of two cells has
  the three-valued truth of the comparison of their values
  (`Sym.eval3_cellCmp`). A symbolic relation holds, under the descriptor
  of each parameter row, the encodings of the rows the query computes
  there (`Sym.SliceIs`); projection, selection, join, the leaves and the
  grouping map these slices (`Sym.sliceIs_symProj`, `sliceIs_symSel`,
  `sliceIs_joinL`/`R`, `sliceIs_leaf`, `gammaRows_slice`), and so do the
  windows (`Sym.sliceIs_symWin`) and a bag recursion run against a list of
  counters (`Sym.sliceIs_symMu`). `Sym.sym` assembles the symbolic
  evaluation of a query, and `Sym.sym_correct` says it is correct wherever
  the values the evaluation reads are good and the environment provides
  enough counters. The environment is built from a cut by products,
  selections, projections and the `NOT IN` difference (`Sym.envOf`, sound by
  `Sym.envOK_envOf`), and the cut of a query is defined by recursion, each
  aggregation adding the values its symbolic counterpart computes at the cut
  of its input (`Sym.cutQ`); `Sym.tabQ_correct` puts the two together, and
  the table settles on every instance, its recursions bounded by counters
  (`Sym.settlesAt_tabQ`). An apply is then a product of its left side with
  the descriptors, the table and a pool of values, a row's own descriptor
  being picked by a predicate that holds of it alone (`Sym.eval3_matchSP_true`)
  and the table's cells read back as values (`Sym.eval3_decCell_true`):
  `Sym.evaluatePlain_applyX`. The constructions stay in the fragment
  (`Sym.fine_applyX`) and are well formed over the schema
  (`Sym.over_applyX`). Run from the leaves up through a query over
  `{∅, Π, σ, apply, γ, win, μ^⊎}` (`Sym.exists_prodPass_aux`), with each
  apply's pool a closed query holding its left side's values – inside a
  recursive term, the values of the base and those the term creates – this
  gives **`Sym.basisProdOps_generatesOnRec`: the product in place of the
  apply, `{∅, Π, σ, ×, γ, win, μ^⊎}` generates the whole algebra** in the
  minimal universe, and with the rows of `required_mem_of_generatesOnRec` it
  is a basis there (`Sym.basisProdOps_minimal`, `Sym.basisProdOps_isBasis`)
- `Provenance.DiffBasis` – **the difference in place of the selection**:
  `basisRecDiffOps_generatesOnRec` says `{∅, Π, −, apply, γ, win, μ^⊎}`
  generates the whole algebra in the minimal universe, and
  `basisRecDiffOps_isBasis` that it is a basis there. A selection becomes an
  apply of its input with a closed test holding the empty tuple once where
  the predicate is true at the row (`DiffBasis.selX`,
  `DiffBasis.evaluatePlain_selX`); the test is built by induction on the
  predicate in Kleene's logic, true and false together (`DiffBasis.predTF`),
  the connectives and the equalities from the difference alone. The order
  is read by a window: over `{a, b}`, a bag recursion of one round
  (`DiffBasis.pairZ`), the row of `b` counts the rows strictly before it,
  and that count is compared with `0` as a key (`DiffBasis.ltT`,
  `DiffBasis.evaluatePlain_ltT`). Reading the count as a key is what
  `Explode` does, which `usesOnly` charges to no class; without it `σ` is in
  every basis (`sel_mem_of_generatesAtNoExplode`)
- `Provenance.RecursionBases` – **all the bases of the whole algebra in the
  minimal universe**: a recursive term reads its recursive relation under a
  projection, a selection, a product, the left side of an apply, a union,
  `Explode` and `Retag`, and only the selection and the apply drop a row.
  Without them a round has `k · |X|` rows for a `k` the round does not
  change, so a bag recursion that settles is its base
  (`AggQueryIn.evaluatePlain_mu_degenerate`, `AggQueryIn.exists_dropMu`),
  the answers are polynomial, and the chain of diamonds gives the row
  `sel_or_apply_mem_of_generatesOnRec`. So `{∅, Π, −, ×, γ, win, μ^⊎}` is
  not a basis (`not_generatesOnRec_prodDiff`), and `generatesOnRec_iff`
  says a set of classes generates the whole algebra over `ℕ` with the count
  exactly when it holds `basisRecOps`, `Sym.basisProdOps` or
  `basisRecDiffOps`
- `Provenance.RecFreeBasis` – **the bases of the recursion-free algebra in
  the minimal universe**: `GeneratesOnRF` is the generation of every query
  with no recursion, and `generatesOnRF_iff` says that among class sets with
  no recursion the generating ones over `ℕ` with the count are exactly the
  supersets of `∅`, `Π`, `⊎`, `γ`, `win` with `σ` or `−` and with `×` or the
  apply – all four pairings, each minimal (`rfSelApplyOps_minimal` and its
  three siblings). The rows are the whole algebra's at its recursion-free
  witnesses, `⊎` added (`union_mem_of_generatesOnRF`). The positive halves
  run a recursion-free pass (`AggQueryIn.exists_rfPass`) that keeps `⊎`,
  keeps `×` or `−` where the target has them, and keeps a selection, where
  the target has no `σ`, by its test from `Provenance.DiffBasis` decorrelated
  over the distinct rows of its input (`AggQueryIn.exists_selByTest`). The
  `×` bases first remove the applies by the decorrelation of
  `Provenance.Decorrelate`, which stays in the signature for queries whose
  parameter leaves are regular (`AggQueryIn.exists_applyFree_plainEquiv_sig`,
  `AggQueryIn.paramsReg`) and asks `σ` and `ε` only of a product or an apply
  (`AggQueryIn.hasDecorrelation_of_usesOnly_gen`). Recursion-free, `{−, ×}`
  is a basis; with recursion it is not (`not_generatesOnRec_prodDiff`)
- `Provenance.WindowPartition` – **a window over a whole partition is a join
  with its grouping**: `AggQueryIn.winByJoin` writes it without a window – join
  the query with its own grouping on the partition key with `≐`, the
  syntactic equality a window partitions by, and keep the group's aggregate
  column – and `evaluatePlain_winByJoin`, `evaluate_winByJoin` prove
  the two agree over plain and over annotated relations. The plain statement
  is a rearrangement; the annotated one is not, since the join carries the
  group's existence factor `δ(⊕ U)` that a window never produces. The two
  agree only because the group of a row *contains that row*, so the factor
  reads `α ⊗ δ(α ⊕ β')`, which is `α` by δ-absorption – a frame excluding the
  current row would have no such identity and no such rewriting. The
  combinatorial step is `filter_product_key`: a table with distinct keys,
  joined on the key, gives each row exactly the entry of its own key
- `Provenance.ReadsCongr` – **an evaluation reads its context only where
  it says it does**: under `AggQueryIn.readsRecorded`, two valuations of
  the parameters and two environment contexts agreeing on the positions
  the query reads give the same annotated evaluation
  (`AggQueryIn.evaluate_congr_reads`), terms, predicates and the
  operators' value builders read the parameters only through their terms
- `Provenance.JointHom` – **the joint reading of a family under a
  homomorphism**: a `LeafSpec` says how an aggregate value reads an
  occurrence of its family as a function of the occurrence's row, a value
  built from a listing by one is read off the rows a world selects
  (`classWorlds_presented`), and two listings related by a tie-block
  permutation give corresponding worlds for every value built from them
  together (`classWorlds_hom`); a nested family is read off two values
  whose worlds correspond one by one, the kept product and the absent sum
  pushed through the hom (`NestedValue.WCorr`, `classWorlds_of_wcorr`); a
  row whose families correspond family by family has corresponding joint
  worlds (`jointWorlds_hom`), in particular one whose families are
  presented on both sides (`FamPres`, `jointWorlds_of_famPres`)
- `Provenance.NestedPres` – **nested values under a homomorphism, at
  every storey**: two nested values built from related rows are related
  family by family (`NestInner.Rel`: an expression family presented on
  each side by listings a tie-block permutation apart, a node's
  occurrences paired with their annotations pushed through the hom), and
  where related families share a key on one side exactly when they do on
  the other (`KeysFaithful`, which a coherent evaluation gives) their
  worlds are the images of one bag of decisions, each family and each
  node decided once (`wcorr_of_rel`)
- `Provenance.Coherence` – **one family identifier, one value, across
  every evaluation a query performs** (`AggQueryIn.builds_coherent`): the
  aggregate values the operators build – once per row of an apply's left
  side, once per round of a recursion – and the terms over them carry one
  value per identifier, for a query whose operators record what they read
  (`readsRecorded`), carry distinct labels (`labelsDistinct`), apply no
  arbitrary function to an aggregate value (`sourceCols`) and use frames
  containing the current row (`allFramesContainSelf`). The induction is
  on the identifier's size: an operator's identifier records its
  parameters', and equal parameters make equal inputs
  (`AggQueryIn.coh_node`)
- `Provenance.AggQueryBridges` – **the fused `HAVING` site in closed
  form**: `AggQueryIn.havingSite` is one aggregate comparison directly above
  the grouping, and `AggQueryIn.havingSite_evaluateAnnotated` computes it
  – one row per group key, annotated by `Having.havingProv` – since the
  pending group factor is superseded by the token's predicate provenance
  (`AggValue.predProv_ofGroup`) and the data part collapses to the
  whole-group aggregates. The fused site is thereby a theorem about the
  single annotated evaluator, not a semantics of its own. The file also
  records the opposite regime: a predicate whose compared tokens carry
  two different groups supersedes nothing, so both group factors stay
  pending and are cashed into the row
  (`AggQueryIn.evaluate_Sel_of_two_groups`, and
  `AggQueryIn.evaluate_Sel_or_of_two_groups` for the disjunction the
  `∨` rule is about), and that a projection dropping no token column a
  pending factor belongs to leaves both parts of the annotation alone
  (`AggQueryIn.evaluate_Proj_of_pending_le`) – so such a projection
  standing inside a chain of aggregate selections changes neither the
  families read nor the annotation built. It also carries **equality up
  to impossible rows**: `AnnotatedRelation.dropZero` removes the tuples
  annotated `𝟘`, which are in no world, `ZEq` is equality after that,
  and `AggQueryIn.evaluate_Sel_reg_absorb` says a regular selection may
  be absorbed into the aggregate predicate below it in exactly that
  sense and not as an equality of relations – a selection with an
  aggregate atom keeps its failing rows annotated `𝟘` where a regular
  one removes them
- `Provenance.Normalize` – **reading a chain of selections as one
  predicate**. Under the joint reading `σ_{ψ₁ ∧ ψ₂}` is one sum where
  `σ_{ψ₁} ∘ σ_{ψ₂}` is a product of two, and they agree only where the
  conjunction decomposes, so the two spellings of what a SQL user calls
  one query part would differ – `4` against `2` over `ℕ`
  (`natRangeToken_mul_ne_and`). `AggQueryIn.normalize` merges adjacent
  selections, a query being read as `evaluate (normalize q)`, and
  `normalize_chainFree`, `normalize_id_of_chainFree` and
  `normalize_idem` say the result has no selection above a selection,
  that normalizing a normal form changes nothing, and that the pass is
  idempotent. The equality it buys is up to impossible rows and not of
  relations (`AggQueryIn.evaluate_Sel_reg_absorb`), since merging a
  regular selection keeps the rows it would have removed, annotated
  `𝟘`. Where both predicates read
  one family on a row (`GenPredIn.ReadsOne`), the pending parts of the
  chain and of the merge agree with nothing asked of `K`: each supersede
  test reduces to “drop that family's factor”
  (`Having.supersede_test_iff`), and dropping it twice is dropping it
  once
- `Provenance.Alternatives` – **aggregate columns read as keys**, the
  operator being `AggQueryIn.Explode` in `Provenance.AggQuery`: it replaces
  each occurrence by its alternatives and makes the column regular, so
  a `GROUP BY` on a count or a `DISTINCT` on an aggregate can be
  written at all – every key-comparing operator takes regular columns.
  Over a plain relation an aggregate value is a value and `Explode` is the
  identity. It is **world-faithful**: under a valuation exactly one
  alternative survives, the one whose value the column has in that
  world, and it specializes to what the occurrence specializes to, so
  the random-world commutation covers it. It is **not** data-part
  adequate, and cannot be: it gives one row per value the column takes
  in *some* world, so `AggQueryIn.evaluateAnnotated_toPlain` carries the
  hypothesis `AggQueryIn.noExplode`. It **commutes with homomorphisms**
  (`sim_alternativesAt`), since the values a token takes
  survive both the pushforward (`AggValue.vals_mapAnn`) and tie-block
  equivalence (`AggValue.vals_congr`) – both because `AggValue.vals`
  reads the occurrences only through their values
  (`AggValue.vals_eq_valsOf`). `Explode` is outside the (R1)–(R5)
  fragment. **Several** aggregate columns compared as one key ask for a
  single atom on the tuple of values rather than two atoms conjoined.
  The two coincide where the columns come from *different groupings*,
  whose families are disjoint, `K` being complemented
  (`Having.jointPair_and`, `Having.altProvPair_eq_mul`). They do not
  where the columns come from one grouping: two aggregates of one group
  are one family (`AggValue.annList_ofGroup`), reading them as two
  independent ones counts a world once per half, and over `ℕ` that is
  `4` against `2` (`natRange_jointPair_ne`). So the tuple atom is a
  definition, coinciding with the column-by-column reading only across
  groupings. `Having.jointPair_self_eq_mul` makes the coincidence a
  theorem: reading one family as two independent halves *is* the
  column-by-column product, so a range atom against its two bounds, two
  selections against one on their conjunction, and two key columns
  against the atom on their tuple are the same identity, failing
  together at `4` against `2` or not at all. An
  operator that compares a key reads an occurrence whose column holds
  an aggregate value through its *alternatives*, one per value the
  column takes: `(u[i ↦ v], α ⊗ [a ≐ v])`, where
  `AggValue.altProv` is `[a ≐ v]`, the predicate provenance of the
  atom `a = v` under SQL's null-safe equality – so the case `v = NULL`
  is the atom `a IS NULL` and needs no clause of its own.
  `AggValue.worlds` and `AggValue.vals` are the worlds and the values
  they take, `predProvOfWith_eq_sum_worlds` says the two reading
  conventions differ only in which subfamilies count, and
  `GenRow.alternativesAt` is the reading of an occurrence, whose column
  an alternative makes regular (`alternativesAt_reg`). Two facts make
  it a reading of the worlds rather than an enumeration of values:
  `AggValue.sum_altProv`, the alternatives' shares add up to what the
  worlds carry, so nothing is lost or invented; and
  `AggValue.altProv_mul_eq_zero`, **distinct alternatives exclude each
  other where `K` is exclusive**, since distinct values come from
  distinct worlds – the remark that in `𝔹[X]` exactly one alternative
  of a present occurrence holds under each valuation, and that over
  `ℕ[X]` an operator combining two alternatives of one occurrence
  counts worlds that do not exist
- `Provenance.AggQueryProbability` – **the random-world commutation for
  the general evaluator** over `𝔹[X]`:
  `AggQueryIn.genRandomWorld_evaluate` – specializing the realized rows
  of the general annotated evaluation is the plain evaluation of the
  realized world (`genRandomWorld v (q.evaluate d) =
  q.evaluatePlain (d.randomWorld v)`), for arbitrary queries with
  aggregate comparisons anywhere. Built from the token-level PQE bridge
  (`AggValue.predProv_eval_iff`), the predicate-provenance evaluation
  under existence guards (`GenPredIn.predsem_eval_iff`, with `¬` handled by
  polarity), the existence-entailment extraction
  (`GenPredIn.entails_guard`), the σ-aggregate row lemma
  (`GenPredIn.sel_finalize_eval_iff`), and the conformance and guardedness
  invariants of the evaluator (`evaluate_conform`,
  `evaluate_guarded`). A window commutes for the reason it was built to:
  restricting the relation to a world restricts every frame to that world,
  so the token reads as the plain aggregate the world's relation gives its
  row (`tokenOf_specialize`). Its token is guarded by the row it is computed
  for whenever that row is in its own frame, and scalar – so exempt – when
  it is not. As corollaries, **unrestricted probabilistic
  query evaluation**: `AggQueryIn.boolean_pqe` (the probability that a
  random world has a non-empty answer is the probability of the query's
  Boolean provenance, the `⊕`-sum of the rows' finalized annotations) and
  `AggQueryIn.tuple_pqe` (the marginal probability of an answer tuple, for
  all-regular outputs) – both for arbitrary queries with aggregate
  comparisons anywhere, removing the top-level restriction of the fused
  `booleanHaving_pqe`
- `Provenance.AggQueryHom` – hom commutation for the general evaluator,
  token and annotation layer: the finalized factored annotation
  (`GenAnn.finalize_mapHom`, through `map_delta`), the predicate
  provenance of a token comparison (`AggValue.predProv_mapAnn`) and of a
  whole generalized predicate (`GenPredIn.predsem_mapAnn`) commute with
  every `SemiringWithMonusHom` –
  the `⊕`/`⊗`/`⊖`/`δ`-polynomial content of “compile once, evaluate
  many”. The evaluator-level commutation
  (`AggQueryIn.evaluateAnnotated_hom`) asks nothing of the hom and holds
  over every m-semiring, asking of the query that every window frame
  contain its current row (`allFramesContainSelf`) and that a family
  identifier
  determine its value across the evaluation – distinct labels, recorded
  parameters, no arbitrary function on an aggregate value
  (`labelsDistinct`, `readsRecorded`, `sourceCols`), under which each
  family is presented once for the whole evaluation (`ClassPres`,
  `AggQueryIn.evaluate_hom_univ`): the guard-absorption
  identities licensed by `delta_absorb`
  (`AggValue.predProv_delta_absorb`, `GenPredIn.predsem_delta_absorb`)
  neutralize the supersede decisions a non-injective hom can conflate,
  the group-sequence transport (`havingGroup_tiePerm`,
  `ofGroup_predProv_hom`, `havingGroup_annSum_hom`) neutralizes the
  `≼`-tie-break of `havingGroup`, and a row-wise simulation
  (`GenRow.Sim`, `AggQueryIn.evaluate_hom_rel`) carries both through
  the evaluator. A window's frame is carried unchanged, being read off the
  values; what the pushforward moves is only the order inside a block of
  equal tuples, which `sortList_hom_tiePerm` and `tokenOf_mapAnn_tiePerm`
  render invisible exactly as for a group. A *nested* column is related
  family by family (`NestInner.Rel`): both sides' world enumerations are
  images of one index bag, with products and absent sums pushed through
  the hom (`NestedValue.WCorr`, from `wcorr_of_rel` under
  `KeysFaithful`, which `keysFaithful_of_homUniv` supplies), so its world's
  weight, one monus over every storey, is carried with nothing asked of
  the semiring
- `Provenance.QueryToAgg` – the embedding of the classical query
  syntax into the general evaluator: `Query.toAgg` translates the
  non-aggregating fragment one to one over all-regular kinds, faithfully
  (`Query.toAgg_bridge` and, at the raw row level,
  `Query.toAgg_evaluate_eq`, via the row invariant `GenRow.Inv`); the
  fused `HAVING` site over an embedded subquery reads its input relation
  off the classical one (`Query.toAggHaving_input`). The module sits
  *below* the classical `HAVING` correctness files, so those state their
  theorems over the embedded general query with no side hypothesis
- `Provenance.AggQueryEmbedding` – the compositional JOIN rewriting,
  stated natively on the general syntax: `GenCountHavingRewrite` replaces
  `HAVING COUNT(*)` sites – key projections of `σ_ψ ∘ Gamma`, all-regular
  and hence composable under every operator – by the embedded padded join
  query, and `GenCountHavingRewrite.evaluateGen_eq` proves the
  replacement preserves the general evaluator's rows verbatim; the
  expressible contexts around a site are exactly the ProvSQL-legal ones,
  the kind discipline forbidding deduplication, difference and
  re-grouping over aggregate values just as the system does
- `Provenance.AggQueryRewriting` – **the provenance-aware rewriting,
  natively on the general syntax**: the rewritten column layout
  `ColKind.rewKinds` (`n` regular data columns plus one provenance
  column), the fragment predicate `AggQueryIn.classical`, and the rewriting
  `AggQueryIn.rewriting` mirroring the classical rules – with
  deduplication and difference expressed through the native `ProvSum`
  aggregation of provenance columns and the `Retag` cast
- `Provenance.AggQueryStrip` – the strip of the classical fragment back
  to the classical `Query` syntax (`AggQueryIn.strip`) and its
  faithfulness `AggQueryIn.strip_bridge`, through the row invariant
  `GenRow.Inv`
- `Provenance.AggQueryRewritingValid` – **correctness of the native
  rewriting**: the plain-semantics agreement `AggQueryIn.rewriting_plain`
  of the two rewritten queries, and `AggQueryIn.rewriting_valid`, which
  states that the annotated semantics folded into composite `T ⊕ K`
  tuples agrees with the plain evaluation of the rewritten query
- `Provenance.AggQueryHavingRewriting` – **the rewritten world's
  evaluator, with tokens as ordinary column values**: rewritten
  queries run over rows `Tuple (GenValue (T ⊕ K) K) n`
  (`AggQueryIn.evaluateRew`), where the token-building grouping `GammaTok`
  is ProvSQL's `provsql_agg` (explicit annotation term, group guard
  `δ(⊕ occs)` in the `prov` output column) and the two term gates are
  interpreted by their primitives (`TermGIn.evalRew`): `TermGIn.cmpAgg` is
  `provsql_having`, read by `AggValue.predProv`, and `TermGIn.chiGate` is
  the regular-atom indicator, read by `Having.chi`. Off the token
  operators and the indicator gate the evaluator is the plain semantics
  through the `inl` embedding (`AggQueryIn.evaluateRew_plain`, under
  `AggQueryIn.noGammaTok` and `AggQueryIn.chiFree`), connecting it to the
  classical rewriting correctness – the classical rewriting stays inside
  that fragment (`AggQueryIn.rewriting_chiFree`). `AggQueryIn.rewriting_provRel` reads a rewritten
  evaluation back as an annotated relation – the input the token-building
  groupings consume – and `Having.havingGroup_toComposite` transports the
  group sequence along the composite embedding; the rewriting rules built
  on top live in `Provenance.AggQueryGroupRewriting` and
  `Provenance.AggQueryClosure`
- `Provenance.AggQueryGroupRewriting` – **the bare-grouping rewriting**, the
  general framework's counterpart of rule (R5): a `GROUP BY` whose
  aggregate columns flow onward as output values, rather than being
  consumed by a comparison gate. No new value domain is needed – the
  rewritten world already has tokens as column values – but the
  correspondence must be stated at token level, since the composite
  embedding of an annotated relation reads tokens through their
  deterministic collapse. `GenRow.toCompositeRow` is the token-aware
  embedding (`AggValue.toComposite` on token columns, the finalized
  annotation appended as the provenance column), agreeing with the old
  embedding on token-free rows (`GenRow.toCompositeRow_of_reg`);
  `AggQueryIn.gammaRew` is the rewritten grouping (`GammaTok` over the
  classically rewritten subquery) and `AggQueryIn.gammaRew_valid` its
  correctness; a `FILTER` clause rides into it unchanged
  (`Selection.castToAnnotatedTuple`), its aggregate's column being an
  expression over the whole group on both sides
  (`AggExpr.ofGroupWhen_toComposite`, against the rewritten world's
  `AggExpr.ofGroupWhenRew`, whose reading is the one the transport
  carries). Both rest on the reusable
  `AggQueryIn.rewriting_provRel` – the rewritten world's reading of a
  classical rewriting back as an annotated relation, and
  `AggValue.predProv_toComposite` – a transported token is read by the
  gate unchanged
- `Provenance.AggQueryClosure` – **the compositional closure of the three
  base rewritings** (classical blocks, `HAVING` sites, bare groupings).
  Since the base rules do not share an output shape – a bare grouping
  emits token columns – the relation `AggQueryIn.RewritesTo` is indexed by
  the rewritten query's own kind vector and correctness
  (`AggQueryIn.rewritesTo_valid`) is stated at token level, specializing to
  the all-regular form as `AggQueryIn.rewritesTo_valid_reg`. The
  uniform rewritten kind vector `ColKind.rewKindsOf κ` (source kinds plus
  the provenance column) makes casting into the rewritten world
  kind-preserving, so `TermGIn.castRew`, `GenPredIn.castRew` and
  `ProjColIn.castRew` need no all-regular hypothesis and selection,
  projection and union close over token-bearing subqueries – the
  `SELECT … FROM (GROUP BY …)` shape. The module also lifts the two
  scope restrictions of the `HAVING` site: `AggQueryIn.havingPredRew` is
  the site *with its aggregates exposed* (keys and tokens kept as output
  columns, the gates in the provenance column – the shape ProvSQL
  actually emits) for an *arbitrary* predicate with an aggregate atom,
  not just a single comparison, regular atoms mixed in included.
  `GenPredIn.gateTerm` translates the `predsem` algebra into a rewritten
  term (`∧ ↦ ⊗`, `∨ ↦ ⊕`, `¬` pushed to the atoms), an aggregate atom
  becoming a `provsql_having` gate and a regular one a `TermGIn.chiGate`
  indicator gate. It is faithful (`GenPredIn.gateTerm_evalRew`) for a row
  whose aggregate columns hold no *nested* token: the gate reads the
  transported column, and the transport preserves the reading of an
  ordinary token (`AggValue.predProvOf_toComposite`) and of an
  expression – a window's, or a filtered aggregate's – alike
  (`AggExpr.predProv_toComposite`, off the world transport
  `AggExpr.isWorld_toComposite` and `AggExpr.valOn_toComposite`). What it
  does exclude is a *range* atom (`GenPredIn.rangeFree`), and that is the
  gate vocabulary's own limit: ProvSQL's gate carries one comparison, so
  the emitted term is the product of two of them, which denotes the
  two-world reading. The system recovers the one-world reading in its
  evaluation pass instead – a product of conditions over one contributor
  family is resolved jointly, with the closed form `S_C ⊖ S_{D+1}`
  (`Having.G_eq_S_monus_S`) for a two-sided bound on a count – so
  lifting the fence means modeling that pass, not adding a gate.
  Whether the group-existence guard is superseded or
  kept as a factor is decided by `GenPredIn.entailsExistence`, in
  `GenPredIn.siteProvTerm`: an aggregate-only predicate always supersedes
  it (`GenPredIn.aggOnly_entailsExistence`), one with a regular atom
  reachable in an empty group does not. Deduplication closes too, through
  `AggQueryIn.dedupRew`/`AggQueryIn.dedupRew_valid`: ProvSQL's `ε` rule
  (group by the data columns, `⊕`-sum the provenance column) proven
  against an arbitrary rewritten subquery. So does product
  (`AggQueryIn.prodRew`/`AggQueryIn.prodRew_valid`), whose join reassembly
  uses the kind-dispatched column copy `ProjColIn.copy`, faithful because
  the operands' rows conform (`GenRow.toCompositeRow_conform` over
  `AggQueryIn.evaluate_conform`). The **grouping itself** closes over an
  arbitrary rewritten subquery (`AggQueryIn.RewritesTo.gammaOf`, off
  `AggQueryIn.gammaRewOf_valid`): the rule asks only that some query of the
  rewritten world compute its input's rows – the pairs of a plain tuple
  and the annotation its provenance column carries, which
  `AggQueryIn.provRel_of_toCompositeRow` reads off any such rewriting – so
  a `GROUP BY` over a `GROUP BY` is covered, the inner aggregate column
  read out first as the kinds ask
  (`AggQueryIn.rewritesTo_gamma_gamma`). The **selection with an aggregate
  atom** closes over an arbitrary rewritten subquery as well
  (`AggQueryIn.RewritesTo.selAgg`, off `AggQueryIn.selAggRew_valid`), so a
  `HAVING` need not sit on the grouping it reads – one over a grouping of
  a grouping is covered (`AggQueryIn.rewritesTo_having_over_gamma`). Its
  provenance column is the gate term times the row's own provenance
  column, with no entailment test: where the predicate entails the
  group's existence the evaluator drops the pending factor and the gate
  term absorbs the guard left in the column instead
  (`GenPredIn.predsem_absorb_prod`, for exactly the factors the evaluator's
  supersede filter selects). ProvSQL's
  `having_entails_group_existence` test is therefore an optimization and
  not what makes the rewriting correct; the fused site rule stays because
  it is the shape ProvSQL emits. Difference above a grouping the kinds
  already forbid; what is left outside is the operators this layer gives
  no rule for – the apply, the two recursions and the alternatives, each
  for a reason in the shape of the rewritten plan, and the **windows**,
  which ProvSQL does rewrite: what is missing there is a specification of
  that rewriting, not a possibility, and specifying it is outside the
  semantics this library formalizes

**The classical rewriting layer**

- `Provenance.QueryRewriting` – alternative query evaluation by rewriting plain
  queries on `T ⊕ K`; implements rules (R1)–(R4) of
  [Sen, Maniu & Senellart][sen2026provsql] on the classical syntax, with
  correctness `Query.rewriting_valid`. The difference rule joins the two
  branches on their data columns with `≐`, the syntactic equality difference
  itself uses, so the rule holds over a domain with a null as it stands.
  Rule (R5) – aggregation – lives on the
  general syntax instead (`Provenance.AggQueryGroupRewriting`), where an
  aggregate output is a symbolic token rather than a quotiented K-tensor
**HAVING: algebra, possible worlds, probability, and correctness**

- `Provenance.Having` – algebraic identities behind `HAVING (count)` aggregate
  provenance: include/exclude recurrences for the JOIN and possible-world expressions,
  the upward-expansion bound, the upward-closed collapse
  (`upward_closed_collapse`, `collapse_to_minimal`), the sandwich
  `T_U(W) ≤ ann_U(W) ≤ A_W` of the factored world annotation and the
  resulting distributivity-free collapse of the monotone case
  (`monus_factor_le`, `witness_identity`, `witness_minimal`, `Fann_eq_S`),
  the range closed form `range_eq_S_monus_S` – `HAVING C+1 ≤ count ≤ D`
  is `S_{C+1} ⊖ S_{D+1}`, of which `atMost_eq_S_monus_S` and
  `G_eq_S_monus_S` are the cases `C = 0` and `D = C + 1`, and whose
  hypotheses are not confined to the step `F = S` it passes through
  (`Having.natRange_ne` separates the two sides over `ℕ` on two
  occurrences annotated `𝟙`), and the index-set size facts
- `Provenance.HavingSemantics` – the possible-world semantics of the fused
  `Query.Having` operator (grouping + aggregate comparison) over annotated
  databases: group-occurrence sequences, the bridge between subsequences and
  `Finset`-of-positions worlds (`seqOf_sublist`, `sublist_eq_seqOf`,
  `seqOf_injective`), the factored world annotation (`worldAnn`), the
  predicate provenance (`havingProv`) with
  its attachment to the query-free algebra (`havingProv_eq_prov`), and
  Boolean combinations of aggregate comparisons (`HavingPred`).
  **Existential comparisons collapse to the qualifying occurrences**
  (`havingProv_existential3`): in an absorptive m-semiring the provenance of
  `f(t) op c` is the `⊕`-sum of the annotations of the occurrences whose
  value makes the comparison *true*. It holds over a domain with a null as
  it stands, and SQL's own `MIN` and `MAX` are existential in that reading
  (`Existential.sqlOf3`, `existential3_sqlOf_min_le` and its three
  companions) – the values the aggregate skips being exactly the values a
  strict comparison is unknown on, an occurrence with a null value is in no
  world's reason for the predicate holding
- `Provenance.HavingMinMax` – the `HAVING` aggregate comparisons whose validity
  is decided occurrence by occurrence: for `MIN`, `MAX` and `PICKFIRST`, and for
  all six comparison operators, the possible-world provenance of a group
  collapses, in an absorptive m-semiring, to a closed form computable by a
  single scan over the occurrences (`minScan_correct`, `maxScan_correct`,
  `firstScan_correct`), hence in polynomial time in data complexity. The
  collapse rests on the identity `meet_family_eq` for the worlds that stay
  inside a set `G` and meet a set `H`
- `Provenance.Probability` – intensional probabilistic query evaluation: probability
  distribution over Boolean valuations, probability of a `BoolFunc X`, and the
  statement of Theorem 12 of [Sen, Maniu & Senellart][sen2026provsql] reducing
  `Pr(t ∈ q(Î))` to `Pr(⋁_{(t,α) ∈ ⟪q⟫^Î} α)`; the proof is reduced to a single
  structural commutation lemma `randomWorld_evaluateAnnotated`
- `Provenance.SupportAdequacy` – support adequacy over `𝔹`, for the full
  non-aggregation fragment (difference and duplicate elimination included):
  the support of the `𝔹`-annotated evaluation is the plain evaluation of the
  support of the database, and this transfers along any m-semiring
  homomorphism `K → 𝔹`. This is the equality that replaces `ℕ`-adequacy
  ([Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini][benzaken2021coq])
  beyond the positive fragment.
- `Provenance.Circuit` – Boolean circuits with structural predicates and
  two recursive bottom-up probability evaluators: the **read-once**
  evaluator with the inclusion-exclusion correction at OR gates
  (`Circuit.prob`), and the **d-D** evaluator with direct summation at
  OR gates under decomposability + determinism (`Circuit.probDD`). Both
  evaluators are proved correct against the sum-over-valuations
  semantics ([Sen, Maniu & Senellart][sen2026provsql], Section V-D
  step 1).
- `Provenance.CategoricalBlock` – the categorical-block counterpart of
  `Provenance.Circuit`'s d-D weighted-model-counting correctness: an
  independent re-proof over **categorical block variables** (the **free
  Boolean** case is the `κ ≡ fun _ => Bool` instance). A `CatAssignment`
  gives each block its own categorical distribution, `CatCircuit` has
  block-outcome literals,
  and `CatCircuit.dD_eventProb_eq_probDD` proves the direct-summation
  evaluator correct on decomposable + deterministic categorical circuits.
  The three block lemmas (`CatAssignment.mulin_disjoint`, `mulin_or_prob`,
  `mulin_none`) and `singleBlock_detOR_sound` back ProvSQL's trust in the
  deterministic-OR (`plus(mulinputs)`) mark and the `1 - Σ pᵢ` none-branch
  of the bounded-treewidth `repair_key` / BID route (`evaluateCertifiedIsland`).
- `Provenance.HavingProbability` – probability identities for evaluating
  `HAVING`-style aggregate comparisons under contributor independence:
  given pairwise-disjoint contributor variable supports (so contributors
  are independent Bernoullis with marginals `p i = P.funcProb (α i)`),
  the MAX / MIN factorization formulas for all six comparison operators
  (`funcProb_maxLeOnNonempty` / `funcProb_minGeOnNonempty` and the
  generic `funcProb_guardedSome` covering the remaining operators),
  the COUNT / SUM Poisson-binomial-style recurrences
  (`countMass_insert_zero` / `countMass_insert_succ` /
  `sumMass_insert_of_le` / `sumMass_insert_of_lt`), and the CDF assembly
  around them (`funcProb_count_filter`, empty-world mass `countMass_zero`,
  and the shorter-tail identity `funcProb_count_ge_eq_absent_le`).
- `Provenance.DistributionExample` – `percent_rank`, `cume_dist` and
  `ntile` evaluated on a three-row partition, including a partition of one
  row and one with peers: the values SQL gives, and the pair of counts the
  two nested frames supply. Also `rank` against `dense_rank`, which part
  exactly where the order has peers.
- `Provenance.NestedExample` – second-level aggregation, `sum(count(*))`
  over a `GROUP BY`, written through the alternatives: the inner count read
  as a key becomes a regular column, so the outer aggregate is an ordinary
  one and nothing nested is involved. The alternatives and their
  annotations are printed, one of them impossible, and with them the gap
  between a world's answer and the token's deterministic reading that
  keeps `Explode` out of `AggQueryIn.evaluateAnnotated_toPlain`.
- `Provenance.HavingExample` – worked examples on a three-occurrence group:
  the `SUM ≥ 5` possible-world provenance in `𝔹[X]` and its collapse to
  minimal worlds (both computed by kernel evaluation), and the
  Poisson-binomial `Pr[COUNT(*) ≥ 2] = 7/24` computation via the
  recurrence and CDF assembly.
- `Provenance.HavingQueryCorrectness` – query-level correctness of the fused
  `Having` operator against the JOIN-based rewriting, in absorptive
  m-semirings (`⊗`-over-`⊖` distributivity is needed for `<`, `≤`, `=`,
  `≠` only; the monotone `≥` and `>` cases hold without it,
  `Query.joinCount_monotone_correct`): the `C = 1` case
  (`AggQueryIn.havingSite_count_ge_one`, the fused `COUNT(*) ≥ 1` site
  equals the duplicate-eliminated key projection) and the general
  case (`Query.joinChain_count_correct`, the `C`-fold self-join chain with
  a lexicographic occurrence-identifier tie-break gives every key the
  `⊕`-sum of its `(C+1)`-element world monomials, the fused
  `COUNT(*) ≥ C + 1` provenance), via the extensional characterization
  `groupByKey_eq_dedup_map` of duplicate elimination and the chain algebra
  `chainAgg`/`esymm`
- `Provenance.HavingJoinCompositional` – the JOIN rewriting upgraded from
  extensional (per-key annotation sums) to intensional, multiset-level
  equality: the padded rewriting `joinCountQueryPadded` (the join query
  unioned with the `𝟘`-annotated self-difference of the key query, then
  duplicate-eliminated) evaluates to exactly one row per group key with
  the fused predicate provenance (`joinCountQueryPadded_correct`; for
  `≥` and `>`, `joinCountQueryPadded_monotone_correct` without
  distributivity), which is precisely the key projection of the fused
  output (`fused_key_proj`); the combined `countHaving_site_rewrite`
  (`countHaving_site_rewrite_monotone`) makes the substitution
  transparent to every surrounding operator – padding matters, since a
  bare “equal up to `𝟘`-rows” relation is not a congruence for enclosing
  aggregates. The compositional query-to-query form of the rewriting
  lives on the general syntax (`GenCountHavingRewrite`, in
  `Provenance.AggQueryEmbedding`)
- `Provenance.HavingMonotone` – monotone `HAVING` conditions, for which
  absorptivity suffices: the existential comparisons `MIN(t) ≤ c`, `< c`,
  `MAX(t) ≥ c`, `> c` rewrite as `ε(Π_{#0}(σ_{t op c}(q)))`
  (`existential_site_rewrite`, `minLe_site_rewrite` …), and the syntax
  `MonoCond` of positive Boolean combinations of `COUNT(*) ≥ C`, `> C` and
  existential atoms comes with the compositional rewriting
  `MonoCond.rewrite` (conjunction as join on the group key, disjunction as
  set union), the closed form `MonoCond.site_evaluateAnnotated` of the fused
  site of a compound condition in the general evaluator, and the site
  substitution `MonoCond.site_rewrite`, all without distributivity of `⊗`
  over `⊖`
- `Provenance.HavingQueryCounterexamples` – `decide`-checked counterexamples,
  at the level of queries evaluated on concrete annotated databases, showing
  that the HAVING / JOIN correspondence for `COUNT(*)` needs both
  absorptivity (tropical over `ℤ ∪ {∞}`, for `≥`) and `⊗`-over-`⊖`
  distributivity (`ChainFive`, for `=`), and that the `≥` correspondence
  does close in `ChainFive` (`HavingQueryCounterexamples.ChainFive.query_ge_agree`).
  It also witnesses that the collapse of a
  count needs absorptivity: over `ℕ`, two occurrences annotated `1` and `2`
  give a possible-world sum of `2`, the product, because every world
  omitting one of them is killed by the monus – neither the `⊕`-sum `3`
  that the absorptive collapse gives nor the indicator reading `𝟙`
  (`natCountToken_ne_sum`, `natCountToken_ne_delta`).
  The `∨` rule is witnessed not to be a decomposition of the one sum over
  the union of the disjuncts' families, in `𝔹` and in `ℕ`
  (`bool_or_ne_joint`, `nat_or_ne_joint`), the `𝔹` instance closing at
  row level where the `ℕ` one does not. Beside them, `joint2` and
  `joint3` are the one-sum readings over two and three families, and:
  the two alternatives of a *Boolean* aggregate column overcount – over
  `ℕ` they carry `2` where the worlds of the two families together carry
  `𝟙`, which is what every non-Boolean column's alternatives carry
  (`nat_or_alternatives_ne_support`); a searched `CASE` splits into its
  branches without double counting, since the guards exclude each other,
  in every m-semiring and with no hypothesis on it
  (`Having.joint2_branch_split`), the second branch's guard being the
  test that the first is *not true* and not its negation, which would be
  `𝟘` where the guard is unknown; but the split parts from the one sum
  over the union as soon as two branches read different families, with
  no disjunction anywhere in the query (`natCase_ne`, `1` against `2`
  over `ℕ`). And **inclusion–exclusion is not the joint reading of a
  disjunction**: `S₁ ⊕ S₂ ⊖ S₁ ⊗ S₂` holds over `ℕ`
  (`nat_incl_excl_eq`) and fails in `𝔹` (`bool_incl_excl_ne`), where
  `⊤ ⊕ ⊤ ⊖ ⊤ ⊗ ⊤` is `⊥` while both sides hold – the overlap is not a
  quantity to remove, and where `⊕` is idempotent it was never counted
  twice. Min-max is the row where the two roads to killing an *invented*
  world of a nested aggregate – an exclusive `⊕`, or a `δ` saturating
  to `𝟙` – are both closed, and the instances say so: over `ℕ` the
  world that keeps an inner occurrence of a dropped outer one is
  annotated `𝟘` (`nat_incoherentWorld_eq_zero`), over min-max it is not
  (`mm_incoherentWorld_ne_zero`), since `𝟙 ⊖ g = 𝟙` there. Min-max does
  nonetheless keep the **row-level** absorption of the `∨` rule, in
  every configuration of the two tests (`mm_row_agree_one`,
  `mm_row_agree_both`, `mm_row_agree_neither`) – so `δ = id` suffices
  for that where `ChainFive` showed an idempotent `⊕` does not.
  Both instances are also stated against the definition
  itself rather than against a sum written family by family –
  `natOrExpr` and `natCaseExpr` are the two Boolean functions as
  `AggExpr`s over one shared family, and `natOrExpr_ne_structural` and
  `natCaseExpr_ne_split` are the same two numbers read off
  `AggExpr.predProv`. At the **row level** the picture differs and the
  file says so: what an implementation reports is
  `δ(β₁) ⊗ δ(β₂) ⊗ predsem(ψ)`, and over `𝔹` those factors close the
  gap the `∨` rule opens (`bool_row_agree`), so the `𝔹` instance is
  about the predicate provenance and not about the row. An idempotent
  `⊕` is not what closes it: `ChainFive` is absorptive, hence
  `⊕`-idempotent, and its `δ` is not the identity, and there the
  reported row is `hi` where the joint reading is `lo`
  (`chain_row_ne`).
- `Provenance.Tseitin` – the Tseitin CNF transformation encoding a
  circuit as an equisatisfiable CNF over `X ⊕ Circuit X`. Provides
  syntactic `Literal` / `Clause` / `CNF` types, the Tseitin encoder,
  and the bidirectional **equisatisfiability** theorem
  `Circuit.tseitin_equisat` ([Sen, Maniu & Senellart][sen2026provsql],
  Section V-D step 3, before the knowledge compiler is invoked).

**Algorithms**

- `Provenance.Algorithms.CompOp` – shared comparison-operator type used by the
  HAVING enumeration algorithms and by the predicate languages: the six
  comparisons, which `CompOp.strict` marks as unknown on a null operand, and
  the two syntactic ones (`syneq`, `synne`) which are not
- `Provenance.Algorithms.CountEnum` – enumeration of valid possible worlds for
  `HAVING count op C` predicates: definitions of `combinations`, `addExact`, and
  `countEnum`, together with the correctness theorem `countEnum_correct`
- `Provenance.Algorithms.SumDP` – subset-sum enumeration of valid possible
  worlds for `HAVING sum(t) op C` predicates: definition of `sumExact` and
  `sumDP`, together with the correctness theorem `sumDP_correct`

**Complexity**

- `Provenance.HavingComplexity` – deciding whether `HAVING SUM` provenance over
  an `ℕ[X]`-instance is non-`𝟘` is NP-complete, already in data complexity
  (`havingSumNonzero_NP_complete`). Built on the
  [descriptive-complexity](https://github.com/PierreSenellart/descriptive-complexity)
  library: membership is `Knapsack` cut down by one first-order sentence, and
  hardness is a padding FO reduction from `Knapsack`, hence stronger than a Karp
  reduction. The bridge to the semiring semantics is
  `havingSumProv_ne_zero_iff`, and `havingSumNonzeroHow_faithful` closes the
  loop on the other side: a concrete group – a list of aggregate values and a
  constant – is encoded with its size bounds discharged, so the statement is
  about values written in *binary*; `exists_concreteNonemptySubsetSum_iff`
  closes it in the decoding direction, which is what carries the hardness back
  to concrete groups. In unary the problem is tractable, by the
  very dynamic program of `Provenance.Algorithms.SumDP`

**Concrete m-semirings** (`Provenance.Semirings.*`)

- `Provenance.Semirings.Bool` – the Boolean m-semiring `𝔹`
- `Provenance.Semirings.BoolFunc` – the Boolean-function m-semiring `𝔹[X]`
- `Provenance.Semirings.Why` – the Why[X] m-semiring (sets of witness sets)
- `Provenance.Semirings.Which` – the Which[X] m-semiring (lineage / Lin[X])
- `Provenance.Semirings.How` – the ℕ[X] m-semiring of multivariate
  polynomials; the universal provenance semiring
- `Provenance.Semirings.Nat` – the counting m-semiring `ℕ`
- `Provenance.Semirings.Tropical` – the tropical m-semiring (min-plus) over `ℕ ∪ {∞}`, `ℚ ∪ {∞}`, or
  `ℝ ∪ {∞}`; the `ℝ` instance is also used as a counterexample showing that the absorptive
  hypothesis of `Having.F_eq_S` and of the `MIN`/`MAX`/`PICKFIRST` scan collapses
  (`MinTropicalR.minScan_ne_prov`) is genuinely required (idempotent + `⊗`-over-`⊖` distributive
  is not enough)
- `Provenance.Semirings.Viterbi` – the Viterbi m-semiring (max-times) over `[0,1]`
- `Provenance.Semirings.MinMax` – the min-max semiring over any bounded linear
  order (security / access control semiring and dual fuzzy semiring)
- `Provenance.Semirings.Lukasiewicz` – the Łukasiewicz (fuzzy logic) m-semiring over `ℚ ∩ [0,1]`
- `Provenance.Semirings.ChainFive` – a five-element chain m-semiring, absorptive but without
  `⊗`-over-`⊖` distributivity; witnesses that the distributivity hypothesis of
  `Having.world_bound` (hence of the `HAVING count =`/`≤` identities) is genuinely required
- `Provenance.Semirings.Interval`, `Provenance.Semirings.IntervalUnion` –
  intervals and finite unions of intervals over a dense linear order, used for
  temporal databases
- `Provenance.Semirings.Security` – the alternative security semiring
  `S′ = 𝔹^L` of Amsterdamer, Deutch and Tannen: the subsets of a set of
  clearance levels, a tuple annotated with the levels at which it may be
  seen. It is the instance at `Set L` of
  `BooleanAlgebra.toSemiringWithMonus`, which reads **any** Boolean
  algebra as an m-semiring (`⊕ = ⊔`, `⊗ = ⊓`, `a ⊖ b = a ∖ b`, `δ = id`)
  and proves there, once, every property the library states of an
  m-semiring: both idempotences, absorptivity, exclusivity,
  complementedness and `⊗`-over-`⊖` distributivity. That construction is
  a `def` and not an instance on purpose – `Bool`, `Prop`, `Set α` and
  `α → Bool` are all Boolean algebras, so a global instance would collide
  with the catalog's own `𝔹` and `𝔹[X]` instances – and `Security` is its
  own type for the same reason
- `Provenance.Semirings.Regex` – **the regular-expression semiring**
  (ProvSQL's `sr_regex`, 1.13.0): languages over the labels of the
  input tuples, `⊕` the union, `⊗` the concatenation, a product gate
  concatenating its factors in the order of the query. The first entry
  of the catalog whose `⊗` **does not commute** (`not_commutative`), on
  Mathlib's `Language`. An m-semiring all the same: the monus is the
  difference of languages, which ProvSQL declines to compute but which
  exists, and `δ` the indicator of non-emptiness. Idempotent,
  complemented, neither absorptive nor exclusive, and every value has a
  Kleene star with the identities ProvSQL's simplifier applies
  (`kstar_one_add`, `kstar_kstar`, `kstar_zero`, `kstar_one`)
- `Provenance.Semirings.TropicalPaths` – **the min-cost-paths semiring**
  (`sr_tropical_paths`): a cost with every derivation of that cost as a
  language, `⊕` keeping the lower cost and merging the languages on a
  tie, `⊗` adding the costs and concatenating. `⊕` is the join of the
  lexicographic order of the costs reversed and the languages by
  inclusion, with `𝟘` at the bottom, and the monus that order
  determines (the difference of the languages on a tie) makes it an
  m-semiring, again one ProvSQL declines to compute. The star it
  implements is verified against the fixpoint equation it solves: `𝟙`
  for a positive cost, `(0, L∗)` for a cost `0`, and no solution for a
  negative one (`no_fixpoint_of_neg`), which is the refusal
  `recursion-cycle-no-value`
- `Provenance.Semirings.BestPath` – **the one-best-derivation semiring**
  (`sr_best_path`): a cost with one word of labels, the better value
  being the cheaper one and, at equal costs, the shortlex-smaller word;
  `⊕` the better of two, so the values are a chain with `𝟘` at the
  bottom, `⊗` the concatenation with the costs added. Selective,
  idempotent, non-commutative, complemented, with `⊗` distributing over
  the monus on both sides, and absorptive on both sides for nonnegative
  costs (`absorptive_of`), which is what lets ProvSQL solve a recursion
  in it by Dijkstra's algorithm

**Published papers**

- `Provenance.Papers.Icde2026` – a frozen restatement of the claims of
  [Sen, Maniu & Senellart][sen2026provsql], each proved by applying the
  declaration the paper links to. Its statements are fixed at publication and
  never edited to follow the library, so a generalization keeps compiling while
  a weakening breaks the build; together with `scripts/check-anchors.sh`, which
  reads its `Anchor:` lines, it is what keeps the paper's hyperlinks honest

See `Provenance.Example` for an example annotated database computation.

## Related formalizations

[Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini][benzaken2021coq]
formalize K-relations in Coq/Rocq, for the *positive* relational algebra extended
with a single top-level aggregate, and prove an adequacy theorem: at `K = ℕ`,
the annotated semantics computes exactly the standard bag semantics of the
relational algebra. Their positivity restriction is essential to that theorem:
`ℕ`-adequacy fails as soon as monus-based difference interacts with duplicate
elimination (`Nat.counterexample_diff_adequacy` in
`Provenance.QueryAdequacy`). This library covers the non-monotone m-semiring
extension instead – monus difference, duplicate elimination, compositional
aggregation – and therefore anchors correctness differently: through
homomorphism commutation (`Provenance.QueryAnnotatedDatabaseHom`), the
rewriting correctness theorems (`Query.rewriting_valid`,
`AggQueryIn.rewritesTo_valid`), the possible-worlds adequacy of the
Boolean-function annotated semantics (`randomWorld_evaluateAnnotated` in
`Provenance.Probability`), the `𝔹`-support adequacy and its transfer along
monus homomorphisms (`Provenance.SupportAdequacy`), and the data-part
adequacy results of `Provenance.QueryAdequacy`. Conversely, this library
does not treat NULL
values, correlated subqueries, or a SQL surface syntax, which the Coq/Rocq
development inherits from Datacert.

## References

* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
* [Geerts & Poggi, *On database query languages for K-relations*][geerts2010database]
* [Green & Tannen, *The Semiring Framework for Database Provenance*][green2017provenance]
* [Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
  Provenance and Probability of Data*][sen2026provsql]
* [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini, *A Coq formalization
  of data provenance*][benzaken2021coq]
-/

@[expose] public section
