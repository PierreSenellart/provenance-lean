/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/

/- Three-valued logic and value domains with a null -/
import Provenance.Util.Kleene
import Provenance.Util.ValueTypeNull

/- Queries on annotated relations -/
import Provenance.QueryAnnotatedDatabase
import Provenance.QueryAnnotatedDatabaseHom

/- Data-part adequacy of the annotated semantics -/
import Provenance.QueryAdequacy

/- HAVING algebraic identities -/
import Provenance.Having

/- Possible-world semantics of the fused Having operator -/
import Provenance.HavingSemantics

/- Symbolic aggregate tokens for the general HAVING semantics -/
import Provenance.AggValue
import Provenance.AggExpr
import Provenance.AggValueCongr

/- Kind-indexed general queries and their annotated semantics -/
import Provenance.AggQuery
import Provenance.AggQuerySubst

/- Operators that abbreviate a query of the basis -/
import Provenance.Derived
import Provenance.DerivedAnn

/- Relations read as families of occurrences -/
import Provenance.Occurrence

/- Window frames determined by values -/
import Provenance.OrderSpec
import Provenance.Frame

/- The window operator's token -/
import Provenance.Window

/- Surface syntax for kind-indexed queries -/
import Provenance.Notation

/- Data-part adequacy of the general evaluator -/
import Provenance.AggQueryAdequacy

/- Regression bridges: the fused Having recovered from the general syntax -/
/- A window over a whole partition is a join with its grouping -/
import Provenance.WindowPartition
import Provenance.AggQueryBridges

/- Possible-world foundations for the general evaluator -/
import Provenance.AggQueryProbability

/- Hom commutation for the general evaluator, token and annotation layer -/
import Provenance.AggQueryHom
import Provenance.QueryToAgg
import Provenance.AggQueryEmbedding

/- Provenance-aware rewriting stated natively on the general syntax -/
import Provenance.AggQueryRewriting
import Provenance.AggQueryStrip
import Provenance.AggQueryRewritingValid

/- The rewritten world's token-bearing evaluator (HAVING rewriting) -/
import Provenance.AggQueryHavingRewriting

/- The bare-grouping rewriting: aggregate results as output values -/
import Provenance.AggQueryGroupRewriting

/- Compositional closure of the rewriting rules -/
import Provenance.AggQueryClosure

/- Scan-computable HAVING provenance for MIN, MAX and PICKFIRST -/
import Provenance.HavingMinMax

/- Probability distributions over Boolean variables -/
import Provenance.Probability

/- Support adequacy over 𝔹 and transfer along monus homomorphisms -/
import Provenance.SupportAdequacy

/- Boolean circuits, read-once and d-D correctness -/
import Provenance.Circuit

/- Categorical-block probability and deterministic-OR (mulinput) soundness -/
import Provenance.CategoricalBlock

/- Probability identities for HAVING aggregate comparisons under independence -/
import Provenance.HavingProbability

/- Worked examples: HAVING provenance collapse and Poisson-binomial probability -/
import Provenance.HavingExample

/- Query-level correctness of the fused Having operator vs the JOIN rewriting -/
import Provenance.HavingQueryCorrectness
import Provenance.HavingJoinCompositional
import Provenance.HavingMonotone

/- Query-level counterexamples for the HAVING / JOIN correspondence -/
import Provenance.HavingQueryCounterexamples

/- Tseitin CNF encoding (equisatisfiability) -/
import Provenance.Tseitin

/- Algorithms (HAVING enumeration) -/
import Provenance.Algorithms.CountEnum
import Provenance.Algorithms.SumDP

/- Complexity of the HAVING semantics -/
import Provenance.HavingComplexity

/- Various semirings -/
import Provenance.Semirings.Bool
import Provenance.Semirings.BoolFunc
import Provenance.Semirings.ChainFive
import Provenance.Semirings.How
import Provenance.Semirings.IntervalUnion
import Provenance.Semirings.Lukasiewicz
import Provenance.Semirings.MinMax
import Provenance.Semirings.Nat
import Provenance.Semirings.Tropical
import Provenance.Semirings.Viterbi
import Provenance.Semirings.Which
import Provenance.Semirings.Why

/- Frozen restatements of the claims of published papers -/
import Provenance.Papers.Icde2026

/- Example -/
import Provenance.Example

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
  `CASE`, a disjunction a `COALESCE`, a negation `CompOp.negate`. Also the aggregate catalog `SeqAggFunc` and
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
  column values `T ⊕ AggValue T K` mixing key and token columns **A count compared to zero collapses to a single
  reading**: `predProvScalar_count_eq_zero` gives `𝟙 ⊖ ⊕ᵢ αᵢ` with no
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
  whose two known cases are its degenerate ones. The
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
- `Provenance.AggExpr` – **aggregate expressions**: what a term that
  mentions a column of aggregate kind produces. `AggExpr` is the formal
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
- `Provenance.AggValueCongr` – congruence of the token readings under
  tie-block permutations of the payload: `TiePerm`, the guarded analogue
  of `List.Perm` whose swaps only exchange adjacent elements with equal
  sort keys (`tiePerm_of_perm_of_sorted` produces one from two sorted
  permuted lists), a recursion form of the predicate provenance
  (`AggValue.predProvAux`, equal to the world-sum by
  `AggValue.predProv_eq_predProvAux`), and the congruences
  (`AggValue.predProv_congr`, `collapse_congr`, `annSum_congr`) making the
  annotation tie-break of the group sort semantically invisible
- `Provenance.AggQuery` – the general (non-fused) HAVING semantics:
  kind-indexed queries `AggQuery` over three column kinds – regular
  values, aggregate tokens, provenance values, ProvSQL's regular /
  `agg_token` / uuid data types – enforcing the scope conditions
  statically (`Gamma` over all-regular inputs only, no `Dedup`/`Diff`
  over token columns, normal-form projections and selections),
  aggregation without grouping (`GammaScalar`, whose single row survives an
  empty input: annotated `𝟙` with no group-existence factor, its tokens
  read in the scalar convention), the
  token-building grouping `GammaTok` and provenance aggregation
  `ProvSum` of rewritten plans, the generalized selection grammar
  `GenPred` mixing regular and aggregate atoms (`∧ ↦ ⊗`, `∨ ↦ ⊕`, `¬` by
  operator complementation), and the general evaluator
  `AggQuery.evaluate` with factored row annotations `GenAnn`
  implementing the replace-the-δ-factor combination rule: `Gamma` leaves
  its group-existence factor pending, an aggregate selection supersedes
  exactly the compared groups' factors with the predicate provenance, and
  projections cash the factors of dropped token columns. Also the plain
  evaluator `AggQuery.evaluatePlain` (classical filtering, aggregates
  computed over the whole group) and the stripping `AggQuery.stripAgg`.
  A projection column may also *compute* over one aggregate column
  (`ProjCol.aggTerm`), which produces an aggregate column again – the
  unary aggregate expression of `Provenance.AggExpr` – and is what
  `count(*) + 1` and the ranks need; over plain relations it is an
  ordinary term, and its token is the input's read through the
  function, so every reading of it is the input's read through the
  function too.
  Predicates are read three-valuedly throughout – `GenPred.eval3`,
  `evalPlain3`, `HavingPred.evalOnSeq`, `GenPred.evalRew3` – with `holds`,
  `holdsPlain`, `holdsOnSeq` and `holdsRew` keeping the rows on which the
  predicate is *true*. `Having.chi` contributes `𝟘` to a provenance on an
  unknown comparison, and `predsem` needed no change at all: its polarity
  flag, the `⊗`/`⊕` swap at `∧`/`∨` and the operator negator at the atoms
  were already Kleene's reading (`CompOp.negate_eval3`).
  The window operator `Win` gives every row of its input a further column
  holding the aggregate over that row's frame: it removes no row, merges
  none and changes no annotation, so it creates no group and leaves nothing
  pending. `AggQuery.evaluate_Win_eq` and `AggQuery.evaluatePlain_Win_eq`
  read its output off the relation – the input mapped row by row, each row
  gaining the token (`ValueFrame.tokenOf`) or the value
  (`ValueFrame.windowValue`) that the relation gives it – which is the form
  every theorem about the operator uses
- `Provenance.AggQuerySubst` – **substituting the outer columns**: the
  apply is defined by substitution – its right side is read, for each
  row `u` of the left, as the closed query `q₂[u]` – while the
  evaluators read it under an outer *valuation*, which is what makes
  them structurally recursive. `AggQuery.substMap` performs the
  substitution (generally enough to close only the ambient part of a
  nested context, which is what passing under an apply needs) and
  `AggQuery.evaluate_substMap` says the two readings agree, so that the
  document's clauses `AggQuery.evaluate_Apply_subst` and
  `AggQuery.evaluatePlain_Apply_subst` are theorems about the evaluator
  rather than a second semantics
- `Provenance.Occurrence` – **relations as families of occurrences**:
  `OccFam`, a relation read as an indexed family rather than a multiset, so
  that two copies of a row are two occurrences. The row type is a parameter,
  since the rows a window produces carry a token where the rows it reads
  carry only values. A multiset discards that
  identity, which three things need: an operator that gives equal rows
  different results (a window frame excluding the row it is computed for
  reads its twin, not itself), a comparison reading two aggregate values
  whose occurrence families overlap, and a statement quantifying over the
  ways equal rows could be told apart. `toRelation` forgets the index and
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
  `ASC` and nothing is null (`rangeUpTo_asc`, `rangeBefore_asc`); the `ROWS` frames with offsets are not among them and
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
  `frameOf_filter` (the restriction property again, now on relations),
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
  (`AggQuery.evaluateAnnotated_toPlain`), the aggregate tokens
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
  (`OrderSpec.le_refl`, `le_trans`, `le_total`) and not an order: the values
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
  is in range that §derivedann asks for (`predsem_rankRange`), with no
  hypothesis on the m-semiring – where a conjunction of two atoms would
  give the product of two sums. No `provsql_having` gate carries a range,
  so the site rewriting is stated on range-free predicates
  (`GenPredIn.rangeFree`): the term it would emit denotes the product,
  which an evaluator may resolve back to the range's own sum by
  recognising that the two gates read one family, but which the term
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
  `ValueFrame.tokenOfDist_specialize`). The metatheorems go through on
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
- `Provenance.WindowPartition` – **a window over a whole partition is a join
  with its grouping**: `AggQuery.winByJoin` writes it without a window – join
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
- `Provenance.AggQueryBridges` – **the fused `HAVING` site in closed
  form**: `AggQuery.havingSite` is one aggregate comparison directly above
  the grouping, and `AggQuery.havingSite_evaluateAnnotated` computes it
  – one row per group key, annotated by `Having.havingProv` – since the
  pending group factor is superseded by the token's predicate provenance
  (`AggValue.predProv_ofGroup`) and the data part collapses to the
  whole-group aggregates. The fused site is thereby a theorem about the
  single annotated evaluator, not a semantics of its own
- `Provenance.AggQueryProbability` – **the random-world commutation for
  the general evaluator** over `𝔹[X]`:
  `AggQuery.genRandomWorld_evaluate` – specializing the realized rows
  of the general annotated evaluation is the plain evaluation of the
  realized world (`genRandomWorld v (q.evaluate d) =
  q.evaluatePlain (d.randomWorld v)`), for arbitrary queries with
  aggregate comparisons anywhere. Built from the token-level PQE bridge
  (`AggValue.predProv_eval_iff`), the predicate-provenance evaluation
  under existence guards (`GenPred.predsem_eval_iff`, with `¬` handled by
  polarity), the existence-entailment extraction
  (`GenPred.entails_guard`), the σ-aggregate row lemma
  (`GenPred.sel_finalize_eval_iff`), and the conformance and guardedness
  invariants of the evaluator (`evaluate_conform`,
  `evaluate_guarded`). A window commutes for the reason it was built to:
  restricting the relation to a world restricts every frame to that world,
  so the token reads as the plain aggregate the world's relation gives its
  row (`tokenOf_specialize`). Its token is guarded by the row it is computed
  for whenever that row is in its own frame, and scalar – so exempt – when
  it is not. As corollaries, **unrestricted probabilistic
  query evaluation**: `AggQuery.boolean_pqe` (the probability that a
  random world has a non-empty answer is the probability of the query's
  Boolean provenance, the `⊕`-sum of the rows' finalized annotations) and
  `AggQuery.tuple_pqe` (the marginal probability of an answer tuple, for
  all-regular outputs) – both for arbitrary queries with aggregate
  comparisons anywhere, removing the top-level restriction of the fused
  `booleanHaving_pqe`
- `Provenance.AggQueryHom` – hom commutation for the general evaluator,
  token and annotation layer: the finalized factored annotation
  (`GenAnn.finalize_mapHom`, through `map_delta`), the predicate
  provenance of a token comparison (`AggValue.predProv_mapAnn`) and of a
  whole generalized predicate (`GenPred.predsem_mapAnn`) commute with
  every `SemiringWithMonusHom` –
  the `⊕`/`⊗`/`⊖`/`δ`-polynomial content of “compile once, evaluate
  many”. The evaluator-level commutation
  (`AggQuery.evaluateAnnotated_hom`) holds hypothesis-free over every
  m-semiring: the guard-absorption identities licensed by `delta_absorb`
  (`AggValue.predProv_delta_absorb`, `GenPred.predsem_delta_absorb`)
  neutralize the supersede decisions a non-injective hom can conflate,
  the group-sequence transport (`havingGroup_tiePerm`,
  `ofGroup_predProv_hom`, `havingGroup_annSum_hom`) neutralizes the
  `≼`-tie-break of `havingGroup`, and a row-wise simulation
  (`GenRow.Sim`, `AggQuery.evaluate_hom_rel`) carries both through
  the evaluator. A window's frame is carried unchanged, being read off the
  values; what the pushforward moves is only the order inside a block of
  equal tuples, which `sortList_hom_tiePerm` and `tokenOf_mapAnn_tiePerm`
  render invisible exactly as for a group
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
  column), the fragment predicate `AggQuery.classical`, and the rewriting
  `AggQuery.rewriting` mirroring the classical rules – with
  deduplication and difference expressed through the native `ProvSum`
  aggregation of provenance columns and the `Retag` cast
- `Provenance.AggQueryStrip` – the strip of the classical fragment back
  to the classical `Query` syntax (`AggQuery.strip`) and its
  faithfulness `AggQuery.strip_bridge`, through the row invariant
  `GenRow.Inv`
- `Provenance.AggQueryRewritingValid` – **correctness of the native
  rewriting**: the plain-semantics agreement `AggQuery.rewriting_plain`
  of the two rewritten queries, and `AggQuery.rewriting_valid`, which
  states that the annotated semantics folded into composite `T ⊕ K`
  tuples agrees with the plain evaluation of the rewritten query
- `Provenance.AggQueryHavingRewriting` – **the rewritten world's
  evaluator, with tokens as ordinary column values**: rewritten
  queries run over rows `Tuple (GenValue (T ⊕ K) K) n`
  (`AggQuery.evaluateRew`), where the token-building grouping `GammaTok`
  is ProvSQL's `provsql_agg` (explicit annotation term, group guard
  `δ(⊕ occs)` in the `prov` output column) and the two term gates are
  interpreted by their primitives (`TermG.evalRew`): `TermG.cmpAgg` is
  `provsql_having`, read by `AggValue.predProv`, and `TermG.chiGate` is
  the regular-atom indicator, read by `Having.chi`. Off the token
  operators and the indicator gate the evaluator is the plain semantics
  through the `inl` embedding (`AggQuery.evaluateRew_plain`, under
  `AggQuery.noGammaTok` and `AggQuery.chiFree`), connecting it to the
  classical rewriting correctness – the classical rewriting stays inside
  that fragment (`AggQuery.rewriting_chiFree`). `AggQuery.rewriting_provRel` reads a rewritten
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
  `AggQuery.gammaRew` is the rewritten grouping (`GammaTok` over the
  classically rewritten subquery) and `AggQuery.gammaRew_valid` its
  correctness, resting on the reusable
  `AggQuery.rewriting_provRel` – the rewritten world's reading of a
  classical rewriting back as an annotated relation, and
  `AggValue.predProv_toComposite` – a transported token is read by the
  gate unchanged
- `Provenance.AggQueryClosure` – **the compositional closure of the three
  base rewritings** (classical blocks, `HAVING` sites, bare groupings).
  Since the base rules do not share an output shape – a bare grouping
  emits token columns – the relation `AggQuery.RewritesTo` is indexed by
  the rewritten query's own kind vector and correctness
  (`AggQuery.rewritesTo_valid`) is stated at token level, specializing to
  the all-regular form as `AggQuery.rewritesTo_valid_reg`. The
  uniform rewritten kind vector `ColKind.rewKindsOf κ` (source kinds plus
  the provenance column) makes casting into the rewritten world
  kind-preserving, so `TermG.castRew`, `GenPred.castRew` and
  `ProjCol.castRew` need no all-regular hypothesis and selection,
  projection and union close over token-bearing subqueries – the
  `SELECT … FROM (GROUP BY …)` shape. The module also lifts the two
  scope restrictions of the `HAVING` site: `AggQuery.havingPredRew` is
  the site *with its aggregates exposed* (keys and tokens kept as output
  columns, the gates in the provenance column – the shape ProvSQL
  actually emits) for an *arbitrary* predicate with an aggregate atom,
  not just a single comparison, regular atoms mixed in included.
  `GenPred.gateTerm` translates the `predsem` algebra into a rewritten
  term (`∧ ↦ ⊗`, `∨ ↦ ⊕`, `¬` pushed to the atoms), an aggregate atom
  becoming a `provsql_having` gate and a regular one a `TermG.chiGate`
  indicator gate. Whether the group-existence guard is superseded or
  kept as a factor is decided by `GenPred.entailsExistence`, in
  `GenPred.siteProvTerm`: an aggregate-only predicate always supersedes
  it (`GenPred.aggOnly_entailsExistence`), one with a regular atom
  reachable in an empty group does not. Deduplication closes too, through
  `AggQuery.dedupRew`/`AggQuery.dedupRew_valid`: ProvSQL's `ε` rule
  (group by the data columns, `⊕`-sum the provenance column) proven
  against an arbitrary rewritten subquery. So does product
  (`AggQuery.prodRew`/`AggQuery.prodRew_valid`), whose join reassembly
  uses the kind-dispatched column copy `ProjCol.copy`, faithful because
  the operands' rows conform (`GenRow.toCompositeRow_conform` over
  `AggQuery.evaluate_conform`). Only difference above a grouping is
  left out

**The classical rewriting layer**

- `Provenance.QueryRewriting` – alternative query evaluation by rewriting plain
  queries on `T ⊕ K`; implements rules (R1)–(R4) of
  [Sen, Maniu & Senellart][sen2026provsql] on the classical syntax, with
  correctness `Query.rewriting_valid`. The difference rule joins the two
  branches on their data columns with `≐`, the syntactic equality difference
  itself uses, so the rule holds over a domain with a null as it stands. Rule (R5) – aggregation – lives on the
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
  (`AggQuery.havingSite_count_ge_one`, the fused `COUNT(*) ≥ 1` site
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
  does close in `ChainFive` (`ChainFive.query_ge_agree`). It also witnesses that the collapse of a
  count needs absorptivity: over `ℕ`, two occurrences annotated `1` and `2`
  give a possible-world sum of `2`, the product, because every world
  omitting one of them is killed by the monus – neither the `⊕`-sum `3`
  that the absorptive collapse gives nor the indicator reading `𝟙`
  (`natCountToken_ne_sum`, `natCountToken_ne_delta`).
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
`AggQuery.rewritesTo_valid`), the possible-worlds adequacy of the
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
