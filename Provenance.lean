/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/

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
import Provenance.AggValueCongr

/- Kind-indexed general queries and their annotated semantics -/
import Provenance.AggQuery

/- Data-part adequacy of the general evaluator -/
import Provenance.AggQueryAdequacy

/- Regression bridges: the fused Having recovered from the general syntax -/
import Provenance.AggQueryBridges

/- Possible-world foundations for the general evaluator -/
import Provenance.AggQueryProbability

/- Hom commutation for the general evaluator, token and annotation layer -/
import Provenance.AggQueryHom
import Provenance.QueryToAgg
import Provenance.AggQueryEmbedding

/- Provenance-aware rewriting stated natively on the general syntax -/
import Provenance.AggQueryRewriting

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
- `Provenance.Database` – tuples, relations, and plain databases
- `Provenance.Query` – relational algebra (select, project, join, union, difference…)
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
  `predProv_ofGroup`), the annotation pushforward (`mapAnn`), and lifted
  column values `T ⊕ AggValue T K` mixing key and token columns
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
  over token columns, normal-form projections and selections), the
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
  computed over the whole group) and the stripping `AggQuery.stripAgg`
- `Provenance.AggQueryAdequacy` – **data-part adequacy of the general
  evaluator**: forgetting the annotations of `Query.evaluateAnnotated` yields
  the plain evaluation of the stripped query
  (`AggQuery.evaluateAnnotated_toPlain`), the aggregate tokens
  contributing through their deterministic `collapse` reading and the
  fused group sequence projecting onto the plain one
  (`havingGroup_map_fst`)
- `Provenance.AggQueryBridges` – **the fused `HAVING` site in closed
  form**: `AggQuery.havingSite` is one aggregate comparison directly above
  the grouping, and `AggQuery.havingSite_evaluateAnnotated` computes it
  – one row per group key, annotated by `Having.havingProv` – since the
  pending group factor is superseded by the token's predicate provenance
  (`AggValue.predProv_ofGroup`) and the data part collapses to the
  whole-group aggregates. This is the content the separate fused evaluator
  used to carry, now a theorem about the single annotated evaluator
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
  `evaluate_guarded`). As corollaries, **unrestricted probabilistic
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
  the `⊕`/`⊗`/`⊖`/`δ`-polynomial content of "compile once, evaluate
  many". The evaluator-level commutation additionally hinges on the
  many". The evaluator-level commutation
  (`AggQuery.evaluateAnnotated_hom`) holds hypothesis-free over every
  m-semiring: the guard-absorption identities licensed by `delta_absorb`
  (`AggValue.predProv_delta_absorb`, `GenPred.predsem_delta_absorb`)
  neutralize the supersede decisions a non-injective hom can conflate,
  the group-sequence transport (`havingGroup_tiePerm`,
  `ofGroup_predProv_hom`, `havingGroup_annSum_hom`) neutralizes the
  `≼`-tie-break of `havingGroup`, and a row-wise simulation
  (`GenRow.Sim`, `AggQuery.evaluate_hom_rel`) carries both through
  the evaluator
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
  aggregation of provenance columns and the `Retag` cast. Correctness,
  `AggQuery.rewriting_valid`, states that the annotated semantics
  folded into composite `T ⊕ K` tuples agrees with the plain evaluation
  of the rewritten query; it is proven by stripping to the classical
  fragment (`AggQuery.strip`, faithful by `AggQuery.strip_bridge` through
  the row invariant `GenRow.Inv`) and the plain-semantics agreement
  `AggQuery.rewriting_plain` of the two rewritten queries
- `Provenance.AggQueryHavingRewriting` – **the rewritten world's
  evaluator, with tokens as first-class column values**: rewritten
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
  Since the base rules no longer share an output shape – a bare grouping
  emits token columns – the relation `AggQuery.RewritesTo` is indexed by
  the rewritten query's own kind vector and correctness
  (`AggQuery.rewritesTo_valid`) is stated at token level, specialising to
  the earlier all-regular form as `AggQuery.rewritesTo_valid_reg`. The
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
  correctness `Query.rewriting_valid`. Rule (R5) – aggregation – lives on the
  general syntax instead (`Provenance.AggQueryGroupRewriting`), where an
  aggregate output is a symbolic token rather than a quotiented K-tensor
**HAVING: algebra, possible worlds, probability, and correctness**

- `Provenance.Having` – algebraic identities behind `HAVING (count)` aggregate
  provenance: include/exclude recurrences for the JOIN and possible-world expressions,
  the upward-expansion bound, the upward-closed collapse
  (`upward_closed_collapse`, `collapse_to_minimal`), and the index-set size facts
- `Provenance.HavingSemantics` – the possible-world semantics of the fused
  `Query.Having` operator (grouping + aggregate comparison) over annotated
  databases: group-occurrence sequences, the bridge between subsequences and
  `Finset`-of-positions worlds (`seqOf_sublist`, `sublist_eq_seqOf`,
  `seqOf_injective`), the factored world annotation (`worldAnn`), the
  predicate provenance (`havingProv`) with
  its attachment to the query-free algebra (`havingProv_eq_prov`), and
  Boolean combinations of aggregate comparisons (`HavingPred`)
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
  the MAX / MIN factorisation formulas for all six comparison operators
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
  m-semirings with `⊗`-over-`⊖` distributivity: the `C = 1` case
  (`AggQuery.havingSite_count_ge_one`, the fused `COUNT(*) ≥ 1` site
  equals the duplicate-eliminated key projection) and the general
  case (`Query.joinChain_count_correct`, the `C`-fold self-join chain with
  a lexicographic occurrence-identifier tie-break gives every key the
  `⊕`-sum of its `(C+1)`-element world monomials, the fused
  `COUNT(*) ≥ C + 1` provenance), via the extensional characterisation
  `groupByKey_eq_dedup_map` of duplicate elimination and the chain algebra
  `chainAgg`/`esymm`
- `Provenance.HavingJoinCompositional` – the JOIN rewriting upgraded from
  extensional (per-key annotation sums) to intensional, multiset-level
  equality: the padded rewriting `joinCountQueryPadded` (the join query
  unioned with the `𝟘`-annotated self-difference of the key query, then
  duplicate-eliminated) evaluates to exactly one row per group key with
  the fused predicate provenance (`joinCountQueryPadded_correct`), which
  is precisely the key projection of the fused output (`fused_key_proj`);
  the combined `countHaving_site_rewrite` makes the substitution
  transparent to every surrounding operator – padding matters, since a
  bare "equal up to `𝟘`-rows" relation is not a congruence for enclosing
  aggregates. The compositional query-to-query form of the rewriting
  lives on the general syntax (`GenCountHavingRewrite`, in
  `Provenance.AggQueryEmbedding`)
- `Provenance.HavingQueryCounterexamples` – `decide`-checked counterexamples,
  at the level of queries evaluated on concrete annotated databases, showing
  that the HAVING / JOIN correspondence for `COUNT(*)` needs both
  absorptivity (tropical over `ℤ ∪ {∞}`) and `⊗`-over-`⊖` distributivity
  (`ChainFive`).
- `Provenance.Tseitin` – the Tseitin CNF transformation encoding a
  circuit as an equisatisfiable CNF over `X ⊕ Circuit X`. Provides
  syntactic `Literal` / `Clause` / `CNF` types, the Tseitin encoder,
  and the bidirectional **equisatisfiability** theorem
  `Circuit.tseitin_equisat` ([Sen, Maniu & Senellart][sen2026provsql],
  Section V-D step 3, before the knowledge compiler is invoked).

**Algorithms**

- `Provenance.Algorithms.CompOp` – shared comparison-operator type used by the
  HAVING enumeration algorithms
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
  `havingSumProv_ne_zero_iff`

**Concrete m-semirings** (`Provenance.Semirings.*`)

- `Provenance.Semirings.Bool` – the Boolean m-semiring `𝔹`
- `Provenance.Semirings.BoolFunc` – the Boolean-function m-semiring `𝔹[X]`
- `Provenance.Semirings.Why` – the Why[X] m-semiring (sets of witness sets)
- `Provenance.Semirings.Which` – the Which[X] m-semiring (lineage / Lin[X])
- `Provenance.Semirings.How` – the ℕ[X] m-semiring of multivariate polynomials; the universal provenance
  semiring
- `Provenance.Semirings.Nat` – the counting m-semiring `ℕ`
- `Provenance.Semirings.Tropical` – the tropical m-semiring (min-plus) over `ℕ ∪ {∞}`, `ℚ ∪ {∞}`, or
  `ℝ ∪ {∞}`; the `ℝ` instance is also used as a counterexample showing that the absorptive
  hypothesis of `Having.F_eq_S` and of the `MIN`/`MAX`/`PICKFIRST` scan collapses
  (`TropicalR.minScan_ne_prov`) is genuinely required (idempotent + `⊗`-over-`⊖` distributive
  is not enough)
- `Provenance.Semirings.Viterbi` – the Viterbi m-semiring (max-times) over `[0,1]`
- `Provenance.Semirings.MinMax` – the min-max semiring over any bounded linear order (security / access
  control semiring and dual fuzzy semiring)
- `Provenance.Semirings.Lukasiewicz` – the Łukasiewicz (fuzzy logic) m-semiring over `ℚ ∩ [0,1]`
- `Provenance.Semirings.ChainFive` – a five-element chain m-semiring, absorptive but without
  `⊗`-over-`⊖` distributivity; witnesses that the distributivity hypothesis of
  `Having.world_bound` (hence of the `HAVING count =`/`≤` identities) is genuinely required
- `Provenance.Semirings.Interval`, `Provenance.Semirings.IntervalUnion` – intervals and finite unions of intervals over a dense
  linear order, used for temporal databases

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
`Query.rewriting_valid_full`), the possible-worlds adequacy of the
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
* [Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the Provenance and Probability of Data*][sen2026provsql]
* [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini, *A Coq formalization of data provenance*][benzaken2021coq]
-/
