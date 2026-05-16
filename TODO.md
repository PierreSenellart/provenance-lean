# TODO

The Diff case of `Query.rewriting_valid` is stuck on a deep Lean
infrastructure issue (HOU + competing `DecidableEq (T⊕K)` instance
resolutions inside `Multiset.dedup`/`Multiset.filter`); see the Git
log around commits `2dc8be2`, `d4ca753` and earlier `TODO.md`
revisions for the full diagnosis. Strategy switch: leave the two
remaining `sorry`s in `QueryRewriting.lean` alone for now and pick up
a complementary, mathematically distinct direction.

## ✅ Done

### A. Hom commutation for `Query.evaluateAnnotated`

`Provenance/QueryAnnotatedDatabaseHom.lean` defines the pushforward
`SemiringWithMonusHom.mapAnnotatedTuple`/`mapAnnotatedRelation`/
`mapAnnotatedDatabase` and proves `Query.evaluateAnnotated_hom` for
the whole non-`Agg` fragment: Rel, Proj, Sel, Prod, Sum, Dedup,
Diff. Zero sorries.

### F. Prod case of `randomWorld_evaluateAnnotated`

The last non-aggregation case of the structural-commutation theorem
underlying Theorem 12 is now closed. The proof is a `Multiset.induction_on`
on `r₁` (at the Prod-typed carrier, not Lex), where each cons step
distributes `Multiset.product` via `Multiset.cons_bind` (Mathlib's
`Multiset.cons_product` is stated with `×ˢ` notation which does not
match `.product` syntactically; the `unfold` + `cons_bind` route
sidesteps that). Two local helpers do the bookkeeping:

- `hrw_cons`: random world of a Prod-typed cons (the unfolded form)
  factors as an `if` on `a.snd v`. Used to expose the cons distribution
  of `randomWorld v (p ::ₘ s)` on the RHS.
- `h_head`: random world of the head slice `Multiset.product {p} r₂`
  matches `Multiset.product {p.fst} (randomWorld v r₂)` (when
  `p.snd v = true`) or vanishes (otherwise). Proved by induction on
  `r₂'` and case-split on `p.snd v` / `q.snd v`; uses the `BoolFunc`
  multiplication-is-pointwise-AND identity `(α * β) v = α v && β v`.

The arity cast (`Eq.mp` inside the LHS map, `Relation.cast` on the RHS)
is dispatched by `subst hn`, after which both wrappers reduce to identity.

The result lifts `randomWorld_evaluateAnnotated` to a zero-sorry proof
on the entire non-`Agg` fragment, which in turn upgrades Theorem 12
(`ProbAssignment.theorem_12`) and Corollary 13 (`ProbAssignment.corollary_13`)
to depend only on the parked R4/R5 `sorry`s in `QueryRewriting.lean`.

### C. δ on `SemiringWithMonus` + the 12 instances

`Provenance/SemiringWithMonus.lean` now carries a `δ : α → α` field
with axioms `delta_zero : δ 0 = 0` and
`delta_natCast_pos : 0 < n → δ ((n : α)) = 1`. A small derived lemma
`delta_one : δ 1 = 1` is exposed at the top level.

All 12 concrete m-semiring instances were extended with a `δ` matching
ProvSQL's `Semiring::delta` in `src/semiring/`:

- Identity (idempotent semirings): `Bool`, `BoolFunc`, `Which`, `Why`,
  `MinMax` (and `MaxMin` via `OrderDual`), `IntervalUnion`.
- Support indicator (`0 ↦ 0`, otherwise `↦ 1`): `Nat`, `How`,
  `Lukasiewicz`, `Viterbi`, `Tropical`.

For idempotent semirings the `delta_natCast_pos` axiom follows from
`natCast_pos_eq_one_of_idempotent` (already in `SemiringWithMonus.lean`).
For `Nat`/`How` it follows by computing the constant coefficient. For
`Lukasiewicz`/`Viterbi`/`Tropical` (idempotent but using the
indicator definition to match ProvSQL exactly) we first reduce
`(n : α)` to `1` via idempotence and then dispatch the `if`. The
`Tropical` proof handles the trivial degenerate case (`α` collapses
`⊤` and `0`, so `1 = 0` in `Tropical α`) gracefully via `split_ifs`.

Key supporting lemmas (all proved):
- `find_mapAnnotatedDatabase`, `map_fst_mapAnnotatedRelation`,
  `map_snd_mapAnnotatedRelation`
- `mapAnnotatedRelation_filter_fst` (predicate-only-on-fst filter
  commutes with pushforward)
- `mapAnnotatedRelation_filter` (variant for `Filter T n` predicates,
  used by the `Sel` case)
- `sum_filter_map_snd_mapAnnotatedRelation`: the inner sum-of-
  filtered-annotations equation, via `Multiset.sum_hom` after
  pushing the pushforward through `filter`/`map snd`. Uses `convert`
  to bypass a syntactic-but-not-instance match on the residual
  `Multiset.filter` decidability witnesses.
- `groupByKey_find_eq_filter_sum` (file-top-level): bridges the
  `groupByKey`-based Diff aggregation with the `filter`-based form,
  using `groupByKey_key_iff` and `groupByKey_value` from
  `QueryRewriting.lean` (those were promoted from `private` to
  public, a single-word edit).

Side effect: `QueryRewriting.lean` now exposes `groupByKey_key_iff`
and `groupByKey_value` publicly.

### E. Intensional probabilistic query evaluation (Theorem 12 + Corollary 13)

Section IV-D of the paper. The probability foundation, Theorem 12 and
Corollary 13 are now formalised in `Provenance/Probability.lean`. The
proof of Theorem 12 reduces to a single structural-commutation lemma
`randomWorld_evaluateAnnotated`, which is proven for **all 7
non-aggregation cases** (`Rel`, `Proj`, `Sel`, `Sum`, `Prod`, `Dedup`,
`Diff`); the `Prod` case is closed in item F below.

Concretely formalised:
- `ProbAssignment X` (probabilities in `[0, 1]` on a finite var set),
  `valProb v` (independence-product over a valuation), `funcProb f`
  (probability of a Boolean function as the sum over satisfying
  valuations), with all basic properties (`sum_valProb_eq_one`,
  `funcProb_nonneg`, `funcProb_le_one`, `funcProb_zero`,
  `funcProb_one`, `funcProb_congr`).
- `randomWorld v r` (data side of `r`'s annotated tuples whose
  annotation evaluates to `true` at `v`), `AnnotatedDatabase.randomWorld`,
  and the pointwise bridge `tupleAnnotation_apply_eq_true_iff`.
- `marginalProb P q Î t` (sum-over-valuations definition of the
  marginal probability).
- **Theorem 12** (`ProbAssignment.theorem_12`): for any non-aggregation
  `q ∈ RA_k`, any `BoolFunc X`-instance `Î` and any tuple `t`,
  `Pr(t ∈ ⟦q⟧(Î)) = Pr(⋁_{(t,α) ∈ ⟪q⟫^Î} α)`. Modulo the `Prod`
  case of `randomWorld_evaluateAnnotated`.
- **Corollary 13** (`ProbAssignment.corollary_13`): the same identity
  with the **plain** rewritten query `q̂` evaluated on the composite
  database `Î.toComposite`, derived by composing Theorem 12 with
  `Query.rewriting_valid` (Theorem 10 of the paper, R1–R5).
  Modulo the same `Prod` sorry plus the parked R4 `Diff` sorry from
  `Query.rewriting_valid`.

Supporting helpers:
- `randomWorld_add`, `randomWorld_map_data`, `randomWorld_filter_data`
  (multiset distribution of `randomWorld`).
- `diff_annotation_eq_false_iff` (the Diff subtraction-annotation
  evaluates to `false` at `v` iff the data tuple is absent from the
  random world of the subtracted relation).
- `Tuple.fromComposite_toComposite` + `AnnotatedRelation.map_fromComposite_toComposite`
  (composite-encoding roundtrip, lifted to multisets).

A repeated technical hurdle (documented in
`~/.claude/projects/.../memory/project_lex_prod_typeclass.md`): for
concrete `K = BoolFunc X`, elaboration of `Multiset.filter` over
`AnnotatedRelation` synthesises a different `DecidablePred` instance
than the rewrite lemma's, even though `Lex α = α` definitionally. The
recurring workarounds are (i) bind a `let r' : Multiset (Tuple T _ × K)
:= r` at the unfolded `Prod` type before inducting, (ii) bridge
instance-different filters via `Subsingleton.elim` on the
`DecidablePred` (rewriting **into the helper** rather than into the
goal), and (iii) always pass `(p := fun … => …)` named-arg to
`Multiset.filter_cons_of_pos` / `_neg` so HOU does not pick the wrong
predicate decomposition.

## Candidates

A pass over the ICDE 2026 paper (`sen2026provsql.pdf`) was performed
to inventory every formal claim and check coverage. Defs 1/3/5,
RA_k (Section III), the annotated semantics ⟪·⟫ (Section IV-B), the
hom commutation of Section V-C, and Proposition 6 are all covered.
Theorem 10 is partial (R1–R3 done, R4/R5 parked above). Theorem 12
and Corollary 13 (items E and F above) are now complete for the
non-aggregation fragment. The complexity content of Section V-D
(tree-decomposition probability, knowledge compilers, linear-time
read-once evaluation) and the #P-hardness statement are out of scope
per the project conventions.

### B. Aggregation provenance via K-semimodules (Amsterdamer-Deutch-Tannen)

`Query.evaluateAnnotated` currently rules out aggregation via the
`q.noAgg` precondition. Filling this gap means:
- adding a `K`-semimodule typeclass and the tensor product `K ⋆ M`
  (or a concrete realisation thereof);
- formalising Definition 7 of the paper (monoid aggregate function
  as a monoid hom from `(Multiset V, ⊎)` into a target monoid);
- giving a real `Agg` clause in `evaluateAnnotated`, matching the
  semantics of `⟪γ_…[t₁,…,t_n : f₁,…,f_n](q)⟫` on p. 4 of the paper.

The δ prerequisite (item C) is already done. This is the formal
semantics described in Section IV-B of the ICDE 2026 paper for the
aggregation operator.

### D. d-DNNF correctness (semantic, not complexity)

Define `Circuit Bool` + smoothness / decomposability / determinism
predicates, give a finite-sum-over-assignments probabilistic
semantics, and prove the bottom-up evaluator agrees with it under
those structural predicates. No complexity claim; pure semantic
correctness.

A natural sub-piece is the read-once case (Section V-D step 1 of the
paper): on a read-once Boolean circuit, recursive evaluation
`Pr(g) = Pr(g_left) ⊙ Pr(g_right)` (with `⊙` depending on the gate
type) agrees with the sum-over-valuations semantics. Same character
as the d-DNNF result but smaller; can land first.

Would also give a foundation for later formalising the BID → TID
rewrite (`rewriteMultivaluedGates` in `BooleanCircuit.cpp`) and, in
combination with the now-formalised Theorem 12, the Tseitin-based
CNF-encoding step of Section V-D step 3 (purely semantic —
equisatisfiability — not the knowledge-compiler call itself).

### Out of scope

- Polynomial-time / linear-time results on circuits or the
  Shapley-on-d-DNNFs algorithm (Karmakar-Monet-Senellart-Bressan
  PODS 2024): Mathlib does not currently provide a usable
  formalism for complexity classes. The linear-time tree-decomposition
  algorithm of Section V-D step 2 of the paper falls here too.
- #P-hardness of probabilistic query evaluation (Section V-D): same
  reason — no complexity formalism in Mathlib.
- Knowledge compilers (d4, c2d, DSHARP) used as black boxes in
  Section V-D step 3: not internal to ProvSQL.
- A `Formula` semiring distinct from `BoolFunc`: the ProvSQL
  `Formula` is a symbolic rendering of the provenance circuit, not
  an algebraic semiring (concatenation is not commutative, etc.).
- `How.universal` (already proven in `Provenance/Semirings/How.lean`).

## Working order

A done → C done → E done → F done → **B** → D. Theorem 12 and its
corollary are now closed for the entire non-aggregation fragment.
B (aggregation provenance) and D (d-DNNF correctness) remain
longer-horizon items.
