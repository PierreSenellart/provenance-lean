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

## Candidates (after auditing ProvSQL against the Lean library)

A pass over the ICDE 2026 paper (`sen2026provsql.pdf`) was performed
to inventory every formal claim and check coverage. Defs 1/3/5,
RA_k (Section III), the annotated semantics ⟪·⟫ (Section IV-B), the
hom commutation of Section V-C, and Proposition 6 are all covered.
Theorem 10 is partial (R1–R3 done, R4/R5 parked above). Theorem 12
and Corollary 13 are new gaps — see item E. The complexity content
of Section V-D (tree-decomposition probability, knowledge compilers,
linear-time read-once evaluation) and the #P-hardness statement are
out of scope per the project conventions.

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

### E. Intensional probabilistic query evaluation (Theorem 12 + Corollary 13)

Section IV-D of the paper. Currently nothing on the probability side
is formalised. To close this gap:
- define `Pr : X → ℚ ∩ [0,1]` and its independence-extension to a
  distribution over valuations `v : X → 𝔹`, i.e. the product
  `∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`;
- define `Pr(f)` for `f : BoolFunc X` as `∑_{v ⊨ f} Pr(v)`;
- prove **Theorem 12**: for any non-aggregation `q ∈ RA_k`, any
  `BoolFunc X`-instance `Î` and any tuple `t`,
  `Pr(t ∈ ⟦q⟧(Î)) = Pr(⋁_{(t,α) ∈ ⟪q⟫^Î} α)`;
- derive **Corollary 13** by composing with `Query.evaluateAnnotated_hom`
  (the existing rewriting / hom commutation), giving the same identity
  with `⟦q̂⟧^I` on the LHS for the rewriting `q̂` of `q`.

Self-contained and does not depend on aggregation or on the parked
R4/R5 sorries. This is the formal justification for ProvSQL's entire
probabilistic-evaluation pipeline and is the largest single gap
between the paper's formal claims and the Lean library.

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
combination with item E, the Tseitin-based CNF-encoding step of
Section V-D step 3 (purely semantic — equisatisfiability — not the
knowledge-compiler call itself).

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

A done → C done → **E** → B → D. E is promoted ahead of B because it
maximises paper coverage per unit effort: it does not depend on the
aggregation infrastructure and unlocks Corollary 13 immediately via
the existing hom commutation.
