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


### B. Aggregation provenance via K-semimodules (Amsterdamer-Deutch-Tannen)

`Query.evaluateAnnotated` currently rules out aggregation via the
`q.noAgg` precondition. Filling this gap means:
- adding a `K`-semimodule typeclass and the tensor product `K ⋆ M`
  (or a concrete realisation thereof);
- adding `δ : K → K` to `SemiringWithMonus` with the two axioms
  `δ(0) = 0` and `δ(1 ⊕ … ⊕ 1) = 1`;
- providing `δ` instances for every existing concrete semiring;
- giving a real `Agg` clause in `evaluateAnnotated`.

This is the formal semantics described in the ICDE 2026 paper.

### C. Add `δ` to `SemiringWithMonus` + verify the 12 instances

A smaller, self-contained piece of B: just the δ-semiring structure,
without yet touching `Query.Agg`. `gate_delta` is currently
unmodeled on the Lean side. One new field on the class + ~12 short
instance proofs.

### D. d-DNNF correctness (semantic, not complexity)

Define `Circuit Bool` + smoothness / decomposability / determinism
predicates, give a finite-sum-over-assignments probabilistic
semantics, and prove the bottom-up evaluator agrees with it under
those structural predicates. No complexity claim; pure semantic
correctness.

Would also give a foundation for later formalising the BID → TID
rewrite (`rewriteMultivaluedGates` in `BooleanCircuit.cpp`).

### Out of scope

- Polynomial-time / linear-time results on circuits or the
  Shapley-on-d-DNNFs algorithm (Karmakar-Monet-Senellart-Bressan
  PODS 2024): Mathlib does not currently provide a usable
  formalism for complexity classes.
- A `Formula` semiring distinct from `BoolFunc`: the ProvSQL
  `Formula` is a symbolic rendering of the provenance circuit, not
  an algebraic semiring (concatenation is not commutative, etc.).
- `How.universal` (already proven in `Provenance/Semirings/How.lean`).

## Working order

A done → C (small bridge) → B → D.
