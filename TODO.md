# TODO

The Diff case of `Query.rewriting_valid` is stuck on a deep Lean
infrastructure issue (HOU + competing `DecidableEq (T⊕K)` instance
resolutions inside `Multiset.dedup`/`Multiset.filter`); see the Git
log around commits `2dc8be2`, `d4ca753` for the full diagnosis. The
two remaining `sorry`s in `QueryRewriting.lean` (R4/R5) are parked.

## Candidates

A pass over the ICDE 2026 paper (`sen2026provsql.pdf`) was performed
to inventory every formal claim and check coverage. Defs 1/3/5,
RA_k (Section III), the annotated semantics ⟪·⟫ (Section IV-B), the
hom commutation of Section V-C, Proposition 6, and Theorem 12 +
Corollary 13 (Section IV-D) are all covered. Theorem 10 is partial
(R1–R3 done, R4/R5 parked). The complexity content of Section V-D
(tree-decomposition probability, knowledge compilers, linear-time
read-once evaluation) and the #P-hardness statement are out of scope
per the project conventions.

### B. Aggregation provenance via K-semimodules (Amsterdamer-Deutch-Tannen)

First-cut scope is in (`Provenance.KSemiModule` + `Provenance.QueryAggregation`):
- `KSemiModule K M` typeclass (six standard semimodule axioms) and
  canonical instance `KSemiModule K K` via multiplication;
- free formal-sum `KTensor K M := Multiset (K × M)` with `AddCommMonoid`,
  `smul`, `embed` — un-quotiented (no bilinear relations enforced);
- `Query.evaluateAggSum` for top-level aggregation with `AggFunc.sum`:
  one row per group, per-aggregated-column `(value, K-tensor)` annotation.
- Exercised end-to-end on `Provenance.Example.qc`.

Remaining for B:
- General aggregation: other `AggFunc` constructors, nested aggregation
  (Agg under a non-Agg parent). Currently `AggFunc` only has `sum`, so
  this is mostly a scaffolding/refactor task.
- Bilinear quotient for `KTensor`: replace the formal-sum representation
  with the proper tensor product `K ⊗ M` (or use Mathlib's `TensorProduct`
  where applicable). Required before stating correctness theorems that
  compare to ProvSQL's intended semantics.
- Correctness theorems: hom commutation (`evaluateAggSum_hom`),
  random-world commutation (analogue of `randomWorld_evaluateAnnotated`
  for the Agg case), rewriting correctness (R6 of the paper, currently
  not formalised).

The δ prerequisite on `SemiringWithMonus` (item C) is already in place
on all 12 concrete instances and is used in `Provenance.Having` for the
HAVING-count fragment.

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
combination with the formalised Theorem 12, the Tseitin-based
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

## Working order

**B** → D. B (aggregation provenance) completes the formal semantics
of Section IV-B; D (d-DNNF correctness) is a longer-horizon item that
also unlocks the Tseitin / BID → TID directions.
