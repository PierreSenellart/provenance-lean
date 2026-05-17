# TODO

`Query.rewriting_valid` is now fully proved for R1–R4 (sorry-free),
with R5 proved in `Query.rewriting_valid_full` in
`QueryEvaluateInVK.lean`. The Diff case splits into an `unmatched_eq`
half (semijoin via `Multiset.semijoin_proj_eq_filter`,
`Query.rewriting_valid_diff_inner_dd_inst`,
`AnnotatedRelation.toComposite_filter`, `Relation.cast_eq_map`, plus
Fin-arithmetic helpers `proj_outer_cast_append_eq_fst` /
`cast_append_at_ofNat_{left,right}` / `selFilter_cast_append_iff`)
and a `matched_eq` half (keyed-projection semijoin
`Multiset.semijoin_keyed_proj_eq_filter`, the closed-form
`Query.evaluate_agg_rewriting_eq` for the inner aggregation, plus the
2n+2 Fin-arithmetic helpers `cast_append_2n2_at_ofNat_{left,right,n}`
/ `cast_append_2n2_at_last` / `proj_outer_2n2_cast_append_eq_fst` /
`selFilter_cast_append_2n2_iff`).

## Candidates

A pass over the ICDE 2026 paper (`sen2026provsql.pdf`) was performed
to inventory every formal claim and check coverage. Defs 1/3/5,
RA_k (Section III), the annotated semantics ⟪·⟫ (Section IV-B), the
hom commutation of Section V-C, Proposition 6, Theorem 10 (R1–R5),
and Theorem 12 + Corollary 13 (Section IV-D) are all covered. The
complexity content of Section V-D (tree-decomposition probability,
knowledge compilers, linear-time read-once evaluation) and the
#P-hardness statement are out of scope per the project conventions.

### B. Aggregation provenance via K-semimodules (Amsterdamer-Deutch-Tannen)

First-cut scope is in (`Provenance.KSemiModule` + `Provenance.QueryAggregation`):
- `KSemiModule K M` typeclass (six standard semimodule axioms) and
  canonical instance `KSemiModule K K` via multiplication;
- free formal-sum `KTensor K M := Multiset (K × M)` with `AddCommMonoid`,
  `smul`, `embed` — un-quotiented (no bilinear relations enforced);
- `Query.evaluateAggSum` for top-level aggregation with `AggFunc.sum`:
  one row per group, per-aggregated-column `(value, K-tensor)` annotation.
- Hom commutation `Query.evaluateAggSum_hom` (aggregation commutes with
  `SemiringWithMonusHom`).
- (R5) aggregation rewriting `Query.rewritingAgg` and its correctness
  via the unified `Query.rewriting_valid_full` in
  `Provenance.QueryEvaluateInVK`, together with the V_K-lifted
  evaluator `Query.evaluateInVK`, the unified Def-7 annotated
  semantics `Query.evaluateAnnotatedFull`, and its hom commutation
  `Query.evaluateAnnotatedFull_hom`.
- Exercised end-to-end on `Provenance.Example.qc`.

Remaining for B:
- General aggregation: other `AggFunc` constructors, nested aggregation
  (Agg under a non-Agg parent). Currently `AggFunc` only has `sum`, so
  this is mostly a scaffolding/refactor task.
- Bilinear quotient for `KTensor`: replace the formal-sum representation
  with the proper tensor product `K ⊗ M` (or use Mathlib's `TensorProduct`
  where applicable). Required before stating the random-world
  commutation theorem in its expected form (Amsterdamer-Deutch-Tannen),
  and before any further correctness theorems that compare to ProvSQL's
  intended semantics modulo bilinearity.
- Random-world commutation for the Agg case: the analogue of
  `randomWorld_evaluateAnnotated` for `evaluateAggSum`. Best landed
  after the bilinear quotient.

The δ prerequisite on `SemiringWithMonus` (item C) is already in place
on all 12 concrete instances and is used in `Provenance.Having` for the
HAVING-count fragment.

### D. Read-once and d-D correctness (semantic, not complexity)

Both sub-pieces have landed in `Provenance.Circuit`, sorry-free.

**Common infrastructure.**
- `Circuit X` inductive type (`const` / `var` / `not` / `and` / `or`),
  with `eval`, `toBoolFunc`, `vars`.
- `BoolFunc.DependsOn` (variable support of a Boolean function) plus
  `Circuit.toBoolFunc_dependsOn_vars`.
- `ProbAssignment.funcProb_var`, `funcProb_sub_self_const_one`,
  `funcProb_add_eq` (inclusion-exclusion).
- The **independence lemma** `ProbAssignment.funcProb_mul_disjoint`:
  `Pr(f * g) = Pr(f) * Pr(g)` whenever `f`, `g` depend on disjoint
  variable supports, proved by splitting valuations via
  `Equiv.piEquivPiSubtypeProd`, factoring `valProb` along the partition,
  and collapsing each unused half by marginalisation.

**Read-once.**
- `Circuit.ReadOnce` (gate-by-gate disjoint-supports predicate) and
  the inclusion-exclusion evaluator `Circuit.prob`.
- `Circuit.readOnce_funcProb_eq_prob`: for any `ReadOnce` circuit `c`,
  `Pr(c.toBoolFunc) = c.prob P`.

**d-D (decomposable + deterministic).** No NNF restriction; `not` is
treated semantically via `funcProb_sub_self_const_one`.
- `Circuit.Decomposable` (every AND has disjoint variable supports).
- `Circuit.Deterministic` (every OR has mutually exclusive children,
  i.e., `c₁.toBoolFunc * c₂.toBoolFunc = 0`).
- The d-D evaluator `Circuit.probDD` (AND = product, OR = sum, no
  inclusion-exclusion correction).
- `Circuit.dD_funcProb_eq_probDD`: for any `Decomposable +
  Deterministic` circuit `c`, `Pr(c.toBoolFunc) = c.probDD P`. The OR
  case collapses the inclusion-exclusion correction `Pr(f * g)` to zero
  using the determinism hypothesis.

**Tseitin CNF encoding (`Provenance.Tseitin`, sorry-free).** The
semantic step of Section V-D step 3 (before the knowledge compiler is
invoked):
- `Literal`, `Clause`, `CNF` syntactic infrastructure with eval
  semantics.
- `Circuit.gateClauses`, `Circuit.tseitinClauses`, `Circuit.tseitin`
  (Tseitin transformation, aux variables indexed by sub-circuits, with
  the root assertion clause prepended).
- `Circuit.tseitinValuation` (canonical lift of `v : X → Bool` to
  `(X ⊕ Circuit X) → Bool`).
- `Circuit.tseitin_eval_tseitinValuation`: the lifted valuation
  satisfies the CNF iff the circuit is satisfied.
- `Circuit.tseitin_models_restrict`: any CNF model restricts to a
  circuit model via `Sum.inl`.
- `Circuit.tseitin_equisat`: the bidirectional **equisatisfiability**
  theorem.

**Future directions (longer horizon).**
Smoothness predicate on `Circuit X` and the corresponding correctness
for smoothed sd-DNNF; the BID → TID rewrite (`rewriteMultivaluedGates`
in `BooleanCircuit.cpp`); and a Tseitin-style refinement that bridges
to **weighted** model counting (i.e., `Pr` rather than just
satisfiability), pairing `tseitin_equisat` with Theorem 12.

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

**B** is the main open item; D (read-once and d-D semantic correctness)
has landed. B (aggregation provenance) completes the formal semantics
of Section IV-B. The longer-horizon D follow-ups (smoothness / sd-DNNF,
Tseitin, BID → TID) can be taken on once B's bilinear quotient is in.
