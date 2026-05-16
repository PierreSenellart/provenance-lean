# TODO

The Diff case of `Query.rewriting_valid` carries one remaining `sorry`
(R4 only; R5 is fully proved in `Query.rewriting_valid_full` in
`QueryEvaluateInVK.lean`), in the `matched_eq` half. The `unmatched_eq`
half is now fully proved, using the new helpers
`Query.rewriting_valid_diff_inner_dd_inst` (instance-polymorphic
wrapper bridging `LinearOrder.toDecidableEq` and `instDecidableEqSum`
via `Subsingleton.elim`), `Multiset.semijoin_proj_eq_filter` (generic
multiset semijoin), `AnnotatedRelation.toComposite_filter`,
`Relation.cast_eq_map`, and the Fin-arithmetic
`proj_outer_cast_append_eq_fst` / `cast_append_at_ofNat_{left,right}`
/ `selFilter_cast_append_iff`. The remaining `matched_eq` involves a
top-level `Query.Agg` and so needs unfolding the aggregation evaluator,
matching the inner sum against the right-hand side's
`(Multiset.map Prod.snd ∘ filter (·.1 = p.1))` form, then assembling
the product-filter-projection on top.

## Candidates

A pass over the ICDE 2026 paper (`sen2026provsql.pdf`) was performed
to inventory every formal claim and check coverage. Defs 1/3/5,
RA_k (Section III), the annotated semantics ⟪·⟫ (Section IV-B), the
hom commutation of Section V-C, Proposition 6, and Theorem 12 +
Corollary 13 (Section IV-D) are all covered. Theorem 10 is partial
(R1–R3, R5 done; R4 parked). The complexity content of Section V-D
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
