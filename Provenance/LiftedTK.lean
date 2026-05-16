/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AnnotatedDatabase
import Provenance.KSemiModule
import Provenance.Util.ValueType

/-!
# The `V_K`-lifted value type

This file defines `LiftedTK T K`, a three-constructor sum that extends the
composite encoding `T ⊕ K` with K-tensor monomials. It is the target value
type for evaluating the rewriting of aggregate queries (rule (R5) of
[Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql]).

## Why a new value type

The existing `ValueType (T ⊕ K)` instance has the unfortunate property that
multiplying a data value with an annotation drops the annotation:

```
Sum.inl v * Sum.inr α = Sum.inl v
```

That is fine for the rules (R1)–(R4), which only multiply same-kind values
(data × data in the projected products, annotation × annotation when combining
two tuples' K-coordinates), but it loses information in (R5). The rewritten
aggregate column term `t_j * #(k+1)` evaluates to `Sum.inl v_j * Sum.inr α`,
which the current `Mul` collapses to `Sum.inl v_j` — the K-side `α` is gone
before the aggregator `f̂_j` ever sees it.

The paper resolves this by interpreting the rewritten aggregation *in the
semimodule `V_K`*, which can represent formal sums `Σ vᵢ ⊗ αᵢ`. `LiftedTK T K`
gives us a Lean encoding of that domain:

* `LiftedTK.data v` — a plain value `v ∈ T`;
* `LiftedTK.ann α` — a plain annotation `α ∈ K`;
* `LiftedTK.ktensor t` — a formal K-tensor sum `t : KTensor K T`.

The fixed `Mul` produces a `ktensor` monomial when given a data and an
annotation:

```
data v * ann α = ktensor (embed α v)
```

so the rewritten R5 aggregation now sees per-tuple K-tensor monomials, and
its aggregator `f̂_j = sum` (multiset union in `KTensor K T`) accumulates
them into the formal sum the paper prescribes.

## Notes

* `LiftedTK` is not (yet) made into a `ValueType` — `ValueType` requires a
  `LinearOrder`, and a decidable total order on `KTensor K T` (a `Multiset`)
  is not naturally available. We provide the algebraic operations
  (`Zero`, `Add`, `Sub`, `Mul`) directly and skip the order requirement;
  the rewriting evaluator (`Query.evaluateInVK`, defined elsewhere) does
  not need to compare values via `≤`.
* The lifting `T ⊕ K → LiftedTK T K` is **not** a `Mul`-homomorphism on
  mixed cases — that is precisely the point. It *is* a homomorphism on
  same-kind cases, which is what justifies that `evaluateInVK` agrees with
  the standard `evaluate` on the non-aggregate fragment.

## References

* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Section IV-B, R5)
* [Amsterdamer, Deutch & Tannen][amsterdamer2011aggregate]
-/

/-- The `V_K`-lifted value type: a plain `T`-value, a plain `K`-annotation, or
a formal K-tensor sum. -/
inductive LiftedTK (T K : Type) where
  /-- A plain data value `v ∈ T`. -/
  | data : T → LiftedTK T K
  /-- A plain annotation `α ∈ K`. -/
  | ann : K → LiftedTK T K
  /-- A formal K-tensor sum `Σ αᵢ ⊗ vᵢ : KTensor K T`. -/
  | ktensor : KTensor K T → LiftedTK T K

namespace LiftedTK

variable {T K : Type}

/-- Embed a `T ⊕ K` value into `LiftedTK T K`. -/
def ofSum (x : T ⊕ K) : LiftedTK T K :=
  match x with
  | Sum.inl t => .data t
  | Sum.inr k => .ann k

/-! ## Zero -/

instance [Zero K] : Zero (LiftedTK T K) := ⟨.ann 0⟩

@[simp] theorem zero_def [Zero K] : (0 : LiftedTK T K) = .ann 0 := rfl

/-! ## Addition

The same-kind cases use the underlying additive structure on `T`, `K`, or
`KTensor K T` (multiset union). The mixed cases follow the same "data wins"
convention as the existing `ValueType (T ⊕ K)` `Add`, with `0` (= `ann 0`)
absorbing into the other operand so that `0 + x = x` for every kind. This
is enough for the aggregation evaluator: the aggregator `f̂_j = sum`
operates within a single kind (the per-column term `t_j * #(k+1)` always
produces a `ktensor`; the per-row annotation `#(k+1) : δ(⊕)` always produces
an `ann`), and the fold's initial value is `0 = ann 0` which is absorbed by
the first non-zero summand. -/

instance [Add T] [Add K] : Add (LiftedTK T K) where
  add a b := match a, b with
    | .data x, .data y => .data (x + y)
    | .ann α, .ann β => .ann (α + β)
    | .ktensor t, .ktensor t' => .ktensor (t + t')
    -- 0 (= ann 0) absorbs into the other operand: caught by the catch-all below
    -- in conjunction with the `Zero K` placement.
    | .data x, .ann _ => .data x
    | .ann _, .data x => .data x
    | .ktensor t, .ann _ => .ktensor t
    | .ann _, .ktensor t => .ktensor t
    | .data x, .ktensor _ => .data x
    | .ktensor _, .data x => .data x

@[simp] theorem add_data_data [Add T] [Add K] (x y : T) :
    (.data x : LiftedTK T K) + .data y = .data (x + y) := rfl

@[simp] theorem add_ann_ann [Add T] [Add K] (α β : K) :
    (.ann α : LiftedTK T K) + .ann β = .ann (α + β) := rfl

@[simp] theorem add_ktensor_ktensor [Add T] [Add K] (t t' : KTensor K T) :
    (.ktensor t : LiftedTK T K) + .ktensor t' = .ktensor (t + t') := rfl

@[simp] theorem add_data_ann [Add T] [Add K] (x : T) (α : K) :
    (.data x : LiftedTK T K) + .ann α = .data x := rfl

@[simp] theorem add_ann_data [Add T] [Add K] (α : K) (x : T) :
    (.ann α : LiftedTK T K) + .data x = .data x := rfl

@[simp] theorem add_ktensor_ann [Add T] [Add K] (t : KTensor K T) (α : K) :
    (.ktensor t : LiftedTK T K) + .ann α = .ktensor t := rfl

@[simp] theorem add_ann_ktensor [Add T] [Add K] (α : K) (t : KTensor K T) :
    (.ann α : LiftedTK T K) + .ktensor t = .ktensor t := rfl

@[simp] theorem add_data_ktensor [Add T] [Add K] (x : T) (t : KTensor K T) :
    (.data x : LiftedTK T K) + .ktensor t = .data x := rfl

@[simp] theorem add_ktensor_data [Add T] [Add K] (t : KTensor K T) (x : T) :
    (.ktensor t : LiftedTK T K) + .data x = .data x := rfl

/-- The `Add` on `LiftedTK T K` is commutative whenever `T` and `K` are.
The mixed cases give the same result either way (data wins over ann and
ktensor; ktensor wins over ann), and same-kind cases inherit commutativity. -/
instance [AddCommSemigroup T] [AddCommSemigroup K] :
    @Std.Commutative (LiftedTK T K) (· + ·) where
  comm a b := by
    cases a <;> cases b <;> simp <;> exact add_comm _ _

/-- The `Add` on `LiftedTK T K` is associative whenever `T` and `K` are.
The mixed cases follow the priority order "data > ktensor > ann"; same-kind
cases inherit associativity from the underlying carriers. -/
instance [AddCommSemigroup T] [AddCommSemigroup K] :
    @Std.Associative (LiftedTK T K) (· + ·) where
  assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp <;> exact add_assoc _ _ _

/-! ## Subtraction

`LiftedTK` inherits `Sub` componentwise on same-kind operands; mixed cases
mirror the additive convention. R5 does not exercise `Sub` on mixed kinds,
so the specific choices on those cases are not load-bearing for correctness;
they are picked to keep `Sub` a total function. -/

instance [Sub T] [Sub K] : Sub (LiftedTK T K) where
  sub a b := match a, b with
    | .data x, .data y => .data (x - y)
    | .ann α, .ann β => .ann (α - β)
    | .ktensor t, .ktensor _ => .ktensor t  -- KTensor has no canonical Sub; keep lhs
    | .data x, _ => .data x
    | .ann α, _ => .ann α
    | .ktensor t, _ => .ktensor t

/-! ## Multiplication — the fix for R5

Same-kind multiplication uses the underlying `Mul` on `T`, `K`, or `KTensor`
(the last being the `KTensor.smul`-style action; here we take `KTensor *
KTensor` to be `0` since R5 does not exercise it, and we already know the
un-quotiented `Multiset (K × M)` is not closed under a meaningful "tensor of
tensors" operation).

The **mixed `data × ann` case** is the one that distinguishes `LiftedTK`
from `T ⊕ K`: instead of dropping `α`, it produces a single-monomial
K-tensor `α ⊗ v`. -/

variable [CommSemiringWithMonus K] [Mul T]

instance : Mul (LiftedTK T K) where
  mul a b := match a, b with
    | .data x, .data y => .data (x * y)
    | .ann α, .ann β => .ann (α * β)
    | .data v, .ann α => .ktensor (KTensor.embed α v)
    | .ann α, .data v => .ktensor (KTensor.embed α v)
    | .ktensor t, .ann β => .ktensor (KTensor.smul β t)
    | .ann β, .ktensor t => .ktensor (KTensor.smul β t)
    | .ktensor _, .ktensor _ => .ann 0  -- not exercised by R5
    | .data _, .ktensor _ => .ann 0      -- not exercised by R5
    | .ktensor _, .data _ => .ann 0      -- not exercised by R5

/-! ## Decidable equality

Decidable equality for `LiftedTK T K` requires it on `T`, `K`, and on
`KTensor K T`. The last reduces to decidable equality on `Multiset (K × T)`,
which is decidable from `DecidableEq K` and `DecidableEq T`. -/

instance [DecidableEq T] [DecidableEq K] : DecidableEq (LiftedTK T K)
  | .data x, .data y =>
      decidable_of_iff (x = y) ⟨fun h => h ▸ rfl, fun h => by injection h⟩
  | .ann α, .ann β =>
      decidable_of_iff (α = β) ⟨fun h => h ▸ rfl, fun h => by injection h⟩
  | .ktensor t, .ktensor t' =>
      let dec : Decidable ((t : Multiset (K × T)) = (t' : Multiset (K × T))) :=
        @Multiset.decidableEq _ instDecidableEqProd t t'
      match dec with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse (fun heq => h (by injection heq))
  | .data _, .ann _ => isFalse (by intro h; injection h)
  | .data _, .ktensor _ => isFalse (by intro h; injection h)
  | .ann _, .data _ => isFalse (by intro h; injection h)
  | .ann _, .ktensor _ => isFalse (by intro h; injection h)
  | .ktensor _, .data _ => isFalse (by intro h; injection h)
  | .ktensor _, .ann _ => isFalse (by intro h; injection h)

end LiftedTK

/-! ## Lifted view of an annotated relation

`AnnotatedRelation.toLifted` is the `LiftedTK`-tuple view of an annotated
relation: a row `(t, α)` becomes the `(n+1)`-tuple whose first `n`
entries are `data (t i)` and whose last entry is `ann α`. This is the
"Definition 7" representation of a non-aggregate `K`-annotated relation
in `V_K`-lifted form, mirroring `AnnotatedRelation.toComposite` (which
produces a `T ⊕ K`-tuple in the same shape).

The bridge `toLifted_eq_map_ofSum_toComposite` says that lifting an
annotated relation via `toLifted` agrees pointwise with
"go through `toComposite` and then `LiftedTK.ofSum` each entry", which
is exactly how `Query.evaluateInVK` interprets the non-Agg cases. This
lets us upgrade the existing `Query.rewriting_valid` (stated in
`toComposite` form) to the unified `Query.rewriting_valid_full` (stated
in `toLifted` form). -/

/-- Lifted view of an `AnnotatedTuple`: the `n` data entries become
`data v_i`, with the annotation appended as `ann α` in the last slot. -/
def AnnotatedTuple.toLifted {T K : Type} {n : ℕ} (p : AnnotatedTuple T K n) :
    Tuple (LiftedTK T K) (n + 1) :=
  Fin.append (fun k : Fin n => LiftedTK.data (p.fst k)) ![LiftedTK.ann p.snd]

/-- Lifted view of an `AnnotatedRelation`: pointwise `toLifted` on tuples. -/
def AnnotatedRelation.toLifted {T K : Type} {n : ℕ} (ar : AnnotatedRelation T K n) :
    Multiset (Tuple (LiftedTK T K) (n + 1)) :=
  ar.map AnnotatedTuple.toLifted

/-- The bridge: lifting an annotated tuple agrees pointwise with composite-
encoding followed by `LiftedTK.ofSum`. -/
theorem AnnotatedTuple.toLifted_eq_ofSum_toComposite {T K : Type} {n : ℕ}
    (p : AnnotatedTuple T K n) :
    p.toLifted = fun k => LiftedTK.ofSum (p.toComposite k) := by
  funext k
  unfold AnnotatedTuple.toLifted AnnotatedTuple.toComposite
  refine Fin.addCases ?_ ?_ k
  · -- k = Fin.castAdd 1 i, with i : Fin n
    intro i
    rw [Fin.append_left, Fin.append_left]
    rfl
  · -- k = Fin.natAdd n j, with j : Fin 1
    intro j
    rw [Fin.append_right, Fin.append_right]
    have hj : j = 0 := by
      ext; exact Nat.lt_one_iff.mp j.isLt
    subst hj
    rfl

/-- The bridge at the multiset level: `toLifted` agrees with
`toComposite ∘ map ofSum-on-tuples`. -/
theorem AnnotatedRelation.toLifted_eq_map_ofSum_toComposite {T K : Type} {n : ℕ}
    (ar : AnnotatedRelation T K n) :
    ar.toLifted = ar.toComposite.map (fun t => fun k => LiftedTK.ofSum (t k)) := by
  unfold AnnotatedRelation.toLifted AnnotatedRelation.toComposite
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  exact AnnotatedTuple.toLifted_eq_ofSum_toComposite p
