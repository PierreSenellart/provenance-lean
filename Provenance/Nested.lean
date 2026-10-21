/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.AggExpr

/-!
# Nested aggregate values

When the term of an aggregation or a window reads an aggregate column,
the aggregate value it builds is **nested**: what it aggregates, at
each of its occurrences, is not a value of the domain but another
aggregate value. Its occurrences are those of its own family `U`
*together with* those of the inner values, and its value in a world is
the outer aggregate applied to the inner values read in that world.

An `AggValue` cannot hold this: its reading consults its own occurrence
list alone. `NestedValue` carries, per outer occurrence, the inner
aggregate value the term reads there, and a `World` chooses which outer
occurrences are present *and* which occurrences of each inner family
are. An inner value may itself be nested, to any depth: `NestInner T K j`
is a value of storey `j`, an aggregate expression at storey `0` and an
expression or an inner node (`NestNode`) above it.

## Inner families are shared

Two outer occurrences may read one inner family: a join, a product or an
apply repeats a row carrying an aggregate value, and a grouping over the
result sees the value once per copy. The inner family is then **one**
family, decided once in each world, not once per copy – the inner
occurrences are objects, and an object is present or absent, not both.
So a world decides each family once: the value's own occurrences
(`World.root`), the positions kept of each expression family
(`World.leaf`) and the occurrences present of each inner node
(`World.node`), read through the decider that looks a family up by its
key (`World.dec`); a world's annotation counts each inner occurrence
once. Two inner expressions belong to one family when they carry the same
family identifier and the same occurrence annotations (`leafKey`), which
is how the joint reading of a selection groups the aggregate columns of a
row (`AggTok.classKey`); two inner nodes, when they carry the same family
identifier and the same occurrences (`NestNode.key`).

## No sequence, and so a bag

`≼` orders plain tuples, and an occurrence of a nested value carries a
tuple with an *aggregate* column, so there is nothing to order these
occurrences by: the family a nested value aggregates is a bag, and so is
each inner node's. Its aggregate is accordingly a function of a bag, a
world is made of bags of decisions, and `worlds` enumerates the worlds
off those bags.
Nothing indexes an occurrence, so no reading has to be shown invariant
under a relisting of the family, and an operator building a nested value
needs no order to list its group in – which is what it could not have, a
listing of a multiset not being computable.

## Which worlds count

A world meets the family of each grouped inner value **that it reads**,
which is to say each inner value at an outer occurrence the world keeps
– `World.IsWorld`. The condition is on the inner values read and not on
all of them: an outer occurrence absent from the world contributes
nothing to the value there, and asking its inner family to be met would
ask a group to be non-empty while the row carrying it is absent.

This is not the condition a *predicate*'s worlds satisfy, which meet
every grouped family the predicate mentions with no such conditionality
– and the difference is structural rather than an oversight. A
predicate's families all belong to one tuple, which exists or does not,
so demanding all of them demands that the tuple exist. A nested value's
inner families each belong to outer occurrences, and the world is
choosing which of those occurrences are present, so a blanket condition
would quantify over occurrences the world has already excluded.

Whether a world should also be *barred* from meeting an inner family no
present occurrence reads is settled in the negative (`World.IsWorldWith`
sets out why); the refuted reading is kept as `World.IsWorldCoherent` so
that its refutation can be stated.
-/

@[expose] public section

variable {T K : Type}

/-- A subfamily of one listing of a family read in another: the positions
with the same index. -/
def trW {a b : ℕ} (W : Finset (Fin a)) : Finset (Fin b) :=
  Finset.univ.filter (fun i => ∃ j ∈ W, (j : ℕ) = i)

/-- Reading a subfamily in a listing of the same length is reindexing it. -/
theorem trW_eq_map {a b : ℕ} (h : a = b) (W : Finset (Fin a)) :
    trW (b := b) W = W.map (finCongr h).toEmbedding := by
  ext i
  simp only [trW, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
  constructor
  · rintro ⟨j, hj, hji⟩
    convert hj using 1
    exact Fin.ext (by simp [hji])
  · intro hi
    exact ⟨(finCongr h).symm i, hi, by simp⟩

/-- Nothing read in another listing is nothing. -/
@[simp] theorem trW_empty {a b : ℕ} : trW (a := a) (b := b) ∅ = ∅ := by
  ext i
  simp [trW]

/-- Reading a reindexed subfamily is reading the subfamily. -/
theorem trW_map_finCongr {a a' b : ℕ} (h : a = a') (W : Finset (Fin a)) :
    trW (b := b) (W.map (finCongr h).toEmbedding) = trW W := by
  ext i
  simp only [trW, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact ⟨(finCongr h).symm j, hj, by simpa using hji⟩
  · rintro ⟨j, hj, hji⟩
    exact ⟨finCongr h j, by simpa using hj, by simpa using hji⟩

/-- Reading a subfamily in a reindexed listing. -/
theorem trW_trW_map {a b b' : ℕ} (h : b = b') (W : Finset (Fin a)) :
    trW (b := b') W = (trW (b := b) W).map (finCongr h).toEmbedding := by
  ext i
  simp only [trW, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
  rfl

/-! ## Storeys

A nested value reads, at each of its occurrences, an inner value that may
itself be nested. The types say how deep: `NestInner T K j` is what an
occurrence of a value of storey `j` reads – at storey `0` an aggregate
expression, at storey `j + 1` either something storey `j` reads or a
**node** of storey `j`, an outer aggregate over a bag of occurrences
reading storey-`j` values. A node can only hold inner values of lower
storeys, which is what makes every reading a recursion on the storey. -/

/-- **A node of a nested value**: an outer aggregate over a bag of
occurrences, each carrying what it reads (of type `X`) and its
annotation. -/
structure NestNode (T K X : Type) where
  /-- **The outer aggregate, as a function of a bag.** It cannot read a
  sequence: the order `≼` is an order on plain tuples, and an occurrence
  of a nested value carries a tuple with an aggregate column, so there is
  no sequence for an order-dependent aggregate to read. An ordinary
  aggregate becomes one of these when it is symmetric
  (`SeqAggFunc.onBag`), and an order-dependent outer aggregate has no
  nested reading at all – it goes through the alternatives
  (`AggQueryIn.Explode`), after which nothing is nested. -/
  agg : Multiset T → T
  /-- **The occurrences**: per occurrence, what the term reads there and
  the occurrence's own annotation. A bag, for the reason the aggregate is
  a function of one – nothing orders a tuple with an aggregate column. -/
  occs : Multiset (X × K)
  /-- Whether the outer reading is scalar – whether the empty world is
  one of its worlds. -/
  scalar : Bool
  /-- Which occurrence family the value reads (`AggValue.fam`). -/
  fam : FamId T

/-- **What an occurrence of a nested value of storey `j` reads.** At
storey `0`, an aggregate expression: a term over several aggregate
columns is one – `sum(c₁ - c₂)` over a block with two counts is as
ordinary as `avg(c)` over one – and an ordinary token embeds as the
expression of itself (`AggExpr.ofValue`). At storey `j + 1`, what storey
`j` reads, or a node of storey `j`. -/
def NestInner (T K : Type) : ℕ → Type
  | 0 => AggExpr T K
  | j + 1 => NestInner T K j ⊕ NestNode T K (NestInner T K j)

/-- **A nested aggregate value**: a node of some storey. Storey `0` is a
value whose occurrences read aggregate expressions; storey `j + 1` one
whose occurrences may read nested values of storey `j` and below. -/
structure NestedValue (T K : Type) where
  /-- The storey. -/
  lev : ℕ
  /-- The outer aggregate (`NestNode.agg`). -/
  agg : Multiset T → T
  /-- The occurrences (`NestNode.occs`). -/
  occs : Multiset (NestInner T K lev × K)
  /-- Whether the outer reading is scalar. -/
  scalar : Bool
  /-- Which occurrence family the value reads. -/
  fam : FamId T

/-! ## Which occurrences are one

A nested value's occurrences are its own **and** those of every value it
reads, at every storey, and an occurrence is one object however many
times it is read. Two outer occurrences may read one inner family: a join,
a product or an apply repeats a row carrying an aggregate value, and a
grouping over the result sees the value once per copy. The inner family
is then one family, decided once in each world – the inner occurrences
are objects, and an object is present or absent, not both. The same holds
one storey up: a nested value repeated by a join, then read by a
second-level grouping, has its occurrences decided once.

So a world decides each **family** once. An aggregate expression's family
is keyed by its family identifier and its annotations (`leafKey`) – the
key a joint reading groups a row's aggregate columns by
(`AggTok.classKey`); a node's occurrences by its family identifier and the
occurrences themselves (`NestNode.key`). -/

/-- **The key of an expression's family**: its family identifier and its
occurrence annotations. -/
abbrev LeafKey (T K : Type) := (ℕ × List T × List (T ⊕ FamId T)) × List K

/-- The key of an expression's family. -/
def leafKey (e : AggExpr T K) : LeafKey T K := (e.fam.family, e.annList)

/-- **The key of a node's occurrences**: its family identifier and its
occurrences. -/
abbrev NodeKey (T K : Type) (j : ℕ) :=
  (ℕ × List T × List (T ⊕ FamId T)) × Multiset (NestInner T K j × K)

/-- The key of a node's occurrences. -/
def NestNode.key {j : ℕ} (N : NestNode T K (NestInner T K j)) : NodeKey T K j :=
  (N.fam.family, N.occs)

instance [DecidableEq T] [DecidableEq K] : DecidableEq (LeafKey T K) :=
  @instDecidableEqProd _ _ FamId.instDecidableEqFamily inferInstance

namespace NestInner

/-- **The expression families an inner value reads**, with repetition. -/
def leaves : (j : ℕ) → NestInner T K j → Multiset (LeafKey T K)
  | 0, e => {leafKey (T := T) (K := K) e}
  | j + 1, Sum.inl x => leaves j x
  | j + 1, Sum.inr N => N.occs.bind (fun o => leaves j o.1)

/-- **The nodes an inner value reads**, each with its storey, with
repetition. -/
def nodes : (j : ℕ) → NestInner T K j → Multiset (Σ i, NodeKey T K i)
  | 0, _ => 0
  | j + 1, Sum.inl x => nodes j x
  | j + 1, Sum.inr N => ⟨j, N.key⟩ ::ₘ N.occs.bind (fun o => nodes j o.1)

/-- **The deterministic reading**: every occurrence present. -/
def collapse : (j : ℕ) → NestInner T K j → T
  | 0, e => AggExpr.collapse (T := T) (K := K) e
  | j + 1, Sum.inl x => collapse j x
  | j + 1, Sum.inr N => N.agg (N.occs.map (fun o => collapse j o.1))

end NestInner

namespace NestedValue

/-- The value as a node of its storey. -/
def toNode (a : NestedValue T K) : NestNode T K (NestInner T K a.lev) :=
  ⟨a.agg, a.occs, a.scalar, a.fam⟩

/-- The value of a node of storey `j`. -/
def ofNode {j : ℕ} (N : NestNode T K (NestInner T K j)) : NestedValue T K :=
  ⟨j, N.agg, N.occs, N.scalar, N.fam⟩

/-- **The nested value of a bag of occurrences.** -/
def ofOccs (agg : Multiset T → T) {j : ℕ} (U : Multiset (NestInner T K j × K))
    (scalar : Bool) (fam : FamId T) : NestedValue T K :=
  ⟨j, agg, U, scalar, fam⟩

@[simp] theorem agg_ofOccs (agg : Multiset T → T) {j : ℕ} (U : Multiset (NestInner T K j × K))
    (scalar : Bool) (fam : FamId T) : (ofOccs agg U scalar fam).agg = agg := rfl

@[simp] theorem lev_ofOccs (agg : Multiset T → T) {j : ℕ} (U : Multiset (NestInner T K j × K))
    (scalar : Bool) (fam : FamId T) : (ofOccs agg U scalar fam).lev = j := rfl

@[simp] theorem occs_ofOccs (agg : Multiset T → T) {j : ℕ} (U : Multiset (NestInner T K j × K))
    (scalar : Bool) (fam : FamId T) : (ofOccs agg U scalar fam).occs = U := rfl

@[simp] theorem scalar_ofOccs (agg : Multiset T → T) {j : ℕ}
    (U : Multiset (NestInner T K j × K)) (scalar : Bool) (fam : FamId T) :
    (ofOccs agg U scalar fam).scalar = scalar := rfl

@[simp] theorem fam_ofOccs (agg : Multiset T → T) {j : ℕ} (U : Multiset (NestInner T K j × K))
    (scalar : Bool) (fam : FamId T) : (ofOccs agg U scalar fam).fam = fam := rfl

variable [DecidableEq T] [DecidableEq K]

/-- **The expression families of a nested value**, each once. -/
def leaves (a : NestedValue T K) : Multiset (LeafKey T K) :=
  (a.occs.bind (fun o => NestInner.leaves a.lev o.1)).dedup

open Classical in
/-- **The inner nodes of a nested value**, each once. Two nodes are one
when their keys are, and a key carries inner values, so they are compared
classically: a value of storey `0` has no inner node, and nothing is
compared there. -/
noncomputable def nodes (a : NestedValue T K) : Multiset (Σ i, NodeKey T K i) :=
  (a.occs.bind (fun o => NestInner.nodes a.lev o.1)).dedup

theorem nodup_leaves (a : NestedValue T K) : a.leaves.Nodup := Multiset.nodup_dedup _

open Classical in
theorem nodup_nodes (a : NestedValue T K) : a.nodes.Nodup := by
  unfold nodes; exact Multiset.nodup_dedup _

/-- The deterministic reading: the outer aggregate of the inner
collapses. -/
def collapse (a : NestedValue T K) : T :=
  a.agg (a.occs.map (fun o => NestInner.collapse a.lev o.1))

end NestedValue

/-! ## Reading under a decision

A world is a decision about every occurrence a value holds. The readings
are written against a **decider** – what is kept of each expression
family (by position) and of each node's occurrences (each with a presence
flag) – so that a world read off the enumeration and the world a valuation
cuts out are read by one recursion. -/

/-- **A decision about every family**: the positions kept of each
expression family, and of each node's occurrences, each with whether it
is present. -/
structure NestDec (T K : Type) where
  /-- The positions kept of an expression family. -/
  leaf : LeafKey T K → Finset ℕ
  /-- The occurrences of a node, each with whether it is present. -/
  node : (j : ℕ) → NodeKey T K j → Multiset (NestInner T K j × K × Bool)

/-- **A set of positions, read on a family of a given length.** -/
def trS {n : ℕ} (S : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i : ℕ) ∈ S)

@[simp] theorem mem_trS {n : ℕ} (S : Finset ℕ) (i : Fin n) : i ∈ (trS S : Finset (Fin n)) ↔ (i : ℕ) ∈ S := by
  simp [trS]

namespace NestInner

/-- **The value an inner value reads under a decision.** -/
def val (D : NestDec T K) : (j : ℕ) → NestInner T K j → T
  | 0, e => AggExpr.valOn (T := T) (K := K) e (trS (D.leaf (leafKey (T := T) (K := K) e)))
  | j + 1, Sum.inl x => val D j x
  | j + 1, Sum.inr N => N.agg (((D.node j N.key).filter (fun m => m.2.2 = true)).map
      (fun m => val D j m.1))

/-- **Whether a decision is a world of an inner value**: each expression
family it reads met where its leaves are grouped (`AggExpr.IsWorld`), and
each node it reads met unless scalar – and, of each node, only the
occurrences the decision keeps are asked anything. The condition is
one-directional: a present occurrence asks its inner family to be met, a
met inner family does not make an occurrence present. -/
def ok (D : NestDec T K) : (j : ℕ) → NestInner T K j → Prop
  | 0, e => AggExpr.IsWorld (T := T) (K := K) e (trS (D.leaf (leafKey (T := T) (K := K) e)))
  | j + 1, Sum.inl x => ok D j x
  | j + 1, Sum.inr N => (N.scalar = true ∨ ∃ m ∈ D.node j N.key, m.2.2 = true)
      ∧ ∀ m ∈ D.node j N.key, m.2.2 = true → ok D j m.1

/-- Whether a decision is a world of an inner value is decidable. -/
def decOk (D : NestDec T K) : (j : ℕ) → (x : NestInner T K j) → Decidable (ok D j x)
  | 0, e => inferInstanceAs (Decidable (AggExpr.IsWorld (T := T) (K := K) e _))
  | j + 1, Sum.inl x => decOk D j x
  | j + 1, Sum.inr N =>
    haveI : ∀ x, Decidable (ok D j x) := decOk D j
    haveI : Decidable (∃ m ∈ D.node j N.key, m.2.2 = true) := Multiset.decidableExistsMultiset
    inferInstanceAs (Decidable ((N.scalar = true ∨ ∃ m ∈ D.node j N.key, m.2.2 = true)
      ∧ ∀ m ∈ D.node j N.key, m.2.2 = true → ok D j m.1))

instance (D : NestDec T K) (j : ℕ) (x : NestInner T K j) : Decidable (ok D j x) :=
  decOk D j x

end NestInner

/-! ## Worlds

A world of a nested value decides its own occurrences (`root`), each
expression family once (`leaf`, the positions kept) and each inner node
once (`node`, its occurrences with presence flags). It is read through
the decider looking each family up by its key. -/

/-- **A world of a nested value of storey `d`.** -/
structure NestedValue.World (T K : Type) (d : ℕ) where
  /-- The value's own occurrences, each with whether it is present. -/
  root : Multiset (NestInner T K d × K × Bool)
  /-- Each expression family, with the positions kept. -/
  leaf : Multiset (LeafKey T K × Finset ℕ)
  /-- Each inner node, with its occurrences and whether each is
  present. -/
  node : Multiset (Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool))

namespace NestedValue

/-- The positions an expression family keeps, looked up by key. -/
def leafSub [DecidableEq T] [DecidableEq K] (L : Multiset (LeafKey T K × Finset ℕ))
    (κ : LeafKey T K) : Finset ℕ :=
  ((L.filter (fun e => e.1 = κ)).map Prod.snd).sup

open Classical in
/-- The decision about a node's occurrences, looked up by key. -/
noncomputable def nodeDec (N : Multiset (Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool)))
    (j : ℕ) (κ : NodeKey T K j) : Multiset (NestInner T K j × K × Bool) :=
  N.bind (fun e => match e with
    | ⟨i, κ', D⟩ => if h : i = j then (by subst h; exact if κ' = κ then D else 0) else 0)

/-- **The decider a world reads by.** -/
noncomputable def World.dec [DecidableEq T] [DecidableEq K] {d : ℕ} (W : World T K d) :
    NestDec T K :=
  ⟨leafSub W.leaf, nodeDec W.node⟩

variable [DecidableEq T] [DecidableEq K]

/-- **The inner values a world reads**: one per outer occurrence it
keeps. The outer family is met when this is not empty, and the value read
in the world is the outer aggregate of it. -/
noncomputable def World.kept {d : ℕ} (W : World T K d) : Multiset T :=
  (W.root.filter (fun m => m.2.2 = true)).map (fun m => NestInner.val W.dec d m.1)

/-- **Whose world it is**: it decides on exactly the value's own
occurrences, expression families and inner nodes, each family's kept
positions among its own. -/
def World.IsWorldOf (a : NestedValue T K) (W : World T K a.lev) : Prop :=
  W.root.map (fun m => (m.1, m.2.1)) = a.occs ∧ W.leaf.map Prod.fst = a.leaves
    ∧ (∀ e ∈ W.leaf, e.2 ⊆ Finset.range e.1.2.length)
    ∧ W.node.map (fun e => ⟨e.1, e.2.1⟩) = a.nodes
    ∧ (∀ e ∈ W.node, e.2.2.map (fun m => (m.1, m.2.1)) = e.2.1.2)

/-- **Admissibility, with the coherence condition as a parameter.**
`extra` is the clause asking whether a world is barred from meeting an
inner family no present occurrence reads. The reading is `IsWorld`,
`extra` vacuous: barring it is not a convention but wrong.

Why: the world a valuation realizes sets an occurrence present exactly
when the valuation makes its *outer* annotation true, and keeps the inner
occurrences it makes true, independently (`realizedWorld`). A selection
on an aggregate value brings a failing group's row to `𝟘` while its
aggregate column stays realized, so the actual world keeps the inner
occurrences of an absent outer one. Barring that configuration removes
the world as it is: over `𝔹` the two readings give `⊤` and `𝟘` on
`nestedIncoherentWitness` (in `HavingQueryCounterexamples`;
`nestedIncoherent_ne_coherent`, `realizedWorld_not_coherent`), so a
coherent reading would contradict `World.ann_eval_iff` and the
possible-world results resting on it.

The condition is one-directional and must be: a present outer occurrence
needs its inner family met, but a met family does **not** make its
occurrence present. The parameter stays because it is what the two
readings are compared through. -/
def World.IsWorldWith {d : ℕ} (W : World T K d) (a : NestedValue T K)
    (extra : World T K d → Prop) : Prop :=
  (a.scalar = true ∨ 0 < Multiset.card W.kept)
    ∧ (∀ m ∈ W.root, m.2.2 = true → NestInner.ok W.dec d m.1)
    ∧ extra W

/-- **The worlds a nested value admits**: the outer family met unless
the reading is scalar, and, of each inner value *the world reads*, its
own world condition (`NestInner.ok`) – each grouped expression family
met, each grouped node met, recursively along the occurrences kept. -/
def World.IsWorld {d : ℕ} (W : World T K d) (a : NestedValue T K) : Prop :=
  W.IsWorldWith a (fun _ => True)

/-- The reading that bars a world from meeting an expression family no
present occurrence of the value reads directly. **Refuted**, not an
alternative: it removes the world a valuation realizes where a selection
has brought an outer annotation to `𝟘`, which `IsWorldWith`'s docstring
sets out. Kept so that the refutation can be stated. -/
def World.IsWorldCoherent {d : ℕ} (W : World T K d) (a : NestedValue T K) : Prop :=
  W.IsWorldWith a (fun W => ∀ e ∈ W.leaf,
    (∀ m ∈ W.root, m.2.2 = true → e.1 ∉ NestInner.leaves d m.1) → e.2 = ∅)

noncomputable instance {d : ℕ} (W : World T K d) (a : NestedValue T K) :
    Decidable (W.IsWorld a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The value of a nested aggregate in a world**: the outer aggregate
of the bag of inner values read there. -/
noncomputable def valOn {d : ℕ} (a : NestedValue T K) (W : World T K d) : T :=
  a.agg W.kept

end NestedValue

/-! ## Looking a family up -/

namespace NestedValue

theorem filter_fst_eq_singleton {α β : Type} [DecidableEq α] {L : Multiset (α × β)}
    (hnd : (L.map Prod.fst).Nodup) {a : α} {b : β} (h : (a, b) ∈ L) :
    L.filter (fun e => e.1 = a) = {(a, b)} := by
  obtain ⟨L', rfl⟩ := Multiset.exists_cons_of_mem h
  rw [Multiset.map_cons, Multiset.nodup_cons] at hnd
  have h0 : L'.filter (fun e => e.1 = a) = 0 := Multiset.filter_eq_nil.mpr
    (fun e he hea => hnd.1 (by
      show a ∈ L'.map Prod.fst; rw [← hea]; exact Multiset.mem_map_of_mem Prod.fst he))
  rw [Multiset.filter_cons, h0]
  simp

theorem leafSub_of_mem [DecidableEq T] [DecidableEq K] {L : Multiset (LeafKey T K × Finset ℕ)}
    (hnd : (L.map Prod.fst).Nodup) {κ : LeafKey T K} {S : Finset ℕ} (h : (κ, S) ∈ L) :
    leafSub L κ = S := by
  unfold leafSub
  rw [filter_fst_eq_singleton hnd h]
  simp

open Classical in
theorem nodeDec_cons_self (N : Multiset (Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool)))
    {j : ℕ} (κ κ' : NodeKey T K j) (D : Multiset (NestInner T K j × K × Bool)) :
    nodeDec (⟨j, κ', D⟩ ::ₘ N) j κ = (if κ' = κ then D else 0) + nodeDec N j κ := by
  unfold nodeDec
  rw [Multiset.cons_bind]
  simp

open Classical in
theorem nodeDec_eq_zero {N : Multiset (Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool))}
    {j : ℕ} {κ : NodeKey T K j}
    (h : ∀ e ∈ N, (⟨e.1, e.2.1⟩ : Σ i, NodeKey T K i) ≠ ⟨j, κ⟩) : nodeDec N j κ = 0 := by
  unfold nodeDec
  rw [Multiset.bind, Multiset.join, Multiset.sum_eq_zero]
  intro x hx
  obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨i, κ', D⟩ := e
  dsimp only
  by_cases hij : i = j
  · subst hij
    have hne : κ' ≠ κ := fun hk => h _ he (by rw [hk])
    simp [hne]
  · simp [hij]

theorem nodeDec_of_mem {N : Multiset (Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool))}
    (hnd : (N.map (fun e => (⟨e.1, e.2.1⟩ : Σ i, NodeKey T K i))).Nodup) {j : ℕ}
    {κ : NodeKey T K j} {D : Multiset (NestInner T K j × K × Bool)} (h : ⟨j, κ, D⟩ ∈ N) :
    nodeDec N j κ = D := by
  classical
  obtain ⟨N', rfl⟩ := Multiset.exists_cons_of_mem h
  rw [Multiset.map_cons, Multiset.nodup_cons] at hnd
  rw [nodeDec_cons_self, nodeDec_eq_zero, add_zero]
  · simp
  intro e he hek
  exact hnd.1 (hek ▸ Multiset.mem_map_of_mem _ he)

end NestedValue

/-! ## Reading with the support fixed

What an inner value reads depends on the decision only at the families it
reads. -/

namespace NestInner

/-- **Two decisions that agree on what an inner value reads read it
alike**, the second deciding each node it reads on that node's own
occurrences. -/
theorem val_congr (D D' : NestDec T K) : ∀ (j : ℕ) (x : NestInner T K j),
    (∀ κ ∈ leaves j x, D.leaf κ = D'.leaf κ) →
    (∀ e ∈ nodes j x, D.node e.1 e.2 = D'.node e.1 e.2
      ∧ (D'.node e.1 e.2).map (fun m => (m.1, m.2.1)) = e.2.2) →
    val D j x = val D' j x
  | 0, e, hl, _ => by
    show AggExpr.valOn e _ = AggExpr.valOn e _
    rw [hl _ (Multiset.mem_singleton_self _)]
  | j + 1, Sum.inl x, hl, hn => val_congr D D' j x hl hn
  | j + 1, Sum.inr N, hl, hn => by
    show N.agg _ = N.agg _
    obtain ⟨heq, hproj⟩ := hn ⟨j, N.key⟩ (Multiset.mem_cons_self _ _)
    rw [heq]
    refine congrArg N.agg (Multiset.map_congr rfl (fun m hm => ?_))
    have hm' : (m.1, m.2.1) ∈ N.occs := by
      have := Multiset.mem_map_of_mem (fun m => (m.1, m.2.1)) (Multiset.mem_of_mem_filter hm)
      rwa [hproj] at this
    refine val_congr D D' j m.1 (fun κ hκ => hl κ ?_) (fun e he => hn e ?_)
    · exact Multiset.mem_bind.mpr ⟨_, hm', hκ⟩
    · exact Multiset.mem_cons_of_mem (Multiset.mem_bind.mpr ⟨_, hm', he⟩)

/-- **And agree on whether it is a world.** -/
theorem ok_congr (D D' : NestDec T K) : ∀ (j : ℕ) (x : NestInner T K j),
    (∀ κ ∈ leaves j x, D.leaf κ = D'.leaf κ) →
    (∀ e ∈ nodes j x, D.node e.1 e.2 = D'.node e.1 e.2
      ∧ (D'.node e.1 e.2).map (fun m => (m.1, m.2.1)) = e.2.2) →
    (ok D j x ↔ ok D' j x)
  | 0, e, hl, _ => by
    show AggExpr.IsWorld e _ ↔ AggExpr.IsWorld e _
    rw [hl _ (Multiset.mem_singleton_self _)]
  | j + 1, Sum.inl x, hl, hn => ok_congr D D' j x hl hn
  | j + 1, Sum.inr N, hl, hn => by
    show (_ ∧ _) ↔ (_ ∧ _)
    obtain ⟨heq, hproj⟩ := hn ⟨j, N.key⟩ (Multiset.mem_cons_self _ _)
    rw [heq]
    refine and_congr Iff.rfl (forall₂_congr (fun m hm => imp_congr Iff.rfl ?_))
    have hm' : (m.1, m.2.1) ∈ N.occs := by
      have := Multiset.mem_map_of_mem (fun m => (m.1, m.2.1)) hm
      rwa [hproj] at this
    refine ok_congr D D' j m.1 (fun κ hκ => hl κ ?_) (fun e he => hn e ?_)
    · exact Multiset.mem_bind.mpr ⟨_, hm', hκ⟩
    · exact Multiset.mem_cons_of_mem (Multiset.mem_bind.mpr ⟨_, hm', he⟩)

/-- **The full decision**: everything kept. -/
def fullDec : NestDec T K :=
  ⟨fun κ => Finset.range κ.2.length, fun _ κ => κ.2.map (fun o => (o.1, o.2, true))⟩

theorem trS_range (e : AggExpr T K) :
    (trS (Finset.range (leafKey e).2.length) : Finset (Fin e.occs.length)) = Finset.univ := by
  ext i
  simp [leafKey, AggExpr.annList, i.isLt]

/-- **Everything kept reads as the collapse.** -/
theorem val_fullDec : ∀ (j : ℕ) (x : NestInner T K j), val fullDec j x = collapse j x
  | 0, e => by
    show AggExpr.valOn e (trS (Finset.range (leafKey e).2.length)) = AggExpr.collapse e
    rw [trS_range]
    rfl
  | j + 1, Sum.inl x => val_fullDec j x
  | j + 1, Sum.inr N => by
    show N.agg _ = N.agg _
    refine congrArg N.agg ?_
    show (((N.occs.map (fun o => (o.1, o.2, true))).filter (fun m => m.2.2 = true)).map _) = _
    rw [Multiset.filter_eq_self.mpr (fun m hm => by
      obtain ⟨o, -, rfl⟩ := Multiset.mem_map.mp hm; rfl), Multiset.map_map]
    exact Multiset.map_congr rfl (fun o _ => val_fullDec j o.1)

/-- **The decision a valuation of the annotations makes**: it keeps the
occurrences, of every family and every node, whose annotations it makes
true. -/
def realDec (ν : K → Bool) : NestDec T K :=
  ⟨fun κ => (Finset.range κ.2.length).filter (fun i => ∃ h : i < κ.2.length, ν (κ.2.get ⟨i, h⟩)),
    fun _ κ => κ.2.map (fun o => (o.1, o.2, ν o.2))⟩

/-- **The world-faithful reading** of an inner value under a valuation. -/
def specialize (ν : K → Bool) (j : ℕ) (x : NestInner T K j) : T := val (realDec ν) j x

theorem trS_realDec (e : AggExpr T K) (ν : K → Bool) :
    (trS ((realDec (T := T) ν).leaf (leafKey e)) : Finset (Fin e.occs.length))
      = e.realizedWorld ν := by
  ext i
  simp [realDec, leafKey, AggExpr.realizedWorld, AggExpr.annList, AggExpr.anns, i.isLt]

theorem specialize_zero (ν : K → Bool) (e : AggExpr T K) :
    specialize ν 0 e = AggExpr.specialize e ν := by
  show AggExpr.valOn e _ = _
  rw [trS_realDec]
  rfl

theorem specialize_inl (ν : K → Bool) {j : ℕ} (x : NestInner T K j) :
    specialize ν (j + 1) (Sum.inl x) = specialize ν j x := rfl

theorem specialize_inr (ν : K → Bool) {j : ℕ} (N : NestNode T K (NestInner T K j)) :
    specialize ν (j + 1) (Sum.inr N)
      = N.agg ((N.occs.filter (fun o => ν o.2 = true)).map (fun o => specialize ν j o.1)) := by
  show N.agg _ = N.agg _
  refine congrArg N.agg ?_
  show (((N.occs.map (fun o => (o.1, o.2, ν o.2))).filter (fun m => m.2.2 = true)).map _) = _
  rw [Multiset.filter_map, Multiset.map_map]
  rfl

end NestInner

/-! ## The worlds of a nested value, enumerated

The worlds are the decisions one can make about each family – at each of
the value's own occurrences and each inner node's, present or not; at each
expression family, which positions are kept – so they are built by
running over the families and letting every world so far gain every
decision available at the next one. Everything is a bag and the
construction has to be read off it rather than off a listing, which is
what the steps being left-commutative says – and the multiplicities are
kept: two occurrences carrying the same inner value and the same
annotation are two occurrences, and a world may keep one and drop the
other. -/

namespace NestedValue

section Enumeration

variable {X : Type}

/-- The presence decisions over a bag of occurrences. -/
def addMem (o : X × K) (acc : Multiset (Multiset (X × K × Bool))) :
    Multiset (Multiset (X × K × Bool)) :=
  ({true, false} : Multiset Bool).bind (fun b => acc.map (fun ms => (o.1, o.2, b) ::ₘ ms))

instance : LeftCommutative (addMem (X := X) (K := K)) where
  left_comm o₁ o₂ acc := by
    unfold addMem
    simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]
    rw [Multiset.bind_bind]
    exact Multiset.bind_congr (fun b₂ _ => Multiset.bind_congr
      (fun b₁ _ => Multiset.map_congr rfl (fun ms _ => Multiset.cons_swap _ _ _)))

/-- Every choice of presence over a bag of occurrences. -/
def memChoices (M : Multiset (X × K)) : Multiset (Multiset (X × K × Bool)) :=
  M.foldr addMem {0}

theorem map_of_mem_memChoices {M : Multiset (X × K)} {ms : Multiset (X × K × Bool)}
    (h : ms ∈ memChoices M) : ms.map (fun m => (m.1, m.2.1)) = M := by
  induction M using Multiset.induction_on generalizing ms with
  | empty =>
    rw [memChoices, Multiset.foldr_zero, Multiset.mem_singleton] at h
    rw [h, Multiset.map_zero]
  | cons o M ih =>
    rw [memChoices, Multiset.foldr_cons, addMem] at h
    obtain ⟨b, -, hb⟩ := Multiset.mem_bind.mp h
    obtain ⟨ms', hms', rfl⟩ := Multiset.mem_map.mp hb
    rw [Multiset.map_cons, ih hms']

theorem mem_memChoices_of_map : ∀ {ms : Multiset (X × K × Bool)} {M : Multiset (X × K)},
    ms.map (fun m => (m.1, m.2.1)) = M → ms ∈ memChoices M := by
  intro ms
  induction ms using Multiset.induction_on with
  | empty =>
    intro M h
    rw [Multiset.map_zero] at h
    subst h
    exact Multiset.mem_singleton_self _
  | cons m ms ih =>
    intro M h
    rw [Multiset.map_cons] at h
    subst h
    rw [memChoices, Multiset.foldr_cons, addMem]
    refine Multiset.mem_bind.mpr ⟨m.2.2, by cases m.2.2 <;> simp, ?_⟩
    exact Multiset.mem_map.mpr ⟨ms, ih rfl, rfl⟩

theorem mem_memChoices_iff {M : Multiset (X × K)} {ms : Multiset (X × K × Bool)} :
    ms ∈ memChoices M ↔ ms.map (fun m => (m.1, m.2.1)) = M :=
  ⟨map_of_mem_memChoices, mem_memChoices_of_map⟩

/-- The positions one can keep of an expression family. -/
def addLeaf (κ : LeafKey T K) (acc : Multiset (Multiset (LeafKey T K × Finset ℕ))) :
    Multiset (Multiset (LeafKey T K × Finset ℕ)) :=
  (Finset.range κ.2.length).powerset.val.bind (fun S => acc.map ((κ, S) ::ₘ ·))

instance : LeftCommutative (addLeaf (T := T) (K := K)) where
  left_comm κ₁ κ₂ acc := by
    unfold addLeaf
    simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]
    rw [Multiset.bind_bind]
    exact Multiset.bind_congr (fun S₂ _ => Multiset.bind_congr
      (fun S₁ _ => Multiset.map_congr rfl (fun ms _ => Multiset.cons_swap _ _ _)))

/-- The decisions one can make about a node's occurrences. -/
def addNode (κ : Σ j, NodeKey T K j)
    (acc : Multiset (Multiset (Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool)))) :
    Multiset (Multiset (Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool))) :=
  (memChoices κ.2.2).bind (fun D => acc.map (⟨κ.1, κ.2, D⟩ ::ₘ ·))

instance : LeftCommutative (addNode (T := T) (K := K)) where
  left_comm κ₁ κ₂ acc := by
    unfold addNode
    simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]
    rw [Multiset.bind_bind]
    exact Multiset.bind_congr (fun S₂ _ => Multiset.bind_congr
      (fun S₁ _ => Multiset.map_congr rfl (fun ms _ => Multiset.cons_swap _ _ _)))

theorem mem_foldr_addLeaf_iff : ∀ {s : Multiset (LeafKey T K)}
    {L : Multiset (LeafKey T K × Finset ℕ)},
    L ∈ s.foldr addLeaf {0} ↔ L.map Prod.fst = s ∧ ∀ e ∈ L, e.2 ⊆ Finset.range e.1.2.length := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro L
    rw [Multiset.foldr_zero, Multiset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact Multiset.map_eq_zero.mp h
  | cons κ s ih =>
    intro L
    rw [Multiset.foldr_cons, addLeaf]
    constructor
    · intro h
      obtain ⟨S, hS, hL⟩ := Multiset.mem_bind.mp h
      obtain ⟨L', hL', rfl⟩ := Multiset.mem_map.mp hL
      obtain ⟨h1, h2⟩ := ih.mp hL'
      refine ⟨by rw [Multiset.map_cons, h1], fun e he => ?_⟩
      rcases Multiset.mem_cons.mp he with rfl | he
      · exact Finset.mem_powerset.mp (Finset.mem_val.mp hS)
      · exact h2 e he
    · rintro ⟨h1, h2⟩
      have hκ : κ ∈ L.map Prod.fst := by rw [h1]; exact Multiset.mem_cons_self _ _
      obtain ⟨e, he, hek⟩ := Multiset.mem_map.mp hκ
      obtain ⟨L', rfl⟩ := Multiset.exists_cons_of_mem he
      refine Multiset.mem_bind.mpr ⟨e.2, Finset.mem_val.mpr (Finset.mem_powerset.mpr ?_), ?_⟩
      · have := h2 e (Multiset.mem_cons_self _ _); rwa [hek] at this
      · refine Multiset.mem_map.mpr ⟨L', ih.mpr ⟨?_, fun e' he' => h2 e'
          (Multiset.mem_cons_of_mem he')⟩, ?_⟩
        · rw [Multiset.map_cons, hek] at h1; exact Multiset.cons_inj_right _ |>.mp h1
        · rw [← hek]
    
theorem mem_foldr_addNode_iff : ∀ {s : Multiset (Σ j, NodeKey T K j)}
    {N : Multiset (Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool))},
    N ∈ s.foldr addNode {0} ↔ N.map (fun e => (⟨e.1, e.2.1⟩ : Σ j, NodeKey T K j)) = s
      ∧ ∀ e ∈ N, e.2.2.map (fun m => (m.1, m.2.1)) = e.2.1.2 := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro N
    rw [Multiset.foldr_zero, Multiset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact Multiset.map_eq_zero.mp h
  | cons κ s ih =>
    intro N
    rw [Multiset.foldr_cons, addNode]
    constructor
    · intro h
      obtain ⟨D, hD, hN⟩ := Multiset.mem_bind.mp h
      obtain ⟨N', hN', rfl⟩ := Multiset.mem_map.mp hN
      obtain ⟨h1, h2⟩ := ih.mp hN'
      refine ⟨by rw [Multiset.map_cons, h1], fun e he => ?_⟩
      rcases Multiset.mem_cons.mp he with rfl | he
      · exact map_of_mem_memChoices hD
      · exact h2 e he
    · rintro ⟨h1, h2⟩
      have hκ : κ ∈ N.map (fun e => (⟨e.1, e.2.1⟩ : Σ j, NodeKey T K j)) := by
        rw [h1]; exact Multiset.mem_cons_self _ _
      obtain ⟨e, he, hek⟩ := Multiset.mem_map.mp hκ
      obtain ⟨N', rfl⟩ := Multiset.exists_cons_of_mem he
      subst hek
      refine Multiset.mem_bind.mpr ⟨e.2.2, mem_memChoices_of_map
        (h2 e (Multiset.mem_cons_self _ _)), ?_⟩
      refine Multiset.mem_map.mpr ⟨N', ih.mpr ⟨?_, fun e' he' => h2 e'
        (Multiset.mem_cons_of_mem he')⟩, rfl⟩
      rw [Multiset.map_cons] at h1; exact Multiset.cons_inj_right _ |>.mp h1

variable [DecidableEq T] [DecidableEq K]

/-- **The worlds of a nested value.** -/
noncomputable def worlds (a : NestedValue T K) : Multiset (World T K a.lev) :=
  (memChoices a.occs).bind (fun R => (a.leaves.foldr addLeaf {0}).bind
    (fun L => (a.nodes.foldr addNode {0}).map (fun N => ⟨R, L, N⟩)))

theorem mem_worlds_iff {a : NestedValue T K} {W : World T K a.lev} :
    W ∈ a.worlds ↔ W.IsWorldOf a := by
  unfold worlds World.IsWorldOf
  constructor
  · intro h
    obtain ⟨R, hR, h⟩ := Multiset.mem_bind.mp h
    obtain ⟨L, hL, h⟩ := Multiset.mem_bind.mp h
    obtain ⟨N, hN, rfl⟩ := Multiset.mem_map.mp h
    obtain ⟨hL1, hL2⟩ := mem_foldr_addLeaf_iff.mp hL
    obtain ⟨hN1, hN2⟩ := mem_foldr_addNode_iff.mp hN
    exact ⟨map_of_mem_memChoices hR, hL1, hL2, hN1, hN2⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact Multiset.mem_bind.mpr ⟨W.root, mem_memChoices_of_map h1, Multiset.mem_bind.mpr
      ⟨W.leaf, mem_foldr_addLeaf_iff.mpr ⟨h2, h3⟩, Multiset.mem_map.mpr
        ⟨W.node, mem_foldr_addNode_iff.mpr ⟨h4, h5⟩, rfl⟩⟩⟩

theorem isWorldOf_of_mem_worlds {a : NestedValue T K} {W : World T K a.lev}
    (h : W ∈ a.worlds) : W.IsWorldOf a :=
  mem_worlds_iff.mp h

end Enumeration

end NestedValue

/-! ## What a world of a nested value is annotated

The annotation is the one every family gets: the product of what is
present times `𝟙 ⊖` the sum of what is absent – the value's own
occurrences, each expression family **once** and each inner node's
occurrences **once**, however many occurrences read them, at every storey
together. It does not depend on which worlds are admitted, that being a
separate question from how a given one is weighed. -/

namespace NestedValue

section Annotation

variable [CommSemiringWithMonus K] {X : Type}

/-- What a decision over a bag of occurrences keeps. -/
def decProd (D : Multiset (X × K × Bool)) : K :=
  (D.map (fun m => if m.2.2 = true then m.2.1 else 1)).prod

/-- What a decision over a bag of occurrences leaves out. -/
def decAbs (D : Multiset (X × K × Bool)) : K :=
  (D.map (fun m => if m.2.2 = true then 0 else m.2.1)).sum

/-- What a decision about an expression family keeps. -/
def leafProd (e : LeafKey T K × Finset ℕ) : K := ∏ i ∈ e.2, e.1.2.getD i 0

/-- What a decision about an expression family leaves out. -/
def leafAbs (e : LeafKey T K × Finset ℕ) : K :=
  ∑ i ∈ Finset.range e.1.2.length \ e.2, e.1.2.getD i 0

/-- The product of the annotations a world keeps. -/
def World.presentProd {d : ℕ} (W : World T K d) : K :=
  decProd W.root * (W.leaf.map leafProd).prod * (W.node.map (fun e => decProd e.2.2)).prod

/-- The sum of the annotations a world leaves out. -/
def World.absentSum {d : ℕ} (W : World T K d) : K :=
  decAbs W.root + (W.leaf.map leafAbs).sum + (W.node.map (fun e => decAbs e.2.2)).sum

/-- **The annotation of a world of a nested value.** -/
def World.ann {d : ℕ} (W : World T K d) : K :=
  W.presentProd * (1 - W.absentSum)

/-- **The annotation of an occurrence a world keeps is a factor of what
it keeps.** -/
theorem decProd_eq_mul {D : Multiset (X × K × Bool)} {m : X × K × Bool} (hm : m ∈ D)
    (hp : m.2.2 = true) : ∃ x : K, decProd D = m.2.1 * x := by
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hm
  refine ⟨decProd u, ?_⟩
  rw [decProd, Multiset.map_cons, Multiset.prod_cons, ite_eq_left hp]
  rfl

/-- **The annotation of an occurrence a world keeps is a factor of the
world's annotation.** This is what lets a world swallow the `δ`-guard of
the family it reads. -/
theorem World.exists_ann_eq_mul {d : ℕ} {W : World T K d} {m : NestInner T K d × K × Bool}
    (hm : m ∈ W.root) (hp : m.2.2 = true) : ∃ x : K, W.ann = m.2.1 * x := by
  obtain ⟨x, hx⟩ := decProd_eq_mul hm hp
  refine ⟨x * (W.leaf.map leafProd).prod * (W.node.map (fun e => decProd e.2.2)).prod
    * (1 - W.absentSum), ?_⟩
  rw [World.ann, World.presentProd, hx]
  simp only [mul_assoc]

theorem World.presentProd_eq_mul {d : ℕ} {W : World T K d} {m : NestInner T K d × K × Bool}
    (hm : m ∈ W.root) (hp : m.2.2 = true) : ∃ x : K, W.presentProd = m.2.1 * x := by
  obtain ⟨x, hx⟩ := decProd_eq_mul hm hp
  refine ⟨x * (W.leaf.map leafProd).prod * (W.node.map (fun e => decProd e.2.2)).prod, ?_⟩
  rw [World.presentProd, hx]
  simp only [mul_assoc]

end Annotation

/-! ## Worlds built from a decision

The full world and the realized one are each a decision applied to every
family the value holds (`World.ofDec`), which a world reads back exactly
where the value reads. -/

variable [DecidableEq T] [DecidableEq K]

/-- **The world a decision makes of a value**: its own occurrences
decided by `R`, and every family by `D`. -/
noncomputable def World.ofDec (a : NestedValue T K) (R : Multiset (NestInner T K a.lev × K × Bool))
    (D : NestDec T K) : World T K a.lev :=
  ⟨R, a.leaves.map (fun κ => (κ, D.leaf κ)), a.nodes.map (fun e => ⟨e.1, e.2, D.node e.1 e.2⟩)⟩

theorem mem_leaves {a : NestedValue T K} {o : NestInner T K a.lev × K} (ho : o ∈ a.occs)
    {κ : LeafKey T K} (hκ : κ ∈ NestInner.leaves a.lev o.1) : κ ∈ a.leaves :=
  Multiset.mem_dedup.mpr (Multiset.mem_bind.mpr ⟨o, ho, hκ⟩)

theorem mem_nodes {a : NestedValue T K} {o : NestInner T K a.lev × K} (ho : o ∈ a.occs)
    {e : Σ i, NodeKey T K i} (he : e ∈ NestInner.nodes a.lev o.1) : e ∈ a.nodes := by
  classical
  rw [nodes, Multiset.mem_dedup]
  exact Multiset.mem_bind.mpr ⟨o, ho, he⟩

theorem leafSub_ofDec {a : NestedValue T K} (R : Multiset (NestInner T K a.lev × K × Bool))
    (D : NestDec T K) {κ : LeafKey T K} (hκ : κ ∈ a.leaves) :
    (World.ofDec a R D).dec.leaf κ = D.leaf κ := by
  refine leafSub_of_mem ?_ (Multiset.mem_map_of_mem _ hκ)
  show (Multiset.map Prod.fst (a.leaves.map _)).Nodup
  rw [Multiset.map_map]
  exact (Multiset.map_id' _).symm ▸ a.nodup_leaves

theorem nodeDec_ofDec {a : NestedValue T K} (R : Multiset (NestInner T K a.lev × K × Bool))
    (D : NestDec T K) {e : Σ i, NodeKey T K i} (he : e ∈ a.nodes) :
    (World.ofDec a R D).dec.node e.1 e.2 = D.node e.1 e.2 := by
  refine nodeDec_of_mem ?_ (Multiset.mem_map_of_mem
    (fun e : Σ i, NodeKey T K i => (⟨e.1, e.2, D.node e.1 e.2⟩ :
      Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool))) he)
  show (Multiset.map _ (a.nodes.map _)).Nodup
  rw [Multiset.map_map]
  exact (Multiset.map_id' _).symm ▸ a.nodup_nodes

/-- **A world built from a decision reads every occurrence of the value as
the decision does**, when the decision decides each node on that node's
own occurrences. -/
theorem val_ofDec {a : NestedValue T K} (R : Multiset (NestInner T K a.lev × K × Bool))
    (D : NestDec T K)
    (hD : ∀ (j : ℕ) (κ : NodeKey T K j), (D.node j κ).map (fun m => (m.1, m.2.1)) = κ.2)
    {o : NestInner T K a.lev × K} (ho : o ∈ a.occs) :
    NestInner.val (World.ofDec a R D).dec a.lev o.1 = NestInner.val D a.lev o.1 :=
  NestInner.val_congr _ _ _ _ (fun _ hκ => leafSub_ofDec R D (mem_leaves ho hκ))
    (fun e he => ⟨nodeDec_ofDec R D (mem_nodes ho he), hD e.1 e.2⟩)

theorem ok_ofDec {a : NestedValue T K} (R : Multiset (NestInner T K a.lev × K × Bool))
    (D : NestDec T K)
    (hD : ∀ (j : ℕ) (κ : NodeKey T K j), (D.node j κ).map (fun m => (m.1, m.2.1)) = κ.2)
    {o : NestInner T K a.lev × K} (ho : o ∈ a.occs) :
    NestInner.ok (World.ofDec a R D).dec a.lev o.1 ↔ NestInner.ok D a.lev o.1 :=
  NestInner.ok_congr _ _ _ _ (fun _ hκ => leafSub_ofDec R D (mem_leaves ho hκ))
    (fun e he => ⟨nodeDec_ofDec R D (mem_nodes ho he), hD e.1 e.2⟩)

theorem isWorldOf_ofDec (a : NestedValue T K) (R : Multiset (NestInner T K a.lev × K × Bool))
    (D : NestDec T K) (hR : R.map (fun m => (m.1, m.2.1)) = a.occs)
    (hL : ∀ κ, D.leaf κ ⊆ Finset.range κ.2.length)
    (hD : ∀ (j : ℕ) (κ : NodeKey T K j), (D.node j κ).map (fun m => (m.1, m.2.1)) = κ.2) :
    (World.ofDec a R D).IsWorldOf a := by
  refine ⟨hR, ?_, ?_, ?_, ?_⟩
  · show Multiset.map Prod.fst (a.leaves.map _) = _
    rw [Multiset.map_map]; exact Multiset.map_id' _
  · intro e he
    obtain ⟨κ, -, rfl⟩ := Multiset.mem_map.mp he
    exact hL κ
  · show Multiset.map _ (a.nodes.map _) = _
    rw [Multiset.map_map]; exact Multiset.map_id' _
  · intro e he
    obtain ⟨e', -, rfl⟩ := Multiset.mem_map.mp he
    exact hD e'.1 e'.2

omit [DecidableEq T] [DecidableEq K] in
theorem fullDec_node (j : ℕ) (κ : NodeKey T K j) :
    ((NestInner.fullDec (T := T) (K := K)).node j κ).map (fun m => (m.1, m.2.1)) = κ.2 := by
  show (κ.2.map _).map _ = _
  rw [Multiset.map_map]; exact Multiset.map_id' _

omit [DecidableEq T] [DecidableEq K] in
theorem realDec_node (ν : K → Bool) (j : ℕ) (κ : NodeKey T K j) :
    ((NestInner.realDec (T := T) ν).node j κ).map (fun m => (m.1, m.2.1)) = κ.2 := by
  show (κ.2.map _).map _ = _
  rw [Multiset.map_map]; exact Multiset.map_id' _

/-- The world in which every occurrence, outer and inner, is present. -/
noncomputable def World.full (a : NestedValue T K) : World T K a.lev :=
  World.ofDec a (a.occs.map (fun o => (o.1, o.2, true))) NestInner.fullDec

theorem World.isWorldOf_full (a : NestedValue T K) : (World.full a).IsWorldOf a :=
  isWorldOf_ofDec _ _ _ (by rw [Multiset.map_map]; exact Multiset.map_id' _)
    (fun _ => subset_refl _) fullDec_node

/-- **Everything present reads as the collapse.** -/
theorem valOn_full (a : NestedValue T K) : a.valOn (World.full a) = a.collapse := by
  unfold valOn collapse World.kept
  refine congrArg a.agg ?_
  show ((a.occs.map (fun o => (o.1, o.2, true))).filter _).map _ = _
  rw [Multiset.filter_eq_self.mpr (fun m hm => by
    obtain ⟨o, -, rfl⟩ := Multiset.mem_map.mp hm; rfl), Multiset.map_map]
  refine Multiset.map_congr rfl (fun o ho => ?_)
  simp only [Function.comp_apply]
  rw [show (World.full a).dec = (World.ofDec a _ NestInner.fullDec).dec from rfl,
    val_ofDec _ _ fullDec_node ho, NestInner.val_fullDec]

/-- **The world a valuation of the annotations realizes**: every
occurrence, of the value, of each expression family and of each inner
node, whose annotation the valuation makes true – the outer and the
inner ones independently. -/
noncomputable def realizedWorld (a : NestedValue T K) (ν : K → Bool) : World T K a.lev :=
  World.ofDec a (a.occs.map (fun o => (o.1, o.2, ν o.2))) (NestInner.realDec ν)

theorem isWorldOf_realizedWorld (a : NestedValue T K) (ν : K → Bool) :
    (a.realizedWorld ν).IsWorldOf a :=
  isWorldOf_ofDec _ _ _ (by rw [Multiset.map_map]; exact Multiset.map_id' _)
    (fun _ => Finset.filter_subset _ _) (realDec_node ν)

/-- **What the realized world reads, occurrence by occurrence**: the
valuation keeps the occurrences whose annotation it makes true, and reads
each of them in the world it cuts out of everything that occurrence
reads. -/
theorem kept_realizedWorld (a : NestedValue T K) (ν : K → Bool) :
    (a.realizedWorld ν).kept
      = (a.occs.filter (fun o => ν o.2 = true)).map
          (fun o => NestInner.specialize ν a.lev o.1) := by
  unfold World.kept
  show ((a.occs.map (fun o => (o.1, o.2, ν o.2))).filter _).map _ = _
  rw [Multiset.filter_map, Multiset.map_map]
  refine Multiset.map_congr (Multiset.filter_congr (fun _ _ => Iff.rfl)) (fun o ho => ?_)
  simp only [Function.comp_apply]
  exact val_ofDec _ _ (realDec_node ν) (Multiset.mem_of_mem_filter ho)

/-- **The world-faithful reading**: the value in the realized world. -/
noncomputable def specialize (a : NestedValue T K) (ν : K → Bool) : T :=
  a.valOn (a.realizedWorld ν)

/-- **The world-faithful reading, occurrence by occurrence.** -/
theorem specialize_eq (a : NestedValue T K) (ν : K → Bool) :
    a.specialize ν
      = a.agg ((a.occs.filter (fun o => ν o.2 = true)).map
          (fun o => NestInner.specialize ν a.lev o.1)) :=
  congrArg a.agg (kept_realizedWorld a ν)

omit [DecidableEq T] [DecidableEq K] in
theorem realDec_of_forall (ν : K → Bool) (h : ∀ x : K, ν x = true) :
    NestInner.realDec (T := T) ν = NestInner.fullDec := by
  unfold NestInner.realDec NestInner.fullDec
  congr 1
  · funext κ
    exact Finset.filter_true_of_mem (fun i hi => ⟨Finset.mem_range.mp hi, h _⟩)
  · funext j κ
    simp [h]

/-- A valuation that keeps every occurrence realizes the full world. -/
theorem realizedWorld_of_forall (a : NestedValue T K) (ν : K → Bool)
    (h : ∀ x : K, ν x = true) : a.realizedWorld ν = World.full a := by
  unfold realizedWorld World.full
  rw [realDec_of_forall ν h]
  simp [h]

/-- **Where every occurrence is realized the reading is the
collapse**, so the world-faithful reading and the deterministic one
agree on the database as it is. -/
theorem specialize_of_forall (a : NestedValue T K) (ν : K → Bool)
    (h : ∀ x : K, ν x = true) : a.specialize ν = a.collapse := by
  rw [specialize, realizedWorld_of_forall a ν h, valOn_full]

end NestedValue

/-! ## The readings over the nested worlds

With the world set fixed – the coherence clause not imposed – the
readings a nested value owes can be written: the predicate provenance of
a test of its value, and the values it takes. Both are the `AggValue`
ones with `World` in place of a subfamily and `World.ann` in place of
`Having.worldAnn`, and the sum runs over the enumerated worlds. -/

namespace NestedValue

section Readings

variable [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]

/-- **The predicate provenance of a test of a nested value**: the `⊕`
over its worlds of the world's annotation times the truth of the test
there. -/
noncomputable def predProvWith (a : NestedValue T K) (P : T → Kleene) : K :=
  ((a.worlds.filter (fun W => W.IsWorld a)).map
    (fun W => W.ann * Having.chiOf P (a.valOn W))).sum

/-- The comparison case. -/
noncomputable def predProvOf (a : NestedValue T K) (op : CompOp) (c : T) : K :=
  a.predProvWith (fun v => op.eval3 v c)

/-- **The values a nested value takes over its worlds**, for a key
reading. -/
noncomputable def vals (a : NestedValue T K) : Finset T :=
  (((a.worlds.filter (fun W => W.IsWorld a)).map a.valOn)).toFinset

omit [ValueType T] [CommSemiringWithMonus K] in
/-- A kept occurrence is one of the value's. -/
theorem mem_occs_of_root [DecidableEq T] {a : NestedValue T K} {W : World T K a.lev}
    (hW : W.IsWorldOf a) {m : NestInner T K a.lev × K × Bool} (hm : m ∈ W.root) :
    (m.1, m.2.1) ∈ a.occs := by
  rw [← hW.1]; exact Multiset.mem_map_of_mem _ hm

omit [ValueType T] in
/-- **A world that reads something absorbs the `δ`-guard of the outer
family**: one of the outer annotations it keeps swallows `δ` of the
family's sum. -/
theorem World.presentProd_delta_absorb [DecidableEq T] {a : NestedValue T K}
    {W : World T K a.lev} (hW : W.IsWorldOf a) (hk : 0 < Multiset.card W.kept) :
    W.presentProd * SemiringWithMonus.delta (a.occs.map Prod.snd).sum = W.presentProd := by
  obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp hk
  obtain ⟨m, hm, -⟩ := Multiset.mem_map.mp hv
  obtain ⟨hmR, hp⟩ := Multiset.mem_filter.mp hm
  have hfam : m.2.1 ∈ a.occs.map Prod.snd :=
    Multiset.mem_map_of_mem Prod.snd (mem_occs_of_root hW hmR)
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hfam
  have key : m.2.1 * SemiringWithMonus.delta (a.occs.map Prod.snd).sum = m.2.1 := by
    rw [hs, Multiset.sum_cons]; exact SemiringWithMonus.delta_absorb _ _
  obtain ⟨x, hx⟩ := World.presentProd_eq_mul hmR hp
  rw [hx, mul_right_comm, key]

/-- **A nested value's predicate provenance absorbs the `δ`-guard of its
own outer family**, provided the reading is grouped – which is what makes
every admissible world keep an occurrence, so that one occurrence
annotation is there to swallow `δ` of the family's sum. Where the reading
is scalar the empty world is a world and there is nothing to absorb
with. -/
theorem predProvWith_delta_absorb (a : NestedValue T K)
    (hsc : a.scalar = false) (P : T → Kleene) :
    a.predProvWith P * SemiringWithMonus.delta (a.occs.map Prod.snd).sum
      = a.predProvWith P := by
  unfold predProvWith
  rw [← Multiset.sum_map_mul_right]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun W hW => ?_))
  obtain ⟨hmem, hworld⟩ := Multiset.mem_filter.mp hW
  have hkept : 0 < Multiset.card W.kept := by
    rcases hworld.1 with hs | hs
    · exact absurd (hsc.symm.trans hs) Bool.false_ne_true
    · exact hs
  obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp hkept
  obtain ⟨m, hm, -⟩ := Multiset.mem_map.mp hv
  obtain ⟨hmR, hp⟩ := Multiset.mem_filter.mp hm
  have hfam : m.2.1 ∈ a.occs.map Prod.snd :=
    Multiset.mem_map_of_mem Prod.snd (mem_occs_of_root (isWorldOf_of_mem_worlds hmem) hmR)
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hfam
  have key : m.2.1 * SemiringWithMonus.delta (a.occs.map Prod.snd).sum = m.2.1 := by
    rw [hs, Multiset.sum_cons]
    exact SemiringWithMonus.delta_absorb _ _
  obtain ⟨x, hx⟩ := World.exists_ann_eq_mul hmR hp
  rw [hx]
  calc m.2.1 * x * Having.chiOf P (a.valOn W)
        * SemiringWithMonus.delta (a.occs.map Prod.snd).sum
      = (x * Having.chiOf P (a.valOn W))
        * (m.2.1 * SemiringWithMonus.delta (a.occs.map Prod.snd).sum) := by
        rw [mul_rotate m.2.1, mul_assoc]
    _ = (x * Having.chiOf P (a.valOn W)) * m.2.1 := by rw [key]
    _ = m.2.1 * x * Having.chiOf P (a.valOn W) := (mul_rotate _ _ _).symm

/-- **Reading a nested value's aggregate through a function** – what a
term over the aggregate column it produces reads. The occurrences, the
convention and so the worlds are untouched, so every reading is the
reading of the value, read through `gf`. -/
def postcomp (gf : T → T) (a : NestedValue T K) : NestedValue T K :=
  ⟨a.lev, fun s => gf (a.agg s), a.occs, a.scalar, a.fam⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem lev_postcomp (gf : T → T) (a : NestedValue T K) :
    (postcomp gf a).lev = a.lev := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem occs_postcomp (gf : T → T) (a : NestedValue T K) :
    (postcomp gf a).occs = a.occs := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem scalar_postcomp (gf : T → T) (a : NestedValue T K) :
    (postcomp gf a).scalar = a.scalar := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem collapse_postcomp (gf : T → T) (a : NestedValue T K) :
    (postcomp gf a).collapse = gf a.collapse := rfl

omit [CommSemiringWithMonus K] in
/-- The values it takes are the values of the nested value, read through
the function. -/
theorem vals_postcomp (gf : T → T) (a : NestedValue T K) :
    (postcomp gf a).vals = a.vals.image gf := by
  have h : (postcomp gf a).vals
      = ((a.worlds.filter (fun W => W.IsWorld a)).map
          (fun W => gf (a.valOn W))).toFinset := rfl
  rw [h]
  ext v
  simp only [vals, Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨W, hW, rfl⟩
    exact ⟨a.valOn W, ⟨W, hW, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨W, hW, rfl⟩, rfl⟩
    exact ⟨W, hW, rfl⟩

/-- And a test of `gf(a)` is the composed test of `a`. -/
theorem predProvWith_postcomp (gf : T → T) (a : NestedValue T K)
    (P : T → Kleene) :
    (postcomp gf a).predProvWith P = a.predProvWith (fun v => P (gf v)) := rfl

/-- **A test no value satisfies annotates `𝟘`.** -/
theorem predProvWith_of_never (a : NestedValue T K) {P : T → Kleene}
    (h : ∀ v : T, P v ≠ Kleene.true) : a.predProvWith P = 0 := by
  refine Multiset.sum_eq_zero (fun x hx => ?_)
  rw [Multiset.mem_map] at hx
  obtain ⟨W, _, rfl⟩ := hx
  rw [Having.chiOf, ite_eq_right (h _), mul_zero]

end Readings

/-- A world of the nested reading is one of the coherent reading's as
soon as it keeps no inner occurrence no present occurrence reads. -/
theorem World.isWorld_of_isWorldCoherent [DecidableEq T] [DecidableEq K] {d : ℕ}
    {a : NestedValue T K} {W : World T K d} (h : W.IsWorldCoherent a) : W.IsWorld a :=
  ⟨h.1, h.2.1, trivial⟩

/-! ## The pushforward of the annotations

Changing the annotation semiring moves no value and no occurrence: each
inner value keeps its occurrences and each node its own. Only the
annotations travel. -/

section MapAnn

variable {K' : Type}

/-- **The pushforward of an inner value.** -/
def _root_.NestInner.mapAnn (h : K → K') : (j : ℕ) → NestInner T K j → NestInner T K' j
  | 0, e => AggExpr.mapAnn (T := T) h e
  | j + 1, Sum.inl x => Sum.inl (NestInner.mapAnn h j x)
  | j + 1, Sum.inr N => Sum.inr ⟨N.agg, N.occs.map (fun o => (NestInner.mapAnn h j o.1, h o.2)),
      N.scalar, N.fam⟩

/-- **The pushforward of a nested value**: both the inner values and the
outer annotations go through `h`. -/
def mapAnn (h : K → K') (a : NestedValue T K) : NestedValue T K' :=
  ⟨a.lev, a.agg, a.occs.map (fun o => (NestInner.mapAnn h a.lev o.1, h o.2)), a.scalar, a.fam⟩

@[simp] theorem lev_mapAnn (h : K → K') (a : NestedValue T K) : (a.mapAnn h).lev = a.lev := rfl

@[simp] theorem agg_mapAnn (h : K → K') (a : NestedValue T K) : (a.mapAnn h).agg = a.agg := rfl

@[simp] theorem scalar_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).scalar = a.scalar := rfl

@[simp] theorem fam_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).fam = a.fam := rfl

@[simp] theorem occs_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).occs = a.occs.map (fun o => (NestInner.mapAnn h a.lev o.1, h o.2)) := rfl

theorem _root_.NestInner.collapse_mapAnn (h : K → K') :
    ∀ (j : ℕ) (x : NestInner T K j),
      NestInner.collapse j (NestInner.mapAnn h j x) = NestInner.collapse j x
  | 0, e => AggExpr.collapse_mapAnn h e
  | j + 1, Sum.inl x => NestInner.collapse_mapAnn h j x
  | j + 1, Sum.inr N => by
    show N.agg _ = N.agg _
    rw [Multiset.map_map]
    exact congrArg N.agg (Multiset.map_congr rfl
      (fun o _ => NestInner.collapse_mapAnn h j o.1))

/-- The deterministic reading survives the pushforward. -/
@[simp] theorem collapse_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).collapse = a.collapse := by
  show a.agg _ = a.agg _
  rw [occs_mapAnn, Multiset.map_map]
  exact congrArg a.agg (Multiset.map_congr rfl (fun o _ => NestInner.collapse_mapAnn h _ o.1))

end MapAnn

/-! ## Nothing nested: the degenerate case

A nested value whose inner values read nothing is an ordinary aggregate
value, and it had better be annotated like one. `constInner v` is the
inner value that reads no occurrence and returns `v`; `ofAggValue`
builds the nested value of a token by putting one at each of its
occurrences, all reading the one empty family, and `ann_worldOf` says a
world of it carries exactly `Having.worldAnn` of the token's own
family. -/

/-- The inner reading that reads nothing and returns `v`: the expression
of the token with no occurrence whose aggregate is `v`. Its only world is
the empty one, and it contributes no occurrence. -/
def constInner (v : T) : AggExpr T K :=
  AggExpr.ofValue ⟨fun _ => v, [], true, FamId.none, []⟩

@[simp] theorem annList_constInner (v : T) : (constInner v : AggExpr T K).annList = [] := rfl

/-- **The nested value of an ordinary token**: nothing is nested, each
occurrence carrying a value rather than a family. The token's aggregate
has to be symmetric to be the outer one, a nested value's aggregate being
a function of the bag. -/
def ofAggValue (a : AggValue T K) (hsym : a.agg.Symmetric) : NestedValue T K :=
  ⟨0, a.agg.onBag hsym,
    ((a.occs.map (fun o => ((constInner o.fst : AggExpr T K), o.snd)) :
      List (AggExpr T K × K)) : Multiset (AggExpr T K × K)),
    a.scalar, a.fam⟩

/-- **A world of an unnested token, as a world of its nested form**: the
one empty inner family, and the occurrences the subfamily keeps. -/
def worldOf [DecidableEq T] [DecidableEq K] (a : AggValue T K)
    (W : Finset (Fin a.occs.length)) : World T K 0 :=
  ⟨(((List.finRange a.occs.length).map (fun i =>
      ((constInner (a.occs.get i).fst : AggExpr T K), (a.occs.get i).snd, decide (i ∈ W))) :
        List (AggExpr T K × K × Bool)) : Multiset (AggExpr T K × K × Bool)),
    (((a.occs.map (fun o => leafKey (constInner o.fst : AggExpr T K))) :
      List (LeafKey T K)) : Multiset (LeafKey T K)).dedup.map (fun κ => (κ, ∅)),
    0⟩

/-- It is a world of the nested form. -/
theorem isWorldOf_worldOf [DecidableEq T] [DecidableEq K] (a : AggValue T K)
    (hsym : a.agg.Symmetric) (W : Finset (Fin a.occs.length)) :
    (worldOf a W).IsWorldOf (ofAggValue a hsym) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (Multiset.ofList _).map _ = Multiset.ofList _
    rw [Multiset.map_coe]
    refine congrArg Multiset.ofList ?_
    refine List.ext_getElem (by simp) (fun n h₁ h₂ => ?_)
    simp
  · dsimp only [worldOf]
    rw [Multiset.map_map]
    simp only [Function.comp_def, Multiset.map_id']
    show _ = (Multiset.bind _
      (fun o : AggExpr T K × K => ({leafKey o.1} : Multiset (LeafKey T K)))).dedup
    rw [Multiset.bind_singleton]
    show _ = (Multiset.map _ (Multiset.ofList _)).dedup
    rw [Multiset.map_coe, List.map_map]
    rfl
  · intro e he
    dsimp only [worldOf] at he
    obtain ⟨κ, -, rfl⟩ := Multiset.mem_map.mp he
    exact Finset.empty_subset _
  · show (0 : Multiset _).map _ = _
    unfold nodes ofAggValue
    simp [NestInner.nodes]
  · intro e he; exact absurd he (Multiset.notMem_zero _)

section DegenerateAnn

variable [CommSemiringWithMonus K]

/-- **A world of an unnested value is annotated as the token's own
family annotates it.** -/
theorem ann_worldOf [DecidableEq T] [DecidableEq K] (a : AggValue T K)
    (W : Finset (Fin a.occs.length)) :
    (worldOf a W).ann = Having.worldAnn a.anns W := by
  have hpres : decProd (((List.finRange a.occs.length).map (fun i =>
      ((constInner (a.occs.get i).fst : AggExpr T K), (a.occs.get i).snd, decide (i ∈ W))) :
        List (AggExpr T K × K × Bool)) : Multiset (AggExpr T K × K × Bool))
      = ∏ i ∈ W, a.anns i := by
    rw [decProd, Multiset.map_coe, Multiset.prod_coe, List.map_map,
      show ((List.finRange a.occs.length).map
          ((fun m : AggExpr T K × K × Bool => if m.2.2 = true then m.2.1 else 1) ∘
            (fun i => ((constInner (a.occs.get i).fst : AggExpr T K), (a.occs.get i).snd,
              decide (i ∈ W))))).prod
        = ∏ i : Fin a.occs.length, (if i ∈ W then a.anns i else 1) from by
          rw [Fin.prod_univ_def]
          exact congrArg List.prod (List.map_congr_left
            (fun i _ => by simp [AggValue.anns])),
      ← Finset.prod_filter]
    exact Finset.prod_congr (Finset.filter_univ_mem W) (fun _ _ => rfl)
  have habs : decAbs (((List.finRange a.occs.length).map (fun i =>
      ((constInner (a.occs.get i).fst : AggExpr T K), (a.occs.get i).snd, decide (i ∈ W))) :
        List (AggExpr T K × K × Bool)) : Multiset (AggExpr T K × K × Bool))
      = ∑ i ∈ Wᶜ, a.anns i := by
    rw [decAbs, Multiset.map_coe, Multiset.sum_coe, List.map_map,
      show ((List.finRange a.occs.length).map
          ((fun m : AggExpr T K × K × Bool => if m.2.2 = true then 0 else m.2.1) ∘
            (fun i => ((constInner (a.occs.get i).fst : AggExpr T K), (a.occs.get i).snd,
              decide (i ∈ W))))).sum
        = ∑ i : Fin a.occs.length, (if i ∈ Wᶜ then a.anns i else 0) from by
          rw [Fin.sum_univ_def]
          refine congrArg List.sum (List.map_congr_left (fun i _ => ?_))
          by_cases hi : i ∈ W <;> simp [AggValue.anns, hi],
      ← Finset.sum_filter]
    exact Finset.sum_congr (Finset.filter_univ_mem Wᶜ) (fun _ _ => rfl)
  have hl : ∀ e ∈ (worldOf a W).leaf, leafProd e = (1 : K) ∧ leafAbs e = (0 : K) := by
    intro e he
    dsimp only [worldOf] at he
    obtain ⟨κ, hκ, rfl⟩ := Multiset.mem_map.mp he
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp (Multiset.mem_dedup.mp hκ))
    simp [leafProd, leafAbs, leafKey]
  unfold World.ann World.presentProd World.absentSum
  dsimp only [worldOf] at hl ⊢
  rw [hpres, habs,
    Multiset.prod_eq_one (fun x hx => by
      obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp hx; exact (hl e he).1),
    Multiset.sum_eq_zero (fun x hx => by
      obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp hx; exact (hl e he).2)]
  simp [Having.worldAnn]

end DegenerateAnn

end NestedValue


variable [ValueType T]


/-! ## The aggregate side of a lifted value

A column of aggregate kind holds an ordinary token, a nested one or an
aggregate expression. `AggTok` is that choice, and `GenValue` is built on
it, so an ordinary token keeps its type and everything already proved
about `AggValue` applies to the `tok` case unchanged. The `nest` case has
its own readings: the pushforward keeps the values the column takes
(`AggTok.vals_mapAnn`), and the hom commutation relates two nested values
family by family (`NestInner.Rel`), their world enumerations being images
of one index bag (`wcorr_of_rel`). It also absorbs the `δ`-guard of its own family
(`NestedValue.predProvWith_delta_absorb`), which is what the evaluator's
supersede bookkeeping needs, and over `𝔹[X]` only the world a valuation
cuts out is annotated true (`NestedValue.World.ann_eval_iff`), which is
what the random-world reading needs. So the results of the metatheory
ask nothing of the kind of token a column holds; the one-token `mapAnn`
commutations (`AggTok.predProvOf_mapAnn` and its siblings) ask
`isNested = false`, and nothing downstream reads them on a nested column.
What a result may exclude is the *operator* that builds one – second-level aggregation,
`AggQueryIn.GammaNest` – and it does that with
`AggQueryIn.noGammaNest`, not with a condition on the column;
`GenRow.NoNested` is what `AggQueryIn.evaluate_noNested` gives a query
that has no such operator. -/

/-- An aggregate column's value: an ordinary token, or a **nested** one
whose occurrences include those of the aggregate values its term
read. -/
inductive AggTok (T K : Type) where
  /-- An ordinary aggregate value. -/
  | tok : AggValue T K → AggTok T K
  /-- A nested one. -/
  | nest : NestedValue T K → AggTok T K
  /-- An aggregate expression: a function of several aggregate values
  over one shared family of occurrences, which is what a term over more
  than one aggregate column produces. A term over *one* stays a `tok`,
  post-composed, since `AggValue.postcomp` represents that case already
  and keeping it spares the metatheory a case. -/
  | expr : AggExpr T K → AggTok T K

namespace AggTok

omit [ValueType T]

/-- **The occurrence family the value reads** (`AggValue.fam`). -/
def fam : AggTok T K → FamId T
  | .tok a => a.fam
  | .nest a => a.fam
  | .expr a => a.fam

/-- **The value, read as one of the family `φ`**: what the operator that
computes it stamps on it. Nothing else changes. -/
def setFam (φ : FamId T) (ids : Option (List (OccId T)) := none) :
    AggTok T K → AggTok T K
  | .tok a => .tok { a with fam := φ, oids := ids.getD a.oids }
  | .nest a => .nest { a with fam := φ }
  | .expr a => .expr { a with fam := φ, oids := ids.getD a.oids }

@[simp] theorem fam_setFam (φ : FamId T) {ids : Option (List (OccId T))} (a : AggTok T K) :
    (a.setFam φ ids).fam = φ := by
  cases a <;> rfl

theorem setFam_tok (φ : FamId T) (a : AggValue T K) :
    (AggTok.tok a).setFam φ = .tok { a with fam := φ } := rfl

theorem setFam_nest (φ : FamId T) {ids : Option (List (OccId T))} (a : NestedValue T K) :
    (AggTok.nest a).setFam φ ids = .nest { a with fam := φ } := rfl

theorem setFam_expr (φ : FamId T) (a : AggExpr T K) :
    (AggTok.expr a).setFam φ = .expr { a with fam := φ } := rfl

/-- An expression stamped with the identities of its occurrences. -/
theorem setFam_expr_some (φ : FamId T) (ids : List (OccId T)) (a : AggExpr T K) :
    (AggTok.expr a).setFam φ (some ids) = .expr { a with fam := φ, oids := ids } := rfl

/-- An ordinary token stamped with the identities of its occurrences. -/
theorem setFam_tok_some (φ : FamId T) (ids : List (OccId T)) (a : AggValue T K) :
    (AggTok.tok a).setFam φ (some ids) = .tok { a with fam := φ, oids := ids } := rfl

/-- The deterministic reading. -/
def collapse : AggTok T K → T
  | .tok a => a.collapse
  | .nest a => a.collapse
  | .expr a => a.collapse

/-- Whether the value is read in the scalar convention. -/
def scalar : AggTok T K → Bool
  | .tok a => a.scalar
  | .nest a => a.scalar
  | .expr a => a.isScalar

/-- The occurrence-annotation list. It is what the evaluator's supersede
test compares, and what makes a family.

A nested value's family is a *bag* of annotations, which no sequence
lists, so what is given here is the single annotation it sums to – what
a guard reads of a family (`δ` of its `⊕`) and no more. The supersede
test therefore compares a nested token's family coarsely: it matches a
pending group factor only when that factor is that one sum. Comparing
the bag itself is what the test would have to do, and is what `annList`
owes once an operator builds a nested token; nothing depends on it in
the meantime, nested tokens being excluded from the metatheory that runs
the test (`GenRow.NoNested`). -/
def annList [AddCommMonoid K] : AggTok T K → List K
  | .tok a => a.occs.map Prod.snd
  | .nest a => [(a.occs.map Prod.snd).sum]
  | .expr a => a.annList

/-- Whether the value is nested. -/
def isNested : AggTok T K → Bool
  | .tok _ => false
  | .nest _ => true
  | .expr _ => false

/-- **Whether the column holds an ordinary aggregate value.** The
readings that cover neither a nested value nor an expression over several
of them require this; it is a statement about the proofs and not about
the definitions, and `AggQueryIn.evaluate_ordinaryTokens` discharges it
for every row of a query with no multi-frame window and no second-level
aggregation. -/
def isTok : AggTok T K → Bool
  | .tok _ => true
  | .nest _ => false
  | .expr _ => false

@[simp] theorem collapse_tok (a : AggValue T K) :
    (AggTok.tok a).collapse = a.collapse := rfl

@[simp] theorem scalar_tok (a : AggValue T K) :
    (AggTok.tok a).scalar = a.scalar := rfl

@[simp] theorem annList_tok [AddCommMonoid K] (a : AggValue T K) :
    (AggTok.tok a).annList = a.occs.map Prod.snd := rfl

@[simp] theorem isNested_tok (a : AggValue T K) :
    (AggTok.tok a).isNested = false := rfl

@[simp] theorem isNested_nest (a : NestedValue T K) :
    (AggTok.nest a).isNested = true := rfl

@[simp] theorem collapse_nest (a : NestedValue T K) :
    (AggTok.nest a).collapse = a.collapse := rfl

@[simp] theorem scalar_nest (a : NestedValue T K) :
    (AggTok.nest a).scalar = a.scalar := rfl

@[simp] theorem collapse_expr (a : AggExpr T K) :
    (AggTok.expr a).collapse = a.collapse := rfl

@[simp] theorem scalar_expr (a : AggExpr T K) :
    (AggTok.expr a).scalar = a.isScalar := rfl

@[simp] theorem annList_expr [AddCommMonoid K] (a : AggExpr T K) :
    (AggTok.expr a).annList = a.annList := rfl

@[simp] theorem annList_nest [AddCommMonoid K] (a : NestedValue T K) :
    (AggTok.nest a).annList = [(a.occs.map Prod.snd).sum] := rfl

@[simp] theorem isNested_expr (a : AggExpr T K) :
    (AggTok.expr a).isNested = false := rfl

@[simp] theorem isTok_tok (a : AggValue T K) :
    (AggTok.tok a).isTok = true := rfl

@[simp] theorem isTok_nest (a : NestedValue T K) :
    (AggTok.nest a).isTok = false := rfl

@[simp] theorem isTok_expr (a : AggExpr T K) :
    (AggTok.expr a).isTok = false := rfl

/-- A token that is not nested is an ordinary one or an expression –
the two kinds whose readings the metatheory covers. -/
theorem eq_tok_or_expr_of_not_nested {x : AggTok T K} (h : x.isNested = false) :
    (∃ a : AggValue T K, x = AggTok.tok a)
      ∨ (∃ e : AggExpr T K, x = AggTok.expr e) := by
  cases x with
  | tok a => exact Or.inl ⟨a, rfl⟩
  | nest a => exact absurd h (by simp)
  | expr e => exact Or.inr ⟨e, rfl⟩

/-- An ordinary token is an aggregate value. -/
theorem eq_tok_of_isTok {x : AggTok T K} (h : x.isTok = true) :
    ∃ a : AggValue T K, x = AggTok.tok a := by
  cases x with
  | tok a => exact ⟨a, rfl⟩
  | nest a => exact absurd h (by simp)
  | expr a => exact absurd h (by simp)


end AggTok

/-! ## Lifted values over the widened token

`AggValue.collapseSum` and `AggValue.mapAnnSum` keep their names and
their meaning; only the token they range over is the widened one. An
ordinary token coerces into it, so a lifted value is still written
`Sum.inr a`. -/

namespace AggTok

omit [ValueType T] in
/-- Push the annotations forward through a token, ordinary or nested. -/
def mapAnn {K' : Type} (h : K → K') : AggTok T K → AggTok T K'
  | .tok a => .tok (a.mapAnn h)
  | .nest a => .nest (a.mapAnn h)
  | .expr a => .expr (a.mapAnn h)

/-! ### The readings, on each kind of token

Each reading delegates: to `AggValue` on an ordinary token, to
`NestedValue` on a nested one – over `World.IsWorld`, the admitted world
set – and to `AggExpr`
on an expression, whose worlds are the subfamilies of the shared family
meeting every grouped leaf. So the *definitions* cover all three kinds;
what the metatheory proves beyond an ordinary token it fences with
`AggTok.isTok`, which is a statement about the proofs and not about the
definitions. -/

variable [CommSemiringWithMonus K] [DecidableEq K]

/-- The predicate provenance of a comparison against the token, in its
own convention. On a nested token it is the sum over the nested
worlds. -/
noncomputable def predProvOfWith (P : T → Kleene) : AggTok T K → K
  | .tok a => a.predProvOfWith P
  | .nest a => a.predProvWith P
  | .expr a => a.predProvWith P

/-- Read the token's aggregate through a function – what a term over
one aggregate column produces. -/
def postcomp (gf : T → T) : AggTok T K → AggTok T K
  | .tok a => .tok ⟨fun L => gf (a.agg L), a.occs, a.scalar, a.fam, a.oids⟩
  | .nest a => .nest (a.postcomp gf)
  | .expr a => .expr (a.postcomp gf)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem isNested_postcomp (gf : T → T) (x : AggTok T K) :
    (x.postcomp gf).isNested = x.isNested := by
  cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem isTok_postcomp (gf : T → T) (x : AggTok T K) :
    (x.postcomp gf).isTok = x.isTok := by
  cases x <;> rfl

/-- The comparison case. -/
noncomputable def predProvOf (op : CompOp) (c : T) (x : AggTok T K) : K :=
  x.predProvOfWith (fun v => op.eval3 v c)

/-- The world-faithful reading under a valuation of the annotations. On
a nested token it is the value in the world the valuation realizes, inner
occurrences included. -/
noncomputable def specialize (ν : K → Bool) : AggTok T K → T
  | .tok a => a.specialize ν
  | .nest a => a.specialize ν
  | .expr a => a.specialize ν

omit [CommSemiringWithMonus K] in
@[simp] theorem specialize_tok (a : AggValue T K) (ν : K → Bool) :
    (AggTok.tok a).specialize ν = a.specialize ν := rfl

/-- The values the token takes over its worlds, for a key reading – the
nested worlds on a nested token. -/
noncomputable def vals : AggTok T K → Finset T
  | .tok a => a.vals
  | .nest a => a.vals
  | .expr a => a.vals

/-- `[a ≐ v]`. -/
noncomputable def altProv (x : AggTok T K) (v : T) : K :=
  x.predProvOfWith (fun y => CompOp.syneq.eval3 y v)

@[simp] theorem predProvOfWith_tok (a : AggValue T K) (P : T → Kleene) :
    (AggTok.tok a).predProvOfWith P = a.predProvOfWith P := rfl

@[simp] theorem predProvOfWith_expr (a : AggExpr T K) (P : T → Kleene) :
    (AggTok.expr a).predProvOfWith P = a.predProvWith P := rfl

@[simp] theorem predProvOf_tok (a : AggValue T K) (op : CompOp) (c : T) :
    (AggTok.tok a).predProvOf op c = a.predProvOf op c := rfl

omit [CommSemiringWithMonus K] in
@[simp] theorem vals_tok (a : AggValue T K) :
    (AggTok.tok a).vals = a.vals := rfl

@[simp] theorem altProv_tok (a : AggValue T K) (v : T) :
    (AggTok.tok a).altProv v = a.altProv v := rfl

/-! ### The pushforward, token by token

Pushing the annotations forward leaves everything the metatheory reads
off a column but the annotations themselves: which kind of token it is,
the convention it is read in and the values it takes. The last is stated
away from a nested token, whose values are the one reading still
unproved. -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem isNested_mapAnn {K' : Type} (f : K → K') (x : AggTok T K) :
    (x.mapAnn f).isNested = x.isNested := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem isTok_mapAnn {K' : Type} (f : K → K') (x : AggTok T K) :
    (x.mapAnn f).isTok = x.isTok := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem scalar_mapAnn {K' : Type} (f : K → K') (x : AggTok T K) :
    (x.mapAnn f).scalar = x.scalar := by cases x <;> rfl

omit [CommSemiringWithMonus K] in
/-- The values a column takes survive the pushforward, on a token that is
not nested. -/
theorem vals_mapAnn {K' : Type} [CommSemiringWithMonus K'] [DecidableEq K']
    (f : K → K') (x : AggTok T K) (hx : x.isNested = false) : (x.mapAnn f).vals = x.vals := by
  cases x with
  | tok a => exact AggValue.vals_mapAnn f a
  | nest a => exact absurd hx (by simp [isNested])
  | expr e => exact AggExpr.vals_mapAnn f e

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- Reading a column through a function and pushing its annotations
forward commute. -/
theorem mapAnn_postcomp {K' : Type} (f : K → K') (gf : T → T)
    (x : AggTok T K) :
    (x.postcomp gf).mapAnn f = (x.mapAnn f).postcomp gf := by
  cases x <;> rfl

/-! ### The family a value is stamped with

No reading of a value looks at its family: stamping one changes which
values a predicate reads together, and nothing about any one of them. -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem collapse_setFam (φ : FamId T) {ids : Option (List (OccId T))} (x : AggTok T K) :
    (x.setFam φ ids).collapse = x.collapse := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem scalar_setFam (φ : FamId T) {ids : Option (List (OccId T))} (x : AggTok T K) :
    (x.setFam φ ids).scalar = x.scalar := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem annList_setFam [AddCommMonoid K] (φ : FamId T)
    {ids : Option (List (OccId T))} (x : AggTok T K) :
    (x.setFam φ ids).annList = x.annList := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem isNested_setFam (φ : FamId T) {ids : Option (List (OccId T))} (x : AggTok T K) :
    (x.setFam φ ids).isNested = x.isNested := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem isTok_setFam (φ : FamId T) {ids : Option (List (OccId T))} (x : AggTok T K) :
    (x.setFam φ ids).isTok = x.isTok := by cases x <;> rfl

@[simp] theorem predProvOfWith_setFam (φ : FamId T)
    {ids : Option (List (OccId T))} (P : T → Kleene) (x : AggTok T K) :
    (x.setFam φ ids).predProvOfWith P = x.predProvOfWith P := by cases x <;> rfl

@[simp] theorem predProvOf_setFam (φ : FamId T)
    {ids : Option (List (OccId T))} (op : CompOp) (c : T) (x : AggTok T K) :
    (x.setFam φ ids).predProvOf op c = x.predProvOf op c := by cases x <;> rfl

omit [CommSemiringWithMonus K] in
@[simp] theorem specialize_setFam (φ : FamId T)
    {ids : Option (List (OccId T))} (ν : K → Bool) (x : AggTok T K) :
    (x.setFam φ ids).specialize ν = x.specialize ν := by cases x <;> rfl

omit [CommSemiringWithMonus K] in
@[simp] theorem vals_setFam (φ : FamId T) {ids : Option (List (OccId T))} (x : AggTok T K) :
    (x.setFam φ ids).vals = x.vals := by cases x <;> rfl

@[simp] theorem altProv_setFam (φ : FamId T)
    {ids : Option (List (OccId T))} (x : AggTok T K) (v : T) :
    (x.setFam φ ids).altProv v = x.altProv v := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem mapAnn_setFam {K' : Type} (f : K → K') (φ : FamId T)
    {ids : Option (List (OccId T))} (x : AggTok T K) :
    (x.setFam φ ids).mapAnn f = (x.mapAnn f).setFam φ ids := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem postcomp_setFam (gf : T → T) (φ : FamId T)
    {ids : Option (List (OccId T))} (x : AggTok T K) :
    (x.setFam φ ids).postcomp gf = (x.postcomp gf).setFam φ ids := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem setFam_setFam (φ ψ : FamId T) {ids : Option (List (OccId T))} (x : AggTok T K) :
    (x.setFam φ ids).setFam ψ = x.setFam ψ ids := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem setFam_fam (x : AggTok T K) : x.setFam x.fam = x := by cases x <;> rfl

end AggTok

namespace AggValue

omit [ValueType T] in
/-- The deterministic reading of a lifted value. -/
def collapseSum : T ⊕ AggTok T K → T :=
  Sum.elim id AggTok.collapse

omit [ValueType T] in
@[simp] theorem collapseSum_inr_setFam (φ : FamId T)
    {ids : Option (List (OccId T))} (x : AggTok T K) :
    collapseSum (Sum.inr (x.setFam φ ids)) = collapseSum (Sum.inr x) := by
  cases x <;> rfl

omit [ValueType T] in
/-- **A lifted value with its family forgotten**: what two queries that
compute the same values through different operators agree on. -/
def eraseFamSum : T ⊕ AggTok T K → T ⊕ AggTok T K :=
  Sum.map id (fun a => AggTok.setFam FamId.none (some []) a)

omit [ValueType T] in
@[simp] theorem eraseFamSum_inl (v : T) :
    eraseFamSum (Sum.inl v : T ⊕ AggTok T K) = Sum.inl v := rfl

omit [ValueType T] in
@[simp] theorem eraseFamSum_inr_setFam (φ : FamId T)
    {ids : Option (List (OccId T))} (x : AggTok T K) :
    eraseFamSum (Sum.inr (x.setFam φ ids)) = eraseFamSum (Sum.inr x) := by
  cases x <;> rfl

omit [ValueType T] in
/-- The annotation pushforward on a lifted value. -/
def mapAnnSum {K' : Type} (h : K → K') : T ⊕ AggTok T K → T ⊕ AggTok T K' :=
  Sum.map id (AggTok.mapAnn h)

omit [ValueType T] in
@[simp] theorem collapseSum_inl (v : T) :
    collapseSum (Sum.inl v : T ⊕ AggTok T K) = v := rfl

omit [ValueType T] in
@[simp] theorem collapseSum_tok (a : AggValue T K) :
    collapseSum (Sum.inr (AggTok.tok a) : T ⊕ AggTok T K) = a.collapse := rfl

omit [ValueType T] in
/-- **The deterministic reading ignores the annotations**, so it is
unchanged by a pushforward – on an ordinary token, on a nested one whose
inner collapses are unchanged for the same reason, and on an expression,
whose leaves read the same sequences. -/
@[simp] theorem collapseSum_mapAnnSum {K' : Type} (h : K → K')
    (x : T ⊕ AggTok T K) : collapseSum (mapAnnSum h x) = collapseSum x := by
  cases x with
  | inl v => rfl
  | inr x =>
    cases x with
    | tok a => exact AggValue.collapse_mapAnn h a
    | nest a =>
      exact NestedValue.collapse_mapAnn h a
    | expr a => exact AggExpr.collapse_mapAnn h a

end AggValue
