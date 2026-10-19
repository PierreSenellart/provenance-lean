/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggExpr

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
are.

## Inner families are shared

Two outer occurrences may read one inner family: a join, a product or an
apply repeats a row carrying an aggregate value, and a grouping over the
result sees the value once per copy. The inner family is then **one**
family, decided once in each world, not once per copy – the inner
occurrences are objects, and an object is present or absent, not both.
So a nested value keeps its occurrences grouped by the inner family they
read (`groups`, each group with the family's annotations and the
occurrences reading it), a world decides one subfamily per group
(`WorldGrp.sub`), and a world's annotation counts each inner occurrence
once. Two inner values belong to one family when they carry the same
family identifier and the same occurrence annotations (`innerKey`), which
is how the joint reading of a selection groups the aggregate columns of a
row (`AggTok.classKey`).

## No sequence, and so a bag

`≼` orders plain tuples, and an occurrence of a nested value carries a
tuple with an *aggregate* column, so there is nothing to order these
occurrences by: the family a nested value aggregates is a bag, and so is
each group. Its aggregate is accordingly a function of a bag, a world is
a bag of decided groups, and `worlds` enumerates the worlds off that bag.
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
present occurrence reads is settled in the negative (`World.IsWorldWith`):
the predicate is a parameter of everything below so that the refuted
reading can be stated.
-/

variable {T K : Type} [ValueType T]

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

omit [ValueType T] in
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

/-- **A nested aggregate value**: an outer aggregate over occurrences
that carry aggregate values rather than values, grouped by the inner
family they read. -/
structure NestedValue (T K : Type) where
  /-- **The outer aggregate, as a function of a bag.** It cannot read a
  sequence: the order `≼` is an order on plain tuples, and an occurrence
  of a nested value carries a tuple with an aggregate column, so there is
  no sequence for an order-dependent aggregate to read. An ordinary
  aggregate becomes one of these when it is symmetric
  (`SeqAggFunc.onBag`), and an order-dependent outer aggregate has no
  nested reading at all – it goes through the alternatives
  (`AggQueryIn.Explode`), after which nothing is nested. -/
  agg : Multiset T → T
  /-- **The occurrences, grouped by the inner family they read**: per
  group, the annotations of the family's occurrences, and the outer
  occurrences reading it – what the term reads there and the occurrence's
  own annotation. What it reads is an aggregate *expression* and not one
  aggregate value, because a term over several aggregate columns is one
  – `sum(c₁ - c₂)` over a block with two counts is as ordinary as
  `avg(c)` over one – and an ordinary token embeds as the expression of
  itself (`AggExpr.ofValue`). Bags for the reason the aggregate is a
  function of one – nothing orders a tuple with an aggregate column. -/
  groups : Multiset (List K × Multiset (AggExpr T K × K))
  /-- Whether the outer reading is scalar – whether the empty world is
  one of its worlds. -/
  scalar : Bool
  /-- Which occurrence family the value reads (`AggValue.fam`). -/
  fam : FamId T
  /-- Every occurrence of a group reads the group's family. -/
  grouped : ∀ g ∈ groups, ∀ o ∈ g.2, o.1.annList = g.1

namespace NestedValue

/-- **The outer occurrences**, all groups together. -/
def occs (a : NestedValue T K) : Multiset (AggExpr T K × K) :=
  a.groups.bind Prod.snd

/-- **What groups two inner values into one family**: the family
identifier they carry and their occurrence annotations – the key a joint
reading groups a row's aggregate columns by (`AggTok.classKey`). -/
def innerKey (o : AggExpr T K × K) : (ℕ × List T × List (T ⊕ FamId T)) × List K :=
  (o.1.fam.family, o.1.annList)

/-- **The outer occurrences, grouped by inner family.** -/
def groupOccs [DecidableEq K] (U : Multiset (AggExpr T K × K)) :
    Multiset (List K × Multiset (AggExpr T K × K)) :=
  (U.map innerKey).dedup.map (fun κ => (κ.2, U.filter (fun o => innerKey o = κ)))

theorem groupOccs_grouped [DecidableEq K] (U : Multiset (AggExpr T K × K)) :
    ∀ g ∈ groupOccs U, ∀ o ∈ g.2, o.1.annList = g.1 := by
  intro g hg o ho
  obtain ⟨κ, -, rfl⟩ := Multiset.mem_map.mp hg
  have := (Multiset.mem_filter.mp ho).2
  rw [← this]
  rfl

end NestedValue

namespace Multiset

/-- **A bag split by a key**: the parts with the distinct keys sum back to
the bag. -/
theorem bind_dedup_filter {α κ : Type} [DecidableEq κ] (f : α → κ) (s : Multiset α) :
    ((s.map f).dedup.map (fun k => s.filter (fun x => f x = k))).bind id = s := by
  classical
  ext x
  rw [Multiset.count_bind]
  simp only [Multiset.map_map, Function.comp_apply, id]
  rw [Multiset.sum_map_eq_nsmul_single (f x) (fun k hk _ => by
    rw [Multiset.count_filter_of_neg (fun h => hk h.symm)])]
  by_cases hx : x ∈ s
  · rw [Multiset.count_filter_of_pos (p := fun y => f y = f x) rfl, Multiset.count_eq_one_of_mem (Multiset.nodup_dedup _)
      (Multiset.mem_dedup.mpr (Multiset.mem_map_of_mem f hx)), one_smul]
  · rw [Multiset.count_eq_zero.mpr hx, Multiset.count_eq_zero.mpr
      (fun h => hx (Multiset.mem_of_mem_filter h)), smul_eq_mul, mul_zero]

end Multiset

namespace NestedValue

/-- **The grouped bag holds the occurrences it was built from.** -/
theorem bind_groupOccs [DecidableEq K] (U : Multiset (AggExpr T K × K)) :
    (groupOccs U).bind Prod.snd = U := by
  have h := Multiset.bind_dedup_filter innerKey U
  rw [Multiset.bind_map] at h
  unfold groupOccs
  rw [Multiset.bind_map]
  exact h

/-- **The nested value of a bag of occurrences**, grouped by the inner
family each reads. -/
def ofOccs [DecidableEq K] (agg : Multiset T → T) (U : Multiset (AggExpr T K × K))
    (scalar : Bool) (fam : FamId T) : NestedValue T K :=
  ⟨agg, groupOccs U, scalar, fam, groupOccs_grouped U⟩

@[simp] theorem agg_ofOccs [DecidableEq K] (agg : Multiset T → T)
    (U : Multiset (AggExpr T K × K)) (scalar : Bool) (fam : FamId T) :
    (ofOccs agg U scalar fam).agg = agg := rfl

@[simp] theorem groups_ofOccs [DecidableEq K] (agg : Multiset T → T)
    (U : Multiset (AggExpr T K × K)) (scalar : Bool) (fam : FamId T) :
    (ofOccs agg U scalar fam).groups = groupOccs U := rfl

@[simp] theorem scalar_ofOccs [DecidableEq K] (agg : Multiset T → T)
    (U : Multiset (AggExpr T K × K)) (scalar : Bool) (fam : FamId T) :
    (ofOccs agg U scalar fam).scalar = scalar := rfl

@[simp] theorem fam_ofOccs [DecidableEq K] (agg : Multiset T → T)
    (U : Multiset (AggExpr T K × K)) (scalar : Bool) (fam : FamId T) :
    (ofOccs agg U scalar fam).fam = fam := rfl

@[simp] theorem occs_ofOccs [DecidableEq K] (agg : Multiset T → T)
    (U : Multiset (AggExpr T K × K)) (scalar : Bool) (fam : FamId T) :
    (ofOccs agg U scalar fam).occs = U :=
  bind_groupOccs U

omit [ValueType T] in
/-- An occurrence of a group reads a family of the group's length. -/
theorem length_of_grouped {a : NestedValue T K} {g : List K × Multiset (AggExpr T K × K)}
    (hg : g ∈ a.groups) {o : AggExpr T K × K} (ho : o ∈ g.2) :
    g.1.length = o.1.occs.length := by
  rw [← a.grouped g hg o ho, AggExpr.annList, List.length_map]

omit [ValueType T] in
/-- An occurrence of a group reads the group's annotations. -/
theorem anns_of_annList {e : AggExpr T K} {A : List K} (h : e.annList = A)
    (hl : A.length = e.occs.length) (i : Fin A.length) :
    e.anns (finCongr hl i) = A.get i := by
  subst h
  simp [AggExpr.anns, AggExpr.annList]

/-- **A group as a world sees it**: the family's annotations, the
subfamily the world keeps of it, and each outer occurrence reading it
with whether the world keeps that occurrence. -/
structure WorldGrp (T K : Type) where
  /-- The annotations of the inner family. -/
  anns : List K
  /-- The inner occurrences the world keeps. -/
  sub : Finset (Fin anns.length)
  /-- The outer occurrences reading the family, each with whether it is
  present. -/
  mems : Multiset (AggExpr T K × K × Bool)

/-- What a decided group decides about: the group itself. -/
def WorldGrp.base (G : WorldGrp T K) : List K × Multiset (AggExpr T K × K) :=
  (G.anns, G.mems.map (fun m => (m.1, m.2.1)))

/-- **What a decided group reads**: the inner value at each present
occurrence, in the subfamily the world keeps. -/
def WorldGrp.vals (G : WorldGrp T K) : Multiset T :=
  (G.mems.filter (fun m => m.2.2 = true)).map (fun m => m.1.valOn (trW G.sub))

/-- **A world of a nested value**: a decision per group – which inner
occurrences of its family are present, and which outer occurrences. -/
structure World (T K : Type) where
  /-- Each group of the value, with the world's decision about it. -/
  grps : Multiset (WorldGrp T K)

/-- **Whose world it is**: the groups a world decides on are the
value's own, with their multiplicities. -/
def World.IsWorldOf (W : World T K) (a : NestedValue T K) : Prop :=
  W.grps.map WorldGrp.base = a.groups

/-- **The inner values a world reads**: one per outer occurrence it
keeps. The outer family is met when this is not empty, and the value read
in the world is the outer aggregate of it. -/
def World.kept (W : World T K) : Multiset T :=
  W.grps.bind WorldGrp.vals

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
`HavingQueryCounterexamples.nestedIncoherentWitness`
(`nestedIncoherent_ne_coherent`, `realizedWorld_not_coherent`), so a
coherent reading would contradict `World.ann_eval_iff` and the
possible-world results resting on it.

The condition is one-directional and must be: a present outer occurrence
needs its inner family met, but a met family does **not** make its
occurrence present. The parameter stays because it is what the two
readings are compared through. -/
def World.IsWorldWith (W : World T K) (a : NestedValue T K)
    (extra : World T K → Prop) : Prop :=
  (a.scalar = true ∨ 0 < Multiset.card W.kept)
    ∧ (∀ G ∈ W.grps, ∀ m ∈ G.mems, m.2.2 = true → m.1.IsWorld (trW G.sub))
    ∧ extra W

/-- **The worlds a nested value admits**: the outer family met unless
the reading is scalar, and, of each inner expression *the world reads*,
the family of each of its grouped leaves met – which is that
expression's own world condition (`AggExpr.IsWorld`). -/
def World.IsWorld (W : World T K) (a : NestedValue T K) : Prop :=
  W.IsWorldWith a (fun _ => True)

/-- The reading that bars a world from meeting an inner family no
present occurrence reads. **Refuted**, not an alternative: it removes the
world a valuation realizes where a selection has brought an outer
annotation to `𝟘`, which `IsWorldWith`'s docstring sets out. Kept so that
the refutation can be stated. -/
def World.IsWorldCoherent (W : World T K) (a : NestedValue T K) : Prop :=
  W.IsWorldWith a (fun W => ∀ G ∈ W.grps, (∀ m ∈ G.mems, m.2.2 = false) → G.sub = ∅)

instance (W : World T K) (a : NestedValue T K) : Decidable (W.IsWorld a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The value of a nested aggregate in a world**: the outer aggregate
of the bag of inner values read there. -/
def valOn (a : NestedValue T K) (W : World T K) : T :=
  a.agg W.kept

/-- The world in which every occurrence, outer and inner, is present. -/
def World.full (a : NestedValue T K) : World T K :=
  ⟨a.groups.map (fun g => ⟨g.1, Finset.univ, g.2.map (fun o => (o.1, o.2, true))⟩)⟩

omit [ValueType T] in
/-- The full world is a world of the value it is built from. -/
@[simp] theorem World.isWorldOf_full (a : NestedValue T K) :
    (World.full a).IsWorldOf a := by
  unfold World.IsWorldOf World.full WorldGrp.base
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id' a.groups]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  simp only [Function.comp_apply, Multiset.map_map]
  exact Prod.ext rfl (Multiset.map_id' _)

/-- **The deterministic reading**: the outer aggregate of the inner
collapses. -/
def collapse (a : NestedValue T K) : T :=
  a.agg (a.occs.map (fun o => o.1.collapse))

omit [ValueType T] in
/-- **Everything present reads as the collapse.** -/
theorem valOn_full (a : NestedValue T K) :
    a.valOn (World.full a) = a.collapse := by
  unfold valOn collapse World.kept World.full occs
  refine congrArg a.agg ?_
  rw [Multiset.bind_map, Multiset.map_bind]
  refine Multiset.bind_congr (fun g hg => ?_)
  unfold WorldGrp.vals
  dsimp only
  rw [Multiset.filter_eq_self.mpr (fun m hm => by
    obtain ⟨o, -, rfl⟩ := Multiset.mem_map.mp hm; rfl), Multiset.map_map]
  refine Multiset.map_congr rfl (fun o ho => ?_)
  simp only [Function.comp_apply, AggExpr.collapse]
  rw [trW_eq_map (length_of_grouped hg ho), Finset.map_univ_equiv]

/-! ## The worlds of a nested value, enumerated

The worlds are the decisions one can make at each group – a subfamily of
its inner family, and, at each outer occurrence reading it, present or
not – so they are built by running over the groups and letting every
world so far gain every decision available at the next one. The groups
and their occurrences are bags and the construction has to be read off
them rather than off a listing, which is what the steps being
left-commutative says – and the multiplicities are kept: two occurrences
carrying the same inner value and the same annotation are two
occurrences, and a world may keep one and drop the other. -/

section Enumeration

/-- The presence decisions over a bag of outer occurrences. -/
def addMem (o : AggExpr T K × K) (acc : Multiset (Multiset (AggExpr T K × K × Bool))) :
    Multiset (Multiset (AggExpr T K × K × Bool)) :=
  ({true, false} : Multiset Bool).bind (fun b => acc.map (fun ms => (o.1, o.2, b) ::ₘ ms))

omit [ValueType T] in
instance : LeftCommutative (addMem (T := T) (K := K)) where
  left_comm o₁ o₂ acc := by
    unfold addMem
    simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]
    rw [Multiset.bind_bind]
    exact Multiset.bind_congr (fun b₂ _ => Multiset.bind_congr
      (fun b₁ _ => Multiset.map_congr rfl (fun ms _ => Multiset.cons_swap _ _ _)))

/-- Every choice of presence over a bag of outer occurrences. -/
def memChoices (M : Multiset (AggExpr T K × K)) : Multiset (Multiset (AggExpr T K × K × Bool)) :=
  M.foldr addMem {0}

/-- The decisions available at one group: a subfamily of its inner
family, and a presence choice per outer occurrence reading it. -/
def decisions (g : List K × Multiset (AggExpr T K × K)) : Multiset (WorldGrp T K) :=
  (Finset.univ : Finset (Finset (Fin g.1.length))).val.bind
    (fun S => (memChoices g.2).map (fun ms => ⟨g.1, S, ms⟩))

/-- One more group: every world so far gains every decision available at
it. -/
def addGrp (g : List K × Multiset (AggExpr T K × K))
    (ws : Multiset (Multiset (WorldGrp T K))) : Multiset (Multiset (WorldGrp T K)) :=
  (decisions g).bind (fun G => ws.map (fun W => G ::ₘ W))

omit [ValueType T] in
/-- **The order the groups are taken in does not matter**, which is what
lets the worlds be read off the bag. -/
instance : LeftCommutative (addGrp (T := T) (K := K)) where
  left_comm g₁ g₂ ws := by
    unfold addGrp
    simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]
    rw [Multiset.bind_bind]
    exact Multiset.bind_congr (fun d₂ _ => Multiset.bind_congr
      (fun d₁ _ => Multiset.map_congr rfl
        (fun W _ => Multiset.cons_swap _ _ _)))

/-- **The worlds of a nested value.** -/
def worlds (a : NestedValue T K) : Multiset (World T K) :=
  (Multiset.foldr addGrp {0} a.groups).map World.mk

omit [ValueType T] in
theorem map_of_mem_memChoices {M : Multiset (AggExpr T K × K)}
    {ms : Multiset (AggExpr T K × K × Bool)} (h : ms ∈ memChoices M) :
    ms.map (fun m => (m.1, m.2.1)) = M := by
  induction M using Multiset.induction_on generalizing ms with
  | empty =>
    rw [memChoices, Multiset.foldr_zero, Multiset.mem_singleton] at h
    rw [h, Multiset.map_zero]
  | cons o M ih =>
    rw [memChoices, Multiset.foldr_cons, addMem, Multiset.mem_bind] at h
    obtain ⟨b, -, hms⟩ := h
    obtain ⟨ms', hms', rfl⟩ := Multiset.mem_map.mp hms
    rw [Multiset.map_cons, ih hms']

omit [ValueType T] in
theorem mem_memChoices_of_map : ∀ {ms : Multiset (AggExpr T K × K × Bool)}
    {M : Multiset (AggExpr T K × K)}, ms.map (fun m => (m.1, m.2.1)) = M →
    ms ∈ memChoices M := by
  intro ms
  induction ms using Multiset.induction_on with
  | empty =>
    intro M hM
    rw [← hM, Multiset.map_zero, memChoices, Multiset.foldr_zero]
    exact Multiset.mem_singleton_self 0
  | cons m ms ih =>
    intro M hM
    rw [← hM, Multiset.map_cons, memChoices, Multiset.foldr_cons, addMem, Multiset.mem_bind]
    refine ⟨m.2.2, by cases m.2.2 <;> simp, Multiset.mem_map.mpr ⟨ms, ih rfl, rfl⟩⟩

omit [ValueType T] in
theorem base_of_mem_decisions {g : List K × Multiset (AggExpr T K × K)} {G : WorldGrp T K}
    (h : G ∈ decisions g) : G.base = g := by
  unfold decisions at h
  obtain ⟨S, -, hG⟩ := Multiset.mem_bind.mp h
  obtain ⟨ms, hms, rfl⟩ := Multiset.mem_map.mp hG
  exact Prod.ext rfl (map_of_mem_memChoices hms)

omit [ValueType T] in
theorem mem_decisions_base (G : WorldGrp T K) : G ∈ decisions G.base := by
  unfold decisions
  refine Multiset.mem_bind.mpr ⟨G.sub, Finset.mem_val.mpr (Finset.mem_univ _), ?_⟩
  exact Multiset.mem_map.mpr ⟨G.mems, mem_memChoices_of_map rfl, rfl⟩

omit [ValueType T] in
theorem map_base_of_mem_foldr {s : Multiset (List K × Multiset (AggExpr T K × K))}
    {W : Multiset (WorldGrp T K)} (h : W ∈ Multiset.foldr addGrp {0} s) :
    W.map WorldGrp.base = s := by
  induction s using Multiset.induction_on generalizing W with
  | empty =>
    rw [Multiset.foldr_zero, Multiset.mem_singleton] at h
    rw [h, Multiset.map_zero]
  | cons g s ih =>
    rw [Multiset.foldr_cons, addGrp, Multiset.mem_bind] at h
    obtain ⟨G, hG, hW⟩ := h
    obtain ⟨W', hW', rfl⟩ := Multiset.mem_map.mp hW
    rw [Multiset.map_cons, ih hW', base_of_mem_decisions hG]

omit [ValueType T] in
/-- **Every world the enumeration produces is a world of the value.** -/
theorem isWorldOf_of_mem_worlds {a : NestedValue T K} {W : World T K}
    (h : W ∈ a.worlds) : W.IsWorldOf a := by
  rw [worlds, Multiset.mem_map] at h
  obtain ⟨W', hW', rfl⟩ := h
  exact map_base_of_mem_foldr hW'

omit [ValueType T] in
theorem mem_foldr_of_map_base : ∀ {W : Multiset (WorldGrp T K)}
    {s : Multiset (List K × Multiset (AggExpr T K × K))}, W.map WorldGrp.base = s →
    W ∈ Multiset.foldr addGrp {0} s := by
  intro W
  induction W using Multiset.induction_on with
  | empty =>
    intro s hs
    rw [← hs, Multiset.map_zero, Multiset.foldr_zero]
    exact Multiset.mem_singleton_self 0
  | cons G W ih =>
    intro s hs
    rw [← hs, Multiset.map_cons, Multiset.foldr_cons, addGrp, Multiset.mem_bind]
    exact ⟨G, mem_decisions_base G, Multiset.mem_map_of_mem _ (ih rfl)⟩

omit [ValueType T] in
/-- **The worlds of a value are exactly the decisions on its groups.** -/
theorem mem_worlds_iff {a : NestedValue T K} {W : World T K} :
    W ∈ a.worlds ↔ W.IsWorldOf a := by
  refine ⟨isWorldOf_of_mem_worlds, fun h => ?_⟩
  rw [worlds, Multiset.mem_map]
  exact ⟨W.grps, mem_foldr_of_map_base h, rfl⟩

omit [ValueType T] in
/-- Summing a filtered map is summing the map with the rejected entries
read as `𝟘`. -/
theorem sum_map_filter {α β : Type} [AddCommMonoid β] (p : α → Prop)
    [DecidablePred p] (f : α → β) :
    ∀ s : Multiset α,
      ((s.filter p).map f).sum = (s.map (fun x => if p x then f x else 0)).sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons x t ih =>
    by_cases hx : p x
    · rw [Multiset.filter_cons_of_pos _ hx, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_cons, Multiset.sum_cons, ih]
      simp [hx]
    · rw [Multiset.filter_cons_of_neg _ hx, ih, Multiset.map_cons,
        Multiset.sum_cons]
      simp [hx]

end Enumeration

/-! ## What a world of a nested value is annotated

The annotation is the one every family gets: the product of what is
present times `𝟙 ⊖` the sum of what is absent – the outer occurrences, and
each inner family **once**, however many outer occurrences read it. It does
not depend on which worlds are admitted, that being a separate question
from how a given one is weighed. -/

section Annotation

variable [CommSemiringWithMonus K]

/-- What a decided group keeps: its present outer occurrences and its
kept inner ones. -/
def WorldGrp.prod (G : WorldGrp T K) : K :=
  (G.mems.map (fun m => if m.2.2 = true then m.2.1 else 1)).prod
    * ∏ j ∈ G.sub, G.anns.get j

/-- What a decided group leaves out. -/
def WorldGrp.absent (G : WorldGrp T K) : K :=
  (G.mems.map (fun m => if m.2.2 = true then 0 else m.2.1)).sum
    + ∑ j ∈ G.subᶜ, G.anns.get j

/-- The product of the annotations a world keeps. -/
def World.presentProd (W : World T K) : K :=
  (W.grps.map WorldGrp.prod).prod

/-- The sum of the annotations a world leaves out. -/
def World.absentSum (W : World T K) : K :=
  (W.grps.map WorldGrp.absent).sum

/-- **The annotation of a world of a nested value.** -/
def World.ann (W : World T K) : K :=
  W.presentProd * (1 - W.absentSum)

omit [ValueType T] in
/-- **A decided group's own factor splits over its parts**, where `K` is
complemented: each outer occurrence contributes its annotation or the
complement of it, and the inner family its own world annotation. -/
theorem WorldGrp.split (hc : complemented K) (G : WorldGrp T K) :
    G.prod * (1 - G.absent)
      = (G.mems.map (fun m => if m.2.2 = true then m.2.1 else (1 - m.2.1))).prod
        * ((∏ j ∈ G.sub, G.anns.get j) * (1 - ∑ j ∈ G.subᶜ, G.anns.get j)) := by
  unfold WorldGrp.prod WorldGrp.absent
  rw [hc, monus_multiset_sum hc, Multiset.map_map]
  have hout : ((fun a => 1 - a) ∘ fun m : AggExpr T K × K × Bool =>
      if m.2.2 = true then 0 else m.2.1)
      = fun m => if m.2.2 = true then 1 else 1 - m.2.1 := by
    funext m
    by_cases hp : m.2.2 = true <;> simp [hp, monus_zero]
  rw [hout]
  rw [show ∀ x y z w : K, x * y * (z * w) = (x * z) * (y * w) from
    fun x y z w => mul_mul_mul_comm x y z w, ← Multiset.prod_map_mul]
  refine congrArg₂ (· * ·) (congrArg Multiset.prod (Multiset.map_congr rfl (fun m _ => ?_))) rfl
  by_cases hp : m.2.2 = true <;> simp [hp]

omit [ValueType T] in
/-- **The annotation of a nested world splits over its groups**, where
`K` is complemented: one monus over everything the world leaves out is
the product of one monus per group. -/
theorem World.ann_split (hc : complemented K) (W : World T K) :
    W.ann = (W.grps.map (fun G => G.prod * (1 - G.absent))).prod := by
  unfold World.ann World.presentProd World.absentSum
  rw [monus_multiset_sum hc, Multiset.map_map, ← Multiset.prod_map_mul]
  rfl

omit [ValueType T] in
/-- Nothing is absent from the full world. -/
@[simp] theorem World.absentSum_full (a : NestedValue T K) :
    (World.full a).absentSum = 0 := by
  unfold World.absentSum World.full WorldGrp.absent
  simp

omit [ValueType T] in
/-- **The full world is annotated by the product of everything.** -/
theorem World.ann_full (a : NestedValue T K) :
    (World.full a).ann = (World.full a).presentProd := by
  rw [World.ann, World.absentSum_full, monus_zero, mul_one]

omit [ValueType T] in
/-- **The annotation of an occurrence a world keeps is a factor of the
world's annotation.** This is what lets a world swallow the `δ`-guard of
the family it reads. -/
theorem World.exists_ann_eq_mul {W : World T K} {G : WorldGrp T K}
    (hG : G ∈ W.grps) {m : AggExpr T K × K × Bool} (hm : m ∈ G.mems)
    (hp : m.2.2 = true) : ∃ x : K, W.ann = m.2.1 * x := by
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hG
  obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hm
  refine ⟨(u.map (fun m => if m.2.2 = true then m.2.1 else 1)).prod
      * (∏ j ∈ G.sub, G.anns.get j) * (t.map WorldGrp.prod).prod
        * (1 - W.absentSum), ?_⟩
  rw [World.ann, World.presentProd, ht, Multiset.map_cons, Multiset.prod_cons,
    WorldGrp.prod, hu, Multiset.map_cons, Multiset.prod_cons, ite_eq_left hp]
  simp only [mul_assoc]

omit [ValueType T] in
/-- **A world that reads something absorbs the `δ`-guard of the outer
family**: one of the outer annotations it keeps swallows `δ` of the
family's sum. -/
theorem World.presentProd_delta_absorb {a : NestedValue T K} {W : World T K}
    (hW : W.IsWorldOf a) (hk : 0 < Multiset.card W.kept) :
    W.presentProd * SemiringWithMonus.delta (a.occs.map Prod.snd).sum = W.presentProd := by
  obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp hk
  obtain ⟨G, hG, hvG⟩ := Multiset.mem_bind.mp hv
  obtain ⟨m, hm, -⟩ := Multiset.mem_map.mp hvG
  obtain ⟨hmG, hp⟩ := Multiset.mem_filter.mp hm
  have hfam : m.2.1 ∈ a.occs.map Prod.snd := by
    rw [occs, ← hW, Multiset.bind_map, Multiset.map_bind]
    refine Multiset.mem_bind.mpr ⟨G, hG, ?_⟩
    unfold WorldGrp.base
    rw [Multiset.map_map]
    exact Multiset.mem_map_of_mem _ hmG
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hfam
  have key : m.2.1 * SemiringWithMonus.delta (a.occs.map Prod.snd).sum = m.2.1 := by
    rw [hs, Multiset.sum_cons]
    exact SemiringWithMonus.delta_absorb _ _
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hG
  obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hmG
  have hx : W.presentProd = m.2.1 * ((u.map (fun m => if m.2.2 = true then m.2.1 else 1)).prod
      * (∏ j ∈ G.sub, G.anns.get j) * (t.map WorldGrp.prod).prod) := by
    rw [World.presentProd, ht, Multiset.map_cons, Multiset.prod_cons, WorldGrp.prod, hu,
      Multiset.map_cons, Multiset.prod_cons, ite_eq_left hp]
    simp only [mul_assoc]
  rw [hx, mul_right_comm, key]

end Annotation

omit [ValueType T] in
/-- A world of the nested reading is one of the coherent reading's as
soon as it keeps no inner occurrence no present occurrence reads. -/
theorem World.isWorld_of_isWorldCoherent {a : NestedValue T K}
    {W : World T K} (h : W.IsWorldCoherent a) : W.IsWorld a :=
  ⟨h.1, h.2.1, trivial⟩

/-! ## The pushforward of the annotations

Changing the annotation semiring moves no value and no occurrence: each
group keeps its occurrences, each inner value keeps its own, and a world
of the pushforward is a world of the original. Only the annotations
travel, and the readings follow them. The groups are carried as they are:
a pushforward that identifies two annotations does not merge two inner
families, which is what makes it commute with every reading. -/

section MapAnn

variable {K' : Type}

/-- The pushforward of one group. -/
def mapGrp (h : K → K') (g : List K × Multiset (AggExpr T K × K)) :
    List K' × Multiset (AggExpr T K' × K') :=
  (g.1.map h, g.2.map (fun o => (o.1.mapAnn h, h o.2)))

omit [ValueType T] in
theorem annList_mapAnn (h : K → K') (e : AggExpr T K) :
    (e.mapAnn h).annList = e.annList.map h := by
  simp [AggExpr.annList, AggExpr.mapAnn, List.map_map]

/-- **The pushforward of a nested value**: both the inner values and the
outer annotations go through `h`. -/
def mapAnn (h : K → K') (a : NestedValue T K) : NestedValue T K' where
  agg := a.agg
  groups := a.groups.map (mapGrp h)
  scalar := a.scalar
  fam := a.fam
  grouped := by
    intro g' hg' o' ho'
    obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hg'
    obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.mp ho'
    show (o.1.mapAnn h).annList = g.1.map h
    rw [annList_mapAnn, a.grouped g hg o ho]

omit [ValueType T] in
@[simp] theorem agg_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).agg = a.agg := rfl

omit [ValueType T] in
@[simp] theorem scalar_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).scalar = a.scalar := rfl

omit [ValueType T] in
@[simp] theorem groups_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).groups = a.groups.map (mapGrp h) := rfl

omit [ValueType T] in
@[simp] theorem occs_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).occs = a.occs.map (fun o => (o.1.mapAnn h, h o.2)) := by
  unfold occs
  rw [groups_mapAnn, Multiset.bind_map, Multiset.map_bind]
  rfl

/-- **The pushforward of one decided group**: the inner values and the
annotations travel, and the inner subfamily is the same one, read through
the pushforward's own annotation list. -/
def WorldGrp.mapAnn (h : K → K') (G : WorldGrp T K) : WorldGrp T K' where
  anns := G.anns.map h
  sub := G.sub.map (finCongr (List.length_map h).symm).toEmbedding
  mems := G.mems.map (fun m => (m.1.mapAnn h, h m.2.1, m.2.2))

/-- **A world of the pushforward is a world of the original**, the
groups being the same ones and each keeping its decision. -/
def World.mapAnn (h : K → K') (W : World T K) : World T K' :=
  ⟨W.grps.map (WorldGrp.mapAnn h)⟩

omit [ValueType T] in
theorem WorldGrp.base_mapAnn (h : K → K') (G : WorldGrp T K) :
    (G.mapAnn h).base = mapGrp h G.base := by
  unfold WorldGrp.base WorldGrp.mapAnn mapGrp
  simp [Multiset.map_map]

omit [ValueType T] in
/-- **A transported inner value reads its transported subfamily as the
original reads its own.** -/
theorem valOn_trW_mapAnn (h : K → K') (e : AggExpr T K) {L : ℕ} (hL : L = L')
    (S : Finset (Fin L)) :
    (e.mapAnn h).valOn (trW (S.map (finCongr hL).toEmbedding)) = e.valOn (trW S) := by
  rw [trW_map_finCongr, trW_trW_map (AggExpr.length_map_occs h e)]
  exact AggExpr.valOn_mapAnn h e _

omit [ValueType T] in
/-- And has its worlds where the original has its own. -/
theorem isWorld_trW_mapAnn (h : K → K') (e : AggExpr T K) {L : ℕ} (hL : L = L')
    (S : Finset (Fin L)) :
    (e.mapAnn h).IsWorld (trW (S.map (finCongr hL).toEmbedding)) ↔ e.IsWorld (trW S) := by
  rw [trW_map_finCongr, trW_trW_map (AggExpr.length_map_occs h e)]
  exact AggExpr.isWorld_mapAnn h e _

omit [ValueType T] in
/-- The pushforward reads what the group read. -/
theorem WorldGrp.vals_mapAnn (h : K → K') (G : WorldGrp T K) :
    (G.mapAnn h).vals = G.vals := by
  unfold WorldGrp.vals WorldGrp.mapAnn
  dsimp only
  rw [Multiset.filter_map, Multiset.map_map]
  refine Multiset.map_congr (Multiset.filter_congr (fun _ _ => Iff.rfl)) (fun m _ => ?_)
  exact valOn_trW_mapAnn h m.1 _ G.sub

omit [ValueType T] in
/-- The pushforward keeps what the world read. -/
theorem World.kept_mapAnn (h : K → K') (W : World T K) :
    (W.mapAnn h).kept = W.kept := by
  unfold World.kept World.mapAnn
  rw [Multiset.bind_map]
  exact Multiset.bind_congr (fun G _ => WorldGrp.vals_mapAnn h G)

omit [ValueType T] in
/-- The pushforward of a world of a value is a world of its
pushforward. -/
theorem World.isWorldOf_mapAnn (h : K → K') {a : NestedValue T K}
    {W : World T K} (hW : W.IsWorldOf a) :
    (W.mapAnn h).IsWorldOf (a.mapAnn h) := by
  unfold World.IsWorldOf World.mapAnn at *
  rw [groups_mapAnn, ← hW, Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun G _ => WorldGrp.base_mapAnn h G)

omit [ValueType T] in
/-- **A transported world is admissible exactly when the world it came
from is.** The condition reads the conventions and the non-emptiness of
the families, and the pushforward moves neither. -/
theorem World.isWorld_mapAnn (h : K → K') {a : NestedValue T K}
    (W : World T K) : (W.mapAnn h).IsWorld (a.mapAnn h) ↔ W.IsWorld a := by
  unfold World.IsWorld World.IsWorldWith
  rw [World.kept_mapAnn, scalar_mapAnn]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  constructor
  · intro hall G hG m hm hp
    have := hall (G.mapAnn h) (Multiset.mem_map_of_mem _ hG) (m.1.mapAnn h, h m.2.1, m.2.2)
      (Multiset.mem_map_of_mem _ hm) hp
    exact (isWorld_trW_mapAnn h m.1 _ G.sub).mp this
  · intro hall G' hG' m' hm' hp
    obtain ⟨G, hG, rfl⟩ := Multiset.mem_map.mp hG'
    obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hm'
    exact (isWorld_trW_mapAnn h m.1 _ G.sub).mpr (hall G hG m hm hp)

/-! ### The worlds travel with the groups

The groups are a bag and the worlds are read off that bag, so the
pushforward needs no reindexing of anything: the worlds of the
pushforward are the pushforwards of the worlds, each reading the value its
own world reads. Only the annotations move, which is what
`NestedValue.World.ann_mapAnn` says of the weight and
`AggQueryHom`'s `predProvWith_mapAnn` of the reading. -/

omit [ValueType T] in
theorem memChoices_mapAnn (h : K → K') (M : Multiset (AggExpr T K × K)) :
    memChoices (M.map (fun o => (o.1.mapAnn h, h o.2)))
      = (memChoices M).map (Multiset.map (fun m => (m.1.mapAnn h, h m.2.1, m.2.2))) := by
  induction M using Multiset.induction_on with
  | empty => simp [memChoices]
  | cons o M ih =>
    simp only [memChoices, Multiset.map_cons, Multiset.foldr_cons] at ih ⊢
    rw [ih, addMem, addMem, Multiset.map_bind]
    refine Multiset.bind_congr (fun b _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun ms _ => by simp)

omit [ValueType T] in
/-- **The decisions available at a group travel with it.** -/
theorem decisions_mapAnn (h : K → K') (g : List K × Multiset (AggExpr T K × K)) :
    decisions (mapGrp h g) = (decisions g).map (WorldGrp.mapAnn h) := by
  classical
  let eqv : Finset (Fin g.1.length) ≃ Finset (Fin (g.1.map h).length) :=
    (finCongr (List.length_map h).symm).finsetCongr
  unfold decisions
  rw [Multiset.map_bind]
  conv_lhs => rw [← Finset.map_univ_equiv eqv]
  rw [Finset.map_val, Multiset.bind_map]
  refine Multiset.bind_congr (fun S _ => ?_)
  show (memChoices (g.2.map _)).map _ = _
  rw [memChoices_mapAnn, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun ms _ => ?_)
  simp only [Function.comp_apply, WorldGrp.mapAnn, eqv]
  rfl

omit [ValueType T] in
/-- The enumeration travels with them. -/
theorem foldr_addGrp_mapAnn (h : K → K')
    (s : Multiset (List K × Multiset (AggExpr T K × K))) :
    Multiset.foldr addGrp {0} (s.map (mapGrp h))
      = (Multiset.foldr addGrp {0} s).map (fun W => W.map (WorldGrp.mapAnn h)) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.foldr_zero, Multiset.foldr_zero]
    rfl
  | cons g s ih =>
    rw [Multiset.map_cons, Multiset.foldr_cons, Multiset.foldr_cons, addGrp,
      addGrp, ih, decisions_mapAnn, Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun G _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun W _ => ?_)
    show WorldGrp.mapAnn h G ::ₘ W.map (WorldGrp.mapAnn h)
      = (G ::ₘ W).map (WorldGrp.mapAnn h)
    rw [Multiset.map_cons]

omit [ValueType T] in
/-- **The worlds of the pushforward are the pushforwards of the
worlds**, with their multiplicities – no reindexing, the groups being a
bag on both sides. -/
theorem worlds_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).worlds = a.worlds.map (World.mapAnn h) := by
  show (Multiset.foldr addGrp {0} (a.groups.map _)).map World.mk
    = (((Multiset.foldr addGrp {0} a.groups).map World.mk).map (World.mapAnn h))
  rw [foldr_addGrp_mapAnn, Multiset.map_map, Multiset.map_map]
  rfl

omit [ValueType T] in
/-- **The pushforward moves no value**: a transported world reads what
the world it came from reads. -/
theorem valOn_mapAnn (h : K → K') (a : NestedValue T K) (W : World T K) :
    (a.mapAnn h).valOn (W.mapAnn h) = a.valOn W := by
  show a.agg _ = a.agg _
  rw [World.kept_mapAnn]

omit [ValueType T] in
/-- The deterministic reading survives the pushforward. -/
@[simp] theorem collapse_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).collapse = a.collapse := by
  show a.agg _ = a.agg _
  rw [occs_mapAnn, Multiset.map_map]
  exact congrArg a.agg (Multiset.map_congr rfl (fun o _ => AggExpr.collapse_mapAnn h o.1))

end MapAnn

/-! ## The readings over the nested worlds

With the world set fixed – the coherence clause not imposed – the two
readings a nested value owes can be written: the predicate provenance
of a test of its value, and the world-faithful reading under a
valuation of the annotations. Both are the `AggValue` ones with
`World` in place of a subfamily and `World.ann` in place of
`Having.worldAnn`, and the sum runs over the enumerated worlds. -/

section Readings

variable [CommSemiringWithMonus K] [DecidableEq K]

/-- **The predicate provenance of a test of a nested value**: the `⊕`
over its worlds of the world's annotation times the truth of the test
there. -/
def predProvWith (a : NestedValue T K) (P : T → Kleene) : K :=
  ((a.worlds.filter (fun W => W.IsWorld a)).map
    (fun W => W.ann * Having.chiOf P (a.valOn W))).sum

/-- The comparison case. -/
def predProvOf (a : NestedValue T K) (op : CompOp) (c : T) : K :=
  a.predProvWith (fun v => op.eval3 v c)

/-- **What a valuation of the annotations decides about a group**: it
keeps the inner occurrences whose annotations it makes true, and the
outer occurrences whose annotations it makes true – independently. -/
def realizedGrp (ν : K → Bool) (g : List K × Multiset (AggExpr T K × K)) : WorldGrp T K :=
  ⟨g.1, Finset.univ.filter (fun j => ν (g.1.get j)), g.2.map (fun o => (o.1, o.2, ν o.2))⟩

/-- **The world a valuation of the annotations realizes**: every
occurrence, outer or inner, whose annotation the valuation makes
true. -/
def realizedWorld (a : NestedValue T K) (ν : K → Bool) : World T K :=
  ⟨a.groups.map (realizedGrp ν)⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- The realized world is a world of the value it is read off. -/
@[simp] theorem isWorldOf_realizedWorld (a : NestedValue T K) (ν : K → Bool) :
    (a.realizedWorld ν).IsWorldOf a := by
  unfold World.IsWorldOf realizedWorld
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id' a.groups]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  simp only [Function.comp_apply, WorldGrp.base, realizedGrp, Multiset.map_map]
  exact Prod.ext rfl (Multiset.map_id' _)

/-- **The world-faithful reading**: the value in the realized world. -/
def specialize (a : NestedValue T K) (ν : K → Bool) : T :=
  a.valOn (a.realizedWorld ν)

/-- **The values a nested value takes over its worlds**, for a key
reading. -/
def vals (a : NestedValue T K) : Finset T :=
  (((a.worlds.filter (fun W => W.IsWorld a)).map a.valOn)).toFinset

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A valuation that keeps every occurrence realizes the full world. -/
theorem realizedWorld_of_forall (a : NestedValue T K) (ν : K → Bool)
    (h : ∀ x : K, ν x = true) : a.realizedWorld ν = World.full a := by
  unfold realizedWorld World.full
  refine congrArg World.mk (Multiset.map_congr rfl (fun g _ => ?_))
  simp [realizedGrp, h]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **Where every occurrence is realized the reading is the
collapse**, so the world-faithful reading and the deterministic one
agree on the database as it is. -/
theorem specialize_of_forall (a : NestedValue T K) (ν : K → Bool)
    (h : ∀ x : K, ν x = true) : a.specialize ν = a.collapse := by
  rw [specialize, realizedWorld_of_forall a ν h, valOn_full]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **The world a valuation cuts out of a group's family is the one it
cuts out of each inner value reading it.** -/
theorem trW_realized {a : NestedValue T K} {g : List K × Multiset (AggExpr T K × K)}
    (hg : g ∈ a.groups) {o : AggExpr T K × K} (ho : o ∈ g.2) (ν : K → Bool) :
    trW (Finset.univ.filter (fun j : Fin g.1.length => ν (g.1.get j)))
      = o.1.realizedWorld ν := by
  have hl := length_of_grouped hg ho
  rw [trW_eq_map hl]
  ext i
  simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and,
    AggExpr.realizedWorld]
  rw [← anns_of_annList (a.grouped g hg o ho) hl ((finCongr hl).symm i)]
  simp

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **What the realized world reads, occurrence by occurrence**: the
valuation keeps the occurrences whose annotation it makes true, and reads
each of them in the world it cuts out of that occurrence's own
expression – which is the world it cuts out of the shared family. -/
theorem kept_realizedWorld (a : NestedValue T K) (ν : K → Bool) :
    (a.realizedWorld ν).kept
      = (a.occs.filter (fun o => ν o.2 = true)).map (fun o => o.1.specialize ν) := by
  unfold World.kept realizedWorld occs
  rw [Multiset.bind_map, Multiset.filter_bind, Multiset.map_bind]
  refine Multiset.bind_congr (fun g hg => ?_)
  unfold WorldGrp.vals realizedGrp
  dsimp only
  rw [Multiset.filter_map, Multiset.map_map]
  refine Multiset.map_congr (Multiset.filter_congr (fun _ _ => Iff.rfl)) (fun o ho => ?_)
  simp only [Function.comp_apply]
  rw [trW_realized hg (Multiset.mem_of_mem_filter ho)]
  rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **The world-faithful reading, occurrence by occurrence.** -/
theorem specialize_eq (a : NestedValue T K) (ν : K → Bool) :
    a.specialize ν
      = a.agg ((a.occs.filter (fun o => ν o.2 = true)).map
          (fun o => o.1.specialize ν)) :=
  congrArg a.agg (kept_realizedWorld a ν)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **A decision of the realized world** is an occurrence of the value,
present as its annotation is realized, reading the world the valuation
cuts out of its own expression. -/
theorem mem_realizedWorld {a : NestedValue T K} {ν : K → Bool} {G : WorldGrp T K}
    (hG : G ∈ (a.realizedWorld ν).grps) {m : AggExpr T K × K × Bool} (hm : m ∈ G.mems) :
    ∃ o ∈ a.occs, m = (o.1, o.2, ν o.2) ∧ trW G.sub = o.1.realizedWorld ν := by
  obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hG
  obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.mp hm
  exact ⟨o, Multiset.mem_bind.mpr ⟨g, hg, ho⟩, rfl, trW_realized hg ho ν⟩

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **The values a nested value takes survive the pushforward**: the
worlds correspond, and each reads what the world it came from reads. -/
theorem vals_mapAnn {K' : Type} [CommSemiringWithMonus K'] [DecidableEq K']
    (h : K → K') (a : NestedValue T K) : (a.mapAnn h).vals = a.vals := by
  have hfil : Multiset.filter
      ((fun W : World T K' => W.IsWorld (a.mapAnn h)) ∘ World.mapAnn h)
        a.worlds
      = Multiset.filter (fun W => W.IsWorld a) a.worlds :=
    Multiset.filter_congr (fun W _ => World.isWorld_mapAnn (a := a) h W)
  unfold vals
  rw [worlds_mapAnn, Multiset.filter_map, hfil, Multiset.map_map]
  exact congrArg Multiset.toFinset
    (Multiset.map_congr rfl (fun W _ => valOn_mapAnn h a W))

omit [ValueType T] [DecidableEq K] in
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
  obtain ⟨G, hG, hvG⟩ := Multiset.mem_bind.mp hv
  obtain ⟨m, hm, -⟩ := Multiset.mem_map.mp hvG
  obtain ⟨hmG, hp⟩ := Multiset.mem_filter.mp hm
  have hfam : m.2.1 ∈ a.occs.map Prod.snd := by
    rw [occs, ← isWorldOf_of_mem_worlds hmem, Multiset.bind_map, Multiset.map_bind]
    refine Multiset.mem_bind.mpr ⟨G, hG, ?_⟩
    unfold WorldGrp.base
    rw [Multiset.map_map]
    exact Multiset.mem_map_of_mem _ hmG
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hfam
  have key : m.2.1 * SemiringWithMonus.delta (a.occs.map Prod.snd).sum = m.2.1 := by
    rw [hs, Multiset.sum_cons]
    exact SemiringWithMonus.delta_absorb _ _
  obtain ⟨x, hx⟩ := World.exists_ann_eq_mul hG hmG hp
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
  ⟨fun s => gf (a.agg s), a.groups, a.scalar, a.fam, a.grouped⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem groups_postcomp (gf : T → T) (a : NestedValue T K) :
    (postcomp gf a).groups = a.groups := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem occs_postcomp (gf : T → T) (a : NestedValue T K) :
    (postcomp gf a).occs = a.occs := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem scalar_postcomp (gf : T → T) (a : NestedValue T K) :
    (postcomp gf a).scalar = a.scalar := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem collapse_postcomp (gf : T → T) (a : NestedValue T K) :
    (postcomp gf a).collapse = gf a.collapse := rfl

omit [CommSemiringWithMonus K] [DecidableEq K] in
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

omit [ValueType T] [DecidableEq K] in
/-- And a test of `gf(a)` is the composed test of `a`. -/
theorem predProvWith_postcomp (gf : T → T) (a : NestedValue T K)
    (P : T → Kleene) :
    (postcomp gf a).predProvWith P = a.predProvWith (fun v => P (gf v)) := rfl

omit [ValueType T] [DecidableEq K] in
/-- **A test no value satisfies annotates `𝟘`.** -/
theorem predProvWith_of_never (a : NestedValue T K) {P : T → Kleene}
    (h : ∀ v : T, P v ≠ Kleene.true) : a.predProvWith P = 0 := by
  refine Multiset.sum_eq_zero (fun x hx => ?_)
  rw [Multiset.mem_map] at hx
  obtain ⟨W, _, rfl⟩ := hx
  rw [Having.chiOf, ite_eq_right (h _), mul_zero]

end Readings

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
  AggExpr.ofValue ⟨fun _ => v, [], true, FamId.none⟩

omit [ValueType T] in
@[simp] theorem annList_constInner (v : T) : (constInner v : AggExpr T K).annList = [] := rfl

/-- **The nested value of an ordinary token**: nothing is nested, each
occurrence carrying a value rather than a family. The token's aggregate
has to be symmetric to be the outer one, a nested value's aggregate being
a function of the bag. -/
def ofAggValue (a : AggValue T K) (hsym : a.agg.Symmetric) : NestedValue T K :=
  ⟨a.agg.onBag hsym,
    {([], ((a.occs.map (fun o => ((constInner o.fst : AggExpr T K), o.snd)) :
      List (AggExpr T K × K)) : Multiset (AggExpr T K × K)))},
    a.scalar, a.fam, by
      intro g hg o ho
      rw [Multiset.mem_singleton] at hg
      subst hg
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp ho)
      rfl⟩

/-- **A world of an unnested token, as a world of its nested form**: the
one empty inner family, and the occurrences the subfamily keeps. -/
def worldOf (a : AggValue T K) (W : Finset (Fin a.occs.length)) : World T K :=
  ⟨{⟨[], ∅, ((List.finRange a.occs.length).map (fun i =>
      ((constInner (a.occs.get i).fst : AggExpr T K), (a.occs.get i).snd, decide (i ∈ W))) :
        List (AggExpr T K × K × Bool))⟩}⟩

omit [ValueType T] in
/-- It is a world of the nested form. -/
theorem isWorldOf_worldOf (a : AggValue T K) (hsym : a.agg.Symmetric)
    (W : Finset (Fin a.occs.length)) :
    (worldOf a W).IsWorldOf (ofAggValue a hsym) := by
  unfold World.IsWorldOf worldOf ofAggValue
  rw [Multiset.map_singleton]
  refine congrArg _ (Prod.ext rfl ?_)
  show (Multiset.ofList _).map _ = Multiset.ofList _
  rw [Multiset.map_coe]
  refine congrArg Multiset.ofList ?_
  refine List.ext_getElem (by simp) (fun n h₁ h₂ => ?_)
  simp

section DegenerateAnn

variable [CommSemiringWithMonus K]

omit [ValueType T] in
/-- **A world of an unnested value is annotated as the token's own
family annotates it.** -/
theorem ann_worldOf (a : AggValue T K)
    (W : Finset (Fin a.occs.length)) :
    (worldOf a W).ann = Having.worldAnn a.anns W := by
  have hpres : ((Multiset.ofList ((List.finRange a.occs.length).map (fun i =>
      ((constInner (a.occs.get i).fst : AggExpr T K), (a.occs.get i).snd, decide (i ∈ W))))).map
      (fun m : AggExpr T K × K × Bool => if m.2.2 = true then m.2.1 else 1)).prod
      = ∏ i ∈ W, a.anns i := by
    rw [Multiset.map_coe, Multiset.prod_coe, List.map_map,
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
  have habs : ((Multiset.ofList ((List.finRange a.occs.length).map (fun i =>
      ((constInner (a.occs.get i).fst : AggExpr T K), (a.occs.get i).snd, decide (i ∈ W))))).map
      (fun m : AggExpr T K × K × Bool => if m.2.2 = true then 0 else m.2.1)).sum
      = ∑ i ∈ Wᶜ, a.anns i := by
    rw [Multiset.map_coe, Multiset.sum_coe, List.map_map,
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
  unfold World.ann World.presentProd World.absentSum worldOf
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Multiset.sum_singleton,
    WorldGrp.prod, WorldGrp.absent]
  rw [hpres, habs, Finset.prod_empty, mul_one,
    show (∑ x ∈ (∅ : Finset (Fin ([] : List K).length))ᶜ, ([] : List K).get x) = 0 from
      Finset.sum_eq_zero (fun j _ => absurd j.isLt (Nat.not_lt_zero _)), add_zero,
    Having.worldAnn]

end DegenerateAnn

end NestedValue

/-! ## The aggregate side of a lifted value

A column of aggregate kind holds an ordinary token, a nested one or an
aggregate expression. `AggTok` is that choice, and `GenValue` is built on
it, so an ordinary token keeps its type and everything already proved
about `AggValue` applies to the `tok` case unchanged. The `nest` case has
its own readings, and what is proved of them travels: the pushforward
moves no value (`NestedValue.valOn_mapAnn`), keeps the values the column
takes (`vals_mapAnn`) and commutes with the predicate provenance
(`AggQueryHom`'s `NestedValue.predProvWith_mapAnn`), so the hom
commutation of a column and of a predicate asks nothing about the kind of
token. It also absorbs the `δ`-guard of its own family
(`NestedValue.predProvWith_delta_absorb`), which is what the evaluator's
supersede bookkeeping needs, and over `𝔹[X]` only the world a valuation
cuts out is annotated true (`NestedValue.World.ann_eval_iff`), which is
what the random-world reading needs. So no result of the metatheory asks
which kind of token a column holds any more. What a result may still
exclude is the *operator* that builds one – second-level aggregation,
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
def setFam (φ : FamId T) : AggTok T K → AggTok T K
  | .tok a => .tok { a with fam := φ }
  | .nest a => .nest { a with fam := φ }
  | .expr a => .expr { a with fam := φ }

@[simp] theorem fam_setFam (φ : FamId T) (a : AggTok T K) : (a.setFam φ).fam = φ := by
  cases a <;> rfl

theorem setFam_tok (φ : FamId T) (a : AggValue T K) :
    (AggTok.tok a).setFam φ = .tok { a with fam := φ } := rfl

theorem setFam_nest (φ : FamId T) (a : NestedValue T K) :
    (AggTok.nest a).setFam φ = .nest { a with fam := φ } := rfl

theorem setFam_expr (φ : FamId T) (a : AggExpr T K) :
    (AggTok.expr a).setFam φ = .expr { a with fam := φ } := rfl

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
def predProvOfWith (P : T → Kleene) : AggTok T K → K
  | .tok a => a.predProvOfWith P
  | .nest a => a.predProvWith P
  | .expr a => a.predProvWith P

/-- Read the token's aggregate through a function – what a term over
one aggregate column produces. -/
def postcomp (gf : T → T) : AggTok T K → AggTok T K
  | .tok a => .tok ⟨fun L => gf (a.agg L), a.occs, a.scalar, a.fam⟩
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
def predProvOf (op : CompOp) (c : T) (x : AggTok T K) : K :=
  x.predProvOfWith (fun v => op.eval3 v c)

/-- The world-faithful reading under a valuation of the annotations. On
a nested token it is the value in the world the valuation realizes, inner
occurrences included. -/
def specialize (ν : K → Bool) : AggTok T K → T
  | .tok a => a.specialize ν
  | .nest a => a.specialize ν
  | .expr a => a.specialize ν

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem specialize_tok (a : AggValue T K) (ν : K → Bool) :
    (AggTok.tok a).specialize ν = a.specialize ν := rfl

/-- The values the token takes over its worlds, for a key reading – the
nested worlds on a nested token. -/
def vals : AggTok T K → Finset T
  | .tok a => a.vals
  | .nest a => a.vals
  | .expr a => a.vals

/-- `[a ≐ v]`. -/
def altProv (x : AggTok T K) (v : T) : K :=
  x.predProvOfWith (fun y => CompOp.syneq.eval3 y v)

@[simp] theorem predProvOfWith_tok (a : AggValue T K) (P : T → Kleene) :
    (AggTok.tok a).predProvOfWith P = a.predProvOfWith P := rfl

@[simp] theorem predProvOfWith_expr (a : AggExpr T K) (P : T → Kleene) :
    (AggTok.expr a).predProvOfWith P = a.predProvWith P := rfl

@[simp] theorem predProvOf_tok (a : AggValue T K) (op : CompOp) (c : T) :
    (AggTok.tok a).predProvOf op c = a.predProvOf op c := rfl

omit [CommSemiringWithMonus K] [DecidableEq K] in
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

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- The values a column takes survive the pushforward, whichever kind of
token it holds. -/
theorem vals_mapAnn {K' : Type} [CommSemiringWithMonus K'] [DecidableEq K']
    (f : K → K') (x : AggTok T K) : (x.mapAnn f).vals = x.vals := by
  cases x with
  | tok a => exact AggValue.vals_mapAnn f a
  | nest a => exact NestedValue.vals_mapAnn f a
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
@[simp] theorem collapse_setFam (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).collapse = x.collapse := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem scalar_setFam (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).scalar = x.scalar := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem annList_setFam [AddCommMonoid K] (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).annList = x.annList := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem isNested_setFam (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).isNested = x.isNested := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem isTok_setFam (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).isTok = x.isTok := by cases x <;> rfl

@[simp] theorem predProvOfWith_setFam (φ : FamId T) (P : T → Kleene) (x : AggTok T K) :
    (x.setFam φ).predProvOfWith P = x.predProvOfWith P := by cases x <;> rfl

@[simp] theorem predProvOf_setFam (φ : FamId T) (op : CompOp) (c : T) (x : AggTok T K) :
    (x.setFam φ).predProvOf op c = x.predProvOf op c := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem specialize_setFam (φ : FamId T) (ν : K → Bool) (x : AggTok T K) :
    (x.setFam φ).specialize ν = x.specialize ν := by cases x <;> rfl

omit [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem vals_setFam (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).vals = x.vals := by cases x <;> rfl

@[simp] theorem altProv_setFam (φ : FamId T) (x : AggTok T K) (v : T) :
    (x.setFam φ).altProv v = x.altProv v := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem mapAnn_setFam {K' : Type} (f : K → K') (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).mapAnn f = (x.mapAnn f).setFam φ := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem postcomp_setFam (gf : T → T) (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).postcomp gf = (x.postcomp gf).setFam φ := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem setFam_setFam (φ ψ : FamId T) (x : AggTok T K) :
    (x.setFam φ).setFam ψ = x.setFam ψ := by cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem setFam_fam (x : AggTok T K) : x.setFam x.fam = x := by cases x <;> rfl

end AggTok

namespace AggValue

omit [ValueType T] in
/-- The deterministic reading of a lifted value. -/
def collapseSum : T ⊕ AggTok T K → T :=
  Sum.elim id AggTok.collapse

omit [ValueType T] in
@[simp] theorem collapseSum_inr_setFam (φ : FamId T) (x : AggTok T K) :
    collapseSum (Sum.inr (x.setFam φ)) = collapseSum (Sum.inr x) := by
  cases x <;> rfl

omit [ValueType T] in
/-- **A lifted value with its family forgotten**: what two queries that
compute the same values through different operators agree on. -/
def eraseFamSum : T ⊕ AggTok T K → T ⊕ AggTok T K :=
  Sum.map id (AggTok.setFam FamId.none)

omit [ValueType T] in
@[simp] theorem eraseFamSum_inl (v : T) :
    eraseFamSum (Sum.inl v : T ⊕ AggTok T K) = Sum.inl v := rfl

omit [ValueType T] in
@[simp] theorem eraseFamSum_inr_setFam (φ : FamId T) (x : AggTok T K) :
    eraseFamSum (Sum.inr (x.setFam φ)) = eraseFamSum (Sum.inr x) := by
  simp [eraseFamSum]

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
