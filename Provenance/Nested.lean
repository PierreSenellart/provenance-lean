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
occurrences are present *and* which occurrences of each inner value
are.

## No sequence, and so a bag

`≼` orders plain tuples, and an occurrence of a nested value carries a
tuple with an *aggregate* column, so there is nothing to order these
occurrences by: the family a nested value aggregates is a bag. Its
aggregate is accordingly a function of a bag, a world is a bag of
occurrences each carrying what the world decides about it, and `worlds`
enumerates the worlds off that bag. Nothing indexes an occurrence, so no
reading has to be shown invariant under a relisting of the family, and an
operator building a nested value needs no order to list its group in –
which is what it could not have, a listing of a multiset not being
computable.

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
inner families each belong to a *different* outer occurrence, and the
world is choosing which of those occurrences are present, so a blanket
condition would quantify over occurrences the world has already
excluded.

Whether a world should also be *barred* from meeting the family of an
inner value it does not read is open, and the predicate is a parameter
of everything below (`World.IsWorldWith`) so that either answer is a
substitution. No instance realizes such a world – the outer occurrence
is annotated `δ(β)` for the very family at issue, and in an exclusive
semiring the complement factor annihilates them – so the choice is
between imposing the coherence and letting exclusivity dispose of it.
-/

variable {T K : Type} [ValueType T]

/-- **A nested aggregate value**: an outer aggregate over occurrences
that carry aggregate values rather than values. -/
structure NestedValue (T K : Type) where
  /-- **The outer aggregate, as a function of a bag.** It cannot read a
  sequence: the order `≼` is an order on plain tuples, and an occurrence
  of a nested value carries a tuple with an aggregate column, so there is
  no sequence for an order-dependent aggregate to read. An ordinary
  aggregate becomes one of these when it is symmetric
  (`SeqAggFunc.onBag`), and an order-dependent outer aggregate has no
  nested reading at all – it goes through the alternatives
  (`AggQueryIn.Alt`), after which nothing is nested. -/
  agg : Multiset T → T
  /-- **The occurrences, as a bag**: per outer occurrence, what the term
  reads there and the occurrence's own annotation. What it reads is an
  aggregate *expression* and not one aggregate value, because a term over
  several aggregate columns is one – `sum(c₁ - c₂)` over a block with two
  counts is as ordinary as `avg(c)` over one – and an ordinary token
  embeds as the expression of itself (`AggExpr.ofValue`). A bag for the
  reason the aggregate is a function of one – nothing orders a tuple with
  an aggregate column – and so an operator building one has no order to
  list its group in and needs none. -/
  occs : Multiset (AggExpr T K × K)
  /-- Whether the outer reading is scalar – whether the empty world is
  one of its worlds. -/
  scalar : Bool

namespace NestedValue

/-- **An occurrence as a world sees it**: the occurrence itself – what
the term reads there and the occurrence's own annotation – together with
what the world decides about it. -/
structure WorldOcc (T K : Type) where
  /-- The occurrence: the inner expression read there and the
  annotation. -/
  occ : AggExpr T K × K
  /-- Whether the outer occurrence is present. -/
  present : Bool
  /-- Which occurrences of the inner expression's shared family are
  present. A world may keep some of these at an outer occurrence it
  drops, which is the combination `q:nestedcoherent` is about. -/
  sub : Finset (Fin occ.1.occs.length)

/-- **A world of a nested value**: a decision per occurrence – which
outer occurrences are present *and* which occurrences of each inner
value are. The decisions are a bag because the occurrences are one, so
nothing indexes them; which value a world belongs to is `IsWorldOf`. -/
structure World (T K : Type) where
  /-- Each occurrence of the value, with the world's decision about it. -/
  occs : Multiset (WorldOcc T K)

/-- **Whose world it is**: the occurrences a world decides on are the
value's own, with their multiplicities. -/
def World.IsWorldOf (W : World T K) (a : NestedValue T K) : Prop :=
  W.occs.map WorldOcc.occ = a.occs

/-- **The occurrences a world keeps**: the ones it declares present.
The outer family is met when this is not empty, and the value read in
the world is the outer aggregate of these occurrences' inner values. -/
def World.kept (W : World T K) : Multiset (WorldOcc T K) :=
  W.occs.filter (fun d => d.present = true)

/-- **Admissibility, with the coherence condition as a parameter.**
`extra` is the clause `q:nestedcoherent` leaves open – whether a world
is barred from meeting the family of an inner value it does not read.
The document's reading is `IsWorld`, which takes `extra` to be
vacuous. -/
def World.IsWorldWith (W : World T K) (a : NestedValue T K)
    (extra : World T K → Prop) : Prop :=
  (a.scalar = true ∨ 0 < Multiset.card W.kept)
    ∧ (∀ d ∈ W.occs, d.present = true → d.occ.1.IsWorld d.sub)
    ∧ extra W

/-- **The worlds the document commits to**: the outer family met unless
the reading is scalar, and, of each inner expression *the world reads*,
the family of each of its grouped leaves met – which is that
expression's own world condition (`AggExpr.IsWorld`). -/
def World.IsWorld (W : World T K) (a : NestedValue T K) : Prop :=
  W.IsWorldWith a (fun _ => True)

/-- The reading that bars a world from meeting the family of an inner
value it does not read – the other answer to `q:nestedcoherent`. -/
def World.IsWorldCoherent (W : World T K) (a : NestedValue T K) : Prop :=
  W.IsWorldWith a (fun W => ∀ d ∈ W.occs, d.present = false → d.sub = ∅)

instance (W : World T K) (a : NestedValue T K) : Decidable (W.IsWorld a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The value of a nested aggregate in a world**: the outer aggregate
of the bag of inner values read there. -/
def valOn (a : NestedValue T K) (W : World T K) : T :=
  a.agg (W.kept.map (fun d => d.occ.1.valOn d.sub))

/-- The world in which every occurrence, outer and inner, is present. -/
def World.full (a : NestedValue T K) : World T K :=
  ⟨a.occs.map (fun o => ⟨o, true, Finset.univ⟩)⟩

omit [ValueType T] in
/-- The full world is a world of the value it is built from. -/
@[simp] theorem World.isWorldOf_full (a : NestedValue T K) :
    (World.full a).IsWorldOf a := by
  show (a.occs.map _).map _ = a.occs
  rw [Multiset.map_map]
  exact Multiset.map_id' a.occs

/-- **The deterministic reading**: the outer aggregate of the inner
collapses. -/
def collapse (a : NestedValue T K) : T :=
  a.agg (a.occs.map (fun o => o.1.collapse))

omit [ValueType T] in
/-- **Everything present reads as the collapse.** -/
theorem valOn_full (a : NestedValue T K) :
    a.valOn (World.full a) = a.collapse := by
  unfold valOn collapse World.kept World.full
  refine congrArg a.agg ?_
  rw [Multiset.filter_map,
    show Multiset.filter
        ((fun d : WorldOcc T K => d.present = true) ∘
          fun o : AggExpr T K × K => (⟨o, true, Finset.univ⟩ : WorldOcc T K))
        a.occs = a.occs from Multiset.filter_eq_self.mpr (fun o _ => rfl),
    Multiset.map_map]
  exact Multiset.map_congr rfl (fun o _ => rfl)

/-! ## The worlds of a nested value, enumerated

The worlds are the decisions one can make at each occurrence, so they
are built by running over the occurrences and letting every world so far
gain every decision available at the next one. The occurrences are a bag
and the construction has to be read off it rather than off a listing of
it, which is what `addOcc` being left-commutative says – and the
multiplicities are kept: two occurrences carrying the same inner value
and the same annotation are two occurrences, and a world may keep one and
drop the other. -/

section Enumeration

/-- The decisions available at one occurrence: present or not, and any
subfamily of its inner value. -/
def decisions (o : AggExpr T K × K) : Multiset (WorldOcc T K) :=
  (Finset.univ : Finset (Bool × Finset (Fin o.1.occs.length))).val.map
    (fun c => ⟨o, c.1, c.2⟩)

/-- One more occurrence: every world so far gains every decision
available at it. -/
def addOcc (o : AggExpr T K × K)
    (ws : Multiset (Multiset (WorldOcc T K))) :
    Multiset (Multiset (WorldOcc T K)) :=
  (decisions o).bind (fun d => ws.map (fun W => d ::ₘ W))

omit [ValueType T] in
/-- **The order the occurrences are taken in does not matter**, which is
what lets the worlds be read off the bag. -/
instance : LeftCommutative (addOcc (T := T) (K := K)) where
  left_comm o₁ o₂ ws := by
    unfold addOcc
    simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]
    rw [Multiset.bind_bind]
    exact Multiset.bind_congr (fun d₂ _ => Multiset.bind_congr
      (fun d₁ _ => Multiset.map_congr rfl
        (fun W _ => Multiset.cons_swap _ _ _)))

/-! ### What a world weighs, read off the occurrences' statistics

A nested world's annotation is a product over its occurrences
(`World.ann_split`, where `K` is complemented), its value the outer
aggregate of what its present occurrences read, and its admissibility the
conjunction of their own. So each of the three is a function of one datum
per occurrence – the factor its decision carries, the value it
contributes if present, and whether that decision is a world of it – and
the whole reading is a function of the *bag* of those data. That is what
makes a nested value's reading depend on its occurrences' columns only
through `AggExpr.worldStats`, which is what `GenValue.Equiv` carries. -/

/-- The datum a decision carries: its factor, the value it contributes
where it is present, and whether it is a world of its own expression. -/
def statOfDec [CommSemiringWithMonus K] (d : WorldOcc T K) :
    K × Option T × Bool :=
  ((if d.present = true then d.occ.2 else (1 - d.occ.2))
      * ((∏ j ∈ d.sub, d.occ.1.anns j)
        * (1 - ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j)),
    (if d.present = true then some (d.occ.1.valOn d.sub) else none),
    (if d.present = true then decide (d.occ.1.IsWorld d.sub) else true))

/-- The data available at one occurrence. -/
def occStats [CommSemiringWithMonus K] (o : AggExpr T K × K) :
    Multiset (K × Option T × Bool) :=
  (decisions o).map statOfDec

/-- One more occurrence, on the data: every choice so far gains every
datum available at it, accumulating the values it reads, the factor it
carries and whether every decision is a world of its own. -/
def addChoice [CommSemiringWithMonus K] (st : Multiset (K × Option T × Bool))
    (cs : Multiset (Multiset T × K × Bool)) : Multiset (Multiset T × K × Bool) :=
  st.bind (fun z => cs.map (fun c =>
    ((match z.snd.fst with | none => c.fst | some v => v ::ₘ c.fst),
      z.fst * c.snd.fst, z.snd.snd && c.snd.snd)))

omit [ValueType T] in
/-- **The order the occurrences are taken in does not matter here
either.** -/
instance [CommSemiringWithMonus K] :
    LeftCommutative (addChoice (T := T) (K := K)) where
  left_comm st₁ st₂ cs := by
    unfold addChoice
    simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]
    rw [Multiset.bind_bind]
    refine Multiset.bind_congr (fun z₂ _ => Multiset.bind_congr
      (fun z₁ _ => Multiset.map_congr rfl (fun c _ => ?_)))
    refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
    · cases z₁.snd.fst <;> cases z₂.snd.fst <;>
        simp [Multiset.cons_swap]
    · exact mul_left_comm _ _ _
    · cases z₁.snd.snd <;> cases z₂.snd.snd <;> simp

/-- **The choices a bag of data allows**: one datum per occurrence, with
the values, the factor and the admissibility accumulated. -/
def choicesOf [CommSemiringWithMonus K]
    (ss : Multiset (Multiset (K × Option T × Bool))) :
    Multiset (Multiset T × K × Bool) :=
  Multiset.foldr addChoice {(0, 1, true)} ss

/-- **What a world amounts to**: the values its present occurrences read,
the factor it carries, and whether every present occurrence's decision is
a world of its own expression. -/
def summaryOfOccs [CommSemiringWithMonus K] (W : Multiset (WorldOcc T K)) :
    Multiset T × K × Bool :=
  ((W.filter (fun d => d.present = true)).map (fun d => d.occ.1.valOn d.sub),
    (W.map (fun d => (statOfDec d).fst)).prod,
    decide (∀ d ∈ W, d.present = true → d.occ.1.IsWorld d.sub))

omit [ValueType T] in
/-- One more occurrence accumulates its datum. -/
theorem summaryOfOccs_cons [CommSemiringWithMonus K] (d : WorldOcc T K)
    (W : Multiset (WorldOcc T K)) :
    summaryOfOccs (d ::ₘ W)
      = ((match (statOfDec d).snd.fst with
            | none => (summaryOfOccs W).fst
            | some v => v ::ₘ (summaryOfOccs W).fst),
          (statOfDec d).fst * (summaryOfOccs W).snd.fst,
          (statOfDec d).snd.snd && (summaryOfOccs W).snd.snd) := by
  have hall : (∀ x ∈ d ::ₘ W, x.present = true → x.occ.1.IsWorld x.sub)
      ↔ ((d.present = true → d.occ.1.IsWorld d.sub)
        ∧ ∀ x ∈ W, x.present = true → x.occ.1.IsWorld x.sub) := by
    constructor
    · intro h
      exact ⟨h d (Multiset.mem_cons_self _ _),
        fun x hx => h x (Multiset.mem_cons_of_mem hx)⟩
    · rintro ⟨hd, hW⟩ x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx'
      · exact hd
      · exact hW x hx'
  by_cases hp : d.present = true
  · have hopt : (statOfDec d).snd.fst = some (d.occ.1.valOn d.sub) := by
      simp [statOfDec, hp]
    have hok : (statOfDec d).snd.snd = decide (d.occ.1.IsWorld d.sub) := by
      simp [statOfDec, hp]
    rw [hopt, hok]
    unfold summaryOfOccs
    dsimp only
    refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
    · show ((d ::ₘ W).filter (fun x => x.present = true)).map _ = _
      rw [Multiset.filter_cons_of_pos
        (p := fun x : WorldOcc T K => x.present = true) W hp, Multiset.map_cons]
    · show ((d ::ₘ W).map (fun x => (statOfDec x).fst)).prod = _
      rw [Multiset.map_cons, Multiset.prod_cons]
    · show decide (∀ x ∈ d ::ₘ W, x.present = true → x.occ.1.IsWorld x.sub) = _
      dsimp only
      rw [decide_eq_decide.mpr hall, Bool.decide_and]
      refine congrArg₂ (fun x y : Bool => x && y) ?_ rfl
      simp [hp]
  · have hopt : (statOfDec d).snd.fst = none := by
      simp [statOfDec, hp]
    have hok : (statOfDec d).snd.snd = true := by
      simp [statOfDec, hp]
    rw [hopt, hok]
    unfold summaryOfOccs
    dsimp only
    refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
    · show ((d ::ₘ W).filter (fun x => x.present = true)).map _ = _
      rw [Multiset.filter_cons_of_neg
        (p := fun x : WorldOcc T K => x.present = true) W (by simpa using hp)]
    · show ((d ::ₘ W).map (fun x => (statOfDec x).fst)).prod = _
      rw [Multiset.map_cons, Multiset.prod_cons]
    · show decide (∀ x ∈ d ::ₘ W, x.present = true → x.occ.1.IsWorld x.sub) = _
      dsimp only
      rw [decide_eq_decide.mpr hall, Bool.decide_and]
      refine congrArg₂ (fun x y : Bool => x && y) ?_ rfl
      simp [hp]

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

omit [ValueType T] in
/-- **The data at an occurrence are its column's statistics**, taken once
with the occurrence present and once with it absent: its annotation or the
complement of it times the factor the subfamily carries, the value where
it is read, and its own admissibility. So a nested value reads its
occurrences' columns through `AggExpr.worldStats` and nothing else. -/
theorem occStats_eq [CommSemiringWithMonus K] (o : AggExpr T K × K) :
    occStats o
      = ((o.1.worldStats.map (fun z =>
            (o.2 * (z.fst * (1 - z.snd.fst)), some z.snd.snd.fst,
              z.snd.snd.snd)))
        + (o.1.worldStats.map (fun z =>
            ((1 - o.2) * (z.fst * (1 - z.snd.fst)), none, true)))) := by
  have huniv : (Finset.univ
        : Finset (Bool × Finset (Fin o.1.occs.length))).val
      = ((Finset.univ : Finset (Finset (Fin o.1.occs.length))).val.map
          (fun S => ((true : Bool), S)))
        + ((Finset.univ : Finset (Finset (Fin o.1.occs.length))).val.map
          (fun S => ((false : Bool), S))) := by
    rw [show (Finset.univ : Finset (Bool × Finset (Fin o.1.occs.length)))
        = (Finset.univ : Finset Bool) ×ˢ
          (Finset.univ : Finset (Finset (Fin o.1.occs.length))) from
      (Finset.univ_product_univ).symm, Finset.product_val]
    show (Finset.univ : Finset Bool).val.bind _ = _
    rw [show (Finset.univ : Finset Bool).val = {true, false} from rfl]
    simp [Multiset.cons_bind]
  unfold occStats decisions AggExpr.worldStats
  rw [Multiset.map_map, huniv, Multiset.map_add, Multiset.map_map,
    Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg₂ (fun x y : Multiset (K × Option T × Bool) => x + y) ?_ ?_
  · exact Multiset.map_congr rfl (fun S _ => by simp [statOfDec])
  · exact Multiset.map_congr rfl (fun S _ => by simp [statOfDec])

omit [ValueType T] in
/-- **The enumeration of worlds is the enumeration of the data.** Every
world decides once at each occurrence, and what the reading makes of a
world is what its decisions' data amount to – so the reading runs over the
occurrences' statistics and not over their families. -/
theorem foldr_addOcc_map_summary [CommSemiringWithMonus K] :
    ∀ s : Multiset (AggExpr T K × K),
      (Multiset.foldr addOcc {0} s).map summaryOfOccs
        = choicesOf (s.map occStats) := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.foldr_zero, Multiset.map_zero, Multiset.map_singleton]
    show {summaryOfOccs 0} = choicesOf 0
    unfold summaryOfOccs choicesOf
    simp
  | cons o s ih =>
    rw [Multiset.foldr_cons, Multiset.map_cons, choicesOf, Multiset.foldr_cons,
      addOcc, addChoice, occStats, Multiset.map_bind, Multiset.bind_map]
    refine Multiset.bind_congr (fun d _ => ?_)
    rw [Multiset.map_map, ← choicesOf, ← ih, Multiset.map_map]
    exact Multiset.map_congr rfl (fun W _ => summaryOfOccs_cons d W)

/-- **The worlds of a nested value.** -/
def worlds (a : NestedValue T K) : Multiset (World T K) :=
  (Multiset.foldr addOcc {0} a.occs).map World.mk

omit [ValueType T] in
/-- A world the enumeration produces decides on each occurrence of the
bag it ran over, once. -/
theorem map_occ_of_mem_foldr {s : Multiset (AggExpr T K × K)}
    {W : Multiset (WorldOcc T K)} (h : W ∈ Multiset.foldr addOcc {0} s) :
    W.map WorldOcc.occ = s := by
  induction s using Multiset.induction_on generalizing W with
  | empty =>
    rw [Multiset.foldr_zero, Multiset.mem_singleton] at h
    rw [h, Multiset.map_zero]
  | cons o s ih =>
    rw [Multiset.foldr_cons, addOcc, Multiset.mem_bind] at h
    obtain ⟨d, hd, hW⟩ := h
    rw [Multiset.mem_map] at hW
    obtain ⟨W', hW', rfl⟩ := hW
    have hdo : d.occ = o := by
      unfold decisions at hd
      rw [Multiset.mem_map] at hd
      obtain ⟨c, _, rfl⟩ := hd
      rfl
    rw [Multiset.map_cons, ih hW', hdo]

omit [ValueType T] in
/-- **Every world the enumeration produces is a world of the value.** -/
theorem isWorldOf_of_mem_worlds {a : NestedValue T K} {W : World T K}
    (h : W ∈ a.worlds) : W.IsWorldOf a := by
  rw [worlds, Multiset.mem_map] at h
  obtain ⟨W', hW', rfl⟩ := h
  exact map_occ_of_mem_foldr hW'

omit [ValueType T] in
/-- A decided occurrence is one of the decisions available at the
occurrence it decides about. -/
theorem mem_decisions_self (d : WorldOcc T K) : d ∈ decisions d.occ := by
  unfold decisions
  rw [Multiset.mem_map]
  exact ⟨(d.present, d.sub), Finset.mem_val.mpr (Finset.mem_univ _), rfl⟩

omit [ValueType T] in
/-- **And conversely**: a decision per occurrence of the bag is one of
the worlds the enumeration produces. -/
theorem mem_foldr_of_map_occ : ∀ {W : Multiset (WorldOcc T K)}
    {s : Multiset (AggExpr T K × K)}, W.map WorldOcc.occ = s →
    W ∈ Multiset.foldr addOcc {0} s := by
  intro W
  induction W using Multiset.induction_on with
  | empty =>
    intro s hs
    rw [← hs, Multiset.map_zero, Multiset.foldr_zero]
    exact Multiset.mem_singleton_self 0
  | cons d W ih =>
    intro s hs
    rw [← hs, Multiset.map_cons, Multiset.foldr_cons, addOcc, Multiset.mem_bind]
    exact ⟨d, mem_decisions_self d,
      Multiset.mem_map_of_mem _ (ih rfl)⟩

omit [ValueType T] in
/-- **The worlds of a value are exactly the decisions on its
occurrences.** -/
theorem mem_worlds_iff {a : NestedValue T K} {W : World T K} :
    W ∈ a.worlds ↔ W.IsWorldOf a := by
  refine ⟨isWorldOf_of_mem_worlds, fun h => ?_⟩
  rw [worlds, Multiset.mem_map]
  exact ⟨W.occs, mem_foldr_of_map_occ h, rfl⟩

end Enumeration

/-! ## What a world of a nested value is annotated

The annotation is the one every family gets: the product of what is
present times `𝟙 ⊖` the sum of what is absent. It does not depend on
`q:nestedcoherent`, which is about *which* worlds are admitted and not
about how a given one is weighed – so it can be written now. The inner
products range over every occurrence, which is the literal reading of
"the occurrences present in `W`"; under the coherent reading they
collapse to the occurrences the world actually reads
(`World.presentProd_eq_of_coherent`). -/

section Annotation

variable [CommSemiringWithMonus K]

/-- The product of the annotations a world keeps: the outer occurrences
it keeps and, for each occurrence, the inner ones it keeps. -/
def World.presentProd (W : World T K) : K :=
  (W.occs.map (fun d => if d.present = true then d.occ.2 else 1)).prod
    * (W.occs.map (fun d => ∏ j ∈ d.sub, d.occ.1.anns j)).prod

/-- The sum of the annotations a world leaves out. -/
def World.absentSum (W : World T K) : K :=
  (W.occs.map (fun d => if d.present = true then 0 else d.occ.2)).sum
    + (W.occs.map (fun d => ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j)).sum

/-- **The annotation of a world of a nested value.** -/
def World.ann (W : World T K) : K :=
  W.presentProd * (1 - W.absentSum)

omit [ValueType T] in
/-- **The annotation of a nested world splits over its occurrences**,
where `K` is complemented: each occurrence contributes its own outer
annotation, or the complement of it where the world drops it, times its
inner family's own world annotation. The document's one global monus over
both levels and this per-occurrence form agree exactly there – it is
`sec:prelim`'s law, the form a family split into parts uses – and the
split is what makes a nested reading a function of what its occurrences
read, rather than of their families position by position. -/
theorem World.ann_split (hc : complemented K) (W : World T K) :
    W.ann = (W.occs.map (fun d =>
      (if d.present = true then d.occ.2 else (1 - d.occ.2))
        * ((∏ j ∈ d.sub, d.occ.1.anns j)
          * (1 - ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j)))).prod := by
  unfold World.ann World.presentProd World.absentSum
  rw [← Multiset.sum_map_add, monus_multiset_sum hc, Multiset.map_map]
  have hout : ∀ d : WorldOcc T K,
      (1 - ((if d.present = true then 0 else d.occ.2)
        + ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j))
      = (if d.present = true then 1 else (1 - d.occ.2))
        * (1 - ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j) := by
    intro d
    rw [hc]
    by_cases hp : d.present = true
    · rw [hp]
      simp [monus_zero]
    · rw [show d.present = false from by simpa using hp]
      simp
  rw [show ((fun a => 1 - a) ∘ fun d : WorldOcc T K =>
        (if d.present = true then 0 else d.occ.2)
          + ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j)
      = (fun d : WorldOcc T K =>
        (if d.present = true then 1 else (1 - d.occ.2))
          * (1 - ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j)) from funext hout,
    Multiset.prod_map_mul, Multiset.prod_map_mul, Multiset.prod_map_mul]
  rw [show (W.occs.map (fun d : WorldOcc T K =>
        if d.present = true then d.occ.2 else 1)).prod
      * (W.occs.map (fun d : WorldOcc T K =>
          ∏ j ∈ d.sub, d.occ.1.anns j)).prod
      * ((W.occs.map (fun d : WorldOcc T K =>
            if d.present = true then 1 else (1 - d.occ.2))).prod
        * (W.occs.map (fun d : WorldOcc T K =>
            1 - ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j)).prod)
      = ((W.occs.map (fun d : WorldOcc T K =>
              if d.present = true then d.occ.2 else 1)).prod
          * (W.occs.map (fun d : WorldOcc T K =>
              if d.present = true then 1 else (1 - d.occ.2))).prod)
        * ((W.occs.map (fun d : WorldOcc T K =>
              ∏ j ∈ d.sub, d.occ.1.anns j)).prod
          * (W.occs.map (fun d : WorldOcc T K =>
              1 - ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j)).prod)
      from mul_mul_mul_comm _ _ _ _,
    ← Multiset.prod_map_mul, ← Multiset.prod_map_mul, ← Multiset.prod_map_mul]
  rw [← Multiset.prod_map_mul]
  refine congrArg Multiset.prod (Multiset.map_congr rfl (fun d _ => ?_))
  refine congrArg₂ (fun x y : K => x * y) ?_ rfl
  by_cases hp : d.present = true
  · rw [hp]
    simp
  · rw [show d.present = false from by simpa using hp]
    simp

omit [ValueType T] in
/-- Nothing is absent from the full world. -/
@[simp] theorem World.absentSum_full (a : NestedValue T K) :
    (World.full a).absentSum = 0 := by
  unfold World.absentSum World.full
  simp

omit [ValueType T] in
/-- **The full world is annotated by the product of everything.** -/
theorem World.ann_full (a : NestedValue T K) :
    (World.full a).ann = (World.full a).presentProd := by
  rw [World.ann, World.absentSum_full, monus_zero, mul_one]

omit [ValueType T] in
/-- **Under the coherent reading the inner products are over the
occurrences the world reads**: an occurrence the world drops keeps no
inner occurrence, so its factor is empty. -/
theorem World.presentProd_eq_of_coherent {W : World T K}
    (h : ∀ d ∈ W.occs, d.present = false → d.sub = ∅) :
    W.presentProd
      = (W.occs.map (fun d => if d.present = true then d.occ.2 else 1)).prod
        * (W.kept.map (fun d => ∏ j ∈ d.sub, d.occ.1.anns j)).prod := by
  have h1 : ((W.occs.filter (fun d : WorldOcc T K => ¬ d.present = true)).map
      (fun d => ∏ j ∈ d.sub, d.occ.1.anns j)).prod = 1 := by
    refine Multiset.prod_eq_one (fun x hx => ?_)
    rw [Multiset.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [Multiset.mem_filter] at hd
    rw [h d hd.1 (by simpa using hd.2), Finset.prod_empty]
  rw [World.presentProd, World.kept]
  refine congrArg (fun x => _ * x) ?_
  conv_lhs => rw [← Multiset.filter_add_not
    (fun d : WorldOcc T K => d.present = true) W.occs]
  rw [Multiset.map_add, Multiset.prod_add, h1, mul_one]

omit [ValueType T] in
/-- **The annotation of an occurrence a world keeps is a factor of the
world's annotation.** This is what lets a world swallow the `δ`-guard of
the family it reads. -/
theorem World.exists_ann_eq_mul {W : World T K} {d : WorldOcc T K}
    (hd : d ∈ W.occs) (hp : d.present = true) :
    ∃ x : K, W.ann = d.occ.2 * x := by
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hd
  refine ⟨(t.map (fun e => if e.present = true then e.occ.2 else 1)).prod
      * ((W.occs.map (fun e => ∏ j ∈ e.sub, e.occ.1.anns j)).prod
        * (1 - W.absentSum)), ?_⟩
  rw [World.ann, World.presentProd,
    show (W.occs.map (fun e => if e.present = true then e.occ.2 else 1)).prod
      = d.occ.2
        * (t.map (fun e => if e.present = true then e.occ.2 else 1)).prod from by
      rw [ht, Multiset.map_cons, Multiset.prod_cons, ite_eq_left hp],
    mul_assoc, mul_assoc]

end Annotation

omit [ValueType T] in
/-- A world of the document's reading is one of the coherent reading's
as soon as it keeps no inner occurrence it does not read. -/
theorem World.isWorld_of_isWorldCoherent {a : NestedValue T K}
    {W : World T K} (h : W.IsWorldCoherent a) : W.IsWorld a :=
  ⟨h.1, h.2.1, trivial⟩

/-! ## The pushforward of the annotations

Changing the annotation semiring moves no value and no occurrence: the
outer family keeps its occurrences, each inner value keeps its own, and a
world of the pushforward is a world of the original. Only the
annotations travel, and the readings follow them. -/

section MapAnn

variable {K' : Type}

/-- **The pushforward of a nested value**: both the inner values and the
outer annotations go through `h`. -/
def mapAnn (h : K → K') (a : NestedValue T K) : NestedValue T K' where
  agg := a.agg
  occs := a.occs.map (fun o => (o.1.mapAnn h, h o.2))
  scalar := a.scalar

omit [ValueType T] in
@[simp] theorem agg_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).agg = a.agg := rfl

omit [ValueType T] in
@[simp] theorem scalar_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).scalar = a.scalar := rfl

omit [ValueType T] in
@[simp] theorem occs_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).occs = a.occs.map (fun o => (o.1.mapAnn h, h o.2)) := rfl

/-- **The pushforward of one decided occurrence**: the inner value and
the annotation travel, and the inner subfamily is the same one, read
through the pushforward's own occurrence list. -/
def WorldOcc.mapAnn (h : K → K') (d : WorldOcc T K) : WorldOcc T K' where
  occ := (d.occ.1.mapAnn h, h d.occ.2)
  present := d.present
  sub := d.sub.map
    (finCongr (AggExpr.length_map_occs h d.occ.1)).toEmbedding

/-- **A world of the pushforward is a world of the original**, the
occurrences being the same ones and each keeping its decision. -/
def World.mapAnn (h : K → K') (W : World T K) : World T K' :=
  ⟨W.occs.map (WorldOcc.mapAnn h)⟩

omit [ValueType T] in
/-- The pushforward keeps what the world kept. -/
theorem World.kept_mapAnn (h : K → K') (W : World T K) :
    (W.mapAnn h).kept = W.kept.map (WorldOcc.mapAnn h) := by
  show Multiset.filter _ (W.occs.map (WorldOcc.mapAnn h))
    = (W.occs.filter _).map (WorldOcc.mapAnn h)
  rw [Multiset.filter_map]
  exact congrArg (Multiset.map (WorldOcc.mapAnn h))
    (Multiset.filter_congr (fun d _ => Iff.rfl))

omit [ValueType T] in
/-- The pushforward of a world of a value is a world of its
pushforward. -/
theorem World.isWorldOf_mapAnn (h : K → K') {a : NestedValue T K}
    {W : World T K} (hW : W.IsWorldOf a) :
    (W.mapAnn h).IsWorldOf (a.mapAnn h) := by
  show (W.occs.map (WorldOcc.mapAnn h)).map WorldOcc.occ
    = a.occs.map (fun o => (o.1.mapAnn h, h o.2))
  rw [Multiset.map_map, ← hW, Multiset.map_map]
  exact Multiset.map_congr rfl (fun d _ => rfl)

omit [ValueType T] in
/-- **A transported world is admissible exactly when the world it came
from is.** The condition reads the conventions and the non-emptiness of
the families, and the pushforward moves neither. -/
theorem World.isWorld_mapAnn (h : K → K') {a : NestedValue T K}
    (W : World T K) : (W.mapAnn h).IsWorld (a.mapAnn h) ↔ W.IsWorld a := by
  have hcard : Multiset.card (W.mapAnn h).kept = Multiset.card W.kept := by
    rw [World.kept_mapAnn, Multiset.card_map]
  have hmem : ∀ d' ∈ (W.mapAnn h).occs, ∃ d ∈ W.occs, d' = d.mapAnn h := by
    intro d' hd'
    rw [World.mapAnn, Multiset.mem_map] at hd'
    obtain ⟨d, hd, rfl⟩ := hd'
    exact ⟨d, hd, rfl⟩
  have hpres : ∀ d : WorldOcc T K, (d.mapAnn h).present = d.present :=
    fun _ => rfl
  have hne : ∀ d : WorldOcc T K,
      (d.mapAnn h).occ.1.IsWorld (d.mapAnn h).sub ↔ d.occ.1.IsWorld d.sub := by
    intro d
    show (d.occ.1.mapAnn h).IsWorld
        (d.sub.map (finCongr (AggExpr.length_map_occs h d.occ.1)).toEmbedding)
      ↔ _
    exact AggExpr.isWorld_mapAnn h d.occ.1 d.sub
  unfold World.IsWorld World.IsWorldWith
  refine and_congr (or_congr Iff.rfl (by rw [hcard])) (and_congr ?_ Iff.rfl)
  · constructor
    · intro hall d hd hp
      exact (hne d).mp (hall (d.mapAnn h) (Multiset.mem_map_of_mem _ hd)
        (by rw [hpres]; exact hp))
    · intro hall d' hd' hp
      obtain ⟨d, hd, rfl⟩ := hmem d' hd'
      rw [hpres] at hp
      exact (hne d).mpr (hall d hd hp)

/-! ### The worlds travel with the occurrences

The occurrences are a bag and the worlds are read off that bag, so the
pushforward needs no reindexing of anything: the worlds of the
pushforward are the pushforwards of the worlds, each reading the value its
own world reads. Only the annotations move, which is what
`NestedValue.World.ann_mapAnn` says of the weight and
`AggQueryHom`'s `predProvWith_mapAnn` of the reading. -/

omit [ValueType T] in
/-- **The decisions available at an occurrence travel with it**: a
decision about the pushed occurrence is a decision about the occurrence,
the inner family keeping its length. -/
theorem decisions_mapAnn (h : K → K') (o : AggExpr T K × K) :
    decisions (o.1.mapAnn h, h o.2)
      = (decisions o).map (WorldOcc.mapAnn h) := by
  classical
  let eqv : (Bool × Finset (Fin o.1.occs.length))
      ≃ (Bool × Finset (Fin (o.1.mapAnn h).occs.length)) :=
    (Equiv.refl Bool).prodCongr
      ((finCongr (AggExpr.length_map_occs h o.1)).finsetCongr)
  unfold decisions
  rw [Multiset.map_map]
  conv_lhs => rw [← Finset.map_univ_equiv eqv]
  rw [Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl (fun c _ => ?_)
  show (⟨(o.1.mapAnn h, h o.2), (eqv c).1, (eqv c).2⟩ : WorldOcc T K')
    = (⟨o, c.1, c.2⟩ : WorldOcc T K).mapAnn h
  show (⟨(o.1.mapAnn h, h o.2), c.1,
      (finCongr (AggExpr.length_map_occs h o.1)).finsetCongr c.2⟩
      : WorldOcc T K') = _
  rw [Equiv.finsetCongr_apply]
  rfl

omit [ValueType T] in
/-- The enumeration travels with them. -/
theorem foldr_addOcc_mapAnn (h : K → K')
    (s : Multiset (AggExpr T K × K)) :
    Multiset.foldr addOcc {0} (s.map (fun o => (o.1.mapAnn h, h o.2)))
      = (Multiset.foldr addOcc {0} s).map
          (fun W => W.map (WorldOcc.mapAnn h)) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.foldr_zero, Multiset.foldr_zero]
    rfl
  | cons o s ih =>
    rw [Multiset.map_cons, Multiset.foldr_cons, Multiset.foldr_cons, addOcc,
      addOcc, ih, decisions_mapAnn, Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun d _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun W _ => ?_)
    show WorldOcc.mapAnn h d ::ₘ W.map (WorldOcc.mapAnn h)
      = (d ::ₘ W).map (WorldOcc.mapAnn h)
    rw [Multiset.map_cons]

omit [ValueType T] in
/-- **The worlds of the pushforward are the pushforwards of the
worlds**, with their multiplicities – no reindexing, the occurrences
being a bag on both sides. -/
theorem worlds_mapAnn (h : K → K') (a : NestedValue T K) :
    (a.mapAnn h).worlds = a.worlds.map (World.mapAnn h) := by
  show (Multiset.foldr addOcc {0} (a.occs.map _)).map World.mk
    = (((Multiset.foldr addOcc {0} a.occs).map World.mk).map (World.mapAnn h))
  rw [foldr_addOcc_mapAnn, Multiset.map_map, Multiset.map_map]
  rfl

omit [ValueType T] in
/-- **The pushforward moves no value**: a transported world reads what
the world it came from reads. -/
theorem valOn_mapAnn (h : K → K') (a : NestedValue T K) (W : World T K) :
    (a.mapAnn h).valOn (W.mapAnn h) = a.valOn W := by
  show a.agg ((W.mapAnn h).kept.map (fun d => d.occ.1.valOn d.sub)) = a.agg _
  rw [World.kept_mapAnn, Multiset.map_map]
  refine congrArg a.agg (Multiset.map_congr rfl (fun d _ => ?_))
  exact AggExpr.valOn_mapAnn h d.occ.1 d.sub

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

/-- What the reading makes of one choice: the factor it carries times the
truth of the test on the value it reads, where the choice is admissible,
and `𝟘` where it is not. -/
def readOfChoice (agg : Multiset T → T) (sc : Bool) (P : T → Kleene)
    (c : Multiset T × K × Bool) : K :=
  if (sc = true ∨ 0 < Multiset.card c.fst) ∧ c.snd.snd = true
  then c.snd.fst * Having.chiOf P (agg c.fst) else 0

/-- **The predicate provenance of a nested value runs over the data its
occurrences' columns give**, where `K` is complemented: the weight of a
world is the product of its decisions' factors (`World.ann_split`), the
value is the outer aggregate of what the present ones read, and the
admissibility is their own. So two nested values whose occurrences' data
agree read alike – which is what the hom commutation needs, the data
being `AggExpr.worldStats` and the annotation. -/
theorem predProvWith_eq_choicesOf (hc : complemented K) (a : NestedValue T K)
    (P : T → Kleene) :
    a.predProvWith P
      = ((choicesOf (a.occs.map occStats)).map
          (readOfChoice a.agg a.scalar P)).sum := by
  unfold predProvWith
  rw [sum_map_filter]
  unfold worlds
  rw [Multiset.map_map, ← foldr_addOcc_map_summary a.occs, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun Wo _ => ?_))
  have hkept : (World.mk Wo).kept = Wo.filter (fun d => d.present = true) := rfl
  have hval : a.valOn (World.mk Wo) = a.agg (summaryOfOccs Wo).fst := rfl
  have hann : (World.mk Wo).ann = (summaryOfOccs Wo).snd.fst := by
    rw [World.ann_split hc]
    rfl
  have hok : ((summaryOfOccs Wo).snd.snd = true)
      ↔ (∀ d ∈ Wo, d.present = true → d.occ.1.IsWorld d.sub) := by
    show (decide _ = true) ↔ _
    exact decide_eq_true_iff
  have hcard : Multiset.card (summaryOfOccs Wo).fst
      = Multiset.card (Wo.filter (fun d => d.present = true)) := by
    show Multiset.card ((Wo.filter (fun d => d.present = true)).map _) = _
    exact Multiset.card_map _ _
  have hw : (World.mk Wo).IsWorld a
      ↔ ((a.scalar = true ∨ 0 < Multiset.card (summaryOfOccs Wo).fst)
        ∧ (summaryOfOccs Wo).snd.snd = true) := by
    unfold World.IsWorld World.IsWorldWith
    rw [hok, hcard, hkept]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, trivial⟩
  unfold readOfChoice
  by_cases h : (World.mk Wo).IsWorld a
  · have h' := hw.mp h
    simp [h, h', hann, hval]
  · have h' : ¬ ((a.scalar = true
        ∨ 0 < Multiset.card (summaryOfOccs Wo).fst)
        ∧ (summaryOfOccs Wo).snd.snd = true) := fun hc' => h (hw.mpr hc')
    simp [h, h']

omit [DecidableEq K] in
/-- **Two nested values whose occurrences' data agree read alike.** -/
theorem predProvWith_congr_of_occStats (hc : complemented K)
    {a b : NestedValue T K} (hagg : a.agg = b.agg) (hsc : a.scalar = b.scalar)
    (hst : a.occs.map occStats = b.occs.map occStats) (P : T → Kleene) :
    a.predProvWith P = b.predProvWith P := by
  classical
  rw [predProvWith_eq_choicesOf hc, predProvWith_eq_choicesOf hc, hst, hagg,
    hsc]

/-- The comparison case. -/
def predProvOf (a : NestedValue T K) (op : CompOp) (c : T) : K :=
  a.predProvWith (fun v => op.eval3 v c)

/-- **What a valuation of the annotations decides about an
occurrence**: it is present when the valuation makes its annotation
true, and it keeps the inner occurrences whose annotations the valuation
makes true. -/
def realizedOcc (ν : K → Bool) (o : AggExpr T K × K) : WorldOcc T K :=
  ⟨o, ν o.2, Finset.univ.filter (fun j => ν (o.1.anns j))⟩

/-- **The world a valuation of the annotations realizes**: every
occurrence, outer or inner, whose annotation the valuation makes
true. -/
def realizedWorld (a : NestedValue T K) (ν : K → Bool) : World T K :=
  ⟨a.occs.map (realizedOcc ν)⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- The realized world is a world of the value it is read off. -/
@[simp] theorem isWorldOf_realizedWorld (a : NestedValue T K) (ν : K → Bool) :
    (a.realizedWorld ν).IsWorldOf a := by
  show (a.occs.map (realizedOcc ν)).map WorldOcc.occ = a.occs
  rw [Multiset.map_map]
  exact Multiset.map_id' a.occs

/-- **The world-faithful reading**: the value in the realized world. -/
def specialize (a : NestedValue T K) (ν : K → Bool) : T :=
  a.valOn (a.realizedWorld ν)

/-- **The values a nested value takes over its worlds**, for a key
reading. -/
def vals (a : NestedValue T K) : Finset T :=
  (((a.worlds.filter (fun W => W.IsWorld a)).map a.valOn)).toFinset

/-- **The values a nested value takes run over the data too.** -/
theorem vals_eq_choicesOf (hc : complemented K) (a : NestedValue T K) :
    a.vals
      = ((((choicesOf (a.occs.map occStats)).filter
          (fun c => (a.scalar = true ∨ 0 < Multiset.card c.fst)
            ∧ c.snd.snd = true)).map (fun c => a.agg c.fst))).toFinset := by
  unfold vals worlds
  refine congrArg Multiset.toFinset ?_
  rw [Multiset.filter_map, Multiset.map_map,
    ← foldr_addOcc_map_summary a.occs, Multiset.filter_map, Multiset.map_map]
  refine Multiset.map_congr ?_ (fun Wo _ => rfl)
  refine Multiset.filter_congr (fun Wo _ => ?_)
  have hcard : Multiset.card (summaryOfOccs Wo).fst
      = Multiset.card (Wo.filter (fun d => d.present = true)) := by
    show Multiset.card ((Wo.filter (fun d => d.present = true)).map _) = _
    exact Multiset.card_map _ _
  have hok : ((summaryOfOccs Wo).snd.snd = true)
      ↔ (∀ d ∈ Wo, d.present = true → d.occ.1.IsWorld d.sub) :=
    decide_eq_true_iff
  show (World.mk Wo).IsWorld a ↔ _
  unfold World.IsWorld World.IsWorldWith
  show _ ↔ ((a.scalar = true ∨ 0 < Multiset.card (summaryOfOccs Wo).fst)
    ∧ (summaryOfOccs Wo).snd.snd = true)
  rw [hok, hcard]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, trivial⟩

omit [DecidableEq K] in
/-- **Two nested values whose occurrences' data agree take the same
values.** -/
theorem vals_congr_of_occStats (hc : complemented K)
    {a b : NestedValue T K} (hagg : a.agg = b.agg) (hsc : a.scalar = b.scalar)
    (hst : a.occs.map occStats = b.occs.map occStats) :
    a.vals = b.vals := by
  classical
  rw [vals_eq_choicesOf hc, vals_eq_choicesOf hc, hst, hagg, hsc]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A valuation that keeps every occurrence realizes the full world. -/
theorem realizedWorld_of_forall (a : NestedValue T K) (ν : K → Bool)
    (h : ∀ x : K, ν x = true) : a.realizedWorld ν = World.full a := by
  unfold realizedWorld World.full
  refine congrArg World.mk (Multiset.map_congr rfl (fun o _ => ?_))
  simp [realizedOcc, h]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **Where every occurrence is realized the reading is the
collapse**, so the world-faithful reading and the deterministic one
agree on the database as it is. -/
theorem specialize_of_forall (a : NestedValue T K) (ν : K → Bool)
    (h : ∀ x : K, ν x = true) : a.specialize ν = a.collapse := by
  rw [specialize, realizedWorld_of_forall a ν h, valOn_full]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **The world-faithful reading, occurrence by occurrence**: the
valuation keeps the occurrences whose annotation it makes true, and reads
each of them in the world it cuts out of that occurrence's own
expression. -/
theorem specialize_eq (a : NestedValue T K) (ν : K → Bool) :
    a.specialize ν
      = a.agg ((a.occs.filter (fun o => ν o.2 = true)).map
          (fun o => o.1.specialize ν)) := by
  show a.agg _ = _
  refine congrArg a.agg ?_
  show ((a.occs.map (realizedOcc ν)).filter
      (fun d => d.present = true)).map (fun d => d.occ.1.valOn d.sub) = _
  rw [Multiset.filter_map, Multiset.map_map]
  exact Multiset.map_congr
    (Multiset.filter_congr (fun o _ => Iff.rfl)) (fun o _ => rfl)

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
  obtain ⟨d₀, hd₀⟩ := Multiset.card_pos_iff_exists_mem.mp hkept
  have hd₀occ : d₀ ∈ W.occs := Multiset.mem_of_mem_filter hd₀
  have hp : d₀.present = true := (Multiset.mem_filter.mp hd₀).2
  have hfam : d₀.occ.2 ∈ a.occs.map Prod.snd := by
    rw [← isWorldOf_of_mem_worlds hmem, Multiset.map_map]
    exact Multiset.mem_map_of_mem _ hd₀occ
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hfam
  have key : d₀.occ.2 * SemiringWithMonus.delta (a.occs.map Prod.snd).sum
      = d₀.occ.2 := by
    rw [hs, Multiset.sum_cons]
    exact SemiringWithMonus.delta_absorb _ _
  obtain ⟨x, hx⟩ := World.exists_ann_eq_mul hd₀occ hp
  rw [hx]
  calc d₀.occ.2 * x * Having.chiOf P (a.valOn W)
        * SemiringWithMonus.delta (a.occs.map Prod.snd).sum
      = (x * Having.chiOf P (a.valOn W))
        * (d₀.occ.2
          * SemiringWithMonus.delta (a.occs.map Prod.snd).sum) := by
        rw [mul_rotate d₀.occ.2, mul_assoc]
    _ = (x * Having.chiOf P (a.valOn W)) * d₀.occ.2 := by rw [key]
    _ = d₀.occ.2 * x * Having.chiOf P (a.valOn W) := (mul_rotate _ _ _).symm

/-- **Reading a nested value's aggregate through a function** – what a
term over the aggregate column it produces reads. The occurrences, the
convention and so the worlds are untouched, so every reading is the
reading of the value, read through `gf`. -/
def postcomp (gf : T → T) (a : NestedValue T K) : NestedValue T K :=
  ⟨fun s => gf (a.agg s), a.occs, a.scalar⟩

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
occurrences, and `ann_worldOf` says a world of it carries exactly
`Having.worldAnn` of the token's own family. -/

/-- The inner reading that reads nothing and returns `v`: the expression
of the token with no occurrence whose aggregate is `v`. Its only world is
the empty one, and it contributes no occurrence. -/
def constInner (v : T) : AggExpr T K :=
  AggExpr.ofValue ⟨fun _ => v, [], true⟩

/-- **The nested value of an ordinary token**: nothing is nested, each
occurrence carrying a value rather than a family. The token's aggregate
has to be symmetric to be the outer one, a nested value's aggregate being
a function of the bag. -/
def ofAggValue (a : AggValue T K) (hsym : a.agg.Symmetric) : NestedValue T K :=
  ⟨a.agg.onBag hsym,
    ((a.occs.map (fun o => ((constInner o.fst : AggExpr T K), o.snd)) :
      List (AggExpr T K × K)) : Multiset (AggExpr T K × K)),
    a.scalar⟩

/-- **What a subfamily of an unnested token decides about its `i`-th
occurrence**: the occurrence carries the value there as an inner value
that reads nothing, it is present when the subfamily keeps it, and it has
no inner occurrence to decide about. -/
def worldOccOf (a : AggValue T K) (W : Finset (Fin a.occs.length))
    (i : Fin a.occs.length) : WorldOcc T K :=
  ⟨((constInner (a.occs.get i).fst : AggExpr T K), (a.occs.get i).snd),
    decide (i ∈ W), ∅⟩

/-- **A world of an unnested token, as a world of its nested form.** -/
def worldOf (a : AggValue T K) (W : Finset (Fin a.occs.length)) :
    World T K :=
  ⟨((List.finRange a.occs.length).map (worldOccOf a W) : List (WorldOcc T K))⟩

omit [ValueType T] in
/-- It is a world of the nested form. -/
theorem isWorldOf_worldOf (a : AggValue T K) (hsym : a.agg.Symmetric)
    (W : Finset (Fin a.occs.length)) :
    (worldOf a W).IsWorldOf (ofAggValue a hsym) := by
  unfold World.IsWorldOf worldOf ofAggValue
  show (Multiset.ofList _).map _ = Multiset.ofList _
  rw [Multiset.map_coe]
  refine congrArg Multiset.ofList ?_
  refine List.ext_getElem (by simp) (fun n h₁ h₂ => ?_)
  simp [worldOccOf]

section DegenerateAnn

variable [CommSemiringWithMonus K]

omit [ValueType T] in
/-- **A world of an unnested value is annotated as the token's own
family annotates it.** -/
theorem ann_worldOf (a : AggValue T K)
    (W : Finset (Fin a.occs.length)) :
    (worldOf a W).ann = Having.worldAnn a.anns W := by
  have hmem : ∀ d ∈ (worldOf a W).occs,
      ∃ i : Fin a.occs.length, d = worldOccOf a W i := by
    intro d hd
    have hd' : d ∈ (((List.finRange a.occs.length).map (worldOccOf a W) :
        List (WorldOcc T K)) : Multiset (WorldOcc T K)) := hd
    rw [Multiset.mem_coe, List.mem_map] at hd'
    obtain ⟨i, _, rfl⟩ := hd'
    exact ⟨i, rfl⟩
  have hpres : ((worldOf a W).occs.map
      (fun d => if d.present = true then d.occ.2 else 1)).prod
      = ∏ i ∈ W, a.anns i := by
    show (Multiset.map _ (Multiset.ofList _)).prod = _
    rw [Multiset.map_coe, Multiset.prod_coe, List.map_map,
      show ((List.finRange a.occs.length).map
          ((fun d : WorldOcc T K => if d.present = true then d.occ.2 else 1) ∘
            worldOccOf a W)).prod
        = ∏ i : Fin a.occs.length, (if i ∈ W then a.anns i else 1) from by
          rw [Fin.prod_univ_def]
          exact congrArg List.prod (List.map_congr_left
            (fun i _ => by simp [worldOccOf, AggValue.anns])),
      ← Finset.prod_filter]
    exact Finset.prod_congr (Finset.filter_univ_mem W) (fun _ _ => rfl)
  have habs : ((worldOf a W).occs.map
      (fun d => if d.present = true then 0 else d.occ.2)).sum
      = ∑ i ∈ Wᶜ, a.anns i := by
    show (Multiset.map _ (Multiset.ofList _)).sum = _
    rw [Multiset.map_coe, Multiset.sum_coe, List.map_map,
      show ((List.finRange a.occs.length).map
          ((fun d : WorldOcc T K => if d.present = true then 0 else d.occ.2) ∘
            worldOccOf a W)).sum
        = ∑ i : Fin a.occs.length, (if i ∈ Wᶜ then a.anns i else 0) from by
          rw [Fin.sum_univ_def]
          refine congrArg List.sum (List.map_congr_left (fun i _ => ?_))
          by_cases hi : i ∈ W <;> simp [worldOccOf, AggValue.anns, hi],
      ← Finset.sum_filter]
    exact Finset.sum_congr (Finset.filter_univ_mem Wᶜ) (fun _ _ => rfl)
  have hip : ((worldOf a W).occs.map
      (fun d => ∏ j ∈ d.sub, d.occ.1.anns j)).prod = 1 := by
    refine Multiset.prod_eq_one (fun x hx => ?_)
    rw [Multiset.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := hmem d hd
    exact Finset.prod_empty
  have his : ((worldOf a W).occs.map
      (fun d => ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j)).sum = 0 := by
    refine Multiset.sum_eq_zero (fun x hx => ?_)
    rw [Multiset.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := hmem d hd
    exact Finset.sum_eq_zero (fun j _ => absurd j.isLt (by
      simp [worldOccOf, constInner, AggExpr.ofValue]))
  rw [World.ann, World.presentProd, World.absentSum, hpres, habs, hip, his,
    mul_one, add_zero, Having.worldAnn]

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
  | .nest a => .nest ⟨a.agg,
      a.occs.map (fun o => (o.1.mapAnn h, h o.2)), a.scalar⟩
  | .expr a => .expr (a.mapAnn h)

/-! ### The readings, on each kind of token

Each reading delegates: to `AggValue` on an ordinary token, to
`NestedValue` on a nested one – over the world set `q:nestedcoherent`
leaves as a choice between two available definitions – and to `AggExpr`
on an expression, whose worlds are the subfamilies of the shared family
meeting every grouped leaf. So the *definitions* cover all three kinds;
what the metatheory has not yet proved beyond an ordinary token it
excludes with `AggTok.isTok`, which is a statement about the proofs and
no longer about the definitions. -/

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
  | .tok a => .tok ⟨fun L => gf (a.agg L), a.occs, a.scalar⟩
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

end AggTok

namespace AggValue

omit [ValueType T] in
/-- The deterministic reading of a lifted value. -/
def collapseSum : T ⊕ AggTok T K → T :=
  Sum.elim id AggTok.collapse

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
      show a.agg _ = a.agg _
      refine congrArg a.agg ?_
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl
        (fun o _ => AggExpr.collapse_mapAnn h o.1)
    | expr a => exact AggExpr.collapse_mapAnn h a

end AggValue
