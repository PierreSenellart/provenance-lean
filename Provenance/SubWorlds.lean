/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.AggValueCongr
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Bound.Init

/-!
# The subfamilies of a listing, as a bag

A world of an occurrence family is a set of positions of its listing, and
what a reading takes from it is three things: the product of the
annotations it keeps, the sum of those it leaves out, and the sequence of
occurrences it selects. `subWorlds ann L` is the bag of those triples,
one per subset of positions, built by a recursion over the listing rather
than over `Finset (Fin L.length)` (`univ_map_eq_subWorlds`).

Its point is what a recursion over the list makes easy: two listings that
differ by a tie-block permutation – adjacent occurrences swapped where the
swapped occurrences look alike – give the same bag once each selected
occurrence is read through a map that cannot tell them apart
(`subWorlds_tiePerm`). Several readings of one listing, which is what a
joint reading of several aggregate values of one family is, are then
blind to the permutation *together*, since all of them are read off the
same selected sequence.
-/

@[expose] public section

variable {β β' K K' : Type}

/-- The commutative semiring underlying a commutative m-semiring, which
the subfamilies are counted in. A definition rather than an instance, to
be made local where it is used. -/
abbrev CommSemiringWithMonus.toCommSemiringSW [CommSemiringWithMonus K] : CommSemiring K :=
  { (inferInstance : Semiring K) with mul_comm := CommSemiringWithMonus.mul_comm }

section SubWorlds

variable [CommSemiring K]

/-- **The subfamilies of a listing**: per subset of its positions, the
product of the annotations kept, the sum of those left out, and the
occurrences selected, in order. -/
def subWorlds (ann : β → K) : List β → Multiset (K × K × List β)
  | [] => {(1, 0, [])}
  | b :: t =>
      (subWorlds ann t).map (fun w => (ann b * w.1, w.2.1, b :: w.2.2))
        + (subWorlds ann t).map (fun w => (w.1, ann b + w.2.1, w.2.2))

namespace SubWorldsAux

variable {n : ℕ}

def succEmb (n : ℕ) : Fin n ↪ Fin (n + 1) :=
  ⟨Fin.succ, Fin.succ_injective n⟩

theorem filter_succ_insert (W' : Finset (Fin n)) :
    Finset.univ.filter
        (fun i : Fin n => i.succ ∈ insert (0 : Fin (n+1)) (W'.map (succEmb n)))
      = W' := by
  ext i
  simp [succEmb, Fin.succ_ne_zero]

theorem filter_succ_map (W' : Finset (Fin n)) :
    Finset.univ.filter (fun i : Fin n => i.succ ∈ W'.map (succEmb n)) = W' := by
  ext i
  simp [succEmb]

theorem notMem_map_succ (W' : Finset (Fin n)) :
    (0 : Fin (n+1)) ∉ W'.map (succEmb n) := by
  simp [succEmb, Fin.succ_ne_zero]

theorem compl_map (W' : Finset (Fin n)) :
    (W'.map (succEmb n))ᶜ = insert (0 : Fin (n+1)) (W'ᶜ.map (succEmb n)) := by
  ext i
  cases i using Fin.cases with
  | zero => simp [succEmb, Fin.succ_ne_zero]
  | succ j => simp [succEmb, Fin.succ_ne_zero]

theorem compl_insert_map (W' : Finset (Fin n)) :
    (insert (0 : Fin (n+1)) (W'.map (succEmb n)))ᶜ = W'ᶜ.map (succEmb n) := by
  rw [Finset.compl_insert, compl_map, Finset.erase_insert (notMem_map_succ _)]

theorem insert_filter {W : Finset (Fin (n+1))} (h0 : (0 : Fin (n+1)) ∈ W) :
    insert (0 : Fin (n+1))
        ((Finset.univ.filter (fun i : Fin n => i.succ ∈ W)).map (succEmb n))
      = W := by
  ext i
  cases i using Fin.cases with
  | zero => simp [h0]
  | succ j => simp [succEmb, Fin.succ_ne_zero]

theorem map_filter {W : Finset (Fin (n+1))} (h0 : (0 : Fin (n+1)) ∉ W) :
    (Finset.univ.filter (fun i : Fin n => i.succ ∈ W)).map (succEmb n) = W := by
  ext i
  cases i using Fin.cases with
  | zero => simp [succEmb, Fin.succ_ne_zero, h0]
  | succ j => simp [succEmb]

/-- The subsets of `Fin (n + 1)`, split by whether they hold `0`. -/
theorem univ_val_split :
    (Finset.univ : Finset (Finset (Fin (n + 1)))).val
      = (Finset.univ : Finset (Finset (Fin n))).val.map
          (fun W' => insert (0 : Fin (n+1)) (W'.map (succEmb n)))
        + (Finset.univ : Finset (Finset (Fin n))).val.map
          (fun W' => W'.map (succEmb n)) := by
  rw [← Multiset.filter_add_not (fun W : Finset (Fin (n+1)) => (0 : Fin (n+1)) ∈ W)
    (Finset.univ : Finset (Finset (Fin (n + 1)))).val]
  congr 1
  · have hinj : Function.Injective
        (fun W' : Finset (Fin n) => insert (0 : Fin (n+1)) (W'.map (succEmb n))) :=
      fun W₁ W₂ h => by
        have h' : insert (0 : Fin (n+1)) (W₁.map (succEmb n))
            = insert 0 (W₂.map (succEmb n)) := h
        rw [← filter_succ_insert W₁, h', filter_succ_insert]
    refine (Multiset.Nodup.ext (Multiset.Nodup.filter _ Finset.univ.nodup)
      (Multiset.Nodup.map hinj Finset.univ.nodup)).mpr (fun W => ?_)
    simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and,
      Multiset.mem_map]
    constructor
    · intro h0
      exact ⟨_, insert_filter h0⟩
    · rintro ⟨W', rfl⟩
      exact Finset.mem_insert_self _ _
  · have hinj : Function.Injective
        (fun W' : Finset (Fin n) => W'.map (succEmb n)) :=
      fun W₁ W₂ h => by
        have h' : W₁.map (succEmb n) = W₂.map (succEmb n) := h
        rw [← filter_succ_map W₁, h', filter_succ_map]
    refine (Multiset.Nodup.ext (Multiset.Nodup.filter _ Finset.univ.nodup)
      (Multiset.Nodup.map hinj Finset.univ.nodup)).mpr (fun W => ?_)
    simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and,
      Multiset.mem_map]
    constructor
    · intro h0
      exact ⟨_, map_filter h0⟩
    · rintro ⟨W', rfl⟩
      exact notMem_map_succ _

end SubWorldsAux

open SubWorldsAux in
/-- **The bag of subfamilies is the enumeration of the subsets of
positions.** -/
theorem univ_map_eq_subWorlds (ann : β → K) : ∀ L : List β,
    (Finset.univ : Finset (Finset (Fin L.length))).val.map
        (fun W => (∏ i ∈ W, ann (L.get i), ∑ i ∈ Wᶜ, ann (L.get i), Having.seqOf L W))
      = subWorlds ann L
  | [] => by
    have : (Finset.univ : Finset (Finset (Fin ([] : List β).length))) = {∅} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun W _ =>
        Finset.eq_empty_of_forall_notMem (fun i => absurd i.isLt (Nat.not_lt_zero _))⟩
    rw [this]
    simp [subWorlds, Having.seqOf]
  | b :: t => by
    rw [subWorlds, ← univ_map_eq_subWorlds ann t]
    show (Finset.univ : Finset (Finset (Fin (t.length + 1)))).val.map _ = _
    rw [univ_val_split, Multiset.map_add, Multiset.map_map, Multiset.map_map,
      Multiset.map_map, Multiset.map_map]
    congr 1
    · refine Multiset.map_congr rfl (fun W' _ => ?_)
      simp only [Function.comp]
      erw [Finset.prod_insert (notMem_map_succ _), compl_insert_map, Finset.prod_map,
        Finset.sum_map]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      show (if (0 : Fin (t.length + 1)) ∈ insert 0 (W'.map (succEmb t.length)) then [b] else [])
          ++ Having.seqOf t (Finset.univ.filter
            (fun i => i.succ ∈ insert (0 : Fin (t.length + 1)) (W'.map (succEmb t.length))))
        = b :: Having.seqOf t W'
      rw [ite_eq_left (Finset.mem_insert_self _ _), filter_succ_insert]
      rfl
    · refine Multiset.map_congr rfl (fun W' _ => ?_)
      simp only [Function.comp]
      erw [compl_map, Finset.sum_insert (notMem_map_succ _), Finset.prod_map,
        Finset.sum_map]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      show (if (0 : Fin (t.length + 1)) ∈ W'.map (succEmb t.length) then [b] else [])
          ++ Having.seqOf t (Finset.univ.filter
            (fun i => i.succ ∈ W'.map (succEmb t.length)))
        = Having.seqOf t W'
      rw [ite_eq_right (notMem_map_succ _), filter_succ_map]
      rfl

/-- The subfamilies of `a :: L`, read through `rd`: those of `L`, with `a`
kept or left out. -/
theorem subWorlds_cons_map {γ : Type} (ann : β → K) (rd : β → γ) (a : β) (L : List β) :
    (subWorlds ann (a :: L)).map (fun w => (w.1, w.2.1, w.2.2.map rd))
      = ((subWorlds ann L).map (fun w => (w.1, w.2.1, w.2.2.map rd))).map
          (fun w => (ann a * w.1, w.2.1, rd a :: w.2.2))
        + ((subWorlds ann L).map (fun w => (w.1, w.2.1, w.2.2.map rd))).map
          (fun w => (w.1, ann a + w.2.1, w.2.2)) := by
  simp only [subWorlds, Multiset.map_add, Multiset.map_map]
  rfl

/-- **A tie-block permutation leaves the subfamilies alone**, read through
a map `rd` of the selected occurrences that cannot tell two tied
occurrences apart. Only the selected sequence needs `rd`: the two worlds
that keep one of two swapped occurrences and leave out the other trade
places, and their annotations go with them. -/
theorem subWorlds_tiePerm {γ : Type} (ann : β → K) (rd : β → γ)
    {eqv : β → β → Prop} (hrd : ∀ {a b}, eqv a b → rd a = rd b)
    {L₁ L₂ : List β} (h : TiePerm eqv L₁ L₂) :
    (subWorlds ann L₁).map (fun w => (w.1, w.2.1, w.2.2.map rd))
      = (subWorlds ann L₂).map (fun w => (w.1, w.2.1, w.2.2.map rd)) := by
  induction h with
  | nil => rfl
  | @cons a L₁ L₂ _ ih =>
    rw [subWorlds_cons_map, subWorlds_cons_map, ih]
  | @swap a b hab L₁ L₂ _ ih =>
    rw [subWorlds_cons_map, subWorlds_cons_map, subWorlds_cons_map, subWorlds_cons_map, ih]
    simp only [Multiset.map_add, Multiset.map_map]
    rw [add_add_add_comm]
    have hr := hrd hab
    congr 2
    · refine Multiset.map_congr rfl (fun w _ => ?_)
      simp only [Function.comp, hr, mul_left_comm (ann a)]
    · refine Multiset.map_congr rfl (fun w _ => ?_)
      simp only [Function.comp, add_left_comm (ann a)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The subfamilies of a listing pushed through a map of annotations**:
the annotations of every world pushed through it. -/
theorem subWorlds_map [CommSemiring K'] (f : K →+* K') (ann : β → K) (ann' : β' → K')
    (e : β → β') (hann : ∀ b, ann' (e b) = f (ann b)) : ∀ L : List β,
    subWorlds ann' (L.map e)
      = (subWorlds ann L).map (fun w => (f w.1, f w.2.1, w.2.2.map e))
  | [] => by simp [subWorlds]
  | b :: t => by
    simp only [List.map_cons, subWorlds, subWorlds_map f ann ann' e hann t, Multiset.map_add,
      Multiset.map_map]
    congr 1
    · refine Multiset.map_congr rfl (fun w _ => ?_)
      simp [hann, map_mul]
    · refine Multiset.map_congr rfl (fun w _ => ?_)
      simp [hann, map_add]

end SubWorlds

/-! ## An aggregate expression read off its selected sequence -/

namespace AggExpr

variable {T : Type}

/-- Whether a selected sequence of occurrences is a world: it holds an
occurrence of the group of every grouped leaf. -/
def okSeq (e : AggExpr T K)
    (s : List ((Fin e.arity → T) × K × (Fin e.arity → Bool) × (Fin e.arity → Bool))) : Prop :=
  ∀ j, e.scalar j = false → ∃ z ∈ s, z.2.2.1 j = true

/-- The value of the expression on a selected sequence of occurrences. -/
def valSeq (e : AggExpr T K)
    (s : List ((Fin e.arity → T) × K × (Fin e.arity → Bool) × (Fin e.arity → Bool))) : T :=
  e.g (fun j => e.aggs j ((s.filter (fun z => z.2.2.1 j && z.2.2.2 j)).map (fun z => z.1 j)))

/-- **A world is read off the occurrences it selects.** -/
theorem isWorld_iff_okSeq (e : AggExpr T K) (W : Finset (Fin e.occs.length)) :
    e.IsWorld W ↔ e.okSeq (Having.seqOf e.occs W) := by
  unfold IsWorld okSeq
  refine forall₂_congr (fun j _ => ?_)
  have hset : W ∩ e.inFrame j
      = W.filter (fun i => (fun z : (Fin e.arity → T) × K × (Fin e.arity → Bool)
          × (Fin e.arity → Bool) => z.2.2.1 j) (e.occs.get i) = true) := by
    ext i
    rw [Finset.mem_inter, mem_inFrame, Finset.mem_filter]
  rw [hset, ← Finset.card_pos, ← Having.seqOf_length,
    Having.seqOf_filter_inter (fun z => z.2.2.1 j) e.occs W, List.length_pos_iff_exists_mem]
  simp only [List.mem_filter]

/-- **So is its value.** -/
theorem valOn_eq_valSeq (e : AggExpr T K) (W : Finset (Fin e.occs.length)) :
    e.valOn W = e.valSeq (Having.seqOf e.occs W) := by
  unfold valOn valSeq leafVal
  simp only [leafSeq_eq_filter]

end AggExpr
