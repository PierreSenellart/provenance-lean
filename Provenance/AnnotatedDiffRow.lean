/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AnnotatedMuUnion
import Provenance.Semirings.Nat
import Mathlib.Algebra.Order.Monoid.Prod

/-!
# The difference is necessary in the annotated algebra

A set of classes that generates the annotated algebra contains `−`. The
witness semiring is `ℕ × ℕ`, `ℕ` read on two instances at once
(`NatPair`). The invariant is that, without a difference, every
annotation a query builds is zero in one coordinate exactly where it is in
the other (`ZeroPat`). That holds of sums and products, since `ℕ` has no
zero divisors, of `δ`, which is the support map, and of the `𝟙 ⊖ s` a
world of an aggregate value is weighed with. It fails for a difference:
`R − S`, with `R` holding `a` annotated `(1, 3)` and `S` holding it twice
annotated `(1, 1)`, gives `(1, 3) ⊖ (2, 2) = (0, 1)`
(`diff_mem_of_generatesAnn`).

The invariant is stated for any property `Q` of annotations closed under
those operations (`AnnClosed`), and proved of every annotation the
evaluator builds – a row's, the occurrences' of the tokens it carries,
and the predicate provenance of a selection on aggregate values
(`AggQueryIn.annIn_evaluate`).
-/

/-! ## Two copies of `ℕ` -/

/-- **`ℕ` read on two instances at once**: pairs, with every operation
componentwise. -/
def NatPair : Type := ℕ × ℕ

namespace NatPair

instance : CommSemiring NatPair := inferInstanceAs (CommSemiring (ℕ × ℕ))
instance : PartialOrder NatPair := inferInstanceAs (PartialOrder (ℕ × ℕ))
instance : IsOrderedAddMonoid NatPair := inferInstanceAs (IsOrderedAddMonoid (ℕ × ℕ))
instance : Sub NatPair := inferInstanceAs (Sub (ℕ × ℕ))
instance : DecidableEq NatPair := inferInstanceAs (DecidableEq (ℕ × ℕ))

/-- The two coordinates of a pair. -/
def fst (a : NatPair) : ℕ := Prod.fst (α := ℕ) (β := ℕ) a
/-- The second coordinate. -/
def snd (a : NatPair) : ℕ := Prod.snd (α := ℕ) (β := ℕ) a
/-- A pair from its coordinates. -/
def mk (u v : ℕ) : NatPair := ((u, v) : ℕ × ℕ)

@[simp] theorem fst_mk (u v : ℕ) : (mk u v).fst = u := rfl
@[simp] theorem snd_mk (u v : ℕ) : (mk u v).snd = v := rfl
theorem ext {a b : NatPair} (h₁ : a.fst = b.fst) (h₂ : a.snd = b.snd) : a = b :=
  Prod.ext h₁ h₂
@[simp] theorem fst_add (a b : NatPair) : (a + b).fst = a.fst + b.fst := rfl
@[simp] theorem snd_add (a b : NatPair) : (a + b).snd = a.snd + b.snd := rfl
@[simp] theorem fst_mul (a b : NatPair) : (a * b).fst = a.fst * b.fst := rfl
@[simp] theorem snd_mul (a b : NatPair) : (a * b).snd = a.snd * b.snd := rfl
@[simp] theorem fst_sub (a b : NatPair) : (a - b).fst = a.fst - b.fst := rfl
@[simp] theorem snd_sub (a b : NatPair) : (a - b).snd = a.snd - b.snd := rfl
@[simp] theorem fst_zero : (0 : NatPair).fst = 0 := rfl
@[simp] theorem snd_zero : (0 : NatPair).snd = 0 := rfl
@[simp] theorem fst_one : (1 : NatPair).fst = 1 := rfl
@[simp] theorem snd_one : (1 : NatPair).snd = 1 := rfl
theorem le_iff {a b : NatPair} : a ≤ b ↔ a.fst ≤ b.fst ∧ a.snd ≤ b.snd := Prod.le_def

instance : CanonicallyOrderedAdd NatPair := inferInstanceAs (CanonicallyOrderedAdd (ℕ × ℕ))

/-- The support map, coordinate by coordinate. -/
def deltaPair (a : NatPair) : NatPair :=
  mk (if a.fst = 0 then 0 else 1) (if a.snd = 0 then 0 else 1)

theorem natCast_eq (n : ℕ) : ((n : ℕ) : NatPair) = mk n n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, ih]; rfl

instance : SemiringWithMonus NatPair where
  monus_spec := fun a b c => by
    rw [le_iff, le_iff]
    simp only [fst_sub, snd_sub, fst_add, snd_add]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h₁, h₂⟩; exact ⟨by omega, by omega⟩
  delta := deltaPair
  delta_zero := rfl
  delta_natCast_pos := fun {n} hn => by
    rw [natCast_eq]
    refine ext ?_ ?_ <;> (simp only [deltaPair, fst_mk, snd_mk]; split_ifs <;> first | rfl | omega)
  delta_absorb := fun a b => by
    refine ext ?_ ?_
    · simp only [deltaPair, fst_mul, fst_add, fst_mk]
      by_cases h : a.fst = 0
      · simp [h]
      · rw [ite_eq_right (by omega), mul_one]
    · simp only [deltaPair, snd_mul, snd_add, snd_mk]
      by_cases h : a.snd = 0
      · simp [h]
      · rw [ite_eq_right (by omega), mul_one]

instance : CommSemiringWithMonus NatPair where
  mul_comm := mul_comm

instance : HasAltLinearOrder NatPair where
  altOrder := inferInstanceAs (LinearOrder (ℕ ×ₗ ℕ))

@[simp] theorem fst_delta (a : NatPair) :
    (SemiringWithMonus.delta a).fst = if a.fst = 0 then 0 else 1 := rfl
@[simp] theorem snd_delta (a : NatPair) :
    (SemiringWithMonus.delta a).snd = if a.snd = 0 then 0 else 1 := rfl

/-- **The two coordinates vanish together.** -/
def ZeroPat (a : NatPair) : Prop := a.fst = 0 ↔ a.snd = 0

end NatPair

variable {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-! ## Properties of annotations the operators keep, but for a difference -/

/-- **A property of annotations every operator but the difference keeps**:
`𝟘`, `𝟙`, sums, products, `δ`, and `𝟙 ⊖ a`. -/
structure AnnClosed (Q : K → Prop) : Prop where
  zero : Q 0
  one : Q 1
  add : ∀ a b, Q a → Q b → Q (a + b)
  mul : ∀ a b, Q a → Q b → Q (a * b)
  delta : ∀ a, Q a → Q (SemiringWithMonus.delta a)
  one_sub : ∀ a, Q a → Q (1 - a)

/-- **Equal zero patterns are kept by every operator but the difference.** -/
theorem NatPair.annClosed_zeroPat : AnnClosed NatPair.ZeroPat := by
  refine ⟨Iff.rfl, by simp [NatPair.ZeroPat], fun a b ha hb => ?_, fun a b ha hb => ?_,
    fun a ha => ?_, fun a ha => ?_⟩
  · unfold NatPair.ZeroPat at *
    simp only [NatPair.fst_add, NatPair.snd_add]
    omega
  · unfold NatPair.ZeroPat at *
    simp only [NatPair.fst_mul, NatPair.snd_mul, Nat.mul_eq_zero]
    tauto
  · unfold NatPair.ZeroPat at *
    simp only [NatPair.fst_delta, NatPair.snd_delta]
    by_cases h : a.fst = 0
    · rw [ite_eq_left h, ite_eq_left (ha.1 h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (ha.2 h'))]
  · unfold NatPair.ZeroPat at *
    simp only [NatPair.fst_sub, NatPair.snd_sub, NatPair.fst_one, NatPair.snd_one]
    omega

namespace AnnClosed

variable {Q : K → Prop} (hQ : AnnClosed Q)
include hQ

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem msum : ∀ s : Multiset K, (∀ a ∈ s, Q a) → Q s.sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; exact hQ.zero
  | cons a s ih =>
    intro h
    rw [Multiset.sum_cons]
    exact hQ.add _ _ (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem mprod : ∀ s : Multiset K, (∀ a ∈ s, Q a) → Q s.prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; exact hQ.one
  | cons a s ih =>
    intro h
    rw [Multiset.prod_cons]
    exact hQ.mul _ _ (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem lsum (l : List K) (h : ∀ a ∈ l, Q a) : Q l.sum := by
  rw [← Multiset.sum_coe]
  exact hQ.msum _ fun a ha => h a (Multiset.mem_coe.1 ha)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem fsum {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, Q (f i)) :
    Q (∑ i ∈ s, f i) := by
  unfold Finset.sum
  exact hQ.msum _ fun a ha => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 ha
    exact h i hi

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem fprod {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, Q (f i)) :
    Q (∏ i ∈ s, f i) := by
  unfold Finset.prod
  exact hQ.mprod _ fun a ha => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 ha
    exact h i hi

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem chi (op : CompOp) (a b : T) : Q (Having.chi op a b : K) := by
  unfold Having.chi; split_ifs; exacts [hQ.one, hQ.zero]

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem chiOf (P : T → Kleene) (a : T) : Q (Having.chiOf P a : K) := by
  unfold Having.chiOf; split_ifs; exacts [hQ.one, hQ.zero]

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem worldAnn {N : ℕ} (α : Fin N → K) (hα : ∀ i, Q (α i)) (W : Finset (Fin N)) :
    Q (Having.worldAnn α W) :=
  hQ.mul _ _ (hQ.fprod _ _ fun i _ => hα i)
    (hQ.one_sub _ (hQ.fsum _ _ fun i _ => hα i))

end AnnClosed

/-! ## The annotations a token carries -/

/-- Every occurrence of an aggregate value is annotated within `Q`. -/
def AggValue.AnnsIn (Q : K → Prop) (a : AggValue T K) : Prop := ∀ p ∈ a.occs, Q p.2

/-- Every occurrence of an aggregate expression is annotated within `Q`. -/
def AggExpr.AnnsIn (Q : K → Prop) (e : AggExpr T K) : Prop := ∀ p ∈ e.occs, Q p.2.1

/-- Every occurrence of a nested value, and every inner one, is annotated
within `Q`. -/
def NestedValue.AnnsIn (Q : K → Prop) (a : NestedValue T K) : Prop :=
  ∀ o ∈ a.occs, Q o.2 ∧ o.1.AnnsIn Q

/-- Every annotation a token carries is within `Q`. -/
def AggTok.AnnsIn (Q : K → Prop) : AggTok T K → Prop
  | .tok a => a.AnnsIn Q
  | .nest a => a.AnnsIn Q
  | .expr e => e.AnnsIn Q

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem AggTok.AnnsIn_setFam (Q : K → Prop) (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).AnnsIn Q ↔ x.AnnsIn Q := by
  cases x <;> exact Iff.rfl

section Tokens

variable {Q : K → Prop}

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggValue.AnnsIn.anns {a : AggValue T K} (h : a.AnnsIn Q) (i : Fin a.occs.length) :
    Q (a.anns i) := h _ (List.get_mem _ _)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggExpr.AnnsIn.anns {e : AggExpr T K} (h : e.AnnsIn Q) (i : Fin e.occs.length) :
    Q (e.anns i) := h _ (List.get_mem _ _)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggValue.annsIn_ofGroup {c m : ℕ} (f : SeqAggFunc T) (t : TermIn T c m)
    (U : List (AnnotatedTuple T K m)) (γ : Fin c → T) (hU : ∀ p ∈ U, Q p.2) :
    (AggValue.ofGroup f t U γ).AnnsIn Q := by
  intro p hp
  obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
  exact hU p' hp'

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggValue.annsIn_ofScalarGroup {c m : ℕ} (f : SeqAggFunc T) (t : TermIn T c m)
    (U : List (AnnotatedTuple T K m)) (γ : Fin c → T) (hU : ∀ p ∈ U, Q p.2) :
    (AggValue.ofScalarGroup f t U γ).AnnsIn Q :=
  AggValue.annsIn_ofGroup f t U γ hU

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem AggValue.annsIn_mergeOccs (hQ : AnnClosed Q) (l : List (T × K))
    (hl : ∀ p ∈ l, Q p.2) : ∀ p ∈ AggValue.mergeOccs l, Q p.2 := by
  intro p hp
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hp
  refine hQ.lsum _ fun a ha => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
  split_ifs
  · exact hl q hq
  · exact hQ.zero

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem AggValue.annsIn_mergeByValue (hQ : AnnClosed Q) {a : AggValue T K}
    (h : a.AnnsIn Q) : a.mergeByValue.AnnsIn Q :=
  AggValue.annsIn_mergeOccs hQ a.occs h

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggExpr.annsIn_ofSeqWhen {c m : ℕ} (f : SeqAggFunc T) (t : TermIn T c m)
    (keep : Tuple T m → Bool) (U : List (AnnotatedTuple T K m)) (sc : Bool) (γ : Fin c → T)
    (hU : ∀ p ∈ U, Q p.2) : (AggExpr.ofSeqWhen f t keep U sc γ).AnnsIn Q := by
  intro p hp
  obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
  exact hU p' hp'

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem AggExpr.annsIn_ofSeqDistWhen (hQ : AnnClosed Q) {c m : ℕ} (f : SeqAggFunc T)
    (t : TermIn T c m) (keep : Tuple T m → Bool) (U : List (AnnotatedTuple T K m)) (sc : Bool)
    (γ : Fin c → T) (hU : ∀ p ∈ U, Q p.2) : (AggExpr.ofSeqDistWhen f t keep U sc γ).AnnsIn Q := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
    refine AggValue.annsIn_mergeOccs hQ _ (fun q hq => ?_) z hz
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hq
    exact hU p' (List.mem_of_mem_filter hp')
  · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
    exact hU p' (List.mem_of_mem_filter hp')

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggExpr.annsIn_ofValue {a : AggValue T K} (h : a.AnnsIn Q) :
    (AggExpr.ofValue a).AnnsIn Q := by
  intro p hp
  obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
  exact h p' hp'

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenValue.annsIn_innerValue (x : GenValue T K)
    (h : ∀ a, x = Sum.inr a → a.AnnsIn Q) : (GenValue.innerValue x).AnnsIn Q := by
  rcases x with v | a
  · intro p hp; exact absurd hp (by simp [GenValue.innerValue, NestedValue.constInner,
      AggExpr.ofValue])
  · cases a with
    | tok a => exact AggExpr.annsIn_ofValue (h _ rfl)
    | nest a => intro p hp; exact absurd hp (by simp [GenValue.innerValue,
        NestedValue.constInner, AggExpr.ofValue])
    | expr e => exact h _ rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggTok.annsIn_postcomp (gf : T → T) {x : AggTok T K} (h : x.AnnsIn Q) :
    (x.postcomp gf).AnnsIn Q := by
  cases x with
  | tok a => exact h
  | nest a => exact h
  | expr e => exact h

/-! ### The predicate provenance -/

omit [HasAltLinearOrder K] in
theorem AggValue.annIn_predProvOfWith (hQ : AnnClosed Q) {a : AggValue T K}
    (h : a.AnnsIn Q) (P : T → Kleene) : Q (a.predProvOfWith P) := by
  unfold AggValue.predProvOfWith AggValue.predProvWith AggValue.predProvScalarWith
  split_ifs
  · exact hQ.fsum _ _ fun W _ => hQ.mul _ _ (hQ.worldAnn _ h.anns W) (hQ.chiOf P _)
  · exact hQ.fsum _ _ fun W _ => hQ.mul _ _ (hQ.worldAnn _ h.anns W) (hQ.chiOf P _)

omit [HasAltLinearOrder K] in
theorem AggExpr.annIn_predProvWith (hQ : AnnClosed Q) {e : AggExpr T K}
    (h : e.AnnsIn Q) (P : T → Kleene) : Q (e.predProvWith P) :=
  hQ.fsum _ _ fun W _ => hQ.mul _ _ (hQ.worldAnn _ h.anns W) (hQ.chiOf P _)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem NestedValue.annIn_predProvWith (hQ : AnnClosed Q) {a : NestedValue T K}
    (h : a.AnnsIn Q) (P : T → Kleene) : Q (a.predProvWith P) := by
  unfold NestedValue.predProvWith
  refine hQ.msum _ fun x hx => ?_
  obtain ⟨W, hW, rfl⟩ := Multiset.mem_map.1 hx
  have hWo : ∀ dd ∈ W.occs, Q dd.occ.2 ∧ dd.occ.1.AnnsIn Q := fun dd hdd => by
    have hW' := NestedValue.isWorldOf_of_mem_worlds (Multiset.mem_of_mem_filter hW)
    exact h dd.occ (hW' ▸ Multiset.mem_map_of_mem _ hdd)
  refine hQ.mul _ _ (hQ.mul _ _ (hQ.mul _ _ ?_ ?_) (hQ.one_sub _ (hQ.add _ _ ?_ ?_)))
    (hQ.chiOf P _)
  · refine hQ.mprod _ fun y hy => ?_
    obtain ⟨dd, hdd, rfl⟩ := Multiset.mem_map.1 hy
    split_ifs
    · exact (hWo dd hdd).1
    · exact hQ.one
  · refine hQ.mprod _ fun y hy => ?_
    obtain ⟨dd, hdd, rfl⟩ := Multiset.mem_map.1 hy
    exact hQ.fprod _ _ fun j _ => (hWo dd hdd).2.anns j
  · refine hQ.msum _ fun y hy => ?_
    obtain ⟨dd, hdd, rfl⟩ := Multiset.mem_map.1 hy
    split_ifs
    · exact hQ.zero
    · exact (hWo dd hdd).1
  · refine hQ.msum _ fun y hy => ?_
    obtain ⟨dd, hdd, rfl⟩ := Multiset.mem_map.1 hy
    exact hQ.fsum _ _ fun j _ => (hWo dd hdd).2.anns j

omit [HasAltLinearOrder K] in
theorem AggTok.annIn_predProvOfWith (hQ : AnnClosed Q) {x : AggTok T K} (h : x.AnnsIn Q)
    (P : T → Kleene) : Q (x.predProvOfWith P) := by
  cases x with
  | tok a => exact AggValue.annIn_predProvOfWith hQ h P
  | nest a => exact NestedValue.annIn_predProvWith hQ h P
  | expr e => exact AggExpr.annIn_predProvWith hQ h P

omit [HasAltLinearOrder K] in
/-- **A predicate's provenance is within `Q`** where every token it reads
carries annotations within `Q`. -/
theorem GenPredIn.annIn_predsem (hQ : AnnClosed Q) {c n : ℕ} {κ : Fin n → ColKind}
    (u : Tuple (GenValue T K) n) (γ : Fin c → T)
    (hu : ∀ k a, u k = Sum.inr a → a.AnnsIn Q) :
    ∀ (φ : GenPredIn T c κ) (neg : Bool), Q (φ.predsem neg u γ) := by
  intro φ
  induction φ with
  | cmp op t₁ t₂ => intro neg; exact hQ.chi _ _ _
  | aggCmp k hk op t =>
    intro neg
    show Q (match u k with
      | Sum.inl _ => 0
      | Sum.inr a => a.predProvOf (if neg then op.negate else op) (t.eval u γ))
    rcases hk' : u k with v | a
    · exact hQ.zero
    · exact AggTok.annIn_predProvOfWith hQ (hu k a hk') _
  | aggRange k hk op₁ t₁ op₂ t₂ =>
    intro neg
    show Q (match u k with
      | Sum.inl _ => 0
      | Sum.inr a => a.predProvOfWith _)
    rcases hk' : u k with v | a
    · exact hQ.zero
    · exact AggTok.annIn_predProvOfWith hQ (hu k a hk') _
  | and φ ψ ihφ ihψ =>
    intro neg
    show Q (if neg then _ else _)
    split_ifs
    · exact hQ.add _ _ (ihφ neg) (ihψ neg)
    · exact hQ.mul _ _ (ihφ neg) (ihψ neg)
  | or φ ψ ihφ ihψ =>
    intro neg
    show Q (if neg then _ else _)
    split_ifs
    · exact hQ.mul _ _ (ihφ neg) (ihψ neg)
    · exact hQ.add _ _ (ihφ neg) (ihψ neg)
  | not φ ih => intro neg; exact ih (!neg)

end Tokens

/-! ## Every annotation the evaluator builds -/

section Evaluate

variable {Q : K → Prop}

/-- **A row's annotations are within `Q`**: its concrete part, its pending
factors' occurrences, and every annotation the tokens it holds carry. -/
def GenRow.AnnIn (Q : K → Prop) {n : ℕ} (r : GenRow T K n) : Prop :=
  Q r.snd.base ∧ (∀ l ∈ r.snd.pending, ∀ x ∈ l, Q x)
    ∧ ∀ k a, r.fst k = Sum.inr a → a.AnnsIn Q

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenRow.AnnIn.finalize (hQ : AnnClosed Q) {n : ℕ} {r : GenRow T K n}
    (h : r.AnnIn Q) : Q r.snd.finalize :=
  hQ.mul _ _ h.1 (hQ.mprod _ fun a ha => by
    obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.1 ha
    exact hQ.delta _ (hQ.lsum _ (h.2.1 l hl)))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenRow.annIn_ofAnnotated {n : ℕ} {p : AnnotatedTuple T K n}
    (h : Q p.2) : (GenRow.ofAnnotated p).AnnIn Q :=
  ⟨h, fun l hl => absurd hl (Multiset.notMem_zero l), fun k a hk => by
    simp [GenRow.ofAnnotated] at hk⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- A projection column reads a token of the row, perhaps through a term. -/
theorem ProjColIn.annsIn_eval {c n : ℕ} {κ : Fin n → ColKind} (p : ProjColIn T c κ)
    {u : Tuple (GenValue T K) n} (γ : Fin c → T) (hu : ∀ k a, u k = Sum.inr a → a.AnnsIn Q)
    {a : AggTok T K} (h : p.eval u γ = Sum.inr a) : a.AnnsIn Q := by
  cases p with
  | term t => exact absurd h (by simp [ProjColIn.eval])
  | provTerm t => exact absurd h (by simp [ProjColIn.eval])
  | token k hk => exact hu k a h
  | aggTerm k hk gf =>
    have h' : Sum.map gf (AggTok.postcomp gf) (u k) = Sum.inr a := h
    rcases hv : u k with v | a₀
    · rw [hv] at h'; simp at h'
    · rw [hv] at h'
      simp only [Sum.map_inr, Sum.inr.injEq] at h'
      rw [← h']
      exact AggTok.annsIn_postcomp gf (hu k a₀ hv)
  | aggTermOf k hk t =>
    have h' : Sum.map t.unary (AggTok.postcomp t.unary) (u k) = Sum.inr a := h
    rcases hv : u k with v | a₀
    · rw [hv] at h'; simp at h'
    · rw [hv] at h'
      simp only [Sum.map_inr, Sum.inr.injEq] at h'
      rw [← h']
      exact AggTok.annsIn_postcomp _ (hu k a₀ hv)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- An occurrence of a frame is the row's own or one of the relation's. -/
theorem mem_frameListOf {α : Type} [LinearOrder α] {n m p : ℕ} (val : α → Tuple T n)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (X : Multiset α) (x y : α) (h : y ∈ ValueFrame.frameListOf val P O o w X x) :
    y = x ∨ y ∈ X := by
  have h1 : y ∈ sortList (ValueFrame.frameOf val P O w X x) :=
    (OrderSpec.sortSeq_perm _).mem_iff.1 h
  rw [mem_sortList] at h1
  unfold ValueFrame.frameOf at h1
  split_ifs at h1
  · rcases Multiset.mem_cons.1 h1 with rfl | h1
    · exact Or.inl rfl
    · exact Or.inr (Multiset.mem_of_mem_filter (Multiset.mem_of_mem_erase h1))
  · exact Or.inr (Multiset.mem_of_mem_filter (Multiset.mem_of_mem_erase h1))

omit [DecidableEq K] in
theorem annsIn_tokenOfDist (hQ : AnnClosed Q) {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (dist : Bool) (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n)
    (γ : Fin c → T) (hX : ∀ q ∈ X, Q q.2) (hx : Q x.2) :
    (ValueFrame.tokenOfDist P O o w t f dist X x γ).AnnsIn Q := by
  have hU : ∀ q ∈ ValueFrame.frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X x,
      Q q.2 := fun q hq => by
    rcases mem_frameListOf _ P O o w X x q hq with rfl | hq
    · exact hx
    · exact hX q hq
  have htok : (ValueFrame.tokenOf P O o w t f X x γ).AnnsIn Q := by
    unfold ValueFrame.tokenOf
    split_ifs
    · exact AggValue.annsIn_ofGroup f t _ γ hU
    · exact AggValue.annsIn_ofScalarGroup f t _ γ hU
  unfold ValueFrame.tokenOfDist
  split_ifs
  · exact AggValue.annsIn_mergeByValue hQ htok
  · exact htok

omit [DecidableEq K] in
theorem annsIn_exprWhenOf (hQ : AnnClosed Q) {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (dist : Bool) (keep : Tuple T n → Bool) (X : AnnotatedRelation T K n)
    (x : AnnotatedTuple T K n) (γ : Fin c → T) (hX : ∀ q ∈ X, Q q.2) (hx : Q x.2) :
    (ValueFrame.exprWhenOf P O o w t f dist keep X x γ).AnnsIn Q := by
  have hU : ∀ q ∈ ValueFrame.frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X x,
      Q q.2 := fun q hq => by
    rcases mem_frameListOf _ P O o w X x q hq with rfl | hq
    · exact hx
    · exact hX q hq
  unfold ValueFrame.exprWhenOf
  split_ifs
  · exact AggExpr.annsIn_ofSeqDistWhen hQ f t keep _ _ γ hU
  · exact AggExpr.annsIn_ofSeqWhen f t keep _ _ γ hU

/-- **Every annotation a query without a difference builds is within any
`Q` the other operators keep**, as soon as the instance's annotations,
the context's tokens and the rounds the holes are bound to are. -/
theorem annIn_evaluate (hQ : AnnClosed Q) {d : AnnotatedDatabase T K} {S : Set OpKind}
    (hS : OpKind.diff ∉ S) {Θ : Set (SeqAggFunc T)}
    (hD : ∀ k t (r : AnnotatedRelation T K k), d.find k t = some r → ∀ a ∈ r, Q a.2) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.inSig Θ → q.noExplode →
      ∀ (γ : Fin c → T) (E : EvalEnv T K),
      (∀ k a, E.ctxAt c γ k = Sum.inr a → a.AnnsIn Q) →
      (∀ p ∈ l, ∀ r ∈ E.holes p.1 p.2, r.AnnIn Q) →
      ∀ r ∈ q.evaluate d γ E, r.AnnIn Q := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ _ _ γ E _ _ r hr
    revert hr
    simp only [AggQueryIn.evaluate]
    cases hf : d.find n s with
    | none => intro hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      intro hr
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hr
      exact GenRow.annIn_ofAnnotated (hD n s rn hf a ha)
  | Hole n s κ =>
    intro _ _ _ γ E _ hH r hr
    exact hH (s, n) (List.mem_singleton_self _) r (Multiset.mem_of_mem_filter hr)
  | Param pv ρ =>
    intro _ _ _ γ E hctx _ r hr
    simp only [AggQueryIn.evaluate, EvalEnv.paramRows] at hr
    split at hr
    · rw [Multiset.mem_singleton] at hr
      subst hr
      refine ⟨hQ.one, fun l hl => absurd hl (Multiset.notMem_zero l), fun k a hk => ?_⟩
      revert hk
      show _root_.Sum.elim Sum.inl (E.ctxAt _ γ) (pv k) = Sum.inr a → a.AnnsIn Q
      cases pv k with
      | inl v => intro hk; simp at hk
      | inr j => intro hk; exact hctx j a hk
    · exact absurd hr (Multiset.notMem_zero r)
  | Empty => intro _ _ _ _ _ _ _ r hr; exact absurd hr (Multiset.notMem_zero r)
  | Proj ps q ih =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hr
    obtain ⟨hb, hp, ht⟩ := ih hu.2 hi.2 hx γ E hctx hH r₀ hr₀
    refine ⟨hQ.mul _ _ hb (hQ.mprod _ fun a ha => ?_), fun l hl x hxl => ?_,
      fun j a hj => ProjColIn.annsIn_eval (ps j) γ ht hj⟩
    · obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.1 ha
      exact hQ.delta _ (hQ.lsum _ (hp l (Multiset.mem_of_le tsub_le_self hl)))
    · exact hp l (Multiset.mem_of_le Multiset.inter_le_left hl) x hxl
  | Sel φ q hφ ih =>
    intro hu hi hx γ E hctx hH r hr
    have ih' := ih hu.2 hi.2 hx γ E hctx hH
    dsimp only [AggQueryIn.evaluate] at hr
    by_cases hagg : φ.hasAggAtom = true
    · rw [ite_eq_left hagg] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hr
      obtain ⟨hb, hp, ht⟩ := ih' r₀ hr₀
      refine ⟨hQ.mul _ _ hb (GenPredIn.annIn_predsem hQ r₀.fst γ ht φ false),
        fun l hl x hxl => ?_, ht⟩
      dsimp only at hl
      split_ifs at hl
      · exact hp l (Multiset.mem_of_mem_filter hl) x hxl
      · exact hp l hl x hxl
    · rw [ite_eq_right hagg] at hr
      exact ih' r (Multiset.mem_of_mem_filter hr)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Multiset.mem_map.1 hr
    obtain ⟨hxm, hym⟩ := Multiset.mem_product.1 hxy
    obtain ⟨bx, px, tx⟩ := ih₁ hu.2.1 hi.1 hx.1 γ E hctx
      (fun p hp => hH p (List.mem_append_left _ hp)) x hxm
    obtain ⟨b_y, py, ty⟩ := ih₂ hu.2.2 hi.2 hx.2 γ E hctx
      (fun p hp => hH p (List.mem_append_right _ hp)) y hym
    refine ⟨hQ.mul _ _ bx b_y, fun l hl => ?_, fun k a hk => ?_⟩
    · rcases Multiset.mem_add.1 hl with hl | hl
      · exact px l hl
      · exact py l hl
    · refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
      · simp only [Fin.append_left] at hk; exact tx i a hk
      · simp only [Fin.append_right] at hk; exact ty i a hk
  | Apply q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l'
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hxm, hr⟩ := Multiset.mem_bind.1 hr
    obtain ⟨y, hym, rfl⟩ := Multiset.mem_map.1 hr
    obtain ⟨bx, px, tx⟩ := ih₁ hu.2.1 hi.1 hx.1 γ E hctx hH x hxm
    obtain ⟨b_y, py, ty⟩ := ih₂ hu.2.2 hi.2 hx.2 _ _ (fun k a hk => by
      rw [EvalEnv.ctxAt_withCtx] at hk
      revert hk
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]; exact tx i a
      · rw [Fin.append_right]; exact hctx i a) (fun p hp => absurd hp List.not_mem_nil) y hym
    refine ⟨hQ.mul _ _ bx b_y, fun l hl => ?_, fun k a hk => ?_⟩
    · rcases Multiset.mem_add.1 hl with hl | hl
      · exact px l hl
      · exact py l hl
    · refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
      · simp only [Fin.append_left] at hk; exact tx i a hk
      · simp only [Fin.append_right] at hk; exact ty i a hk
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    rcases Multiset.mem_add.1 hr with hr | hr
    · exact ih₁ hu.2.1 hi.1 hx.1 γ E hctx (fun p hp => hH p (List.mem_append_left _ hp)) r hr
    · exact ih₂ hu.2.2 hi.2 hx.2 γ E hctx (fun p hp => hH p (List.mem_append_right _ hp)) r hr
  | Dedup q ih =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hr
    rw [groupByKey_eq_dedup_map] at hp
    obtain ⟨u, -, rfl⟩ := Multiset.mem_map.1 hp
    refine GenRow.annIn_ofAnnotated (hQ.msum _ fun a ha => ?_)
    obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_mem_filter hp')
    exact (ih hu.2 hi hx γ E hctx hH r₀ hr₀).finalize hQ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hu => absurd hu.1 hS
  | Explode k hk q ih => exact fun _ _ hx => hx.elim
  | Retag hk q ih =>
    intro hu hi hx γ E hctx hH r hr
    exact ih hu hi hx γ E hctx hH r hr
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    refine forall_mem_muSumFix (P := GenRow.AnnIn Q) (fun X hX y hy => ?_)
      (ih₀ hu.2.1 hi.1 hx.1 γ E hctx (fun p hp => absurd hp List.not_mem_nil)) r hr
    refine ih₁ hu.2.2 hi.2 hx.2 γ _ (by simpa only [EvalEnv.ctxAt_assignHole] using hctx)
      (fun p hp r' hr' => ?_) y hy
    obtain rfl := List.mem_singleton.1 hp
    dsimp only at hr'
    rw [EvalEnv.assignHole_holes_self] at hr'
    exact hX r' hr'
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' n'
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    set step := fun X : Multiset (AnnotatedTuple T K n') =>
      AnnotatedRelation.dedupAnn (((q₀.evaluate d γ E).map GenRow.toAnnotated)
        + ((q₁.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))).map
            GenRow.toAnnotated)) with hstep
    have hit : ∀ k, ∀ p ∈ muIter step k, Q p.2 := by
      intro k
      induction k with
      | zero => intro p hp; exact absurd hp (Multiset.notMem_zero p)
      | succ k ihk =>
        intro p hp
        simp only [muIter, hstep] at hp
        rw [AggQueryIn.dedupAnn_eq_dedupK] at hp
        obtain ⟨u, -, rfl⟩ := Multiset.mem_map.1 hp
        refine hQ.msum _ fun a ha => ?_
        obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.1 ha
        rcases Multiset.mem_add.1 (Multiset.mem_of_mem_filter hp') with hp' | hp'
        · obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp'
          exact (ih₀ hu.2.1 hi.1 hx.1 γ E hctx (fun p hp => absurd hp List.not_mem_nil)
            r₀ hr₀).finalize hQ
        · obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp'
          refine (ih₁ hu.2.2 hi.2 hx.2 γ _
            (by simpa only [EvalEnv.ctxAt_assignHole] using hctx) (fun p hp r' hr' => ?_)
            r₀ hr₀).finalize hQ
          obtain rfl := List.mem_singleton.1 hp
          dsimp only at hr'
          rw [EvalEnv.assignHole_holes_self] at hr'
          obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hr'
          exact GenRow.annIn_ofAnnotated (ihk a ha)
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hr
    exact GenRow.annIn_ofAnnotated (hit _ p hp)
  | Gamma is ts fs q keep ord ih =>
    rename_i c' m n₁ n₂ _
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, hkv, rfl⟩ := Multiset.mem_map.1 hr
    set R := (q.evaluate d γ E).map GenRow.toAnnotated with hR
    have hRb : ∀ p ∈ R, Q p.2 := by
      intro p hp
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp
      exact (ih hu.2 hi.2.2.2 hx γ E hctx hH r₀ hr₀).finalize hQ
    have hU : ∀ x ∈ Having.havingGroupOrd is ord R kv.1, Q x.2 := by
      intro x hx'
      rw [Having.mem_havingGroupOrd, ← Multiset.mem_coe, Having.havingGroup_coe] at hx'
      exact hRb x (Multiset.mem_of_mem_filter hx')
    refine ⟨hQ.one, fun l hl => ?_, fun k a hk => ?_⟩
    · rw [Multiset.mem_singleton] at hl
      subst hl
      intro x hx'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx'
      exact hU y hy
    · refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
      · simp only [Fin.append_left] at hk; simp at hk
      · simp only [Fin.append_right, Sum.inr.injEq] at hk
        subst hk
        rw [AggTok.AnnsIn_setFam]
        split
        · exact AggValue.annsIn_ofGroup _ _ _ γ hU
        · exact AggExpr.annsIn_ofSeqWhen _ _ _ _ _ γ hU
  | GammaScalar ts fs q ord ih =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hr
    subst hr
    refine ⟨hQ.one, fun l hl => absurd hl (Multiset.notMem_zero l), fun k a hk => ?_⟩
    simp only [Sum.inr.injEq] at hk
    subst hk
    rw [AggTok.AnnsIn_setFam]
    refine AggValue.annsIn_ofScalarGroup _ _ _ γ fun x hx' => ?_
    rw [Having.mem_havingGroupOrd, ← Multiset.mem_coe, Having.havingGroup_coe] at hx'
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_mem_filter hx')
    exact (ih hu.2 hi.2.2 hx γ E hctx hH r₀ hr₀).finalize hQ
  | GammaNest is his p g q ih =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨gk, -, rfl⟩ := Multiset.mem_map.1 hr
    have hb := ih hu.2 hi.2.2 hx γ E hctx hH
    have hocc : ∀ o ∈ ((q.evaluate d γ E).filter (fun row =>
        (fun k => AggValue.collapseSum (row.fst (is k))) = gk)).map
          (fun row => (GenValue.innerValue (p.eval row.fst γ), row.snd.finalize)),
        Q o.2 ∧ o.1.AnnsIn Q := by
      intro o ho
      obtain ⟨row, hrow, rfl⟩ := Multiset.mem_map.1 ho
      have hrow' := hb row (Multiset.mem_of_mem_filter hrow)
      exact ⟨hrow'.finalize hQ, GenValue.annsIn_innerValue _ fun a ha =>
        ProjColIn.annsIn_eval p γ hrow'.2.2 ha⟩
    refine ⟨hQ.one, fun l hl => ?_, fun k a hk => ?_⟩
    · rw [Multiset.mem_singleton] at hl
      subst hl
      intro x hx'
      rw [List.mem_singleton] at hx'
      subst hx'
      refine hQ.msum _ fun y hy => ?_
      obtain ⟨o, ho, rfl⟩ := Multiset.mem_map.1 hy
      exact (hocc o ho).1
    · refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
      · simp only [Fin.append_left] at hk; simp at hk
      · simp only [Fin.append_right, Sum.inr.injEq] at hk
        subst hk
        exact hocc
  | ProvSum is his t q ih => exact fun hu => hu.elim
  | GammaTok is his ts fs a q keep ih => exact fun hu => hu.elim
  | Win P O o w t g q hrr dist keep ih =>
    rename_i c' n' m' p' κ' _
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hxm, rfl⟩ := Multiset.mem_map.1 hr
    have hb := ih hu.2 hi.2.2.2 hx γ E hctx hH
    have hX : ∀ y ∈ (q.evaluate d γ E).map (GenRow.readAnnotated κ'), Q y.2 := by
      intro y hy
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hy
      exact (hb r₀ hr₀).finalize hQ
    obtain ⟨bx, px, tx⟩ := hb x hxm
    refine ⟨bx, px, fun k a hk => ?_⟩
    simp only [ValueFrame.windowGenRow] at hk
    refine Fin.lastCases (fun hk => ?_) (fun i hk => ?_) k hk
    · rw [Fin.snoc_last, Sum.inr.injEq] at hk
      subst hk
      rw [AggTok.AnnsIn_setFam]
      split
      · exact annsIn_tokenOfDist hQ P O o w t g dist _ _ γ hX ((hb x hxm).finalize hQ)
      · exact annsIn_exprWhenOf hQ P O o w t g dist _ _ _ γ hX ((hb x hxm).finalize hQ)
    · rw [Fin.snoc_castSucc] at hk; exact tx i a hk
  | WinExpr P O o ws ts fs g q keeps ih => exact fun _ hi => hi.elim

end Evaluate

/-! ## The witness -/

/-- The schema of two unary relations, `R` and `S`. -/
def schemaRS : Schema :=
  Schema.ofFn (fun s => if s = "R" ∨ s = "S" then some 1 else none) {"R", "S"}
    (fun s hs => by
      by_contra hne
      exact hs (ite_eq_right fun h => hne (by rcases h with rfl | rfl <;> simp)))

/-- **`R − S`.** -/
def diffWitness : AggQuery ℕ 1 (ColKind.allReg 1) :=
  AggQueryIn.Diff (AggQueryIn.Rel 1 "R") (AggQueryIn.Rel 1 "S")

/-- **The instance it tells apart from every query without a difference**:
`R` holds `0` annotated `(1, 3)`, and `S` holds it twice, annotated
`(1, 1)`. -/
def dDiff : AnnotatedDatabase ℕ NatPair :=
  AnnotatedDatabase.assign "R"
    (({(((fun _ => 0) : Tuple ℕ 1), NatPair.mk 1 3)}
      : Multiset (AnnotatedTuple ℕ NatPair 1)) : AnnotatedRelation ℕ NatPair 1)
    (AnnotatedDatabase.assign "S"
      (({(((fun _ => 0) : Tuple ℕ 1), NatPair.mk 1 1),
          (((fun _ => 0) : Tuple ℕ 1), NatPair.mk 1 1)}
        : Multiset (AnnotatedTuple ℕ NatPair 1)) : AnnotatedRelation ℕ NatPair 1) [])

theorem dDiff_zeroPat : ∀ k t (r : AnnotatedRelation ℕ NatPair k), dDiff.find k t = some r →
    ∀ a ∈ r, NatPair.ZeroPat a.2 := by
  intro k t r hr a ha
  unfold dDiff at hr
  by_cases h₁ : k = 1 ∧ t = "R"
  · obtain ⟨rfl, rfl⟩ := h₁
    rw [AnnotatedDatabase.find_assign, Option.some.injEq] at hr
    subst hr
    rw [Multiset.mem_singleton] at ha
    subst ha
    show NatPair.ZeroPat (NatPair.mk 1 3)
    simp [NatPair.ZeroPat]
  · rw [AnnotatedDatabase.find_assign_of_ne _ _ _ _ h₁] at hr
    by_cases h₂ : k = 1 ∧ t = "S"
    · obtain ⟨rfl, rfl⟩ := h₂
      rw [AnnotatedDatabase.find_assign, Option.some.injEq] at hr
      subst hr
      have : a.2 = NatPair.mk 1 1 := by
        rcases Multiset.mem_cons.1 ha with rfl | ha
        · rfl
        · rw [Multiset.mem_singleton] at ha; subst ha; rfl
      rw [this]
      simp [NatPair.ZeroPat]
    · rw [AnnotatedDatabase.find_assign_of_ne _ _ _ _ h₂] at hr
      exact absurd hr (by
        rw [show AnnotatedDatabase.find k t ([] : AnnotatedDatabase ℕ NatPair) = none from rfl]
        simp)

/-- **`R − S` there**: `(1, 3) ⊖ (2, 2) = (0, 1)`. -/
theorem evaluateAnnotated_diffWitness :
    diffWitness.evaluateAnnotated dDiff (fun _ => 0)
      = ({(((fun _ => 0) : Tuple ℕ 1), NatPair.mk 0 1)}
        : Multiset (AnnotatedTuple ℕ NatPair 1)) := by
  show diffWitness.ann dDiff (fun _ => 0) {} = _
  rw [diffWitness, AggQueryIn.ann_diff, AggQueryIn.ann_Rel, AggQueryIn.ann_Rel, dDiff,
    AnnotatedDatabase.find_assign,
    AnnotatedDatabase.find_assign_of_ne _ _ _ _ (by decide), AnnotatedDatabase.find_assign]
  simp only [Multiset.map_singleton]
  congr 1

theorem overSchema_diffWitness : diffWitness.overSchema schemaRS := by
  simp [diffWitness, AggQueryIn.overSchema, schemaRS]

theorem usesOnly_diffWitness : diffWitness.usesOnly plainRecOps :=
  ⟨by simp [plainRecOps, plainOps, basisDD, basisOps], trivial, trivial⟩

/-- **`−` is in every set generating the annotated algebra over `ℕ × ℕ`**:
without a difference, every annotation of a query's result is zero in one
coordinate exactly where it is in the other, and `R − S` gives `(0, 1)` on
`dDiff`. -/
theorem diff_mem_of_generatesAnn {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnn ℕ NatPair schemaRS cnt S) : OpKind.diff ∈ S := by
  by_contra hS
  obtain ⟨q', -, hu', hi', ha', -, hm⟩ := h diffWitness overSchema_diffWitness
    usesOnly_diffWitness ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
  obtain ⟨-, he⟩ := hm dDiff (fun _ => 0) ⟨trivial, trivial⟩
  have hmem : ((((fun _ => 0) : Tuple ℕ 1), NatPair.mk 0 1) : AnnotatedTuple ℕ NatPair 1)
      ∈ q'.evaluateAnnotated dDiff (fun _ => 0) := by
    rw [he, evaluateAnnotated_diffWitness]
    exact Multiset.mem_singleton_self _
  obtain ⟨r, hr, hre⟩ := Multiset.mem_map.1 hmem
  have hz := (annIn_evaluate NatPair.annClosed_zeroPat hS dDiff_zeroPat q' hu' hi' ha'
    (fun _ => 0) {} (fun k => k.elim0) (fun p hp => absurd hp List.not_mem_nil)
    r hr).finalize NatPair.annClosed_zeroPat
  have hfin : r.snd.finalize = NatPair.mk 0 1 := congrArg Prod.snd hre
  rw [hfin] at hz
  exact absurd hz (by simp [NatPair.ZeroPat])
