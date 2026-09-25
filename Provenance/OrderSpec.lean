/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Frame
import Provenance.Util.ValueTypeNull

/-!
# Order specifications, and the frames they determine

A window's `ORDER BY` does not order rows by the domain's own order. It
names, for each order column, a *direction* and a *null placement*, and
those two together give a total preorder on the order values: `ASC` or
`DESC` on the values of the domain, `NULLS FIRST` or `NULLS LAST` on the
nulls, which the domain's order knows nothing about. Rows that the preorder
does not separate are SQL's *peers*.

That preorder is what SQL's value-determined frames are defined from, and
it is the reason they need a specification at all: `RANGE BETWEEN UNBOUNDED
PRECEDING AND CURRENT ROW` is *the peers of the current row and everything
sorted before them*, and which rows those are is a question about the
clause, not about the domain.

This file gives the specification (`OrderCol`, `OrderSpec`), proves that it
is a total preorder (`OrderSpec.le_refl`, `le_trans`, `le_total`), and
builds from it the frames of SQL that a preorder determines:
`ValueFrame.rangeUpTo`, `rangeBefore`, `peerGroup`, and the `EXCLUDE`
modifiers `excludeGroup` and `excludeTies`. Each is classified by whether it
contains its current row exactly when it contains its peers
(`ValueFrame.ContainsSelf`), which is what decides whether a window over it
can be read off the relation or needs the occurrences told apart.

What an order specification does *not* do here is fix the sequence a frame
is read in: `ValueFrame.frameSeq` sorts a frame by the canonical order on
annotated tuples, not by the clause. That is harmless exactly where the
aggregate is symmetric (`SeqAggFunc.Symmetric`), which `SUM`, `COUNT`, `MIN`
and `MAX` are and `PICKFIRST` is not – `ValueFrame.windowValue_of_perm` says
any listing of the frame then gives the window's value. Making the sequence
the clause's, which is what an order-dependent aggregate needs, is a
separate change to the operator.
-/

variable {T : Type} {p : ℕ}

/-! ## One order column -/

/-- One column of an `ORDER BY`: which way the column reads, and where its
nulls go. -/
structure OrderCol where
  /-- `DESC`: the domain's order on the non-null values, reversed. -/
  desc : Bool := false
  /-- `NULLS FIRST`: every null sorts before every value of the domain. -/
  nullsFirst : Bool := false
deriving DecidableEq, Repr

namespace OrderCol

/-- `ASC` with SQL's default null placement: a null sorts after every value
of the domain. -/
def ASC : OrderCol := { desc := false, nullsFirst := false }

/-- `DESC` with SQL's default null placement: reversing the direction
reverses where the nulls go too, so a null sorts before every value. -/
def DESC : OrderCol := { desc := true, nullsFirst := true }

variable [ValueType T]

/-- Whether `a` sorts no later than `b` in this column. The nulls are placed
by the specification and compare equal to each other, which is SQL: two
nulls are peers in an `ORDER BY`, however the clause places them. -/
def le (c : OrderCol) (a b : T) : Bool :=
  if ValueType.isNull a then
    (if ValueType.isNull b then true else c.nullsFirst)
  else if ValueType.isNull b then !c.nullsFirst
  else if c.desc then decide (b ≤ a) else decide (a ≤ b)

/-- Two values are *peers* in a column when neither sorts before the other. -/
def peer (c : OrderCol) (a b : T) : Bool := c.le a b && c.le b a

@[simp] theorem le_rfl (c : OrderCol) (a : T) : c.le a a = true := by
  unfold le
  by_cases ha : ValueType.isNull a = true <;> simp [ha]

theorem le_total (c : OrderCol) (a b : T) :
    c.le a b = true ∨ c.le b a = true := by
  unfold le
  cases ha : ValueType.isNull a <;> cases hb : ValueType.isNull b <;> simp
  cases hd : c.desc <;> simp <;> exact _root_.le_total _ _

theorem le_trans (c : OrderCol) {a b d : T}
    (h₁ : c.le a b = true) (h₂ : c.le b d = true) : c.le a d = true := by
  unfold le at h₁ h₂ ⊢
  cases ha : ValueType.isNull a <;> cases hb : ValueType.isNull b <;>
    cases hd : ValueType.isNull d <;> simp_all
  cases hdesc : c.desc <;> simp_all <;>
    first
      | exact _root_.le_trans h₂ h₁
      | exact _root_.le_trans h₁ h₂

@[simp] theorem peer_rfl (c : OrderCol) (a : T) : c.peer a a = true := by
  simp [peer]

theorem peer_comm (c : OrderCol) (a b : T) : c.peer a b = c.peer b a := by
  simp [peer, Bool.and_comm]

theorem peer_trans (c : OrderCol) {a b d : T} (h₁ : c.peer a b = true)
    (h₂ : c.peer b d = true) : c.peer a d = true := by
  simp only [peer, Bool.and_eq_true] at h₁ h₂ ⊢
  exact ⟨c.le_trans h₁.1 h₂.1, c.le_trans h₂.2 h₁.2⟩

/-- **Peers are interchangeable**: replacing a value by a peer of it changes
no comparison. This is what makes the lexicographic reading below well
behaved, and it holds because the column is a total preorder. -/
theorem le_congr_left (c : OrderCol) {a b : T} (h : c.peer a b = true)
    (d : T) : c.le a d = c.le b d := by
  simp only [peer, Bool.and_eq_true] at h
  rw [Bool.eq_iff_iff]
  exact ⟨fun hd => c.le_trans h.2 hd, fun hd => c.le_trans h.1 hd⟩

theorem le_congr_right (c : OrderCol) {a b : T} (h : c.peer a b = true)
    (d : T) : c.le d a = c.le d b := by
  simp only [peer, Bool.and_eq_true] at h
  rw [Bool.eq_iff_iff]
  exact ⟨fun hd => c.le_trans hd h.1, fun hd => c.le_trans hd h.2⟩

/-! ### Where the nulls go -/

/-- **Two nulls are peers**, whatever the clause says: an `ORDER BY` places
the nulls as a block, it does not order them among themselves. -/
theorem peer_of_isNull (c : OrderCol) {a b : T}
    (ha : ValueType.isNull a = true) (hb : ValueType.isNull b = true) :
    c.peer a b = true := by
  simp [peer, le, ha, hb]

/-- **A null and a value of the domain are never peers**: the clause places
every null strictly on one side of every value. -/
theorem not_peer_isNull (c : OrderCol) {a b : T}
    (ha : ValueType.isNull a = true) (hb : ValueType.isNull b = false) :
    c.peer a b = false := by
  cases hn : c.nullsFirst <;> simp [peer, le, ha, hb, hn]

/-- `NULLS FIRST`: every null sorts before everything. -/
theorem le_of_nullsFirst (c : OrderCol) (hc : c.nullsFirst = true) {a : T}
    (ha : ValueType.isNull a = true) (b : T) : c.le a b = true := by
  cases hb : ValueType.isNull b <;> simp [le, ha, hb, hc]

/-- `NULLS LAST`: everything sorts before every null. -/
theorem le_of_nullsLast (c : OrderCol) (hc : c.nullsFirst = false) {b : T}
    (hb : ValueType.isNull b = true) (a : T) : c.le a b = true := by
  cases ha : ValueType.isNull a <;> simp [le, ha, hb, hc]


/-! ### Where nothing is null -/

/-- Where nothing is null, `ASC` is the domain's order. -/
@[simp] theorem ASC_le [NoNulls T] (a b : T) :
    (ASC.le a b) = decide (a ≤ b) := by
  simp [le, ASC, isNull_eq_false]

/-- Where nothing is null, `DESC` is the domain's order reversed. -/
@[simp] theorem DESC_le [NoNulls T] (a b : T) :
    (DESC.le a b) = decide (b ≤ a) := by
  simp [le, DESC, isNull_eq_false]

end OrderCol

/-! ## The clause -/

/-- An `ORDER BY` clause over `p` order columns: a direction and a null
placement for each. -/
abbrev OrderSpec (p : ℕ) := Fin p → OrderCol

namespace OrderSpec

/-- Every column `ASC`, with SQL's default null placement. -/
def asc (p : ℕ) : OrderSpec p := fun _ => OrderCol.ASC

/-- Every column `DESC`, with SQL's default null placement. -/
def desc (p : ℕ) : OrderSpec p := fun _ => OrderCol.DESC

variable [ValueType T]

/-- Lexicographic comparison down a list of columns: the first column whose
values are not peers decides, and tuples that are peers in every column of
the list compare as equal. -/
def leOn (o : OrderSpec p) : List (Fin p) → Tuple T p → Tuple T p → Bool
  | [], _, _ => true
  | k :: ks, x, y =>
      if (o k).peer (x k) (y k) then leOn o ks x y else (o k).le (x k) (y k)

/-- Whether `x` sorts no later than `y` under the clause: lexicographically,
the columns read in the order the clause names them. -/
def le (o : OrderSpec p) (x y : Tuple T p) : Bool :=
  o.leOn (List.finRange p) x y

/-- Two order values are *peers* when neither sorts before the other. SQL's
frames are defined against the peer group, not against the row: `CURRENT
ROW` in a `RANGE` frame means *the current row's peers*. -/
def peer (o : OrderSpec p) (x y : Tuple T p) : Bool := o.le x y && o.le y x

/-- `x` sorts strictly before `y`: `y` is not at or before `x`. -/
def lt (o : OrderSpec p) (x y : Tuple T p) : Bool := !o.le y x

/-! ### The clause is a total preorder -/

@[simp] theorem leOn_rfl (o : OrderSpec p) (l : List (Fin p))
    (x : Tuple T p) : o.leOn l x x = true := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [leOn, ih]

theorem leOn_total (o : OrderSpec p) (l : List (Fin p)) (x y : Tuple T p) :
    o.leOn l x y = true ∨ o.leOn l y x = true := by
  induction l with
  | nil => exact Or.inl rfl
  | cons k ks ih =>
    unfold leOn
    by_cases h : (o k).peer (x k) (y k) = true
    · rw [ite_eq_left h, ite_eq_left (by rw [OrderCol.peer_comm] at h; exact h)]
      exact ih
    · rw [ite_eq_right h, ite_eq_right (by rw [OrderCol.peer_comm]; exact h)]
      exact (o k).le_total (x k) (y k)

theorem leOn_trans (o : OrderSpec p) (l : List (Fin p)) {x y z : Tuple T p}
    (h₁ : o.leOn l x y = true) (h₂ : o.leOn l y z = true) :
    o.leOn l x z = true := by
  induction l with
  | nil => rfl
  | cons k ks ih =>
    unfold leOn at h₁ h₂ ⊢
    by_cases hxy : (o k).peer (x k) (y k) = true
    · by_cases hyz : (o k).peer (y k) (z k) = true
      · rw [ite_eq_left (OrderCol.peer_trans _ hxy hyz)]
        exact ih (by rwa [ite_eq_left hxy] at h₁) (by rwa [ite_eq_left hyz] at h₂)
      · have hxz : (o k).peer (x k) (z k) = true → False := by
          intro h
          exact hyz (OrderCol.peer_trans _
            (by rw [OrderCol.peer_comm]; exact hxy) h)
        rw [ite_eq_right (fun h => hxz h), OrderCol.le_congr_left _ hxy (z k)]
        rwa [ite_eq_right hyz] at h₂
    · have hle : (o k).le (x k) (y k) = true := by rwa [ite_eq_right hxy] at h₁
      by_cases hyz : (o k).peer (y k) (z k) = true
      · have hxz : (o k).peer (x k) (z k) = true → False := by
          intro h
          exact hxy (OrderCol.peer_trans _ h
            (by rw [OrderCol.peer_comm]; exact hyz))
        rw [ite_eq_right (fun h => hxz h), ← OrderCol.le_congr_right _ hyz (x k)]
        exact hle
      · have hle' : (o k).le (y k) (z k) = true := by rwa [ite_eq_right hyz] at h₂
        have hxz : (o k).peer (x k) (z k) = true → False := by
          intro h
          simp only [OrderCol.peer, Bool.and_eq_true] at h
          exact hxy (by
            simp only [OrderCol.peer, Bool.and_eq_true]
            exact ⟨hle, (o k).le_trans hle' h.2⟩)
        rw [ite_eq_right (fun h => hxz h)]
        exact (o k).le_trans hle hle'

@[simp] theorem le_rfl (o : OrderSpec p) (x : Tuple T p) : o.le x x = true :=
  leOn_rfl o _ x

theorem le_total (o : OrderSpec p) (x y : Tuple T p) :
    o.le x y = true ∨ o.le y x = true := leOn_total o _ x y

theorem le_trans (o : OrderSpec p) {x y z : Tuple T p}
    (h₁ : o.le x y = true) (h₂ : o.le y z = true) : o.le x z = true :=
  leOn_trans o _ h₁ h₂

@[simp] theorem peer_rfl (o : OrderSpec p) (x : Tuple T p) :
    o.peer x x = true := by simp [peer]

theorem peer_comm (o : OrderSpec p) (x y : Tuple T p) :
    o.peer x y = o.peer y x := by simp [peer, Bool.and_comm]

theorem peer_trans (o : OrderSpec p) {x y z : Tuple T p}
    (h₁ : o.peer x y = true) (h₂ : o.peer y z = true) : o.peer x z = true := by
  simp only [peer, Bool.and_eq_true] at h₁ h₂ ⊢
  exact ⟨o.le_trans h₁.1 h₂.1, o.le_trans h₂.2 h₁.2⟩

/-- Equal order values are peers – the converse fails, which is the whole
point of a peer group. -/
theorem peer_of_eq (o : OrderSpec p) {x y : Tuple T p} (h : x = y) :
    o.peer x y = true := by subst h; simp

@[simp] theorem lt_irrefl (o : OrderSpec p) (x : Tuple T p) :
    o.lt x x = false := by simp [lt]

theorem lt_iff (o : OrderSpec p) (x y : Tuple T p) :
    o.lt x y = true ↔ o.le y x = false := by simp [lt]

/-- Sorting strictly before implies sorting before. -/
theorem le_of_lt (o : OrderSpec p) {x y : Tuple T p} (h : o.lt x y = true) :
    o.le x y = true := by
  rw [lt_iff] at h
  rcases o.le_total x y with h' | h'
  · exact h'
  · rw [h'] at h; exact absurd h (by simp)

/-- **Before, peer, after**: the three cases the clause allows, and no
fourth. -/
theorem le_iff_lt_or_peer (o : OrderSpec p) (x y : Tuple T p) :
    o.le x y = true ↔ (o.lt x y = true ∨ o.peer x y = true) := by
  simp only [lt, peer, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · intro h
    cases hy : o.le y x
    · exact Or.inl rfl
    · exact Or.inr ⟨h, rfl⟩
  · rintro (h | ⟨h, _⟩)
    · rcases o.le_total x y with h' | h'
      · exact h'
      · rw [h'] at h; exact absurd h (by simp)
    · exact h

end OrderSpec

/-! ## The frames the clause determines

`ρ o' o` reads "an occurrence with order value `o'` is in the frame of one
with order value `o`", so the current row's value is the second argument. -/

namespace ValueFrame

variable [ValueType T]

/-- `RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW` under the clause
`o`, SQL's default frame when a window names an `ORDER BY`: the current row,
its peers, and everything the clause sorts before them. -/
def rangeUpTo (o : OrderSpec p) : ValueFrame T p :=
  ⟨fun o' ov => o.le o' ov, fun _ => true⟩

/-- The rows the clause sorts *strictly* before the current row's peers:
`RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW EXCLUDE GROUP`. It is the
frame a running total that must not read the row it annotates needs, and it
can be empty in a world where that row is present. -/
def rangeBefore (o : OrderSpec p) : ValueFrame T p :=
  ⟨fun o' ov => o.lt o' ov, fun _ => false⟩

/-- `GROUPS BETWEEN CURRENT ROW AND CURRENT ROW`: the current row's peer
group, and nothing else. -/
def peerGroup (o : OrderSpec p) : ValueFrame T p :=
  ⟨fun o' ov => o.peer o' ov, fun _ => true⟩

/-- `EXCLUDE GROUP`: the frame with the current row *and its peers* taken
out. -/
def excludeGroup (o : OrderSpec p) (w : ValueFrame T p) : ValueFrame T p :=
  ⟨fun o' ov => w.ρ o' ov && !o.peer o' ov, fun _ => false⟩

/-- `EXCLUDE TIES`: the frame with the current row's peers taken out, the
row itself left in. -/
def excludeTies (o : OrderSpec p) (w : ValueFrame T p) : ValueFrame T p :=
  ⟨fun o' ov => w.ρ o' ov && !o.peer o' ov, w.s⟩

@[simp] theorem rangeUpTo_containsSelf (o : OrderSpec p) :
    (rangeUpTo o : ValueFrame T p).ContainsSelf := fun ov => by
  simp [rangeUpTo]

@[simp] theorem rangeUpTo_containsCurrent (o : OrderSpec p) :
    (rangeUpTo o : ValueFrame T p).ContainsCurrent := fun _ => rfl

/-- The rows strictly before are determined by the tuple even though the row
is outside its own frame: its peers are outside too, so no occurrence needs
telling from its twin. -/
@[simp] theorem rangeBefore_containsSelf (o : OrderSpec p) :
    (rangeBefore o : ValueFrame T p).ContainsSelf := fun ov => by
  simp [rangeBefore]

@[simp] theorem peerGroup_containsSelf (o : OrderSpec p) :
    (peerGroup o : ValueFrame T p).ContainsSelf := fun ov => by
  simp [peerGroup]

@[simp] theorem peerGroup_containsCurrent (o : OrderSpec p) :
    (peerGroup o : ValueFrame T p).ContainsCurrent := fun _ => rfl

/-- **`EXCLUDE GROUP` keeps a frame readable off the relation**: it drops the
current row together with its peers, so two equal rows are dropped from each
other's frame as well as from their own. -/
@[simp] theorem excludeGroup_containsSelf (o : OrderSpec p)
    (w : ValueFrame T p) : (excludeGroup o w : ValueFrame T p).ContainsSelf :=
  fun ov => by simp [excludeGroup]

/-- **`EXCLUDE TIES` is not**, and for the same reason as `EXCLUDE CURRENT
ROW`: it leaves each of two equal rows in the other's frame and out of its
own, so the two take different values from one relation – which, not telling
them apart, cannot say which takes which. -/
theorem not_containsSelf_excludeTies (o : OrderSpec p) {w : ValueFrame T p}
    (h : w.ContainsCurrent) :
    ¬ (excludeTies o w : ValueFrame T p).ContainsSelf := by
  intro hc
  have hz := hc (0 : Tuple T p)
  rw [show (excludeTies o w).s = w.s from rfl, h (0 : Tuple T p)] at hz
  simp [excludeTies] at hz

end ValueFrame

/-! ## Where nothing is null

With every column `ASC` and no null to place, the clause is the domain's own
lexicographic order on the order values, and the frames it determines are
the ones stated against that order. -/

/-- The tuple without its first column. -/
def Tuple.tail (x : Tuple T (p+1)) : Tuple T p := fun k => x k.succ

@[simp] theorem Tuple.tail_apply (x : Tuple T (p+1)) (k : Fin p) :
    Tuple.tail x k = x k.succ := rfl

variable [ValueType T]

/-- **The tuple order, read one column at a time**: the first column decides
unless it ties. -/
theorem Tuple.lt_succ_iff (x y : Tuple T (p+1)) :
    (x < y) ↔ ((x 0 < y 0) ∨ (x 0 = y 0 ∧ (Tuple.tail x < Tuple.tail y))) := by
  constructor
  · rintro ⟨i, hlt, hi⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact Or.inl hi
    · refine Or.inr ⟨hlt 0 (Fin.succ_pos j), ⟨j, ?_, hi⟩⟩
      exact fun k hk => hlt k.succ (Fin.succ_lt_succ_iff.mpr hk)
  · rintro (h0 | ⟨h0, hm⟩)
    · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h0⟩
    · obtain ⟨m, hlt, hmm⟩ := hm
      refine ⟨m.succ, fun k hk => ?_, hmm⟩
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
      · exact h0
      · exact hlt j (Fin.succ_lt_succ_iff.mp hk)

/-- The same, for `≤`. -/
theorem Tuple.le_succ_iff (x y : Tuple T (p+1)) :
    (x ≤ y) ↔ ((x 0 < y 0) ∨ (x 0 = y 0 ∧ Tuple.tail x ≤ Tuple.tail y)) := by
  have hle : ∀ {q : ℕ} (a b : Tuple T q), (a ≤ b) ↔ ((a < b) ∨ (a = b)) :=
    fun _ _ => Iff.rfl
  have heq : x = y ↔ (x 0 = y 0 ∧ Tuple.tail x = Tuple.tail y) := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h0, ht⟩
      funext k
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
      · exact h0
      · exact congrFun ht j
  rw [hle x y, Tuple.lt_succ_iff, heq, hle (Tuple.tail x) (Tuple.tail y)]
  tauto

namespace OrderSpec

/-- Dropping the first column of the clause together with the first column
of the tuples. -/
theorem leOn_map_succ (o : OrderSpec (p+1)) (l : List (Fin p))
    (x y : Tuple T (p+1)) :
    o.leOn (l.map Fin.succ) x y
      = OrderSpec.leOn (fun k : Fin p => o k.succ) l
          (Tuple.tail x) (Tuple.tail y) := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp only [List.map_cons, leOn, ih, Tuple.tail_apply]

theorem asc_succ (p : ℕ) :
    (fun k : Fin p => OrderSpec.asc (p+1) k.succ) = OrderSpec.asc p := rfl

/-- **Every column `ASC`, on a domain where nothing is null, is the domain's
own order on tuples**: the clause's lexicographic reading and the tuple order
the library already has are the same order. -/
theorem asc_le [NoNulls T] : ∀ {p : ℕ} (x y : Tuple T p),
    (OrderSpec.asc p).le x y = decide (x ≤ y)
  | 0, x, y => by
    have hxy : x = y := funext (fun k => k.elim0)
    simp [le, hxy]
  | (p+1), x, y => by
    rw [le, List.finRange_succ, leOn, leOn_map_succ, asc_succ]
    have hpeer : (OrderSpec.asc (p+1) 0).peer (x 0) (y 0)
        = decide (x 0 = y 0) := by
      simp only [OrderSpec.asc, OrderCol.peer, OrderCol.ASC_le]
      rw [Bool.eq_iff_iff]
      simp [le_antisymm_iff]
    rw [hpeer, show (OrderSpec.asc (p+1) 0).le (x 0) (y 0)
        = decide (x 0 ≤ y 0) from OrderCol.ASC_le _ _]
    by_cases h0 : x 0 = y 0
    · rw [decide_eq_true h0, ite_eq_left rfl,
        show (asc p).leOn (List.finRange p) (Tuple.tail x) (Tuple.tail y)
          = (asc p).le (Tuple.tail x) (Tuple.tail y) from rfl,
        asc_le (Tuple.tail x) (Tuple.tail y), Bool.eq_iff_iff]
      simp [Tuple.le_succ_iff, h0]
    · rw [decide_eq_false h0, ite_eq_right (by simp), Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Tuple.le_succ_iff, h0, false_and, or_false]
      exact ⟨fun h => lt_of_le_of_ne h h0, _root_.le_of_lt⟩

end OrderSpec

namespace ValueFrame

variable [NoNulls T]

/-- Under every column `ASC` and no null to place, `RANGE BETWEEN UNBOUNDED
PRECEDING AND CURRENT ROW` is the frame `ValueFrame.upTo` states against the
domain's order. -/
theorem rangeUpTo_asc :
    (rangeUpTo (OrderSpec.asc p) : ValueFrame T p) = ValueFrame.upTo := by
  unfold rangeUpTo ValueFrame.upTo
  exact congrArg (ValueFrame.mk · _)
    (funext fun a => funext fun b => OrderSpec.asc_le a b)

/-- And the rows strictly before are `ValueFrame.before`. -/
theorem rangeBefore_asc :
    (rangeBefore (OrderSpec.asc p) : ValueFrame T p) = ValueFrame.before := by
  unfold rangeBefore ValueFrame.before
  refine congrArg (ValueFrame.mk · _) (funext fun a => funext fun b => ?_)
  rw [show (OrderSpec.asc p).lt a b = !(OrderSpec.asc p).le b a from rfl,
    OrderSpec.asc_le, Bool.eq_iff_iff]
  simp [not_le]

end ValueFrame
