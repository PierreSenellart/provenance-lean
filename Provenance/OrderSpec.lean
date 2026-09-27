/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggValueCongr
import Provenance.Util.ValueTypeNull

/-!
# Order specifications: what a window's `ORDER BY` orders by

A window's `ORDER BY` does not order rows by the domain's own order. It
names, for each order column, a *direction* and a *null placement*, and
those two together give a total preorder on the order values: `ASC` or
`DESC` on the values of the domain, `NULLS FIRST` or `NULLS LAST` on the
nulls, which the domain's order knows nothing about. Order values that the
preorder does not separate are SQL's *peers*.

This file gives the specification (`OrderCol`, `OrderSpec`) and proves that
it is a total preorder (`OrderSpec.le_refl`, `le_trans`, `le_total`). Two
things are defined from it, and both are things the domain's order cannot
supply.

The first is the *bound* of a frame: `RANGE BETWEEN UNBOUNDED PRECEDING AND
CURRENT ROW` is the peers of the current row and everything sorted before
them, and which rows those are is a question about the clause. Those frames
are built in `Provenance.Frame`, where `ValueFrame` is.

The second is the order a frame is *read* in, which is what an aggregate
that is not symmetric depends on. `OrderSpec.readLe` is that order – the
clause on the order values, its ties broken by the canonical order on the
rows, so that two occurrences are tied exactly when they carry the same
row – and `OrderSpec.sortSeq` puts a listing of a frame into it. It is what
`ValueFrame.frameSeqOn` and hence the window operator read.

`sortSeq_tiePerm` is what makes that usable: any two listings of one frame
come out related by a tie-block permutation whose blocks are the
occurrences of one row, which is precisely the freedom every reading of a
token is invariant under. `map_eq_of_sorted` is the working form – two
readings of one frame give the *same* sequence of values – and
`filter_sortSeq_map_eq` says cutting a frame down to a possible world and
sorting commute on the values read off, which is what the random-world
commutation needs.

A window with no `ORDER BY` has no order columns at all, `OrderSpec.unordered`;
the clause then separates nothing (`peer_of_zero`) and the frame is read as a
group is read (`ValueFrame.frameListOf_of_peer`).
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

/-- **The column read backwards.** Reversing the direction reverses where
the nulls go with it, as `ASC`/`DESC` already do: `OrderCol.ASC.reverse` is
`OrderCol.DESC`. -/
def reverse (c : OrderCol) : OrderCol :=
  { desc := !c.desc, nullsFirst := !c.nullsFirst }

@[simp] theorem reverse_ASC : OrderCol.ASC.reverse = OrderCol.DESC := rfl

@[simp] theorem reverse_DESC : OrderCol.DESC.reverse = OrderCol.ASC := rfl

@[simp] theorem reverse_reverse (c : OrderCol) : c.reverse.reverse = c := by
  cases c; simp [reverse]

@[simp] theorem le_reverse (c : OrderCol) (a b : T) :
    c.reverse.le a b = c.le b a := by
  unfold le reverse
  cases ha : ValueType.isNull a <;> cases hb : ValueType.isNull b <;>
    cases hd : c.desc <;> cases hn : c.nullsFirst <;> simp

@[simp] theorem peer_reverse (c : OrderCol) (a b : T) :
    c.reverse.peer a b = c.peer a b := by
  unfold peer
  rw [le_reverse, le_reverse, Bool.and_comm]

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

/-- **No `ORDER BY`**: the clause with no order columns, which separates
nothing, so a frame under it is read as a group is read. -/
def unordered : OrderSpec 0 := fun k => k.elim0

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

/-- **The clause read backwards**, column by column: what `last_value`
reads its frame in where `first_value` reads it forwards. -/
def reverse (o : OrderSpec p) : OrderSpec p := fun k => (o k).reverse

@[simp] theorem reverse_reverse (o : OrderSpec p) : o.reverse.reverse = o :=
  funext fun k => OrderCol.reverse_reverse (o k)

@[simp] theorem leOn_reverse (o : OrderSpec p) (l : List (Fin p))
    (x y : Tuple T p) : o.reverse.leOn l x y = o.leOn l y x := by
  induction l with
  | nil => rfl
  | cons k ks ih =>
    show (if (o.reverse k).peer (x k) (y k) then o.reverse.leOn ks x y
      else (o.reverse k).le (x k) (y k)) = _
    rw [show o.reverse k = (o k).reverse from rfl, OrderCol.peer_reverse,
      OrderCol.le_reverse, ih]
    show (if (o k).peer (x k) (y k) then _ else _)
      = (if (o k).peer (y k) (x k) then _ else _)
    rw [show (o k).peer (y k) (x k) = (o k).peer (x k) (y k) from by
      unfold OrderCol.peer; rw [Bool.and_comm]]

@[simp] theorem le_reverse (o : OrderSpec p) (x y : Tuple T p) :
    o.reverse.le x y = o.le y x := leOn_reverse o _ x y

@[simp] theorem peer_reverse (o : OrderSpec p) (x y : Tuple T p) :
    o.reverse.peer x y = o.peer x y := by
  unfold peer
  rw [le_reverse, le_reverse, Bool.and_comm]

@[simp] theorem lt_reverse (o : OrderSpec p) (x y : Tuple T p) :
    o.reverse.lt x y = o.lt y x := by
  unfold lt
  rw [le_reverse]

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

/-- **Peers are interchangeable**: replacing an order value by a peer of it
changes no comparison. -/
theorem le_congr_left (o : OrderSpec p) {x y : Tuple T p}
    (h : o.peer x y = true) (z : Tuple T p) : o.le x z = o.le y z := by
  simp only [peer, Bool.and_eq_true] at h
  rw [Bool.eq_iff_iff]
  exact ⟨fun hz => o.le_trans h.2 hz, fun hz => o.le_trans h.1 hz⟩

theorem le_congr_right (o : OrderSpec p) {x y : Tuple T p}
    (h : o.peer x y = true) (z : Tuple T p) : o.le z x = o.le z y := by
  simp only [peer, Bool.and_eq_true] at h
  rw [Bool.eq_iff_iff]
  exact ⟨fun hz => o.le_trans hz h.1, fun hz => o.le_trans hz h.2⟩

/-- **A clause with no order columns separates nothing.** A window with no
`ORDER BY` has every pair of order values as peers, and reads its frame as a
group is read. -/
@[simp] theorem peer_of_zero (o : OrderSpec 0) (x y : Tuple T 0) :
    o.peer x y = true := by
  simp [peer, le, leOn]

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
/-! ## The order a frame is read in

An aggregate is a function on *sequences*, so a window has to say in which
order its frame is read. SQL says: the clause's. Since the clause is a
preorder it does not settle the peers, and the library breaks those ties by
its own order on rows – a choice invisible to every symmetric aggregate
(`SeqAggFunc.Symmetric`), and one that leaves two occurrences tied exactly
when they carry the same row, which is what a tie-block permutation is
allowed to exchange. -/

namespace OrderSpec

variable {α β : Type} [LinearOrder β]

/-- **The order a window reads its frame in**: the clause on the order
values a row carries, its ties broken by the canonical order on the rows
themselves. `val` reads an occurrence's row, `key` the order values of a
row. -/
def readLe (key : β → Tuple T p) (val : α → β) (o : OrderSpec p)
    (x y : α) : Bool :=
  if o.peer (key (val x)) (key (val y)) then decide (val x ≤ val y)
  else o.le (key (val x)) (key (val y))

variable {key : β → Tuple T p} {val : α → β} {o : OrderSpec p}

@[simp] theorem readLe_rfl (x : α) : readLe key val o x x = true := by
  simp [readLe]

/-- Occurrences carrying the same row are read in either order. -/
theorem readLe_of_val_eq {x y : α} (h : val x = val y) :
    readLe key val o x y = true := by
  simp [readLe, h]

theorem readLe_total (x y : α) :
    readLe key val o x y = true ∨ readLe key val o y x = true := by
  unfold readLe
  by_cases hp : o.peer (key (val x)) (key (val y)) = true
  · rw [ite_eq_left hp, ite_eq_left (by rw [OrderSpec.peer_comm] at hp; exact hp)]
    rcases _root_.le_total (val x) (val y) with h | h <;> simp [h]
  · rw [ite_eq_right hp, ite_eq_right (by rw [OrderSpec.peer_comm]; exact hp)]
    exact o.le_total _ _

theorem readLe_trans {x y z : α} (h₁ : readLe key val o x y = true)
    (h₂ : readLe key val o y z = true) : readLe key val o x z = true := by
  unfold readLe at h₁ h₂ ⊢
  by_cases hxy : o.peer (key (val x)) (key (val y)) = true
  · rw [ite_eq_left hxy] at h₁
    by_cases hyz : o.peer (key (val y)) (key (val z)) = true
    · rw [ite_eq_left hyz] at h₂
      rw [ite_eq_left (o.peer_trans hxy hyz)]
      exact decide_eq_true
        (_root_.le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂))
    · rw [ite_eq_right hyz] at h₂
      have hxz : o.peer (key (val x)) (key (val z)) = true → False :=
        fun h => hyz (o.peer_trans (by rw [OrderSpec.peer_comm]; exact hxy) h)
      rw [ite_eq_right (fun h => hxz h), o.le_congr_left hxy _]
      exact h₂
  · rw [ite_eq_right hxy] at h₁
    by_cases hyz : o.peer (key (val y)) (key (val z)) = true
    · have hxz : o.peer (key (val x)) (key (val z)) = true → False :=
        fun h => hxy (o.peer_trans h (by rw [OrderSpec.peer_comm]; exact hyz))
      rw [ite_eq_right (fun h => hxz h), ← o.le_congr_right hyz _]
      exact h₁
    · rw [ite_eq_right hyz] at h₂
      have hxz : o.peer (key (val x)) (key (val z)) = true → False := by
        intro h
        simp only [OrderSpec.peer, Bool.and_eq_true] at h
        exact hxy (by
          simp only [OrderSpec.peer, Bool.and_eq_true]
          exact ⟨h₁, o.le_trans h₂ h.2⟩)
      rw [ite_eq_right (fun h => hxz h)]
      exact o.le_trans h₁ h₂

/-- **Two occurrences are tied exactly when they carry the same row.** The
clause alone does not separate peers; the canonical tie-break does, down to
the row. -/
theorem val_eq_of_readLe {x y : α} (h₁ : readLe key val o x y = true)
    (h₂ : readLe key val o y x = true) : val x = val y := by
  unfold readLe at h₁ h₂
  by_cases hp : o.peer (key (val x)) (key (val y)) = true
  · rw [ite_eq_left hp] at h₁
    rw [ite_eq_left (by rw [OrderSpec.peer_comm] at hp; exact hp)] at h₂
    exact _root_.le_antisymm (of_decide_eq_true h₁) (of_decide_eq_true h₂)
  · rw [ite_eq_right hp] at h₁
    rw [ite_eq_right (by rw [OrderSpec.peer_comm]; exact hp)] at h₂
    exact absurd (by simp only [OrderSpec.peer, Bool.and_eq_true]; exact ⟨h₁, h₂⟩) hp

/-- **The occurrences of a frame, in the order the clause reads them.** -/
def sortSeq (key : β → Tuple T p) (val : α → β) (o : OrderSpec p)
    (L : List α) : List α :=
  L.mergeSort (readLe key val o)

theorem sortSeq_perm (L : List α) : (sortSeq key val o L).Perm L :=
  List.mergeSort_perm L _

theorem sortSeq_sorted (L : List α) :
    (sortSeq key val o L).Pairwise (fun x y => readLe key val o x y = true) :=
  List.pairwise_mergeSort (fun _ _ _ => readLe_trans) (fun a b => by
    rcases readLe_total (key := key) (val := val) (o := o) a b with h | h <;>
      simp [h]) L

/-- **Any two readings of one frame in the clause's order give the same
sequence of values.** They differ only inside blocks of occurrences carrying
equal rows, and equal rows give equal values. -/
theorem map_eq_of_sorted [DecidableEq α] {γ : Type} (g : β → γ)
    {L L' : List α} (h : L.Perm L')
    (hL : L.Pairwise (fun x y => readLe key val o x y = true))
    (hL' : L'.Pairwise (fun x y => readLe key val o x y = true)) :
    L.map (fun x => g (val x)) = L'.map (fun x => g (val x)) :=
  TiePerm.map_eq (fun hv => congrArg g hv)
    (tiePerm_of_perm_of_sorted_by (fun x y => readLe key val o x y = true) val
      (fun hxy hyx => val_eq_of_readLe hxy hyx)
      (fun hv => readLe_of_val_eq hv) h hL hL')

/-- Two listings of one frame give the same sequence of values once sorted
by the clause. -/
theorem sortSeq_map_eq [DecidableEq α] {γ : Type} (g : β → γ)
    {L L' : List α} (h : L.Perm L') :
    (sortSeq key val o L).map (fun x => g (val x))
      = (sortSeq key val o L').map (fun x => g (val x)) :=
  map_eq_of_sorted g (((sortSeq_perm L).trans h).trans (sortSeq_perm L').symm)
    (sortSeq_sorted L) (sortSeq_sorted L')

/-- **Cutting a frame down and sorting commute, on the values read off.**
Selecting occurrences from a sorted reading and sorting the selection give
the same sequence of values. -/
theorem filter_sortSeq_map_eq [DecidableEq α] {γ : Type} (g : β → γ)
    (q : α → Bool) (L : List α) :
    ((sortSeq key val o L).filter q).map (fun x => g (val x))
      = (sortSeq key val o (L.filter q)).map (fun x => g (val x)) :=
  map_eq_of_sorted g
    (((sortSeq_perm L).filter q).trans (sortSeq_perm (L.filter q)).symm)
    ((sortSeq_sorted L).filter q) (sortSeq_sorted (L.filter q))

/-- **Sorting by the clause settles the sequence down to the rows.** Two
listings of the same frame come out tie-permuted, the blocks being the
occurrences that carry one row – which is exactly the freedom the readings
of a token are invariant under. -/
theorem sortSeq_tiePerm [DecidableEq α] {L L' : List α} (h : L.Perm L') :
    TiePerm (fun x y => val x = val y)
      (sortSeq key val o L) (sortSeq key val o L') :=
  tiePerm_of_perm_of_sorted_by (fun x y => readLe key val o x y = true) val
    (fun hxy hyx => val_eq_of_readLe hxy hyx)
    (fun hv => readLe_of_val_eq hv)
    (((sortSeq_perm L).trans h).trans (sortSeq_perm L').symm)
    (sortSeq_sorted L) (sortSeq_sorted L')

end OrderSpec
