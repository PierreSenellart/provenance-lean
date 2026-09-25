/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Occurrence
import Provenance.AggValue

/-!
# Window frames determined by values

A window function computes, for each row, an aggregate over a *frame*: some
of the rows sharing its partition. Which rows, in general, depends on
positions in a sorted partition – the previous row, the previous three – and
a position is not something a row carries. In a world where some rows are
absent the previous row is the previous *present* row, so a frame read
positionally is not the restriction of the frame read on the whole relation,
and the value a row gets cannot be computed world by world.

A frame is *determined by values* when membership depends only on the order
values of the two rows and on whether they are the same occurrence: a
relation `ρ` between order values decides the other rows, and a predicate `s`
on its own order value decides whether the row is in its own frame. SQL's
`RANGE` and `GROUPS` frames without offsets, the frames with `EXCLUDE`, and
the frame of the rows strictly before the current one are all of this form;
`ROWS` frames other than the whole partition are not.

For such a frame the restriction property holds (`frame_inter`): the frame of
an occurrence among the present rows is its frame in the whole relation,
intersected with them. That is what lets a window be read in every world, and
it is the only property of frames the annotated semantics uses.
-/

variable {T K : Type} {n m p : ℕ}

/-- The values a tuple has at a list of columns: its partition key, or its
order value. -/
def Tuple.key (is : Tuple (Fin n) p) (u : Tuple T n) : Tuple T p :=
  fun k => u (is k)

/-- A multiset as a sorted list: the canonical reading of a relation as a
sequence. It is computable, where a choice through `Multiset.toList` is not,
and it is determined by the multiset, which is what lets two sequences built
from the same rows be recognised as the same sequence. -/
def sortList {α : Type} [LinearOrder α] (M : Multiset α) : List α :=
  (M.foldr sortedInsert ⟨[], by simp⟩).val

@[simp] theorem sortList_coe {α : Type} [LinearOrder α] (M : Multiset α) :
    (↑(sortList M) : Multiset α) = M :=
  Having.foldr_sortedInsert_coe M

theorem sortList_pairwise {α : Type} [LinearOrder α] (M : Multiset α) :
    (sortList M).Pairwise (· ≤ ·) :=
  (Multiset.foldr sortedInsert ⟨[], by simp⟩ M).property

/-- **A sorted list is its multiset's sorted list.** Two sequences built by
sorting the same rows are the same sequence, whatever route built them. -/
theorem sortList_eq {α : Type} [LinearOrder α] {l : List α} {M : Multiset α}
    (hs : l.Pairwise (· ≤ ·)) (hm : (↑l : Multiset α) = M) : l = sortList M :=
  List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hs (sortList_pairwise M)
    (Multiset.coe_eq_coe.mp (by rw [hm, sortList_coe]))

/-- Sorting and then keeping what a predicate accepts is sorting what it
accepts: filtering does not disturb an order. -/
theorem sortList_filter {α : Type} [LinearOrder α] (M : Multiset α)
    (c : α → Prop) [DecidablePred c] :
    (sortList M).filter (fun a => decide (c a)) = sortList (M.filter c) :=
  sortList_eq (List.Pairwise.filter _ (sortList_pairwise M))
    (by rw [← Multiset.filter_coe, sortList_coe])

/-- The canonical indexing of a relation: its rows in sorted order. It is
computable, where a choice through `Multiset.toList` is not, and canonical
rather than arbitrary – though by `OccFam.Congr_of_toMultiset_eq` any
indexing would give the same answer for an operator that respects
re-indexing. -/
def OccFam.ofSorted [LinearOrder α] (s : Multiset α) : OccFam α :=
  ⟨((s.foldr sortedInsert ⟨[], by simp⟩).val).length,
    fun i => ((s.foldr sortedInsert ⟨[], by simp⟩).val).get i⟩

@[simp] theorem OccFam.toMultiset_ofSorted [LinearOrder α] (s : Multiset α) :
    (OccFam.ofSorted s).toMultiset = s := by
  have hlist : ∀ l : List α, (OccFam.mk l.length l.get).toMultiset
      = (l : Multiset α) := by
    intro l
    show Multiset.map l.get (Finset.univ : Finset (Fin l.length)).val = _
    rw [show (Finset.univ : Finset (Fin l.length)).val
          = Multiset.ofList (List.finRange l.length) from rfl,
      Multiset.map_coe, ← List.ofFn_eq_map, List.ofFn_get]
  rw [show OccFam.ofSorted s
        = OccFam.mk ((s.foldr sortedInsert ⟨[], by simp⟩).val).length
            ((s.foldr sortedInsert ⟨[], by simp⟩).val).get from rfl,
    hlist]
  exact Having.foldr_sortedInsert_coe s

/-- A frame determined by values: `ρ` decides which *other* occurrences of
the partition belong, from the two order values, and `s` decides whether the
occurrence belongs to its own frame.

Writing the two separately is what distinguishes `EXCLUDE CURRENT ROW` from
its peers: the current row and a peer have the same order value, so no
relation on order values alone could drop one and keep the other. -/
structure ValueFrame (T : Type) (p : ℕ) where
  /-- Whether an occurrence with order value `o'` is in the frame of one
  with order value `o`. -/
  ρ : Tuple T p → Tuple T p → Bool
  /-- Whether an occurrence with order value `o` is in its own frame. -/
  s : Tuple T p → Bool

namespace ValueFrame

variable [ValueType T]

/-- The frame *contains its current row exactly when it contains its peers*.
Under this condition the frame of an occurrence depends only on its tuple, so
a window over it does not need the occurrences told apart; `EXCLUDE CURRENT
ROW` and `EXCLUDE TIES` are the frames that fail it. -/
def ContainsSelf (w : ValueFrame T p) : Prop := ∀ o, w.s o = w.ρ o o

/-- Whether occurrence `j` is in the frame of occurrence `i`: same partition,
and then `s` on itself or `ρ` on the order values. -/
def mem {α : Type} (val : α → Tuple T n) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (r : OccFam α) (i j : Fin r.size) : Bool :=
  decide (Tuple.key P (val (r.row j)) = Tuple.key P (val (r.row i)))
    && (if j = i then w.s (Tuple.key O (val (r.row i)))
        else w.ρ (Tuple.key O (val (r.row j))) (Tuple.key O (val (r.row i))))

/-- The frame of an occurrence, among a set of present occurrences. -/
def frameIn {α : Type} (val : α → Tuple T n) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (r : OccFam α) (W : Finset (Fin r.size)) (i : Fin r.size) :
    Finset (Fin r.size) :=
  W.filter (fun j => mem val P O w r i j)

/-- The frame of an occurrence in the whole relation. -/
def frame {α : Type} (val : α → Tuple T n) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (r : OccFam α) (i : Fin r.size) : Finset (Fin r.size) :=
  frameIn val P O w r Finset.univ i

/-- Where the frame contains its current row exactly when it contains its
peers, membership stops mentioning the occurrence at all: the `if` collapses,
because an occurrence and itself have the same order value. -/
theorem mem_of_containsSelf {α : Type} {val : α → Tuple T n}
    {P : Tuple (Fin n) m} {O : Tuple (Fin n) p}
    {w : ValueFrame T p} (h : w.ContainsSelf) (r : OccFam α)
    (i j : Fin r.size) :
    mem val P O w r i j
      = (decide (Tuple.key P (val (r.row j)) = Tuple.key P (val (r.row i)))
          && w.ρ (Tuple.key O (val (r.row j))) (Tuple.key O (val (r.row i)))) := by
  unfold mem
  by_cases hji : j = i
  · subst hji
    rw [ite_eq_left rfl, h]
  · rw [ite_eq_right hji]

/-- **Such a frame depends only on the tuple.** Two occurrences carrying the
same tuple have the same frame, so a window over such a frame gives equal
rows equal values and needs no occurrences told apart.

The frames that fail `ContainsSelf` are exactly `EXCLUDE CURRENT ROW` and
`EXCLUDE TIES`, and they are exactly the ones that do need them: each of two
equal rows is then in the other's frame and not in its own, so the two get
different aggregates from the same relation. -/
theorem frame_eq_of_key_eq {α : Type} {val : α → Tuple T n}
    {P : Tuple (Fin n) m} {O : Tuple (Fin n) p}
    {w : ValueFrame T p} (h : w.ContainsSelf) (r : OccFam α)
    {i i' : Fin r.size} (hP : Tuple.key P (val (r.row i))
        = Tuple.key P (val (r.row i')))
    (hO : Tuple.key O (val (r.row i)) = Tuple.key O (val (r.row i'))) :
    frame val P O w r i = frame val P O w r i' := by
  unfold frame frameIn
  ext j
  simp only [Finset.mem_filter, mem_of_containsSelf h, hP, hO]

/-- **The restriction property.** The frame of an occurrence among the
present rows is its frame in the whole relation, intersected with them.

This is the only property of frames the annotated semantics uses, and it is
what a positional frame lacks: whether an occurrence belongs to another's
frame depends on the two order values and on whether they are the same
occurrence, on nothing else that the absent rows could change. -/
theorem frame_inter {α : Type} (val : α → Tuple T n) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (r : OccFam α) (W : Finset (Fin r.size))
    (i : Fin r.size) :
    frameIn val P O w r W i = frame val P O w r i ∩ W := by
  unfold frameIn frame
  ext j
  constructor
  · intro hj
    obtain ⟨hjW, hmem⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmem⟩, hjW⟩
  · intro hj
    obtain ⟨hall, hjW⟩ := Finset.mem_inter.mp hj
    exact Finset.mem_filter.mpr ⟨hjW, (Finset.mem_filter.mp hall).2⟩

/-- The frame *contains its current row*: `s` holds everywhere. A frame that
does is read like a group – in a world where the row is present its frame has
at least that row, so it is never empty. One that may exclude it can be empty
while the row exists, and its aggregate then ranges over nothing.

The operator below decides this per row rather than per frame, by asking `s`
of the row's own order value, which is decidable where this is not. The two
agree wherever `s` is constant, which is every frame of SQL: `true` for the
defaults, `false` for `EXCLUDE CURRENT ROW` and for the frame of the rows
strictly before, and `ρ o o` for `EXCLUDE TIES`. -/
def ContainsCurrent (w : ValueFrame T p) : Prop := ∀ o, w.s o = true

/-! ## The frames of SQL

The frames a `WINDOW` clause can name that are determined by values: the
whole partition, the rows up to and including the current row's peers, the
rows strictly before them, and the `EXCLUDE` variants of each. The `ROWS`
frames with offsets – the previous row, the previous three – are not among
them, and cannot be: which row is the previous one depends on which rows are
present, so no relation on order values decides it. -/

/-- The whole partition: SQL's default frame under no `ORDER BY`, and
`RANGE BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING`. -/
def whole : ValueFrame T p := ⟨fun _ _ => true, fun _ => true⟩

/-- `RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW`, SQL's default frame
under an `ORDER BY`: the current row, its peers, and everything ordered
before them. -/
def upTo : ValueFrame T p :=
  ⟨fun o' o => decide (o' ≤ o), fun _ => true⟩

/-- The rows strictly before the current row's peers: the frame a running
total that must not read the row it annotates needs. It contains neither the
row nor its peers, so it can be empty in a world where the row is present –
which is why a window over it reads its token in the scalar convention. -/
def before : ValueFrame T p :=
  ⟨fun o' o => decide (o' < o), fun _ => false⟩

/-- `EXCLUDE CURRENT ROW`: the same frame with the current occurrence taken
out, its peers left in. It is the modifier no relation on order values can
express, which is why `s` is a field of its own. -/
def excludeCurrent (w : ValueFrame T p) : ValueFrame T p := ⟨w.ρ, fun _ => false⟩

omit [ValueType T] in
@[simp] theorem whole_containsSelf : (whole : ValueFrame T p).ContainsSelf :=
  fun _ => rfl

omit [ValueType T] in
@[simp] theorem whole_containsCurrent : (whole : ValueFrame T p).ContainsCurrent :=
  fun _ => rfl

@[simp] theorem upTo_containsSelf : (upTo : ValueFrame T p).ContainsSelf :=
  fun o => by simp [upTo]

@[simp] theorem upTo_containsCurrent : (upTo : ValueFrame T p).ContainsCurrent :=
  fun _ => rfl

/-- The rows strictly before are determined by the tuple even though the row
is outside its own frame: its peers are outside too, so no occurrence needs
telling from its twin. -/
@[simp] theorem before_containsSelf : (before : ValueFrame T p).ContainsSelf :=
  fun o => by simp [before]

omit [ValueType T] in
/-- **`EXCLUDE CURRENT ROW` is exactly what occurrences are needed for.**
Excluding the current row from a frame that contained it leaves each of two
equal rows in the other's frame and out of its own, so the two get different
aggregates from the same relation – and a relation, which does not tell them
apart, cannot say which gets which. -/
theorem not_containsSelf_excludeCurrent {w : ValueFrame T p}
    (h : ∃ o : Tuple T p, w.ρ o o = true) :
    ¬ (excludeCurrent w).ContainsSelf := by
  obtain ⟨o, ho⟩ := h
  intro hc
  have hco := hc o
  simp [excludeCurrent, ho] at hco

variable [HasAltLinearOrder K]

/-- The occurrence sequence of a frame: its occurrences with their
annotations, in the canonical order of annotated tuples, as a group's are.

The order matters only to order-dependent aggregates, and the tie-break
between occurrences carrying equal tuples is invisible to every reading of
the token that is built from it. -/
def frameSeq {α : Type} [LinearOrder α] (val : α → Tuple T n)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (r : OccFam α) (i : Fin r.size) : List α :=
  (((frame val P O w r i).val.map r.row).foldr sortedInsert ⟨[], by simp⟩).val

/-- The order in which a group or a frame reads its occurrences: the
canonical one on annotated tuples, with the semiring's auxiliary order
breaking ties between equal tuples. The tie-break is invisible to every
reading of the token built from the sequence. -/
instance annotatedTupleLinearOrder : LinearOrder (AnnotatedTuple T K n) :=
  letI : LinearOrder K := HasAltLinearOrder.altOrder
  inferInstanceAs (LinearOrder (Tuple T n ×ₗ K))

/-- The canonical order on annotated tuples reads the tuple first, so it
refines the order on tuples. -/
theorem le_fst_of_le {a b : AnnotatedTuple T K n} (h : a ≤ b) :
    a.fst ≤ b.fst := by
  let _ : LinearOrder K := HasAltLinearOrder.altOrder
  exact Prod.Lex.monotone_fst a b h

/-- The plain reading of a family of annotated occurrences: the same
occurrences in the same order, their annotations forgotten. -/
def _root_.OccFam.plain (r : OccFam (AnnotatedTuple T K n)) : OccFam (Tuple T n) :=
  ⟨r.size, fun i => (r.row i).fst⟩

/-- **Sorting annotated tuples and projecting is sorting the tuples.** The
canonical order reads the tuple first, so the tie-break between equal tuples
is invisible after projection: the two lists are sorted and have the same
elements. -/
theorem sorted_map_fst (s : Multiset (AnnotatedTuple T K n)) :
    List.map (α := AnnotatedTuple T K n) Prod.fst
        ((s.foldr sortedInsert ⟨[], by simp⟩).val)
      = ((Multiset.map (α := AnnotatedTuple T K n) Prod.fst s).foldr
          sortedInsert ⟨[], by simp⟩).val := by
  have hmono : ∀ p q : AnnotatedTuple T K n, p ≤ q → p.fst ≤ q.fst :=
    fun _ _ h => le_fst_of_le h
  have hperm : List.Perm
      (List.map (α := AnnotatedTuple T K n) Prod.fst
        ((s.foldr sortedInsert ⟨[], by simp⟩).val))
      (((Multiset.map (α := AnnotatedTuple T K n) Prod.fst s).foldr
        sortedInsert ⟨[], by simp⟩).val) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.map_coe,
      Having.foldr_sortedInsert_coe, Having.foldr_sortedInsert_coe]
  refine hperm.eq_of_pairwise' (r := (· ≤ ·))
    (List.Pairwise.map (α := AnnotatedTuple T K n) Prod.fst hmono
      ((Multiset.foldr sortedInsert ⟨[], by simp⟩ s).property))
    ((Multiset.foldr sortedInsert ⟨[], by simp⟩
      (Multiset.map (α := AnnotatedTuple T K n) Prod.fst s)).property)

/-- Sorting annotated tuples and projecting is sorting the tuples, in the
`sortList` form. -/
theorem sortList_map_fst (s : Multiset (AnnotatedTuple T K n)) :
    List.map (α := AnnotatedTuple T K n) Prod.fst (sortList s)
      = sortList (Multiset.map (α := AnnotatedTuple T K n) Prod.fst s) :=
  sorted_map_fst s

/-- The canonical indexing of a relation projects onto the canonical
indexing of its plain reading: the same occurrences in the same order. -/
theorem ofSorted_plain (s : Multiset (AnnotatedTuple T K n)) :
    (OccFam.ofSorted s).plain
      = OccFam.ofSorted (Multiset.map (α := AnnotatedTuple T K n) Prod.fst s) := by
  refine OccFam.ext_cast ?_ (fun i => ?_) <;>
    simp [OccFam.plain, OccFam.ofSorted, ← sorted_map_fst s]

/-- The token a window gives an occurrence: the aggregate over its frame,
read in the convention that occurrence's frame warrants.

Whether the row is in its own frame is decided by `s` of its own order
value. A row that is reads its aggregate as a group's, never over nothing; a
row that is not may have an empty frame in a world where it is itself
present, and its aggregate then ranges over no occurrence at all. -/
def token (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) : AggValue T K :=
  if w.s (Tuple.key O (r.row i).fst) then
    AggValue.ofGroup f t (frameSeq (α := AnnotatedTuple T K n) Prod.fst P O w r i)
  else
    AggValue.ofScalarGroup f t (frameSeq (α := AnnotatedTuple T K n) Prod.fst P O w r i)

/-- A row inside its own frame reads its aggregate as a group's. -/
@[simp] theorem token_scalar_of_mem (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size)
    (h : w.s (Tuple.key O (r.row i).fst) = true) :
    (token P O w t f r i).scalar = false := by
  simp [token, h]

/-- A row outside its own frame reads it in the scalar convention: the frame
may be empty in a world where the row is present. -/
@[simp] theorem token_scalar_of_not_mem (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (w : ValueFrame T p) (t : Term T n)
    (f : SeqAggFunc T) (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size)
    (h : w.s (Tuple.key O (r.row i).fst) = false) :
    (token P O w t f r i).scalar = true := by
  simp [token, h]

/-- Whichever convention it is read in, the token aggregates the frame. -/
theorem token_occs (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) :
    (token P O w t f r i).occs
      = (frameSeq (α := AnnotatedTuple T K n) Prod.fst P O w r i).map (fun q => (t.eval q.fst, q.snd)) := by
  unfold token AggValue.ofScalarGroup AggValue.ofGroup
  split <;> rfl

/-- An occurrence is in its own frame exactly when the frame contains the
current row at that occurrence's order value. -/
theorem self_mem_frame {α : Type} (val : α → Tuple T n) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (w : ValueFrame T p) (r : OccFam α) (i : Fin r.size) :
    i ∈ frame val P O w r i ↔ w.s (Tuple.key O (val (r.row i))) = true := by
  unfold frame frameIn mem
  simp

/-- The occurrence sequence of a frame holds exactly the frame's rows. -/
theorem frameSeq_coe {α : Type} [LinearOrder α] (val : α → Tuple T n)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (r : OccFam α) (i : Fin r.size) :
    (↑(frameSeq val P O w r i) : Multiset α)
      = (frame val P O w r i).val.map r.row :=
  Having.foldr_sortedInsert_coe _

/-- Whichever convention it is read in, the token aggregates with `f`. -/
theorem token_agg (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) :
    (token P O w t f r i).agg = f := by
  unfold token AggValue.ofScalarGroup AggValue.ofGroup
  split <;> rfl

/-! ## The frame read off the relation

An occurrence's frame is a set of occurrences, but what it *aggregates* is a
multiset of rows, and that multiset depends only on the relation and on the
row the frame is computed for: the rows of the partition that the frame's
relation accepts, with the occurrence's own row taken out and put back
exactly as `s` says. Reading it this way is what lets a window be compared
across a change of semiring or a restriction to a world, neither of which
preserves an indexing. -/

/-- The rows an occurrence's frame aggregates, read off the relation: the
rows the frame's relation accepts, with one copy of the occurrence's own row
removed and put back exactly when `s` holds. -/
def frameOf {α : Type} [LinearOrder α] (val : α → Tuple T n)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (X : Multiset α) (x : α) : Multiset α :=
  if w.s (Tuple.key O (val x)) = true then
    x ::ₘ (X.filter (fun y =>
      Tuple.key P (val y) = Tuple.key P (val x)
        ∧ w.ρ (Tuple.key O (val y)) (Tuple.key O (val x)) = true)).erase x
  else
    (X.filter (fun y =>
      Tuple.key P (val y) = Tuple.key P (val x)
        ∧ w.ρ (Tuple.key O (val y)) (Tuple.key O (val x)) = true)).erase x

/-- **The whole partition is the partition.** With `whole`, an occurrence's
frame is every row sharing its partition key – its own row included, once. -/
theorem frameOf_whole {α : Type} [LinearOrder α] (val : α → Tuple T n)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (X : Multiset α) {x : α}
    (hx : x ∈ X) :
    frameOf val P O (whole : ValueFrame T p) X x
      = X.filter (fun y => Tuple.key P (val y) = Tuple.key P (val x)) := by
  have hs : (whole : ValueFrame T p).s (Tuple.key O (val x)) = true := rfl
  have hmem : x ∈ X.filter (fun y =>
      Tuple.key P (val y) = Tuple.key P (val x)
        ∧ (whole : ValueFrame T p).ρ (Tuple.key O (val y))
            (Tuple.key O (val x)) = true) :=
    Multiset.mem_filter.mpr ⟨hx, rfl, rfl⟩
  unfold frameOf
  rw [ite_eq_left hs, Multiset.cons_erase hmem]
  exact Multiset.filter_congr (fun y _ => and_iff_left rfl)

/-- **A frame is carried along a map that keeps the values.** Changing the
semiring, or forgetting the annotations, leaves every frame the image of the
frame it came from: a frame reads the values and nothing else. -/
theorem frameOf_map {α β : Type} [LinearOrder α] [LinearOrder β]
    {valα : α → Tuple T n} {valβ : β → Tuple T n} (g : α → β)
    (hg : ∀ a, valβ (g a) = valα a) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (w : ValueFrame T p) (X : Multiset α) {x : α}
    (hx : x ∈ X) :
    frameOf valβ P O w (X.map g) (g x) = (frameOf valα P O w X x).map g := by
  have hfil : (X.map g).filter (fun y =>
        Tuple.key P (valβ y) = Tuple.key P (valβ (g x))
          ∧ w.ρ (Tuple.key O (valβ y)) (Tuple.key O (valβ (g x))) = true)
      = (X.filter (fun y =>
        Tuple.key P (valα y) = Tuple.key P (valα x)
          ∧ w.ρ (Tuple.key O (valα y)) (Tuple.key O (valα x)) = true)).map g := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map g)
      (Multiset.filter_congr (fun y _ => by
        show (Tuple.key P (valβ (g y)) = _ ∧ w.ρ (Tuple.key O (valβ (g y))) _ = true) ↔ _
        rw [hg y, hg x]))
  have herase : ((X.filter (fun y =>
        Tuple.key P (valα y) = Tuple.key P (valα x)
          ∧ w.ρ (Tuple.key O (valα y)) (Tuple.key O (valα x)) = true)).map g).erase (g x)
      = ((X.filter (fun y =>
        Tuple.key P (valα y) = Tuple.key P (valα x)
          ∧ w.ρ (Tuple.key O (valα y)) (Tuple.key O (valα x)) = true)).erase x).map g := by
    by_cases hmem : x ∈ X.filter (fun y =>
        Tuple.key P (valα y) = Tuple.key P (valα x)
          ∧ w.ρ (Tuple.key O (valα y)) (Tuple.key O (valα x)) = true)
    · conv_lhs => rw [← Multiset.cons_erase hmem]
      rw [Multiset.map_cons, Multiset.erase_cons_head]
    · have hnot : g x ∉ (X.filter (fun y =>
          Tuple.key P (valα y) = Tuple.key P (valα x)
            ∧ w.ρ (Tuple.key O (valα y)) (Tuple.key O (valα x)) = true)).map g := by
        intro hgm
        obtain ⟨y, hy, hgy⟩ := Multiset.mem_map.mp hgm
        obtain ⟨-, hpy⟩ := Multiset.mem_filter.mp hy
        refine hmem (Multiset.mem_filter.mpr ⟨hx, ?_⟩)
        have hval : valα y = valα x := by rw [← hg y, ← hg x, hgy]
        rwa [hval] at hpy
      rw [Multiset.erase_of_notMem hnot, Multiset.erase_of_notMem hmem]
  unfold frameOf
  rw [hfil, herase, hg]
  by_cases hs : w.s (Tuple.key O (valα x)) = true
  · rw [ite_eq_left hs, ite_eq_left hs, Multiset.map_cons]
  · rw [ite_eq_right hs, ite_eq_right hs]

/-- **The restriction property, read off the relation.** Restricting the
relation to the rows a predicate keeps restricts every frame of a kept row
to the rows it keeps. This is what lets a window be read world by world, and
it is the only property of frames the annotated semantics uses. -/
theorem frameOf_filter {α : Type} [LinearOrder α] (val : α → Tuple T n)
    (c : α → Prop) [DecidablePred c] (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (w : ValueFrame T p) (X : Multiset α) {x : α}
    (hx : c x) :
    frameOf val P O w (X.filter c) x = (frameOf val P O w X x).filter c := by
  have hfil : (X.filter c).filter (fun y =>
        Tuple.key P (val y) = Tuple.key P (val x)
          ∧ w.ρ (Tuple.key O (val y)) (Tuple.key O (val x)) = true)
      = (X.filter (fun y =>
        Tuple.key P (val y) = Tuple.key P (val x)
          ∧ w.ρ (Tuple.key O (val y)) (Tuple.key O (val x)) = true)).filter c := by
    rw [Multiset.filter_filter, Multiset.filter_filter]
    exact Multiset.filter_congr (fun y _ => and_comm)
  have herase : ∀ M : Multiset α, (M.filter c).erase x = (M.erase x).filter c := by
    intro M
    by_cases hm : x ∈ M
    · conv_lhs => rw [← Multiset.cons_erase hm]
      rw [Multiset.filter_cons_of_pos _ hx, Multiset.erase_cons_head]
    · have : x ∉ M.filter c := fun h => hm (Multiset.mem_of_mem_filter h)
      rw [Multiset.erase_of_notMem this, Multiset.erase_of_notMem hm]
  unfold frameOf
  rw [hfil, herase]
  by_cases hs : w.s (Tuple.key O (val x)) = true
  · rw [ite_eq_left hs, ite_eq_left hs, Multiset.filter_cons_of_pos _ hx]
  · rw [ite_eq_right hs, ite_eq_right hs]

/-- **A frame aggregates what the relation says it does.** The occurrence
sequence of a frame holds exactly the rows `frameOf` names, so nothing an
aggregate reads off a frame depends on the indexing. -/
theorem frameSeq_coe_frameOf {α : Type} [LinearOrder α]
    (val : α → Tuple T n) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (r : OccFam α) (i : Fin r.size) :
    (↑(frameSeq val P O w r i) : Multiset α)
      = frameOf val P O w r.toMultiset (r.row i) := by
  rw [frameSeq_coe]
  set Q : α → Prop := fun y =>
    Tuple.key P (val y) = Tuple.key P (val (r.row i))
      ∧ w.ρ (Tuple.key O (val y)) (Tuple.key O (val (r.row i))) = true with hQ
  set S : Multiset (Fin r.size) :=
    (Finset.univ : Finset (Fin r.size)).val.filter (fun j => Q (r.row j)) with hSdef
  have hnd : S.Nodup :=
    Multiset.Nodup.filter _ (Finset.univ : Finset (Fin r.size)).nodup
  -- the rows the frame's relation accepts are the image of the accepted indices
  have hfilter : r.toMultiset.filter Q = Multiset.map r.row S := by
    unfold OccFam.toMultiset
    rw [Multiset.filter_map]
    rfl
  have hiS : i ∈ S ↔ w.ρ (Tuple.key O (val (r.row i)))
      (Tuple.key O (val (r.row i))) = true := by
    simp [hSdef, hQ]
  -- removing the occurrence's own row removes exactly its own index
  have herase : (Multiset.map r.row S).erase (r.row i)
      = Multiset.map r.row (S.erase i) := by
    by_cases hi : i ∈ S
    · conv_lhs => rw [← Multiset.cons_erase hi]
      rw [Multiset.map_cons, Multiset.erase_cons_head]
    · have hx' : r.row i ∉ Multiset.map r.row S := by
        intro hmem
        obtain ⟨j, hj, hji⟩ := Multiset.mem_map.mp hmem
        refine hi (hiS.mpr ?_)
        have hQj := (Multiset.mem_filter.mp hj).2
        rw [hQ] at hQj
        rw [hji] at hQj
        exact hQj.2
      rw [Multiset.erase_of_notMem hx', Multiset.erase_of_notMem hi]
  -- the frame's indices are the accepted ones, its own put in exactly by `s`
  have hframe : (frame val P O w r i).val
      = if w.s (Tuple.key O (val (r.row i))) = true then i ::ₘ S.erase i
        else S.erase i := by
    refine Multiset.Nodup.ext (frame val P O w r i).nodup ?_ |>.mpr (fun j => ?_)
    · by_cases hs : w.s (Tuple.key O (val (r.row i))) = true
      · rw [ite_eq_left hs]
        exact (hnd.erase i).cons hnd.notMem_erase
      · rw [ite_eq_right hs]
        exact hnd.erase i
    · have hmemS : j ∈ S ↔ Q (r.row j) := by simp [hSdef]
      unfold frame frameIn mem
      by_cases hs : w.s (Tuple.key O (val (r.row i))) = true
      · rw [ite_eq_left hs]
        by_cases hji : j = i
        · subst hji
          simp [hs]
        · simp [hji, hnd.mem_erase_iff, hmemS, hQ]
      · rw [ite_eq_right hs]
        by_cases hji : j = i
        · subst hji
          simp [hs, hnd.mem_erase_iff]
        · simp [hji, hnd.mem_erase_iff, hmemS, hQ]
  rw [hframe]
  show Multiset.map r.row
      (if w.s (Tuple.key O (val (r.row i))) = true then i ::ₘ S.erase i
        else S.erase i)
    = if w.s (Tuple.key O (val (r.row i))) = true
      then r.row i ::ₘ (r.toMultiset.filter Q).erase (r.row i)
      else (r.toMultiset.filter Q).erase (r.row i)
  rw [hfilter, herase]
  by_cases hs : w.s (Tuple.key O (val (r.row i))) = true
  · rw [ite_eq_left hs, ite_eq_left hs, Multiset.map_cons]
  · rw [ite_eq_right hs, ite_eq_right hs]

/-- **A frame's occurrence sequence is read off the relation.** It is the
sorted list of the rows `frameOf` names, so it depends on the relation and
the row alone – not on which indexing of the relation was chosen, and not on
which occurrence of an equal row the frame belongs to, beyond what `s`
decides. -/
theorem frameSeq_eq_sortList {α : Type} [LinearOrder α] (val : α → Tuple T n)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (r : OccFam α) (i : Fin r.size) :
    frameSeq val P O w r i = sortList (frameOf val P O w r.toMultiset (r.row i)) :=
  sortList_eq (sortList_pairwise _) (frameSeq_coe_frameOf val P O w r i)

/-- **The token read off the relation.** A window's token depends on the
relation and on the row it is computed for, and on nothing else: which
occurrence of an equal row it is decides nothing beyond what `s` decides for
every one of them. -/
def tokenOf (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (t : Term T n) (f : SeqAggFunc T) (X : AnnotatedRelation T K n)
    (x : AnnotatedTuple T K n) : AggValue T K :=
  if w.s (Tuple.key O x.fst) then
    AggValue.ofGroup f t
      (sortList (frameOf (α := AnnotatedTuple T K n) Prod.fst P O w X x))
  else
    AggValue.ofScalarGroup f t
      (sortList (frameOf (α := AnnotatedTuple T K n) Prod.fst P O w X x))

/-- An occurrence's token is the token its relation gives its row. -/
theorem token_eq_tokenOf (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) :
    token P O w t f r i = tokenOf P O w t f r.toMultiset (r.row i) := by
  unfold token tokenOf
  rw [frameSeq_eq_sortList]

/-- Whichever convention it is read in, the token aggregates its frame. -/
theorem tokenOf_occs (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n) :
    (tokenOf P O w t f X x).occs
      = (sortList (frameOf (α := AnnotatedTuple T K n) Prod.fst P O w X x)).map
          (fun q => (t.eval q.fst, q.snd)) := by
  unfold tokenOf AggValue.ofScalarGroup AggValue.ofGroup
  split <;> rfl

/-- Whichever convention it is read in, the token aggregates with `f`. -/
theorem tokenOf_agg (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n) :
    (tokenOf P O w t f X x).agg = f := by
  unfold tokenOf AggValue.ofScalarGroup AggValue.ofGroup
  split <;> rfl

/-- The convention a token is read in is decided by whether the row is in
its own frame. -/
theorem tokenOf_scalar (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n) :
    (tokenOf P O w t f X x).scalar = !(w.s (Tuple.key O x.fst)) := by
  unfold tokenOf AggValue.ofScalarGroup AggValue.ofGroup
  split <;> simp_all

/-- **A row in its own frame is one of its own token's occurrences**, and
with its own annotation. That is what makes such a token guarded: in a world
where the row exists, its aggregate ranges over at least that row. -/
theorem mem_token_occs (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size)
    (h : w.s (Tuple.key O (r.row i).fst) = true) :
    (t.eval (r.row i).fst, (r.row i).snd) ∈ (token P O w t f r i).occs := by
  rw [token_occs]
  refine List.mem_map.mpr ⟨r.row i, ?_, rfl⟩
  rw [← Multiset.mem_coe, frameSeq_coe]
  exact Multiset.mem_map.mpr ⟨i, (self_mem_frame _ P O w r i).mpr h, rfl⟩

omit [HasAltLinearOrder K] in
/-- A frame does not read the annotations: an occurrence's frame in the
plain reading of a family is its frame in the family. -/
theorem frame_plain (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) :
    frame (α := Tuple T n) id P O w r.plain i
      = frame (α := AnnotatedTuple T K n) Prod.fst P O w r i := rfl

/-- **A frame's occurrence sequence projects onto the plain one.** The
sequence is built by sorting, and sorting annotated tuples then projecting is
sorting the tuples. -/
theorem frameSeq_plain (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) :
    List.map (α := AnnotatedTuple T K n) Prod.fst
        (frameSeq (α := AnnotatedTuple T K n) Prod.fst P O w r i)
      = frameSeq (α := Tuple T n) id P O w r.plain i := by
  unfold frameSeq
  rw [sorted_map_fst, Multiset.map_map]
  rfl

/-- **The token's deterministic reading is the plain aggregate over the
frame** – whichever convention the token is read in, since the convention
decides what the *worlds* of a comparison are and not what the aggregate is
over the whole relation. -/
theorem collapse_token (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) :
    (token P O w t f r i).collapse
      = f ((frameSeq (α := Tuple T n) id P O w r.plain i).map t.eval) := by
  unfold AggValue.collapse
  rw [token_occs, token_agg, List.map_map, ← frameSeq_plain, List.map_map]
  rfl

end ValueFrame
