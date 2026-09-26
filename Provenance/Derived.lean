/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQuery

/-!
# Derived operators

The operators of this file add nothing to the algebra: each is an
abbreviation, a query built from the basis, and its semantics – plain and
annotated – is the semantics of the query it abbreviates. What they buy is
that the theorems proved of the basis apply to them as they stand, and that
the translation of SQL has something to name.

Padding replaces columns by the null, which is what an outer join does to
the arm with no match. Intersection is a self-join of the two deduplicated
arms on all their columns, matching syntactically as SQL's `INTERSECT`
does – and not `ε(q₁ - (q₁ - q₂))`, which has the same rows but annotates
them by a difference of differences rather than by a conjunction of the two
memberships.

The semijoin and the antijoin are *not* here. They apply the left arm to a
scalar aggregation of the filtered right one, so that each occurrence of
the left arm keeps its multiplicity – a grouping on the left arm's columns
would merge its duplicates, which `WHERE EXISTS` does not. That needs the
apply operator, which this library does not have; over plain relations the
decorrelation would give the same rows, but not the same annotations, so
there is nothing to gain by anticipating it. What they will need is in
place: `SeqAggFunc.Counts`, `Having.existentialOn_counting`, and
`AggValue.predProvScalar_count_eq_zero`.
-/

variable {T : Type} {n m : ℕ}

namespace AggQuery

/-! ## Padding -/

section Padding

variable [ValueTypeNull T]

/-- The projection column that reads column `k`, or the null when there is
no column to read. -/
def padCol (c : Option (Fin n)) :
    ProjCol T (ColKind.allReg n) :=
  match c with
  | some k => .term (TermGIn.index k rfl)
  | none => .term (TermGIn.const ValueTypeNull.null)

@[simp] theorem padCol_kind (c : Option (Fin n)) :
    (padCol (T := T) c).kind = ColKind.reg := by
  cases c <;> rfl

/-- **Padding**: a projection that reads the columns `π` names and puts the
null where `π` names none. It is what an outer join does to the arm with no
match, and it adds no operator. -/
def pad (π : Fin m → Option (Fin n))
    (q : AggQuery T n (ColKind.allReg n)) : AggQuery T m (ColKind.allReg m) :=
  (Proj (fun j => padCol (π j)) q).castKind (funext fun j => padCol_kind (π j))

/-- The padding that keeps every column of `q` and appends `l` null
columns, as a left outer join does to an unmatched row. -/
def padRight (l : ℕ)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + l) (ColKind.allReg (n + l)) :=
  pad (Fin.addCases (fun i => some i) (fun _ => none)) q

/-- The padding that prepends `l` null columns, as a right outer join
does. -/
def padLeft (l : ℕ)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (l + n) (ColKind.allReg (l + n)) :=
  pad (Fin.addCases (fun _ => none) (fun i => some i)) q

/-- **What padding computes**: the rows of `q`, each read through `π` –
the column `π` names, or the null where it names none. -/
theorem evaluatePlain_pad (π : Fin m → Option (Fin n))
    (q : AggQuery T n (ColKind.allReg n)) (d : Database T) :
    (pad π q).evaluatePlain d
      = (q.evaluatePlain d).map (fun u => (fun j =>
          match π j with
          | some k => u k
          | none => ValueTypeNull.null : Tuple T m)) := by
  unfold pad
  rw [AggQuery.evaluatePlain_castKind]
  refine congrArg (Multiset.map · _) (funext fun u => funext fun j => ?_)
  show (padCol (π j)).evalPlain u = _
  cases π j <;> rfl

/-- Padding on the right keeps every column of `q` and appends nulls. -/
theorem evaluatePlain_padRight (l : ℕ)
    (q : AggQuery T n (ColKind.allReg n)) (d : Database T) :
    (padRight l q).evaluatePlain d
      = (q.evaluatePlain d).map (fun u =>
          (Fin.append u (fun _ : Fin l => ValueTypeNull.null) : Tuple T (n + l))) := by
  unfold padRight
  rw [evaluatePlain_pad]
  refine congrArg (Multiset.map · _) (funext fun u => funext fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    show (match Fin.addCases (fun i => some i) (fun _ => none) (Fin.castAdd l i) with
      | some k => u k | none => ValueTypeNull.null) = u i
    rw [Fin.addCases_left]
  · rw [Fin.append_right]
    show (match Fin.addCases (fun i => some i) (fun _ => none) (Fin.natAdd n i) with
      | some k => u k | none => ValueTypeNull.null) = ValueTypeNull.null
    rw [Fin.addCases_right]

/-- Padding on the left prepends nulls. -/
theorem evaluatePlain_padLeft (l : ℕ)
    (q : AggQuery T n (ColKind.allReg n)) (d : Database T) :
    (padLeft l q).evaluatePlain d
      = (q.evaluatePlain d).map (fun u =>
          (Fin.append (fun _ : Fin l => ValueTypeNull.null) u : Tuple T (l + n))) := by
  unfold padLeft
  rw [evaluatePlain_pad]
  refine congrArg (Multiset.map · _) (funext fun u => funext fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    show (match Fin.addCases (fun _ => none) (fun i => some i) (Fin.castAdd n i) with
      | some k => u k | none => ValueTypeNull.null) = ValueTypeNull.null
    rw [Fin.addCases_left]
  · rw [Fin.append_right]
    show (match Fin.addCases (fun _ => none) (fun i => some i) (Fin.natAdd l i) with
      | some k => u k | none => ValueTypeNull.null) = u i
    rw [Fin.addCases_right]

end Padding

/-! ## Intersection -/

section Inter

variable [ValueType T]

/-- The conjunction `⋀_{i<k} #i ≐ #(k+i)`: the two blocks of a doubled
schema agree, column by column, *syntactically* – two nulls being the same
value, as every key comparison in SQL's set operators is. -/
def interCond (k : ℕ) :
    GenPred T (ColKind.allReg (k + k)) :=
  keyJoinCond (fun i : Fin k => Fin.castAdd k i) (fun i : Fin k => Fin.natAdd k i)
    (fun _ => rfl) (fun _ => rfl)

@[simp] theorem interCond_hasAggAtom (k : ℕ) :
    (interCond (T := T) k).hasAggAtom = false :=
  keyJoinCond_hasAggAtom _ _ _ _

/-- The projection onto the first `a` columns of a schema of `a + b`. -/
def firstCols (a b : ℕ) : Tuple (ProjCol T (ColKind.allReg (a + b))) a :=
  fun i => .term (TermGIn.index (Fin.castAdd b i) rfl)

/-- The projection onto the last `b` columns of a schema of `a + b`. -/
def lastCols (a b : ℕ) : Tuple (ProjCol T (ColKind.allReg (a + b))) b :=
  fun j => .term (TermGIn.index (Fin.natAdd a j) rfl)

/-- The projection onto the first block of a doubled schema. -/
def fstBlock (k : ℕ) : Tuple (ProjCol T (ColKind.allReg (k + k))) k :=
  firstCols k k

omit [ValueType T] in
@[simp] theorem firstCols_kind (a b : ℕ) (i : Fin a) :
    ((firstCols (T := T) a b) i).kind = ColKind.reg := rfl

omit [ValueType T] in
@[simp] theorem lastCols_kind (a b : ℕ) (j : Fin b) :
    ((lastCols (T := T) a b) j).kind = ColKind.reg := rfl

omit [ValueType T] in
@[simp] theorem fstBlock_kind (k : ℕ) (i : Fin k) :
    ((fstBlock (T := T) k) i).kind = ColKind.reg := rfl

/-- Doubling an all-regular schema leaves it all-regular. -/
theorem append_allReg (a b : ℕ) :
    Fin.append (ColKind.allReg a) (ColKind.allReg b) = ColKind.allReg (a + b) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- A product filtered to its diagonal, where the right side has no
duplicate: the left rows that occur on the right, once each. -/
theorem filter_product_diag {α : Type} [DecidableEq α]
    (A B : Multiset α) (hB : B.Nodup)
    (P' : α × α → Prop) (inst : DecidablePred P')
    (hP : ∀ a b : α, P' (a, b) ↔ a = b) :
    @Multiset.filter _ P' inst (A.product B)
      = (A.filter (fun a => a ∈ B)).map (fun a => (a, a)) := by
  let _ := inst
  induction A using Multiset.induction_on with
  | empty => rfl
  | cons a A ih =>
    have hfil : Multiset.filter (fun b => P' (a, b)) B
        = if a ∈ B then {a} else 0 := by
      rw [Multiset.filter_congr (fun b _ => hP a b)]
      by_cases ha : a ∈ B
      · rw [ite_eq_left ha, Multiset.filter_eq B a,
          Multiset.count_eq_one_of_mem hB ha]
        rfl
      · rw [ite_eq_right ha, Multiset.filter_eq B a,
          Multiset.count_eq_zero.mpr ha]
        rfl
    have hhead : @Multiset.filter _ P' inst (Multiset.map (Prod.mk a) B)
        = if a ∈ B then {(a, a)} else 0 := by
      rw [Multiset.filter_map]
      simp only [Function.comp_def]
      rw [hfil]
      by_cases ha : a ∈ B <;> simp [ha]
    rw [show (a ::ₘ A).product B = (a ::ₘ A) ×ˢ B from rfl,
      Multiset.cons_product, Multiset.filter_add, hhead,
      show A ×ˢ B = A.product B from rfl, ih, Multiset.filter_cons]
    by_cases ha : a ∈ B <;> simp [ha]

/-- **Intersection**, SQL's `INTERSECT`: one copy of each tuple the two
arms share, matched syntactically. Its annotation is the product of the
two `⊕`-sums, one per arm – the provenance of a conjunction of the two
memberships, which is what `ε(q₁ - (q₁ - q₂))` would not give. -/
def inter (q₁ q₂ : AggQuery T n (ColKind.allReg n)) :
    AggQuery T n (ColKind.allReg n) :=
  (Proj (fstBlock n)
    (Sel (interCond n)
      ((Prod (Dedup q₁) (Dedup q₂)).castKind (append_allReg n n))))
  |>.castKind (funext fun i => fstBlock_kind n i)

/-- The join condition of `inter` holds on a pair exactly when the two
blocks are the same tuple. -/
theorem interCond_holdsPlain (u v : Tuple T n) :
    (interCond (T := T) n).holdsPlain (Fin.append u v) ↔ u = v := by
  rw [interCond, keyJoinCond_holdsPlain]
  constructor
  · intro h
    funext k
    have := h k
    rwa [Fin.append_left, Fin.append_right] at this
  · rintro rfl k
    rw [Fin.append_left, Fin.append_right]

/-- **What intersection computes**: one copy of each tuple the two arms
share, matched syntactically. -/
theorem evaluatePlain_inter (q₁ q₂ : AggQuery T n (ColKind.allReg n))
    (d : Database T) :
    (inter q₁ q₂).evaluatePlain d
      = Multiset.filter
          (fun u : Tuple T n =>
            u ∈ (show Multiset (Tuple T n) from q₂.evaluatePlain d))
          ((show Multiset (Tuple T n) from q₁.evaluatePlain d).dedup) := by
  unfold inter
  simp only [AggQuery.evaluatePlain_castKind, AggQuery.evaluatePlain]
  rw [show ∀ A B : Relation T n, A * B
      = Multiset.map (fun p : Tuple T n × Tuple T n => Fin.append p.1 p.2)
          (A.product B) from fun _ _ => rfl,
    Multiset.filter_map]
  rw [Multiset.filter_congr (fun p (_ : p ∈ (q₁.evaluatePlain d).dedup.product
      (q₂.evaluatePlain d).dedup) =>
    show ((interCond (T := T) n).holdsPlain ∘
        fun p : Tuple T n × Tuple T n => Fin.append p.1 p.2) p ↔ p.1 = p.2 from
      interCond_holdsPlain p.1 p.2)]
  rw [filter_product_diag _ _ (Multiset.nodup_dedup _) _ _ (fun _ _ => Iff.rfl),
    Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def]
  rw [show (fun u : Tuple T n =>
        (fun j => (fstBlock n j).evalPlain (Fin.append u u) : Tuple T n))
      = id from by
    funext u
    funext j
    show (Fin.append u u) (Fin.castAdd n j) = u j
    rw [Fin.append_left]]
  rw [Multiset.map_id]
  exact Multiset.filter_congr (fun u _ => Multiset.mem_dedup)

end Inter

/-! ## Outer joins -/

section Outer

variable [ValueTypeNull T] {n₁ n₂ : ℕ}

/-- The inner join of the two arms: the rows that match. -/
def innerJoin (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  Sel φ ((Prod q₁ q₂).castKind (append_allReg n₁ n₂))

/-- The rows of the left arm with no match, padded on the right with
nulls. -/
def leftUnmatched (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  padRight n₂ (Diff q₁
    ((Proj (firstCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
      (funext fun i => firstCols_kind n₁ n₂ i)))

/-- The rows of the right arm with no match, padded on the left with
nulls. -/
def rightUnmatched (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  padLeft n₁ (Diff q₂
    ((Proj (lastCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
      (funext fun j => lastCols_kind n₁ n₂ j)))

/-- **Left outer join**: the matching rows, and the rows of the left arm
with no match padded with nulls. -/
def leftOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  Sum (innerJoin φ q₁ q₂) (leftUnmatched φ q₁ q₂)

/-- **Right outer join**. -/
def rightOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  Sum (innerJoin φ q₁ q₂) (rightUnmatched φ q₁ q₂)

/-- **Full outer join**: both arms padded. -/
def fullOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  Sum (leftOuter φ q₁ q₂) (rightUnmatched φ q₁ q₂)

/-! ### What the outer joins compute -/

/-- The rows of the left arm that have a match: the first block of the
inner join. -/
def matchedLeft (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : Database T) :
    Multiset (Tuple T n₁) :=
  Multiset.map (fun w : Tuple T (n₁ + n₂) =>
      (fun j => w (Fin.castAdd n₂ j) : Tuple T n₁))
    (show Multiset (Tuple T (n₁ + n₂)) from (innerJoin φ q₁ q₂).evaluatePlain d)

/-- **A row of the left arm is matched exactly when some row of the right
arm satisfies the join predicate with it.** -/
theorem mem_matchedLeft (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : Database T)
    (u : Tuple T n₁) :
    u ∈ matchedLeft φ q₁ q₂ d
      ↔ (u ∈ (show Multiset (Tuple T n₁) from q₁.evaluatePlain d)
          ∧ ∃ v ∈ (show Multiset (Tuple T n₂) from q₂.evaluatePlain d),
              (φ.holdsPlain (Fin.append u v))) := by
  unfold matchedLeft innerJoin
  simp only [AggQuery.evaluatePlain_castKind, AggQuery.evaluatePlain]
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Multiset.mem_filter] at hw
    obtain ⟨hwp, hφ⟩ := hw
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hwp
    rw [show Multiset.product (q₁.evaluatePlain d) (q₂.evaluatePlain d)
        = (show Multiset (Tuple T n₁) from q₁.evaluatePlain d) ×ˢ
          (show Multiset (Tuple T n₂) from q₂.evaluatePlain d) from rfl,
      Multiset.mem_product] at hp
    refine ⟨?_, p.2, hp.2, ?_⟩
    · have : (fun j => (Fin.append p.1 p.2) (Fin.castAdd n₂ j) : Tuple T n₁) = p.1 := by
        funext j; rw [Fin.append_left]
      rw [this]; exact hp.1
    · have : (fun j => (Fin.append p.1 p.2) (Fin.castAdd n₂ j) : Tuple T n₁) = p.1 := by
        funext j; rw [Fin.append_left]
      rw [this]; exact hφ
  · rintro ⟨hu, v, hv, hφ⟩
    refine ⟨Fin.append u v, ?_, ?_⟩
    · rw [Multiset.mem_filter]
      exact ⟨Multiset.mem_map.mpr ⟨(u, v), Multiset.mem_product.mpr ⟨hu, hv⟩, rfl⟩, hφ⟩
    · funext j; rw [Fin.append_left]

/-- **What a left outer join computes**: the matching pairs, and the rows
of the left arm with no match, padded on the right with nulls. -/
theorem evaluatePlain_leftOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : Database T) :
    (leftOuter φ q₁ q₂).evaluatePlain d
      = (show Multiset (Tuple T (n₁ + n₂)) from (innerJoin φ q₁ q₂).evaluatePlain d)
        + (Multiset.map
            (fun u : Tuple T n₁ =>
              (Fin.append u (fun _ : Fin n₂ => ValueTypeNull.null) :
                Tuple T (n₁ + n₂)))
            (Multiset.filter (fun u => u ∉ matchedLeft φ q₁ q₂ d)
              (show Multiset (Tuple T n₁) from q₁.evaluatePlain d))
           : Multiset (Tuple T (n₁ + n₂))) := by
  show (show Multiset (Tuple T (n₁ + n₂)) from (innerJoin φ q₁ q₂).evaluatePlain d)
      + (show Multiset (Tuple T (n₁ + n₂)) from
          (leftUnmatched φ q₁ q₂).evaluatePlain d) = _
  refine congrArg (_ + ·) ?_
  unfold leftUnmatched
  rw [evaluatePlain_padRight]
  refine congrArg (Multiset.map _) ?_
  show Multiset.filter _ _ = _
  exact Multiset.filter_congr (fun u _ => by
    rw [matchedLeft, AggQuery.evaluatePlain_castKind]
    rfl)

/-- The rows of the right arm that have a match: the second block of the
inner join. -/
def matchedRight (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : Database T) :
    Multiset (Tuple T n₂) :=
  Multiset.map (fun w : Tuple T (n₁ + n₂) =>
      (fun j => w (Fin.natAdd n₁ j) : Tuple T n₂))
    (show Multiset (Tuple T (n₁ + n₂)) from (innerJoin φ q₁ q₂).evaluatePlain d)

/-- **A row of the right arm is matched exactly when some row of the left
arm satisfies the join predicate with it.** -/
theorem mem_matchedRight (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : Database T)
    (v : Tuple T n₂) :
    v ∈ matchedRight φ q₁ q₂ d
      ↔ (v ∈ (show Multiset (Tuple T n₂) from q₂.evaluatePlain d)
          ∧ ∃ u ∈ (show Multiset (Tuple T n₁) from q₁.evaluatePlain d),
              (φ.holdsPlain (Fin.append u v))) := by
  unfold matchedRight innerJoin
  simp only [AggQuery.evaluatePlain_castKind, AggQuery.evaluatePlain]
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Multiset.mem_filter] at hw
    obtain ⟨hwp, hφ⟩ := hw
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hwp
    rw [show Multiset.product (q₁.evaluatePlain d) (q₂.evaluatePlain d)
        = (show Multiset (Tuple T n₁) from q₁.evaluatePlain d) ×ˢ
          (show Multiset (Tuple T n₂) from q₂.evaluatePlain d) from rfl,
      Multiset.mem_product] at hp
    have hsnd : (fun j => (Fin.append p.1 p.2) (Fin.natAdd n₁ j) : Tuple T n₂) = p.2 := by
      funext j; rw [Fin.append_right]
    refine ⟨?_, p.1, hp.1, ?_⟩
    · rw [hsnd]; exact hp.2
    · rw [hsnd]; exact hφ
  · rintro ⟨hv, u, hu, hφ⟩
    refine ⟨Fin.append u v, ?_, ?_⟩
    · rw [Multiset.mem_filter]
      exact ⟨Multiset.mem_map.mpr ⟨(u, v), Multiset.mem_product.mpr ⟨hu, hv⟩, rfl⟩, hφ⟩
    · funext j; rw [Fin.append_right]

/-- **What a right outer join computes**: the matching pairs, and the rows
of the right arm with no match, padded on the left with nulls. -/
theorem evaluatePlain_rightOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : Database T) :
    (rightOuter φ q₁ q₂).evaluatePlain d
      = (show Multiset (Tuple T (n₁ + n₂)) from (innerJoin φ q₁ q₂).evaluatePlain d)
        + (Multiset.map
            (fun v : Tuple T n₂ =>
              (Fin.append (fun _ : Fin n₁ => ValueTypeNull.null) v :
                Tuple T (n₁ + n₂)))
            (Multiset.filter (fun v => v ∉ matchedRight φ q₁ q₂ d)
              (show Multiset (Tuple T n₂) from q₂.evaluatePlain d))
           : Multiset (Tuple T (n₁ + n₂))) := by
  show (show Multiset (Tuple T (n₁ + n₂)) from (innerJoin φ q₁ q₂).evaluatePlain d)
      + (show Multiset (Tuple T (n₁ + n₂)) from
          (rightUnmatched φ q₁ q₂).evaluatePlain d) = _
  refine congrArg (_ + ·) ?_
  unfold rightUnmatched
  rw [evaluatePlain_padLeft]
  refine congrArg (Multiset.map _) ?_
  show Multiset.filter _ _ = _
  exact Multiset.filter_congr (fun v _ => by
    rw [matchedRight, AggQuery.evaluatePlain_castKind]
    rfl)

/-- **What a full outer join computes**: the left outer join, and the rows
of the right arm with no match, padded on the left. -/
theorem evaluatePlain_fullOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : Database T) :
    (fullOuter φ q₁ q₂).evaluatePlain d
      = (show Multiset (Tuple T (n₁ + n₂)) from (leftOuter φ q₁ q₂).evaluatePlain d)
        + (Multiset.map
            (fun v : Tuple T n₂ =>
              (Fin.append (fun _ : Fin n₁ => ValueTypeNull.null) v :
                Tuple T (n₁ + n₂)))
            (Multiset.filter (fun v => v ∉ matchedRight φ q₁ q₂ d)
              (show Multiset (Tuple T n₂) from q₂.evaluatePlain d))
           : Multiset (Tuple T (n₁ + n₂))) := by
  show (show Multiset (Tuple T (n₁ + n₂)) from (leftOuter φ q₁ q₂).evaluatePlain d)
      + (show Multiset (Tuple T (n₁ + n₂)) from
          (rightUnmatched φ q₁ q₂).evaluatePlain d) = _
  refine congrArg (_ + ·) ?_
  unfold rightUnmatched
  rw [evaluatePlain_padLeft]
  refine congrArg (Multiset.map _) ?_
  show Multiset.filter _ _ = _
  exact Multiset.filter_congr (fun v _ => by
    rw [matchedRight, AggQuery.evaluatePlain_castKind]
    rfl)

end Outer

end AggQuery
