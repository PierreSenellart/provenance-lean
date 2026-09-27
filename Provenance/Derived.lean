/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Data.Finset.Sort

import Provenance.AggQuerySubst

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

The semijoin and the antijoin apply the left arm to a scalar aggregation
of the filtered right one, so that each occurrence of the left arm keeps
its multiplicity – a grouping on the left arm's columns would merge its
duplicates, which `WHERE EXISTS` does not – and so that a row with no
match still has its row, with count `𝟘`. Comparing that count against
`𝟘` is what tells the two apart. Over plain relations the decorrelation
`R - Π(σ_φ(R × Q))` gives the same rows, but not the same annotations,
which is why the apply is needed here.

Truncation filters the rank and drops the rank column, so a row tied with
the last one kept is kept too. Grouping sets are the union of one
aggregation per set of the family, each padded back onto the columns of
the whole key, which is what `pad` is for.

A `FILTER` clause is not an operator either: the aggregate reads its
term through SQL's `CASE`, and the input policy – null-skipping or
counting – drops what the clause nulls out.

A `DISTINCT` aggregate deduplicates the key columns together with the
aggregated term and aggregates the added column. Over annotated relations
that is what gives each distinct value one occurrence, annotated by the
`⊕` of the occurrences it stands for; over plain ones it is the aggregate
read over the distinct values (`SeqAggFunc.distinct`).
-/

variable {T : Type} {n m : ℕ}

namespace AggQueryIn

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
  rw [AggQueryIn.evaluatePlain_castKind]
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
  simp only [AggQueryIn.evaluatePlain_castKind, AggQueryIn.evaluatePlain]
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
  simp only [AggQueryIn.evaluatePlain_castKind, AggQueryIn.evaluatePlain]
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
    rw [matchedLeft, AggQueryIn.evaluatePlain_castKind]
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
  simp only [AggQueryIn.evaluatePlain_castKind, AggQueryIn.evaluatePlain]
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
    rw [matchedRight, AggQueryIn.evaluatePlain_castKind]
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
    rw [matchedRight, AggQueryIn.evaluatePlain_castKind]
    rfl)

end Outer

/-! ## Semijoin and antijoin

`R ⋉_φ Q` keeps the occurrences of `R` that `φ` matches with some row of
`Q`, and `R ▷_φ Q` those it matches with none. Both are read off one
query: the apply of `R` to the scalar aggregation that counts the
matches, followed by a comparison of that count against `𝟘` and a
projection back onto `R`'s columns. The counted column `kap` is one that
is never null in a row of `Q` – a key column, or a constant `1` added to
`Q` – so that the count is `𝟘` exactly where nothing matches. -/

section Semijoin

variable [ValueType T] {k l : ℕ}

/-- The kind vector of a match-count row: the left arm's columns
followed by the count. -/
abbrev countKinds (k : ℕ) : Fin (k + 1) → ColKind :=
  Fin.append (ColKind.allReg k) (fun _ : Fin 1 => ColKind.agg)

/-- The column a match count appends. -/
abbrev countCol (k : ℕ) : Fin (k + 1) := Fin.natAdd k 0

theorem countKinds_countCol (k : ℕ) : countKinds k (countCol k) = ColKind.agg :=
  Fin.append_right _ _ 0

/-- **The match count**: one row per occurrence of `R`, carrying that
occurrence and the token that counts, with `cnt` over the column `kap`,
the rows of `Q` the condition `φ` matches it with. The aggregation is
the scalar one, which has its row even where nothing matches. -/
def matchCount (cnt : SeqAggFunc T) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (R : AggQuery T k (ColKind.allReg k))
    (Q : AggQueryIn T k l (ColKind.allReg l)) :
    AggQuery T (k + 1) (countKinds k) :=
  Apply R (GammaScalar ![TermIn.index kap] ![cnt] (Sel φ Q))

/-- The projection that keeps the left arm's columns and drops the
count. -/
def dropCount (k : ℕ) : Tuple (ProjCol T (countKinds k)) k :=
  fun i => .term (TermGIn.index (Fin.castAdd 1 i) (Fin.append_left _ _ i))

/-- **Semijoin**: the occurrences of `R` that `φ` matches with at least
one row of `Q`. -/
def semijoin (cnt : SeqAggFunc T) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (R : AggQuery T k (ColKind.allReg k))
    (Q : AggQueryIn T k l (ColKind.allReg l)) :
    AggQuery T k (ColKind.allReg k) :=
  Proj (dropCount k)
    (Sel (GenPredIn.aggCmp (countCol k) (countKinds_countCol k) CompOp.ne
        (TermGIn.const 0))
      (matchCount cnt kap φ R Q))

/-- **Antijoin**: the occurrences of `R` that `φ` matches with no row of
`Q`. -/
def antijoin (cnt : SeqAggFunc T) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (R : AggQuery T k (ColKind.allReg k))
    (Q : AggQueryIn T k l (ColKind.allReg l)) :
    AggQuery T k (ColKind.allReg k) :=
  Proj (dropCount k)
    (Sel (GenPredIn.aggCmp (countCol k) (countKinds_countCol k) CompOp.eq
        (TermGIn.const 0))
      (matchCount cnt kap φ R Q))

end Semijoin

/-! ## Offset functions

`first_value` and `last_value` read one end of a frame; `lag` and `lead`
read the frames of the rows strictly before and strictly after. All four
are the window operator with `PICKFIRST`, the aggregate that takes the
first value of the sequence it is given, so what tells them apart is the
frame and the order the frame is read in – the two jobs the clause does,
which the window operator keeps separate because the frame is an
argument of its own. A value at an offset other than one needs an
aggregate that reads a position other than the end, `SeqAggFunc.pickNth`,
and `nthValue`, `lagAt` and `leadAt` are the same three queries over
it. -/

section Offset

variable [ValueType T] {n m p : ℕ}

/-- `first_value(t)` over the frame `w`: the value of `t` on the first row
of the frame in the clause's order. -/
def firstValue (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : Term T n)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  Win P O o w t SeqAggFunc.pickFirst q

/-- `last_value(t)`: the same frame, read backwards. Only the reading
order is reversed – the frame is an argument, so a frame the clause
bounds is still bounded by the clause as it stands. -/
def lastValue (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : Term T n)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  Win P O o.reverse w t SeqAggFunc.pickFirst q

/-- `lag(t)`: `last_value` over the rows strictly before the current
row's peers. -/
def lag (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (t : Term T n) (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  lastValue P O o (ValueFrame.rangeBefore o) t q

/-- `lead(t)`: `first_value` over the rows strictly after. -/
def lead (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (t : Term T n) (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  firstValue P O o (ValueFrame.rangeAfter o) t q

/-- `nth_value(t, i+1)` over the frame `w`: the value of `t` on the row
at offset `i` of the frame in the clause's order, counting from `0`.
`firstValue` is the case `i = 0`. -/
def nthValue (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (i : ℕ) (t : Term T n)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  Win P O o w t (SeqAggFunc.pickNth i) q

/-- `lag(t, i+1)`: the value `i + 1` rows before the current row's
peers, the frame of `lag` read backwards from its end. -/
def lagAt (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (i : ℕ) (t : Term T n) (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  nthValue P O o.reverse (ValueFrame.rangeBefore o) i t q

/-- `lead(t, i+1)`: the value `i + 1` rows after. -/
def leadAt (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (i : ℕ) (t : Term T n) (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  nthValue P O o (ValueFrame.rangeAfter o) i t q

theorem lagAt_zero (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (t : Term T n)
    (q : AggQuery T n (ColKind.allReg n)) :
    lagAt P O o 0 t q = lag P O o t q := by
  unfold lagAt nthValue lag lastValue
  rw [SeqAggFunc.pickNth_zero]

theorem leadAt_zero (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (t : Term T n)
    (q : AggQuery T n (ColKind.allReg n)) :
    leadAt P O o 0 t q = lead P O o t q := by
  unfold leadAt nthValue lead firstValue
  rw [SeqAggFunc.pickNth_zero]

end Offset

/-! ## Ranks

SQL's ranks are counts over the rows the clause sorts strictly before the
current row's peers, plus one. The `+ 1` is a term over an aggregate
column, so the rank column is an aggregate column too – the unary
aggregate expression of `Provenance.AggExpr`, which
`ProjColIn.aggTerm` names and `AggValue.postcomp` represents. -/

section Ranks

variable [ValueType T] {n m p : ℕ}

/-- The projection that keeps a window's input columns and reads its
added column through `gf`. -/
def overWindow (n : ℕ) (gf : T → T) :
    Tuple (ProjCol T (Fin.snoc (ColKind.allReg n) ColKind.agg)) (n + 1) :=
  Fin.snoc (fun i => .term (TermGIn.index i.castSucc (by simp [ColKind.allReg])))
    (.aggTerm (Fin.last n) (by simp) gf)

omit [ValueType T] in
@[simp] theorem overWindow_kind (n : ℕ) (gf : T → T) (j : Fin (n + 1)) :
    (overWindow n gf j).kind
      = (Fin.snoc (ColKind.allReg n) ColKind.agg : Fin (n + 1) → ColKind) j
        := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [overWindow, Fin.snoc_last, Fin.snoc_last]
    rfl
  · rw [overWindow, Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl

/-- **`rank()`**: one plus the count of the rows the clause sorts
strictly before the current row's peers. `cnt` is the counting
aggregate, read over the constant term – SQL's `COUNT(*)`. -/
def rank [One T] (cnt : SeqAggFunc T) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  (Proj (overWindow n (fun x => 1 + x))
    (Win P O o (ValueFrame.rangeBefore o) (TermIn.const 1) cnt q)).castKind
      (funext (overWindow_kind n _))

/-- **What a rank computes over plain relations**: each row of the input,
extended by one plus the count over the rows the clause sorts strictly
before its peers. -/
theorem evaluatePlain_rank [One T] (cnt : SeqAggFunc T)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (q : AggQuery T n (ColKind.allReg n)) (D : Database T) :
    (rank cnt P O o q).evaluatePlain D
      = (q.evaluatePlain D).map (fun u =>
          (Fin.snoc u (1 + ValueFrame.windowValue P O o
              (ValueFrame.rangeBefore o) (TermIn.const (c := 0) 1) cnt
              (q.evaluatePlain D) u)
            : Tuple T (n + 1))) := by
  rw [rank, AggQueryIn.evaluatePlain_castKind, AggQueryIn.evaluatePlain,
    AggQueryIn.evaluatePlain_Win_eq, Multiset.map_map]
  refine Multiset.map_congr rfl (fun u _ => ?_)
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j <;>
    simp [overWindow, ProjColIn.evalPlain, TermGIn.evalPlain]

end Ranks

/-! ## Truncation

`λ^{P,O}_{m,c}` keeps the occurrences with at least `m` and fewer than
`m + c` rows ranked strictly before them in their partition: it filters
the rank and drops the rank column again. Rows tied with the last one
kept are kept too, the rank counting the rows strictly before a row's
peers – SQL's `FETCH FIRST c ROWS WITH TIES`. An infinite count is
`truncateFrom`, the same query with the upper bound dropped. -/

section Truncation

variable [ValueType T] {n m p : ℕ}

/-- The projection that drops the rank column a truncation filters on. -/
def dropRank (n : ℕ) :
    Tuple (ProjCol T (Fin.snoc (ColKind.allReg n) ColKind.agg)) n :=
  fun i => .term (TermGIn.index i.castSucc (by simp [ColKind.allReg]))

/-- The range of ranks a truncation keeps: more than `lo` rows ranked
strictly before the row's peers, and at most `hi`. -/
def rankRange (n : ℕ) (lo hi : T) :
    GenPred T (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  .and (.aggCmp (Fin.last n) (by simp) CompOp.gt (.const lo))
    (.aggCmp (Fin.last n) (by simp) CompOp.le (.const hi))

/-- **Truncation** `λ^{P,O}_{m,c}`. -/
def truncate [One T] (cnt : SeqAggFunc T) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (lo hi : T)
    (q : AggQuery T n (ColKind.allReg n)) : AggQuery T n (ColKind.allReg n) :=
  Proj (dropRank n) (Sel (rankRange n lo hi) (rank cnt P O o q))

theorem evaluatePlain_truncate [One T] (cnt : SeqAggFunc T)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p) (lo hi : T)
    (q : AggQuery T n (ColKind.allReg n)) (D : Database T) :
    (truncate cnt P O o lo hi q).evaluatePlain D
      = (q.evaluatePlain D).filter (fun u =>
          (rankRange n lo hi).holdsPlain
            (Fin.snoc u (1 + ValueFrame.windowValue P O o
              (ValueFrame.rangeBefore o) (TermIn.const (c := 0) 1) cnt
              (q.evaluatePlain D) u))) := by
  rw [truncate, AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain,
    evaluatePlain_rank]
  rw [Multiset.filter_map, Multiset.map_map]
  simp only [Function.comp_def]
  refine Eq.trans (Multiset.map_congr rfl (fun u _ => ?_)) (Multiset.map_id' _)
  funext j
  show ProjColIn.evalPlain (dropRank n j) _ = _
  rw [dropRank]
  show (Fin.snoc u _ : Tuple T (n + 1)) j.castSucc = _
  rw [Fin.snoc_castSucc]

theorem holdsPlain_rankRange [NoNulls T] (n : ℕ) (lo hi : T)
    (u : Tuple T (n + 1)) :
    (rankRange n lo hi).holdsPlain u
      ↔ (lo < u (Fin.last n)) ∧ (u (Fin.last n) ≤ hi) := by
  rw [rankRange, GenPredIn.holdsPlain_and]
  show (CompOp.gt.eval3 (u (Fin.last n)) lo = Kleene.true)
      ∧ (CompOp.le.eval3 (u (Fin.last n)) hi = Kleene.true) ↔ _
  rw [CompOp.eval3_eq_true_iff_noNulls, CompOp.eval3_eq_true_iff_noNulls]
  exact Iff.rfl

/-- **What a truncation keeps over plain relations**: the rows with at
least `lo` and at most `hi` rows ranked strictly before their peers. -/
theorem evaluatePlain_truncate_noNulls [NoNulls T] [One T] (cnt : SeqAggFunc T)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p) (lo hi : T)
    (q : AggQuery T n (ColKind.allReg n)) (D : Database T) :
    (truncate cnt P O o lo hi q).evaluatePlain D
      = (q.evaluatePlain D).filter (fun u =>
          (lo < 1 + ValueFrame.windowValue P O o (ValueFrame.rangeBefore o)
              (TermIn.const (c := 0) (1 : T)) cnt (q.evaluatePlain D) u)
            ∧ (1 + ValueFrame.windowValue P O o (ValueFrame.rangeBefore o)
              (TermIn.const (c := 0) (1 : T)) cnt (q.evaluatePlain D) u ≤ hi)) := by
  rw [evaluatePlain_truncate]
  refine Multiset.filter_congr (fun u _ => ?_)
  rw [holdsPlain_rankRange, Fin.snoc_last]

/-- The lower half of the range: at least `lo` rows ranked strictly
before the row's peers. It is what an infinite count asks for – SQL's
`OFFSET` with no `LIMIT`. -/
def rankFrom (n : ℕ) (lo : T) :
    GenPred T (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  .aggCmp (Fin.last n) (by simp) CompOp.gt (.const lo)

/-- **`SELECT DISTINCT ON (P) … ORDER BY P, O`**: one row per partition,
the first in the clause's order, which is the truncation
`λ^{P,O}_{0,1}` – and, with peers, the rows tied with it. -/
def distinctOn [One T] (cnt : SeqAggFunc T) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p)
    (q : AggQuery T n (ColKind.allReg n)) : AggQuery T n (ColKind.allReg n) :=
  truncate cnt P O o 0 1 q

/-- **Truncation with an infinite count**, `λ^{P,O}_{m,∞}`. -/
def truncateFrom [One T] (cnt : SeqAggFunc T) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (lo : T)
    (q : AggQuery T n (ColKind.allReg n)) : AggQuery T n (ColKind.allReg n) :=
  Proj (dropRank n) (Sel (rankFrom n lo) (rank cnt P O o q))

theorem evaluatePlain_truncateFrom [One T] (cnt : SeqAggFunc T)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p) (lo : T)
    (q : AggQuery T n (ColKind.allReg n)) (D : Database T) :
    (truncateFrom cnt P O o lo q).evaluatePlain D
      = (q.evaluatePlain D).filter (fun u =>
          (rankFrom n lo).holdsPlain
            (Fin.snoc u (1 + ValueFrame.windowValue P O o
              (ValueFrame.rangeBefore o) (TermIn.const (c := 0) 1) cnt
              (q.evaluatePlain D) u))) := by
  rw [truncateFrom, AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain,
    evaluatePlain_rank]
  rw [Multiset.filter_map, Multiset.map_map]
  simp only [Function.comp_def]
  refine Eq.trans (Multiset.map_congr rfl (fun u _ => ?_)) (Multiset.map_id' _)
  funext j
  show ProjColIn.evalPlain (dropRank n j) _ = _
  rw [dropRank]
  show (Fin.snoc u _ : Tuple T (n + 1)) j.castSucc = _
  rw [Fin.snoc_castSucc]

theorem holdsPlain_rankFrom [NoNulls T] (n : ℕ) (lo : T)
    (u : Tuple T (n + 1)) :
    (rankFrom n lo).holdsPlain u ↔ (lo < u (Fin.last n)) := by
  show (CompOp.gt.eval3 (u (Fin.last n)) lo = Kleene.true) ↔ _
  rw [CompOp.eval3_eq_true_iff_noNulls]
  exact Iff.rfl

/-- **What an offset with no limit keeps over plain relations.** -/
theorem evaluatePlain_truncateFrom_noNulls [NoNulls T] [One T]
    (cnt : SeqAggFunc T) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (lo : T) (q : AggQuery T n (ColKind.allReg n))
    (D : Database T) :
    (truncateFrom cnt P O o lo q).evaluatePlain D
      = (q.evaluatePlain D).filter (fun u =>
          (lo < 1 + ValueFrame.windowValue P O o (ValueFrame.rangeBefore o)
            (TermIn.const (c := 0) (1 : T)) cnt (q.evaluatePlain D) u)) := by
  rw [evaluatePlain_truncateFrom]
  refine Multiset.filter_congr (fun u _ => ?_)
  rw [holdsPlain_rankFrom, Fin.snoc_last]

end Truncation

/-! ## Grouping sets

`γ_𝒮[t₁:f₁,…,tₙ:fₙ](q)` is the union, over the sets of the family, of the
aggregation on the indices that set keeps, padded back onto the columns
of the whole key: a key column a set drops is the null there. Each arm
therefore has the same columns – the whole key, then the aggregates –
and the union is a union of the algebra. It is what SQL's `GROUPING
SETS`, `ROLLUP` and `CUBE` name. -/

section GroupingSets

variable [ValueTypeNull T] {c k m na : ℕ}

/-- The position of a grouping index inside a grouping set. -/
abbrev gsPos (S : Finset (Fin m)) (a : Fin m) (ha : a ∈ S) : Fin S.card :=
  (S.orderIsoOfFin rfl).symm ⟨a, ha⟩

/-- The projection that pads a grouping set's result back onto the
columns of the whole key: a key column the set drops becomes the null,
one it keeps is read where the aggregation put it, and the aggregate
columns follow. -/
def gsCol (S : Finset (Fin m)) (na : ℕ) (j : Fin (m + na)) :
    ProjColIn T c (Fin.append (fun _ : Fin S.card => ColKind.reg)
      (fun _ : Fin na => ColKind.agg)) :=
  Fin.addCases
    (fun a : Fin m =>
      if ha : a ∈ S then
        .term (TermGIn.index (Fin.castAdd na (gsPos S a ha))
          (Fin.append_left _ _ _))
      else .term (TermGIn.const ValueTypeNull.null))
    (fun l : Fin na => .token (Fin.natAdd S.card l) (Fin.append_right _ _ l))
    j

theorem gsCol_kind (S : Finset (Fin m)) (na : ℕ) (j : Fin (m + na)) :
    (gsCol (T := T) (c := c) S na j).kind
      = Fin.append (fun _ : Fin m => ColKind.reg)
          (fun _ : Fin na => ColKind.agg) j := by
  refine Fin.addCases (fun a => ?_) (fun l => ?_) j
  · rw [gsCol, Fin.addCases_left, Fin.append_left]
    split <;> rfl
  · rw [gsCol, Fin.addCases_right, Fin.append_right]
    rfl

/-- **One grouping set**: the aggregation on the indices the set keeps,
padded back onto the columns of the whole key. -/
def gammaSet (is : Tuple (Fin k) m) (ts : Tuple (TermIn T c k) na)
    (fs : Tuple (SeqAggFunc T) na) (S : Finset (Fin m))
    (q : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c (m + na)
      (Fin.append (fun _ : Fin m => ColKind.reg)
        (fun _ : Fin na => ColKind.agg)) :=
  (Proj (gsCol S na) (Gamma (fun a => is ((S.orderIsoOfFin rfl) a)) ts fs q)).castKind
    (funext (gsCol_kind S na))

/-- **Grouping sets**: the union of the aggregations over each set of the
family, all padded onto the same columns. -/
def gammaSets (is : Tuple (Fin k) m) (ts : Tuple (TermIn T c k) na)
    (fs : Tuple (SeqAggFunc T) na) (S₀ : Finset (Fin m))
    (𝒮 : List (Finset (Fin m))) (q : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c (m + na)
      (Fin.append (fun _ : Fin m => ColKind.reg)
        (fun _ : Fin na => ColKind.agg)) :=
  𝒮.foldr (fun S acc => Sum (gammaSet is ts fs S q) acc) (gammaSet is ts fs S₀ q)

/-- The row a grouping set's padding builds: the null where the set drops
a key column, the aggregation's column where it keeps it, then the
aggregates. -/
def gsRow (S : Finset (Fin m)) (na : ℕ) (v : Tuple T (S.card + na)) :
    Tuple T (m + na) :=
  Fin.addCases
    (fun a : Fin m => if ha : a ∈ S then v (Fin.castAdd na (gsPos S a ha))
      else ValueTypeNull.null)
    (fun l : Fin na => v (Fin.natAdd S.card l))

/-- **What one grouping set computes over plain relations**: the rows of
the aggregation on the indices it keeps, padded. -/
theorem evaluatePlain_gammaSet (is : Tuple (Fin k) m)
    (ts : Tuple (TermIn T c k) na) (fs : Tuple (SeqAggFunc T) na)
    (S : Finset (Fin m)) (q : AggQueryIn T c k (ColKind.allReg k))
    (D : Database T) {γ : Fin c → T} :
    (gammaSet is ts fs S q).evaluatePlain D γ
      = ((Gamma (fun a => is ((S.orderIsoOfFin rfl) a)) ts fs
          q).evaluatePlain D γ).map (gsRow S na) := by
  rw [gammaSet, AggQueryIn.evaluatePlain_castKind, AggQueryIn.evaluatePlain]
  refine Multiset.map_congr rfl (fun v _ => funext fun j => ?_)
  show (gsCol S na j).evalPlain v γ = gsRow S na v j
  refine Fin.addCases (fun a => ?_) (fun l => ?_) j
  · rw [gsCol, Fin.addCases_left, gsRow, Fin.addCases_left]
    split <;> rfl
  · rw [gsCol, Fin.addCases_right, gsRow, Fin.addCases_right]
    rfl

/-- **What grouping sets compute over plain relations**: the union of
what each set of the family computes. -/
theorem evaluatePlain_gammaSets (is : Tuple (Fin k) m)
    (ts : Tuple (TermIn T c k) na) (fs : Tuple (SeqAggFunc T) na)
    (S₀ : Finset (Fin m)) (𝒮 : List (Finset (Fin m)))
    (q : AggQueryIn T c k (ColKind.allReg k)) (D : Database T)
    {γ : Fin c → T} :
    (gammaSets is ts fs S₀ 𝒮 q).evaluatePlain D γ
      = 𝒮.foldr (fun S acc => (gammaSet is ts fs S q).evaluatePlain D γ + acc)
          ((gammaSet is ts fs S₀ q).evaluatePlain D γ) := by
  induction 𝒮 with
  | nil => rfl
  | cons S l ih =>
    show (Sum (gammaSet is ts fs S q) _).evaluatePlain D γ = _
    rw [AggQueryIn.evaluatePlain, List.foldr_cons]
    exact congrArg (fun x => (gammaSet is ts fs S q).evaluatePlain D γ + x) ih

end GroupingSets



/-! ## `DISTINCT` aggregates

`γ_i[t:f^distinct](q)` is the aggregate of the distinct values of `t` in
each group. It is an abbreviation: deduplicate the key columns together
with `t`, then aggregate the added column. Over annotated relations that
is what gives each distinct value one occurrence, annotated by the `⊕` of
the occurrences it stands for – the reading of the paper – and the group,
its key and its existence factor are those of the deduplicated projection,
which are those of the input.

The `DISTINCT` of a *window* aggregate is not this: the frame's
occurrences would have to be merged by value in place, which the window
operator does not do. Only the grouped and the scalar forms are here. -/

section Distinct

variable [ValueType T] {c n₁ : ℕ}

/-- The projection `Π_{#i₁,…,#i_{n₁},t}` that a `DISTINCT` aggregate
deduplicates. -/
def distinctCols (is : Tuple (Fin m) n₁) (t : TermIn T c m) :
    Tuple (ProjColIn T c (ColKind.allReg m)) (n₁ + 1) :=
  fun j => .term ((Fin.snoc (fun k => (TermIn.index (is k)).toGen) t.toGen :
    Fin (n₁ + 1) → TermGIn T c (ColKind.allReg m)) j)

omit [ValueType T] in
@[simp] theorem distinctCols_kind (is : Tuple (Fin m) n₁) (t : TermIn T c m)
    (j : Fin (n₁ + 1)) : (distinctCols is t j).kind = ColKind.reg := rfl

/-- The row that projection builds: the key columns followed by the value
of the aggregated term. -/
def distinctRow (is : Tuple (Fin m) n₁) (t : TermIn T c m)
    (γ : Fin c → T := fun _ => 0) (u : Tuple T m) : Tuple T (n₁ + 1) :=
  Fin.snoc (fun k => u (is k)) (t.eval u γ)

theorem evaluatePlain_distinctProj (is : Tuple (Fin m) n₁) (t : TermIn T c m)
    (q : AggQueryIn T c m (ColKind.allReg m)) (D : Database T)
    {γ : Fin c → T} :
    ((Proj (distinctCols is t) q).castKind
        (funext (distinctCols_kind is t))).evaluatePlain D γ
      = (q.evaluatePlain D γ).map (distinctRow is t γ) := by
  rw [AggQueryIn.evaluatePlain_castKind, AggQueryIn.evaluatePlain]
  refine Multiset.map_congr rfl (fun u _ => funext fun j => ?_)
  show (distinctCols is t j).evalPlain u γ = _
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [distinctCols, Fin.snoc_last, distinctRow, Fin.snoc_last]
    exact TermIn.evalPlain_toGen t u γ
  · rw [distinctCols, Fin.snoc_castSucc, distinctRow, Fin.snoc_castSucc]
    rfl

/-- **Deduplicating the projection does not change the groups**: a key is
one of the deduplicated projection exactly when it is one of the input. -/
theorem keys_distinctRow (is : Tuple (Fin m) n₁) (t : TermIn T c m)
    (r : Multiset (Tuple T m)) {γ : Fin c → T} :
    (((r.map (distinctRow is t γ)).dedup).map
        (fun v => (fun k => v k.castSucc : Tuple T n₁))).dedup
      = (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup := by
  refine (Multiset.Nodup.ext (Multiset.nodup_dedup _)
    (Multiset.nodup_dedup _)).mpr (fun g => ?_)
  simp only [Multiset.mem_dedup, Multiset.mem_map]
  constructor
  · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, funext fun k => by rw [distinctRow, Fin.snoc_castSucc]⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨distinctRow is t γ u, ⟨u, hu, rfl⟩, funext fun k => ?_⟩
    rw [distinctRow, Fin.snoc_castSucc]

/-- **What the deduplicated projection leaves a group to aggregate**: the
distinct values of the term over that group, in some order. -/
theorem groupSeq_distinctRow_perm (is : Tuple (Fin m) n₁) (t : TermIn T c m)
    (r : Multiset (Tuple T m)) (g : Tuple T n₁) {γ : Fin c → T} :
    ((Relation.groupSeq (fun k : Fin n₁ => k.castSucc)
        ((r.map (distinctRow is t γ)).dedup) g).map
        (fun v => v (Fin.last n₁))).Perm
      (((Relation.groupSeq is r g).map (fun v => t.eval v γ)).dedup) := by
  have hmem : ∀ a : T,
      a ∈ ((Relation.groupSeq (fun k : Fin n₁ => k.castSucc)
          ((r.map (distinctRow is t γ)).dedup) g).map
          (fun v => v (Fin.last n₁)))
        ↔ ∃ u ∈ r, (∀ k, u (is k) = g k) ∧ t.eval u γ = a := by
    intro a
    simp only [List.mem_map, Relation.mem_groupSeq, Multiset.mem_dedup,
      Multiset.mem_map]
    constructor
    · rintro ⟨v, ⟨⟨u, hu, rfl⟩, hk⟩, rfl⟩
      refine ⟨u, hu, fun k => ?_, ?_⟩
      · rw [← hk k, distinctRow, Fin.snoc_castSucc]
      · rw [distinctRow, Fin.snoc_last]
    · rintro ⟨u, hu, hk, rfl⟩
      refine ⟨distinctRow is t γ u, ⟨⟨u, hu, rfl⟩, fun k => ?_⟩, ?_⟩
      · rw [distinctRow, Fin.snoc_castSucc]; exact hk k
      · rw [distinctRow, Fin.snoc_last]
  refine (List.perm_ext_iff_of_nodup ?_ (List.nodup_dedup _)).mpr (fun a => ?_)
  · refine List.Nodup.map_on (fun v hv w hw hvw => ?_)
      (Relation.nodup_groupSeq _ (Multiset.nodup_dedup _) g)
    rw [Relation.mem_groupSeq] at hv hw
    funext j
    refine Fin.lastCases hvw (fun i => ?_) j
    rw [hv.2 i, hw.2 i]
  · rw [hmem a, List.mem_dedup, List.mem_map]
    constructor
    · rintro ⟨u, hu, hk, rfl⟩
      exact ⟨u, Relation.mem_groupSeq.mpr ⟨hu, hk⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rw [Relation.mem_groupSeq] at hu
      exact ⟨u, hu.1, hu.2, rfl⟩

/-- **A `DISTINCT` aggregate**, `γ_i[t:f^distinct](q)`: deduplicate the
key columns together with the aggregated term, then aggregate the added
column over each group. -/
def gammaDistinct (is : Tuple (Fin m) n₁) (t : TermIn T c m)
    (f : SeqAggFunc T) (q : AggQueryIn T c m (ColKind.allReg m)) :
    AggQueryIn T c (n₁ + 1)
      (Fin.append (fun _ => ColKind.reg) (fun _ => ColKind.agg)) :=
  Gamma (fun k => k.castSucc) ![TermIn.index (Fin.last n₁)] ![f]
    (Dedup ((Proj (distinctCols is t) q).castKind (funext (distinctCols_kind is t))))

/-- **What a `DISTINCT` aggregate computes over plain relations**: the
aggregate, read through `SeqAggFunc.distinct`, of the term over each
group. The aggregate has to be symmetric, the two readings sequencing the
distinct values of a group differently. -/
theorem evaluatePlain_gammaDistinct (is : Tuple (Fin m) n₁) (t : TermIn T c m)
    {f : SeqAggFunc T} (hf : f.Symmetric)
    (q : AggQueryIn T c m (ColKind.allReg m)) (D : Database T)
    {γ : Fin c → T} :
    (gammaDistinct is t f q).evaluatePlain D γ
      = (Gamma is ![t] ![f.distinct] q).evaluatePlain D γ := by
  simp only [gammaDistinct, AggQueryIn.evaluatePlain, evaluatePlain_distinctProj]
  rw [keys_distinctRow]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  refine congrArg (Fin.append g) (funext fun j => ?_)
  obtain rfl : j = 0 := Fin.fin_one_eq_zero j
  simp only [Matrix.cons_val_zero]
  show f (List.map (fun v : Tuple T (n₁ + 1) => v (Fin.last n₁)) _)
    = f (List.map (fun v : Tuple T m => t.eval v γ) _).dedup
  exact hf (groupSeq_distinctRow_perm is t _ g)

/-- **A `DISTINCT` aggregate without grouping**: the same abbreviation
with no key column, so that the deduplication is that of the values of
the term alone. -/
def gammaScalarDistinct (t : TermIn T c m) (f : SeqAggFunc T)
    (q : AggQueryIn T c m (ColKind.allReg m)) :
    AggQueryIn T c 1 (fun _ => ColKind.agg) :=
  GammaScalar ![TermIn.index (Fin.last 0)] ![f]
    (Dedup ((Proj (distinctCols (fun k : Fin 0 => k.elim0) t) q).castKind
      (funext (distinctCols_kind _ t))))

/-- **What a `DISTINCT` aggregate without grouping computes over plain
relations**: the aggregate of the distinct values of the term over the
whole input. -/
theorem evaluatePlain_gammaScalarDistinct (t : TermIn T c m)
    {f : SeqAggFunc T} (hf : f.Symmetric)
    (q : AggQueryIn T c m (ColKind.allReg m)) (D : Database T)
    {γ : Fin c → T} :
    (gammaScalarDistinct t f q).evaluatePlain D γ
      = (GammaScalar ![t] ![f.distinct] q).evaluatePlain D γ := by
  simp only [gammaScalarDistinct, AggQueryIn.evaluatePlain,
    evaluatePlain_distinctProj]
  refine congrArg (fun u => (Multiset.ofList [u] : Relation T 1)) (funext fun j => ?_)
  obtain rfl : j = 0 := Fin.fin_one_eq_zero j
  simp only [Matrix.cons_val_zero]
  show f (List.map (fun v : Tuple T (0 + 1) => v (Fin.last 0)) _)
    = f (List.map (fun v : Tuple T m => t.eval v γ) _).dedup
  exact hf (groupSeq_distinctRow_perm _ t _ _)

end Distinct

/-! ## The `FILTER` clause

`f(t) FILTER (WHERE φ)` restricts what the aggregate reads. Over a
null-skipping aggregate it is `f` over `CASE WHEN φ THEN t END`, and over
a count it is the same term read through the counting policy: both
policies drop the nulls, so nulling out the occurrences the clause
rejects is exactly leaving them out of the sequence. The group, its key
and its annotation are those of all the occurrences – a filtered-out
occurrence still witnesses its group – which is why the clause belongs
in the term and not in a selection under the aggregation.

A guard that is a Boolean combination of comparisons needs nothing more:
a conjunction is a nested `CASE`, a disjunction a `COALESCE` of the two
cases, and a negation `CompOp.negate`.

The third input policy is not here. A null-keeping aggregate reads every
value, the null included, so it cannot tell an occurrence the clause
rejects from one whose term is null; SQL removes the rejected ones from
the sequence, which no term can do and which the aggregation operators
would have to be told about. -/

section Filter

variable [ValueTypeNull T] {c n m : ℕ}

/-- The term a `FILTER` clause makes an aggregate read: the aggregated
term where the clause holds, the null where it does not. -/
def filterTerm (op : CompOp) (t₁ t₂ t : TermIn T c n) : TermIn T c n :=
  .caseWhen op t₁ t₂ t (.const ValueTypeNull.null)

/-- Whether a `FILTER` clause holds on a row. -/
def filterHolds (op : CompOp) (t₁ t₂ : TermIn T c n) (γ : Fin c → T)
    (u : Tuple T n) : Bool :=
  decide (op.eval3 (t₁.eval u γ) (t₂.eval u γ) = Kleene.true)

theorem notNull_eq (a : T) :
    decide (a ≠ ValueTypeNull.null) = !ValueType.isNull a := by
  rw [ValueTypeNull.isNull_iff]
  simp

theorem eval_filterTerm (op : CompOp) (t₁ t₂ t : TermIn T c n)
    (u : Tuple T n) (γ : Fin c → T) :
    (filterTerm op t₁ t₂ t).eval u γ
      = if filterHolds op t₁ t₂ γ u then t.eval u γ
        else ValueTypeNull.null := by
  rw [filterTerm, TermIn.eval, filterHolds]
  simp only [decide_eq_true_eq]
  rfl

theorem filter_map_filterTerm (op : CompOp) (t₁ t₂ t : TermIn T c n)
    (γ : Fin c → T) (L : List (Tuple T n)) :
    (L.map (fun u => (filterTerm op t₁ t₂ t).eval u γ)).filter
        (fun a => !ValueType.isNull a)
      = ((L.filter (filterHolds op t₁ t₂ γ)).map
          (fun u => t.eval u γ)).filter (fun a => !ValueType.isNull a) := by
  induction L with
  | nil => rfl
  | cons u L ih =>
    rw [List.map_cons, eval_filterTerm]
    by_cases h : filterHolds op t₁ t₂ γ u = true <;>
      simp [h, List.filter_cons, ih]

/-- **What a `FILTER` clause makes a null-skipping aggregate read**: the
values of the occurrences the clause keeps. Nulling out the others and
skipping them is the same as leaving them out of the sequence. -/
theorem sqlOf_map_filterTerm (f : SeqAggFunc T) (op : CompOp)
    (t₁ t₂ t : TermIn T c n) (γ : Fin c → T) (L : List (Tuple T n)) :
    f.sqlOf (L.map (fun u => (filterTerm op t₁ t₂ t).eval u γ))
      = f.sqlOf ((L.filter (filterHolds op t₁ t₂ γ)).map
          (fun u => t.eval u γ)) := by
  unfold SeqAggFunc.sqlOf
  simp only [notNull_eq, filter_map_filterTerm]

/-- **What a `FILTER` clause makes a count read**: the same. -/
theorem counting_map_filterTerm (f : SeqAggFunc T) (op : CompOp)
    (t₁ t₂ t : TermIn T c n) (γ : Fin c → T) (L : List (Tuple T n)) :
    f.counting (L.map (fun u => (filterTerm op t₁ t₂ t).eval u γ))
      = f.counting ((L.filter (filterHolds op t₁ t₂ γ)).map
          (fun u => t.eval u γ)) := by
  unfold SeqAggFunc.counting
  rw [filter_map_filterTerm]

/-- **An aggregation with a `FILTER` clause**: the aggregate reads the
term through the clause. The aggregate comes already read through its
input policy – `SeqAggFunc.sqlOf` for a null-skipping aggregate,
`SeqAggFunc.counting` for a count – and it is that policy which drops
the occurrences the clause nulls out. -/
def gammaFilter {m n₁ : ℕ} (is : Tuple (Fin m) n₁) (op : CompOp)
    (t₁ t₂ t : TermIn T c m) (f : SeqAggFunc T)
    (q : AggQueryIn T c m (ColKind.allReg m)) :
    AggQueryIn T c (n₁ + 1)
      (Fin.append (fun _ => ColKind.reg) (fun _ => ColKind.agg)) :=
  Gamma is ![filterTerm op t₁ t₂ t] ![f] q

/-- **A window aggregate with a `FILTER` clause.** -/
def winFilter {n mp p : ℕ} (P : Tuple (Fin n) mp) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (op : CompOp)
    (t₁ t₂ t : TermIn T c n) (f : SeqAggFunc T)
    (q : AggQueryIn T c n (ColKind.allReg n)) :
    AggQueryIn T c (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  Win P O o w (filterTerm op t₁ t₂ t) f q

/-- **What a filtered null-skipping aggregation computes over plain
relations**: each group's aggregate reads the occurrences of the group
the clause keeps. The group itself is unchanged – a filtered-out
occurrence still witnesses it. -/
theorem evaluatePlain_gammaFilter_sqlOf {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (op : CompOp) (t₁ t₂ t : TermIn T c m) (f : SeqAggFunc T)
    (q : AggQueryIn T c m (ColKind.allReg m)) (D : Database T)
    {γ : Fin c → T} :
    (gammaFilter is op t₁ t₂ t f.sqlOf q).evaluatePlain D γ
      = ((q.evaluatePlain D γ).map
          (fun u => (fun k => u (is k) : Tuple T n₁))).dedup.map
          (fun g => Fin.append g (fun _ : Fin 1 =>
            f.sqlOf (((Relation.groupSeq is (q.evaluatePlain D γ) g).filter
              (filterHolds op t₁ t₂ γ)).map (fun v => t.eval v γ)))) := by
  rw [gammaFilter, AggQueryIn.evaluatePlain]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  refine congrArg (Fin.append g) (funext fun j => ?_)
  obtain rfl : j = 0 := Fin.fin_one_eq_zero j
  simp only [Matrix.cons_val_zero]
  exact sqlOf_map_filterTerm f op t₁ t₂ t γ _

/-- **What a filtered count computes over plain relations**: the same,
the counting policy dropping the occurrences the clause nulls out. -/
theorem evaluatePlain_gammaFilter_counting {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (op : CompOp) (t₁ t₂ t : TermIn T c m) (f : SeqAggFunc T)
    (q : AggQueryIn T c m (ColKind.allReg m)) (D : Database T)
    {γ : Fin c → T} :
    (gammaFilter is op t₁ t₂ t f.counting q).evaluatePlain D γ
      = ((q.evaluatePlain D γ).map
          (fun u => (fun k => u (is k) : Tuple T n₁))).dedup.map
          (fun g => Fin.append g (fun _ : Fin 1 =>
            f.counting (((Relation.groupSeq is (q.evaluatePlain D γ) g).filter
              (filterHolds op t₁ t₂ γ)).map (fun v => t.eval v γ)))) := by
  rw [gammaFilter, AggQueryIn.evaluatePlain]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  refine congrArg (Fin.append g) (funext fun j => ?_)
  obtain rfl : j = 0 := Fin.fin_one_eq_zero j
  simp only [Matrix.cons_val_zero]
  exact counting_map_filterTerm f op t₁ t₂ t γ _

/-- **What a filtered window aggregate reads**: the rows of the frame the
clause keeps. -/
theorem windowValue_filterTerm_sqlOf {n mp p : ℕ} (P : Tuple (Fin n) mp)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (op : CompOp) (t₁ t₂ t : TermIn T c n) (f : SeqAggFunc T)
    (R : Relation T n) (u : Tuple T n) (γ : Fin c → T) :
    ValueFrame.windowValue P O o w (filterTerm op t₁ t₂ t) f.sqlOf R u γ
      = f.sqlOf (((ValueFrame.frameListOf (α := Tuple T n) id P O o w R u).filter
          (filterHolds op t₁ t₂ γ)).map (fun v => t.eval v γ)) :=
  sqlOf_map_filterTerm f op t₁ t₂ t γ _

/-- **What a filtered window count reads**: the same. -/
theorem windowValue_filterTerm_counting {n mp p : ℕ} (P : Tuple (Fin n) mp)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (op : CompOp) (t₁ t₂ t : TermIn T c n) (f : SeqAggFunc T)
    (R : Relation T n) (u : Tuple T n) (γ : Fin c → T) :
    ValueFrame.windowValue P O o w (filterTerm op t₁ t₂ t) f.counting R u γ
      = f.counting (((ValueFrame.frameListOf (α := Tuple T n) id P O o w R u).filter
          (filterHolds op t₁ t₂ γ)).map (fun v => t.eval v γ)) :=
  counting_map_filterTerm f op t₁ t₂ t γ _

end Filter


end AggQueryIn
