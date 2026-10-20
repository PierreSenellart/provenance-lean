import Provenance.SymPass

/-!
# The difference in place of the selection

`{∅, Π, −, apply, γ, win, μ^⊎}` generates the whole algebra in the
minimal universe: a selection is an apply of its input with a closed test
that holds the empty tuple once where the predicate is true at the row and
nothing elsewhere. The tests are built from the difference alone, except
for the order: `x < y` is read by a window counting, over the relation
`{x, y}` (a bag recursion of one round), the rows strictly before `y`, and
that count is compared with `0` as a key, which `Explode` allows.
-/

variable {T : Type} [ValueType T]

/-- **The classes of the basis with the difference in place of the
selection**: `∅`, `Π`, `−`, the apply, `γ`, `win`, `μ^⊎`. -/
def basisRecDiffOps : Set OpKind :=
  {OpKind.empty, OpKind.proj, OpKind.diff, OpKind.apply, OpKind.gamma, OpKind.win,
    OpKind.muBag}

namespace DiffBasis

/-! ## Truth values as relations of arity `0` -/

/-- A relation read as the bag of its rows. -/
abbrev rows {k : ℕ} (X : Relation T k) : Multiset (Tuple T k) := X

/-- The value an expression names: a constant, or a position of the
context. -/
def val {C : ℕ} (γ : Fin C → T) (e : T ⊕ Fin C) : T := _root_.Sum.elim id γ e

/-- The relation of arity `0` holding the empty tuple once where `b`
holds, and nothing elsewhere. -/
def boolRel (b : Bool) : Multiset (Tuple T 0) := if b then {fun k => k.elim0} else 0

omit [ValueType T] in
theorem tuple0_eq (u v : Tuple T 0) : u = v := funext fun k => k.elim0

omit [ValueType T] in
theorem mem_boolRel {b : Bool} {u : Tuple T 0} : u ∈ boolRel b ↔ b = true := by
  cases b
  · simp [boolRel]
  · simp only [boolRel, ite_true, Multiset.mem_singleton, iff_true]
    exact tuple0_eq _ _

/-- One row, of the value `e` names. -/
def param1 {C : ℕ} (e : T ⊕ Fin C) : AggQueryIn T C 1 (ColKind.allReg 1) :=
  AggQueryIn.Param (fun _ => e) (ColKind.allReg 1)

theorem evaluatePlain_param1 {C : ℕ} (e : T ⊕ Fin C) (D : Database T) (γ : Fin C → T) :
    (param1 e).evaluatePlain D γ = ({fun _ => val γ e} : Multiset (Tuple T 1)) := rfl

/-- Every row projected onto no column. -/
def proj0 {C k : ℕ} (q : AggQueryIn T C k (ColKind.allReg k)) :
    AggQueryIn T C 0 (ColKind.allReg 0) :=
  (AggQueryIn.Proj (fun j : Fin 0 => j.elim0) q).castKind (funext fun j => j.elim0)

theorem evaluatePlain_proj0 {C k : ℕ} (q : AggQueryIn T C k (ColKind.allReg k))
    (D : Database T) (γ : Fin C → T) :
    (proj0 q).evaluatePlain D γ
      = (q.evaluatePlain D γ : Multiset (Tuple T k)).map (fun _ => fun j => j.elim0) := by
  rw [proj0, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  exact Multiset.map_congr rfl fun _ _ => funext fun j => j.elim0

theorem evaluatePlain_diff {C k : ℕ} (X Y : AggQueryIn T C k (ColKind.allReg k))
    (D : Database T) (γ : Fin C → T) :
    (AggQueryIn.Diff X Y).evaluatePlain D γ
      = (X.evaluatePlain D γ : Multiset (Tuple T k)).filter
          (fun t => t ∉ rows (Y.evaluatePlain D γ)) := rfl

/-- A bag of rows read as a relation. -/
abbrev rel {k : ℕ} (X : Multiset (Tuple T k)) : Relation T k := X

/-- The rows of `X` that are rows of `Y`, by two differences. -/
def inter {C k : ℕ} (X Y : AggQueryIn T C k (ColKind.allReg k)) :
    AggQueryIn T C k (ColKind.allReg k) :=
  AggQueryIn.Diff X (AggQueryIn.Diff X Y)

theorem evaluatePlain_inter {C k : ℕ} (X Y : AggQueryIn T C k (ColKind.allReg k))
    (D : Database T) (γ : Fin C → T) :
    (inter X Y).evaluatePlain D γ
      = (X.evaluatePlain D γ : Multiset (Tuple T k)).filter
          (fun t => t ∈ rows (Y.evaluatePlain D γ)) := by
  rw [inter, evaluatePlain_diff, evaluatePlain_diff]
  refine Multiset.filter_congr fun t ht => ?_
  rw [Multiset.mem_filter]
  tauto

/-- Truth negated: the unit minus the test. -/
def notT {C : ℕ} (A : AggQueryIn T C 0 (ColKind.allReg 0)) :
    AggQueryIn T C 0 (ColKind.allReg 0) :=
  AggQueryIn.Diff AggQueryIn.unitC A

/-- Both tests hold. -/
def andT {C : ℕ} (A B : AggQueryIn T C 0 (ColKind.allReg 0)) :
    AggQueryIn T C 0 (ColKind.allReg 0) := inter A B

/-- One of the two tests holds. -/
def orT {C : ℕ} (A B : AggQueryIn T C 0 (ColKind.allReg 0)) :
    AggQueryIn T C 0 (ColKind.allReg 0) := notT (andT (notT A) (notT B))

variable {C : ℕ} {D : Database T} {γ : Fin C → T}

theorem evaluatePlain_notT {A : AggQueryIn T C 0 (ColKind.allReg 0)} {a : Bool}
    (hA : A.evaluatePlain D γ = boolRel a) : (notT A).evaluatePlain D γ = boolRel (!a) := by
  rw [notT, evaluatePlain_diff, hA, AggQueryIn.evaluatePlain_unitC D γ (fun k => k.elim0)]
  cases a
  · simp [boolRel]
  · simp only [boolRel, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [Multiset.filter_singleton, ite_eq_right (by simp)]
    rfl

theorem evaluatePlain_andT {A B : AggQueryIn T C 0 (ColKind.allReg 0)} {a b : Bool}
    (hA : A.evaluatePlain D γ = boolRel a) (hB : B.evaluatePlain D γ = boolRel b) :
    (andT A B).evaluatePlain D γ = boolRel (a && b) := by
  rw [andT, evaluatePlain_inter, hA, hB]
  cases a
  · simp [boolRel]
  · simp only [boolRel, ite_true, Bool.true_and]
    rw [Multiset.filter_singleton]
    cases b
    · simp
    · simp

theorem evaluatePlain_orT {A B : AggQueryIn T C 0 (ColKind.allReg 0)} {a b : Bool}
    (hA : A.evaluatePlain D γ = boolRel a) (hB : B.evaluatePlain D γ = boolRel b) :
    (orT A B).evaluatePlain D γ = boolRel (a || b) := by
  rw [orT, evaluatePlain_notT (evaluatePlain_andT (evaluatePlain_notT hA)
    (evaluatePlain_notT hB))]
  cases a <;> cases b <;> rfl

/-! ## Equality and nulls -/

/-- The two values are equal. -/
def eqT (a b : T ⊕ Fin C) : AggQueryIn T C 0 (ColKind.allReg 0) :=
  proj0 (inter (param1 a) (param1 b))

theorem evaluatePlain_eqT (a b : T ⊕ Fin C) :
    (eqT a b).evaluatePlain D γ = boolRel (decide (val γ a = val γ b)) := by
  rw [eqT, evaluatePlain_proj0, evaluatePlain_inter, evaluatePlain_param1,
    evaluatePlain_param1, Multiset.filter_singleton]
  by_cases h : val γ a = val γ b
  · rw [ite_eq_left (by rw [h]; exact Multiset.mem_singleton_self _), decide_eq_true h]
    simp [boolRel]
  · rw [ite_eq_right (fun hm => h (congrFun (Multiset.mem_singleton.mp hm) 0)), decide_eq_false h]
    simp [boolRel]

/-- The value is not null. -/
def nnT (a : T ⊕ Fin C) : AggQueryIn T C 0 (ColKind.allReg 0) :=
  match (ValueType.nullVal : Option T) with
  | none => AggQueryIn.unitC
  | some ν => notT (eqT a (_root_.Sum.inl ν))

theorem evaluatePlain_nnT (a : T ⊕ Fin C) :
    (nnT a).evaluatePlain D γ = boolRel (!ValueType.isNull (val γ a)) := by
  unfold nnT
  split
  · next h =>
    rw [AggQueryIn.evaluatePlain_unitC D γ (fun k => k.elim0)]
    have : ValueType.isNull (val γ a) = false := by
      cases hn : ValueType.isNull (val γ a)
      · rfl
      · rw [ValueType.isNull_iff_nullVal, h] at hn
        cases hn
    rw [this]
    rfl
  · next ν h =>
    rw [evaluatePlain_notT (evaluatePlain_eqT a _)]
    congr 1
    cases hn : ValueType.isNull (val γ a)
    · have : val γ a ≠ ν := fun he => by
        rw [he, (ValueType.isNull_iff_nullVal ν).mpr h] at hn
        cases hn
      show (!decide (val γ a = ν)) = !false
      rw [decide_eq_false this]
    · have he : ValueType.nullVal = some (val γ a) := ValueType.isNull_iff_nullVal _ |>.mp hn
      rw [h] at he
      have : val γ a = ν := (Option.some.inj he).symm
      show (!decide (val γ a = ν)) = !true
      rw [decide_eq_true this]

/-! ## The order -/

/-- An expression read one position further in, past the row of an
apply's left side. -/
def liftE (e : T ⊕ Fin C) : T ⊕ Fin (1 + C) := _root_.Sum.map id (Fin.natAdd 1) e

omit [ValueType T] in
theorem val_liftE (e : T ⊕ Fin C) (u : Tuple T 1) :
    val (Fin.append u γ) (liftE e) = val γ e := by
  cases e with
  | inl a => rfl
  | inr j => exact Fin.append_right u γ j

/-- **The round of the recursion building `{a, b}`**: the row of `b`, once
per row of the recursive relation other than `b`. -/
def stepBody (s : String) (b : T ⊕ Fin C) : AggQueryIn T C 1 (ColKind.allReg 1) [(s, 1)] :=
  (AggQueryIn.Proj (fun _ : Fin 1 => ProjColIn.term
      (TermGIn.index (κ := Fin.append (ColKind.allReg 1) (ColKind.allReg 1))
        (Fin.natAdd 1 (0 : Fin 1)) (Fin.append_right _ _ 0)))
    (AggQueryIn.Apply (AggQueryIn.Hole 1 s)
      (AggQueryIn.Diff (param1 (liftE b))
        (param1 (_root_.Sum.inr (Fin.castAdd C 0)))))).castKind (funext fun _ => rfl)

theorem evaluatePlain_stepBody (s : String) (b : T ⊕ Fin C) (X : Relation T 1) :
    (stepBody s b).evaluatePlain (D.assign s X) γ
      = (rows X).bind (fun u => if u 0 = val γ b then 0
          else ({fun _ => val γ b} : Multiset (Tuple T 1))) := by
  rw [stepBody, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain, Database.find_assign]
  rw [Multiset.map_bind]
  refine Multiset.bind_congr fun u _ => ?_
  have h1 : val (Fin.append u γ) (liftE b) = val γ b := val_liftE b u
  have h2 : val (Fin.append u γ) (_root_.Sum.inr (Fin.castAdd C 0)) = u 0 :=
    Fin.append_left u γ 0
  rw [evaluatePlain_param1, evaluatePlain_param1, h1, h2, Multiset.filter_singleton]
  by_cases h : u 0 = val γ b
  · rw [ite_eq_right (fun hm => hm (by rw [h]; exact Multiset.mem_singleton_self _)),
      ite_eq_left h]
    rfl
  · rw [ite_eq_left (fun hm => h (congrFun (Multiset.mem_singleton.mp hm) 0).symm),
      ite_eq_right h, Multiset.map_singleton, Multiset.map_singleton]
    congr 1

/-- The row of a value. -/
def r1 (a : T) : Tuple T 1 := fun _ => a

/-- **`{a, b}`** – `{a}` where the two are equal – as a bag recursion of
one round from `a`. -/
def pairZ (s : String) (a b : T ⊕ Fin C) : AggQueryIn T C 1 (ColKind.allReg 1) :=
  AggQueryIn.Mu s (param1 a) (stepBody s b)

theorem settlesAt_stepBody (s : String) (b : T ⊕ Fin C) (D : Database T) (γ : Fin C → T) :
    (stepBody s b).SettlesAt D γ := by
  rw [stepBody, AggQueryIn.settlesAt_castKind]
  exact ⟨trivial, fun _ _ => ⟨trivial, trivial⟩⟩

theorem pairZ_spec (s : String) (a b : T ⊕ Fin C) :
    (pairZ s a b).SettlesAt D γ ∧ (pairZ s a b).evaluatePlain D γ
      = if val γ a = val γ b then ({r1 (val γ a)} : Multiset (Tuple T 1))
        else r1 (val γ a) ::ₘ {r1 (val γ b)} := by
  set step : Multiset (Tuple T 1) → Multiset (Tuple T 1) :=
    fun X => (stepBody s b).evaluatePlain (D.assign s X) γ with hstep
  have hs : ∀ X, step X = (rows X).bind (fun u => if u 0 = val γ b then 0
      else ({fun _ => val γ b} : Multiset (Tuple T 1))) :=
    fun X => evaluatePlain_stepBody s b X
  have h0 : step 0 = 0 := by rw [hs]; rfl
  have hM : (param1 (C := C) a).evaluatePlain D γ = ({r1 (val γ a)} : Multiset (Tuple T 1)) :=
    rfl
  have hone : ∀ x, step {r1 x} = if x = val γ b then 0 else {r1 (val γ b)} := fun x => by
    rw [hs]
    exact Multiset.singleton_bind _ _
  by_cases hab : val γ a = val γ b
  · have hk : step^[0 + 1] ((param1 (C := C) a).evaluatePlain D γ) = 0 := by
      rw [Function.iterate_one, hM, hone, ite_eq_left hab]
    refine ⟨⟨trivial, h0, ⟨0, hk⟩, fun _ => settlesAt_stepBody s b _ γ⟩, ?_⟩
    rw [ite_eq_left hab]
    show muSumFix step _ = _
    rw [muSumFix_eq_of_empty h0 hk, hM]
    rfl
  · have h1 : step ((param1 (C := C) a).evaluatePlain D γ) = {r1 (val γ b)} := by
      rw [hM, hone, ite_eq_right hab]
    have hk : step^[1 + 1] ((param1 (C := C) a).evaluatePlain D γ) = 0 := by
      rw [Function.iterate_succ_apply', Function.iterate_one, h1, hone, ite_eq_left rfl]
    refine ⟨⟨trivial, h0, ⟨1, hk⟩, fun _ => settlesAt_stepBody s b _ γ⟩, ?_⟩
    rw [ite_eq_right hab]
    show muSumFix step _ = _
    rw [muSumFix_eq_of_empty h0 hk]
    rw [muSum, muSum, h1, hM]
    exact Multiset.singleton_add _ _

/-- **A way to build `{a, b}`** from two expressions, at every context. -/
abbrev PairQ (T : Type) [ValueType T] : Type :=
  ∀ {C : ℕ}, T ⊕ Fin C → T ⊕ Fin C → AggQueryIn T C 1 (ColKind.allReg 1)

/-- **What `{a, b}` is asked**: defined everywhere, `{a}` where the two
are equal and `{a, b}` otherwise. -/
def PairSpec (pr : PairQ T) : Prop :=
  ∀ {C : ℕ} (a b : T ⊕ Fin C) (D : Database T) (γ : Fin C → T),
    (pr a b).SettlesAt D γ ∧ (pr a b).evaluatePlain D γ
      = if val γ a = val γ b then ({r1 (val γ a)} : Multiset (Tuple T 1))
        else r1 (val γ a) ::ₘ {r1 (val γ b)}

/-- `{a, b}` by a bag recursion of one round. -/
def prZ (s : String) : PairQ T := fun a b => pairZ s a b

theorem pairSpec_prZ (s : String) : PairSpec (prZ (T := T) s) :=
  fun a b D γ => pairZ_spec (D := D) (γ := γ) s a b

/-- **The frame of the rows strictly before the current one**, its peers
and itself excluded. -/
def beforeW : ValueFrame T 1 := ⟨FrameCond.lt (OrderSpec.asc 1), false⟩

/-- No partition. -/
def P0 : Tuple (Fin 1) 0 := fun j => j.elim0

/-- Ordered by the one column. -/
def O0 : Tuple (Fin 1) 1 := fun _ => 0

/-- Whether `a` sorts strictly before `b`, ascending. -/
def ltO (a b : T) : Bool := (OrderSpec.asc 1).lt (fun _ => a) (fun _ => b)

theorem frameOf_beforeW (Z : Multiset (Tuple T 1)) (x : Tuple T 1) :
    ValueFrame.frameOf id P0 O0 beforeW Z x
      = (Z.filter (fun y => ltO (y 0) (x 0) = true)).erase x := by
  unfold ValueFrame.frameOf
  rw [ite_eq_right (by simp [beforeW]), Multiset.erase_instEq _ instDecidableEqTuple]
  congr 1
  apply Multiset.filter_congr
  intro y _
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨funext fun j => j.elim0, h⟩

theorem windowValue_beforeW {cnt : SeqAggFunc T} {g : ℕ → T}
    (hg : ∀ L : List T, cnt L = g (L.countP (fun x => !ValueType.isNull x)))
    (Z : Multiset (Tuple T 1)) (x : Tuple T 1) :
    ValueFrame.windowValue P0 O0
        (OrderSpec.asc 1) beforeW (TermIn.index 0) cnt Z x γ
      = g ((((Z.filter (fun y => ltO (y 0) (x 0) = true)).erase x).map
          (fun v => v 0)).countP (fun x => ValueType.isNull x = false)) := by
  unfold ValueFrame.windowValue
  rw [hg, ← frameOf_beforeW, ← ValueFrame.frameListOf_coe, Multiset.map_coe,
    Multiset.coe_countP]
  congr 1
  refine List.countP_congr fun v _ => ?_
  cases ValueType.isNull v <;> simp

theorem kinds_explode :
    Function.update (Fin.snoc (α := fun _ => ColKind) (ColKind.allReg 1) ColKind.agg)
      (Fin.last 1) ColKind.reg = ColKind.allReg 2 := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [Function.update_self]
    rfl
  · rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne, Fin.snoc_castSucc]
    rfl

/-- **`{a, b}` with, on each row, the number of rows strictly before it**,
the count read as a key. -/
def winZ (cnt : SeqAggFunc T) (Z : AggQueryIn T C 1 (ColKind.allReg 1)) :
    AggQueryIn T C 2 (ColKind.allReg 2) :=
  (AggQueryIn.Explode (Fin.last 1) (Fin.snoc_last (α := fun _ => ColKind) _ _)
    (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) (fun j : Fin 0 =>
      j.elim0)
      (fun _ : Fin 1 => (0 : Fin 1)) (OrderSpec.asc 1) beforeW (TermIn.index 0) cnt
      Z (winReadsReg_allReg _ _ _))).castKind kinds_explode

theorem evaluatePlain_winZ (cnt : SeqAggFunc T) (Z : AggQueryIn T C 1 (ColKind.allReg 1)) :
    (winZ cnt Z).evaluatePlain D γ
      = (rows (Z.evaluatePlain D γ)).map (fun x : Tuple T 1 => (Fin.snoc x
          (ValueFrame.windowValue P0 O0
            (OrderSpec.asc 1) beforeW (TermIn.index 0) cnt
            (rows (Z.evaluatePlain D γ)) x γ) : Tuple T 2)) := by
  rw [winZ, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain, ColKind.readTuple_allReg, Multiset.map_id',
    ValueFrame.windowValueOpt_none]
  rfl

/-- The value an expression names, as a term. -/
def termOf {k : ℕ} {κ : Fin k → ColKind} (e : T ⊕ Fin C) : TermGIn T C κ :=
  match e with
  | .inl a => .const a
  | .inr j => .outer j

theorem evalPlain_termOf {k : ℕ} {κ : Fin k → ColKind} (e : T ⊕ Fin C) (w : Tuple T k) :
    (termOf e : TermGIn T C κ).evalPlain w γ = val γ e := by
  cases e <;> rfl

/-- Each row's count, beside the value `b`. -/
def projB (b : T ⊕ Fin C) (W : AggQueryIn T C 2 (ColKind.allReg 2)) :
    AggQueryIn T C 2 (ColKind.allReg 2) :=
  (AggQueryIn.Proj (Fin.snoc (α := fun _ => ProjColIn T C (ColKind.allReg 2))
      (fun _ : Fin 1 => ProjColIn.term (termOf b))
      (ProjColIn.term (TermGIn.index (Fin.last 1) rfl))) W).castKind (by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last]; rfl
    · rw [Fin.snoc_castSucc]; rfl)

theorem evaluatePlain_projB (b : T ⊕ Fin C) (W : AggQueryIn T C 2 (ColKind.allReg 2)) :
    (projB b W).evaluatePlain D γ
      = (rows (W.evaluatePlain D γ)).map (fun w => (Fin.snoc (r1 (val γ b)) (w (Fin.last 1))
          : Tuple T 2)) := by
  rw [projB, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  refine Multiset.map_congr rfl fun w _ => funext fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last, Fin.snoc_last]
    rfl
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact evalPlain_termOf b w

/-- **`a < b`**, nulls aside: the row of `b` in `{a, b}` has a row strictly
before it. -/
def ltT (cnt : SeqAggFunc T) (pr : PairQ T) (a b : T ⊕ Fin C) :
    AggQueryIn T C 0 (ColKind.allReg 0) :=
  proj0 (AggQueryIn.Diff (inter (winZ cnt (pr a b)) (projB b (winZ cnt (pr a b))))
    (AggQueryIn.Param (Fin.snoc (α := fun _ => T ⊕ Fin C) (fun _ : Fin 1 => b)
      (_root_.Sum.inl 0)) (ColKind.allReg 2)))

omit [ValueType T] in
theorem r1_inj {a b : T} : r1 a = r1 b ↔ a = b :=
  ⟨fun h => congrFun h 0, fun h => h ▸ rfl⟩

theorem ltO_self (a : T) : ltO a a = false := OrderSpec.lt_irrefl _ _

theorem evaluatePlain_ltT {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {pr : PairQ T} (hpr : PairSpec pr)
    (a b : T ⊕ Fin C) :
    (ltT cnt pr a b).evaluatePlain D γ
      = boolRel (ltO (val γ a) (val γ b) && !ValueType.isNull (val γ a)) := by
  obtain ⟨g, hg, -, hg0⟩ := hcnt
  have hW := evaluatePlain_winZ (D := D) (γ := γ) cnt (pr a b)
  rw [(hpr a b D γ).2] at hW
  have hP : (AggQueryIn.Param (Fin.snoc (α := fun _ => T ⊕ Fin C) (fun _ : Fin 1 => b)
      (_root_.Sum.inl 0)) (ColKind.allReg 2)).evaluatePlain D γ
      = ({(Fin.snoc (r1 (val γ b)) 0 : Tuple T 2)} : Multiset (Tuple T 2)) := by
    simp only [AggQueryIn.evaluatePlain]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last]; rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
  rw [ltT, evaluatePlain_proj0, evaluatePlain_diff, evaluatePlain_inter,
    evaluatePlain_projB, hW, hP]
  set va := val γ a
  set vb := val γ b
  by_cases hab : va = vb
  · rw [ite_eq_left hab]
    have hc : ValueFrame.windowValue P0 O0 (OrderSpec.asc 1) beforeW (TermIn.index 0) cnt
        (rel {r1 va}) (r1 va) γ = 0 := by
      rw [windowValue_beforeW hg, Multiset.filter_singleton, ite_eq_right (by
        show ¬ ltO va va = true
        rw [ltO_self]; simp)]
      exact (hg0 _).mpr rfl
    rw [← hab, ltO_self]
    simp only [rows, Multiset.map_singleton, Multiset.filter_singleton]
    erw [hc]
    simp only [Fin.snoc_last, Multiset.mem_singleton, ite_true, Multiset.filter_singleton,
      not_true_eq_false, ite_false, Bool.false_and]
    rfl
  · rw [ite_eq_right hab]
    have hne : r1 va ≠ r1 vb := fun h => hab (r1_inj.mp h)
    have hcb : ValueFrame.windowValue P0 O0 (OrderSpec.asc 1) beforeW (TermIn.index 0) cnt
        (rel (r1 va ::ₘ {r1 vb})) (r1 vb) γ
          = g (if (ltO va vb && !ValueType.isNull va) = true then 1 else 0) := by
      rw [windowValue_beforeW hg]
      congr 1
      rw [Multiset.filter_cons, Multiset.filter_singleton,
        ite_eq_right (show ¬ ltO (r1 vb 0) (r1 vb 0) = true by rw [ltO_self]; simp),
        Multiset.empty_eq_zero, add_zero]
      cases h : ltO va vb
      · rw [ite_eq_right (show ¬ ltO (r1 va 0) (r1 vb 0) = true by
          show ¬ ltO va vb = true; rw [h]; simp)]
        simp
      · rw [ite_eq_left (show ltO (r1 va 0) (r1 vb 0) = true from h),
          Multiset.erase_of_notMem (fun hm => hne (Multiset.mem_singleton.mp hm).symm)]
        show Multiset.countP _ ((va ::ₘ 0 : Multiset T)) = _
        rw [Multiset.countP_cons]
        cases hn : ValueType.isNull va <;> simp
    simp only [rows, Multiset.map_cons, Multiset.map_singleton]
    erw [hcb]
    have hx : ∀ c c' : T, ¬ (Fin.snoc (r1 va) c : Tuple T 2) = Fin.snoc (r1 vb) c' :=
      fun c c' h => hne (Fin.snoc_injective2 h).1
    simp only [Fin.snoc_last, Multiset.filter_cons, Multiset.filter_singleton,
      Multiset.mem_cons, Multiset.mem_singleton, hx, false_or, or_true, ite_true, ite_false,
      zero_add]
    cases hB : (ltO va vb && !ValueType.isNull va)
    · have h0 : g 0 = 0 := (hg0 0).mpr rfl
      simp only [Bool.false_eq_true, ite_false, h0, not_true_eq_false]
      rfl
    · have h1 : g 1 ≠ 0 := fun h => one_ne_zero ((hg0 1).mp h)
      have : ¬ (Fin.snoc (r1 vb) (g 1) : Tuple T 2) = Fin.snoc (r1 vb) 0 :=
        fun h => h1 (Fin.snoc_injective2 h).2
      simp only [ite_true, this, not_false_eq_true]
      rfl

/-- On two values of the domain, the ascending order is the domain's. -/
theorem ltO_eq {a b : T} (ha : ValueType.isNull a = false) (hb : ValueType.isNull b = false) :
    ltO a b = decide (a < b) := by
  unfold ltO OrderSpec.lt OrderSpec.le
  simp only [List.finRange_succ, List.finRange_zero, List.map_nil,
    OrderSpec.leOn, OrderSpec.asc, OrderCol.ASC, OrderCol.peer, OrderCol.le, ha, hb,
    Bool.false_eq_true, ite_false]
  by_cases h : b ≤ a
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

theorem evaluatePlain_ltT_of {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {pr : PairQ T} (hpr : PairSpec pr)
    (a b : T ⊕ Fin C) (ha : ValueType.isNull (val γ a) = false)
    (hb : ValueType.isNull (val γ b) = false) :
    (ltT cnt pr a b).evaluatePlain D γ = boolRel (decide (val γ a < val γ b)) := by
  rw [evaluatePlain_ltT hcnt hpr, ltO_eq ha hb, ha]
  simp

/-! ## Comparisons, in Kleene's logic -/

/-- The comparison holds, read two-valued: the order through `ltT`, the
equalities through `eqT`. -/
def opE (cnt : SeqAggFunc T) (pr : PairQ T) (op : CompOp) (a b : T ⊕ Fin C) :
    AggQueryIn T C 0 (ColKind.allReg 0) :=
  match op with
  | .eq => eqT a b
  | .syneq => eqT a b
  | .ne => notT (eqT a b)
  | .synne => notT (eqT a b)
  | .lt => ltT cnt pr a b
  | .gt => ltT cnt pr b a
  | .le => notT (ltT cnt pr b a)
  | .ge => notT (ltT cnt pr a b)

theorem evaluatePlain_opE {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {pr : PairQ T} (hpr : PairSpec pr) (op : CompOp)
    (a b : T ⊕ Fin C) (ha : ValueType.isNull (val γ a) = false)
    (hb : ValueType.isNull (val γ b) = false) :
    (opE cnt pr op a b).evaluatePlain D γ = boolRel (decide (op.eval (val γ a) (val γ b))) := by
  cases op
  · exact evaluatePlain_eqT a b
  · rw [opE, evaluatePlain_notT (evaluatePlain_eqT a b)]
    simp [CompOp.eval]
  · exact evaluatePlain_ltT_of hcnt hpr a b ha hb
  · rw [opE, evaluatePlain_notT (evaluatePlain_ltT_of hcnt hpr b a hb ha)]
    congr 1
    by_cases h : val γ b < val γ a
    · simp [CompOp.eval, h, not_le.mpr h]
    · simp [CompOp.eval, h, not_lt.mp h]
  · rw [opE, evaluatePlain_ltT_of hcnt hpr b a hb ha]
    simp [CompOp.eval]
  · rw [opE, evaluatePlain_notT (evaluatePlain_ltT_of hcnt hpr a b ha hb)]
    congr 1
    by_cases h : val γ a < val γ b
    · simp [CompOp.eval, h, not_le.mpr h]
    · simp [CompOp.eval, h, not_lt.mp h]
  · exact evaluatePlain_eqT a b
  · rw [opE, evaluatePlain_notT (evaluatePlain_eqT a b)]
    simp [CompOp.eval]

/-- **A comparison's truth and falsity**: for a null-strict one, both
values non-null and the comparison, or its negation; for `IS [NOT]
DISTINCT FROM`, equality, which is never unknown. -/
def cmpTF (cnt : SeqAggFunc T) (pr : PairQ T) (op : CompOp) (a b : T ⊕ Fin C) :
    AggQueryIn T C 0 (ColKind.allReg 0) × AggQueryIn T C 0 (ColKind.allReg 0) :=
  match op with
  | .syneq => (eqT a b, notT (eqT a b))
  | .synne => (notT (eqT a b), eqT a b)
  | op => (andT (nnT a) (andT (nnT b) (opE cnt pr op a b)),
      andT (nnT a) (andT (nnT b) (notT (opE cnt pr op a b))))

omit [ValueType T] in
theorem boolRel_inj {a b : Bool} (h : (boolRel a : Multiset (Tuple T 0)) = boolRel b) : a = b := by
  cases a <;> cases b <;> simp_all [boolRel]

theorem exists_evaluatePlain_opE {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {pr : PairQ T} (hpr : PairSpec pr)
    (op : CompOp) (a b : T ⊕ Fin C) :
    ∃ e, (opE cnt pr op a b).evaluatePlain D γ = boolRel e := by
  cases op
  · exact ⟨_, evaluatePlain_eqT a b⟩
  · exact ⟨_, evaluatePlain_notT (evaluatePlain_eqT a b)⟩
  · exact ⟨_, evaluatePlain_ltT hcnt hpr a b⟩
  · exact ⟨_, evaluatePlain_notT (evaluatePlain_ltT hcnt hpr b a)⟩
  · exact ⟨_, evaluatePlain_ltT hcnt hpr b a⟩
  · exact ⟨_, evaluatePlain_notT (evaluatePlain_ltT hcnt hpr a b)⟩
  · exact ⟨_, evaluatePlain_eqT a b⟩
  · exact ⟨_, evaluatePlain_notT (evaluatePlain_eqT a b)⟩

theorem cmpTF_spec {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {pr : PairQ T} (hpr : PairSpec pr) (op : CompOp)
    (a b : T ⊕ Fin C) :
    (cmpTF cnt pr op a b).1.evaluatePlain D γ
        = boolRel (decide (op.eval3 (val γ a) (val γ b) = Kleene.true))
      ∧ (cmpTF cnt pr op a b).2.evaluatePlain D γ
        = boolRel (decide (op.eval3 (val γ a) (val γ b) = Kleene.false)) := by
  have hstrict : ∀ op' : CompOp, op'.strict = true →
      (andT (nnT a) (andT (nnT b) (opE cnt pr op' a b))).evaluatePlain D γ
          = boolRel (decide (op'.eval3 (val γ a) (val γ b) = Kleene.true))
        ∧ (andT (nnT a) (andT (nnT b) (notT (opE cnt pr op' a b)))).evaluatePlain D γ
          = boolRel (decide (op'.eval3 (val γ a) (val γ b) = Kleene.false)) := by
    intro op' hs
    obtain ⟨e, hE⟩ := exists_evaluatePlain_opE (D := D) (γ := γ) hcnt hpr op' a b
    rw [evaluatePlain_andT (evaluatePlain_nnT a) (evaluatePlain_andT (evaluatePlain_nnT b) hE),
      evaluatePlain_andT (evaluatePlain_nnT a)
        (evaluatePlain_andT (evaluatePlain_nnT b) (evaluatePlain_notT hE))]
    cases ha : ValueType.isNull (val γ a)
    · cases hb : ValueType.isNull (val γ b)
      · have he : e = decide (op'.eval (val γ a) (val γ b)) :=
          boolRel_inj (hE.symm.trans (evaluatePlain_opE hcnt hpr op' a b ha hb))
        subst he
        simp only [CompOp.eval3, hs, ha, hb, Bool.false_eq_true, or_self, and_false, ite_false,
          Bool.not_false, Bool.true_and]
        cases decide (op'.eval (val γ a) (val γ b)) <;> simp [Kleene.ofBool]
      · simp [CompOp.eval3, hs, hb]
    · simp [CompOp.eval3, hs, ha]
  cases op
  all_goals first
    | exact hstrict _ rfl
    | skip
  · show (eqT a b).evaluatePlain D γ = _ ∧ (notT (eqT a b)).evaluatePlain D γ = _
    rw [evaluatePlain_notT (evaluatePlain_eqT a b), evaluatePlain_eqT]
    by_cases h : val γ a = val γ b <;>
      simp [h, CompOp.eval3, CompOp.strict, CompOp.eval, Kleene.ofBool]
  · show (notT (eqT a b)).evaluatePlain D γ = _ ∧ (eqT a b).evaluatePlain D γ = _
    rw [evaluatePlain_notT (evaluatePlain_eqT a b), evaluatePlain_eqT]
    by_cases h : val γ a = val γ b <;>
      simp [h, CompOp.eval3, CompOp.strict, CompOp.eval, Kleene.ofBool]

/-! ## Predicates -/

/-- **A term of the minimal signature as an expression of the test's
context**, the row of the selection's input coming first. -/
def termE {c n : ℕ} {κ : Fin n → ColKind} : TermGIn T c κ → T ⊕ Fin (n + c)
  | .const a => .inl a
  | .outer j => .inr (Fin.natAdd n j)
  | .index k _ => .inr (Fin.castAdd c k)
  | .provIndex k _ => .inr (Fin.castAdd c k)
  | _ => .inl 0

theorem val_termE {c n : ℕ} {κ : Fin n → ColKind} (t : TermGIn T c κ) (ht : t.noFun = true)
    (u : Tuple T n) (γ : Fin c → T) :
    val (Fin.append u γ) (termE t) = t.evalPlain u γ := by
  cases t with
  | const a => rfl
  | outer j => exact Fin.append_right u γ j
  | index k _ => exact Fin.append_left u γ k
  | provIndex k _ => exact Fin.append_left u γ k
  | _ => simp [TermGIn.noFun] at ht

/-- **The test of a predicate, true and false**: the first holds the empty
tuple where the predicate is true at the row, the second where it is
false. -/
def predTF (cnt : SeqAggFunc T) (pr : PairQ T) {c n : ℕ} {κ : Fin n → ColKind} :
    GenPredIn T c κ →
      AggQueryIn T (n + c) 0 (ColKind.allReg 0) × AggQueryIn T (n + c) 0 (ColKind.allReg 0)
  | .cmp op t₁ t₂ => cmpTF cnt pr op (termE t₁) (termE t₂)
  | .aggCmp k _ op t => cmpTF cnt pr op (.inr (Fin.castAdd c k)) (termE t)
  | .aggRange k _ op₁ t₁ op₂ t₂ =>
      (andT (cmpTF cnt pr op₁ (.inr (Fin.castAdd c k)) (termE t₁)).1
          (cmpTF cnt pr op₂ (.inr (Fin.castAdd c k)) (termE t₂)).1,
        orT (cmpTF cnt pr op₁ (.inr (Fin.castAdd c k)) (termE t₁)).2
          (cmpTF cnt pr op₂ (.inr (Fin.castAdd c k)) (termE t₂)).2)
  | .and φ ψ => (andT (predTF cnt pr φ).1 (predTF cnt pr ψ).1,
      orT (predTF cnt pr φ).2 (predTF cnt pr ψ).2)
  | .or φ ψ => (orT (predTF cnt pr φ).1 (predTF cnt pr ψ).1,
      andT (predTF cnt pr φ).2 (predTF cnt pr ψ).2)
  | .not φ => ((predTF cnt pr φ).2, (predTF cnt pr φ).1)

theorem kleene_and_true (x y : Kleene) :
    decide (x.and y = Kleene.true) = (decide (x = Kleene.true) && decide (y = Kleene.true)) := by
  cases x <;> cases y <;> rfl

theorem kleene_and_false (x y : Kleene) :
    decide (x.and y = Kleene.false) = (decide (x = Kleene.false) || decide (y = Kleene.false)) := by
  cases x <;> cases y <;> rfl

theorem kleene_or_true (x y : Kleene) :
    decide (x.or y = Kleene.true) = (decide (x = Kleene.true) || decide (y = Kleene.true)) := by
  cases x <;> cases y <;> rfl

theorem kleene_or_false (x y : Kleene) :
    decide (x.or y = Kleene.false) = (decide (x = Kleene.false) && decide (y = Kleene.false)) := by
  cases x <;> cases y <;> rfl

theorem kleene_not_true (x : Kleene) :
    decide (x.not = Kleene.true) = decide (x = Kleene.false) := by
  cases x <;> rfl

theorem kleene_not_false (x : Kleene) :
    decide (x.not = Kleene.false) = decide (x = Kleene.true) := by
  cases x <;> rfl

theorem predTF_spec {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {pr : PairQ T} (hpr : PairSpec pr) {c n : ℕ}
    {κ : Fin n → ColKind} (φ : GenPredIn T c κ) (hφ : φ.noFun = true) (D : Database T)
    (u : Tuple T n) (γ : Fin c → T) :
    (predTF cnt pr φ).1.evaluatePlain D (Fin.append u γ)
        = boolRel (decide (φ.evalPlain3 u γ = Kleene.true))
      ∧ (predTF cnt pr φ).2.evaluatePlain D (Fin.append u γ)
        = boolRel (decide (φ.evalPlain3 u γ = Kleene.false)) := by
  induction φ with
  | cmp op t₁ t₂ =>
    simp only [GenPredIn.noFun, Bool.and_eq_true] at hφ
    have h := cmpTF_spec (D := D) (γ := Fin.append u γ) hcnt hpr op (termE t₁) (termE t₂)
    rw [val_termE t₁ hφ.1, val_termE t₂ hφ.2] at h
    exact h
  | aggCmp k hk op t =>
    have h := cmpTF_spec (D := D) (γ := Fin.append u γ) hcnt hpr op (.inr (Fin.castAdd c k))
      (termE t)
    have hk' : val (Fin.append u γ) (.inr (Fin.castAdd c k)) = u k := Fin.append_left u γ k
    rw [val_termE t hφ, hk'] at h
    exact h
  | aggRange k hk op₁ t₁ op₂ t₂ =>
    simp only [GenPredIn.noFun, Bool.and_eq_true] at hφ
    have h₁ := cmpTF_spec (D := D) (γ := Fin.append u γ) hcnt hpr op₁ (.inr (Fin.castAdd c k))
      (termE t₁)
    have h₂ := cmpTF_spec (D := D) (γ := Fin.append u γ) hcnt hpr op₂ (.inr (Fin.castAdd c k))
      (termE t₂)
    have hk' : val (Fin.append u γ) (.inr (Fin.castAdd c k)) = u k := Fin.append_left u γ k
    rw [val_termE t₁ hφ.1, hk'] at h₁
    rw [val_termE t₂ hφ.2, hk'] at h₂
    refine ⟨(evaluatePlain_andT h₁.1 h₂.1).trans ?_, (evaluatePlain_orT h₁.2 h₂.2).trans ?_⟩
    · rw [GenPredIn.evalPlain3, kleene_and_true]
    · rw [GenPredIn.evalPlain3, kleene_and_false]
  | and φ ψ ihφ ihψ =>
    simp only [GenPredIn.noFun, Bool.and_eq_true] at hφ
    obtain ⟨h₁, h₂⟩ := ihφ hφ.1
    obtain ⟨h₃, h₄⟩ := ihψ hφ.2
    refine ⟨(evaluatePlain_andT h₁ h₃).trans ?_, (evaluatePlain_orT h₂ h₄).trans ?_⟩
    · rw [GenPredIn.evalPlain3, kleene_and_true]
    · rw [GenPredIn.evalPlain3, kleene_and_false]
  | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.noFun, Bool.and_eq_true] at hφ
    obtain ⟨h₁, h₂⟩ := ihφ hφ.1
    obtain ⟨h₃, h₄⟩ := ihψ hφ.2
    refine ⟨(evaluatePlain_orT h₁ h₃).trans ?_, (evaluatePlain_andT h₂ h₄).trans ?_⟩
    · rw [GenPredIn.evalPlain3, kleene_or_true]
    · rw [GenPredIn.evalPlain3, kleene_or_false]
  | not φ ih =>
    obtain ⟨h₁, h₂⟩ := ih hφ
    refine ⟨h₂.trans ?_, h₁.trans ?_⟩
    · rw [GenPredIn.evalPlain3, kleene_not_true]
    · rw [GenPredIn.evalPlain3, kleene_not_false]

/-! ## The tests are in the fragment -/

/-- **The classes every test uses**: `∅`, `Π`, `−`, `γ` and `win`; the pair
`{a, b}` adds its own. -/
def selTestOps : Set OpKind :=
  {OpKind.empty, OpKind.proj, OpKind.diff, OpKind.gamma, OpKind.win}

/-- **What a closed test is asked**: its classes, its signature, a schema
satisfying `Q`, no relation mentioned, and defined everywhere. -/
structure TestOK (S : Set OpKind) (Θ : Set (SeqAggFunc T)) (Q : Schema → Prop) {C k : ℕ}
    {κ : Fin k → ColKind} (q : AggQueryIn T C k κ) : Prop where
  uses : q.usesOnly S
  sig : q.inSig Θ
  over : ∀ sch : Schema, Q sch → q.overSchema sch
  noM : ∀ x, q.noMention x
  settles : ∀ (D : Database T) (γ : Fin C → T), q.SettlesAt D γ
  preg : q.paramsReg

variable {S : Set OpKind} {Θ : Set (SeqAggFunc T)} {Q : Schema → Prop}

theorem TestOK.castKind {k : ℕ} {κ κ' : Fin k → ColKind} {q : AggQueryIn T C k κ}
    (h : κ = κ') (hq : TestOK S Θ Q q) : TestOK S Θ Q (q.castKind h) where
  uses := (AggQueryIn.usesOnly_castKind h q _).mpr hq.uses
  sig := (AggQueryIn.inSig_castKind h q Θ).mpr hq.sig
  over sch hs := (AggQueryIn.overSchema_castKind h q).mpr (hq.over sch hs)
  noM x := (AggQueryIn.noMention_castKind h q).mpr (hq.noM x)
  settles D γ := (AggQueryIn.settlesAt_castKind h q D γ).mpr (hq.settles D γ)
  preg := (AggQueryIn.paramsReg_castKind h q).mpr hq.preg

theorem testOK_param (hS : selTestOps ⊆ S) {k : ℕ} (pv : Fin k → T ⊕ Fin C) :
    TestOK S Θ Q (AggQueryIn.Param pv (ColKind.allReg k)) where
  uses := ⟨hS (by simp [selTestOps]), hS (by simp [selTestOps]), hS (by simp [selTestOps])⟩
  sig := trivial
  over _ _ := trivial
  noM _ := trivial
  settles _ _ := trivial
  preg _ := rfl

theorem testOK_param1 (hS : selTestOps ⊆ S) (e : T ⊕ Fin C) : TestOK S Θ Q (param1 e) :=
  testOK_param hS _

theorem testOK_diff (hS : selTestOps ⊆ S) {k : ℕ} {X Y : AggQueryIn T C k (ColKind.allReg k)}
    (hX : TestOK S Θ Q X) (hY : TestOK S Θ Q Y) : TestOK S Θ Q (AggQueryIn.Diff X Y) where
  uses := ⟨hS (by simp [selTestOps]), hX.uses, hY.uses⟩
  sig := ⟨hX.sig, hY.sig⟩
  over sch hs := ⟨hX.over sch hs, hY.over sch hs⟩
  noM x := ⟨hX.noM x, hY.noM x⟩
  settles D γ := ⟨hX.settles D γ, hY.settles D γ⟩
  preg := ⟨hX.preg, hY.preg⟩

theorem testOK_unitC (hS : selTestOps ⊆ S) :
    TestOK S Θ Q (AggQueryIn.unitC : AggQueryIn T C 0 _) where
  uses := by
    rw [AggQueryIn.unitC, AggQueryIn.usesOnly_castKind]
    exact ⟨hS (by simp [selTestOps]), hS (by simp [selTestOps])⟩
  sig := AggQueryIn.inSig_unitC Θ
  over sch _ := AggQueryIn.overSchema_unitC sch
  noM x := AggQueryIn.noMention_unitC x
  settles D γ := AggQueryIn.settlesAt_unitC D γ
  preg := by rw [AggQueryIn.unitC, AggQueryIn.paramsReg_castKind]; trivial

theorem testOK_proj0 (hS : selTestOps ⊆ S) {k : ℕ} {q : AggQueryIn T C k (ColKind.allReg k)}
    (hq : TestOK S Θ Q q) : TestOK S Θ Q (proj0 q) :=
  TestOK.castKind _ {
    uses := ⟨⟨hS (by simp [selTestOps]), fun j => j.elim0⟩, hq.uses⟩
    sig := ⟨fun j => j.elim0, hq.sig⟩
    over := fun sch hs => hq.over sch hs
    noM := fun x => hq.noM x
    settles := fun D γ => hq.settles D γ
    preg := hq.preg }

theorem testOK_inter (hS : selTestOps ⊆ S) {k : ℕ} {X Y : AggQueryIn T C k (ColKind.allReg k)}
    (hX : TestOK S Θ Q X) (hY : TestOK S Θ Q Y) : TestOK S Θ Q (inter X Y) :=
  testOK_diff hS hX (testOK_diff hS hX hY)

theorem testOK_notT (hS : selTestOps ⊆ S) {A : AggQueryIn T C 0 (ColKind.allReg 0)}
    (hA : TestOK S Θ Q A) : TestOK S Θ Q (notT A) := testOK_diff hS (testOK_unitC hS) hA

theorem testOK_andT (hS : selTestOps ⊆ S) {A B : AggQueryIn T C 0 (ColKind.allReg 0)}
    (hA : TestOK S Θ Q A) (hB : TestOK S Θ Q B) : TestOK S Θ Q (andT A B) :=
  testOK_inter hS hA hB

theorem testOK_orT (hS : selTestOps ⊆ S) {A B : AggQueryIn T C 0 (ColKind.allReg 0)}
    (hA : TestOK S Θ Q A) (hB : TestOK S Θ Q B) : TestOK S Θ Q (orT A B) :=
  testOK_notT hS (testOK_andT hS (testOK_notT hS hA) (testOK_notT hS hB))

theorem testOK_eqT (hS : selTestOps ⊆ S) (a b : T ⊕ Fin C) : TestOK S Θ Q (eqT a b) :=
  testOK_proj0 hS (testOK_inter hS (testOK_param1 hS a) (testOK_param1 hS b))

theorem testOK_nnT (hS : selTestOps ⊆ S) (a : T ⊕ Fin C) : TestOK S Θ Q (nnT a) := by
  unfold nnT
  split
  · exact testOK_unitC hS
  · exact testOK_notT hS (testOK_eqT hS _ _)

/-- **The pair by a bag recursion** is in the fragment over a schema not
declaring its name. -/
theorem testOK_pairZ (hS : selTestOps ⊆ S) (hmu : OpKind.muBag ∈ S) (hap : OpKind.apply ∈ S)
    (s₀ : String) (a b : T ⊕ Fin C) :
    TestOK S Θ (fun sch => sch s₀ = none) (pairZ s₀ a b) where
  uses := ⟨hmu, (testOK_param1 (Θ := Θ) (Q := fun _ => True) hS a).uses, by
    rw [stepBody, AggQueryIn.usesOnly_castKind]
    exact ⟨⟨hS (by simp [selTestOps]), fun _ => rfl⟩, hap, trivial,
      (testOK_diff (Θ := Θ) (Q := fun _ => True) hS (testOK_param1 hS _)
        (testOK_param1 hS _)).uses⟩⟩
  sig := ⟨trivial, by
    rw [stepBody, AggQueryIn.inSig_castKind]
    exact ⟨fun _ => rfl, trivial, trivial, trivial⟩⟩
  over sch hs := ⟨hs, trivial, by
    rw [stepBody, AggQueryIn.noMention_castKind]
    exact ⟨trivial, trivial, trivial⟩, by
    rw [stepBody, AggQueryIn.overSchema_castKind]
    exact ⟨show (sch.update s₀ 1) s₀ = some 1 by simp, trivial, trivial⟩⟩
  noM x := ⟨trivial, by
    rw [stepBody, AggQueryIn.noMention_castKind]
    exact ⟨trivial, trivial, trivial⟩⟩
  settles D γ := (pairZ_spec (D := D) (γ := γ) s₀ a b).1
  preg := ⟨fun _ => rfl, by
    rw [stepBody, AggQueryIn.paramsReg_castKind]
    exact ⟨trivial, fun _ => rfl, fun _ => rfl⟩⟩

theorem testOK_winZ (hS : selTestOps ⊆ S) {cnt : SeqAggFunc T} (hc : cnt ∈ Θ)
    {Z : AggQueryIn T C 1 (ColKind.allReg 1)} (hZ : TestOK S Θ Q Z) :
    TestOK S Θ Q (winZ cnt Z) :=
  TestOK.castKind _ {
    uses := ⟨hS (by simp [selTestOps]), hZ.uses⟩
    sig := ⟨rfl, by simpa using hc, rfl, rfl, hZ.sig⟩
    over := fun sch hs => hZ.over sch hs
    noM := fun x => hZ.noM x
    settles := fun D γ => hZ.settles D γ
    preg := hZ.preg }

omit [ValueType T] in
theorem noFun_termOf {k : ℕ} {κ : Fin k → ColKind} (e : T ⊕ Fin C) :
    (termOf e : TermGIn T C κ).noFun = true := by
  cases e <;> rfl

theorem testOK_projB (hS : selTestOps ⊆ S) (b : T ⊕ Fin C)
    {W : AggQueryIn T C 2 (ColKind.allReg 2)} (hW : TestOK S Θ Q W) :
    TestOK S Θ Q (projB b W) :=
  TestOK.castKind _ {
    uses := ⟨⟨hS (by simp [selTestOps]), fun j => by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; rfl
      · rw [Fin.snoc_castSucc]; rfl⟩, hW.uses⟩
    sig := ⟨fun j => by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; rfl
      · rw [Fin.snoc_castSucc]; exact noFun_termOf b, hW.sig⟩
    over := fun sch hs => hW.over sch hs
    noM := fun x => hW.noM x
    settles := fun D γ => hW.settles D γ
    preg := hW.preg }

/-- A pair construction whose pairs are in the fragment. -/
def PairOK (S : Set OpKind) (Θ : Set (SeqAggFunc T)) (Q : Schema → Prop) (pr : PairQ T) :
    Prop :=
  ∀ {C : ℕ} (a b : T ⊕ Fin C), TestOK S Θ Q (pr a b)

theorem pairOK_prZ (hS : selTestOps ⊆ S) (hmu : OpKind.muBag ∈ S) (hap : OpKind.apply ∈ S)
    (s₀ : String) : PairOK S Θ (fun sch => sch s₀ = none) (prZ (T := T) s₀) :=
  fun a b => testOK_pairZ hS hmu hap s₀ a b

variable {pr : PairQ T}

theorem testOK_ltT (hS : selTestOps ⊆ S) {cnt : SeqAggFunc T} (hc : cnt ∈ Θ)
    (hpr : PairOK S Θ Q pr) (a b : T ⊕ Fin C) : TestOK S Θ Q (ltT cnt pr a b) :=
  testOK_proj0 hS (testOK_diff hS (testOK_inter hS (testOK_winZ hS hc (hpr a b))
    (testOK_projB hS b (testOK_winZ hS hc (hpr a b)))) (testOK_param hS _))

theorem testOK_opE (hS : selTestOps ⊆ S) {cnt : SeqAggFunc T} (hc : cnt ∈ Θ)
    (hpr : PairOK S Θ Q pr) (op : CompOp) (a b : T ⊕ Fin C) :
    TestOK S Θ Q (opE cnt pr op a b) := by
  cases op
  · exact testOK_eqT hS a b
  · exact testOK_notT hS (testOK_eqT hS a b)
  · exact testOK_ltT hS hc hpr a b
  · exact testOK_notT hS (testOK_ltT hS hc hpr b a)
  · exact testOK_ltT hS hc hpr b a
  · exact testOK_notT hS (testOK_ltT hS hc hpr a b)
  · exact testOK_eqT hS a b
  · exact testOK_notT hS (testOK_eqT hS a b)

theorem testOK_cmpTF (hS : selTestOps ⊆ S) {cnt : SeqAggFunc T} (hc : cnt ∈ Θ)
    (hpr : PairOK S Θ Q pr) (op : CompOp) (a b : T ⊕ Fin C) :
    TestOK S Θ Q (cmpTF cnt pr op a b).1 ∧ TestOK S Θ Q (cmpTF cnt pr op a b).2 := by
  have hg : ∀ op' : CompOp,
      TestOK S Θ Q (andT (nnT a) (andT (nnT b) (opE cnt pr op' a b)))
        ∧ TestOK S Θ Q (andT (nnT a) (andT (nnT b) (notT (opE cnt pr op' a b)))) :=
    fun op' => ⟨testOK_andT hS (testOK_nnT hS a)
        (testOK_andT hS (testOK_nnT hS b) (testOK_opE hS hc hpr op' a b)),
      testOK_andT hS (testOK_nnT hS a) (testOK_andT hS (testOK_nnT hS b)
        (testOK_notT hS (testOK_opE hS hc hpr op' a b)))⟩
  cases op
  all_goals first
    | exact hg _
    | exact ⟨testOK_eqT hS a b, testOK_notT hS (testOK_eqT hS a b)⟩
    | exact ⟨testOK_notT hS (testOK_eqT hS a b), testOK_eqT hS a b⟩

theorem testOK_predTF (hS : selTestOps ⊆ S) {cnt : SeqAggFunc T} (hc : cnt ∈ Θ)
    (hpr : PairOK S Θ Q pr) {c n : ℕ} {κ : Fin n → ColKind} (φ : GenPredIn T c κ) :
    TestOK S Θ Q (predTF cnt pr φ).1 ∧ TestOK S Θ Q (predTF cnt pr φ).2 := by
  induction φ with
  | cmp op t₁ t₂ => exact testOK_cmpTF hS hc hpr op _ _
  | aggCmp k _ op t => exact testOK_cmpTF hS hc hpr op _ _
  | aggRange k _ op₁ t₁ op₂ t₂ =>
    exact ⟨testOK_andT hS (testOK_cmpTF hS hc hpr op₁ _ _).1 (testOK_cmpTF hS hc hpr op₂ _ _).1,
      testOK_orT hS (testOK_cmpTF hS hc hpr op₁ _ _).2 (testOK_cmpTF hS hc hpr op₂ _ _).2⟩
  | and φ ψ ihφ ihψ => exact ⟨testOK_andT hS ihφ.1 ihψ.1, testOK_orT hS ihφ.2 ihψ.2⟩
  | or φ ψ ihφ ihψ => exact ⟨testOK_orT hS ihφ.1 ihψ.1, testOK_andT hS ihφ.2 ihψ.2⟩
  | not φ ih => exact ⟨ih.2, ih.1⟩

/-! ## A selection as an apply -/

omit [ValueType T] in
theorem kinds_append0 {n : ℕ} (κ : Fin n → ColKind) :
    (Fin.append κ (ColKind.allReg 0) : Fin (n + 0) → ColKind) = κ :=
  funext fun k => Fin.append_left κ (ColKind.allReg 0) k

/-- **A selection written with the apply**: each row of the input meets the
test of the predicate at that row, which holds the empty tuple once where
the predicate is true and nothing elsewhere. -/
def selX (cnt : SeqAggFunc T) (pr : PairQ T) {c n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (φ : GenPredIn T c κ) (q : AggQueryIn T c n κ l) :
    AggQueryIn T c n κ l :=
  (AggQueryIn.Apply q (predTF cnt pr φ).1).castKind (kinds_append0 κ)

omit [ValueType T] in
theorem bind_ite_singleton {α : Type} (X : Multiset α) (p : α → Prop) [DecidablePred p] :
    X.bind (fun u => if p u then {u} else 0) = X.filter p := by
  induction X using Multiset.induction_on with
  | empty => rfl
  | cons a X ih =>
    rw [Multiset.cons_bind, ih, Multiset.filter_cons]

theorem evaluatePlain_selX {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {pr : PairQ T} (hpr : PairSpec pr) {c n : ℕ}
    {κ : Fin n → ColKind} {l : List (String × ℕ)} (φ : GenPredIn T c κ) (hφ : φ.noFun = true)
    (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T) :
    (selX cnt pr φ q).evaluatePlain D γ
      = @Multiset.filter _ (fun u => φ.holdsPlain u γ) (fun u => φ.decHoldsPlain u γ)
          (q.evaluatePlain D γ) := by
  rw [selX, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  rw [← bind_ite_singleton]
  refine Multiset.bind_congr fun u _ => ?_
  rw [(predTF_spec hcnt hpr φ hφ D u γ).1]
  unfold GenPredIn.holdsPlain
  cases h : decide (φ.evalPlain3 u γ = Kleene.true)
  · rw [ite_eq_right (of_decide_eq_false h)]
    rfl
  · rw [ite_eq_left (of_decide_eq_true h)]
    show Multiset.map _ {(fun k => k.elim0 : Tuple T 0)} = _
    rw [Multiset.map_singleton]
    congr 1
    funext k
    exact Fin.append_left u (fun j : Fin 0 => j.elim0) k

theorem settlesAt_selX (hS : selTestOps ⊆ S) {cnt : SeqAggFunc T} (hc : cnt ∈ Θ)
    (hpr : PairOK S Θ Q pr) {c n : ℕ}
    {κ : Fin n → ColKind} {l : List (String × ℕ)} (φ : GenPredIn T c κ)
    (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T) (hq : q.SettlesAt D γ) :
    (selX cnt pr φ q).SettlesAt D γ := by
  rw [selX, AggQueryIn.settlesAt_castKind]
  exact ⟨hq, fun _ _ => (testOK_predTF hS hc hpr φ).1.settles D _⟩

/-! ## The pass -/

/-- **Every selection replaced by an apply of its test**, the rest kept:
from a query over `Src` to one over `Tgt`, which has every class of `Src`
but `σ`, the apply and the tests' classes, building `{a, b}` with `pr`; in
the signature, well formed over every schema the source is over satisfying
`Q`, and defined and equal wherever the source is. `Q` must survive the
binding of any name but `s₀`, which the source does not use. -/
theorem exists_selPass_of {Src Tgt : Set OpKind}
    (hsub : ∀ k ∈ Src, k ≠ OpKind.sel → k ∈ Tgt) (hap : OpKind.apply ∈ Tgt)
    (hS : selTestOps ⊆ Tgt) (hms : OpKind.muSet ∉ Src) {cnt : SeqAggFunc T} (hc : cnt ∈ Θ)
    (hcnt : cnt.IsCount) (hpr : PairSpec pr) (hprOK : PairOK Tgt Θ Q pr) (s₀ : String)
    (hQ : ∀ (sch : Schema) (t : String) (m : ℕ), Q sch → t ≠ s₀ → Q (sch.update t m)) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly Src → q.inSig Θ → s₀ ∉ q.names →
      ∃ q' : AggQueryIn T c n κ l, q'.usesOnly Tgt ∧ q'.inSig Θ
        ∧ (∀ sch : Schema, Q sch → q.overSchema sch → q'.overSchema sch)
        ∧ (∀ x, q.noMention x → q'.noMention x)
        ∧ ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
            q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    exact fun _ _ _ => ⟨AggQueryIn.Rel n s, trivial, trivial, fun _ _ h => h, fun _ h => h,
      fun _ _ h => ⟨h, rfl⟩⟩
  | Hole n s κh =>
    exact fun _ _ _ => ⟨AggQueryIn.Hole n s κh, trivial, trivial, fun _ _ h => h, fun _ h => h,
      fun _ _ h => ⟨h, rfl⟩⟩
  | Param pv ρ =>
    exact fun hu _ _ => ⟨AggQueryIn.Param pv ρ,
      ⟨hsub _ hu.1 (by decide), hsub _ hu.2.1 (by decide),
        hsub _ hu.2.2 (by decide)⟩, trivial, fun _ _ h => h, fun _ h => h,
      fun _ _ h => ⟨h, rfl⟩⟩
  | Empty =>
    exact fun hu _ _ => ⟨AggQueryIn.Empty, hsub _ hu (by decide), trivial, fun _ _ h => h,
      fun _ h => h, fun _ _ h => ⟨h, rfl⟩⟩
  | Proj ps q ih =>
    intro hu hi hn
    obtain ⟨q', hu', hi', ho', hm', he'⟩ := ih hu.2 hi.2 hn
    refine ⟨AggQueryIn.Proj ps q', ⟨⟨hsub _ hu.1.1 (by decide), hu.1.2⟩, hu'⟩,
      ⟨hi.1, hi'⟩, ho', hm', fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | Sel φ q hφ ih =>
    intro hu hi hn
    obtain ⟨q', hu', hi', ho', hm', he'⟩ := ih hu.2 hi.2 hn
    refine ⟨selX cnt pr φ q', ?_, ?_, fun sch hs ho => ?_, fun x hx => ?_, fun D γ h => ⟨
      settlesAt_selX hS hc hprOK φ q' D γ (he' D γ h).1, ?_⟩⟩
    · rw [selX, AggQueryIn.usesOnly_castKind]
      exact ⟨hap, hu', (testOK_predTF hS hc hprOK φ).1.uses⟩
    · rw [selX, AggQueryIn.inSig_castKind]
      exact ⟨hi', (testOK_predTF hS hc hprOK φ).1.sig⟩
    · rw [selX, AggQueryIn.overSchema_castKind]
      exact ⟨ho' sch hs ho, (testOK_predTF hS hc hprOK φ).1.over sch hs⟩
    · rw [selX, AggQueryIn.noMention_castKind]
      exact ⟨hm' x hx, (testOK_predTF hS hc hprOK φ).1.noM x⟩
    · rw [evaluatePlain_selX hcnt hpr φ hi.1 q' D γ, ← (he' D γ h).2]
      rfl
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hu hi hn
    simp only [AggQueryIn.names, Finset.mem_union, not_or] at hn
    obtain ⟨q₁', hu₁, hi₁, ho₁, hm₁, he₁⟩ := ih₁ hu.2.1 hi.1 hn.1
    obtain ⟨q₂', hu₂, hi₂, ho₂, hm₂, he₂⟩ := ih₂ hu.2.2 hi.2 hn.2
    refine ⟨AggQueryIn.Prod q₁' q₂', ⟨hsub _ hu.1 (by decide), hu₁, hu₂⟩, ⟨hi₁, hi₂⟩,
      fun sch hs ho => ⟨ho₁ sch hs ho.1, ho₂ sch hs ho.2⟩,
      fun x hx => ⟨hm₁ x hx.1, hm₂ x hx.2⟩,
      fun D γ h => ⟨⟨(he₁ D γ h.1).1, (he₂ D γ h.2).1⟩, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he₁ D γ h.1).2, (he₂ D γ h.2).2]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hu hi hn
    simp only [AggQueryIn.names, Finset.mem_union, not_or] at hn
    obtain ⟨q₁', hu₁, hi₁, ho₁, hm₁, he₁⟩ := ih₁ hu.2.1 hi.1 hn.1
    obtain ⟨q₂', hu₂, hi₂, ho₂, hm₂, he₂⟩ := ih₂ hu.2.2 hi.2 hn.2
    refine ⟨AggQueryIn.Apply q₁' q₂', ⟨hsub _ hu.1 (by decide), hu₁, hu₂⟩, ⟨hi₁, hi₂⟩,
      fun sch hs ho => ⟨ho₁ sch hs ho.1, ho₂ sch hs ho.2⟩,
      fun x hx => ⟨hm₁ x hx.1, hm₂ x hx.2⟩, fun D γ h => ?_⟩
    obtain ⟨hs₁, he₁'⟩ := he₁ D γ h.1
    refine ⟨⟨hs₁, fun u hu' => (he₂ D _ (h.2 u (he₁' ▸ hu'))).1⟩, ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁']
    refine Multiset.bind_congr fun u hu' => ?_
    rw [(he₂ D _ (h.2 u (he₁' ▸ hu'))).2]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hu hi hn
    simp only [AggQueryIn.names, Finset.mem_union, not_or] at hn
    obtain ⟨q₁', hu₁, hi₁, ho₁, hm₁, he₁⟩ := ih₁ hu.2.1 hi.1 hn.1
    obtain ⟨q₂', hu₂, hi₂, ho₂, hm₂, he₂⟩ := ih₂ hu.2.2 hi.2 hn.2
    refine ⟨AggQueryIn.Sum q₁' q₂', ⟨hsub _ hu.1 (by decide), hu₁, hu₂⟩, ⟨hi₁, hi₂⟩,
      fun sch hs ho => ⟨ho₁ sch hs ho.1, ho₂ sch hs ho.2⟩,
      fun x hx => ⟨hm₁ x hx.1, hm₂ x hx.2⟩,
      fun D γ h => ⟨⟨(he₁ D γ h.1).1, (he₂ D γ h.2).1⟩, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he₁ D γ h.1).2, (he₂ D γ h.2).2]
  | Dedup q ih =>
    intro hu hi hn
    obtain ⟨q', hu', hi', ho', hm', he'⟩ := ih hu.2 hi hn
    refine ⟨AggQueryIn.Dedup q', ⟨hsub _ hu.1 (by decide), hu'⟩, hi', ho', hm',
      fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hu hi hn
    simp only [AggQueryIn.names, Finset.mem_union, not_or] at hn
    obtain ⟨q₁', hu₁, hi₁, ho₁, hm₁, he₁⟩ := ih₁ hu.2.1 hi.1 hn.1
    obtain ⟨q₂', hu₂, hi₂, ho₂, hm₂, he₂⟩ := ih₂ hu.2.2 hi.2 hn.2
    refine ⟨AggQueryIn.Diff q₁' q₂', ⟨hsub _ hu.1 (by decide), hu₁, hu₂⟩, ⟨hi₁, hi₂⟩,
      fun sch hs ho => ⟨ho₁ sch hs ho.1, ho₂ sch hs ho.2⟩,
      fun x hx => ⟨hm₁ x hx.1, hm₂ x hx.2⟩,
      fun D γ h => ⟨⟨(he₁ D γ h.1).1, (he₂ D γ h.2).1⟩, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he₁ D γ h.1).2, (he₂ D γ h.2).2]
  | Explode k hk q ih =>
    intro hu hi hn
    obtain ⟨q', hu', hi', ho', hm', he'⟩ := ih hu hi hn
    exact ⟨AggQueryIn.Explode k hk q', hu', hi', ho', hm', he'⟩
  | Retag h q ih =>
    intro hu hi hn
    obtain ⟨q', hu', hi', ho', hm', he'⟩ := ih hu hi hn
    exact ⟨AggQueryIn.Retag h q', hu', hi', ho', hm', he'⟩
  | @Mu c' n' κ' s q₀ q₁ ih₀ ih₁ =>
    intro hu hi hn
    simp only [AggQueryIn.names, Finset.mem_insert, Finset.mem_union, not_or] at hn
    obtain ⟨q₀', hu₀, hi₀, ho₀, hm₀, he₀⟩ := ih₀ hu.2.1 hi.1 hn.2.1
    obtain ⟨q₁', hu₁, hi₁, ho₁, hm₁, he₁⟩ := ih₁ hu.2.2 hi.2 hn.2.2
    refine ⟨AggQueryIn.Mu s q₀' q₁', ⟨hsub _ hu.1 (by decide), hu₀, hu₁⟩, ⟨hi₀, hi₁⟩,
      fun sch hs ho => ⟨ho.1, ho₀ sch hs ho.2.1, hm₁ s ho.2.2.1,
        ho₁ (sch.update s n') (hQ sch s n' hs (Ne.symm hn.1)) ho.2.2.2⟩,
      fun x hx => ⟨hm₀ x hx.1, hm₁ x hx.2⟩, fun D γ h => ?_⟩
    have := Sym.mu_rename s s q₀ q₀' q₁ q₁' D γ h (he₀ D γ h.1) (fun _ => True) trivial trivial
      (fun X _ hX => ⟨(he₁ _ γ hX).1, (he₁ _ γ hX).2, trivial⟩)
    exact ⟨this.1, this.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hu => absurd hu.1 hms
  | @Gamma c' m n₁ n₂ lab rd is ts fs q keep ord ih =>
    intro hu hi hn
    obtain ⟨q', hu', hi', ho', hm', he'⟩ := ih hu.2 hi.2.2.2 hn
    refine ⟨AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q' keep ord,
      ⟨hsub _ hu.1 (by decide), hu'⟩, ⟨hi.1, hi.2.1, hi.2.2.1, hi'⟩, ho', hm',
      fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | @GammaScalar c' m n₂ lab rd ts fs q ord ih =>
    intro hu hi hn
    obtain ⟨q', hu', hi', ho', hm', he'⟩ := ih hu.2 hi.2.2 hn
    refine ⟨AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q' ord,
      ⟨hsub _ hu.1 (by decide), hu'⟩, ⟨hi.1, hi.2.1, hi'⟩, ho', hm',
      fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | @GammaNest c' m n₁ κ' lab rd is his p f q ih =>
    intro hu hi hn
    obtain ⟨q', hu', hi', ho', hm', he'⟩ := ih hu.2 hi.2.2 hn
    refine ⟨AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q',
      ⟨⟨hsub _ hu.1.1 (by decide), hu.1.2⟩, hu'⟩, ⟨hi.1, hi.2.1, hi'⟩, ho', hm',
      fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | ProvSum is his t q ih => exact fun hu => hu.elim
  | GammaTok is his ts fs a q keep ih => exact fun hu => hu.elim
  | @Win c' n' m' p' κ' lab rd P O o w _ t f q hrr dist keep ih =>
    intro hu hi hn
    obtain ⟨q', hu', hi', ho', hm', he'⟩ := ih hu.2 hi.2.2.2.2 hn
    refine ⟨AggQueryIn.Win (hsql := sql_frame%) (lab := lab) (rd := rd) P O o w t f q' hrr dist
        keep,
      ⟨hsub _ hu.1 (by decide), hu'⟩, ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi'⟩, ho', hm',
      fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | WinExpr P O o ws ts fs g q keeps ih => exact fun _ hi => hi.elim

theorem mem_diffOps {k : OpKind} (hk : k ∈ basisRecOps) (hne : k ≠ OpKind.sel) :
    k ∈ basisRecDiffOps := by
  simp only [basisRecOps, AggQueryIn.sumMuOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  simp only [basisRecDiffOps, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hk with h | h | h | h | h | h | h <;> subst h <;> simp_all

/-- **The pass for the whole algebra**: over `{∅, Π, −, apply, γ, win, μ^⊎}`,
`{a, b}` built by a bag recursion named `s₀`, over every schema the source
is over that does not declare `s₀`. -/
theorem exists_selPass {cnt : SeqAggFunc T} (hc : cnt ∈ Θ) (hcnt : cnt.IsCount)
    (s₀ : String) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly basisRecOps → q.inSig Θ → s₀ ∉ q.names →
      ∃ q' : AggQueryIn T c n κ l, q'.usesOnly basisRecDiffOps ∧ q'.inSig Θ
        ∧ (∀ sch : Schema, sch s₀ = none → q.overSchema sch → q'.overSchema sch)
        ∧ (∀ x, q.noMention x → q'.noMention x)
        ∧ ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
            q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ :=
  fun q => exists_selPass_of (fun _ hk hne => mem_diffOps hk hne) (by simp [basisRecDiffOps])
    (fun k hk => by
      simp only [selTestOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      simp only [basisRecDiffOps, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto)
    (by simp [basisRecOps, AggQueryIn.sumMuOps]) hc hcnt (pairSpec_prZ s₀)
    (pairOK_prZ (fun k hk => by
      simp only [selTestOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      simp only [basisRecDiffOps, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto) (by simp [basisRecDiffOps]) (by simp [basisRecDiffOps]) s₀) s₀
    (fun sch t m hs ht => by rw [Schema.update_apply, ite_eq_right (Ne.symm ht)]; exact hs) q

end DiffBasis

/-! ## The basis with the difference -/

/-- **`{∅, Π, −, apply, γ, win, μ^⊎}` generates the whole algebra** in the
minimal universe: every query of the algebra over a schema, in the
signature with a count as its only aggregate, is matched by one over those
seven classes, defined and equal wherever the query is. First the query is
matched over `{∅, Π, σ, apply, γ, win, μ^⊎}` (`basisRecOps_generatesOnRec`),
then each selection of the match becomes an apply of its test
(`DiffBasis.exists_selPass`), the order being read by a window and its
count compared as a key. -/
theorem basisRecDiffOps_generatesOnRec (sch : Schema) (cnt : SeqAggFunc T)
    (hcnt : cnt.IsCount) : GeneratesOnRec T sch cnt basisRecDiffOps := by
  intro n κ q ho hq hi
  obtain ⟨κ₁, q₁, ho₁, hu₁, hi₁, hx₁⟩ := basisRecOps_generatesOnRec sch cnt hcnt q ho hq hi
  obtain ⟨f, -, hfsch, hfr⟩ := AggQueryIn.exists_freshSupply sch q₁.names
  obtain ⟨q₂, hu₂, hi₂, ho₂, -, he⟩ :=
    DiffBasis.exists_selPass (Θ := {cnt}) (Set.mem_singleton cnt) hcnt (f 0) q₁ hu₁ hi₁ (hfr 0)
  exact ⟨κ₁, q₂, ho₂ sch (hfsch 0) ho₁, hu₂, hi₂,
    fun D γ r h => (AggQueryIn.Extends.of_settles fun D γ hs => he D γ hs) D γ r (hx₁ D γ r h)⟩

/-- **No proper subset of `basisRecDiffOps` generates the whole algebra** in
the minimal universe over `ℕ`. The rows of `required_mem_of_generatesOnRec`
force each class: `−` because `σ` is not in the set, and the apply because
`×` is not. -/
theorem basisRecDiffOps_minimal {S : Set OpKind} (hS : S ⊂ basisRecDiffOps) :
    ¬ ∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count S := by
  intro hgen
  obtain ⟨he, hp, hg, hm, hwin, hs, ha⟩ := required_mem_of_generatesOnRec hgen
  obtain ⟨x, hx, hxS⟩ := Set.exists_of_ssubset hS
  have hsub := hS.subset
  have hsel : OpKind.sel ∉ S := fun h => by
    have := hsub h
    simp [basisRecDiffOps] at this
  have hprod : OpKind.prod ∉ S := fun h => by
    have := hsub h
    simp [basisRecDiffOps] at this
  simp only [basisRecDiffOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hxS he
  · exact hxS hp
  · exact hxS (hs.resolve_left hsel)
  · exact hxS (ha.resolve_left hprod)
  · exact hxS hg
  · exact hxS hwin
  · exact hxS hm

/-- **`basisRecDiffOps` is a basis of the whole algebra in the minimal
universe over `ℕ`**: it generates over every schema, and no proper subset
does. -/
theorem basisRecDiffOps_isBasis :
    (∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count basisRecDiffOps)
      ∧ ∀ S : Set OpKind, S ⊂ basisRecDiffOps →
          ¬ ∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count S :=
  ⟨fun sch => basisRecDiffOps_generatesOnRec sch _ SeqAggFunc.isCount_count_nat,
    fun _ hS => basisRecDiffOps_minimal hS⟩
