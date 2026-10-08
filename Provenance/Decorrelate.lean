/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.PlainBasis

/-!
# Decorrelation: an apply read as a product

An apply evaluates its right side once per row of its left side, with
that row's values filled in for the parameters. `sec:basis` claims that
nothing is lost by forbidding it: every query is equivalent to one whose
applies are products. The construction is Galindo-Legaria and Joshi's,
and the form here is the paper's `lem:decorrelation`: given a *parameter
relation* `P` whose rows are pairwise distinct, a query `q` reading `P`'s
columns as parameters is turned into a closed query `D_P(q)` over the
parameters and `q`'s own columns together, so that

  `D_P(q) = ⊎_{v ∈ P} {v} × q[v]`,

which is the apply of `P` and `q`. Every operator inside carries the
parameter columns along: a selection on a parameter becomes one on a
column, a grouping or a window gains the parameters in its key or
partition, and an apply recurses with the distinct rows of its own left
side as the parameter relation.

This file carries the first half: **lifting** the parameters of a term,
a predicate or a projection column into columns of the decorrelated
query. A term's outer column `j` becomes the column `j` of the result, a
column `i` of its own becomes the column `c + i`, and the reading is
unchanged (`TermGIn.evalPlain_lift`).
-/

variable {T : Type} [ValueType T]

/-- **The kinds of a decorrelated query**: the parameters first, which
are regular columns, then the query's own. -/
abbrev ColKind.liftKinds (c : ℕ) {k : ℕ} (κ : Fin k → ColKind) :
    Fin (c + k) → ColKind :=
  Fin.append (ColKind.allReg c) κ

/-- A parameter column of the decorrelated query is regular. -/
theorem ColKind.liftKinds_param (c : ℕ) {k : ℕ} (κ : Fin k → ColKind)
    (j : Fin c) :
    ColKind.liftKinds c κ (Fin.castAdd k j) = ColKind.reg := by
  rw [ColKind.liftKinds, Fin.append_left]
  rfl

/-- And a column of the query's own keeps its kind. -/
theorem ColKind.liftKinds_col (c : ℕ) {k : ℕ} (κ : Fin k → ColKind)
    (i : Fin k) : ColKind.liftKinds c κ (Fin.natAdd c i) = κ i := by
  rw [ColKind.liftKinds, Fin.append_right]

/-! ## Lifting a term -/

/-- **A term with its parameters read as columns**: the outer column `j`
becomes the column `j`, and the term's own column `i` becomes the column
`c + i`. -/
def TermIn.lift {c k : ℕ} : TermIn T c k → TermIn T 0 (c + k)
  | .const a => .const a
  | .outer j => .index (Fin.castAdd k j)
  | .index i => .index (Fin.natAdd c i)
  | .add t₁ t₂ => .add t₁.lift t₂.lift
  | .sub t₁ t₂ => .sub t₁.lift t₂.lift
  | .mul t₁ t₂ => .mul t₁.lift t₂.lift
  | .caseWhen op t₁ t₂ t₃ t₄ =>
      .caseWhen op t₁.lift t₂.lift t₃.lift t₄.lift
  | .coalesce t₁ t₂ => .coalesce t₁.lift t₂.lift

/-- **Lifting does not change what a term reads**: on the row that holds
the parameters and the query's own columns together, the lifted term
reads what the term read of that row under those parameters. -/
theorem TermIn.eval_lift {c k : ℕ} (t : TermIn T c k) (v : Tuple T c)
    (w : Tuple T k) :
    (t.lift).eval (Fin.append v w) (fun _ => 0) = t.eval w v := by
  induction t with
  | const a => rfl
  | outer j =>
    show (Fin.append v w : Tuple T (c + k)) (Fin.castAdd k j) = v j
    rw [Fin.append_left]
  | index i =>
    show (Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i) = w i
    rw [Fin.append_right]
  | add t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [ih₁, ih₂, ih₃, ih₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁, ih₂]
    rfl

/-! ## Lifting a general term -/

/-- **A general term with its parameters read as columns.** -/
def TermGIn.lift {c k : ℕ} {κ : Fin k → ColKind} :
    TermGIn T c κ → TermGIn T 0 (ColKind.liftKinds c κ)
  | .const a => .const a
  | .outer j => .index (Fin.castAdd k j) (ColKind.liftKinds_param c κ j)
  | .index i h =>
      .index (Fin.natAdd c i) ((ColKind.liftKinds_col c κ i).trans h)
  | .provIndex i h =>
      .provIndex (Fin.natAdd c i) ((ColKind.liftKinds_col c κ i).trans h)
  | .cmpAgg i h op t =>
      .cmpAgg (Fin.natAdd c i) ((ColKind.liftKinds_col c κ i).trans h) op
        t.lift
  | .chiGate op t₁ t₂ => .chiGate op t₁.lift t₂.lift
  | .add t₁ t₂ => .add t₁.lift t₂.lift
  | .sub t₁ t₂ => .sub t₁.lift t₂.lift
  | .mul t₁ t₂ => .mul t₁.lift t₂.lift
  | .caseWhen op t₁ t₂ t₃ t₄ =>
      .caseWhen op t₁.lift t₂.lift t₃.lift t₄.lift
  | .coalesce t₁ t₂ => .coalesce t₁.lift t₂.lift

/-- **Lifting does not change what a general term reads.** -/
theorem TermGIn.evalPlain_lift {c k : ℕ} {κ : Fin k → ColKind}
    (t : TermGIn T c κ) (v : Tuple T c) (w : Tuple T k) :
    (t.lift).evalPlain (Fin.append v w) (fun _ => 0) = t.evalPlain w v := by
  induction t with
  | const a => rfl
  | outer j =>
    show (Fin.append v w : Tuple T (c + k)) (Fin.castAdd k j) = v j
    rw [Fin.append_left]
  | index i h =>
    show (Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i) = w i
    rw [Fin.append_right]
  | provIndex i h =>
    show (Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i) = w i
    rw [Fin.append_right]
  | cmpAgg i h op t ih => rfl
  | chiGate op t₁ t₂ ih₁ ih₂ => rfl
  | add t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [ih₁, ih₂, ih₃, ih₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁, ih₂]
    rfl

/-! ## Lifting a predicate and a projection column -/

/-- **A predicate with its parameters read as columns.** -/
def GenPredIn.lift {c k : ℕ} {κ : Fin k → ColKind} :
    GenPredIn T c κ → GenPred T (ColKind.liftKinds c κ)
  | .cmp op t₁ t₂ => .cmp op t₁.lift t₂.lift
  | .aggCmp i h op t =>
      .aggCmp (Fin.natAdd c i) ((ColKind.liftKinds_col c κ i).trans h) op
        t.lift
  | .aggRange i h op₁ t₁ op₂ t₂ =>
      .aggRange (Fin.natAdd c i) ((ColKind.liftKinds_col c κ i).trans h)
        op₁ t₁.lift op₂ t₂.lift
  | .and φ ψ => .and φ.lift ψ.lift
  | .or φ ψ => .or φ.lift ψ.lift
  | .not φ => .not φ.lift

/-- **Lifting does not change which rows a predicate keeps.** -/
theorem GenPredIn.evalPlain3_lift {c k : ℕ} {κ : Fin k → ColKind}
    (φ : GenPredIn T c κ) (v : Tuple T c) (w : Tuple T k) :
    (φ.lift).evalPlain3 (Fin.append v w) (fun _ => 0)
      = φ.evalPlain3 w v := by
  induction φ with
  | cmp op t₁ t₂ =>
    show op.eval3 _ _ = op.eval3 _ _
    rw [TermGIn.evalPlain_lift, TermGIn.evalPlain_lift]
  | aggCmp i h op t =>
    show op.eval3 ((Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i)) _
      = op.eval3 (w i) _
    rw [Fin.append_right, TermGIn.evalPlain_lift]
  | aggRange i h op₁ t₁ op₂ t₂ =>
    show ((op₁.eval3 ((Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i)) _).and
      (op₂.eval3 ((Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i)) _)) = _
    rw [Fin.append_right, TermGIn.evalPlain_lift, TermGIn.evalPlain_lift]
    rfl
  | and φ ψ ihφ ihψ => exact congrArg₂ _ ihφ ihψ
  | or φ ψ ihφ ihψ => exact congrArg₂ _ ihφ ihψ
  | not φ ih => exact congrArg _ ih

theorem GenPredIn.holdsPlain_lift {c k : ℕ} {κ : Fin k → ColKind}
    (φ : GenPredIn T c κ) (v : Tuple T c) (w : Tuple T k) :
    (φ.lift).holdsPlain (Fin.append v w) (fun _ => 0)
      ↔ φ.holdsPlain w v := by
  unfold GenPredIn.holdsPlain
  rw [GenPredIn.evalPlain3_lift]

/-- **A projection column with its parameters read as columns.** -/
def ProjColIn.lift {c k : ℕ} {κ : Fin k → ColKind} :
    ProjColIn T c κ → ProjCol T (ColKind.liftKinds c κ)
  | .term t => .term t.lift
  | .token i h => .token (Fin.natAdd c i) ((ColKind.liftKinds_col c κ i).trans h)
  | .aggTerm i h gf =>
      .aggTerm (Fin.natAdd c i) ((ColKind.liftKinds_col c κ i).trans h) gf
  | .provTerm t => .provTerm t.lift

omit [ValueType T] in
/-- Lifting keeps a projection column's kind. -/
@[simp] theorem ProjColIn.kind_lift {c k : ℕ} {κ : Fin k → ColKind}
    (p : ProjColIn T c κ) : (p.lift).kind = p.kind := by
  cases p <;> rfl

/-- **Lifting does not change what a projection column computes**, over
plain rows. -/
theorem ProjColIn.evalPlain_lift {c k : ℕ} {κ : Fin k → ColKind}
    (p : ProjColIn T c κ) (v : Tuple T c) (w : Tuple T k) :
    (p.lift).evalPlain (Fin.append v w) (fun _ => 0) = p.evalPlain w v := by
  cases p with
  | term t => exact TermGIn.evalPlain_lift t v w
  | token i h =>
    show (Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i) = w i
    rw [Fin.append_right]
  | aggTerm i h gf =>
    show gf ((Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i)) = gf (w i)
    rw [Fin.append_right]
  | provTerm t => exact TermGIn.evalPlain_lift t v w

/-! ## Slices: what a decorrelated query computes

A decorrelated query holds, for each row `v` of the parameter relation, a
*slice*: the rows of `q[v]` with `v` in front. Everything below is read
off that shape, and the operators of the algebra act slice by slice –
which is why the construction can push them through. The parameter rows
being pairwise distinct is what makes the slices disjoint, and so is
needed exactly where an operator compares whole rows: `ε` and `−`. -/

/-- **The slices of a parameter relation**: for each `v ∈ P`, the rows
`f v` with `v` in front. -/
def Relation.slices {c k : ℕ} (P : Multiset (Tuple T c))
    (f : Tuple T c → Multiset (Tuple T k)) : Multiset (Tuple T (c + k)) :=
  P.bind (fun v => (f v).map (fun w => (Fin.append v w : Tuple T (c + k))))

omit [ValueType T] in
/-- Appending is injective in both arguments, which is what keeps the
slices apart. -/
theorem Fin.append_inj {c k : ℕ} {v v' : Tuple T c} {w w' : Tuple T k}
    (h : (Fin.append v w : Tuple T (c + k)) = Fin.append v' w') :
    v = v' ∧ w = w' := by
  refine ⟨funext (fun j => ?_), funext (fun i => ?_)⟩
  · have hj := congrFun h (Fin.castAdd k j)
    rwa [Fin.append_left, Fin.append_left] at hj
  · have hi := congrFun h (Fin.natAdd c i)
    rwa [Fin.append_right, Fin.append_right] at hi

omit [ValueType T] in
/-- A row of the slices is a row of one slice. -/
theorem Relation.mem_slices {c k : ℕ} (P : Multiset (Tuple T c))
    (f : Tuple T c → Multiset (Tuple T k)) (x : Tuple T (c + k)) :
    x ∈ Relation.slices P f
      ↔ ∃ v ∈ P, ∃ w ∈ f v, x = (Fin.append v w : Tuple T (c + k)) := by
  rw [Relation.slices, Multiset.mem_bind]
  constructor
  · rintro ⟨v, hv, hx⟩
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
    exact ⟨v, hv, w, hw, rfl⟩
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨v, hv, Multiset.mem_map_of_mem _ hw⟩

omit [ValueType T] in
/-- Slices add slice by slice. -/
theorem Relation.slices_add {c k : ℕ} (P : Multiset (Tuple T c))
    (f g : Tuple T c → Multiset (Tuple T k)) :
    Relation.slices P (fun v => f v + g v)
      = Relation.slices P f + Relation.slices P g := by
  unfold Relation.slices
  rw [← Multiset.bind_add]
  exact Multiset.bind_congr (fun v _ => Multiset.map_add _ _ _)

omit [ValueType T] in
/-- A filter that reads the whole row acts slice by slice. -/
theorem Relation.slices_filter {c k : ℕ} (P : Multiset (Tuple T c))
    (f : Tuple T c → Multiset (Tuple T k))
    (p : Tuple T (c + k) → Prop) [DecidablePred p] :
    Multiset.filter p (Relation.slices P f)
      = Relation.slices P (fun v =>
          Multiset.filter (fun w => p (Fin.append v w)) (f v)) := by
  unfold Relation.slices
  rw [Multiset.filter_bind]
  exact Multiset.bind_congr (fun v _ => Multiset.filter_map _ _ _)

omit [ValueType T] in
/-- A map that keeps the parameters acts slice by slice. -/
theorem Relation.slices_map {c k k' : ℕ} (P : Multiset (Tuple T c))
    (f : Tuple T c → Multiset (Tuple T k))
    (F : Tuple T c → Tuple T k → Tuple T k') :
    Multiset.map (fun x : Tuple T (c + k) =>
        (Fin.append (fun j => x (Fin.castAdd k j))
          (F (fun j => x (Fin.castAdd k j)) (fun i => x (Fin.natAdd c i)))
          : Tuple T (c + k')))
        (Relation.slices P f)
      = Relation.slices P (fun v => (f v).map (F v)) := by
  unfold Relation.slices
  rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun v _ => ?_)
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun w _ => ?_)
  show (Fin.append (fun j => (Fin.append v w : Tuple T (c + k)) (Fin.castAdd k j))
      (F _ (fun i => (Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i)))
      : Tuple T (c + k')) = _
  rw [show (fun j => (Fin.append v w : Tuple T (c + k)) (Fin.castAdd k j)) = v
      from funext (fun j => by rw [Fin.append_left]),
    show (fun i => (Fin.append v w : Tuple T (c + k)) (Fin.natAdd c i)) = w
      from funext (fun i => by rw [Fin.append_right])]
  rfl

omit [ValueType T] in
/-- A row of one slice is in the slices exactly when it is in that
slice, the parameter block telling the slices apart. -/
theorem Relation.append_mem_slices {c k : ℕ} {P : Multiset (Tuple T c)}
    {f : Tuple T c → Multiset (Tuple T k)} {v : Tuple T c} (hv : v ∈ P)
    (w : Tuple T k) :
    (Fin.append v w : Tuple T (c + k)) ∈ Relation.slices P f ↔ w ∈ f v := by
  rw [Relation.mem_slices]
  constructor
  · rintro ⟨v', hv', w', hw', heq⟩
    obtain ⟨rfl, rfl⟩ := Fin.append_inj heq
    exact hw'
  · intro hw
    exact ⟨v, hv, w, hw, rfl⟩

/-- **Duplicate elimination acts slice by slice**, the parameter rows
being pairwise distinct: a row of one slice is a row of no other. -/
theorem Relation.slices_dedup {c k : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (f : Tuple T c → Multiset (Tuple T k)) :
    (Relation.slices P f).dedup
      = Relation.slices P (fun v => (f v).dedup) := by
  classical
  refine Multiset.Nodup.ext (Multiset.nodup_dedup _) ?_ |>.mpr (fun x => ?_)
  · -- the slices of deduplicated slices are themselves duplicate-free
    refine Multiset.nodup_bind.mpr ⟨fun v _ => ?_, ?_⟩
    · exact (Multiset.nodup_dedup _).map (fun w w' h => (Fin.append_inj h).2)
    · refine hP.pairwise (fun v _ v' _ hne => ?_)
      refine Multiset.disjoint_left.mpr (fun {x} hx hx' => hne ?_)
      obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨w', -, heq⟩ := Multiset.mem_map.mp hx'
      exact (Fin.append_inj heq).1.symm
  · rw [Multiset.mem_dedup, Relation.mem_slices, Relation.mem_slices]
    exact exists_congr (fun v => and_congr_right (fun _ =>
      exists_congr (fun w => and_congr_left' (Multiset.mem_dedup).symm)))

/-- **The difference acts slice by slice**: a row of one slice matches a
row of the right side exactly when it matches one in its own slice. -/
theorem Relation.slices_diff {c k : ℕ} (P : Multiset (Tuple T c))
    (f g : Tuple T c → Multiset (Tuple T k)) :
    Multiset.filter (fun x => x ∉ Relation.slices P g) (Relation.slices P f)
      = Relation.slices P (fun v =>
          Multiset.filter (fun w => w ∉ g v) (f v)) := by
  classical
  rw [Relation.slices_filter]
  unfold Relation.slices
  refine Multiset.bind_congr (fun v hv => ?_)
  exact congrArg _ (Multiset.filter_congr (fun w _ =>
    not_congr (Relation.append_mem_slices hv w)))

/-! ## The parameter join

Two decorrelated queries over the same parameters are put side by side
by a product, a selection matching their parameter blocks, and a
projection keeping one copy of the parameters. This is the step that
turns an apply into a product, and the one that needs the parameter rows
to be pairwise distinct: a repeated row would pair the copies of its own
slice with each other. -/

/-- The parameters a row of a decorrelated query carries. -/
def Relation.paramsOf {c k : ℕ} (x : Tuple T (c + k)) : Tuple T c :=
  fun j => x (Fin.castAdd k j)

omit [ValueType T] in
/-- The parameters of a row built from them. -/
@[simp] theorem Relation.paramsOf_append {c k : ℕ} (v : Tuple T c)
    (w : Tuple T k) :
    Relation.paramsOf (Fin.append v w : Tuple T (c + k)) = v :=
  funext (fun j => by
    show (Fin.append v w : Tuple T (c + k)) (Fin.castAdd k j) = v j
    rw [Fin.append_left])

/-- The condition the parameter join selects on: the two parameter
blocks agree. -/
def Relation.joinParams {c k₁ k₂ : ℕ}
    (x : Tuple T ((c + k₁) + (c + k₂))) : Prop :=
  ∀ j : Fin c, x (Fin.castAdd (c + k₂) (Fin.castAdd k₁ j))
    = x (Fin.natAdd (c + k₁) (Fin.castAdd k₂ j))

instance {c k₁ k₂ : ℕ} (x : Tuple T ((c + k₁) + (c + k₂))) :
    Decidable (Relation.joinParams x) :=
  inferInstanceAs (Decidable (∀ _, _ = _))

/-- The columns the parameter join keeps: the parameters once, then each
side's own columns. -/
def Relation.joinCols {c k₁ k₂ : ℕ} (x : Tuple T ((c + k₁) + (c + k₂))) :
    Tuple T (c + (k₁ + k₂)) :=
  Fin.append (fun j : Fin c => x (Fin.castAdd (c + k₂) (Fin.castAdd k₁ j)))
    (Fin.append (fun i : Fin k₁ => x (Fin.castAdd (c + k₂) (Fin.natAdd c i)))
      (fun i : Fin k₂ => x (Fin.natAdd (c + k₁) (Fin.natAdd c i))))

/-- Binding a choice that is the same on one value and empty elsewhere
is binding over the rows that match it. -/
theorem Multiset.bind_ite_eq {α β : Type} [DecidableEq α] (s : Multiset α)
    (a : α) (X : Multiset β) :
    (s.bind (fun x => if x = a then X else 0))
      = (s.filter (fun x => x = a)).bind (fun _ => X) := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons b s ih =>
    rw [Multiset.cons_bind, ih, Multiset.filter_cons]
    by_cases h : b = a
    · rw [ite_eq_left h, ite_eq_left h, Multiset.singleton_add,
        Multiset.cons_bind]
    · rw [ite_eq_right h, ite_eq_right h, Multiset.zero_add,
        Multiset.zero_add]

/-- **The rows of one slice, read off the slices by their parameters**:
with the parameter rows distinct, the rows carrying `v` are exactly that
slice's. -/
theorem Relation.filter_paramsOf_slices {c k : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (g : Tuple T c → Multiset (Tuple T k)) {v : Tuple T c}
    (hv : v ∈ P) :
    Multiset.filter (fun b : Tuple T (c + k) => Relation.paramsOf b = v)
        (Relation.slices P g)
      = (g v).map (fun w => (Fin.append v w : Tuple T (c + k))) := by
  classical
  unfold Relation.slices
  rw [Multiset.filter_bind]
  have hone : ∀ v' ∈ P,
      Multiset.filter (fun b : Tuple T (c + k) => Relation.paramsOf b = v)
          ((g v').map (fun w => (Fin.append v' w : Tuple T (c + k))))
        = if v' = v then (g v).map (fun w => (Fin.append v w : Tuple T (c + k)))
          else 0 := by
    intro v' _
    rw [Multiset.filter_map]
    by_cases hvv : v' = v
    · subst hvv
      rw [ite_eq_left rfl]
      refine congrArg _ (Multiset.filter_eq_self.mpr (fun w _ => ?_))
      show (fun j => (Fin.append v' w : Tuple T (c + k)) (Fin.castAdd k j)) = v'
      exact funext (fun j => by rw [Fin.append_left])
    · rw [ite_eq_right hvv]
      refine Multiset.map_eq_zero.mpr (Multiset.filter_eq_nil.mpr
        (fun w _ hw => hvv ?_))
      have hw' : (fun j => (Fin.append v' w : Tuple T (c + k))
          (Fin.castAdd k j)) = v := hw
      exact (funext (fun j => by
        have := congrFun hw' j
        rwa [Fin.append_left] at this))
  rw [Multiset.bind_congr hone, Multiset.bind_ite_eq, Multiset.filter_eq',
    Multiset.count_eq_one_of_mem hP hv, Multiset.replicate_one,
    Multiset.singleton_bind]

/-- **The parameter join of two decorrelated queries** is the
decorrelation of their product: each slice is paired with its own. -/
theorem Relation.slices_joinParams {c k₁ k₂ : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (f : Tuple T c → Multiset (Tuple T k₁))
    (g : Tuple T c → Multiset (Tuple T k₂)) :
    (((Relation.slices P f).bind (fun a => (Relation.slices P g).map
            (fun b => (Fin.append a b : Tuple T ((c + k₁) + (c + k₂)))))).filter
        Relation.joinParams).map Relation.joinCols
      = Relation.slices P (fun v => (f v).bind (fun w₁ =>
          (g v).map (fun w₂ => (Fin.append w₁ w₂ : Tuple T (k₁ + k₂))))) := by
  classical
  unfold Relation.slices
  rw [Multiset.filter_bind, Multiset.map_bind, Multiset.bind_assoc]
  refine Multiset.bind_congr (fun v hv => ?_)
  rw [Multiset.bind_map, Multiset.map_bind]
  refine Multiset.bind_congr (fun w₁ _ => ?_)
  rw [Multiset.filter_map, Multiset.map_map]
  -- the right side's rows the condition keeps are its own slice's
  have hiff : ∀ b : Tuple T (c + k₂),
      Relation.joinParams
          (Fin.append (Fin.append v w₁ : Tuple T (c + k₁)) b
            : Tuple T ((c + k₁) + (c + k₂)))
        ↔ Relation.paramsOf b = v := by
    intro b
    unfold Relation.joinParams Relation.paramsOf
    constructor
    · intro h
      refine funext (fun j => ?_)
      have hj := h j
      rw [Fin.append_left, Fin.append_left, Fin.append_right] at hj
      exact hj.symm
    · intro h j
      rw [Fin.append_left, Fin.append_left, Fin.append_right]
      exact (congrFun h j).symm
  refine Eq.trans (congrArg (Multiset.map (Relation.joinCols ∘
      fun b : Tuple T (c + k₂) =>
        (Fin.append (Fin.append v w₁ : Tuple T (c + k₁)) b
          : Tuple T ((c + k₁) + (c + k₂)))))
    (Eq.trans (Multiset.filter_congr
        (q := fun b : Tuple T (c + k₂) => Relation.paramsOf b = v)
        (fun b _ => hiff b))
      (Relation.filter_paramsOf_slices P hP g hv))) ?_
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun w₂ _ => ?_)
  -- and the projection reassembles the parameters once with both halves
  show Relation.joinCols (Fin.append (Fin.append v w₁ : Tuple T (c + k₁))
      (Fin.append v w₂ : Tuple T (c + k₂)))
    = (Fin.append v (Fin.append w₁ w₂ : Tuple T (k₁ + k₂))
        : Tuple T (c + (k₁ + k₂)))
  unfold Relation.joinCols
  refine congrArg₂ Fin.append (funext (fun j => ?_)) (congrArg₂ Fin.append
    (funext (fun i => ?_)) (funext (fun i => ?_)))
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_left, Fin.append_right]
  · rw [Fin.append_right, Fin.append_right]

/-! ## What a decorrelated query is, and the cases of the construction

The claim is one statement per operator: given decorrelations of the
subqueries over the same parameter relation, build one for the whole.
Each case is a lemma below, and the induction that assembles them is at
the end. Nothing here needs a `castKind`: the kind vector of the
decorrelated query is whatever the construction produces, and what is
claimed of it is an equality of plain semantics. -/

/-- The classes a basis of the plain semantics consists of – everything
but the apply, which is what the construction removes. -/
def basisOps : Set OpKind :=
  {OpKind.empty, OpKind.proj, OpKind.sel, OpKind.prod, OpKind.union,
    OpKind.dedup, OpKind.diff, OpKind.gamma, OpKind.win}

/-- **A decorrelation of `q` over the parameter relation `P`**: a closed
query whose rows are the slices, one per row of `P`, holding what `q`
gives under that row. -/
def AggQueryIn.DecorrelatesTo {c k : ℕ} {κ : Fin k → ColKind}
    {κ' : Fin (c + k) → ColKind} (P : AggQuery T c (ColKind.allReg c))
    (q : AggQueryIn T c k κ) (q' : AggQueryIn T 0 (c + k) κ') : Prop :=
  ∀ D : Database T, q'.evaluatePlain D
    = Relation.slices (P.evaluatePlain D) (fun v => q.evaluatePlain D v)

/-- **`q` has a decorrelation over `P`** using no apply. Its columns are
the parameters and `q`'s own, with the kinds they have: that the kind
vector is exactly the lifted one is what lets a selection's predicate,
a union's two sides and a difference's be put over it. -/
def AggQueryIn.HasDecorrelation {c k : ℕ} {κ : Fin k → ColKind}
    (P : AggQuery T c (ColKind.allReg c)) (q : AggQueryIn T c k κ) : Prop :=
  ∃ q' : AggQueryIn T 0 (c + k) (ColKind.liftKinds c κ),
    q'.usesOnly basisOps ∧ AggQueryIn.DecorrelatesTo P q q'

omit [ValueType T] in
/-- Transporting a query along an equality of kind vectors changes no
operator, so it changes nothing `usesOnly` sees. -/
@[simp] theorem AggQueryIn.usesOnly_castKind {c n : ℕ}
    {κ κ' : Fin n → ColKind} (h : κ = κ') (q : AggQueryIn T c n κ)
    (S : Set OpKind) : (q.castKind h).usesOnly S ↔ q.usesOnly S := by
  cases h
  exact Iff.rfl

/-! ### The leaves -/

/-- **A relation reference** is the product of the parameters with it:
the same rows under every parameter row. -/
theorem AggQueryIn.hasDecorrelation_rel {c n : ℕ}
    (P : AggQuery T c (ColKind.allReg c)) (hP : P.usesOnly basisOps)
    (s : String) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Rel n s) := by
  refine ⟨AggQueryIn.Prod P (AggQueryIn.Rel n s),
    ⟨by simp [basisOps], hP, trivial⟩, fun D => ?_⟩
  show (P.evaluatePlain D * (AggQueryIn.Rel n s).evaluatePlain D) = _
  rw [Relation.hMul_eq_bind]
  rfl

/-- **The empty relation** likewise: no row under any parameter row. -/
theorem AggQueryIn.hasDecorrelation_empty {c : ℕ}
    (P : AggQuery T c (ColKind.allReg c)) (hP : P.usesOnly basisOps) :
    AggQueryIn.HasDecorrelation P AggQueryIn.Empty := by
  refine ⟨AggQueryIn.Prod P AggQueryIn.Empty,
    ⟨by simp [basisOps], hP, by simp [AggQueryIn.usesOnly, basisOps]⟩,
    fun D => ?_⟩
  show (P.evaluatePlain D * AggQueryIn.Empty.evaluatePlain D) = _
  rw [Relation.hMul_eq_bind]
  rfl

/-! ### The operators that act slice by slice -/

/-- **A union** is the union of the decorrelations. -/
theorem AggQueryIn.hasDecorrelation_sum {c k : ℕ} {κ : Fin k → ColKind}
    {P : AggQuery T c (ColKind.allReg c)} {q₁ q₂ : AggQueryIn T c k κ}
    (h₁ : AggQueryIn.HasDecorrelation P q₁)
    (h₂ : AggQueryIn.HasDecorrelation P q₂) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Sum q₁ q₂) := by
  obtain ⟨q₁', hu₁, hd₁⟩ := h₁
  obtain ⟨q₂', hu₂, hd₂⟩ := h₂
  refine ⟨AggQueryIn.Sum q₁' q₂', ⟨by simp [basisOps], hu₁, hu₂⟩, fun D => ?_⟩
  show q₁'.evaluatePlain D + q₂'.evaluatePlain D = _
  rw [hd₁, hd₂, ← Relation.slices_add]
  rfl

/-- **A selection** is the selection on the lifted predicate: it reads
the parameters as columns, and the rows it keeps in a slice are those
the original keeps under that slice's parameters. -/
theorem AggQueryIn.hasDecorrelation_sel {c k : ℕ} {κ : Fin k → ColKind}
    {P : AggQuery T c (ColKind.allReg c)} {q : AggQueryIn T c k κ}
    (φ : GenPredIn T c κ) (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Sel φ q) := by
  classical
  obtain ⟨q', hu, hd⟩ := h
  refine ⟨AggQueryIn.Sel φ.lift q', ⟨by simp [basisOps], hu⟩, fun D => ?_⟩
  show Multiset.filter (fun u => φ.lift.holdsPlain u) (q'.evaluatePlain D) = _
  rw [hd, Relation.slices_filter]
  refine Multiset.bind_congr (fun v _ => ?_)
  refine congrArg _ (Multiset.filter_congr (fun w _ => ?_))
  exact GenPredIn.holdsPlain_lift φ v w

/-- **Duplicate elimination** is duplicate elimination of the
decorrelation: the slices are disjoint, the parameter rows being
pairwise distinct. -/
theorem AggQueryIn.hasDecorrelation_dedup {c k : ℕ}
    {P : AggQuery T c (ColKind.allReg c)}
    (hnd : ∀ D : Database T, (P.evaluatePlain D).Nodup)
    {q : AggQueryIn T c k (ColKind.allReg k)}
    (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Dedup q) := by
  classical
  obtain ⟨q', hu, hd⟩ := h
  refine ⟨((AggQueryIn.Dedup
      (q'.castKind (AggQueryIn.append_allReg c k))).castKind
      (AggQueryIn.append_allReg c k).symm), ?_, fun D => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], (AggQueryIn.usesOnly_castKind _ _ _).mpr hu⟩
  rw [AggQueryIn.evaluatePlain_castKind]
  show (AggQueryIn.evaluatePlain (q'.castKind _) D).dedup = _
  rw [AggQueryIn.evaluatePlain_castKind, hd, Relation.slices_dedup _ (hnd D)]
  rfl

/-- **A difference** is the difference of the decorrelations: a row of
one slice matches a row of the right side exactly when it matches one in
its own slice. -/
theorem AggQueryIn.hasDecorrelation_diff {c k : ℕ}
    {P : AggQuery T c (ColKind.allReg c)}
    {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)}
    (h₁ : AggQueryIn.HasDecorrelation P q₁)
    (h₂ : AggQueryIn.HasDecorrelation P q₂) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Diff q₁ q₂) := by
  classical
  obtain ⟨q₁', hu₁, hd₁⟩ := h₁
  obtain ⟨q₂', hu₂, hd₂⟩ := h₂
  refine ⟨((AggQueryIn.Diff (q₁'.castKind (AggQueryIn.append_allReg c k))
      (q₂'.castKind (AggQueryIn.append_allReg c k))).castKind
      (AggQueryIn.append_allReg c k).symm), ?_, fun D => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], (AggQueryIn.usesOnly_castKind _ _ _).mpr hu₁,
      (AggQueryIn.usesOnly_castKind _ _ _).mpr hu₂⟩
  rw [AggQueryIn.evaluatePlain_castKind]
  set A : Multiset (Tuple T (c + k)) :=
    AggQueryIn.evaluatePlain (q₁'.castKind (AggQueryIn.append_allReg c k)) D
    with hA
  set B : Multiset (Tuple T (c + k)) :=
    AggQueryIn.evaluatePlain (q₂'.castKind (AggQueryIn.append_allReg c k)) D
    with hB
  show Multiset.filter (fun t => t ∉ B) A = _
  rw [hA, hB, AggQueryIn.evaluatePlain_castKind,
    AggQueryIn.evaluatePlain_castKind, hd₁, hd₂, Relation.slices_diff]
  rfl

omit [ValueType T] in
/-- A row of a decorrelated query is its parameters and its own columns. -/
theorem Relation.append_paramsOf {c k : ℕ} (x : Tuple T (c + k)) :
    (Fin.append (Relation.paramsOf x) (fun i : Fin k => x (Fin.natAdd c i))
      : Tuple T (c + k)) = x := by
  funext j
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    rfl
  · rw [Fin.append_right]

/-- **A projection** keeps the parameters and reads each of its columns
lifted: a column that read a parameter reads the column holding it. -/
theorem AggQueryIn.hasDecorrelation_proj {c k m : ℕ} {κ : Fin k → ColKind}
    {P : AggQuery T c (ColKind.allReg c)} {q : AggQueryIn T c k κ}
    (ps : Tuple (ProjColIn T c κ) m) (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Proj ps q) := by
  obtain ⟨q', hu, hd⟩ := h
  -- the parameters as themselves, then the lifted columns
  set cols : Tuple (ProjCol T (ColKind.liftKinds c κ)) (c + m) :=
    Fin.append
      (fun j : Fin c => ProjColIn.term
        (TermGIn.index (Fin.castAdd k j) (ColKind.liftKinds_param c κ j)))
      (fun i : Fin m => (ps i).lift) with hcols
  have hkinds : (fun j => (cols j).kind)
      = ColKind.liftKinds c (fun i => (ps i).kind) := by
    funext j
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
    · show ProjColIn.kind (cols (Fin.castAdd m jp))
        = Fin.append (ColKind.allReg c) (fun i => (ps i).kind)
            (Fin.castAdd m jp)
      rw [hcols, Fin.append_left, Fin.append_left]
      rfl
    · show ProjColIn.kind (cols (Fin.natAdd c i))
        = Fin.append (ColKind.allReg c) (fun i => (ps i).kind)
            (Fin.natAdd c i)
      rw [hcols, Fin.append_right, Fin.append_right]
      exact ProjColIn.kind_lift (ps i)
  refine ⟨(AggQueryIn.Proj cols q').castKind hkinds, ?_, fun D => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], hu⟩
  rw [AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u => (fun j => (cols j).evalPlain u (fun _ => 0)))
      (q'.evaluatePlain D) = _
  rw [hd]
  refine Eq.trans (Multiset.map_congr rfl (fun x _ => ?_))
    (Relation.slices_map (P.evaluatePlain D) (fun v => q.evaluatePlain D v)
      (fun v w => (fun i => (ps i).evalPlain w v)))
  -- the parameter columns copy the parameters, and the others read the
  -- row as the original read it under them
  funext j
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · rw [Fin.append_left, hcols, Fin.append_left]
    rfl
  · rw [Fin.append_right, hcols, Fin.append_right]
    refine Eq.trans (congrArg (fun y => ((ps i).lift).evalPlain y (fun _ => 0))
      (Relation.append_paramsOf x).symm) ?_
    exact ProjColIn.evalPlain_lift (ps i) (Relation.paramsOf x)
      (fun i' => x (Fin.natAdd c i'))

/-! ### The product: a join on the parameters

Two decorrelations over the same parameters are put side by side by a
product, a selection matching their parameter blocks and a projection
keeping one copy of them. The projection copies each column as its kind
asks (`AggQueryIn.carryCol`), so aggregate and provenance columns are
carried through as well. -/

/-- Where each column of the parameter join reads from. -/
def joinSrc (c k₁ k₂ : ℕ) :
    Fin (c + (k₁ + k₂)) → Fin ((c + k₁) + (c + k₂)) :=
  Fin.addCases (fun jp : Fin c => Fin.castAdd (c + k₂) (Fin.castAdd k₁ jp))
    (Fin.addCases (fun i₁ : Fin k₁ => Fin.castAdd (c + k₂) (Fin.natAdd c i₁))
      (fun i₂ : Fin k₂ => Fin.natAdd (c + k₁) (Fin.natAdd c i₂)))

/-- **A product** is the parameter join of the two decorrelations. -/
theorem AggQueryIn.hasDecorrelation_prod {c k₁ k₂ : ℕ}
    {κ₁ : Fin k₁ → ColKind} {κ₂ : Fin k₂ → ColKind}
    {P : AggQuery T c (ColKind.allReg c)}
    (hnd : ∀ D : Database T, (P.evaluatePlain D).Nodup)
    {q₁ : AggQueryIn T c k₁ κ₁} {q₂ : AggQueryIn T c k₂ κ₂}
    (h₁ : AggQueryIn.HasDecorrelation P q₁)
    (h₂ : AggQueryIn.HasDecorrelation P q₂) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Prod q₁ q₂) := by
  classical
  obtain ⟨q₁', hu₁, hd₁⟩ := h₁
  obtain ⟨q₂', hu₂, hd₂⟩ := h₂
  -- the kinds of the product, and where each column of the join reads
  set κp : Fin ((c + k₁) + (c + k₂)) → ColKind :=
    Fin.append (ColKind.liftKinds c κ₁) (ColKind.liftKinds c κ₂) with hκp
  have hleft : ∀ j : Fin c,
      κp (Fin.castAdd (c + k₂) (Fin.castAdd k₁ j)) = ColKind.reg := by
    intro j
    rw [hκp, Fin.append_left]
    exact ColKind.liftKinds_param c κ₁ j
  have hright : ∀ j : Fin c,
      κp (Fin.natAdd (c + k₁) (Fin.castAdd k₂ j)) = ColKind.reg := by
    intro j
    rw [hκp, Fin.append_right]
    exact ColKind.liftKinds_param c κ₂ j
  have hsrc : ∀ j, κp (joinSrc c k₁ k₂ j)
      = ColKind.liftKinds c (Fin.append κ₁ κ₂) j := by
    intro j
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
    · show κp (joinSrc c k₁ k₂ (Fin.castAdd (k₁ + k₂) jp)) = _
      rw [joinSrc, Fin.addCases_left, hleft jp, ColKind.liftKinds,
        Fin.append_left]
      rfl
    · show κp (joinSrc c k₁ k₂ (Fin.natAdd c i)) = _
      rw [joinSrc, Fin.addCases_right, ColKind.liftKinds, Fin.append_right]
      refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
      · rw [Fin.addCases_left, hκp, Fin.append_left, ColKind.liftKinds,
          Fin.append_right, Fin.append_left]
      · rw [Fin.addCases_right, hκp, Fin.append_right, ColKind.liftKinds,
          Fin.append_right, Fin.append_right]
  refine ⟨(AggQueryIn.Proj (fun j => AggQueryIn.carryCol κp (joinSrc c k₁ k₂ j))
      (AggQueryIn.Sel
        (keyJoinCond (fun j : Fin c => Fin.castAdd (c + k₂) (Fin.castAdd k₁ j))
          (fun j : Fin c => Fin.natAdd (c + k₁) (Fin.castAdd k₂ j))
          hleft hright)
        (AggQueryIn.Prod q₁' q₂'))).castKind
      (funext (fun j => (AggQueryIn.carryCol_kind κp _).trans (hsrc j))),
    ?_, fun D => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], by simp [basisOps],
      ⟨by simp [basisOps], hu₁, hu₂⟩⟩
  rw [AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u => (fun j =>
      (AggQueryIn.carryCol κp (joinSrc c k₁ k₂ j)).evalPlain u (fun _ => 0)))
      (Multiset.filter (fun u => (keyJoinCond _ _ hleft hright).holdsPlain u)
        (q₁'.evaluatePlain D * q₂'.evaluatePlain D)) = _
  rw [Relation.hMul_eq_bind, hd₁, hd₂]
  refine Eq.trans ?_ (Eq.trans
    (Relation.slices_joinParams (P.evaluatePlain D) (hnd D)
      (fun v => q₁.evaluatePlain D v) (fun v => q₂.evaluatePlain D v))
    (congrArg (Relation.slices (P.evaluatePlain D))
      (funext (fun v => (Relation.hMul_eq_bind _ _).symm))))
  refine congrArg₂ Multiset.map (funext (fun u => funext (fun j => ?_)))
    (Multiset.filter_congr (fun u _ => ?_))
  · -- each column of the join copies the column it reads
    rw [AggQueryIn.evalPlain_carryCol]
    show u (joinSrc c k₁ k₂ j) = Relation.joinCols u j
    unfold Relation.joinCols
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
    · rw [joinSrc, Fin.addCases_left, Fin.append_left]
    · rw [joinSrc, Fin.addCases_right, Fin.append_right]
      refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
      · rw [Fin.addCases_left, Fin.append_left]
      · rw [Fin.addCases_right, Fin.append_right]
  · -- and the condition is that the two parameter blocks agree
    exact (keyJoinCond_holdsPlain _ _ hleft hright u).trans Iff.rfl

omit [ValueType T] in
/-- A parameter column is not a column of the query's own. -/
theorem Fin.castAdd_ne_natAdd {c k : ℕ} (jp : Fin c) (i : Fin k) :
    (Fin.castAdd k jp : Fin (c + k)) ≠ Fin.natAdd c i := by
  intro hc
  have hv := congrArg Fin.val hc
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := jp.isLt
  omega

omit [ValueType T] in
/-- The query's own columns are named injectively. -/
theorem Fin.natAdd_left_inj {c k : ℕ} {i i' : Fin k}
    (h : (Fin.natAdd c i : Fin (c + k)) = Fin.natAdd c i') : i = i' := by
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd] at hv
  exact Fin.ext (by omega)

/-! ### The operators the plain semantics does not see -/

/-- **A retagging** is a retagging: it changes no row. -/
theorem AggQueryIn.hasDecorrelation_retag {c k : ℕ}
    {κ κ' : Fin k → ColKind} {P : AggQuery T c (ColKind.allReg c)}
    (hbase : ∀ i, (κ i).base = (κ' i).base) {q : AggQueryIn T c k κ}
    (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Retag hbase q) := by
  obtain ⟨q', hu, hd⟩ := h
  have hlift : ∀ j, (ColKind.liftKinds c κ j).base
      = (ColKind.liftKinds c κ' j).base := by
    intro j
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
    · show (Fin.append (ColKind.allReg c) κ (Fin.castAdd k jp)).base
        = (Fin.append (ColKind.allReg c) κ' (Fin.castAdd k jp)).base
      rw [Fin.append_left, Fin.append_left]
    · show (Fin.append (ColKind.allReg c) κ (Fin.natAdd c i)).base
        = (Fin.append (ColKind.allReg c) κ' (Fin.natAdd c i)).base
      rw [Fin.append_right, Fin.append_right]
      exact hbase i
  exact ⟨AggQueryIn.Retag hlift q', hu, hd⟩

/-- **The alternatives reading of an aggregate column** likewise: it
reads the column as a key and changes no row of the plain semantics. -/
theorem AggQueryIn.hasDecorrelation_alt {c k : ℕ} {κ : Fin k → ColKind}
    {P : AggQuery T c (ColKind.allReg c)} (i : Fin k)
    (hi : κ i = ColKind.agg) {q : AggQueryIn T c k κ}
    (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Alt i hi q) := by
  obtain ⟨q', hu, hd⟩ := h
  have hagg : ColKind.liftKinds c κ (Fin.natAdd c i) = ColKind.agg :=
    (ColKind.liftKinds_col c κ i).trans hi
  have hkinds : Function.update (ColKind.liftKinds c κ) (Fin.natAdd c i)
        ColKind.reg
      = ColKind.liftKinds c (Function.update κ i ColKind.reg) := by
    funext j
    refine Fin.addCases (fun jp => ?_) (fun i' => ?_) j
    · rw [Function.update_of_ne (Fin.castAdd_ne_natAdd jp i)]
      show Fin.append (ColKind.allReg c) κ (Fin.castAdd k jp)
        = Fin.append (ColKind.allReg c) _ (Fin.castAdd k jp)
      rw [Fin.append_left, Fin.append_left]
    · show Function.update (ColKind.liftKinds c κ) (Fin.natAdd c i)
          ColKind.reg (Fin.natAdd c i')
        = Fin.append (ColKind.allReg c) (Function.update κ i ColKind.reg)
            (Fin.natAdd c i')
      rw [Fin.append_right]
      by_cases hii : i' = i
      · subst hii
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (fun hc => hii (Fin.natAdd_left_inj hc)),
          Function.update_of_ne hii, ColKind.liftKinds_col]
  exact ⟨(AggQueryIn.Alt (Fin.natAdd c i) hagg q').castKind hkinds,
    (AggQueryIn.usesOnly_castKind _ _ _).mpr hu, fun D => by
      rw [AggQueryIn.evaluatePlain_castKind]
      exact hd D⟩

/-! ### Shifting a closed term over the parameter block

A window's `FILTER` clause is a selection on its input's columns, and
the decorrelated window's input has the parameters before them. The
clause therefore has to read the column `c + i` where it read the
column `i`; it reads no parameter, having none to read. -/

/-- **A term reading the columns of the decorrelated query's own
half**: the column `i` becomes the column `c + i`. Unlike `TermIn.lift`
this leaves the outer columns alone – it shifts a term's reading, where
`lift` closes it. -/
def TermIn.shift (c : ℕ) {c' k : ℕ} : TermIn T c' k → TermIn T c' (c + k)
  | .const a => .const a
  | .outer j => .outer j
  | .index i => .index (Fin.natAdd c i)
  | .add t₁ t₂ => .add (t₁.shift c) (t₂.shift c)
  | .sub t₁ t₂ => .sub (t₁.shift c) (t₂.shift c)
  | .mul t₁ t₂ => .mul (t₁.shift c) (t₂.shift c)
  | .caseWhen op t₁ t₂ t₃ t₄ =>
      .caseWhen op (t₁.shift c) (t₂.shift c) (t₃.shift c) (t₄.shift c)
  | .coalesce t₁ t₂ => .coalesce (t₁.shift c) (t₂.shift c)

/-- **Shifting does not change what a term reads**, the block it skips
holding the parameters. -/
theorem TermIn.eval_shift (c : ℕ) {c' k : ℕ} (t : TermIn T c' k)
    (v : Tuple T c) (u : Tuple T k) (γ : Fin c' → T) :
    (t.shift c).eval (Fin.append v u) γ = t.eval u γ := by
  induction t with
  | const a => rfl
  | outer j => rfl
  | index i =>
    show (Fin.append v u : Tuple T (c + k)) (Fin.natAdd c i) = u i
    rw [Fin.append_right]
  | add t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [ih₁, ih₂, ih₃, ih₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁, ih₂]
    rfl

omit [ValueType T] in
/-- Shifting a term's reading does not change which kinds of column it
reads, the parameters being regular. -/
theorem TermIn.regOnly_shift {c c' k : ℕ} (κ : Fin k → ColKind)
    (t : TermIn T c' k) :
    (t.shift c).regOnly (ColKind.liftKinds c κ) = t.regOnly κ := by
  induction t with
  | const a => rfl
  | outer j => rfl
  | index i =>
    show ((ColKind.liftKinds c κ (Fin.natAdd c i)).base == ColKind.reg) = _
    rw [ColKind.liftKinds_col]
    rfl
  | add t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (_ && _ && _ && _) = (_ && _ && _ && _)
    rw [ih₁, ih₂, ih₃, ih₄]
  | coalesce t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂

omit [ValueType T] in
/-- And lifting a term's parameters into columns does not either. -/
theorem TermIn.regOnly_lift {c k : ℕ} (κ : Fin k → ColKind)
    (t : TermIn T c k) :
    (t.lift).regOnly (ColKind.liftKinds c κ) = t.regOnly κ := by
  induction t with
  | const a => rfl
  | outer j =>
    show ((ColKind.liftKinds c κ (Fin.castAdd k j)).base == ColKind.reg) = _
    rw [ColKind.liftKinds_param]
    rfl
  | index i =>
    show ((ColKind.liftKinds c κ (Fin.natAdd c i)).base == ColKind.reg) = _
    rw [ColKind.liftKinds_col]
    rfl
  | add t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (_ && _ && _ && _) = (_ && _ && _ && _)
    rw [ih₁, ih₂, ih₃, ih₄]
  | coalesce t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂

/-- **A comparison on the shifted columns.** -/
def BoolTerm.shift (c : ℕ) {k : ℕ} : BoolTerm T k → BoolTerm T (c + k)
  | .EQ a b => .EQ (a.shift c) (b.shift c)
  | .NE a b => .NE (a.shift c) (b.shift c)
  | .LE a b => .LE (a.shift c) (b.shift c)
  | .LT a b => .LT (a.shift c) (b.shift c)
  | .GE a b => .GE (a.shift c) (b.shift c)
  | .GT a b => .GT (a.shift c) (b.shift c)
  | .SYNEQ a b => .SYNEQ (a.shift c) (b.shift c)
  | .SYNNE a b => .SYNNE (a.shift c) (b.shift c)

/-- It compares the same two values. -/
theorem BoolTerm.eval3_shift (c : ℕ) {k : ℕ} (φ : BoolTerm T k)
    (v : Tuple T c) (u : Tuple T k) :
    (φ.shift c).eval3 (Fin.append v u) = φ.eval3 u := by
  have hargs : ∀ ψ : BoolTerm T k,
      ((ψ.shift c).args.1.eval (Fin.append v u) = ψ.args.1.eval u
        ∧ (ψ.shift c).args.2.eval (Fin.append v u) = ψ.args.2.eval u)
      ∧ (ψ.shift c).toCompOp = ψ.toCompOp := by
    intro ψ
    cases ψ <;>
      exact ⟨⟨TermIn.eval_shift c _ v u _, TermIn.eval_shift c _ v u _⟩, rfl⟩
  obtain ⟨⟨h₁, h₂⟩, hop⟩ := hargs φ
  unfold BoolTerm.eval3
  rw [h₁, h₂, hop]

/-- **A selection on the shifted columns.** -/
def Selection.shift (c : ℕ) {k : ℕ} : Selection T k → Selection T (c + k)
  | .BT b => .BT (b.shift c)
  | .Not φ => .Not (φ.shift c)
  | .And φ₁ φ₂ => .And (φ₁.shift c) (φ₂.shift c)
  | .Or φ₁ φ₂ => .Or (φ₁.shift c) (φ₂.shift c)
  | .True => .True

/-- It keeps the same rows. -/
theorem Selection.keeps_shift (c : ℕ) {k : ℕ} (φ : Selection T k)
    (v : Tuple T c) (u : Tuple T k) :
    (φ.shift c).keeps (Fin.append v u) = φ.keeps u := by
  have h3 : ∀ ψ : Selection T k,
      (ψ.shift c).eval3 (Fin.append v u) = ψ.eval3 u := by
    intro ψ
    induction ψ with
    | BT b => exact BoolTerm.eval3_shift c b v u
    | Not ψ ih => exact congrArg Kleene.not ih
    | And ψ₁ ψ₂ ih₁ ih₂ => exact congrArg₂ Kleene.and ih₁ ih₂
    | Or ψ₁ ψ₂ ih₁ ih₂ => exact congrArg₂ Kleene.or ih₁ ih₂
    | True => rfl
  unfold Selection.keeps
  rw [h3 φ]

/-! ### Groups: the parameters join the key

An aggregation of the decorrelated query groups by the parameters as well
as by its own key columns, so each group is one slice's group. The rows
of that group are the slice's with the parameters in front, which is what
the aggregates then read. -/

/-- **Prefixing a common block does not change the order**: the domain's
order on tuples is lexicographic, and the block the two rows share is
read first. (The comparisons are written out: this file is in the scope
of the relational notation, where `<` reads as a predicate's.) -/
theorem Fin.append_lt_append {c k : ℕ} (v : Tuple T c) (w w' : Tuple T k) :
    @LT.lt (Tuple T (c + k)) _ (Fin.append v w) (Fin.append v w')
      ↔ @LT.lt (Tuple T k) _ w w' := by
  show (∃ i : Fin (c + k),
      (∀ j, Nat.lt j.val i.val → (Fin.append v w : Tuple T (c + k)) j
        = Fin.append v w' j)
      ∧ @LT.lt T _ ((Fin.append v w : Tuple T (c + k)) i) (Fin.append v w' i))
    ↔ (∃ i : Fin k, (∀ j, Nat.lt j.val i.val → w j = w' j)
      ∧ @LT.lt T _ (w i) (w' i))
  constructor
  · rintro ⟨i, hlt, hi⟩
    refine Fin.addCases (motive := fun i =>
      (∀ j, Nat.lt j.val i.val → (Fin.append v w : Tuple T (c + k)) j
          = Fin.append v w' j)
        → @LT.lt T _ ((Fin.append v w : Tuple T (c + k)) i)
            (Fin.append v w' i)
        → ∃ i' : Fin k, (∀ j, Nat.lt j.val i'.val → w j = w' j)
            ∧ @LT.lt T _ (w i') (w' i'))
      (fun jp => ?_) (fun i₀ => ?_) i hlt hi
    · intro _ hc
      rw [Fin.append_left, Fin.append_left] at hc
      exact absurd hc (lt_irrefl _)
    · intro hlt' hi'
      rw [Fin.append_right, Fin.append_right] at hi'
      refine ⟨i₀, fun j hj => ?_, hi'⟩
      have hj' : Nat.lt (Fin.natAdd c j : Fin (c + k)).val
          (Fin.natAdd c i₀ : Fin (c + k)).val := by
        simp only [Fin.val_natAdd]
        exact Nat.add_lt_add_left hj c
      have hres := hlt' (Fin.natAdd c j) hj'
      rwa [Fin.append_right, Fin.append_right] at hres
  · rintro ⟨i, hlt, hi⟩
    refine ⟨Fin.natAdd c i, fun j hj => ?_, ?_⟩
    · refine Fin.addCases (motive := fun j =>
        Nat.lt j.val (Fin.natAdd c i : Fin (c + k)).val
          → (Fin.append v w : Tuple T (c + k)) j = Fin.append v w' j)
        (fun jp => ?_) (fun j₀ => ?_) j hj
      · intro _
        rw [Fin.append_left, Fin.append_left]
      · intro hj₀
        rw [Fin.append_right, Fin.append_right]
        refine hlt j₀ ?_
        simp only [Fin.val_natAdd] at hj₀
        exact Nat.lt_of_add_lt_add_left hj₀
    · rw [Fin.append_right, Fin.append_right]
      exact hi

/-- **Sorting commutes with prefixing a common block.** -/
theorem sortList_map_append {c k : ℕ} (v : Tuple T c)
    (M : Multiset (Tuple T k)) :
    sortList (Multiset.map (fun w => (Fin.append v w : Tuple T (c + k))) M
        : Multiset (Tuple T (c + k)))
      = (sortList M).map (fun w => (Fin.append v w : Tuple T (c + k))) := by
  refine (sortList_eq ?_ ?_).symm
  · refine List.pairwise_map.mpr
      ((sortList_pairwise M).imp (fun {a b} hab => ?_))
    rcases lt_or_eq_of_le hab with hlt | rfl
    · exact le_of_lt ((Fin.append_lt_append v a b).mpr hlt)
    · exact @le_refl (Tuple T (c + k)) _ (Fin.append v a)
  · exact Eq.trans (Multiset.map_coe _ _).symm
      (congrArg (Multiset.map (fun w => (Fin.append v w : Tuple T (c + k))))
        (sortList_coe M))

/-- The order columns, shifted. -/
def winOrd (c : ℕ) {k p : ℕ} (O : Tuple (Fin k) p) :
    Tuple (Fin (c + k)) p :=
  fun i => Fin.natAdd c (O i)

omit [ValueType T] in
/-- Prefixing a block does not change the order values the clause
reads. -/
theorem Tuple.key_winOrd {c k p : ℕ} (O : Tuple (Fin k) p) (v : Tuple T c)
    (u : Tuple T k) :
    Tuple.key (winOrd c O) (Fin.append v u : Tuple T (c + k))
      = Tuple.key O u :=
  funext (fun i => by
    show (Fin.append v u : Tuple T (c + k)) (Fin.natAdd c (O i)) = u (O i)
    rw [Fin.append_right])

/-- **The clause reads a prefixed pair as it reads the pair**: the order
values are the same, and the ties it leaves are broken by the rows, which
a common prefix does not reorder. -/
theorem OrderSpec.readLe_append {c k p : ℕ} (O : Tuple (Fin k) p)
    (o : OrderSpec p) (v : Tuple T c) (x y : Tuple T k) :
    OrderSpec.readLe (Tuple.key (winOrd c O))
        (id : Tuple T (c + k) → Tuple T (c + k)) o
        (Fin.append v x) (Fin.append v y)
      = OrderSpec.readLe (Tuple.key O) (id : Tuple T k → Tuple T k) o x y := by
  unfold OrderSpec.readLe
  simp only [id_eq]
  rw [Tuple.key_winOrd, Tuple.key_winOrd]
  by_cases hp : o.peer (Tuple.key O x) (Tuple.key O y) = true
  · rw [ite_eq_left hp, ite_eq_left hp]
    refine decide_eq_decide.mpr ?_
    show @LE.le (Tuple T (c + k)) _ (Fin.append v x) (Fin.append v y)
      ↔ @LE.le (Tuple T k) _ x y
    show (@LT.lt (Tuple T (c + k)) _ (Fin.append v x) (Fin.append v y)
        ∨ (Fin.append v x : Tuple T (c + k)) = Fin.append v y)
      ↔ (@LT.lt (Tuple T k) _ x y ∨ x = y)
    refine or_congr (Fin.append_lt_append v x y) ?_
    exact ⟨fun h => (Fin.append_inj h).2, fun h => by rw [h]⟩
  · rw [ite_eq_right hp, ite_eq_right hp]

/-- **Sorting by the clause commutes with prefixing a block.** -/
theorem OrderSpec.sortSeq_map_append {c k p : ℕ} (O : Tuple (Fin k) p)
    (o : OrderSpec p) (v : Tuple T c) (L : List (Tuple T k)) :
    OrderSpec.sortSeq (Tuple.key (winOrd c O))
        (id : Tuple T (c + k) → Tuple T (c + k)) o
        (L.map (fun x => (Fin.append v x : Tuple T (c + k))))
      = (OrderSpec.sortSeq (Tuple.key O) (id : Tuple T k → Tuple T k) o L).map
          (fun x => (Fin.append v x : Tuple T (c + k))) :=
  (List.map_insertionSort _
    (fun x y => OrderSpec.readLe (Tuple.key (winOrd c O))
      (id : Tuple T (c + k) → Tuple T (c + k)) o x y = true)
    (fun x => (Fin.append v x : Tuple T (c + k))) L
    (fun x y _ _ => by rw [OrderSpec.readLe_append])).symm

/-- The key columns of a decorrelated aggregation: the parameters, then
the key columns of the original. -/
def groupKey (c : ℕ) {m n₁ : ℕ} (is : Tuple (Fin m) n₁) :
    Tuple (Fin (c + m)) (c + n₁) :=
  Fin.append (fun j : Fin c => Fin.castAdd m j)
    (fun i : Fin n₁ => Fin.natAdd c (is i))

/-- **A group of the decorrelated query is a group of one slice**: the
parameters are part of the key, so the rows of the group at `(v, g)` are
the rows of `f v`'s group at `g`, with `v` in front. -/
theorem Relation.groupSeq_slices {c m n₁ : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (f : Tuple T c → Multiset (Tuple T m))
    (is : Tuple (Fin m) n₁) {v : Tuple T c} (hv : v ∈ P) (g : Tuple T n₁) :
    Relation.groupSeq (groupKey c is) (Relation.slices P f)
        (Fin.append v g)
      = (Relation.groupSeq is (f v) g).map
          (fun w => (Fin.append v w : Tuple T (c + m))) := by
  classical
  unfold Relation.groupSeq
  rw [← sortList_map_append]
  refine congrArg sortList ?_
  -- the rows of the group: those whose parameters are `v` and whose key
  -- columns carry `g`
  have hcond : ∀ u : Tuple T (c + m),
      (∀ k', u (groupKey c is k') = (Fin.append v g : Tuple T (c + n₁)) k')
        ↔ ((∀ i, (fun i' => u (Fin.natAdd c i')) (is i) = g i)
            ∧ Relation.paramsOf u = v) := by
    intro u
    constructor
    · intro h
      refine ⟨fun i => ?_, funext (fun jp => ?_)⟩
      · have hi := h (Fin.natAdd c i)
        rw [groupKey, Fin.append_right, Fin.append_right] at hi
        exact hi
      · have hj := h (Fin.castAdd n₁ jp)
        rw [groupKey, Fin.append_left, Fin.append_left] at hj
        exact hj
    · rintro ⟨hkey, hpar⟩ k'
      refine Fin.addCases (motive := fun k' =>
        u (groupKey c is k') = (Fin.append v g : Tuple T (c + n₁)) k')
        (fun jp => ?_) (fun i => ?_) k'
      · rw [groupKey, Fin.append_left, Fin.append_left]
        exact congrFun hpar jp
      · rw [groupKey, Fin.append_right, Fin.append_right]
        exact hkey i
  rw [Multiset.filter_congr (fun u _ => hcond u),
    show Multiset.filter (fun u : Tuple T (c + m) =>
          (∀ i, (fun i' => u (Fin.natAdd c i')) (is i) = g i)
            ∧ Relation.paramsOf u = v)
          (Relation.slices P f)
        = Multiset.filter (fun u : Tuple T (c + m) =>
            ∀ i, (fun i' => u (Fin.natAdd c i')) (is i) = g i)
            (Multiset.filter (fun u => Relation.paramsOf u = v)
              (Relation.slices P f))
      from (Multiset.filter_filter _ _ _).symm,
    Relation.filter_paramsOf_slices P hP f hv, Multiset.filter_map]
  refine congrArg _ (Multiset.filter_congr (fun w _ => ?_))
  refine forall_congr' (fun i => ?_)
  show (Fin.append v w : Tuple T (c + m)) (Fin.natAdd c (is i)) = g i ↔ _
  rw [Fin.append_right]

/-! ### A grouping's own clauses

An aggregation carries an `ORDER BY` of its own and a `FILTER` clause
per aggregate. Both read the input's columns, so both are shifted over
the parameter block: the order reads the column `c + i` where it read
`i`, which leaves the reading order unchanged (`OrderSpec.readLe_append`),
and the clause keeps the same rows (`Selection.keeps_shift`). -/

/-- **A grouping's `ORDER BY`, shifted over the parameters.** -/
def GroupOrder.lift (c : ℕ) {m : ℕ} : GroupOrder T m → GroupOrder T (c + m)
  | .unord => .unord
  | .byCols cols spec => .byCols (winOrd c cols) spec

/-- **A group of the decorrelated query, read in the clause's order**, is
one slice's group read in that order: the clause reads the shifted
columns, and the parameter block it shares does not reorder the rows. -/
theorem Relation.groupSeqOrd_slices {c m n₁ : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (f : Tuple T c → Multiset (Tuple T m))
    (is : Tuple (Fin m) n₁) (ord : GroupOrder T m) {v : Tuple T c}
    (hv : v ∈ P) (g : Tuple T n₁) :
    Relation.groupSeqOrd (groupKey c is) (ord.lift c) (Relation.slices P f)
        (Fin.append v g)
      = (Relation.groupSeqOrd is ord (f v) g).map
          (fun w => (Fin.append v w : Tuple T (c + m))) := by
  cases ord with
  | unord => exact Relation.groupSeq_slices P hP f is hv g
  | byCols cols spec =>
    show OrderSpec.sortSeq (Tuple.key (winOrd c cols))
        (id : Tuple T (c + m) → Tuple T (c + m)) spec
        (Relation.groupSeq (groupKey c is) (Relation.slices P f)
          (Fin.append v g)) = _
    rw [Relation.groupSeq_slices P hP f is hv g,
      OrderSpec.sortSeq_map_append cols spec v]
    rfl

/-- **And under a `FILTER` clause**, which keeps the same rows. -/
theorem Relation.groupSeqOptOrd_slices {c m n₁ : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (f : Tuple T c → Multiset (Tuple T m))
    (is : Tuple (Fin m) n₁) (ord : GroupOrder T m) {v : Tuple T c}
    (hv : v ∈ P) (g : Tuple T n₁) (keep : Option (Selection T m)) :
    Relation.groupSeqOptOrd (groupKey c is) (ord.lift c) (Relation.slices P f)
        (Fin.append v g) (keep.map (Selection.shift c))
      = (Relation.groupSeqOptOrd is ord (f v) g keep).map
          (fun w => (Fin.append v w : Tuple T (c + m))) := by
  cases keep with
  | none => exact Relation.groupSeqOrd_slices P hP f is ord hv g
  | some φ =>
    show ((Relation.groupSeqOrd (groupKey c is) (ord.lift c)
        (Relation.slices P f) (Fin.append v g)).filter
          (φ.shift c).keeps) = _
    rw [Relation.groupSeqOrd_slices P hP f is ord hv g, List.filter_map,
      show ((φ.shift c).keeps ∘ fun w => (Fin.append v w : Tuple T (c + m)))
          = φ.keeps from funext (fun w => Selection.keeps_shift c φ v w)]
    rfl

/-- Where each column of a decorrelated aggregation reads from: the
parameters and the key come from its key block, the aggregates from its
aggregate block. -/
def gammaSrc (c n₁ n₂ : ℕ) :
    Fin (c + (n₁ + n₂)) → Fin ((c + n₁) + n₂) :=
  Fin.addCases
    (fun jp : Fin c => Fin.castAdd n₂ (Fin.castAdd n₁ jp))
    (Fin.addCases (fun i : Fin n₁ => Fin.castAdd n₂ (Fin.natAdd c i))
      (fun j : Fin n₂ => Fin.natAdd (c + n₁) j))

set_option maxHeartbeats 1000000 in
/-- **A grouped aggregation** groups by the parameters as well: each
group is one slice's group, read in the same order, so the aggregates
read what they read there. -/
theorem AggQueryIn.hasDecorrelation_gamma {c m n₁ n₂ : ℕ}
    {P : AggQuery T c (ColKind.allReg c)}
    (hnd : ∀ D : Database T, (P.evaluatePlain D).Nodup)
    (is : Tuple (Fin m) n₁) (ts : Tuple (TermIn T c m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂)
    {q : AggQueryIn T c m (ColKind.allReg m)}
    (keep : Fin n₂ → Option (Selection T m)) (ord : GroupOrder T m)
    (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Gamma is ts fs q keep ord) := by
  classical
  obtain ⟨q', hu, hd⟩ := h
  set κg : Fin ((c + n₁) + n₂) → ColKind :=
    Fin.append (fun _ : Fin (c + n₁) => ColKind.reg)
      (fun _ : Fin n₂ => ColKind.agg) with hκg
  have hsrc : ∀ j, κg (gammaSrc c n₁ n₂ j)
      = ColKind.liftKinds c
          (Fin.append (fun _ : Fin n₁ => ColKind.reg)
            (fun _ : Fin n₂ => ColKind.agg)) j := by
    intro j
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
    · show κg (gammaSrc c n₁ n₂ (Fin.castAdd (n₁ + n₂) jp)) = _
      rw [gammaSrc, Fin.addCases_left, hκg, Fin.append_left,
        ColKind.liftKinds, Fin.append_left]
      rfl
    · show κg (gammaSrc c n₁ n₂ (Fin.natAdd c i)) = _
      rw [gammaSrc, Fin.addCases_right, ColKind.liftKinds, Fin.append_right]
      refine Fin.addCases (fun i₁ => ?_) (fun j₂ => ?_) i
      · rw [Fin.addCases_left, hκg, Fin.append_left, Fin.append_left]
      · rw [Fin.addCases_right, hκg, Fin.append_right, Fin.append_right]
  refine ⟨(AggQueryIn.Proj (fun j => AggQueryIn.carryCol κg (gammaSrc c n₁ n₂ j))
      (AggQueryIn.Gamma (groupKey c is) (fun j => (ts j).lift) fs
        (q'.castKind (AggQueryIn.append_allReg c m))
        (fun j => (keep j).map (Selection.shift c)) (ord.lift c))).castKind
      (funext (fun j => (AggQueryIn.carryCol_kind κg _).trans (hsrc j))),
    ?_, fun D => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], by simp [basisOps],
      (AggQueryIn.usesOnly_castKind _ _ _).mpr hu⟩
  rw [AggQueryIn.evaluatePlain_castKind]
  -- the keys are the slices of the input's keys, and the group at each
  -- one is that slice's group
  show Multiset.map (fun u => (fun j =>
      (AggQueryIn.carryCol κg (gammaSrc c n₁ n₂ j)).evalPlain u (fun _ => 0)))
      (Multiset.map (fun g => (Fin.append g (fun j => (fs j)
          ((Relation.groupSeqOptOrd (groupKey c is) (ord.lift c)
              ((q'.castKind (AggQueryIn.append_allReg c m)).evaluatePlain D) g
              ((keep j).map (Selection.shift c))).map
            (fun w => ((ts j).lift).eval w (fun _ => 0))))
          : Tuple T ((c + n₁) + n₂)))
        ((Multiset.map (fun u : Tuple T (c + m) =>
            (fun k => u (groupKey c is k) : Tuple T (c + n₁)))
          ((q'.castKind (AggQueryIn.append_allReg c m)).evaluatePlain D)).dedup))
    = _
  rw [AggQueryIn.evaluatePlain_castKind, hd]
  -- the keys
  rw [show Multiset.map (fun u : Tuple T (c + m) =>
          (fun k => u (groupKey c is k) : Tuple T (c + n₁)))
        (Relation.slices (P.evaluatePlain D) (fun v => q.evaluatePlain D v))
      = Relation.slices (P.evaluatePlain D) (fun v =>
          (q.evaluatePlain D v).map
            (fun w => (fun i => w (is i) : Tuple T n₁))) from by
    refine Eq.trans (Multiset.map_congr rfl (fun x _ => funext (fun k => ?_)))
      (Relation.slices_map (P.evaluatePlain D) (fun v => q.evaluatePlain D v)
        (fun _ w => (fun i => w (is i) : Tuple T n₁)))
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) k
    · rw [Fin.append_left, groupKey, Fin.append_left]
    · rw [Fin.append_right, groupKey, Fin.append_right],
    Relation.slices_dedup _ (hnd D), Multiset.map_map]
  -- each key row gives the parameters, the key and the aggregates read
  -- over that slice's group
  refine Eq.trans (Multiset.map_congr rfl (fun x hx => ?_))
    (Relation.slices_map (P.evaluatePlain D)
      (fun v => ((q.evaluatePlain D v).map
        (fun w => (fun i => w (is i) : Tuple T n₁))).dedup)
      (fun v g => (Fin.append g (fun j => fs j
        ((Relation.groupSeqOptOrd is ord (q.evaluatePlain D v) g (keep j)).map
          (fun w => (ts j).eval w v))) : Tuple T (n₁ + n₂))))
  obtain ⟨v, hv, g, -, rfl⟩ := (Relation.mem_slices _ _ x).mp hx
  simp only [Function.comp_apply]
  rw [show (fun j => (Fin.append v g : Tuple T (c + n₁)) (Fin.castAdd n₁ j))
        = v from funext (fun j => by rw [Fin.append_left]),
    show (fun i => (Fin.append v g : Tuple T (c + n₁)) (Fin.natAdd c i))
        = g from funext (fun i => by rw [Fin.append_right])]
  funext j
  rw [AggQueryIn.evalPlain_carryCol]
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · rw [Fin.append_left, gammaSrc, Fin.addCases_left, Fin.append_left,
      Fin.append_left]
  · rw [Fin.append_right, gammaSrc, Fin.addCases_right]
    refine Fin.addCases (fun i₁ => ?_) (fun j₂ => ?_) i
    · rw [Fin.addCases_left, Fin.append_left, Fin.append_left,
        Fin.append_right]
    · rw [Fin.addCases_right, Fin.append_right, Fin.append_right]
      refine congrArg (fs j₂) ?_
      rw [Relation.groupSeqOptOrd_slices (P.evaluatePlain D) (hnd D)
        (fun v => q.evaluatePlain D v) is ord hv g (keep j₂), List.map_map]
      refine List.map_congr_left (fun w _ => ?_)
      exact TermIn.eval_lift (ts j₂) v w

/-! ### The scalar aggregation

A scalar aggregation has one row whatever its input, so the
decorrelation has one row per parameter row – including those whose
slice is empty, which a grouping by the parameters does not produce.
Those are recovered from the parameter rows the slices do not reach, as
`prop:collapse` has it. Where the paper writes the aggregates' value on
no input as a *constant term*, the library writes it as a constant
aggregate: a projection column carrying a constant is a regular column,
and the column a scalar aggregation produces is an aggregate one, so only
an aggregating operator can build it. -/

/-- The group of a decorrelated query at a parameter row, when the
parameters are the whole key: the slice itself. -/
theorem Relation.groupSeq_paramsKey {c m : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (f : Tuple T c → Multiset (Tuple T m))
    {v : Tuple T c} (hv : v ∈ P) :
    Relation.groupSeq (fun j : Fin c => Fin.castAdd m j)
        (Relation.slices P f) v
      = (sortList (f v)).map (fun w => (Fin.append v w : Tuple T (c + m))) := by
  classical
  unfold Relation.groupSeq
  rw [← sortList_map_append]
  refine congrArg sortList ?_
  refine Eq.trans (Multiset.filter_congr (fun u _ => ?_))
    (Relation.filter_paramsOf_slices P hP f hv)
  show (∀ j, u (Fin.castAdd m j) = v j) ↔ Relation.paramsOf u = v
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

/-- A group with no key columns is the whole relation, sorted. -/
@[simp] theorem Relation.groupSeq_emptyKey {m : ℕ}
    (r : Multiset (Tuple T m)) :
    Relation.groupSeq (fun k : Fin 0 => k.elim0) r
        (fun k : Fin 0 => k.elim0) = sortList r := by
  unfold Relation.groupSeq
  rw [Multiset.filter_eq_self.mpr (fun u _ => fun k => k.elim0)]

/-- **The parameter rows the slices reach** are those with a non-empty
slice, each once. -/
theorem Relation.dedup_paramsOf_slices {c m : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (f : Tuple T c → Multiset (Tuple T m)) :
    ((Relation.slices P f).map Relation.paramsOf).dedup
      = P.filter (fun v => f v ≠ 0) := by
  classical
  refine Multiset.Nodup.ext (Multiset.nodup_dedup _)
    (hP.filter _) |>.mpr (fun v => ?_)
  rw [Multiset.mem_dedup, Multiset.mem_filter]
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hv
    obtain ⟨v', hv', w, hw, rfl⟩ := (Relation.mem_slices _ _ x).mp hx
    refine ⟨?_, ?_⟩
    · show Relation.paramsOf (Fin.append v' w : Tuple T (c + m)) ∈ P
      rw [Relation.paramsOf_append]
      exact hv'
    · rw [Relation.paramsOf_append]
      exact fun h0 => absurd hw (by rw [h0]; exact Multiset.notMem_zero w)
  · rintro ⟨hv, hne⟩
    obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hne
    refine Multiset.mem_map.mpr ⟨Fin.append v w, ?_, ?_⟩
    · exact (Relation.mem_slices _ _ _).mpr ⟨v, hv, w, hw, rfl⟩
    · exact Relation.paramsOf_append v w

/-- **And the ones they do not reach** are those with an empty slice. -/
theorem Relation.filter_notMem_paramsOf_slices {c m : ℕ}
    (P : Multiset (Tuple T c)) (f : Tuple T c → Multiset (Tuple T m)) :
    Multiset.filter
        (fun v => v ∉ (Relation.slices P f).map Relation.paramsOf) P
      = P.filter (fun v => f v = 0) := by
  classical
  refine Multiset.filter_congr (fun v hv => ?_)
  constructor
  · intro hnot
    by_contra h0
    obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero h0
    refine hnot (Multiset.mem_map.mpr ⟨Fin.append v w, ?_, ?_⟩)
    · exact (Relation.mem_slices _ _ _).mpr ⟨v, hv, w, hw, rfl⟩
    · exact Relation.paramsOf_append v w
  · intro h0 hmem
    obtain ⟨x, hx, hpar⟩ := Multiset.mem_map.mp hmem
    obtain ⟨v', hv', w, hw, rfl⟩ := (Relation.mem_slices _ _ x).mp hx
    rw [Relation.paramsOf_append] at hpar
    subst hpar
    exact absurd hw (by rw [h0]; exact Multiset.notMem_zero w)

set_option maxHeartbeats 1000000 in
/-- **An empty relation has an empty group**, whatever order the clause
asks for. -/
@[simp] theorem Relation.groupSeqOrd_zero {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (ord : GroupOrder T m) (g : Tuple T n₁) :
    Relation.groupSeqOrd is ord (0 : Relation T m) g = [] := by
  cases ord with
  | unord => rfl
  | byCols cols spec =>
    show OrderSpec.sortSeq (Tuple.key cols) (id : Tuple T m → Tuple T m) spec
        (Relation.groupSeq is (0 : Relation T m) g) = []
    rw [show Relation.groupSeq is (0 : Relation T m) g = [] from rfl]
    rfl

/-- **The group at a parameter row, read in the clause's order**: the
slice itself, read in that order. -/
theorem Relation.groupSeqOrd_paramsKey {c m : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (f : Tuple T c → Multiset (Tuple T m))
    (ord : GroupOrder T m) {v : Tuple T c} (hv : v ∈ P) :
    Relation.groupSeqOrd (fun j : Fin c => Fin.castAdd m j) (ord.lift c)
        (Relation.slices P f) v
      = (Relation.groupSeqOrd (fun k : Fin 0 => k.elim0) ord (f v)
          (fun k : Fin 0 => k.elim0)).map
          (fun w => (Fin.append v w : Tuple T (c + m))) := by
  cases ord with
  | unord =>
    show Relation.groupSeqOrd (fun j : Fin c => Fin.castAdd m j)
        GroupOrder.unord (Relation.slices P f) v = _
    rw [Relation.groupSeqOrd_unord, Relation.groupSeqOrd_unord,
      Relation.groupSeq_emptyKey]
    exact Relation.groupSeq_paramsKey P hP f hv
  | byCols cols spec =>
    show OrderSpec.sortSeq (Tuple.key (winOrd c cols))
        (id : Tuple T (c + m) → Tuple T (c + m)) spec
        (Relation.groupSeq (fun j : Fin c => Fin.castAdd m j)
          (Relation.slices P f) v) = _
    rw [Relation.groupSeq_paramsKey P hP f hv,
      OrderSpec.sortSeq_map_append cols spec v]
    show _ = (OrderSpec.sortSeq (Tuple.key cols)
      (id : Tuple T m → Tuple T m) spec
        (Relation.groupSeq (fun k : Fin 0 => k.elim0) (f v)
          (fun k : Fin 0 => k.elim0))).map _
    rw [Relation.groupSeq_emptyKey]

/-- **A scalar aggregation**: one row per parameter row. Grouping the
decorrelation by the parameters gives those whose slice is non-empty;
the others are the parameter rows the slices do not reach, carrying each
aggregate's value on no input. -/
theorem AggQueryIn.hasDecorrelation_gammaScalar {c m n₂ : ℕ}
    {P : AggQuery T c (ColKind.allReg c)} (hPu : P.usesOnly basisOps)
    (hnd : ∀ D : Database T, (P.evaluatePlain D).Nodup)
    (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    {q : AggQueryIn T c m (ColKind.allReg m)} (ord : GroupOrder T m)
    (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.GammaScalar ts fs q ord) := by
  obtain ⟨q', hu, hd⟩ := h
  -- the parameters of the decorrelated rows, as a query
  set paramCols : Tuple (ProjCol T (ColKind.liftKinds c (ColKind.allReg m))) c :=
    fun j => ProjColIn.term (TermGIn.index (Fin.castAdd m j)
      (ColKind.liftKinds_param c (ColKind.allReg m) j)) with hpc
  set reached : AggQuery T c (ColKind.allReg c) :=
    (AggQueryIn.Proj paramCols q').castKind rfl with hreached
  -- the parameter rows the slices do not reach
  set missing : AggQuery T c (ColKind.allReg c) :=
    AggQueryIn.Diff P reached with hmissing
  refine ⟨AggQueryIn.Sum
      (AggQueryIn.Gamma (fun j : Fin c => Fin.castAdd m j)
        (fun j => (ts j).lift) fs
        (q'.castKind (AggQueryIn.append_allReg c m)) (fun _ => none)
        (ord.lift c))
      (AggQueryIn.Gamma (fun j : Fin c => j) (fun _ => TermIn.const 0)
        (fun j => fun _ => fs j []) missing), ?_, fun D => ?_⟩
  · refine ⟨by simp [basisOps], ⟨by simp [basisOps], ?_⟩,
      ⟨by simp [basisOps], ?_⟩⟩
    · exact (AggQueryIn.usesOnly_castKind _ _ _).mpr hu
    · refine ⟨by simp [basisOps], hPu, ?_⟩
      rw [hreached, AggQueryIn.usesOnly_castKind]
      exact ⟨by simp [basisOps], hu⟩
  -- the slices, as a function into multisets: what the lemmas read
  set Pr : Multiset (Tuple T c) := P.evaluatePlain D with hPr
  set f : Tuple T c → Multiset (Tuple T m) := fun v => q.evaluatePlain D v
    with hf
  have hreach : (reached.evaluatePlain D : Multiset (Tuple T c))
      = (Relation.slices Pr f).map Relation.paramsOf := by
    rw [hreached, AggQueryIn.evaluatePlain_castKind]
    show Multiset.map (fun u => (fun j => (paramCols j).evalPlain u
        (fun _ => 0))) (q'.evaluatePlain D) = _
    rw [hd]
    refine Multiset.map_congr rfl (fun x _ => funext (fun j => ?_))
    rw [hpc]
    rfl
  have hmiss : (missing.evaluatePlain D : Multiset (Tuple T c))
      = Pr.filter (fun v => f v = 0) := by
    rw [hmissing]
    refine Eq.trans (Multiset.filter_congr (fun v _ => ?_))
      (Relation.filter_notMem_paramsOf_slices Pr f)
    exact not_congr (Iff.of_eq (congrArg (fun S => v ∈ S) hreach))
  -- the `Gamma` case of the plain evaluator, with the clauses it carries
  have hgamma : ∀ {m' n₁' n₂' : ℕ} (js : Tuple (Fin m') n₁')
      (ts' : Tuple (TermIn T 0 m') n₂') (fs' : Tuple (SeqAggFunc T) n₂')
      (qq : AggQuery T m' (ColKind.allReg m'))
      (kp : Fin n₂' → Option (Selection T m')) (od : GroupOrder T m'),
      (AggQueryIn.Gamma js ts' fs' qq kp od).evaluatePlain D
        = ((qq.evaluatePlain D).map
            (fun u => (fun k => u (js k) : Tuple T n₁'))).dedup.map
          (fun g => Fin.append g (fun j => (fs' j)
            ((Relation.groupSeqOptOrd js od (qq.evaluatePlain D) g (kp j)).map
              (fun w => (ts' j).eval w (fun _ => 0))))) :=
    fun _ _ _ _ _ _ => rfl
  show (AggQueryIn.Gamma _ _ _ _ _ _).evaluatePlain D
      + (AggQueryIn.Gamma _ _ _ _ _ _).evaluatePlain D = _
  rw [hgamma, hgamma, AggQueryIn.evaluatePlain_castKind, hd, hmiss]
  rw [show Multiset.map (fun u : Tuple T (c + m) =>
          (fun k => u (Fin.castAdd m k) : Tuple T c)) (Relation.slices Pr f)
      = (Relation.slices Pr f).map Relation.paramsOf from rfl,
    Relation.dedup_paramsOf_slices _ (hnd D)]
  -- the second part's keys are the parameter rows it is built from
  rw [show (Multiset.map (fun u : Tuple T c => (fun k => u k : Tuple T c))
        (Pr.filter (fun v => f v = 0))).dedup
      = Pr.filter (fun v => f v = 0) from by
    rw [Multiset.map_id']
    exact ((hnd D).filter _).dedup]
  -- the source gives one row per parameter row, read over the whole slice
  show _ = Relation.slices Pr (fun v =>
    (Multiset.ofList [(fun j => (fs j)
      ((Relation.groupSeqOrd (fun k : Fin 0 => k.elim0) ord
        (f v) (fun k : Fin 0 => k.elim0)).map
          (fun w => (ts j).eval w v)) : Tuple T n₂)] : Relation T n₂))
  have hrhs : Relation.slices Pr (fun v =>
        (Multiset.ofList [(fun j => (fs j)
          ((Relation.groupSeqOrd (fun k : Fin 0 => k.elim0) ord
            (f v) (fun k : Fin 0 => k.elim0)).map
              (fun w => (ts j).eval w v)) : Tuple T n₂)] : Relation T n₂))
      = Pr.map (fun v => (Fin.append v (fun j => (fs j)
          ((Relation.groupSeqOrd (fun k : Fin 0 => k.elim0) ord (f v)
              (fun k : Fin 0 => k.elim0)).map
            (fun w => (ts j).eval w v)))
            : Tuple T (c + n₂))) := by
    rw [Relation.slices]
    exact Multiset.bind_singleton (s := Pr) (fun v => (Fin.append v
      (fun j => (fs j)
        ((Relation.groupSeqOrd (fun k : Fin 0 => k.elim0) ord (f v)
            (fun k : Fin 0 => k.elim0)).map
          (fun w => (ts j).eval w v))) : Tuple T (c + n₂)))
  rw [hrhs]
  -- the two parts are the parameter rows with a non-empty slice and the rest
  refine Eq.trans ?_ (congrArg (Multiset.map (fun v =>
      (Fin.append v (fun j => (fs j)
        ((Relation.groupSeqOrd (fun k : Fin 0 => k.elim0) ord (f v)
            (fun k : Fin 0 => k.elim0)).map
          (fun w => (ts j).eval w v)))
          : Tuple T (c + n₂))))
    (Multiset.filter_add_not (fun v => f v ≠ 0) Pr))
  rw [Multiset.map_add]
  refine congrArg₂ (· + ·) (Multiset.map_congr rfl (fun v hv => ?_))
    (Eq.trans (Multiset.map_congr rfl (fun v hv => ?_))
      (congrArg (Multiset.map _) (Multiset.filter_congr (fun v _ =>
        ⟨fun h0 => not_not_intro h0, fun hnn => Classical.not_not.mp hnn⟩))))
  · -- a non-empty slice: the group is the slice, read in the same order
    refine congrArg (Fin.append v) (funext (fun j => congrArg (fs j) ?_))
    rw [Relation.groupSeqOptOrd_none,
      Relation.groupSeqOrd_paramsKey Pr (hnd D) f ord
        (Multiset.mem_filter.mp hv).1, List.map_map]
    exact List.map_congr_left (fun w _ => TermIn.eval_lift (ts j) v w)
  · -- an empty slice: every aggregate reads the empty sequence
    rw [(Multiset.mem_filter.mp hv).2, Relation.groupSeqOrd_zero]
    simp only [List.map_nil]

/-! ### Windows: the parameters join the partition

A window of the decorrelated query partitions by the parameters as well,
so each partition lies inside one slice; the frames are then the frames
of that slice, read in the same order, because the clause reads the
shifted order columns and the parameter block it shares is read first. -/

/-- The partition columns of a decorrelated window: the parameters, then
the partition columns of the original. -/
def winPart (c : ℕ) {k mp : ℕ} (P' : Tuple (Fin k) mp) :
    Tuple (Fin (c + k)) (c + mp) :=
  Fin.append (fun j : Fin c => Fin.castAdd k j)
    (fun i : Fin mp => Fin.natAdd c (P' i))

omit [ValueType T] in
/-- And the partition key is the parameters beside the original key. -/
theorem Tuple.key_winPart {c k mp : ℕ} (P' : Tuple (Fin k) mp)
    (v : Tuple T c) (u : Tuple T k) :
    Tuple.key (winPart c P') (Fin.append v u : Tuple T (c + k))
      = Fin.append v (Tuple.key P' u) := by
  funext j
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · show (Fin.append v u : Tuple T (c + k))
        (winPart c P' (Fin.castAdd mp jp)) = _
    rw [winPart, Fin.append_left, Fin.append_left, Fin.append_left]
  · show (Fin.append v u : Tuple T (c + k))
        (winPart c P' (Fin.natAdd c i)) = _
    rw [winPart, Fin.append_right, Fin.append_right, Fin.append_right]
    rfl

omit [ValueType T] in
/-- **Which decision procedure an erasure uses does not matter**: a
decidable equality is unique, and the frame machinery's comes from the
domain's order where instance search finds the pointwise one. -/
theorem Multiset.erase_instEq {α : Type} (i j : DecidableEq α)
    (s : Multiset α) (a : α) :
    @Multiset.erase α i s a = @Multiset.erase α j s a := by
  rw [Subsingleton.elim i j]

/-- **Erasing a row of one slice is erasing it from that slice**: the
parameter block is carried along injectively, so one occurrence goes on
each side. -/
theorem Multiset.map_erase_append {c k : ℕ} (v : Tuple T c) (u : Tuple T k)
    (X : Multiset (Tuple T k)) :
    @Multiset.erase (Tuple T (c + k)) (fun a b => LinearOrder.toDecidableEq a b)
        (X.map (fun x => (Fin.append v x : Tuple T (c + k)))) (Fin.append v u)
      = (@Multiset.erase (Tuple T k) (fun a b => LinearOrder.toDecidableEq a b)
          X u).map (fun x => (Fin.append v x : Tuple T (c + k))) := by
  classical
  rw [Multiset.erase_instEq _ (fun a b => instDecidableEqTuple a b),
    Multiset.erase_instEq (α := Tuple T k)
      _ (fun a b => instDecidableEqTuple a b)]
  exact (Multiset.map_erase (fun x => (Fin.append v x : Tuple T (c + k)))
    (fun a b hab => (Fin.append_inj hab).2) u X).symm

/-- **A frame of the decorrelated query is a frame of one slice**: the
parameters are part of the partition key, so a row of another slice is in
no frame, and within a slice the frame condition reads the same values.
`EXCLUDE CURRENT ROW` and `EXCLUDE TIES` are covered too: the row the
frame takes out is the same row on both sides. -/
theorem ValueFrame.frameOf_slices {c k mp p : ℕ} (P : Multiset (Tuple T c))
    (hP : P.Nodup) (f : Tuple T c → Multiset (Tuple T k))
    (P' : Tuple (Fin k) mp) (O : Tuple (Fin k) p) (w : ValueFrame T p)
    {v : Tuple T c} (hv : v ∈ P) (u : Tuple T k) :
    ValueFrame.frameOf (α := Tuple T (c + k)) id (winPart c P') (winOrd c O) w
        (Relation.slices P f) (Fin.append v u)
      = (ValueFrame.frameOf (α := Tuple T k) id P' O w (f v) u).map
          (fun x => (Fin.append v x : Tuple T (c + k))) := by
  classical
  -- the rows the frame condition keeps are its slice's
  have hcond : ∀ y : Tuple T (c + k),
      (Tuple.key (winPart c P') (id y)
            = Tuple.key (winPart c P') (id (Fin.append v u : Tuple T (c + k)))
          ∧ w.ρ (Tuple.key (winOrd c O) (id y))
              (Tuple.key (winOrd c O)
                (id (Fin.append v u : Tuple T (c + k)))) = true)
        ↔ ((Tuple.key P' (fun i => y (Fin.natAdd c i)) = Tuple.key P' u
              ∧ w.ρ (Tuple.key O (fun i => y (Fin.natAdd c i)))
                  (Tuple.key O u) = true)
            ∧ Relation.paramsOf y = v) := by
    intro y
    rw [show (id y : Tuple T (c + k)) = y from rfl,
      show (id (Fin.append v u : Tuple T (c + k))) = Fin.append v u from rfl,
      Tuple.key_winPart, Tuple.key_winOrd]
    rw [show Tuple.key (winPart c P') y
        = Fin.append (Relation.paramsOf y)
            (Tuple.key P' (fun i => y (Fin.natAdd c i))) from by
      conv_lhs => rw [← Relation.append_paramsOf y]
      rw [Tuple.key_winPart],
      show Tuple.key (winOrd c O) y
        = Tuple.key O (fun i => y (Fin.natAdd c i)) from by
      conv_lhs => rw [← Relation.append_paramsOf y]
      rw [Tuple.key_winOrd]]
    constructor
    · rintro ⟨hk, hρ⟩
      obtain ⟨hpar, hkey⟩ := Fin.append_inj hk
      exact ⟨⟨hkey, hρ⟩, hpar⟩
    · rintro ⟨⟨hkey, hρ⟩, hpar⟩
      exact ⟨by rw [hpar, hkey], hρ⟩
  have hfil : Multiset.filter (fun y : Tuple T (c + k) =>
        Tuple.key (winPart c P') (id y)
            = Tuple.key (winPart c P') (id (Fin.append v u : Tuple T (c + k)))
          ∧ w.ρ (Tuple.key (winOrd c O) (id y))
              (Tuple.key (winOrd c O)
                (id (Fin.append v u : Tuple T (c + k)))) = true)
        (Relation.slices P f)
      = (Multiset.filter (fun x : Tuple T k =>
          Tuple.key P' (id x) = Tuple.key P' (id u)
            ∧ w.ρ (Tuple.key O (id x)) (Tuple.key O (id u)) = true)
          (f v)).map (fun x => (Fin.append v x : Tuple T (c + k))) := by
    rw [Multiset.filter_congr (fun y _ => hcond y),
      show Multiset.filter (fun y : Tuple T (c + k) =>
            (Tuple.key P' (fun i => y (Fin.natAdd c i)) = Tuple.key P' u
                ∧ w.ρ (Tuple.key O (fun i => y (Fin.natAdd c i)))
                    (Tuple.key O u) = true)
              ∧ Relation.paramsOf y = v)
            (Relation.slices P f)
          = Multiset.filter (fun y : Tuple T (c + k) =>
              Tuple.key P' (fun i => y (Fin.natAdd c i)) = Tuple.key P' u
                ∧ w.ρ (Tuple.key O (fun i => y (Fin.natAdd c i)))
                    (Tuple.key O u) = true)
              (Multiset.filter (fun y => Relation.paramsOf y = v)
                (Relation.slices P f))
        from (Multiset.filter_filter _ _ _).symm,
      Relation.filter_paramsOf_slices P hP f hv, Multiset.filter_map]
    refine congrArg _ (Multiset.filter_congr (fun y _ => ?_))
    simp only [Function.comp_apply, id_eq]
    rw [show (fun i => (Fin.append v y : Tuple T (c + k)) (Fin.natAdd c i))
        = y from funext (fun i => by rw [Fin.append_right])]
  -- and the row the frame takes out is the same row on both sides
  unfold ValueFrame.frameOf
  by_cases hs : w.s (Tuple.key (winOrd c O)
      (id (Fin.append v u : Tuple T (c + k)))) = true
  · have hs' : w.s (Tuple.key O (id u)) = true := by
      rw [show (id u : Tuple T k) = u from rfl, ← Tuple.key_winOrd O v u]
      exact hs
    rw [ite_eq_left hs, ite_eq_left hs', hfil, Multiset.map_erase_append,
      ← Multiset.map_cons]
  · have hs' : ¬ w.s (Tuple.key O (id u)) = true := by
      rw [show (id u : Tuple T k) = u from rfl, ← Tuple.key_winOrd O v u]
      exact hs
    rw [ite_eq_right hs, ite_eq_right hs', hfil, Multiset.map_erase_append]

/-- **And so is the sequence it is read as.** -/
theorem ValueFrame.frameListOf_slices {c k mp p : ℕ}
    (P : Multiset (Tuple T c)) (hP : P.Nodup)
    (f : Tuple T c → Multiset (Tuple T k)) (P' : Tuple (Fin k) mp)
    (O : Tuple (Fin k) p) (o : OrderSpec p) (w : ValueFrame T p)
    {v : Tuple T c} (hv : v ∈ P) (u : Tuple T k) :
    ValueFrame.frameListOf (α := Tuple T (c + k)) id (winPart c P')
        (winOrd c O) o w (Relation.slices P f) (Fin.append v u)
      = (ValueFrame.frameListOf (α := Tuple T k) id P' O o w (f v) u).map
          (fun x => (Fin.append v x : Tuple T (c + k))) := by
  unfold ValueFrame.frameListOf
  rw [ValueFrame.frameOf_slices P hP f P' O w hv u, sortList_map_append,
    OrderSpec.sortSeq_map_append]

/-- **What a window reads of a decorrelated row**: the parameters, which
are regular columns and so read as they stand, and what it reads of the
row's own half. -/
theorem ColKind.readTuple_liftKinds {c k : ℕ} (κ : Fin k → ColKind)
    (v : Tuple T c) (u : Tuple T k) :
    ColKind.readTuple (ColKind.liftKinds c κ)
        (Fin.append v u : Tuple T (c + k))
      = (Fin.append v (ColKind.readTuple κ u) : Tuple T (c + k)) := by
  funext j
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · show (match (ColKind.liftKinds c κ (Fin.castAdd k jp)).base with
        | ColKind.agg => 0
        | _ => (Fin.append v u : Tuple T (c + k)) (Fin.castAdd k jp))
      = (Fin.append v (ColKind.readTuple κ u) : Tuple T (c + k))
          (Fin.castAdd k jp)
    rw [ColKind.liftKinds_param, Fin.append_left, Fin.append_left]
    rfl
  · show (match (ColKind.liftKinds c κ (Fin.natAdd c i)).base with
        | ColKind.agg => 0
        | _ => (Fin.append v u : Tuple T (c + k)) (Fin.natAdd c i))
      = (Fin.append v (ColKind.readTuple κ u) : Tuple T (c + k))
          (Fin.natAdd c i)
    rw [ColKind.liftKinds_col, Fin.append_right, Fin.append_right]
    rfl

omit [ValueType T] in
/-- **A window of the decorrelated query reads regular columns too**:
the parameters are regular, and the partition, the order and the term
read what they read before. -/
theorem winReadsReg_lift {c k mp p : ℕ} {κ : Fin k → ColKind}
    {P' : Tuple (Fin k) mp} {O : Tuple (Fin k) p} {t : TermIn T c k}
    (hrr : WinReadsReg κ P' O t) :
    WinReadsReg (ColKind.liftKinds c κ) (winPart c P') (winOrd c O)
      (t.lift (T := T)) := by
  refine ⟨fun j => ?_, fun i => ?_,
    by rw [TermIn.regOnly_lift]; exact hrr.2.2⟩
  · refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
    · show (ColKind.liftKinds c κ (winPart c P' (Fin.castAdd mp jp))).base
        = ColKind.reg
      rw [winPart, Fin.append_left, ColKind.liftKinds_param]
      rfl
    · show (ColKind.liftKinds c κ (winPart c P' (Fin.natAdd c i))).base
        = ColKind.reg
      rw [winPart, Fin.append_right, ColKind.liftKinds_col]
      exact hrr.1 i
  · show (ColKind.liftKinds c κ (winOrd c O i)).base = ColKind.reg
    rw [winOrd, ColKind.liftKinds_col]
    exact hrr.2.1 i

/-- **The value a window's column takes on a decorrelated row** is the
value it takes on the row of its slice: the frame is that slice's frame,
and the term reads the parameters off the row instead of the context. -/
theorem ValueFrame.windowValue_slices {c k mp p : ℕ}
    (P : Multiset (Tuple T c)) (hP : P.Nodup)
    (f : Tuple T c → Multiset (Tuple T k)) (P' : Tuple (Fin k) mp)
    (O : Tuple (Fin k) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c k) (g : SeqAggFunc T)
    {v : Tuple T c} (hv : v ∈ P) (u : Tuple T k) :
    ValueFrame.windowValue (winPart c P') (winOrd c O) o w t.lift g
        (Relation.slices P f) (Fin.append v u) (fun _ => 0)
      = ValueFrame.windowValue P' O o w t g (f v) u v := by
  unfold ValueFrame.windowValue
  rw [ValueFrame.frameListOf_slices P hP f P' O o w hv u, List.map_map]
  refine congrArg g (List.map_congr_left (fun x _ => ?_))
  exact TermIn.eval_lift t v x

/-- **And so under a `FILTER` clause**, which keeps the same rows of the
frame, reading them through the shifted columns. -/
theorem ValueFrame.windowValueWhen_slices {c k mp p : ℕ}
    (P : Multiset (Tuple T c)) (hP : P.Nodup)
    (f : Tuple T c → Multiset (Tuple T k)) (P' : Tuple (Fin k) mp)
    (O : Tuple (Fin k) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c k) (g : SeqAggFunc T)
    (φ : Selection T k) {v : Tuple T c} (hv : v ∈ P) (u : Tuple T k) :
    ValueFrame.windowValueWhen (winPart c P') (winOrd c O) o w t.lift g
        (φ.shift c).keeps (Relation.slices P f) (Fin.append v u) (fun _ => 0)
      = ValueFrame.windowValueWhen P' O o w t g φ.keeps (f v) u v := by
  unfold ValueFrame.windowValueWhen
  rw [ValueFrame.frameListOf_slices P hP f P' O o w hv u,
    List.filter_map, List.map_map,
    show ((φ.shift c).keeps ∘ fun x => (Fin.append v x : Tuple T (c + k)))
        = φ.keeps from funext (fun x => Selection.keeps_shift c φ v x)]
  refine congrArg g (List.map_congr_left (fun x _ => ?_))
  show (t.lift).eval (Fin.append v x) (fun _ => 0) = t.eval x v
  exact TermIn.eval_lift t v x

/-- **The clause or no clause.** -/
theorem ValueFrame.windowValueOpt_slices {c k mp p : ℕ}
    (P : Multiset (Tuple T c)) (hP : P.Nodup)
    (f : Tuple T c → Multiset (Tuple T k)) (P' : Tuple (Fin k) mp)
    (O : Tuple (Fin k) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c k) (g : SeqAggFunc T)
    (keep : Option (Selection T k)) {v : Tuple T c} (hv : v ∈ P)
    (u : Tuple T k) :
    ValueFrame.windowValueOpt (winPart c P') (winOrd c O) o w t.lift g
        (keep.map (Selection.shift c)) (Relation.slices P f)
        (Fin.append v u) (fun _ => 0)
      = ValueFrame.windowValueOpt P' O o w t g keep (f v) u v := by
  cases keep with
  | none =>
    exact ValueFrame.windowValue_slices P hP f P' O o w t g hv u
  | some φ =>
    exact ValueFrame.windowValueWhen_slices P hP f P' O o w t g φ hv u

/-- The column a decorrelated window's row takes each of its own from:
the parameters, the input's columns and the window's column last. -/
def winSrc (c n : ℕ) : Fin (c + (n + 1)) → Fin ((c + n) + 1) :=
  Fin.addCases (fun jp : Fin c => (Fin.castAdd n jp).castSucc)
    (Fin.lastCases (Fin.last (c + n)) (fun i : Fin n => (Fin.natAdd c i).castSucc))

omit [ValueType T] in
/-- **The kinds a decorrelated window's columns are read from**: a
parameter and an input column keep their kind, and the column the window
adds is the aggregate one. -/
theorem ColKind.snoc_winSrc {c n : ℕ} (κ : Fin n → ColKind)
    {κ' : Fin (c + n) → ColKind} (h : κ' = ColKind.liftKinds c κ)
    (j : Fin (c + (n + 1))) :
    (Fin.snoc κ' ColKind.agg : Fin ((c + n) + 1) → ColKind) (winSrc c n j)
      = ColKind.liftKinds c (Fin.snoc κ ColKind.agg) j := by
  subst h
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · show (Fin.snoc (ColKind.liftKinds c κ) ColKind.agg
        : Fin ((c + n) + 1) → ColKind) (winSrc c n (Fin.castAdd (n + 1) jp)) = _
    rw [winSrc, Fin.addCases_left, Fin.snoc_castSucc,
      ColKind.liftKinds_param, ColKind.liftKinds_param]
  · show (Fin.snoc (ColKind.liftKinds c κ) ColKind.agg
        : Fin ((c + n) + 1) → ColKind) (winSrc c n (Fin.natAdd c i)) = _
    rw [winSrc, Fin.addCases_right, ColKind.liftKinds_col]
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.lastCases_last, Fin.snoc_last, Fin.snoc_last]
    · rw [Fin.lastCases_castSucc, Fin.snoc_castSucc,
        ColKind.liftKinds_col, Fin.snoc_castSucc]

/-- **A window partitions by the parameters as well**: each partition
then lies inside one slice, so a frame is a frame of that slice and the
column takes the value it takes there. The frames are asked to contain
their current row, which is what `thm:plainbasis` asks of the windows it
covers. -/
theorem AggQueryIn.hasDecorrelation_win {c n mp p : ℕ} {κ : Fin n → ColKind}
    {P : AggQuery T c (ColKind.allReg c)}
    (hnd : ∀ D : Database T, (P.evaluatePlain D).Nodup)
    (P' : Tuple (Fin n) mp) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) {q : AggQueryIn T c n κ} (hrr : WinReadsReg κ P' O t)
    (dist : Bool) (keep : Option (Selection T n))
    (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P
      (AggQueryIn.Win P' O o w t f q hrr dist keep) := by
  classical
  obtain ⟨q', hu, hd⟩ := h
  set κw : Fin ((c + n) + 1) → ColKind :=
    Fin.snoc (ColKind.liftKinds c κ) ColKind.agg with hκw
  have hsrc : ∀ j, κw (winSrc c n j)
      = ColKind.liftKinds c (Fin.snoc κ ColKind.agg) j :=
    fun j => ColKind.snoc_winSrc κ (κ' := ColKind.liftKinds c κ) rfl j
  refine ⟨(AggQueryIn.Proj (fun j => AggQueryIn.carryCol κw (winSrc c n j))
      (AggQueryIn.Win (winPart c P') (winOrd c O) o w t.lift f q'
        (winReadsReg_lift hrr) dist
        (keep.map (Selection.shift c)))).castKind
      (funext (fun j => (AggQueryIn.carryCol_kind κw _).trans (hsrc j))),
    ?_, fun D => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], by simp [basisOps], hu⟩
  rw [AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u => (fun j =>
      (AggQueryIn.carryCol κw (winSrc c n j)).evalPlain u (fun _ => 0)))
      ((AggQueryIn.Win (winPart c P') (winOrd c O) o w t.lift f q'
        (winReadsReg_lift hrr) dist
        (keep.map (Selection.shift c))).evaluatePlain D) = _
  rw [AggQueryIn.evaluatePlain_Win_eq_opt, hd]
  -- each slice's rows are read as the window reads them there
  refine Eq.trans ?_ (congrArg (Relation.slices (P.evaluatePlain D))
    (funext (fun v => AggQueryIn.evaluatePlain_Win_eq_opt P' O o w t f dist
      keep q hrr D (γ := v)))).symm
  -- what the window reads is the slices of what it read
  rw [show Multiset.map (ColKind.readTuple (ColKind.liftKinds c κ))
        (Relation.slices (P.evaluatePlain D) (fun v => q.evaluatePlain D v))
      = Relation.slices (P.evaluatePlain D)
          (fun v => (q.evaluatePlain D v).map (ColKind.readTuple κ)) from by
    refine Eq.trans (Multiset.map_congr rfl (fun x _ => ?_))
      (Relation.slices_map (P.evaluatePlain D)
        (fun v => q.evaluatePlain D v) (fun _ u => ColKind.readTuple κ u))
    conv_lhs => rw [← Relation.append_paramsOf x]
    rw [ColKind.readTuple_liftKinds]
    rfl]
  rw [Multiset.map_map]
  refine Eq.trans (Multiset.map_congr rfl (fun x hx => ?_))
    (Relation.slices_map (P.evaluatePlain D) (fun v => q.evaluatePlain D v)
      (fun v u => (Fin.snoc u (ValueFrame.windowValueOpt P' O o w t
        (if dist then f.distinct else f) keep
        ((q.evaluatePlain D v).map (ColKind.readTuple κ))
        (ColKind.readTuple κ u) v) : Tuple T (n + 1))))
  obtain ⟨v, hv, u, hu, rfl⟩ := (Relation.mem_slices _ _ x).mp hx
  simp only [Function.comp_apply]
  rw [show (fun j => (Fin.append v u : Tuple T (c + n)) (Fin.castAdd n j))
        = v from funext (fun j => by rw [Fin.append_left]),
    show (fun i => (Fin.append v u : Tuple T (c + n)) (Fin.natAdd c i))
        = u from funext (fun i => by rw [Fin.append_right]),
    ColKind.readTuple_liftKinds,
    ValueFrame.windowValueOpt_slices (P.evaluatePlain D) (hnd D)
      (fun v => (q.evaluatePlain D v).map (ColKind.readTuple κ)) P' O o w t
      (if dist then f.distinct else f) keep hv (ColKind.readTuple κ u)]
  funext j
  rw [AggQueryIn.evalPlain_carryCol]
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · rw [Fin.append_left, winSrc, Fin.addCases_left, Fin.snoc_castSucc,
      Fin.append_left]
  · rw [Fin.append_right, winSrc, Fin.addCases_right]
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.lastCases_last, Fin.snoc_last, Fin.snoc_last]
    · rw [Fin.lastCases_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc,
        Fin.append_right]

/-- **A window over several frames of one partition** decorrelates the
same way: the parameters join the partition, every leaf reads its own
frame of the slice, and the leaves' values are combined as before. Each
frame is asked to contain its current row. -/
theorem AggQueryIn.hasDecorrelation_winExpr {c n mp p na : ℕ}
    {P : AggQuery T c (ColKind.allReg c)}
    (hnd : ∀ D : Database T, (P.evaluatePlain D).Nodup)
    (P' : Tuple (Fin n) mp) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ws : Fin na → ValueFrame T p)
    (ts : Fin na → TermIn T c n) (fs : Fin na → SeqAggFunc T)
    (g : (Fin na → T) → T) {q : AggQueryIn T c n (ColKind.allReg n)}
    (keeps : Fin na → Option (Selection T n))
    (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P
      (AggQueryIn.WinExpr P' O o ws ts fs g q keeps) := by
  classical
  obtain ⟨q', hu, hd⟩ := h
  set κw : Fin ((c + n) + 1) → ColKind :=
    Fin.snoc (ColKind.allReg (c + n)) ColKind.agg with hκw
  refine ⟨(AggQueryIn.Proj (fun j => AggQueryIn.carryCol κw (winSrc c n j))
      (AggQueryIn.WinExpr (winPart c P') (winOrd c O) o ws
        (fun l => (ts l).lift) fs g (q'.castKind (AggQueryIn.append_allReg c n))
        (fun l => (keeps l).map (Selection.shift c)))).castKind
      (funext (fun j => (AggQueryIn.carryCol_kind κw _).trans
        (ColKind.snoc_winSrc (ColKind.allReg n)
          (AggQueryIn.append_allReg c n).symm j))),
    ?_, fun D => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], by simp [basisOps],
      (AggQueryIn.usesOnly_castKind _ _ _).mpr hu⟩
  rw [AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u => (fun j =>
      (AggQueryIn.carryCol κw (winSrc c n j)).evalPlain u (fun _ => 0)))
      ((AggQueryIn.WinExpr (winPart c P') (winOrd c O) o ws
        (fun l => (ts l).lift) fs g (q'.castKind (AggQueryIn.append_allReg c n))
        (fun l => (keeps l).map (Selection.shift c))).evaluatePlain D) = _
  rw [AggQueryIn.evaluatePlain_WinExpr_eq_when,
    AggQueryIn.evaluatePlain_castKind, hd]
  -- each slice's rows are read as the leaves read them there
  refine Eq.trans ?_ (congrArg (Relation.slices (P.evaluatePlain D))
    (funext (fun v => AggQueryIn.evaluatePlain_WinExpr_eq_when P' O o ws ts fs
      g keeps q D (γ := v)))).symm
  rw [Multiset.map_map]
  refine Eq.trans (Multiset.map_congr rfl (fun x hx => ?_))
    (Relation.slices_map (P.evaluatePlain D) (fun v => q.evaluatePlain D v)
      (fun v u => (Fin.snoc u (g (fun l => ValueFrame.windowValueOpt P' O o
        (ws l) (ts l) (fs l) (keeps l) (q.evaluatePlain D v) u v))
        : Tuple T (n + 1))))
  obtain ⟨v, hv, u, hu', rfl⟩ := (Relation.mem_slices _ _ x).mp hx
  simp only [Function.comp_apply]
  rw [show (fun j => (Fin.append v u : Tuple T (c + n)) (Fin.castAdd n j))
        = v from funext (fun j => by rw [Fin.append_left]),
    show (fun i => (Fin.append v u : Tuple T (c + n)) (Fin.natAdd c i))
        = u from funext (fun i => by rw [Fin.append_right]),
    show (fun l => ValueFrame.windowValueOpt (winPart c P') (winOrd c O) o
          (ws l) ((ts l).lift) (fs l) ((keeps l).map (Selection.shift c))
          (Relation.slices (P.evaluatePlain D) (fun v => q.evaluatePlain D v))
          (Fin.append v u) (fun _ => 0))
        = (fun l => ValueFrame.windowValueOpt P' O o (ws l) (ts l) (fs l)
            (keeps l) (q.evaluatePlain D v) u v)
      from funext (fun l => ValueFrame.windowValueOpt_slices
        (P.evaluatePlain D) (hnd D) (fun v => q.evaluatePlain D v) P' O o
        (ws l) (ts l) (fs l) (keeps l) hv u)]
  funext j
  rw [AggQueryIn.evalPlain_carryCol]
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · rw [Fin.append_left, winSrc, Fin.addCases_left, Fin.snoc_castSucc,
      Fin.append_left]
  · rw [Fin.append_right, winSrc, Fin.addCases_right]
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.lastCases_last, Fin.snoc_last, Fin.snoc_last]
    · rw [Fin.lastCases_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc,
        Fin.append_right]

/-! ### Second-level aggregation

A second-level aggregation reads its group as a *bag* – its aggregate is
a function of one – so the decorrelation needs the group itself rather
than the sequence it is read as. -/

/-- **The rows of a decorrelated group**: with the parameters in the key,
the group at `(v, g)` holds the rows of `f v`'s group at `g`, each with
`v` in front. This is `Relation.groupSeq_slices` for the bag. -/
theorem Relation.filter_groupKey_slices {c m n₁ : ℕ}
    (P : Multiset (Tuple T c)) (hP : P.Nodup)
    (f : Tuple T c → Multiset (Tuple T m)) (is : Tuple (Fin m) n₁)
    {v : Tuple T c} (hv : v ∈ P) (g : Tuple T n₁) :
    Multiset.filter (fun u : Tuple T (c + m) =>
        (fun k => u (groupKey c is k) : Tuple T (c + n₁)) = Fin.append v g)
        (Relation.slices P f)
      = (Multiset.filter (fun w : Tuple T m =>
          (fun k => w (is k) : Tuple T n₁) = g) (f v)).map
          (fun w => (Fin.append v w : Tuple T (c + m))) := by
  classical
  -- a row is in the group exactly when it is in that slice and its own
  -- key is `g`
  have hiff : ∀ u : Tuple T (c + m),
      ((fun k => u (groupKey c is k) : Tuple T (c + n₁)) = Fin.append v g)
        ↔ ((fun k => (fun i => u (Fin.natAdd c i)) (is k) : Tuple T n₁) = g
            ∧ Relation.paramsOf u = v) := by
    intro u
    rw [show (fun k => u (groupKey c is k) : Tuple T (c + n₁))
          = Fin.append (Relation.paramsOf u)
              (fun k => (fun i => u (Fin.natAdd c i)) (is k)) from by
      funext k
      refine Fin.addCases (fun jp => ?_) (fun i => ?_) k
      · rw [Fin.append_left, groupKey, Fin.append_left]
        rfl
      · rw [Fin.append_right, groupKey, Fin.append_right]]
    constructor
    · intro h
      obtain ⟨hpar, hkey⟩ := Fin.append_inj h
      exact ⟨hkey, hpar⟩
    · rintro ⟨hkey, hpar⟩
      rw [hpar, hkey]
  rw [Multiset.filter_congr (fun u _ => hiff u),
    show Multiset.filter (fun u : Tuple T (c + m) =>
          (fun k => (fun i => u (Fin.natAdd c i)) (is k) : Tuple T n₁) = g
            ∧ Relation.paramsOf u = v) (Relation.slices P f)
        = Multiset.filter (fun u : Tuple T (c + m) =>
            (fun k => (fun i => u (Fin.natAdd c i)) (is k) : Tuple T n₁) = g)
            (Multiset.filter (fun u => Relation.paramsOf u = v)
              (Relation.slices P f))
      from (Multiset.filter_filter _ _ _).symm,
    Relation.filter_paramsOf_slices P hP f hv, Multiset.filter_map]
  refine congrArg _ (Multiset.filter_congr (fun w _ => ?_))
  simp only [Function.comp_apply]
  rw [show (fun k => (Fin.append v w : Tuple T (c + m)) (Fin.natAdd c (is k))
        : Tuple T n₁) = (fun k => w (is k) : Tuple T n₁)
      from funext (fun k => by rw [Fin.append_right])]

set_option maxHeartbeats 1000000 in
/-- **A second-level aggregation** decorrelates as a grouped one does:
the parameters join the key, and the group at each key is one slice's
group, whose rows the aggregate reads through the lifted column. -/
theorem AggQueryIn.hasDecorrelation_gammaNest {c m n₁ : ℕ}
    {κ : Fin m → ColKind} {P : AggQuery T c (ColKind.allReg c)}
    (hnd : ∀ D : Database T, (P.evaluatePlain D).Nodup)
    (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (pc : ProjColIn T c κ) (f : Multiset T → T)
    {q : AggQueryIn T c m κ} (h : AggQueryIn.HasDecorrelation P q) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.GammaNest is his pc f q) := by
  classical
  obtain ⟨q', hu, hd⟩ := h
  have his' : ∀ k, ColKind.liftKinds c κ (groupKey c is k) ≠ ColKind.agg := by
    intro k
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) k
    · show ColKind.liftKinds c κ (groupKey c is (Fin.castAdd n₁ jp))
        ≠ ColKind.agg
      rw [groupKey, Fin.append_left, ColKind.liftKinds_param]
      exact fun hc => absurd hc (by decide)
    · show ColKind.liftKinds c κ (groupKey c is (Fin.natAdd c i))
        ≠ ColKind.agg
      rw [groupKey, Fin.append_right, ColKind.liftKinds_col]
      exact his i
  set κn : Fin ((c + n₁) + 1) → ColKind :=
    Fin.append (fun k : Fin (c + n₁) => ColKind.liftKinds c κ (groupKey c is k))
      (fun _ : Fin 1 => ColKind.agg) with hκn
  have hsrc : ∀ j, κn (gammaSrc c n₁ 1 j)
      = ColKind.liftKinds c
          (Fin.append (fun k => κ (is k)) (fun _ : Fin 1 => ColKind.agg)) j := by
    intro j
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
    · show κn (gammaSrc c n₁ 1 (Fin.castAdd (n₁ + 1) jp)) = _
      rw [gammaSrc, Fin.addCases_left, hκn, Fin.append_left, groupKey,
        Fin.append_left, ColKind.liftKinds_param, ColKind.liftKinds_param]
    · show κn (gammaSrc c n₁ 1 (Fin.natAdd c i)) = _
      rw [gammaSrc, Fin.addCases_right, ColKind.liftKinds_col]
      refine Fin.addCases (fun i₁ => ?_) (fun z => ?_) i
      · rw [Fin.addCases_left, hκn, Fin.append_left, Fin.append_left, groupKey,
          Fin.append_right, ColKind.liftKinds_col]
      · rw [Fin.addCases_right, hκn, Fin.append_right, Fin.append_right]
  refine ⟨(AggQueryIn.Proj (fun j => AggQueryIn.carryCol κn (gammaSrc c n₁ 1 j))
      (AggQueryIn.GammaNest (groupKey c is) his' pc.lift f q')).castKind
      (funext (fun j => (AggQueryIn.carryCol_kind κn _).trans (hsrc j))),
    ?_, fun D => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], by simp [basisOps], hu⟩
  rw [AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u => (fun j =>
      (AggQueryIn.carryCol κn (gammaSrc c n₁ 1 j)).evalPlain u (fun _ => 0)))
      (Multiset.map (fun g => (Fin.append g (fun _ : Fin 1 => f
          ((Multiset.filter (fun u : Tuple T (c + m) =>
              (fun k => u (groupKey c is k) : Tuple T (c + n₁)) = g)
            (q'.evaluatePlain D)).map
              (fun u => pc.lift.evalPlain u (fun _ => 0))))
          : Tuple T ((c + n₁) + 1)))
        ((Multiset.map (fun u : Tuple T (c + m) =>
            (fun k => u (groupKey c is k) : Tuple T (c + n₁)))
          (q'.evaluatePlain D)).dedup)) = _
  rw [hd]
  -- the keys are the slices of the input's keys
  rw [show Multiset.map (fun u : Tuple T (c + m) =>
          (fun k => u (groupKey c is k) : Tuple T (c + n₁)))
        (Relation.slices (P.evaluatePlain D) (fun v => q.evaluatePlain D v))
      = Relation.slices (P.evaluatePlain D) (fun v =>
          (q.evaluatePlain D v).map
            (fun w => (fun i => w (is i) : Tuple T n₁))) from by
    refine Eq.trans (Multiset.map_congr rfl (fun x _ => funext (fun k => ?_)))
      (Relation.slices_map (P.evaluatePlain D) (fun v => q.evaluatePlain D v)
        (fun _ w => (fun i => w (is i) : Tuple T n₁)))
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) k
    · rw [Fin.append_left, groupKey, Fin.append_left]
    · rw [Fin.append_right, groupKey, Fin.append_right],
    Relation.slices_dedup _ (hnd D), Multiset.map_map]
  -- and the group at each key is that slice's group
  refine Eq.trans (Multiset.map_congr rfl (fun x hx => ?_))
    (Relation.slices_map (P.evaluatePlain D)
      (fun v => ((q.evaluatePlain D v).map
        (fun w => (fun i => w (is i) : Tuple T n₁))).dedup)
      (fun v g => (Fin.append g (fun _ : Fin 1 => f
        ((Multiset.filter (fun w : Tuple T m =>
            (fun k => w (is k) : Tuple T n₁) = g)
          (q.evaluatePlain D v)).map (fun w => pc.evalPlain w v)))
        : Tuple T (n₁ + 1))))
  obtain ⟨v, hv, g, -, rfl⟩ := (Relation.mem_slices _ _ x).mp hx
  simp only [Function.comp_apply]
  rw [show (fun j => (Fin.append v g : Tuple T (c + n₁)) (Fin.castAdd n₁ j))
        = v from funext (fun j => by rw [Fin.append_left]),
    show (fun i => (Fin.append v g : Tuple T (c + n₁)) (Fin.natAdd c i))
        = g from funext (fun i => by rw [Fin.append_right]),
    Relation.filter_groupKey_slices (P.evaluatePlain D) (hnd D)
      (fun v => q.evaluatePlain D v) is hv g, Multiset.map_map]
  rw [show ((fun u => pc.lift.evalPlain u (fun _ => 0))
        ∘ fun w => (Fin.append v w : Tuple T (c + m)))
      = (fun w => pc.evalPlain w v) from funext (fun w =>
    ProjColIn.evalPlain_lift pc v w)]
  funext j
  rw [AggQueryIn.evalPlain_carryCol]
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · rw [Fin.append_left, gammaSrc, Fin.addCases_left, Fin.append_left,
      Fin.append_left]
  · rw [Fin.append_right, gammaSrc, Fin.addCases_right]
    refine Fin.addCases (fun i₁ => ?_) (fun z => ?_) i
    · rw [Fin.addCases_left, Fin.append_left, Fin.append_left, Fin.append_right]
    · rw [Fin.addCases_right, Fin.append_right, Fin.append_right]

/-! ### The apply: the construction's own recursion

An apply reads its right side once per row of its left, with that row's
columns as the context. Decorrelating it is the recursion the whole
construction is for: the left side is decorrelated over `P`, and the
right side over the *distinct rows of that decorrelation*, which are the
pairs its context ranges over. Pairing the two back by those columns
restores the multiplicities duplicate elimination dropped.

An apply's right side reads its left row first and the ambient
parameters after it, where a decorrelation puts the parameters in front:
the two orders are swapped, which is what `Relation.swapBlocks` does. -/

/-- The columns of the swapped block order: the left row, then the
parameters. -/
def swapSrc (c n₁ : ℕ) : Fin (n₁ + c) → Fin (c + n₁) :=
  Fin.addCases (fun i : Fin n₁ => Fin.natAdd c i)
    (fun j : Fin c => Fin.castAdd n₁ j)

/-- **A row with its two blocks swapped**: what an apply's right side
reads as its context, read off a row of the left side's
decorrelation. -/
def Relation.swapBlocks (c n₁ : ℕ) (x : Tuple T (c + n₁)) : Tuple T (n₁ + c) :=
  fun j => x (swapSrc c n₁ j)

omit [ValueType T] in
@[simp] theorem Relation.swapBlocks_append {c n₁ : ℕ} (v : Tuple T c)
    (u : Tuple T n₁) :
    Relation.swapBlocks c n₁ (Fin.append v u : Tuple T (c + n₁))
      = (Fin.append u v : Tuple T (n₁ + c)) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun jp => ?_) j
  · show (Fin.append v u : Tuple T (c + n₁)) (swapSrc c n₁ (Fin.castAdd c i))
      = _
    rw [swapSrc, Fin.addCases_left, Fin.append_right, Fin.append_left]
  · show (Fin.append v u : Tuple T (c + n₁)) (swapSrc c n₁ (Fin.natAdd n₁ jp))
      = _
    rw [swapSrc, Fin.addCases_right, Fin.append_left, Fin.append_right]

omit [ValueType T] in
/-- Swapping the blocks loses nothing: it is a bijection of the
columns. -/
theorem Relation.swapBlocks_injective {c n₁ : ℕ} :
    Function.Injective (Relation.swapBlocks (T := T) c n₁) := by
  intro x y h
  funext k
  refine Fin.addCases (fun j => ?_) (fun i => ?_) k
  · have hj := congrFun h (Fin.natAdd n₁ j)
    show x (Fin.castAdd n₁ j) = y (Fin.castAdd n₁ j)
    rw [show (Fin.castAdd n₁ j : Fin (c + n₁)) = swapSrc c n₁ (Fin.natAdd n₁ j)
      from by rw [swapSrc, Fin.addCases_right]]
    exact hj
  · have hi := congrFun h (Fin.castAdd c i)
    show x (Fin.natAdd c i) = y (Fin.natAdd c i)
    rw [show (Fin.natAdd c i : Fin (c + n₁)) = swapSrc c n₁ (Fin.castAdd c i)
      from by rw [swapSrc, Fin.addCases_left]]
    exact hi

omit [ValueType T] in
/-- **Binding slice by slice**: a choice made of a row's parameters and
its own columns, put back under the same parameters, acts on the slices
as it acts on each slice. -/
theorem Relation.slices_bind {c k k' : ℕ} (P : Multiset (Tuple T c))
    (f : Tuple T c → Multiset (Tuple T k))
    (F : Tuple T c → Tuple T k → Multiset (Tuple T k')) :
    (Relation.slices P f).bind (fun x =>
        (F (Relation.paramsOf x) (fun i => x (Fin.natAdd c i))).map
          (fun w => (Fin.append (Relation.paramsOf x) w : Tuple T (c + k'))))
      = Relation.slices P (fun v => (f v).bind (F v)) := by
  unfold Relation.slices
  rw [Multiset.bind_assoc]
  refine Multiset.bind_congr (fun v _ => ?_)
  rw [Multiset.bind_map, Multiset.map_bind]
  refine Multiset.bind_congr (fun u _ => ?_)
  rw [show Relation.paramsOf (Fin.append v u : Tuple T (c + k)) = v
      from Relation.paramsOf_append v u,
    show (fun i => (Fin.append v u : Tuple T (c + k)) (Fin.natAdd c i)) = u
      from funext (fun i => by rw [Fin.append_right])]

omit [ValueType T] in
/-- The swapped row, read off the blocks. -/
theorem Relation.swapBlocks_eq_append {c n₁ : ℕ} (x : Tuple T (c + n₁)) :
    Relation.swapBlocks c n₁ x
      = (Fin.append (fun i => x (Fin.natAdd c i)) (Relation.paramsOf x)
          : Tuple T (n₁ + c)) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun j => ?_) l
  · show x (swapSrc c n₁ (Fin.castAdd c i)) = _
    rw [swapSrc, Fin.addCases_left, Fin.append_left]
  · show x (swapSrc c n₁ (Fin.natAdd n₁ j)) = _
    rw [swapSrc, Fin.addCases_right, Fin.append_right]
    rfl

/-- The columns of the apply's join: the parameters and the left side's
columns off the left decorrelation, the right side's own off the
right. -/
def applySrc (c n₁ n₂ : ℕ) :
    Fin (c + (n₁ + n₂)) → Fin ((c + n₁) + ((n₁ + c) + n₂)) :=
  Fin.addCases
    (fun j : Fin c => Fin.castAdd ((n₁ + c) + n₂) (Fin.castAdd n₁ j))
    (Fin.addCases
      (fun i : Fin n₁ => Fin.castAdd ((n₁ + c) + n₂) (Fin.natAdd c i))
      (fun w : Fin n₂ => Fin.natAdd (c + n₁) (Fin.natAdd (n₁ + c) w)))

/-- **The apply, at the level of relations.** The left side's
decorrelation holds each pair (parameters, left row) with its
multiplicity; the right side's, over the distinct such pairs swapped
into the order its context expects, holds one row per answer. Joining
them on those columns and keeping the parameters, the left row and the
right row gives the apply, slice by slice: duplicate elimination made
the right side's parameter rows distinct, and the join puts the
multiplicities back. -/
theorem Relation.applyJoin_slices {c n₁ n₂ : ℕ} (P : Multiset (Tuple T c))
    (f : Tuple T c → Multiset (Tuple T n₁))
    (g : Tuple T (n₁ + c) → Multiset (Tuple T n₂)) :
    Multiset.map (fun z : Tuple T ((c + n₁) + ((n₁ + c) + n₂)) =>
        (fun j => z (applySrc c n₁ n₂ j) : Tuple T (c + (n₁ + n₂))))
      (Multiset.filter (fun z : Tuple T ((c + n₁) + ((n₁ + c) + n₂)) =>
          ∀ l : Fin (n₁ + c),
            z (Fin.castAdd ((n₁ + c) + n₂) (swapSrc c n₁ l))
              = z (Fin.natAdd (c + n₁) (Fin.castAdd n₂ l)))
        ((Relation.slices P f).bind (fun x =>
          (Relation.slices
              ((Relation.slices P f).dedup.map (Relation.swapBlocks c n₁))
              g).map (fun y => (Fin.append x y
                : Tuple T ((c + n₁) + ((n₁ + c) + n₂)))))))
      = Relation.slices P (fun v => (f v).bind (fun u =>
          (g (Fin.append u v)).map
            (fun w => (Fin.append u w : Tuple T (n₁ + n₂))))) := by
  classical
  have hnd : ((Relation.slices P f).dedup.map
      (Relation.swapBlocks (T := T) c n₁)).Nodup :=
    (Multiset.nodup_dedup _).map Relation.swapBlocks_injective
  rw [Multiset.filter_bind, Multiset.map_bind]
  refine Eq.trans (Multiset.bind_congr (fun x hx => ?_))
    (Relation.slices_bind P f (fun v u =>
      (g (Fin.append u v)).map
        (fun w => (Fin.append u w : Tuple T (n₁ + n₂)))))
  -- the join keeps the rows of the right side carrying this row's
  -- blocks, swapped
  have hiff : ∀ y : Tuple T ((n₁ + c) + n₂),
      ((fun z : Tuple T ((c + n₁) + ((n₁ + c) + n₂)) =>
          ∀ l : Fin (n₁ + c),
            z (Fin.castAdd ((n₁ + c) + n₂) (swapSrc c n₁ l))
              = z (Fin.natAdd (c + n₁) (Fin.castAdd n₂ l)))
        (Fin.append x y : Tuple T ((c + n₁) + ((n₁ + c) + n₂))))
        ↔ Relation.paramsOf y = Relation.swapBlocks c n₁ x := by
    intro y
    constructor
    · intro h
      funext l
      have hl := h l
      rw [Fin.append_left, Fin.append_right] at hl
      show y (Fin.castAdd n₂ l) = x (swapSrc c n₁ l)
      exact hl.symm
    · intro h l
      rw [Fin.append_left, Fin.append_right]
      have hl : Relation.paramsOf y l = Relation.swapBlocks c n₁ x l :=
        congrFun h l
      show x (swapSrc c n₁ l) = y (Fin.castAdd n₂ l)
      exact hl.symm
  rw [Multiset.filter_map, Multiset.map_map]
  refine Eq.trans (congrArg (Multiset.map _) (Eq.trans
    (Multiset.filter_congr (fun y _ => hiff y))
    (Relation.filter_paramsOf_slices _ hnd g
      (Multiset.mem_map_of_mem _ (Multiset.mem_dedup.mpr hx))))) ?_
  rw [Multiset.map_map, Relation.swapBlocks_eq_append x]
  conv_rhs => rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun w _ => ?_)
  funext j
  simp only [Function.comp_apply]
  refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
  · rw [applySrc, Fin.addCases_left, Fin.append_left, Fin.append_left]
    rfl
  · rw [applySrc, Fin.addCases_right, Fin.append_right]
    refine Fin.addCases (fun i₁ => ?_) (fun w₂ => ?_) i
    · rw [Fin.addCases_left, Fin.append_left, Fin.append_left]
    · rw [Fin.addCases_right, Fin.append_right, Fin.append_right,
        Fin.append_right]

set_option maxHeartbeats 1000000 in
/-- **An apply becomes a product.** The left side is decorrelated over
`P`; the distinct rows of that decorrelation, with their blocks swapped,
are the parameter relation the right side is decorrelated over – the
pairs its context ranges over, each once, which is what makes them a
parameter relation at all. The two are then joined on those columns.

This is the case the construction exists for, and the only one whose
hypothesis is the statement for *another* parameter relation: the
recursion is on the query, over every parameter relation at once. -/
theorem AggQueryIn.hasDecorrelation_apply {c n₁ n₂ : ℕ}
    {κ₂ : Fin n₂ → ColKind} {P : AggQuery T c (ColKind.allReg c)}
    {q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁)}
    {q₂ : AggQueryIn T (n₁ + c) n₂ κ₂}
    (h₁ : AggQueryIn.HasDecorrelation P q₁)
    (h₂ : ∀ P₂ : AggQuery T (n₁ + c) (ColKind.allReg (n₁ + c)),
      P₂.usesOnly basisOps → (∀ D : Database T, (P₂.evaluatePlain D).Nodup) →
      AggQueryIn.HasDecorrelation P₂ q₂) :
    AggQueryIn.HasDecorrelation P (AggQueryIn.Apply q₁ q₂) := by
  classical
  obtain ⟨A, huA, hdA⟩ := h₁
  -- the parameter relation of the right side: the distinct pairs the
  -- left side offers, in the order the right side reads its context
  have hswapKind : ∀ j : Fin (n₁ + c),
      (AggQueryIn.carryCol (T := T) (ColKind.allReg (c + n₁))
        (swapSrc c n₁ j)).kind = ColKind.allReg (n₁ + c) j :=
    fun j => (AggQueryIn.carryCol_kind _ _).trans rfl
  set P₂ : AggQuery T (n₁ + c) (ColKind.allReg (n₁ + c)) :=
    (AggQueryIn.Proj (fun j => AggQueryIn.carryCol (ColKind.allReg (c + n₁))
        (swapSrc c n₁ j))
      (AggQueryIn.Dedup (A.castKind (AggQueryIn.append_allReg c n₁)))).castKind
      (funext hswapKind) with hP₂def
  have hP₂eval : ∀ D : Database T, P₂.evaluatePlain D
      = ((A.evaluatePlain D).dedup).map (Relation.swapBlocks c n₁) := by
    intro D
    rw [hP₂def, AggQueryIn.evaluatePlain_castKind]
    show Multiset.map (fun u => (fun j =>
        (AggQueryIn.carryCol (ColKind.allReg (c + n₁))
          (swapSrc c n₁ j)).evalPlain u (fun _ => 0)))
        ((A.castKind (AggQueryIn.append_allReg c n₁)).evaluatePlain D).dedup = _
    rw [AggQueryIn.evaluatePlain_castKind]
    exact Multiset.map_congr rfl (fun x _ => funext (fun j => by
      rw [AggQueryIn.evalPlain_carryCol]
      rfl))
  have hP₂uses : P₂.usesOnly basisOps := by
    rw [hP₂def, AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], by simp [basisOps],
      (AggQueryIn.usesOnly_castKind _ _ _).mpr huA⟩
  have hP₂nd : ∀ D : Database T, (P₂.evaluatePlain D).Nodup := by
    intro D
    rw [hP₂eval]
    exact (Multiset.nodup_dedup _).map Relation.swapBlocks_injective
  obtain ⟨B, huB, hdB⟩ := h₂ P₂ hP₂uses hP₂nd
  -- the join: the left side's columns against the right side's
  -- parameters
  set κa : Fin ((c + n₁) + ((n₁ + c) + n₂)) → ColKind :=
    Fin.append (ColKind.liftKinds c (ColKind.allReg n₁))
      (ColKind.liftKinds (n₁ + c) κ₂) with hκa
  have hleftReg : ∀ k : Fin (c + n₁),
      ColKind.liftKinds c (ColKind.allReg n₁) k = ColKind.reg :=
    fun k => congrFun (AggQueryIn.append_allReg c n₁) k
  have hposL : ∀ l : Fin (n₁ + c),
      κa (Fin.castAdd ((n₁ + c) + n₂) (swapSrc c n₁ l)) = ColKind.reg := by
    intro l
    rw [hκa, Fin.append_left]
    exact hleftReg _
  have hposR : ∀ l : Fin (n₁ + c),
      κa (Fin.natAdd (c + n₁) (Fin.castAdd n₂ l)) = ColKind.reg := by
    intro l
    rw [hκa, Fin.append_right]
    exact ColKind.liftKinds_param (n₁ + c) κ₂ l
  have hsrc : ∀ j, κa (applySrc c n₁ n₂ j)
      = ColKind.liftKinds c
          (Fin.append (ColKind.allReg n₁) κ₂) j := by
    intro j
    refine Fin.addCases (fun jp => ?_) (fun i => ?_) j
    · show κa (applySrc c n₁ n₂ (Fin.castAdd (n₁ + n₂) jp)) = _
      rw [applySrc, Fin.addCases_left, hκa, Fin.append_left, hleftReg,
        ColKind.liftKinds_param]
    · show κa (applySrc c n₁ n₂ (Fin.natAdd c i)) = _
      rw [applySrc, Fin.addCases_right, ColKind.liftKinds_col]
      refine Fin.addCases (fun i₁ => ?_) (fun w => ?_) i
      · rw [Fin.addCases_left, hκa, Fin.append_left, hleftReg, Fin.append_left]
        rfl
      · rw [Fin.addCases_right, hκa, Fin.append_right,
          ColKind.liftKinds_col, Fin.append_right]
  refine ⟨(AggQueryIn.Proj (fun j => AggQueryIn.carryCol κa (applySrc c n₁ n₂ j))
      (AggQueryIn.Sel
        (keyJoinCond (fun l : Fin (n₁ + c) =>
            Fin.castAdd ((n₁ + c) + n₂) (swapSrc c n₁ l))
          (fun l : Fin (n₁ + c) => Fin.natAdd (c + n₁) (Fin.castAdd n₂ l))
          hposL hposR)
        (AggQueryIn.Prod A B))).castKind
      (funext (fun j => (AggQueryIn.carryCol_kind κa _).trans (hsrc j))),
    ?_, fun D => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], by simp [basisOps],
      ⟨by simp [basisOps], huA, huB⟩⟩
  rw [AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u => (fun j =>
      (AggQueryIn.carryCol κa (applySrc c n₁ n₂ j)).evalPlain u (fun _ => 0)))
      (Multiset.filter (fun u => (keyJoinCond _ _ hposL hposR).holdsPlain u)
        (A.evaluatePlain D * B.evaluatePlain D)) = _
  rw [Relation.hMul_eq_bind, hdB, hP₂eval, hdA]
  refine Eq.trans ?_ (Eq.trans
    (Relation.applyJoin_slices (P.evaluatePlain D)
      (fun v => q₁.evaluatePlain D v) (fun z => q₂.evaluatePlain D z))
    (congrArg (Relation.slices (P.evaluatePlain D)) (funext (fun v => rfl))))
  refine congrArg₂ Multiset.map (funext (fun u => funext (fun j => ?_)))
    (Multiset.filter_congr (fun u _ => ?_))
  · rw [AggQueryIn.evalPlain_carryCol]
  · exact keyJoinCond_holdsPlain _ _ hposL hposR u


/-! ## The construction

Putting the cases together: every query of the plain fragment – the
basis classes and the apply – has a decorrelation using the basis
classes only. The induction is on the query, and its statement
quantifies over the parameter relation, because the apply's right side
is decorrelated over a parameter relation built from its left side.

What the parameter relation is asked is that it use the basis classes
(it ends up inside the decorrelation) and that its rows be pairwise
distinct (`Multiset.Nodup`): a repeated parameter row would pair the
copies of its own slice with each other, which is what
`Relation.filter_paramsOf_slices` rules out. -/

/-- **Every query has an apply-free decorrelation** over every parameter
relation whose rows are distinct. This is `lem:decorrelation`: the
construction is Galindo-Legaria and Joshi's, each operator carrying the
parameters along, and the apply itself recursing with the distinct rows
of its own left side as the new parameter relation. -/
theorem AggQueryIn.hasDecorrelation_of_usesOnly :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly (insert OpKind.apply basisOps) →
      ∀ P : AggQuery T c (ColKind.allReg c), P.usesOnly basisOps →
        (∀ D : Database T, (P.evaluatePlain D).Nodup) →
        AggQueryIn.HasDecorrelation P q := by
  intro c n κ q
  induction q with
  | Rel n s => exact fun _ P hPu _ => AggQueryIn.hasDecorrelation_rel P hPu s
  | Empty => exact fun _ P hPu _ => AggQueryIn.hasDecorrelation_empty P hPu
  | Proj ps q ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_proj ps (ih hq.2 P hPu hnd)
  | Sel φ q ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_sel φ (ih hq.2 P hPu hnd)
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_prod hnd (ih₁ hq.2.1 P hPu hnd)
        (ih₂ hq.2.2 P hPu hnd)
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_apply (ih₁ hq.2.1 P hPu hnd)
        (fun P₂ hP₂u hP₂nd => ih₂ hq.2.2 P₂ hP₂u hP₂nd)
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_sum (ih₁ hq.2.1 P hPu hnd)
        (ih₂ hq.2.2 P hPu hnd)
  | Dedup q ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_dedup hnd (ih hq.2 P hPu hnd)
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_diff (ih₁ hq.2.1 P hPu hnd)
        (ih₂ hq.2.2 P hPu hnd)
  | Alt i hi q ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_alt i hi (ih hq P hPu hnd)
  | Retag hbase q ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_retag hbase (ih hq P hPu hnd)
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | Gamma is ts fs q keep ord ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_gamma hnd is ts fs keep ord
        (ih hq.2 P hPu hnd)
  | GammaScalar ts fs q ord ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_gammaScalar hPu hnd ts fs ord
        (ih hq.2 P hPu hnd)
  | GammaNest is his pc f q ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_gammaNest hnd is his pc f (ih hq.2 P hPu hnd)
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Win P' O o w t f q hrr dist keep ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_win hnd P' O o w t f hrr dist keep
        (ih hq.2 P hPu hnd)
  | WinExpr P' O o ws ts fs g q keeps ih =>
    exact fun hq P hPu hnd =>
      AggQueryIn.hasDecorrelation_winExpr hnd P' O o ws ts fs g keeps
        (ih hq.2 P hPu hnd)

/-- **A closed query's applies are eliminable.** Over the unit – one
empty row, which is the parameter relation a closed query reads – the
decorrelation is the query itself, its parameter block empty, so
projecting that block away gives an apply-free query with the same plain
semantics. This is what `sec:basis` asserts when it leaves the apply out
of the basis classes. -/
theorem AggQueryIn.exists_applyFree_plainEquiv {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQuery T n κ) (hq : q.usesOnly (insert OpKind.apply basisOps)) :
    ∃ q' : AggQuery T n κ, q'.usesOnly basisOps ∧ q.PlainEquiv q' := by
  classical
  set v₀ : Tuple T 0 := fun j => j.elim0 with hv₀
  have hunit : (AggQueryIn.unit : AggQuery T 0 (ColKind.allReg 0)).usesOnly
      basisOps := by
    unfold AggQueryIn.unit
    rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], by simp [AggQueryIn.usesOnly, basisOps]⟩
  have hnd : ∀ D : Database T,
      ((AggQueryIn.unit : AggQuery T 0 (ColKind.allReg 0)).evaluatePlain
        D).Nodup := by
    intro D
    rw [evaluatePlain_unit D (fun _ => 0) v₀]
    exact Multiset.nodup_singleton v₀
  obtain ⟨q'', hu, hd⟩ := AggQueryIn.hasDecorrelation_of_usesOnly q hq
    AggQueryIn.unit hunit hnd
  have hkind : ∀ i : Fin n,
      (AggQueryIn.carryCol (T := T) (ColKind.liftKinds 0 κ)
        (Fin.natAdd 0 i)).kind = κ i :=
    fun i => (AggQueryIn.carryCol_kind _ _).trans (ColKind.liftKinds_col 0 κ i)
  refine ⟨(AggQueryIn.Proj (fun i => AggQueryIn.carryCol
      (ColKind.liftKinds 0 κ) (Fin.natAdd 0 i)) q'').castKind
      (funext hkind), ?_, fun D γ => ?_⟩
  · rw [AggQueryIn.usesOnly_castKind]
    exact ⟨by simp [basisOps], hu⟩
  -- a closed query reads no outer column, so the valuation is the empty one
  rw [show γ = (fun _ => 0 : Fin 0 → T) from funext (fun j => j.elim0),
    AggQueryIn.evaluatePlain_castKind]
  show _ = Multiset.map (fun u => (fun i =>
      (AggQueryIn.carryCol (ColKind.liftKinds 0 κ)
        (Fin.natAdd 0 i)).evalPlain u (fun _ => 0)))
      (q''.evaluatePlain D)
  rw [hd, Relation.slices, evaluatePlain_unit D (fun _ => 0) v₀,
    Multiset.singleton_bind, Multiset.map_map,
    show ((fun u => (fun i =>
            (AggQueryIn.carryCol (ColKind.liftKinds 0 κ)
              (Fin.natAdd 0 i)).evalPlain u (fun _ => 0)))
          ∘ fun w => (Fin.append v₀ w : Tuple T (0 + n)))
        = (fun w : Tuple T n => w)
      from funext (fun w => funext (fun i => by
        rw [Function.comp_apply, AggQueryIn.evalPlain_carryCol,
          Fin.append_right]))]
  refine Eq.trans ?_ (Multiset.map_id' (q.evaluatePlain D v₀)).symm
  exact congrArg (fun γ' : Fin 0 → T => q.evaluatePlain D γ')
    (funext (fun j => Fin.elim0 j))

