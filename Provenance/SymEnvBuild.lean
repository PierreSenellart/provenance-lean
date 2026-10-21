module

public import Provenance.SymOrder
public import Provenance.SymCorrect
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Ring.RingNF

/-!
# The environment of the symbolic evaluation, built from a cut

The symbolic evaluation (`Provenance.SymTab`) reads its descriptors and the
counters of its bounded recursions off an environment (`Sym.SymEnv`). This
file builds both from a query computing the cut, as unary relations over
the ambient context, and proves the environment sound wherever the cut
holds the null (`Sym.envOK_envOf`).

The counters of a recursion of arity `n` are the rows of `E^K`, `E` the
non-null values of the cut with the two constants `0` and
`ValueType.nonzero`, and `K = n (k + 3)`: there are at least as many as
the rounds a restricted bag recursion over good values can run.
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

/-- **On non-null values, the ascending order of one column is the
domain's.** -/
theorem ascLt_one {x y : Tuple T 1} (hx : ValueType.isNull (x 0) = false)
    (hy : ValueType.isNull (y 0) = false) : ascLt 1 x y ↔ x 0 < y 0 := by
  unfold ascLt
  rw [OrderSpec.lt_iff]
  show OrderSpec.leOn (OrderSpec.asc 1) [0] y x = false ↔ _
  simp only [OrderSpec.leOn, OrderSpec.asc, OrderCol.peer, OrderCol.le, OrderCol.ASC, hx, hy]
  by_cases h : x 0 < y 0
  · simp [h, not_le.mpr h]
  · have h' := not_lt.mp h
    simp [h, h']

section Build

variable {c : ℕ}

/-! ## Unary relations of values -/

/-- The non-null rows of a unary relation. -/
def nnQ (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  AggQueryIn.Sel (GenPredIn.cmp CompOp.eq (TermGIn.index 0 rfl) (TermGIn.index 0 rfl)) CQ trivial

/-- The one row holding a constant. -/
def constQ (a : T) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  AggQueryIn.Param (fun _ => _root_.Sum.inl a) (ColKind.allReg 1)

omit [ValueType T] in
theorem noMention_constQ (a : T) (s : String) : (constQ (c := c) a).noMention s := by
  unfold constQ; trivial

theorem holdsPlain_eq_self (x : Tuple T 1) (γ : Fin c → T) :
    (GenPredIn.cmp CompOp.eq (TermGIn.index (κ := ColKind.allReg 1) 0 rfl)
      (TermGIn.index 0 rfl)).holdsPlain x γ ↔ ValueType.isNull (x 0) = false := by
  show CompOp.eq.eval3 (x 0) (x 0) = Kleene.true ↔ _
  unfold CompOp.eval3
  cases h : ValueType.isNull (x 0) <;> simp [CompOp.strict, CompOp.eval, Kleene.ofBool]

theorem mem_nnQ (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T)
    (x : Tuple T 1) : Multiset.Mem ((nnQ CQ).evaluatePlain D γ) x ↔
      Multiset.Mem (CQ.evaluatePlain D γ) x ∧ ValueType.isNull (x 0) = false := by
  show x ∈ Multiset.filter _ _ ↔ _
  rw [Multiset.mem_filter, holdsPlain_eq_self]
  rfl

theorem evaluatePlain_constQ (a : T) (D : Database T) (γ : Fin c → T) :
    @Eq (Multiset (Tuple T 1)) ((constQ a).evaluatePlain D γ) {fun _ => a} := rfl

/-! ## The alphabet of the counters -/

/-- **The values counters are written with**: the non-null values of the
cut, `0` and `ValueType.nonzero`, each once. -/
def alphaQ (f : ℕ → String) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) :
    AggQueryIn T c 1 (ColKind.allReg 1) :=
  AggQueryIn.dedupG (AggQueryIn.sumByMuX (f 0) (f 1) (nnQ CQ)
    (AggQueryIn.sumByMuX (f 2) (f 3) (constQ 0) (constQ ValueType.nonzero)))

/-- The supply names a query does not mention. -/
def FreshFor {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (f : ℕ → String)
    (q : AggQueryIn T c n κ l) : Prop := ∀ i, q.noMention (f i)

theorem mem_alphaQ (f : ℕ → String) (CQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (hf : FreshFor f CQ) (D : Database T) (γ : Fin c → T) (x : Tuple T 1) :
    Multiset.Mem ((alphaQ f CQ).evaluatePlain D γ) x ↔
      (Multiset.Mem (CQ.evaluatePlain D γ) x ∧ ValueType.isNull (x 0) = false)
        ∨ x 0 = 0 ∨ x 0 = ValueType.nonzero := by
  rw [alphaQ, AggQueryIn.evaluatePlain_dedupG]
  show x ∈ Multiset.dedup _ ↔ _
  rw [Multiset.mem_dedup]
  rw [AggQueryIn.evaluatePlain_sumByMuX (f 0) (f 1) (nnQ CQ) _ (hf 0)
    (AggQueryIn.noMention_sumByMuX (f 2) (f 3) (constQ (c := c) 0) (constQ ValueType.nonzero)
      (s := f 1) (noMention_constQ _ _) (noMention_constQ _ _))]
  rw [AggQueryIn.evaluatePlain_sumByMuX (f 2) (f 3) (constQ (c := c) 0) (constQ ValueType.nonzero)
    (noMention_constQ _ _) (noMention_constQ _ _)]
  rw [Multiset.mem_add, Multiset.mem_add]
  erw [evaluatePlain_constQ, evaluatePlain_constQ]
  rw [Multiset.mem_singleton, Multiset.mem_singleton]
  have h1 : ∀ a : T, x = (fun _ => a) ↔ x 0 = a := fun a =>
    ⟨fun h => by rw [h], fun h => funext fun i => by rw [Subsingleton.elim i 0, h]⟩
  rw [h1, h1, ← mem_nnQ CQ D γ x]
  rfl

theorem nodup_alphaQ (f : ℕ → String) (CQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (D : Database T) (γ : Fin c → T) :
    ((alphaQ f CQ).evaluatePlain D γ : Multiset (Tuple T 1)).Nodup := by
  rw [alphaQ, AggQueryIn.evaluatePlain_dedupG]
  exact Multiset.nodup_dedup _

theorem nonNull_alphaQ (f : ℕ → String) (CQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (hf : FreshFor f CQ) (D : Database T) (γ : Fin c → T) :
    NonNullRows (alphaQ f CQ) D γ := fun x hx i => by
  rw [Subsingleton.elim i 0]
  rcases (mem_alphaQ f CQ hf D γ x).mp hx with ⟨-, h⟩ | h | h
  · exact h
  · rw [h]; exact ValueType.isNull_zero
  · rw [h]; exact ValueType.isNull_nonzero

/-! ## Powers of a unary relation -/

/-- **The `K`-th power of a unary relation**, by products. -/
def powU (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) : (K : ℕ) → AggQueryIn T c K (ColKind.allReg K)
  | 0 => AggQueryIn.unitC
  | K + 1 => prodR (powU EQ K) EQ

theorem mem_powU (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T) :
    ∀ (K : ℕ) (x : Tuple T K), Multiset.Mem ((powU EQ K).evaluatePlain D γ) x ↔
      ∀ i, Multiset.Mem (EQ.evaluatePlain D γ) (fun _ => x i)
  | 0, x => by
    rw [powU]
    erw [AggQueryIn.evaluatePlain_unitC D γ x]
    simp only [IsEmpty.forall_iff, iff_true]
    exact Multiset.mem_singleton_self x
  | K + 1, x => by
    rw [powU, mem_prodR]
    constructor
    · rintro ⟨y, hy, e, he, rfl⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have : (fun _ : Fin 1 => (Fin.append y e : Tuple T (K + 1)) (Fin.last K)) = e :=
          funext fun z => by
            rw [Subsingleton.elim z 0]
            exact Fin.append_right y e 0
        rw [this]; exact he
      · have := (mem_powU EQ D γ K y).mp hy j
        have h' : (Fin.append y e : Tuple T (K + 1)) (Fin.castSucc j) = y j := Fin.append_left y e j
        rw [h']; exact this
    · intro h
      refine ⟨fun j => x (Fin.castSucc j), (mem_powU EQ D γ K _).mpr (fun j => h _),
        fun _ => x (Fin.last K), h _, ?_⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact (Fin.append_right (fun j => x (Fin.castSucc j)) (fun _ => x (Fin.last K)) 0).symm
      · exact (Fin.append_left (fun j => x (Fin.castSucc j)) (fun _ => x (Fin.last K)) j).symm

theorem nodup_powU (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T)
    (h : (EQ.evaluatePlain D γ : Multiset (Tuple T 1)).Nodup) :
    ∀ K, ((powU EQ K).evaluatePlain D γ : Multiset (Tuple T K)).Nodup
  | 0 => by
    rw [powU]
    erw [AggQueryIn.evaluatePlain_unitC D γ Fin.elim0]
    exact Multiset.nodup_singleton _
  | K + 1 => by
    rw [powU]
    exact nodup_prodR _ _ D γ (nodup_powU EQ D γ h K) h

theorem card_powU (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T) :
    ∀ K, Multiset.card ((powU EQ K).evaluatePlain D γ : Multiset (Tuple T K))
      = Multiset.card (EQ.evaluatePlain D γ : Multiset (Tuple T 1)) ^ K
  | 0 => by
    rw [powU]
    erw [AggQueryIn.evaluatePlain_unitC D γ Fin.elim0]
    rfl
  | K + 1 => by
    rw [powU, evaluatePlain_prodR, Multiset.card_bind, pow_succ, ← card_powU EQ D γ K]
    simp only [Multiset.card_map, Function.comp_def]
    rw [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]

theorem nonNull_powU (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T)
    (h : NonNullRows EQ D γ) (K : ℕ) : NonNullRows (powU EQ K) D γ := fun x hx i =>
  h _ ((mem_powU EQ D γ K x).mp hx i) 0

/-! ## The counters -/

/-- The width of the counters of a recursion of arity `n`, for `k`
parameter components. -/
def ctrW (k n : ℕ) : ℕ := (k + 3) * n

/-- **The counters**: the rows of `E^K`. -/
def ctrQ (f : ℕ → String) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K : ℕ) :
    AggQueryIn T c K (ColKind.allReg K) :=
  powU (alphaQ f CQ) K

/-- The least counter. -/
def lqQ (f : ℕ → String) (cnt : SeqAggFunc T) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K : ℕ) :
    AggQueryIn T c K (ColKind.allReg K) :=
  leastQ (f 4) (f 5) cnt (ctrQ f CQ K)

/-- The successor relation of the counters. -/
def sqQ (f : ℕ → String) (cnt : SeqAggFunc T) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K : ℕ) :
    AggQueryIn T c (K + K) (ColKind.allReg (K + K)) :=
  succQ (f 6) (f 7) cnt (ctrQ f CQ K)

omit [ValueType T] in
theorem noMention_nnQ (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) {s : String}
    (h : CQ.noMention s) : (nnQ CQ).noMention s := h

theorem noMention_alphaQ (f : ℕ → String) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) {s : String}
    (h : CQ.noMention s) : (alphaQ f CQ).noMention s :=
  AggQueryIn.noMention_dedupG _ _ (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_nnQ CQ h)
    (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_constQ _ _) (noMention_constQ _ _)))

omit [ValueType T] in
theorem noMention_powU (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) {s : String}
    (h : EQ.noMention s) : ∀ K, (powU EQ K).noMention s
  | 0 => by rw [powU]; exact AggQueryIn.noMention_unitC s
  | K + 1 => by rw [powU]; exact (noMention_prodR _ _).mpr ⟨noMention_powU EQ h K, h⟩

theorem noMention_ctrQ (f : ℕ → String) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) {s : String}
    (h : CQ.noMention s) (K : ℕ) : (ctrQ f CQ K).noMention s :=
  noMention_powU _ (noMention_alphaQ f CQ h) K

/-- Arithmetic of the counter width. -/
theorem card_le_ctr {A m k : ℕ} (hA : 2 ≤ A) (hm : m ≤ A + 1) (n : ℕ) :
    (m + k + 1) ^ n ≤ A ^ ctrW k n := by
  unfold ctrW
  rw [pow_mul]
  refine Nat.pow_le_pow_left ?_ n
  have h2 : k + 3 ≤ 2 ^ (k + 2) := by
    have := Nat.lt_two_pow_self (n := k + 2)
    omega
  have hA' : 2 ^ (k + 2) ≤ A ^ (k + 2) := Nat.pow_le_pow_left hA _
  have : A * (k + 3) ≤ A ^ (k + 3) := by
    rw [pow_succ, mul_comm (A ^ (k + 2)) A]
    exact Nat.mul_le_mul_left A (h2.trans hA')
  have h3 : A + (k + 2) * 2 ≤ A * (k + 3) := by
    have : (k + 2) * 2 ≤ (k + 2) * A := Nat.mul_le_mul_left _ hA
    calc A + (k + 2) * 2 ≤ A + (k + 2) * A := by omega
      _ = A * (k + 3) := by ring
  omega

/-- The values of a unary relation, as a finite set. -/
noncomputable def valsU (R : Multiset (Tuple T 1)) : Finset T := (R.map (fun y => y 0)).toFinset

/-- **The counters are as many as the rounds a recursion can run**: a list
of them in increasing order, its least element and its successor
relation, of length at least `(|C| + k + 1)^n`. -/
theorem ctr_ok (f : ℕ → String) {cnt : SeqAggFunc T}
    (hc : SeqAggFunc.Counts cnt) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hfr : FreshFor f CQ)
    (D : Database T) (γ : Fin c → T) (k n : ℕ) :
    ∃ cs : List (Tuple T (ctrW k n)), cs.Nodup ∧ ∃ h : 0 < cs.length,
      LE.le (((valsU (CQ.evaluatePlain D γ)).card + k + 1) ^ n) cs.length
      ∧ (lqQ f cnt CQ (ctrW k n)).evaluatePlain D γ = ({cs[0]'h} : Multiset _)
      ∧ (sqQ f cnt CQ (ctrW k n)).evaluatePlain D γ = (succRel cs : Multiset _) := by
  set K := ctrW k n
  set A := (alphaQ f CQ).evaluatePlain D γ with hAdef
  have hAnd : (A : Multiset (Tuple T 1)).Nodup := nodup_alphaQ f CQ D γ
  have hnn : NonNullRows (ctrQ f CQ K) D γ :=
    nonNull_powU _ D γ (nonNull_alphaQ f CQ hfr D γ) K
  have hnd : ((ctrQ f CQ K).evaluatePlain D γ : Multiset (Tuple T K)).Nodup :=
    nodup_powU _ D γ hAnd K
  set cs := sortedRows ((ctrQ f CQ K).evaluatePlain D γ : Multiset (Tuple T K)) with hcs
  have hlen : cs.length = Multiset.card (A : Multiset (Tuple T 1)) ^ K := by
    rw [hcs, length_sortedRows, Multiset.toFinset_card_of_nodup hnd]
    exact card_powU _ D γ K
  -- the alphabet holds two values
  have hmem0 : Multiset.Mem (A : Multiset (Tuple T 1)) (fun _ => 0) :=
    (mem_alphaQ f CQ hfr D γ _).mpr (Or.inr (Or.inl rfl))
  have hmem1 : Multiset.Mem (A : Multiset (Tuple T 1)) (fun _ => ValueType.nonzero) :=
    (mem_alphaQ f CQ hfr D γ _).mpr (Or.inr (Or.inr rfl))
  have hA2 : 2 ≤ Multiset.card (A : Multiset (Tuple T 1)) := by
    have hle : ({fun _ => 0, fun _ => ValueType.nonzero} : Multiset (Tuple T 1)) ≤ A := by
      refine (Multiset.le_iff_subset (Multiset.nodup_cons.mpr ⟨?_, Multiset.nodup_singleton
          _⟩)).mpr ?_
      · intro h
        exact ValueType.nonzero_ne_zero (congrFun (Multiset.mem_singleton.mp h) 0).symm
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact hmem0
        · rw [Multiset.mem_singleton.mp hx]; exact hmem1
    exact (Multiset.card_le_card hle).trans' (by simp)
  -- the cut's values are the alphabet's and perhaps the null
  have hC : (valsU (CQ.evaluatePlain D γ)).card ≤ Multiset.card (A : Multiset (Tuple T 1)) + 1 := by
    have hsub : valsU (CQ.evaluatePlain D γ)
        ⊆ insert (Option.getD ValueType.nullVal 0) (valsU A) := by
      intro a ha
      rw [valsU, Multiset.mem_toFinset, Multiset.mem_map] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      cases hn : ValueType.isNull (y 0)
      · refine Finset.mem_insert_of_mem ?_
        rw [valsU, Multiset.mem_toFinset, Multiset.mem_map]
        exact ⟨y, (mem_alphaQ f CQ hfr D γ y).mpr (Or.inl ⟨hy, hn⟩), rfl⟩
      · rw [(ValueType.isNull_iff_nullVal _).mp hn]
        exact Finset.mem_insert_self _ _
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.add_le_add_right ?_ 1
    rw [valsU]
    exact (Multiset.toFinset_card_le _).trans (by rw [Multiset.card_map])
  have hpos : 0 < cs.length := by
    rw [hlen]; exact Nat.pow_pos (by omega)
  refine ⟨cs, nodup_sortedRows _, hpos, ?_, ?_, ?_⟩
  · rw [hlen]; exact card_le_ctr hA2 hC n
  · exact evaluatePlain_leastQ (f 4) (f 5) hc (noMention_ctrQ f CQ (hfr 4) K)
      (noMention_ctrQ f CQ (hfr 5) K) hnn hnd hpos
  · exact evaluatePlain_succQ (f 6) (f 7) hc (noMention_ctrQ f CQ (hfr 6) K)
      (noMention_ctrQ f CQ (hfr 7) K) hnn hnd

/-! ## The bound above a gap -/

variable (C : Finset T)

theorem upOf_eq_coe_iff (l : WithBot T) (b : T) :
    upOf C l = (b : WithTop T) ↔ (b ∈ C ∧ ValueType.isNull b = false ∧ LT.lt l (b : WithBot T))
      ∧ ∀ t ∈ C, ValueType.isNull t = false → LT.lt l (t : WithBot T) → b ≤ t := by
  unfold upOf
  constructor
  · intro h
    have hm := Finset.mem_of_min h
    obtain ⟨hb, hbn, hlt⟩ := Finset.mem_filter.mp hm
    refine ⟨⟨hb, hbn, hlt⟩, fun t ht htn hlt' => ?_⟩
    have := Finset.min_le (s := C.filter (fun t : T => ValueType.isNull t = false
      ∧ LT.lt l (t : WithBot T))) (Finset.mem_filter.mpr ⟨ht, htn, hlt'⟩)
    rw [h] at this
    exact WithTop.coe_le_coe.mp this
  · rintro ⟨⟨hb, hbn, hlt⟩, hmin⟩
    refine le_antisymm (Finset.min_le (Finset.mem_filter.mpr ⟨hb, hbn, hlt⟩)) ?_
    refine Finset.le_min fun t ht => ?_
    obtain ⟨ht, htn, hlt'⟩ := Finset.mem_filter.mp ht
    exact WithTop.coe_le_coe.mpr (hmin t ht htn hlt')

theorem upOf_eq_top_iff (l : WithBot T) :
    upOf C l = ⊤ ↔ ∀ t ∈ C, ValueType.isNull t = false → ¬ LT.lt l (t : WithBot T) := by
  unfold upOf
  rw [Finset.min_eq_top, Finset.filter_eq_empty_iff]
  constructor
  · intro h t ht htn hlt
    exact h ht ⟨htn, hlt⟩
  · intro h t ht hp
    exact h t ht hp.1 hp.2

variable {C}

/-! ## The cells of the descriptors -/

omit [ValueType T] in
/-- **A cell's columns as arguments**: seven columns and the rank's. -/
def cellSA {N k : ℕ} (v : Fin 7 → SA T c N) (th : Fin k → SA T c N) : Fin (7 + k) → SA T c N :=
  Fin.addCases (motive := fun _ => SA T c N) v th

omit [ValueType T] in
theorem eval_cellSA {N k : ℕ} (v : Fin 7 → SA T c N) (th : Fin k → SA T c N) (x : Tuple T N)
    (γ : Fin c → T) :
    (fun j => (cellSA v th j).eval x γ)
      = Fin.append (fun j => (v j).eval x γ) (fun j => (th j).eval x γ) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [cellSA, Fin.addCases_left, Fin.append_left]
  · simp only [cellSA, Fin.addCases_right, Fin.append_right]

omit [ValueType T] in
/-- Seven arguments read on a row. -/
theorem eval_vec7 {N : ℕ} (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : SA T c N) (x : Tuple T N) (γ : Fin c → T) :
    (fun j => (![a₀, a₁, a₂, a₃, a₄, a₅, a₆] j).eval x γ)
      = ![a₀.eval x γ, a₁.eval x γ, a₂.eval x γ, a₃.eval x γ, a₄.eval x γ, a₅.eval x γ,
          a₆.eval x γ] := by
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl

/-- The row of a constant thermometer. -/
def thRowQ (k r : ℕ) : AggQueryIn T c k (ColKind.allReg k) :=
  AggQueryIn.Param (fun j => _root_.Sum.inl (therm k r j)) (ColKind.allReg k)

/-- **The ranks from `0` to `r` in unary.** -/
def thQ (f : ℕ → String) (k : ℕ) : ℕ → AggQueryIn T c k (ColKind.allReg k)
  | 0 => thRowQ k 0
  | r + 1 => AggQueryIn.sumByMuX (f (2 * r)) (f (2 * r + 1)) (thQ f k r) (thRowQ k (r + 1))

theorem noMention_thRowQ (k r : ℕ) (s : String) : (thRowQ (T := T) (c := c) k r).noMention s := by
  unfold thRowQ; trivial

theorem noMention_thQ (f : ℕ → String) (k : ℕ) (s : String) :
    ∀ r, (thQ (T := T) (c := c) f k r).noMention s
  | 0 => noMention_thRowQ k 0 s
  | r + 1 => AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_thQ f k s r) (noMention_thRowQ _ _ s)

theorem mem_thQ (f : ℕ → String) (k : ℕ) (D : Database T) (γ : Fin c → T) :
    ∀ (r : ℕ) (x : Tuple T k), Multiset.Mem ((thQ f k r).evaluatePlain D γ) x ↔
      ∃ r' ≤ r, x = therm k r'
  | 0, x => by
    show x ∈ ({fun j => therm k 0 j} : Multiset _) ↔ _
    rw [Multiset.mem_singleton]
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨r', hr', h⟩ => by
      rw [Nat.le_zero.mp hr'] at h; exact h⟩
  | r + 1, x => by
    rw [thQ, AggQueryIn.evaluatePlain_sumByMuX _ _ _ _ (noMention_thQ f k _ r)
      (noMention_thRowQ _ _ _)]
    show x ∈ (_ + _ : Multiset _) ↔ _
    rw [Multiset.mem_add]
    have h1 : Multiset.Mem ((thQ f k r).evaluatePlain D γ) x ↔ ∃ r' ≤ r, x = therm k r' :=
      mem_thQ f k D γ r x
    refine Iff.trans (or_congr h1 (Multiset.mem_singleton (b := x) (a := fun j => therm k (r + 1)
        j)))
      ?_
    constructor
    · rintro (⟨r', hr', h⟩ | h)
      · exact ⟨r', by omega, h⟩
      · exact ⟨r + 1, le_rfl, h⟩
    · rintro ⟨r', hr', h⟩
      rcases Nat.lt_or_ge r' (r + 1) with hlt | hge
      · exact Or.inl ⟨r', by omega, h⟩
      · exact Or.inr (by rw [h, show r' = r + 1 by omega])

/-! ## The five kinds of cells -/

/-- The value of a unary row. -/
theorem mem_valsU {R : Multiset (Tuple T 1)} {a : T} :
    a ∈ valsU R ↔ ∃ y ∈ R, y 0 = a := by
  rw [valsU, Multiset.mem_toFinset, Multiset.mem_map]

omit [ValueType T] in
theorem unary_eq (y : Tuple T 1) : y = fun _ => y 0 :=
  funext fun i => by rw [Subsingleton.elim i 0]

/-- **A concrete cell for each value of the cut.** -/
def concP (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) : AggQueryIn T c (7 + k)
    (ColKind.allReg _) :=
  projQ (cellSA ![.const 0, .col 0, .const 0, .const 0, .const 0, .const sLo, .const sHi]
    (fun _ => .const 0)) CQ

theorem mem_concP (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T)
    (γ : Fin c → T) (x : Tuple T (7 + k)) :
    Multiset.Mem ((concP k CQ).evaluatePlain D γ) x ↔
      ∃ a ∈ valsU (CQ.evaluatePlain D γ), x = enc (valsU (CQ.evaluatePlain D γ)) k (.conc a) := by
  rw [concP, evaluatePlain_projQ]
  show x ∈ Multiset.map _ _ ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y 0, mem_valsU.mpr ⟨y, hy, rfl⟩, ?_⟩
    rw [eval_cellSA, eval_vec7]
    rfl
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨y, hy, rfl⟩ := mem_valsU.mp ha
    refine ⟨y, hy, ?_⟩
    rw [eval_cellSA, eval_vec7]
    rfl

theorem mem_nnQ_iff (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T)
    (y : Tuple T 1) : Multiset.Mem ((nnQ CQ).evaluatePlain D γ) y ↔
      y 0 ∈ valsU (CQ.evaluatePlain D γ) ∧ ValueType.isNull (y 0) = false := by
  rw [mem_nnQ]
  constructor
  · rintro ⟨hy, hn⟩
    exact ⟨mem_valsU.mpr ⟨y, hy, rfl⟩, hn⟩
  · rintro ⟨hy, hn⟩
    obtain ⟨y', hy', he⟩ := mem_valsU.mp hy
    refine ⟨?_, hn⟩
    rw [unary_eq y, ← he, ← unary_eq y']
    exact hy'

theorem nonNull_nnQ (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T) :
    NonNullRows (nnQ CQ) D γ := fun y hy i => by
  rw [Subsingleton.elim i 0]; exact ((mem_nnQ CQ D γ y).mp hy).2

/-- The unary ranks. -/
def thP (f : ℕ → String) (k : ℕ) : AggQueryIn T c k (ColKind.allReg k) :=
  thQ (fun i => f (i + 16)) k k

theorem mem_thP (f : ℕ → String) (k : ℕ) (D : Database T) (γ : Fin c → T) (x : Tuple T k) :
    Multiset.Mem ((thP f k).evaluatePlain (c := c) D γ) x ↔ ∃ r ≤ k, x = therm k r :=
  mem_thQ _ k D γ k x

/-- **A cell for each gap above a non-null value of the cut with a value
above it.** -/
def succP (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) :
    AggQueryIn T c (7 + k) (ColKind.allReg _) :=
  projQ (cellSA ![.const ValueType.nonzero, .col (Fin.castAdd k (Fin.castAdd 1 0)), .const 0,
      .col (Fin.castAdd k (Fin.natAdd 1 0)), .const 0, .const sHi, .const sLo]
      (fun r => .col (Fin.natAdd (1 + 1) r)))
    (prodR (succQ (f 8) (f 9) cnt (nnQ CQ)) (thP f k))

theorem mem_succP (f : ℕ → String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hfr : FreshFor f CQ) (D : Database T)
    (γ : Fin c → T) (x : Tuple T (7 + k)) :
    Multiset.Mem ((succP f cnt k CQ).evaluatePlain D γ) x ↔
      ∃ t ∈ valsU (CQ.evaluatePlain D γ), ValueType.isNull t = false
        ∧ upOf (valsU (CQ.evaluatePlain D γ)) (t : WithBot T) ≠ ⊤
        ∧ ∃ r ≤ k, x = enc (valsU (CQ.evaluatePlain D γ)) k (.fresh (t : WithBot T) r) := by
  set C := valsU (CQ.evaluatePlain D γ) with hC
  have hnn := nonNull_nnQ CQ D γ
  rw [succP, evaluatePlain_projQ]
  show x ∈ Multiset.map _ _ ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨ab, hab, th, hth, rfl⟩ := (mem_prodR _ _ D γ w).mp hw
    obtain ⟨a, ha, b, hb, rfl, hlt, hn⟩ := (mem_succQ (f 8) (f 9) hc (noMention_nnQ CQ (hfr 8))
        (noMention_nnQ CQ (hfr 9)) hnn ab).mp hab
    obtain ⟨r, hr, rfl⟩ := (mem_thP f k D γ th).mp hth
    obtain ⟨haC, han⟩ := (mem_nnQ_iff CQ D γ a).mp ha
    obtain ⟨hbC, hbn⟩ := (mem_nnQ_iff CQ D γ b).mp hb
    have hlt' : a 0 < b 0 := (ascLt_one han hbn).mp hlt
    have hup : upOf C (a 0 : WithBot T) = (b 0 : WithTop T) := by
      refine (upOf_eq_coe_iff C _ _).mpr ⟨⟨hbC, hbn, WithBot.coe_lt_coe.mpr hlt'⟩,
        fun u hu hun hau => ?_⟩
      by_contra hcon
      refine hn (fun _ => u) ((mem_nnQ_iff CQ D γ _).mpr ⟨hu, hun⟩) ⟨?_, ?_⟩
      · exact (ascLt_one han hun).mpr (WithBot.coe_lt_coe.mp hau)
      · exact (ascLt_one hun hbn).mpr (not_le.mp hcon)
    refine ⟨a 0, haC, han, by rw [hup]; exact WithTop.coe_ne_top, r, hr, ?_⟩
    rw [eval_cellSA, eval_vec7]
    simp only [SA.eval, Fin.append_left, Fin.append_right]
    show _ = Fin.append ![ValueType.nonzero, a 0, 0, wtVal (upOf C (a 0 : WithBot T)),
      wtFlag (upOf C (a 0 : WithBot T)), sHi, sLo] (therm k r)
    rw [hup]
    rfl
  · rintro ⟨t, htC, htn, htop, r, hr, rfl⟩
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨⟨hbC, hbn, hlt⟩, hmin⟩ := (upOf_eq_coe_iff C _ _).mp hb.symm
    have ha : Multiset.Mem ((nnQ CQ).evaluatePlain D γ) (fun _ => t) :=
      (mem_nnQ_iff CQ D γ _).mpr ⟨htC, htn⟩
    have hb' : Multiset.Mem ((nnQ CQ).evaluatePlain D γ) (fun _ => b) :=
      (mem_nnQ_iff CQ D γ _).mpr ⟨hbC, hbn⟩
    refine ⟨Fin.append (Fin.append (fun _ : Fin 1 => t) (fun _ : Fin 1 => b)) (therm k r),
      (mem_prodR _ _ D γ _).mpr ⟨_, (mem_succQ (f 8) (f 9) hc (noMention_nnQ CQ (hfr 8))
        (noMention_nnQ CQ (hfr 9)) hnn _).mpr
        ⟨_, ha, _, hb', rfl, (ascLt_one htn hbn).mpr (WithBot.coe_lt_coe.mp hlt),
          fun e he ⟨h₁, h₂⟩ => ?_⟩, _, (mem_thP f k D γ _).mpr ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
    · obtain ⟨heC, hen⟩ := (mem_nnQ_iff CQ D γ e).mp he
      have h₁' := (ascLt_one htn hen).mp h₁
      have h₂' := (ascLt_one hen hbn).mp h₂
      exact absurd (hmin _ heC hen (WithBot.coe_lt_coe.mpr h₁')) (not_le.mpr h₂')
    · rw [eval_cellSA, eval_vec7]
      simp only [SA.eval, Fin.append_left, Fin.append_right]
      show Fin.append ![ValueType.nonzero, t, 0, b, 0, sHi, sLo] (therm k r) = Fin.append
        ![ValueType.nonzero, t, 0, wtVal (upOf C (t : WithBot T)), wtFlag (upOf C (t : WithBot T)),
          sHi, sLo] (therm k r)
      rw [← hb]
      rfl

/-- **A cell for each gap above the greatest non-null value of the cut.** -/
def topP (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) :
    AggQueryIn T c (7 + k) (ColKind.allReg _) :=
  projQ (cellSA ![.const ValueType.nonzero, .col (Fin.castAdd k 0), .const 0, .const 0,
      .const ValueType.nonzero, .const sHi, .const sLo] (fun r => .col (Fin.natAdd 1 r)))
    (prodR (greatestQ (f 10) (f 11) cnt (nnQ CQ)) (thP f k))

theorem mem_topP (f : ℕ → String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hfr : FreshFor f CQ) (D : Database T)
    (γ : Fin c → T) (x : Tuple T (7 + k)) :
    Multiset.Mem ((topP f cnt k CQ).evaluatePlain D γ) x ↔
      ∃ t ∈ valsU (CQ.evaluatePlain D γ), ValueType.isNull t = false
        ∧ upOf (valsU (CQ.evaluatePlain D γ)) (t : WithBot T) = ⊤
        ∧ ∃ r ≤ k, x = enc (valsU (CQ.evaluatePlain D γ)) k (.fresh (t : WithBot T) r) := by
  set C := valsU (CQ.evaluatePlain D γ) with hC
  have hnn := nonNull_nnQ CQ D γ
  have hg := mem_greatestQ (f 10) (f 11) hc (noMention_nnQ CQ (hfr 10)) (noMention_nnQ CQ (hfr 11))
    hnn
  rw [topP, evaluatePlain_projQ]
  show x ∈ Multiset.map _ _ ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, ha, th, hth, rfl⟩ := (mem_prodR _ _ D γ w).mp hw
    obtain ⟨ha, hn⟩ := (hg a).mp ha
    obtain ⟨r, hr, rfl⟩ := (mem_thP f k D γ th).mp hth
    obtain ⟨haC, han⟩ := (mem_nnQ_iff CQ D γ a).mp ha
    have hup : upOf C (a 0 : WithBot T) = ⊤ := by
      refine (upOf_eq_top_iff C _).mpr fun u hu hun hau => ?_
      exact hn (fun _ => u) ((mem_nnQ_iff CQ D γ _).mpr ⟨hu, hun⟩)
        ((ascLt_one han hun).mpr (WithBot.coe_lt_coe.mp hau))
    refine ⟨a 0, haC, han, hup, r, hr, ?_⟩
    rw [eval_cellSA, eval_vec7]
    simp only [SA.eval, Fin.append_left, Fin.append_right]
    show _ = Fin.append ![ValueType.nonzero, a 0, 0, wtVal (upOf C (a 0 : WithBot T)),
      wtFlag (upOf C (a 0 : WithBot T)), sHi, sLo] (therm k r)
    rw [hup]
    rfl
  · rintro ⟨t, htC, htn, htop, r, hr, rfl⟩
    have ha : Multiset.Mem ((nnQ CQ).evaluatePlain D γ) (fun _ => t) :=
      (mem_nnQ_iff CQ D γ _).mpr ⟨htC, htn⟩
    refine ⟨Fin.append (fun _ : Fin 1 => t) (therm k r),
      (mem_prodR _ _ D γ _).mpr ⟨_, (hg _).mpr ⟨ha, fun b hb hlt => ?_⟩, _,
        (mem_thP f k D γ _).mpr ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
    · obtain ⟨hbC, hbn⟩ := (mem_nnQ_iff CQ D γ b).mp hb
      exact (upOf_eq_top_iff C _).mp htop _ hbC hbn
        (WithBot.coe_lt_coe.mpr ((ascLt_one htn hbn).mp hlt))
    · rw [eval_cellSA, eval_vec7]
      simp only [SA.eval, Fin.append_left, Fin.append_right]
      show Fin.append ![ValueType.nonzero, t, 0, 0, ValueType.nonzero, sHi, sLo] (therm k r)
        = Fin.append ![ValueType.nonzero, t, 0, wtVal (upOf C (t : WithBot T)),
          wtFlag (upOf C (t : WithBot T)), sHi, sLo] (therm k r)
      rw [htop]
      rfl

/-- **The cells of the gap below the least non-null value of the cut.** -/
def botP (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) :
    AggQueryIn T c (7 + k) (ColKind.allReg _) :=
  projQ (cellSA ![.const ValueType.nonzero, .col (Fin.castAdd k 0), .const ValueType.nonzero,
      .col (Fin.castAdd k 0), .const 0, .const sLo, .const sLo] (fun r => .col (Fin.natAdd 1 r)))
    (prodR (leastQ (f 12) (f 13) cnt (nnQ CQ)) (thP f k))

theorem mem_botP (f : ℕ → String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hfr : FreshFor f CQ) (D : Database T)
    (γ : Fin c → T) (x : Tuple T (7 + k)) :
    Multiset.Mem ((botP f cnt k CQ).evaluatePlain D γ) x ↔
      (∃ t ∈ valsU (CQ.evaluatePlain D γ), ValueType.isNull t = false)
        ∧ ∃ r ≤ k, x = enc (valsU (CQ.evaluatePlain D γ)) k (.fresh ⊥ r) := by
  set C := valsU (CQ.evaluatePlain D γ) with hC
  have hnn := nonNull_nnQ CQ D γ
  have hl := mem_leastQ (f 12) (f 13) hc (noMention_nnQ CQ (hfr 12)) (noMention_nnQ CQ (hfr 13)) hnn
  -- the bound above the gap is the least value
  have hup : ∀ m, Multiset.Mem ((leastQ (f 12) (f 13) cnt (nnQ CQ)).evaluatePlain D γ) m →
      upOf C ⊥ = (m 0 : WithTop T) := by
    intro m hm
    obtain ⟨hm, hn⟩ := (hl m).mp hm
    obtain ⟨hmC, hmn⟩ := (mem_nnQ_iff CQ D γ m).mp hm
    refine (upOf_eq_coe_iff C _ _).mpr ⟨⟨hmC, hmn, WithBot.bot_lt_coe _⟩, fun u hu hun _ => ?_⟩
    by_contra hcon
    exact hn (fun _ => u) ((mem_nnQ_iff CQ D γ _).mpr ⟨hu, hun⟩)
      ((ascLt_one hun hmn).mpr (not_le.mp hcon))
  rw [botP, evaluatePlain_projQ]
  show x ∈ Multiset.map _ _ ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨m, hm, th, hth, rfl⟩ := (mem_prodR _ _ D γ w).mp hw
    obtain ⟨r, hr, rfl⟩ := (mem_thP f k D γ th).mp hth
    obtain ⟨hmC, hmn⟩ := (mem_nnQ_iff CQ D γ m).mp ((hl m).mp hm).1
    refine ⟨⟨m 0, hmC, hmn⟩, r, hr, ?_⟩
    rw [eval_cellSA, eval_vec7]
    simp only [SA.eval, Fin.append_left, Fin.append_right]
    show _ = Fin.append ![ValueType.nonzero, wtVal (upOf C ⊥), ValueType.nonzero, wtVal (upOf C ⊥),
      wtFlag (upOf C ⊥), sLo, sLo] (therm k r)
    rw [hup m hm]
    rfl
  · rintro ⟨⟨t, htC, htn⟩, r, hr, rfl⟩
    -- the least value exists
    have hne : upOf C ⊥ ≠ ⊤ := fun h =>
      (upOf_eq_top_iff C _).mp h t htC htn (WithBot.bot_lt_coe _)
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hne
    obtain ⟨⟨hbC, hbn, -⟩, hmin⟩ := (upOf_eq_coe_iff C _ _).mp hb.symm
    have hm : Multiset.Mem ((leastQ (f 12) (f 13) cnt (nnQ CQ)).evaluatePlain D γ) (fun _ => b) :=
      (hl _).mpr ⟨(mem_nnQ_iff CQ D γ _).mpr ⟨hbC, hbn⟩, fun a ha hlt => by
        obtain ⟨haC, han⟩ := (mem_nnQ_iff CQ D γ a).mp ha
        exact absurd (hmin _ haC han (WithBot.bot_lt_coe _))
          (not_le.mpr ((ascLt_one han hbn).mp hlt))⟩
    refine ⟨Fin.append (fun _ : Fin 1 => b) (therm k r),
      (mem_prodR _ _ D γ _).mpr ⟨_, hm, _, (mem_thP f k D γ _).mpr ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
    rw [eval_cellSA, eval_vec7]
    simp only [SA.eval, Fin.append_left, Fin.append_right]
    show Fin.append ![ValueType.nonzero, b, ValueType.nonzero, b, 0, sLo, sLo] (therm k r)
      = Fin.append ![ValueType.nonzero, wtVal (upOf C ⊥), ValueType.nonzero, wtVal (upOf C ⊥),
        wtFlag (upOf C ⊥), sLo, sLo] (therm k r)
    rw [← hb]
    rfl

/-- **The empty row where the cut holds no non-null value**, nothing
elsewhere. -/
def emptyQ (s₁ s₂ : String) (cnt : SeqAggFunc T) (R : AggQueryIn T c 1 (ColKind.allReg 1)) :
    AggQueryIn T c 0 (ColKind.allReg 0) :=
  AggQueryIn.notInDiffX s₁ s₂ cnt AggQueryIn.unitC (projQ (fun j : Fin 0 => j.elim0) R)

theorem mem_emptyQ (s₁ s₂ : String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (R : AggQueryIn T c 1 (ColKind.allReg 1)) (h₂ : R.noMention s₂) (D : Database T)
    (γ : Fin c → T) (z : Tuple T 0) :
    Multiset.Mem ((emptyQ s₁ s₂ cnt R).evaluatePlain D γ) z ↔
      ∀ y, ¬ Multiset.Mem (R.evaluatePlain D γ) y := by
  rw [emptyQ, AggQueryIn.evaluatePlain_notInDiffX s₁ s₂ cnt hc _ _ (AggQueryIn.noMention_unitC _)
    (by rw [projQ, AggQueryIn.noMention_castKind]; exact h₂) D γ]
  show z ∈ Multiset.filter _ _ ↔ _
  rw [Multiset.mem_filter]
  erw [AggQueryIn.evaluatePlain_unitC D γ z]
  rw [evaluatePlain_projQ]
  constructor
  · rintro ⟨-, hn⟩ y hy
    refine hn (Multiset.mem_map.mpr ⟨y, hy, funext fun j => j.elim0⟩)
  · intro h
    refine ⟨Multiset.mem_singleton_self z, fun hm => ?_⟩
    obtain ⟨y, hy, -⟩ := Multiset.mem_map.mp hm
    exact h y hy

/-- **The cells of the one gap of a cut with no non-null value.** -/
def botEP (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) :
    AggQueryIn T c (7 + k) (ColKind.allReg _) :=
  projQ (cellSA ![.const ValueType.nonzero, .const 0, .const ValueType.nonzero, .const 0,
      .const ValueType.nonzero, .const sLo, .const sLo] (fun r => .col (Fin.natAdd 0 r)))
    (prodR (emptyQ (f 14) (f 15) cnt (nnQ CQ)) (thP f k))

theorem mem_botEP (f : ℕ → String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hfr : FreshFor f CQ) (D : Database T)
    (γ : Fin c → T) (x : Tuple T (7 + k)) :
    Multiset.Mem ((botEP f cnt k CQ).evaluatePlain D γ) x ↔
      (∀ t ∈ valsU (CQ.evaluatePlain D γ), ValueType.isNull t = true)
        ∧ ∃ r ≤ k, x = enc (valsU (CQ.evaluatePlain D γ)) k (.fresh ⊥ r) := by
  set C := valsU (CQ.evaluatePlain D γ) with hC
  have he := mem_emptyQ (f 14) (f 15) hc (nnQ CQ) (noMention_nnQ CQ (hfr 15)) D γ
  have hiff : (∀ y, ¬ Multiset.Mem ((nnQ CQ).evaluatePlain D γ) y)
      ↔ ∀ t ∈ C, ValueType.isNull t = true := by
    constructor
    · intro h t ht
      by_contra hn
      exact h (fun _ => t) ((mem_nnQ_iff CQ D γ _).mpr ⟨ht, by simpa using hn⟩)
    · intro h y hy
      obtain ⟨hyC, hyn⟩ := (mem_nnQ_iff CQ D γ y).mp hy
      rw [h _ hyC] at hyn
      exact absurd hyn (by decide)
  have htop : (∀ t ∈ C, ValueType.isNull t = true) → upOf C ⊥ = ⊤ := fun h =>
    (upOf_eq_top_iff C _).mpr fun t ht htn _ => by rw [h t ht] at htn; exact absurd htn (by decide)
  rw [botEP, evaluatePlain_projQ]
  show x ∈ Multiset.map _ _ ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨z, hz, th, hth, rfl⟩ := (mem_prodR _ _ D γ w).mp hw
    obtain ⟨r, hr, rfl⟩ := (mem_thP f k D γ th).mp hth
    have hall := hiff.mp ((he z).mp hz)
    refine ⟨hall, r, hr, ?_⟩
    rw [eval_cellSA, eval_vec7]
    simp only [SA.eval, Fin.append_right]
    show _ = Fin.append ![ValueType.nonzero, wtVal (upOf C ⊥), ValueType.nonzero, wtVal (upOf C ⊥),
      wtFlag (upOf C ⊥), sLo, sLo] (therm k r)
    rw [htop hall]
    rfl
  · rintro ⟨hall, r, hr, rfl⟩
    refine ⟨Fin.append (Fin.elim0 : Tuple T 0) (therm k r),
      (mem_prodR _ _ D γ _).mpr ⟨_, (he _).mpr (hiff.mpr hall), _,
        (mem_thP f k D γ _).mpr ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
    rw [eval_cellSA, eval_vec7]
    simp only [SA.eval, Fin.append_right]
    show Fin.append ![ValueType.nonzero, 0, ValueType.nonzero, 0, ValueType.nonzero, sLo, sLo]
      (therm k r) = Fin.append ![ValueType.nonzero, wtVal (upOf C ⊥), ValueType.nonzero,
        wtVal (upOf C ⊥), wtFlag (upOf C ⊥), sLo, sLo] (therm k r)
    rw [htop hall]
    rfl

/-! ## The cells -/

/-- **The cells of the descriptors**, each once. -/
def cellsQ (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg
    1)) :
    AggQueryIn T c (7 + k) (ColKind.allReg _) :=
  AggQueryIn.dedupG (AggQueryIn.sumByMuX (f 0) (f 1) (concP k CQ)
    (AggQueryIn.sumByMuX (f 2) (f 3) (succP f cnt k CQ)
      (AggQueryIn.sumByMuX (f 4) (f 5) (topP f cnt k CQ)
        (AggQueryIn.sumByMuX (f 6) (f 7) (botP f cnt k CQ) (botEP f cnt k CQ)))))

/-- A gap's lower bound: none, or a non-null value of the cut. -/
def GapOK (C : Finset T) : WithBot T → Prop
  | ⊥ => True
  | (t : T) => t ∈ C ∧ ValueType.isNull t = false

/-- **The cells**: a value of the cut, or a gap with a rank at most `k`. -/
def CellShape (C : Finset T) (k : ℕ) (x : Tuple T (7 + k)) : Prop :=
  (∃ a ∈ C, x = enc C k (.conc a)) ∨ ∃ l r, GapOK C l ∧ r ≤ k ∧ x = enc C k (.fresh l r)

omit [ValueType T] in
theorem noMention_projQ {N M : ℕ} (F : Fin M → SA T c N) (q : AggQueryIn T c N (ColKind.allReg N))
    {s : String} (h : q.noMention s) : (projQ F q).noMention s := by
  rw [projQ, AggQueryIn.noMention_castKind]; exact h

section Pieces

variable (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1))
  {s : String} (h : CQ.noMention s)
include h

omit h in
theorem noMention_thP : (thP (T := T) (c := c) f k).noMention s := noMention_thQ _ k s k

theorem noMention_concP : (concP k CQ).noMention s := noMention_projQ _ _ h

theorem noMention_succP : (succP f cnt k CQ).noMention s :=
  noMention_projQ _ _ ((noMention_prodR _ _).mpr ⟨AggQueryIn.noMention_notInDiffX _ _ _
    (noMention_ltQ' (noMention_nnQ CQ h)) (noMention_midQ' (noMention_nnQ CQ h)),
    noMention_thP (s := s) f k⟩)

theorem noMention_topP : (topP f cnt k CQ).noMention s :=
  noMention_projQ _ _ ((noMention_prodR _ _).mpr ⟨AggQueryIn.noMention_notInDiffX _ _ _
    (noMention_nnQ CQ h) (noMention_belowQ' (noMention_nnQ CQ h)), noMention_thP (s := s) f k⟩)

theorem noMention_botP : (botP f cnt k CQ).noMention s :=
  noMention_projQ _ _ ((noMention_prodR _ _).mpr ⟨AggQueryIn.noMention_notInDiffX _ _ _
    (noMention_nnQ CQ h) (noMention_aboveQ' (noMention_nnQ CQ h)), noMention_thP (s := s) f k⟩)

theorem noMention_botEP : (botEP f cnt k CQ).noMention s :=
  noMention_projQ _ _ ((noMention_prodR _ _).mpr ⟨AggQueryIn.noMention_notInDiffX _ _ _
    (AggQueryIn.noMention_unitC _) (noMention_projQ _ _ (noMention_nnQ CQ h)),
    noMention_thP (s := s) f k⟩)

theorem noMention_cellsQ : (cellsQ f cnt k CQ).noMention s :=
  AggQueryIn.noMention_dedupG _ _ (AggQueryIn.noMention_sumByMuX _ _ _ _
    (noMention_concP k CQ h) (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_succP f cnt k CQ h)
      (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_topP f cnt k CQ h)
        (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP f cnt k CQ h)
          (noMention_botEP f cnt k CQ h)))))

end Pieces

theorem mem_cellsQ (f : ℕ → String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hfr : FreshFor f CQ) (D : Database T)
    (γ : Fin c → T) (x : Tuple T (7 + k)) :
    Multiset.Mem ((cellsQ f cnt k CQ).evaluatePlain D γ) x ↔
      CellShape (valsU (CQ.evaluatePlain D γ)) k x := by
  set C := valsU (CQ.evaluatePlain D γ) with hC
  rw [cellsQ, AggQueryIn.evaluatePlain_dedupG]
  show x ∈ Multiset.dedup _ ↔ _
  rw [Multiset.mem_dedup]
  rw [AggQueryIn.evaluatePlain_sumByMuX _ _ _ _ (noMention_concP k CQ (hfr 0))
    (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_succP f cnt k CQ (hfr 1))
      (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_topP f cnt k CQ (hfr 1))
        (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP f cnt k CQ (hfr 1))
          (noMention_botEP f cnt k CQ (hfr 1)))))]
  rw [AggQueryIn.evaluatePlain_sumByMuX _ _ _ _ (noMention_succP f cnt k CQ (hfr 2))
    (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_topP f cnt k CQ (hfr 3))
      (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP f cnt k CQ (hfr 3))
        (noMention_botEP f cnt k CQ (hfr 3))))]
  rw [AggQueryIn.evaluatePlain_sumByMuX _ _ _ _ (noMention_topP f cnt k CQ (hfr 4))
    (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP f cnt k CQ (hfr 5))
      (noMention_botEP f cnt k CQ (hfr 5)))]
  rw [AggQueryIn.evaluatePlain_sumByMuX _ _ _ _ (noMention_botP f cnt k CQ (hfr 6))
    (noMention_botEP f cnt k CQ (hfr 7))]
  show x ∈ (_ + (_ + (_ + (_ + _))) : Multiset _) ↔ _
  simp only [Multiset.mem_add]
  refine Iff.trans (or_congr (mem_concP k CQ D γ x) (or_congr (mem_succP f hc k CQ hfr D γ x)
    (or_congr (mem_topP f hc k CQ hfr D γ x) (or_congr (mem_botP f hc k CQ hfr D γ x)
      (mem_botEP f hc k CQ hfr D γ x))))) ?_
  unfold CellShape
  constructor
  · rintro (h | ⟨t, ht, htn, -, r, hr, rfl⟩ | ⟨t, ht, htn, -, r, hr, rfl⟩ | ⟨-, r, hr, rfl⟩ |
      ⟨-, r, hr, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, r, ⟨ht, htn⟩, hr, rfl⟩
    · exact Or.inr ⟨t, r, ⟨ht, htn⟩, hr, rfl⟩
    · exact Or.inr ⟨⊥, r, trivial, hr, rfl⟩
    · exact Or.inr ⟨⊥, r, trivial, hr, rfl⟩
  · rintro (h | ⟨l, r, hl, hr, rfl⟩)
    · exact Or.inl h
    · cases l with
      | bot =>
        by_cases hex : ∃ t ∈ C, ValueType.isNull t = false
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hex, r, hr, rfl⟩)))
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨fun t ht => ?_, r, hr, rfl⟩)))
          by_contra hn
          exact hex ⟨t, ht, by simpa using hn⟩
      | coe t =>
        obtain ⟨ht, htn⟩ := hl
        by_cases htop : upOf C (t : WithBot T) = ⊤
        · exact Or.inr (Or.inr (Or.inl ⟨t, ht, htn, htop, r, hr, rfl⟩))
        · exact Or.inr (Or.inl ⟨t, ht, htn, htop, r, hr, rfl⟩)

theorem nodup_cellsQ (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T) :
    ((cellsQ f cnt k CQ).evaluatePlain D γ : Multiset (Tuple T (7 + k))).Nodup := by
  rw [cellsQ, AggQueryIn.evaluatePlain_dedupG]
  exact Multiset.nodup_dedup _

/-! ## Powers of a relation, block by block -/

theorem blk_lt {m K i j : ℕ} (hi : i < K) (hj : j < m) : m * i + j < m * K := by
  have : m * (i + 1) ≤ m * K := Nat.mul_le_mul_left m hi
  rw [Nat.mul_succ] at this
  omega

/-- **The block `i` of a row of `K` blocks of `m` columns.** -/
def blk (m K : ℕ) (v : Tuple T (m * K)) (i : Fin K) : Tuple T m :=
  fun j => v ⟨m * i + j, blk_lt i.2 j.2⟩

/-- **The `K`-th power of a relation**, its rows laid out block after
block. -/
def powX {m : ℕ} (R : AggQueryIn T c m (ColKind.allReg m)) :
    (K : ℕ) → AggQueryIn T c (m * K) (ColKind.allReg (m * K))
  | 0 => AggQueryIn.unitC
  | K + 1 => prodR (powX R K) R

omit [ValueType T] in
theorem blk_append_last {m K : ℕ} (y : Tuple T (m * K)) (e : Tuple T m) :
    blk m (K + 1) (Fin.append y e : Tuple T (m * K + m)) (Fin.last K) = e := by
  funext j
  show (Fin.append y e : Tuple T (m * K + m)) ⟨m * K + j, _⟩ = e j
  rw [show (⟨m * K + j, blk_lt (Fin.last K).2 j.2⟩ : Fin (m * K + m)) = Fin.natAdd (m * K) j
    from Fin.ext rfl, Fin.append_right]

omit [ValueType T] in
theorem blk_append_castSucc {m K : ℕ} (y : Tuple T (m * K)) (e : Tuple T m) (i : Fin K) :
    blk m (K + 1) (Fin.append y e : Tuple T (m * K + m)) (Fin.castSucc i) = blk m K y i := by
  funext j
  show (Fin.append y e : Tuple T (m * K + m)) ⟨m * i + j, _⟩ = y ⟨m * i + j, _⟩
  rw [show (⟨m * i + j, blk_lt (Fin.castSucc i).2 j.2⟩ : Fin (m * K + m))
    = Fin.castAdd m ⟨m * i + j, blk_lt i.2 j.2⟩ from Fin.ext rfl, Fin.append_left]

theorem mem_powX {m : ℕ} (R : AggQueryIn T c m (ColKind.allReg m)) (D : Database T)
    (γ : Fin c → T) :
    ∀ (K : ℕ) (v : Tuple T (m * K)), Multiset.Mem ((powX R K).evaluatePlain D γ) v ↔
      ∀ i, Multiset.Mem (R.evaluatePlain D γ) (blk m K v i)
  | 0, v => by
    rw [powX]
    erw [AggQueryIn.evaluatePlain_unitC D γ v]
    simp only [IsEmpty.forall_iff, iff_true]
    exact Multiset.mem_singleton_self v
  | K + 1, v => by
    rw [powX, mem_prodR]
    constructor
    · rintro ⟨y, hy, e, he, rfl⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [blk_append_last]; exact he
      · rw [blk_append_castSucc]; exact (mem_powX R D γ K y).mp hy j
    · intro h
      refine ⟨fun x => v (Fin.castAdd m x), (mem_powX R D γ K _).mpr (fun j => ?_),
        fun x => v (Fin.natAdd (m * K) x), ?_, ?_⟩
      · have := h (Fin.castSucc j)
        convert this using 1
        exact funext fun x => rfl
      · have := h (Fin.last K)
        convert this using 1
        exact funext fun x => rfl
      · exact (Fin.append_castAdd_natAdd (f := v)).symm

theorem nodup_powX {m : ℕ} (R : AggQueryIn T c m (ColKind.allReg m)) (D : Database T)
    (γ : Fin c → T) (h : (R.evaluatePlain D γ : Multiset (Tuple T m)).Nodup) :
    ∀ K, ((powX R K).evaluatePlain D γ : Multiset (Tuple T (m * K))).Nodup
  | 0 => by
    rw [powX]
    erw [AggQueryIn.evaluatePlain_unitC D γ Fin.elim0]
    exact Multiset.nodup_singleton _
  | K + 1 => by
    rw [powX]
    exact nodup_prodR _ _ D γ (nodup_powX R D γ h K) h

omit [ValueType T] in
theorem noMention_powX {m : ℕ} (R : AggQueryIn T c m (ColKind.allReg m)) {s : String}
    (h : R.noMention s) : ∀ K, (powX R K).noMention s
  | 0 => by rw [powX]; exact AggQueryIn.noMention_unitC s
  | K + 1 => by rw [powX]; exact (noMention_prodR _ _).mpr ⟨noMention_powX R h K, h⟩

/-! ## The descriptors -/

/-- **The descriptors**: `k` cells. -/
def descQ (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) :
    AggQueryIn T c (k * (7 + k)) (ColKind.allReg _) :=
  projQ (fun x => SA.col (Fin.cast (Nat.mul_comm k (7 + k)) x)) (powX (cellsQ f cnt k CQ) k)

omit [ValueType T] in
theorem cellOf_cast {k : ℕ} (w : Tuple T ((7 + k) * k)) (i : Fin k) :
    cellOf (fun x => w (Fin.cast (Nat.mul_comm k (7 + k)) x)) i = blk (7 + k) k w i := by
  funext j
  show w (Fin.cast _ (finProdFinEquiv (i, j))) = w ⟨(7 + k) * i + j, _⟩
  congr 1
  exact Fin.ext (by simp [finProdFinEquiv]; omega)

theorem mem_descQ (f : ℕ → String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hfr : FreshFor f CQ) (D : Database T)
    (γ : Fin c → T) (v : Tuple T (k * (7 + k))) :
    Multiset.Mem ((descQ f cnt k CQ).evaluatePlain D γ) v ↔
      ∀ i, CellShape (valsU (CQ.evaluatePlain D γ)) k (cellOf v i) := by
  rw [descQ, evaluatePlain_projQ]
  show v ∈ Multiset.map _ _ ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    have := (mem_powX _ D γ k w).mp hw i
    rw [show (fun j => (SA.col (c := c) (Fin.cast (Nat.mul_comm k (7 + k)) j)).eval w γ)
      = (fun x => w (Fin.cast (Nat.mul_comm k (7 + k)) x)) from rfl, cellOf_cast]
    exact (mem_cellsQ f hc k CQ hfr D γ _).mp this
  · intro h
    refine ⟨fun y => v (Fin.cast (Nat.mul_comm k (7 + k)).symm y), (mem_powX _ D γ k _).mpr
      (fun i => (mem_cellsQ f hc k CQ hfr D γ _).mpr ?_), ?_⟩
    · have := cellOf_cast (fun y => v (Fin.cast (Nat.mul_comm k (7 + k)).symm y)) i
      simp only [Fin.cast_cast, Fin.cast_eq_self] at this
      rw [← this]
      exact h i
    · funext x
      show v (Fin.cast _ (Fin.cast _ x)) = v x
      rw [Fin.cast_cast, Fin.cast_eq_self]

theorem nodup_descQ (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T) :
    ((descQ f cnt k CQ).evaluatePlain D γ : Multiset (Tuple T (k * (7 + k)))).Nodup := by
  rw [descQ, evaluatePlain_projQ]
  refine (nodup_powX _ D γ (nodup_cellsQ f cnt k CQ D γ) k).map (fun w w' h => funext fun y => ?_)
  have := congrFun h (Fin.cast (Nat.mul_comm k (7 + k)).symm y)
  simpa [SA.eval] using this

/-! ## The environment -/

/-- **The environment of the symbolic evaluation**, built from a cut. -/
def envOf (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) :
    SymEnv T k c where
  CQ := CQ
  Desc := descQ (fun i => f (2 * i)) cnt k CQ
  ctrK := ctrW k
  Lq := fun n => lqQ (fun i => f (2 * i + 1)) cnt CQ (ctrW k n)
  Sq := fun n => sqQ (fun i => f (2 * i + 1)) cnt CQ (ctrW k n)

theorem cutAt_envOf (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T) :
    cutAt (envOf f cnt k CQ) D γ = valsU (CQ.evaluatePlain D γ) := rfl

/-- **The environment built from a cut is sound** wherever the cut holds
the null. -/
theorem envOK_envOf (f : ℕ → String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hfr : FreshFor f CQ) (D : Database T)
    (γ : Fin c → T)
    (hnull : ∀ a : T, ValueType.isNull a = true → a ∈ valsU (CQ.evaluatePlain D γ)) :
    EnvOK (envOf f cnt k CQ) D γ := by
  have hfr0 : FreshFor (fun i => f (2 * i)) CQ := fun i => hfr _
  have hfr1 : FreshFor (fun i => f (2 * i + 1)) CQ := fun i => hfr _
  refine ⟨nodup_descQ _ cnt k CQ D γ, fun par => ?_, fun n => ?_⟩
  · rw [cutAt_envOf]
    refine (mem_descQ _ hc k CQ hfr0 D γ _).mpr fun i => ?_
    rw [descEnc, cellOf_ofCells]
    set C := valsU (CQ.evaluatePlain D γ)
    by_cases hf : IsFresh C (par i)
    · rw [code_of_fresh hf]
      refine Or.inr ⟨lo C (par i), rank C par (par i), ?_, (rank_code_lt i).le, rfl⟩
      cases hl : lo C (par i) with
      | bot => trivial
      | coe t =>
        obtain ⟨ht, htn, -⟩ := lo_eq_coe hl
        exact ⟨ht, htn⟩
    · rw [code_of_not_fresh hf]
      refine Or.inl ⟨par i, ?_, rfl⟩
      by_contra hm
      cases hn : ValueType.isNull (par i)
      · exact hf ⟨hm, hn⟩
      · exact hm (hnull _ hn)
  · exact ctr_ok _ hc CQ hfr1 D γ k n

/-- **The environment names only what the cut names.** -/
theorem envNoMention_envOf (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) {s : String} (h : CQ.noMention s) :
    EnvNoMention (envOf f cnt k CQ) s := by
  refine ⟨h, noMention_projQ _ _ (noMention_powX _ (noMention_cellsQ _ cnt k CQ h) k),
    fun n => ⟨?_, ?_⟩⟩
  · exact AggQueryIn.noMention_notInDiffX _ _ _ (noMention_ctrQ _ CQ h _)
      (noMention_aboveQ' (noMention_ctrQ _ CQ h _))
  · exact AggQueryIn.noMention_notInDiffX _ _ _ (noMention_ltQ' (noMention_ctrQ _ CQ h _))
      (noMention_midQ' (noMention_ctrQ _ CQ h _))

end Build

end Sym
