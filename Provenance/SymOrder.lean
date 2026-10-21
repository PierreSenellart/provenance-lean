module

public import Provenance.MuUnion
public import Provenance.SumByProd
public import Provenance.SymMu
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Provenance.SymCorrect
import all Provenance.MuUnion
import all Provenance.OrderSpec
import all Provenance.PlainBasis
import all Provenance.SumByProd
import all Provenance.SymCorrect
import all Provenance.SymMu
import all Provenance.Util.Kleene

/-!
# The successor relation of a finite relation, without a recursion

A relation of non-null rows, listed once each, is sorted by the
lexicographic ascending order (`ascLt`). Its **successor relation** – the
pairs of consecutive rows – its least row and its greatest row are
written with products, selections, projections and the `NOT IN`
difference: a pair of rows in increasing order with no row between them,
a row with no row below it, a row with no row above it
(`Sym.evaluatePlain_succQ`, `Sym.evaluatePlain_leastQ`,
`Sym.evaluatePlain_greatestQ`). These are what a bounded recursion's
counters and the gaps of a cut are read off.
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

/-! ## Consecutive elements of a sorted list -/

section Consecutive

variable {α : Type} (r : α → α → Prop)

/-- **Two elements of a strictly sorted list are consecutive** exactly
when the first is below the second and no element lies between them. -/
private theorem mem_zip_tail_iff (htr : ∀ a b c, r a b → r b c → r a c) (hirr : ∀ a, ¬ r a a) :
    ∀ (l : List α), l.Pairwise r → ∀ a b : α,
      (a, b) ∈ l.zip l.tail ↔ a ∈ l ∧ b ∈ l ∧ r a b ∧ ∀ c ∈ l, ¬ (r a c ∧ r c b)
  | List.nil => fun _ a b => by simp
  | List.cons x List.nil => fun _ a b => by
    simp only [List.tail_cons, List.zip_nil_right, List.not_mem_nil, false_iff, List.mem_singleton]
    rintro ⟨rfl, rfl, h, -⟩
    exact hirr _ h
  | List.cons x (List.cons y l) => fun hl a b => by
    have hl' : (List.cons y l).Pairwise r := hl.of_cons
    have hx : ∀ z ∈ List.cons y l, r x z := fun _ hz => List.rel_of_pairwise_cons hl hz
    have hy : ∀ z ∈ l, r y z := fun _ hz => List.rel_of_pairwise_cons hl' hz
    have ih : (a, b) ∈ (List.cons y l).zip l ↔ _ := mem_zip_tail_iff htr hirr (List.cons y l) hl'
        a b
    rw [List.tail_cons, List.zip_cons_cons, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨ha, hb, hab, hn⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        refine ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self,
          hx _ List.mem_cons_self, fun c hc ⟨h₁, h₂⟩ => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hirr _ h₁
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hirr _ h₂
        · exact hirr _ (htr _ _ _ (hy _ hc) h₂)
      · refine ⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, hab, fun c hc h => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hirr _ (htr _ _ _ (hx _ ha) h.1)
        · exact hn c hc h
    · rintro ⟨ha, hb, hab, hn⟩
      rcases List.mem_cons.mp ha with rfl | ha'
      · left
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd hab (hirr _)
        rcases List.mem_cons.mp hb' with rfl | hb''
        · rfl
        · exact absurd ⟨hx _ List.mem_cons_self, hy _ hb''⟩
            (hn _ (List.mem_cons_of_mem _ List.mem_cons_self))
      · right
        refine ⟨ha', ?_, hab, fun c hc => hn c (List.mem_cons_of_mem _ hc)⟩
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd (htr _ _ _ (hx _ ha') hab) (hirr _)
        · exact hb'

/-- The pairs of consecutive elements of a list without repetition are
listed once each. -/
private theorem nodup_zip_tail : ∀ (l : List α), l.Nodup → (l.zip l.tail).Nodup
  | List.nil => fun _ => List.nodup_nil
  | List.cons x List.nil => fun _ => by simp
  | List.cons x (List.cons y l) => fun hl => by
    rw [List.tail_cons, List.zip_cons_cons]
    refine List.nodup_cons.mpr ⟨fun h => ?_, nodup_zip_tail (List.cons y l) hl.of_cons⟩
    have := (List.of_mem_zip h).1
    exact (List.nodup_cons.mp hl).1 this

end Consecutive

/-! ## The sorted listing of a relation -/

/-- **The listing of a relation's rows in increasing order.** -/
noncomputable def sortedRows {p : ℕ} (R : Multiset (Tuple T p)) : List (Tuple T p) :=
  R.toFinset.sort (ascLe p)

private theorem mem_sortedRows {p : ℕ} {R : Multiset (Tuple T p)} {x : Tuple T p} :
    x ∈ sortedRows R ↔ x ∈ R := by
  unfold sortedRows
  rw [Finset.mem_sort, Multiset.mem_toFinset]

private theorem nodup_sortedRows {p : ℕ} (R : Multiset (Tuple T p)) : (sortedRows R).Nodup :=
  Finset.sort_nodup _ _

private theorem pairwise_sortedRows {p : ℕ} (R : Multiset (Tuple T p)) :
    (sortedRows R).Pairwise (ascLt p) := by
  have hp := Finset.pairwise_sort (s := R.toFinset) (r := ascLe p)
  have hnd := nodup_sortedRows R
  unfold sortedRows at hnd ⊢
  rw [List.pairwise_iff_getElem] at hp ⊢
  intro i j hi hj hij
  refine OrderSpec.lt_of_le_of_ne_asc (hp i j hi hj hij) fun heq => ?_
  exact absurd ((List.Nodup.getElem_inj_iff hnd).mp heq) (Nat.ne_of_lt hij)

private theorem length_sortedRows {p : ℕ} (R : Multiset (Tuple T p)) :
    (sortedRows R).length = R.toFinset.card :=
  Finset.length_sort _

private theorem ascLt_trans {p : ℕ} (a b c : Tuple T p) (h₁ : ascLt p a b) (h₂ : ascLt p b c) :
    ascLt p a c := OrderSpec.lt_trans' _ h₁ h₂

private theorem ascLt_irrefl {p : ℕ} (a : Tuple T p) : ¬ ascLt p a a := by
  unfold ascLt; rw [OrderSpec.lt_irrefl]; simp

/-! ## The comparison as a predicate -/

/-- **One block of a row below another**, in the ascending lexicographic
order. -/
def ltOn {c N p : ℕ} (x y : Fin p → Fin N) : GenPredIn T c (ColKind.allReg N) :=
  OrderSpec.ltPredOn (OrderSpec.asc p) (fun k => TermGIn.index (x k) rfl)
    (fun k => TermGIn.index (y k) rfl) (List.finRange p)

private theorem holdsPlain_ltOn {c N p : ℕ} (x y : Fin p → Fin N) (u : Tuple T N) (γ : Fin c → T)
    (hx : ∀ k, ValueType.isNull (u (x k)) = false) (hy : ∀ k, ValueType.isNull (u (y k)) = false) :
    (ltOn (c := c) x y).holdsPlain u γ ↔ ascLt p (fun k => u (x k)) (fun k => u (y k)) := by
  rw [ltOn, OrderSpec.ltPredOn, OrderSpec.holdsPlain_ltPredOnOf (OrderSpec.asc p) _
    (fun k => TermGIn.index (x k) rfl) (fun k => TermGIn.index (y k) rfl) u γ
    (fun k => OrderCol.holdsPlain_ltPred_of (OrderSpec.asc p k)
      (TermGIn.index (x k) rfl) (TermGIn.index (y k) rfl) u γ (hx k) (hy k))
    (fun k a b => OrderSpec.OrderCol.peer_ASC_iff a b)]
  show OrderSpec.le (OrderSpec.asc p) (fun k => u (y k)) (fun k => u (x k)) = false ↔ _
  unfold ascLt
  rw [OrderSpec.lt_iff]

private theorem noFun_ltOn {c N p : ℕ} (x y : Fin p → Fin N) : (ltOn (T := T) (c := c) x y).noFun = true
    := by
  rw [ltOn, OrderSpec.ltPredOn]
  exact OrderSpec.noFun_ltPredOnOf (fun k => OrderCol.noFun_ltPred _ rfl rfl)
    (fun _ => rfl) (fun _ => rfl) _

/-! ## The two blocks of a row -/

/-- The first block of a row. -/
def blockL' (a b : ℕ) (x : Tuple T (a + b)) : Tuple T a := fun i => x (Fin.castAdd b i)

/-- The second block of a row. -/
def blockR' (a b : ℕ) (x : Tuple T (a + b)) : Tuple T b := fun i => x (Fin.natAdd a i)

omit [ValueType T] in
@[simp] private theorem blockL'_append {a b : ℕ} (x : Tuple T a) (y : Tuple T b) :
    blockL' a b (Fin.append x y) = x := funext fun i => Fin.append_left x y i

omit [ValueType T] in
@[simp] private theorem blockR'_append {a b : ℕ} (x : Tuple T a) (y : Tuple T b) :
    blockR' a b (Fin.append x y) = y := funext fun i => Fin.append_right x y i

omit [ValueType T] in
private theorem append_inj {a b : ℕ} {x x' : Tuple T a} {y y' : Tuple T b}
    (h : (Fin.append x y : Tuple T (a + b)) = Fin.append x' y') : x = x' ∧ y = y' := by
  have h₁ := congrArg (blockL' a b) h
  have h₂ := congrArg (blockR' a b) h
  simp only [blockL'_append, blockR'_append] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-! ## Products and projections -/

section Queries

variable {c : ℕ}

/-- **A projection onto arguments**: columns, constants and context
values. -/
def projQ {N M : ℕ} {l : List (String × ℕ)} (F : Fin M → SA T c N)
    (q : AggQueryIn T c N (ColKind.allReg N) l) : AggQueryIn T c M (ColKind.allReg M) l :=
  (AggQueryIn.Proj (projSA F) q).castKind (projSA_kind F)

private theorem evaluatePlain_projQ {N M : ℕ} {l : List (String × ℕ)} (F : Fin M → SA T c N)
    (q : AggQueryIn T c N (ColKind.allReg N) l) (D : Database T) (γ : Fin c → T) :
    ((projQ F q).evaluatePlain D γ : Multiset (Tuple T M))
      = (q.evaluatePlain D γ : Multiset (Tuple T N)).map (fun x i => (F i).eval x γ) :=
  evaluatePlain_projSA F q _ D γ

private theorem mem_prodR {a b : ℕ} {l₁ l₂ : List (String × ℕ)}
    (q₁ : AggQueryIn T c a (ColKind.allReg a) l₁) (q₂ : AggQueryIn T c b (ColKind.allReg b) l₂)
    (D : Database T) (γ : Fin c → T) (v : Tuple T (a + b)) :
    Multiset.Mem ((prodR q₁ q₂).evaluatePlain D γ) v ↔
      ∃ x, Multiset.Mem (q₁.evaluatePlain D γ) x ∧ ∃ y, Multiset.Mem (q₂.evaluatePlain D γ) y
        ∧ v = Fin.append x y := by
  rw [evaluatePlain_prodR]
  show v ∈ Multiset.bind _ _ ↔ _
  rw [Multiset.mem_bind]
  constructor
  · rintro ⟨x, hx, hv⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hv
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, Multiset.mem_map_of_mem _ hy⟩

/-- A product of relations listed once each is listed once each. -/
private theorem nodup_prodR {a b : ℕ} {l₁ l₂ : List (String × ℕ)}
    (q₁ : AggQueryIn T c a (ColKind.allReg a) l₁) (q₂ : AggQueryIn T c b (ColKind.allReg b) l₂)
    (D : Database T) (γ : Fin c → T)
    (h₁ : (q₁.evaluatePlain D γ : Multiset (Tuple T a)).Nodup)
    (h₂ : (q₂.evaluatePlain D γ : Multiset (Tuple T b)).Nodup) :
    ((prodR q₁ q₂).evaluatePlain D γ : Multiset (Tuple T (a + b))).Nodup := by
  rw [evaluatePlain_prodR]
  have : ((q₁.evaluatePlain D γ : Multiset (Tuple T a)).bind (fun r =>
      (q₂.evaluatePlain D γ : Multiset (Tuple T b)).map (fun r' => Fin.append r r')))
      = (Multiset.product (q₁.evaluatePlain D γ : Multiset (Tuple T a))
          (q₂.evaluatePlain D γ : Multiset (Tuple T b))).map (fun xy => Fin.append xy.1 xy.2) := by
    rw [Multiset.product, Multiset.map_bind]
    simp only [Multiset.map_map, Function.comp]
    rfl
  rw [this]
  refine (Multiset.Nodup.product h₁ h₂).map (fun xy xy' h => ?_)
  have h₁' := congrArg (blockL' a b) h
  have h₂' := congrArg (blockR' a b) h
  simp only [blockL'_append, blockR'_append] at h₁' h₂'
  exact Prod.ext h₁' h₂'

end Queries

/-! ## The order queries -/

section OrderQueries

variable {c p : ℕ}

private theorem holdsPlain_and' {N : ℕ} (φ ψ : GenPredIn T c (ColKind.allReg N)) (u : Tuple T N)
    (γ : Fin c → T) : (GenPredIn.and φ ψ).holdsPlain u γ ↔ φ.holdsPlain u γ ∧ ψ.holdsPlain u γ :=
  Kleene.and_eq_true_iff _ _

/-- **The pairs of rows in increasing order.** -/
def ltQ (R : AggQueryIn T c p (ColKind.allReg p)) : AggQueryIn T c (p + p) (ColKind.allReg (p +
    p)) :=
  AggQueryIn.Sel (ltOn (Fin.castAdd p) (Fin.natAdd p)) (prodR R R) trivial

/-- **The pairs of rows with a row between them.** -/
def midQ (R : AggQueryIn T c p (ColKind.allReg p)) : AggQueryIn T c (p + p) (ColKind.allReg (p +
    p)) :=
  projQ (fun j => SA.col (Fin.addCases (fun k => Fin.castAdd p (Fin.castAdd p k))
      (fun k => Fin.natAdd (p + p) k) j))
    (AggQueryIn.Sel (GenPredIn.and
        (ltOn (fun k => Fin.castAdd p (Fin.castAdd p k)) (fun k => Fin.castAdd p (Fin.natAdd p k)))
        (ltOn (fun k => Fin.castAdd p (Fin.natAdd p k)) (fun k => Fin.natAdd (p + p) k)))
      (prodR (prodR R R) R) trivial)

/-- The rows with a row below them. -/
def aboveQ (R : AggQueryIn T c p (ColKind.allReg p)) : AggQueryIn T c p (ColKind.allReg p) :=
  projQ (fun k => SA.col (Fin.natAdd p k)) (ltQ R)

/-- The rows with a row above them. -/
def belowQ (R : AggQueryIn T c p (ColKind.allReg p)) : AggQueryIn T c p (ColKind.allReg p) :=
  projQ (fun k => SA.col (Fin.castAdd p k)) (ltQ R)

/-- **The successor relation.** -/
def succQ (s₁ s₂ : String) (cnt : SeqAggFunc T) (R : AggQueryIn T c p (ColKind.allReg p)) :
    AggQueryIn T c (p + p) (ColKind.allReg (p + p)) :=
  AggQueryIn.notInDiffX s₁ s₂ cnt (ltQ R) (midQ R)

/-- **The least row.** -/
def leastQ (s₁ s₂ : String) (cnt : SeqAggFunc T) (R : AggQueryIn T c p (ColKind.allReg p)) :
    AggQueryIn T c p (ColKind.allReg p) :=
  AggQueryIn.notInDiffX s₁ s₂ cnt R (aboveQ R)

/-- **The greatest row.** -/
def greatestQ (s₁ s₂ : String) (cnt : SeqAggFunc T) (R : AggQueryIn T c p (ColKind.allReg p)) :
    AggQueryIn T c p (ColKind.allReg p) :=
  AggQueryIn.notInDiffX s₁ s₂ cnt R (belowQ R)

variable (R : AggQueryIn T c p (ColKind.allReg p)) (D : Database T) (γ : Fin c → T)

/-- What the relation's rows are asked: no null value. -/
def NonNullRows : Prop :=
  ∀ x, Multiset.Mem (R.evaluatePlain D γ) x → ∀ i, ValueType.isNull (x i) = false

variable {R D γ}

private theorem mem_ltQ (hR : NonNullRows R D γ) (v : Tuple T (p + p)) :
    Multiset.Mem ((ltQ R).evaluatePlain D γ) v ↔
      ∃ a, Multiset.Mem (R.evaluatePlain D γ) a ∧ ∃ b, Multiset.Mem (R.evaluatePlain D γ) b
        ∧ v = Fin.append a b ∧ ascLt p a b := by
  show v ∈ Multiset.filter _ _ ↔ _
  rw [Multiset.mem_filter]
  constructor
  · rintro ⟨hv, hlt⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prodR R R D γ v).mp hv
    refine ⟨a, ha, b, hb, rfl, ?_⟩
    have := (holdsPlain_ltOn (c := c) (Fin.castAdd p) (Fin.natAdd p) (Fin.append a b) γ
      (fun k => by rw [Fin.append_left]; exact hR a ha k)
      (fun k => by rw [Fin.append_right]; exact hR b hb k)).mp hlt
    simpa only [Fin.append_left, Fin.append_right] using this
  · rintro ⟨a, ha, b, hb, rfl, hlt⟩
    refine ⟨(mem_prodR R R D γ _).mpr ⟨a, ha, b, hb, rfl⟩, ?_⟩
    refine (holdsPlain_ltOn (c := c) (Fin.castAdd p) (Fin.natAdd p) (Fin.append a b) γ
      (fun k => by rw [Fin.append_left]; exact hR a ha k)
      (fun k => by rw [Fin.append_right]; exact hR b hb k)).mpr ?_
    simpa only [Fin.append_left, Fin.append_right] using hlt

private theorem mem_midQ (hR : NonNullRows R D γ) (v : Tuple T (p + p)) :
    Multiset.Mem ((midQ R).evaluatePlain D γ) v ↔
      ∃ a, Multiset.Mem (R.evaluatePlain D γ) a ∧ ∃ b, Multiset.Mem (R.evaluatePlain D γ) b
        ∧ ∃ e, Multiset.Mem (R.evaluatePlain D γ) e ∧ v = Fin.append a e
          ∧ ascLt p a b ∧ ascLt p b e := by
  rw [midQ, evaluatePlain_projQ]
  show v ∈ Multiset.map _ (Multiset.filter _ _) ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hw, hp⟩ := Multiset.mem_filter.mp hw
    obtain ⟨x, hx, e, he, rfl⟩ := (mem_prodR _ R D γ w).mp hw
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prodR R R D γ x).mp hx
    rw [holdsPlain_and'] at hp
    have h₁ := (holdsPlain_ltOn (c := c) _ _ (Fin.append (Fin.append a b) e) γ
      (fun k => by simp only [Fin.append_left]; exact hR a ha k)
      (fun k => by simp only [Fin.append_left, Fin.append_right]; exact hR b hb k)).mp hp.1
    have h₂ := (holdsPlain_ltOn (c := c) _ _ (Fin.append (Fin.append a b) e) γ
      (fun k => by simp only [Fin.append_left, Fin.append_right]; exact hR b hb k)
      (fun k => by simp only [Fin.append_right]; exact hR e he k)).mp hp.2
    simp only [Fin.append_left, Fin.append_right] at h₁ h₂
    refine ⟨a, ha, b, hb, e, he, ?_, h₁, h₂⟩
    funext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [Fin.addCases_left, SA.eval, Fin.append_left]
    · simp only [Fin.addCases_right, SA.eval, Fin.append_right]
  · rintro ⟨a, ha, b, hb, e, he, rfl, h₁, h₂⟩
    refine ⟨Fin.append (Fin.append a b) e, Multiset.mem_filter.mpr ⟨(mem_prodR _ R D γ _).mpr
      ⟨_, (mem_prodR R R D γ _).mpr ⟨a, ha, b, hb, rfl⟩, e, he, rfl⟩, ?_⟩, ?_⟩
    · rw [holdsPlain_and']
      refine ⟨(holdsPlain_ltOn (c := c) _ _ (Fin.append (Fin.append a b) e) γ
        (fun k => by simp only [Fin.append_left]; exact hR a ha k)
        (fun k => by simp only [Fin.append_left, Fin.append_right]; exact hR b hb k)).mpr ?_,
        (holdsPlain_ltOn (c := c) _ _ (Fin.append (Fin.append a b) e) γ
        (fun k => by simp only [Fin.append_left, Fin.append_right]; exact hR b hb k)
        (fun k => by simp only [Fin.append_right]; exact hR e he k)).mpr ?_⟩
      · simpa only [Fin.append_left, Fin.append_right] using h₁
      · simpa only [Fin.append_left, Fin.append_right] using h₂
    · funext j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp only [Fin.addCases_left, SA.eval, Fin.append_left]
      · simp only [Fin.addCases_right, SA.eval, Fin.append_right]

private theorem noMention_ltQ' {s : String} (h : R.noMention s) : (ltQ R).noMention s :=
  (noMention_prodR R R).mpr ⟨h, h⟩

private theorem noMention_midQ' {s : String} (h : R.noMention s) : (midQ R).noMention s := by
  rw [midQ, projQ, AggQueryIn.noMention_castKind]
  exact (noMention_prodR _ R).mpr ⟨(noMention_prodR R R).mpr ⟨h, h⟩, h⟩

/-- The successor relation of the sorted listing, row by row. -/
private theorem mem_succRel_iff (hR : NonNullRows R D γ) (v : Tuple T (p + p)) :
    v ∈ (succRel (sortedRows (R.evaluatePlain D γ : Multiset (Tuple T p)))
        : Multiset (Tuple T (p + p))) ↔
      ∃ a, Multiset.Mem (R.evaluatePlain D γ) a ∧ ∃ b, Multiset.Mem (R.evaluatePlain D γ) b
        ∧ v = Fin.append a b ∧ ascLt p a b
        ∧ ∀ e, Multiset.Mem (R.evaluatePlain D γ) e → ¬ (ascLt p a e ∧ ascLt p e b) := by
  have _ := hR
  unfold succRel
  rw [Multiset.mem_coe, List.mem_map]
  have hz := mem_zip_tail_iff (ascLt p) ascLt_trans ascLt_irrefl _
    (pairwise_sortedRows (R.evaluatePlain D γ : Multiset (Tuple T p)))
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    obtain ⟨ha, hb, hlt, hn⟩ := (hz a b).mp hab
    exact ⟨a, mem_sortedRows.mp ha, b, mem_sortedRows.mp hb, rfl, hlt,
      fun e he => hn e (mem_sortedRows.mpr he)⟩
  · rintro ⟨a, ha, b, hb, rfl, hlt, hn⟩
    exact ⟨(a, b), (hz a b).mpr ⟨mem_sortedRows.mpr ha, mem_sortedRows.mpr hb, hlt,
      fun e he => hn e (mem_sortedRows.mp he)⟩, rfl⟩

omit [ValueType T] in
private theorem nodup_succRel (L : List (Tuple T p)) (hL : L.Nodup) :
    (succRel L : Multiset (Tuple T (p + p))).Nodup := by
  unfold succRel
  rw [Multiset.coe_nodup]
  refine (nodup_zip_tail L hL).map (fun x y h => ?_)
  obtain ⟨h₁, h₂⟩ := append_inj h
  exact Prod.ext h₁ h₂

/-- **The successor relation, row by row**, whatever the multiplicities. -/
private theorem mem_succQ (s₁ s₂ : String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (h₁ : R.noMention s₁) (h₂ : R.noMention s₂) (hR : NonNullRows R D γ) (v : Tuple T (p + p)) :
    Multiset.Mem ((succQ s₁ s₂ cnt R).evaluatePlain D γ) v ↔
      ∃ a, Multiset.Mem (R.evaluatePlain D γ) a ∧ ∃ b, Multiset.Mem (R.evaluatePlain D γ) b
        ∧ v = Fin.append a b ∧ ascLt p a b
        ∧ ∀ e, Multiset.Mem (R.evaluatePlain D γ) e → ¬ (ascLt p a e ∧ ascLt p e b) := by
  rw [succQ, AggQueryIn.evaluatePlain_notInDiffX s₁ s₂ cnt hc _ _ (noMention_ltQ' h₁)
    (noMention_midQ' h₂) D γ]
  show v ∈ Multiset.filter _ _ ↔ _
  rw [Multiset.mem_filter]
  constructor
  · rintro ⟨hv, hm⟩
    obtain ⟨a, ha, b, hb, rfl, hlt⟩ := (mem_ltQ hR v).mp hv
    refine ⟨a, ha, b, hb, rfl, hlt, fun e he h => hm ?_⟩
    exact (mem_midQ hR _).mpr ⟨a, ha, e, he, b, hb, rfl, h.1, h.2⟩
  · rintro ⟨a, ha, b, hb, rfl, hlt, hn⟩
    refine ⟨(mem_ltQ hR _).mpr ⟨a, ha, b, hb, rfl, hlt⟩, fun hm => ?_⟩
    obtain ⟨a', ha', e, he, b', hb', heq, h₁, h₂⟩ := (mem_midQ hR _).mp hm
    obtain ⟨rfl, rfl⟩ := append_inj heq
    exact hn e he ⟨h₁, h₂⟩

/-- **The successor relation, as a query.** -/
theorem evaluatePlain_succQ (s₁ s₂ : String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (h₁ : R.noMention s₁) (h₂ : R.noMention s₂) (hR : NonNullRows R D γ)
    (hnd : (R.evaluatePlain D γ : Multiset (Tuple T p)).Nodup) :
    ((succQ s₁ s₂ cnt R).evaluatePlain D γ : Multiset (Tuple T (p + p)))
      = succRel (sortedRows (R.evaluatePlain D γ : Multiset (Tuple T p))) := by
  rw [succQ, AggQueryIn.evaluatePlain_notInDiffX s₁ s₂ cnt hc _ _ (noMention_ltQ' h₁)
    (noMention_midQ' h₂) D γ]
  refine Multiset.Nodup.ext ?_ (nodup_succRel _ (nodup_sortedRows _)) |>.mpr fun v => ?_
  · exact Multiset.Nodup.filter _ (Multiset.Nodup.filter _ (nodup_prodR R R D γ hnd hnd))
  · rw [mem_succRel_iff hR]
    show v ∈ Multiset.filter _ _ ↔ _
    rw [Multiset.mem_filter]
    constructor
    · rintro ⟨hv, hm⟩
      obtain ⟨a, ha, b, hb, rfl, hlt⟩ := (mem_ltQ hR v).mp hv
      refine ⟨a, ha, b, hb, rfl, hlt, fun e he h => hm ?_⟩
      exact (mem_midQ hR _).mpr ⟨a, ha, e, he, b, hb, rfl, h.1, h.2⟩
    · rintro ⟨a, ha, b, hb, rfl, hlt, hn⟩
      refine ⟨(mem_ltQ hR _).mpr ⟨a, ha, b, hb, rfl, hlt⟩, fun hm => ?_⟩
      obtain ⟨a', ha', e, he, b', hb', heq, h₁, h₂⟩ := (mem_midQ hR _).mp hm
      obtain ⟨rfl, rfl⟩ := append_inj heq
      exact hn e he ⟨h₁, h₂⟩

private theorem mem_aboveQ (hR : NonNullRows R D γ) (x : Tuple T p) :
    Multiset.Mem ((aboveQ R).evaluatePlain D γ) x ↔
      Multiset.Mem (R.evaluatePlain D γ) x ∧ ∃ a, Multiset.Mem (R.evaluatePlain D γ) a ∧ ascLt p a
        x := by
  rw [aboveQ, evaluatePlain_projQ]
  show x ∈ Multiset.map _ _ ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨a, ha, b, hb, rfl, hlt⟩ := (mem_ltQ hR v).mp hv
    have : (fun i => (SA.col (c := c) (Fin.natAdd p i)).eval (Fin.append a b : Tuple T (p + p)) γ)
        = b := funext fun i => Fin.append_right a b i
    rw [this]
    exact ⟨hb, a, ha, hlt⟩
  · rintro ⟨hx, a, ha, hlt⟩
    exact ⟨Fin.append a x, (mem_ltQ hR _).mpr ⟨a, ha, x, hx, rfl, hlt⟩,
      funext fun i => Fin.append_right a x i⟩

private theorem mem_belowQ (hR : NonNullRows R D γ) (x : Tuple T p) :
    Multiset.Mem ((belowQ R).evaluatePlain D γ) x ↔
      Multiset.Mem (R.evaluatePlain D γ) x ∧ ∃ b, Multiset.Mem (R.evaluatePlain D γ) b ∧ ascLt p x
        b := by
  rw [belowQ, evaluatePlain_projQ]
  show x ∈ Multiset.map _ _ ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨a, ha, b, hb, rfl, hlt⟩ := (mem_ltQ hR v).mp hv
    have : (fun i => (SA.col (c := c) (Fin.castAdd p i)).eval (Fin.append a b : Tuple T (p + p)) γ)
        = a := funext fun i => Fin.append_left a b i
    rw [this]
    exact ⟨ha, b, hb, hlt⟩
  · rintro ⟨hx, b, hb, hlt⟩
    exact ⟨Fin.append x b, (mem_ltQ hR _).mpr ⟨x, hx, b, hb, rfl, hlt⟩,
      funext fun i => Fin.append_left x b i⟩

private theorem noMention_aboveQ' {s : String} (h : R.noMention s) : (aboveQ R).noMention s := by
  rw [aboveQ, projQ, AggQueryIn.noMention_castKind]; exact noMention_ltQ' h

private theorem noMention_belowQ' {s : String} (h : R.noMention s) : (belowQ R).noMention s := by
  rw [belowQ, projQ, AggQueryIn.noMention_castKind]; exact noMention_ltQ' h

/-- **The rows with no row below them.** -/
private theorem mem_leastQ (s₁ s₂ : String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (h₁ : R.noMention s₁) (h₂ : R.noMention s₂) (hR : NonNullRows R D γ) (x : Tuple T p) :
    Multiset.Mem ((leastQ s₁ s₂ cnt R).evaluatePlain D γ) x ↔ Multiset.Mem (R.evaluatePlain D γ) x
      ∧ ∀ a, Multiset.Mem (R.evaluatePlain D γ) a → ¬ ascLt p a x := by
  rw [leastQ, AggQueryIn.evaluatePlain_notInDiffX s₁ s₂ cnt hc _ _ h₁ (noMention_aboveQ' h₂) D γ]
  show x ∈ Multiset.filter _ _ ↔ _
  rw [Multiset.mem_filter]
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun a ha hlt => hn ((mem_aboveQ hR x).mpr ⟨hx, a, ha, hlt⟩)⟩
  · rintro ⟨hx, hn⟩
    refine ⟨hx, fun hm => ?_⟩
    obtain ⟨-, a, ha, hlt⟩ := (mem_aboveQ hR x).mp hm
    exact hn a ha hlt

/-- **The rows with no row above them.** -/
private theorem mem_greatestQ (s₁ s₂ : String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (h₁ : R.noMention s₁) (h₂ : R.noMention s₂) (hR : NonNullRows R D γ) (x : Tuple T p) :
    Multiset.Mem ((greatestQ s₁ s₂ cnt R).evaluatePlain D γ) x ↔ Multiset.Mem (R.evaluatePlain D
      γ) x
      ∧ ∀ b, Multiset.Mem (R.evaluatePlain D γ) b → ¬ ascLt p x b := by
  rw [greatestQ, AggQueryIn.evaluatePlain_notInDiffX s₁ s₂ cnt hc _ _ h₁ (noMention_belowQ' h₂) D γ]
  show x ∈ Multiset.filter _ _ ↔ _
  rw [Multiset.mem_filter]
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun b hb hlt => hn ((mem_belowQ hR x).mpr ⟨hx, b, hb, hlt⟩)⟩
  · rintro ⟨hx, hn⟩
    refine ⟨hx, fun hm => ?_⟩
    obtain ⟨-, b, hb, hlt⟩ := (mem_belowQ hR x).mp hm
    exact hn b hb hlt

private theorem nodup_leastQ (s₁ s₂ : String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (h₁ : R.noMention s₁) (h₂ : R.noMention s₂)
    (hnd : (R.evaluatePlain D γ : Multiset (Tuple T p)).Nodup) :
    ((leastQ s₁ s₂ cnt R).evaluatePlain D γ : Multiset (Tuple T p)).Nodup := by
  rw [leastQ, AggQueryIn.evaluatePlain_notInDiffX s₁ s₂ cnt hc _ _ h₁ (noMention_aboveQ' h₂) D γ]
  exact Multiset.Nodup.filter _ hnd

private theorem nodup_greatestQ (s₁ s₂ : String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (h₁ : R.noMention s₁) (h₂ : R.noMention s₂)
    (hnd : (R.evaluatePlain D γ : Multiset (Tuple T p)).Nodup) :
    ((greatestQ s₁ s₂ cnt R).evaluatePlain D γ : Multiset (Tuple T p)).Nodup := by
  rw [greatestQ, AggQueryIn.evaluatePlain_notInDiffX s₁ s₂ cnt hc _ _ h₁ (noMention_belowQ' h₂) D γ]
  exact Multiset.Nodup.filter _ hnd

/-- **The least row is the first of the sorted listing.** -/
theorem evaluatePlain_leastQ (s₁ s₂ : String) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (h₁ : R.noMention s₁) (h₂ : R.noMention s₂) (hR : NonNullRows R D γ)
    (hnd : (R.evaluatePlain D γ : Multiset (Tuple T p)).Nodup)
    (h0 : 0 < (sortedRows (R.evaluatePlain D γ : Multiset (Tuple T p))).length) :
    @Eq (Multiset (Tuple T p)) ((leastQ s₁ s₂ cnt R).evaluatePlain D γ)
      {(sortedRows (R.evaluatePlain D γ : Multiset (Tuple T p)))[0]} := by
  set L := sortedRows (R.evaluatePlain D γ : Multiset (Tuple T p)) with hL
  have hpw := pairwise_sortedRows (R.evaluatePlain D γ : Multiset (Tuple T p))
  rw [← hL] at hpw
  refine (Multiset.Nodup.ext (nodup_leastQ s₁ s₂ hc h₁ h₂ hnd) (Multiset.nodup_singleton _)).mpr
    fun x => ?_
  rw [Multiset.mem_singleton]
  refine (mem_leastQ s₁ s₂ hc h₁ h₂ hR x).trans ⟨fun ⟨hx, hn⟩ => ?_, fun hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (mem_sortedRows.mpr hx : x ∈ L)
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rfl
    · exact absurd (List.pairwise_iff_getElem.mp hpw 0 i h0 hi hpos)
        (hn _ (mem_sortedRows.mp (List.getElem_mem h0)))
  · subst hx
    refine ⟨mem_sortedRows.mp (List.getElem_mem h0), fun a ha hlt => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (mem_sortedRows.mpr ha : a ∈ L)
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ascLt_irrefl _ hlt
    · exact ascLt_irrefl _ (ascLt_trans _ _ _ hlt (List.pairwise_iff_getElem.mp hpw 0 i h0 hi hpos))

end OrderQueries

end Sym
