/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQuery

/-!
# Determinacy: the listing an aggregate reads, and the query that is refused

An aggregate reads its group – or a window's frame – as a *sequence*,
and the clause only partly fixes that sequence: rows the clause leaves
tied may be listed either way. A query is admitted only where the
listing cannot matter: each aggregate
is symmetric, or any two rows its clause ties carry equal values of the
term it aggregates. That condition is about the rows, so it is a
judgment about the query *and* the instance, and a query that fails it
is refused rather than given a value.

This module says all three things in Lean.

* **The listing is invisible where the condition holds.**
  `ValueFrame.windowValue_eq_of_listing` and
  `Relation.groupSeqOrd_map_eq_of_listing`: any listing of the frame or
  of the group in the clause's order reads as the evaluator's listing
  does. Both rest on `List.map_eq_of_pairwise_of_symm` – two sorted
  listings of one bag read alike, for a reading that cannot tell two
  mutually-comparable elements apart – and on
  `OrderSpec.peer_of_readLe`, which says that mutual comparability under
  the library's reading *is* peerhood of the clause.
* **The condition itself**, `AggQueryIn.DeterminateOn q D γ`: at each
  aggregation and each window of `q`, either the aggregate reads its
  input as a bag (`SeqAggFunc.Symmetric`) or the term is constant on the
  rows the clause ties (`Relation.rowsAgree`). It is quantified over the
  instance, in the manner of `AggQueryIn.recSettles`, and at an apply it
  follows the rows the left side offers.
* **The evaluator that refuses**, `AggQueryIn.evaluateChecked`: the plain
  answer where the condition holds, and `none` where it does not.
  `AggQueryIn.windowValue_eq_of_listing_of_determinateOn` and
  `gammaAgg_eq_of_listing_of_determinateOn` are what its `some` means at
  the two operators that read an order.

What this module does **not** do is change `AggQueryIn.evaluatePlain`,
which keeps its own listing – the clause's order with ties broken by the
row. That listing is one the condition admits, and every result of the
metatheory relates two readings of *one* listing, so no theorem needs
determinacy: the hom commutation, the random world, the rewriting and
the adequacy hold on every instance, determinate or not. Determinacy is
what a *second* listing asks for, which is why it is the hypothesis the
re-typing of `Provenance.AllRegular` carries at a window: erasing a
column's tag lets it into the tie-break, and
`ValueFrame.windowValueOpt_readTuple_of_det` is where `rowsAgree` and
`OrderSpec.map_eq_of_keySorted` are put to work.
-/

variable {T : Type} [ValueType T] {n m p : ℕ}

private theorem replicate_cons_comm {γ : Type} (k : ℕ) (a : γ) (L : List γ) :
    a :: (List.replicate k a ++ L) = List.replicate k a ++ a :: L := by
  rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ',
    List.append_assoc]
  rfl

/-- **Two sorted listings of one bag read alike**, for a reading that
cannot tell two mutually-comparable elements of the bag apart. -/
theorem List.map_eq_of_pairwise_of_symm {α γ : Type} {R : α → α → Prop}
    {q : α → γ} {S : α → Prop}
    (hq : ∀ x y, S x → S y → R x y → R y x → q x = q y) :
    ∀ (L L' : List α), (∀ x ∈ L, S x) → L.Perm L' → L.Pairwise R →
      L'.Pairwise R → L.map q = L'.map q
  | [], L', _, hp, _, _ => by
    rw [List.Perm.nil_eq hp]
  | x :: t, L', hS, hp, hL, hL' => by
    have hx : x ∈ L' := hp.mem_iff.mp (List.mem_cons_self)
    obtain ⟨pr, s, rfl⟩ := List.append_of_mem hx
    have hts : t.Perm (pr ++ s) := (hp.trans List.perm_middle).cons_inv
    have hps : (pr ++ s).Pairwise R :=
      hL'.sublist ((List.Sublist.refl pr).append (List.sublist_cons_self x s))
    have hconst : ∀ y ∈ pr, q y = q x := by
      intro y hy
      have hyt : y ∈ t := hts.mem_iff.mpr (List.mem_append_left s hy)
      exact hq y x (hS y (List.mem_cons_of_mem x hyt)) (hS x List.mem_cons_self)
        ((List.pairwise_append.mp hL').2.2 y hy x List.mem_cons_self)
        ((List.pairwise_cons.mp hL).1 y hyt)
    have hrep : pr.map q = List.replicate pr.length (q x) := by
      rw [show pr.length = (pr.map q).length from (List.length_map q).symm]
      exact List.eq_replicate_of_mem (fun b hb => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        exact hconst y hy)
    rw [List.map_cons, map_eq_of_pairwise_of_symm hq t (pr ++ s)
      (fun y hy => hS y (List.mem_cons_of_mem x hy)) hts
      (List.pairwise_cons.mp hL).2 hps, List.map_append, List.map_append,
      List.map_cons, hrep, replicate_cons_comm]

/-- **Mutual comparability is peerhood**: the clause's reading breaks a
tie by the row, so two occurrences each of which it puts first are peers
of the clause. -/
theorem OrderSpec.peer_of_readLe {α β : Type} [LinearOrder β] {key : β → Tuple T p}
    {val : α → β} {o : OrderSpec p} {x y : α}
    (h₁ : OrderSpec.readLe key val o x y = true)
    (h₂ : OrderSpec.readLe key val o y x = true) :
    o.peer (key (val x)) (key (val y)) = true := by
  by_cases hp : o.peer (key (val x)) (key (val y)) = true
  · exact hp
  · rw [OrderSpec.readLe, ite_eq_right hp] at h₁
    rw [OrderSpec.readLe, ite_eq_right (fun hc => hp (by
      rw [OrderSpec.peer, Bool.and_eq_true] at hc ⊢
      exact ⟨hc.2, hc.1⟩)) ] at h₂
    exact absurd (by rw [OrderSpec.peer, Bool.and_eq_true]; exact ⟨h₁, h₂⟩) hp

/-- Every row of a frame is a row of the relation. -/
theorem ValueFrame.mem_of_mem_frameOf {α : Type} [LinearOrder α]
    (val : α → Tuple T n) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (X : Multiset α) {x : α} (hx : x ∈ X) {y : α}
    (hy : y ∈ ValueFrame.frameOf val P O w X x) : y ∈ X := by
  unfold ValueFrame.frameOf at hy
  by_cases hs : w.s (Tuple.key O (val x)) = true
  · rw [ite_eq_left hs] at hy
    rcases Multiset.mem_cons.mp hy with rfl | hy'
    · exact hx
    · exact Multiset.mem_filter.mp (Multiset.mem_of_mem_erase hy') |>.1
  · rw [ite_eq_right hs] at hy
    exact Multiset.mem_filter.mp (Multiset.mem_of_mem_erase hy) |>.1

/-- **Any listing of a frame in the clause's order gives the window's
value**, where the aggregated term cannot tell two peers of the clause
apart: the evaluator's listing is one of them, so the value it computes
is the value every admissible listing computes. -/
theorem ValueFrame.windowValue_eq_of_listing {c : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (R : Multiset (Tuple T n))
    {u : Tuple T n} (hu : u ∈ R) (γ : Fin c → T)
    (hdet : ∀ y z : Tuple T n, y ∈ R → z ∈ R →
      o.peer (Tuple.key O y) (Tuple.key O z) = true → t.eval y γ = t.eval z γ)
    (L : List (Tuple T n))
    (hL : (↑L : Multiset (Tuple T n))
      = ValueFrame.frameOf (α := Tuple T n) id P O w R u)
    (hsorted : L.Pairwise (fun y z =>
      OrderSpec.readLe (Tuple.key O) (id : Tuple T n → Tuple T n) o y z = true)) :
    f (L.map (fun v => t.eval v γ))
      = ValueFrame.windowValue P O o w t f R u γ := by
  unfold ValueFrame.windowValue
  refine congrArg f ?_
  refine List.map_eq_of_pairwise_of_symm
    (S := fun y : Tuple T n => y ∈ R)
    (fun y z hyR hzR h₁ h₂ => hdet y z hyR hzR
      (OrderSpec.peer_of_readLe h₁ h₂)) L _ ?_ ?_ hsorted
    (OrderSpec.sortSeq_sorted _)
  · intro y hy
    exact ValueFrame.mem_of_mem_frameOf (α := Tuple T n) id P O w R hu
      (hL ▸ (Multiset.mem_coe.mpr hy))
  · refine Multiset.coe_eq_coe.mp ?_
    rw [hL, ValueFrame.frameListOf_coe]

/-- **Which rows a grouping's `ORDER BY` leaves tied**: with no clause,
all of them – an order-dependent aggregate then reads a sequence the
clause does not fix at all, so its term has to be constant on the
group. -/
def GroupOrder.peers {k : ℕ} (ord : GroupOrder T k) (y z : Tuple T k) : Bool :=
  match ord with
  | .unord => true
  | .byCols cols spec => spec.peer (Tuple.key cols y) (Tuple.key cols z)

/-- **A listing of a group in the clause's order.** -/
def GroupOrder.SortedBy {k : ℕ} (ord : GroupOrder T k)
    (L : List (Tuple T k)) : Prop :=
  match ord with
  | .unord => True
  | .byCols cols spec =>
      L.Pairwise (fun y z => OrderSpec.readLe (Tuple.key cols)
        (id : Tuple T k → Tuple T k) spec y z = true)

/-- **Any listing of a group in the clause's order reads as the
evaluator's does**, where the term cannot tell two rows the clause
leaves tied apart. -/
theorem Relation.groupSeqOrd_map_eq_of_listing {k n₁ : ℕ} {γ' : Type}
    (is : Tuple (Fin k) n₁) (ord : GroupOrder T k)
    (r : Multiset (Tuple T k)) (g : Tuple T n₁) (read : Tuple T k → γ')
    (hdet : ∀ y z : Tuple T k, y ∈ r → z ∈ r → ord.peers y z = true →
      read y = read z)
    (L : List (Tuple T k)) (hperm : L.Perm (Relation.groupSeq is r g))
    (hsorted : ord.SortedBy L) :
    L.map read = (Relation.groupSeqOrd is ord r g).map read := by
  have hmem : ∀ y ∈ Relation.groupSeq is r g, y ∈ r := by
    intro y hy
    rw [Relation.groupSeq, ← Multiset.mem_coe, sortList_coe] at hy
    exact (Multiset.mem_filter.mp hy).1
  cases ord with
  | unord =>
    -- the clause separates nothing, so the term is constant on the group
    have hall : ∀ y ∈ L, ∀ z ∈ L, read y = read z := fun y hy z hz =>
      hdet y z (hmem y (hperm.mem_iff.mp hy)) (hmem z (hperm.mem_iff.mp hz)) rfl
    cases L with
    | nil => exact congrArg (List.map read) (List.Perm.nil_eq hperm)
    | cons x t =>
      have hconstL : ∀ b ∈ (x :: t).map read, b = read x := by
        intro b hb
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        exact hall y hy x List.mem_cons_self
      have hconstG : ∀ b ∈ (Relation.groupSeq is r g).map read, b = read x := by
        intro b hb
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        exact hall y (hperm.mem_iff.mpr hy) x List.mem_cons_self
      rw [show Relation.groupSeqOrd is GroupOrder.unord r g
          = Relation.groupSeq is r g from rfl]
      rw [List.eq_replicate_of_mem hconstL, List.eq_replicate_of_mem hconstG,
        show ((x :: t).map read).length
            = ((Relation.groupSeq is r g).map read).length from by
          rw [List.length_map, List.length_map, hperm.length_eq]]
  | byCols cols spec =>
    exact List.map_eq_of_pairwise_of_symm
      (S := fun y : Tuple T k => y ∈ r)
      (fun y z hyr hzr h₁ h₂ => hdet y z hyr hzr
        (show spec.peer (Tuple.key cols y) (Tuple.key cols z) = true from
          OrderSpec.peer_of_readLe h₁ h₂))
      L _ (fun y hy => hmem y (hperm.mem_iff.mp hy))
      (hperm.trans (OrderSpec.sortSeq_perm _).symm) hsorted
      (OrderSpec.sortSeq_sorted _)

/-- **What a window reads of its input**: its rows with the aggregate
columns nulled, which is the listing the clause orders. -/
noncomputable def AggQueryIn.readRows {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T) :
    Multiset (Tuple T n) :=
  (q.evaluatePlain D γ : Multiset (Tuple T n)).map (ColKind.readTuple κ)

/-- **A reading that cannot tell two tied rows of a relation apart.** -/
def Relation.rowsAgree {k : ℕ} (r : Multiset (Tuple T k))
    (tie : Tuple T k → Tuple T k → Bool) (read : Tuple T k → T) : Prop :=
  ∀ y z : Tuple T k, y ∈ r → z ∈ r → tie y z = true → read y = read z

/-- Every row of a relation satisfies a property. -/
def Relation.allRows {k : ℕ} (r : Multiset (Tuple T k))
    (Q : Tuple T k → Prop) : Prop :=
  ∀ u : Tuple T k, u ∈ r → Q u

/-- **The query's aggregates cannot tell their listings apart, on this
instance**: at each aggregation and each window, either the aggregate
reads its input as a bag, or the term it aggregates is constant on the
rows the clause leaves tied. This is the condition under which a query
is admitted – a condition on the rows, so a judgment about
the query *and* the instance, which is why it is quantified here and not
read off the syntax. -/
def AggQueryIn.DeterminateOn : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Database T → (Fin c → T) → Prop
  | _, _, _, _, .Rel _ _, _, _ => True
  | _, _, _, _, .Hole _ _ _, _, _ => True
  | _, _, _, _, .Param _ _, _, _ => True
  | _, _, _, _, .Empty, _, _ => True
  | _, _, _, _, .Proj _ q, D, γ => q.DeterminateOn D γ
  | _, _, _, _, .Sel _ q _, D, γ => q.DeterminateOn D γ
  | _, _, _, _, .Prod q₁ q₂, D, γ => q₁.DeterminateOn D γ ∧ q₂.DeterminateOn D γ
  | _, _, _, _, .Apply q₁ q₂, D, γ =>
      q₁.DeterminateOn D γ
        ∧ Relation.allRows (q₁.evaluatePlain D γ)
            (fun u => q₂.DeterminateOn D (Fin.append u γ))
  | _, _, _, _, .Sum q₁ q₂, D, γ => q₁.DeterminateOn D γ ∧ q₂.DeterminateOn D γ
  | _, _, _, _, .Dedup q, D, γ => q.DeterminateOn D γ
  | _, _, _, _, .Diff q₁ q₂, D, γ => q₁.DeterminateOn D γ ∧ q₂.DeterminateOn D γ
  | _, _, _, _, .Explode _ _ q, D, γ => q.DeterminateOn D γ
  | _, _, _, _, .Retag _ q, D, γ => q.DeterminateOn D γ
  | _, _, _, _, .Mu _ q₀ q₁, D, γ => q₀.DeterminateOn D γ ∧ q₁.DeterminateOn D γ
  | _, _, _, _, .MuSet _ q₀ q₁, D, γ =>
      q₀.DeterminateOn D γ ∧ q₁.DeterminateOn D γ
  | _, _, _, _, .Gamma _ ts fs q _ ord, D, γ =>
      (∀ j, (fs j).Symmetric
          ∨ Relation.rowsAgree (q.evaluatePlain D γ) ord.peers
              (fun y => (ts j).eval y γ))
        ∧ q.DeterminateOn D γ
  | _, _, _, _, .GammaScalar ts fs q ord, D, γ =>
      (∀ j, (fs j).Symmetric
          ∨ Relation.rowsAgree (q.evaluatePlain D γ) ord.peers
              (fun y => (ts j).eval y γ))
        ∧ q.DeterminateOn D γ
  | _, _, _, _, .GammaNest _ _ _ _ q, D, γ => q.DeterminateOn D γ
  | _, _, _, _, .GammaTok _ _ ts fs _ q _, D, γ =>
      (∀ j, (fs j).Symmetric
          ∨ Relation.rowsAgree (q.evaluatePlain D γ) (fun _ _ => true)
              (fun y => (ts j).eval y γ))
        ∧ q.DeterminateOn D γ
  | _, _, _, _, .ProvSum _ _ _ q, D, γ => q.DeterminateOn D γ
  | _, _, _, _, .Win _ O o _ t f q _ dist _, D, γ =>
      ((if dist then f.distinct else f).Symmetric
          ∨ Relation.rowsAgree (q.readRows D γ)
              (fun y z => o.peer (Tuple.key O y) (Tuple.key O z))
              (fun y => t.eval y γ))
        ∧ q.DeterminateOn D γ
  | _, _, _, _, .WinExpr _ O o _ ts fs _ q _, D, γ =>
      (∀ l, (fs l).Symmetric
          ∨ Relation.rowsAgree (q.evaluatePlain D γ)
              (fun y z => o.peer (Tuple.key O y) (Tuple.key O z))
              (fun y => (ts l).eval y γ))
        ∧ q.DeterminateOn D γ

open Classical in
/-- **The evaluator that refuses**: the plain answer where the query's
aggregates cannot tell their listings apart on this instance, and
nothing where one of them can. -/
noncomputable def AggQueryIn.evaluateChecked {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T) :
    Option (Relation T n) :=
  if q.DeterminateOn D γ then some (q.evaluatePlain D γ) else none

theorem AggQueryIn.evaluateChecked_eq_some {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T)
    (h : q.DeterminateOn D γ) :
    q.evaluateChecked D γ = some (q.evaluatePlain D γ) := by
  unfold AggQueryIn.evaluateChecked
  exact ite_eq_left h

theorem AggQueryIn.evaluateChecked_eq_none {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T)
    (h : ¬ q.DeterminateOn D γ) : q.evaluateChecked D γ = none := by
  unfold AggQueryIn.evaluateChecked
  exact ite_eq_right h

theorem AggQueryIn.evaluateChecked_isSome_iff {c n : ℕ} {κ : Fin n → ColKind} {l : List
    (String × ℕ)}
    (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T) :
    (q.evaluateChecked D γ).isSome = true ↔ q.DeterminateOn D γ := by
  by_cases h : q.DeterminateOn D γ
  · rw [AggQueryIn.evaluateChecked_eq_some q D γ h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [AggQueryIn.evaluateChecked_eq_none q D γ h]
    exact ⟨fun hc => absurd hc (by simp), fun hc => absurd hc h⟩

/-- **What the refusal buys at a window**: where the checked evaluator
answers, the column it computes is the value *every* listing of the
frame in the clause's order gives – so the listing the evaluator happens
to take decides nothing. -/
theorem AggQueryIn.windowValue_eq_of_listing_of_determinateOn {lab : ℕ} {c n m p : ℕ}
    {rd : Fin c → Bool}
    {κ : Fin n → ColKind} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) {hsql : w.IsSQL o} (t : TermIn T c n) (f : SeqAggFunc T)
    (q : AggQueryIn T c n κ) (hrr : WinReadsReg κ P O t) (dist : Bool)
    (keep : Option (Selection T n)) (D : Database T) (γ : Fin c → T)
    (hdet : (AggQueryIn.Win (hsql := sql_frame%) (lab := lab) (rd := rd) P O o w t f q hrr dist
      keep).DeterminateOn D γ)
    {u : Tuple T n} (hu : u ∈ q.readRows D γ) (L : List (Tuple T n))
    (hL : (↑L : Multiset (Tuple T n))
      = ValueFrame.frameOf (α := Tuple T n) id P O w (q.readRows D γ) u)
    (hsorted : L.Pairwise (fun y z =>
      OrderSpec.readLe (Tuple.key O) (id : Tuple T n → Tuple T n) o y z = true)) :
    (if dist then f.distinct else f) (L.map (fun v => t.eval v γ))
      = ValueFrame.windowValue P O o w t (if dist then f.distinct else f)
          (q.readRows D γ) u γ := by
  rcases hdet.1 with hsym | hpeer
  · exact ValueFrame.windowValue_of_perm P O o w t hsym _ u L hL
  · exact ValueFrame.windowValue_eq_of_listing P O o w t _ (q.readRows D γ) hu γ
      hpeer L hL hsorted

/-- **And at a grouping**: the aggregate's value on any listing of the
group in the clause's order is the one the evaluator computes. -/
theorem AggQueryIn.gammaAgg_eq_of_listing_of_determinateOn {lab : ℕ} {c k n₁ n₂ : ℕ}
    {rd : Fin c → Bool}
    (is : Tuple (Fin k) n₁) (ts : Tuple (TermIn T c k) n₂)
    (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c k (ColKind.allReg k))
    (keep : Fin n₂ → Option (Selection T k)) (ord : GroupOrder T k)
    (D : Database T) (γ : Fin c → T)
    (hdet : (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).DeterminateOn D γ)
    (j : Fin n₂) (g : Tuple T n₁) (L : List (Tuple T k))
    (hperm : L.Perm (Relation.groupSeq is (q.evaluatePlain D γ) g))
    (hsorted : ord.SortedBy L) :
    (fs j) (L.map (fun v => (ts j).eval v γ))
      = (fs j) ((Relation.groupSeqOrd is ord (q.evaluatePlain D γ) g).map
          (fun v => (ts j).eval v γ)) := by
  rcases hdet.1 j with hsym | hagree
  · exact hsym ((hperm.trans (Relation.groupSeqOrd_perm is ord _ g).symm).map _)
  · exact congrArg (fs j) (Relation.groupSeqOrd_map_eq_of_listing is ord _ g _
      hagree L hperm hsorted)

/-! ## Listings that agree only on the clause

A re-typing, or any other change of what breaks a tie, leaves a listing
sorted by the clause's *keys* and reorders it inside a block of peers.
That is weaker than `OrderSpec.readLe`-sortedness and it is all the
invariance needs. -/

/-- The clause's reading puts an occurrence before another only where the
clause itself does. -/
theorem OrderSpec.le_of_readLe {α β : Type} [LinearOrder β]
    {key : β → Tuple T p} {val : α → β} {o : OrderSpec p} {x y : α}
    (h : OrderSpec.readLe key val o x y = true) :
    o.le (key (val x)) (key (val y)) = true := by
  by_cases hp : o.peer (key (val x)) (key (val y)) = true
  · rw [OrderSpec.peer, Bool.and_eq_true] at hp
    exact hp.1
  · rw [OrderSpec.readLe, ite_eq_right hp] at h
    exact h

/-- **Two listings of one bag sorted by the clause's keys read alike**,
for a reading that is constant on the clause's peers. This is the
invariance a change of tie-break asks for: the blocks of peers come in
the order the clause fixes, and inside a block the reading does not
look. -/
theorem OrderSpec.map_eq_of_keySorted {α γ : Type} (key : α → Tuple T p)
    (o : OrderSpec p) (q : α → γ) {S : α → Prop}
    (hq : ∀ x y, S x → S y → o.peer (key x) (key y) = true → q x = q y)
    (L L' : List α) (hS : ∀ x ∈ L, S x) (hperm : L.Perm L')
    (hL : L.Pairwise (fun x y => o.le (key x) (key y) = true))
    (hL' : L'.Pairwise (fun x y => o.le (key x) (key y) = true)) :
    L.map q = L'.map q :=
  List.map_eq_of_pairwise_of_symm
    (fun x y hx hy h₁ h₂ => hq x y hx hy
      (by rw [OrderSpec.peer, Bool.and_eq_true]; exact ⟨h₁, h₂⟩))
    L L' hS hperm hL hL'
