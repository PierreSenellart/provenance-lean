module

public import Provenance.Genericity

/-!
# `μ^∪` from `μ^⊎`

A set recursion `μ^∪R.(q₀, q₁)` whose recursive term is `L(R) ⊎ C`, with
`L` reading `R` once under a projection, a selection, a product, the left
side of an apply (and nothing else), is simulated by a bag recursion
over pairs of a tuple and a *counter*: the base is `(q₀ ⊎ C) × E^K` for a
relation `E` of counters, and a round applies `L` to the tuple part of
every row and moves its counter to every strictly larger one (in the
lexicographic order of `E^K`). A row's counters then form a strictly
increasing chain, so the bag recursion ends after `|E|^K` rounds – it
always settles – and its rounds carry, as sets, the rounds of the set
recursion, which reach the fixpoint within `|F|` rounds, `F` the
fixpoint. So `ε(Π_tuple(S)) = F` as soon as `|E|^K ≥ |F|`
(`AggQueryIn.evaluatePlain_simResult`).

This module has the construction and its correctness for *any* counter
relation `E` of non-null values that is large enough. What `E` can be
read off the query is the other half: the values of the instance at the
recursion's leaves, its constants and the context, with two constants of
the domain (`counterRel`), and a width `K` fixed by the query. A count
inside the term takes values that no such set enumerates, which is where
the *order-type* lemma enters: the fixpoint is duplicate-free
over those values and the counts the recursion computes, of which there
are polynomially many (`AggQueryIn.exists_card_bound_muSet` in
`Provenance.Genericity`), so `|F| ≤ |E|^K` for a `K` read off that
polynomial.
-/

@[expose] public section

variable {T : Type} [ValueType T]

/-! ## Linear recursive terms

The typing of a recursive term admits the recursive relation under a
`⊎`, with the other side
closed; the simulation needs the term without that side – which is the
`q₁'` half of the split the generation pass produces – and reading the
relation at a fixed arity. -/

/-- **A term reading the recursive relation `s` once, at arity `n`, and
linearly**: under a projection, a selection on regular columns, either
side of a product or the left side of an apply, with the other side
closed. No `⊎`: its closed side is the `C` of `q₁ = L ⊎ C`. -/
def AggQueryIn.recLinear (s : String) (n : ℕ) : {c m : ℕ} → {κ : Fin m → ColKind} →
    {l : List (String × ℕ)} → AggQueryIn T c m κ l → Prop
  | _, _, _, _, .Rel _ _ => False
  | _, _, _, _, .Hole n' s' _ => s' = s ∧ n' = n
  | _, _, _, _, .Param _ _ => False
  | _, _, _, _, .Empty => False
  | _, _, _, _, .Proj _ q => q.recLinear s n
  | _, _, _, _, .Sel φ q _ => φ.hasAggAtom = false ∧ q.recLinear s n
  | _, _, _, _, @AggQueryIn.Prod _ _ _ _ _ _ l₁ l₂ q₁ q₂ =>
      (q₁.recLinear s n ∧ l₂ = [] ∧ q₂.noMention s)
        ∨ (l₁ = [] ∧ q₁.noMention s ∧ q₂.recLinear s n)
  | _, _, _, _, .Apply q₁ q₂ => q₁.recLinear s n ∧ q₂.noMention s
  | _, _, _, _, .Sum _ _ => False
  | _, _, _, _, .Explode _ _ q => q.recLinear s n
  | _, _, _, _, .Retag _ q => q.recLinear s n
  | _, _, _, _, .Dedup _ => False
  | _, _, _, _, .Diff _ _ => False
  | _, _, _, _, .Mu _ _ _ => False
  | _, _, _, _, .MuSet _ _ _ => False
  | _, _, _, _, .Gamma _ _ _ _ _ _ => False
  | _, _, _, _, .GammaScalar _ _ _ _ => False
  | _, _, _, _, .GammaNest _ _ _ _ _ => False
  | _, _, _, _, .ProvSum _ _ _ _ => False
  | _, _, _, _, .GammaTok _ _ _ _ _ _ _ => False
  | _, _, _, _, .Win _ _ _ _ _ _ _ _ _ _ => False
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => False

omit [ValueType T] in
/-- A linear term's one hole is the recursive relation, at its arity. -/
theorem AggQueryIn.index_of_recLinear {s : String} {n : ℕ} :
    ∀ {c m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
      q.recLinear s n → l = [(s, n)] := by
  intro c m κ l q
  induction q with
  | Rel n s' => exact fun h => h.elim
  | Hole n s' => exact fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact fun h => ih h.2
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, -⟩ | ⟨rfl, -, h₂⟩)
    · rw [ih₁ h₁]; rfl
    · exact ih₂ h₂
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ih₁ h.1
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact ih
  | Retag hk q ih => exact ih
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

/-- **A linear term reads the relation row by row**: its value at `X` is
the sum, over the rows of `X`, of its values at each row alone. -/
theorem AggQueryIn.evaluatePlain_assign_bind_of_recLinear {s : String} {n : ℕ} :
    ∀ {c m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      ∀ (D : Database T) (γ : Fin c → T) (X : Relation T n),
        (q.evaluatePlain (D.assign s X) γ : Multiset (Tuple T m))
          = X.bind (fun t => q.evaluatePlain (D.assign s ({t} : Multiset (Tuple T n))) γ) := by
  intro c m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' =>
    rintro ⟨rfl, rfl⟩ D γ X
    simp only [AggQueryIn.evaluatePlain, Database.find_assign]
    exact (Eq.trans (Multiset.bind_singleton X id) (Multiset.map_id' X)).symm
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih =>
    intro h D γ X
    simp only [AggQueryIn.evaluatePlain]
    rw [ih h D γ X, Multiset.map_bind]
  | Sel φ q _ ih =>
    intro h D γ X
    simp only [AggQueryIn.evaluatePlain]
    rw [ih h.2 D γ X, Multiset.filter_bind]
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) D γ X
    · simp only [AggQueryIn.evaluatePlain]
      rw [ih₁ h₁ D γ X, Relation.hMul_eq_bind, Multiset.bind_assoc]
      refine Multiset.bind_congr fun t _ => ?_
      rw [Relation.hMul_eq_bind, AggQueryIn.evaluatePlain_assign_of_noMention X q₂ h₂,
        AggQueryIn.evaluatePlain_assign_of_noMention ({t} : Multiset (Tuple T n)) q₂ h₂]
    · simp only [AggQueryIn.evaluatePlain]
      rw [ih₂ h₂ D γ X, Relation.hMul_eq_bind,
        AggQueryIn.evaluatePlain_assign_of_noMention X q₁ h₁]
      simp only [Multiset.map_bind]
      rw [Multiset.bind_bind]
      refine Multiset.bind_congr fun t _ => ?_
      rw [AggQueryIn.evaluatePlain_assign_of_noMention ({t} : Multiset (Tuple T n)) q₁ h₁,
        Relation.hMul_eq_bind]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h D γ X
    simp only [AggQueryIn.evaluatePlain]
    rw [ih₁ h.1 D γ X, Multiset.bind_assoc]
    refine Multiset.bind_congr fun t _ => Multiset.bind_congr fun u _ => ?_
    rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₂ h.2,
      AggQueryIn.evaluatePlain_assign_of_noMention ({t} : Multiset (Tuple T n)) q₂ h.2]
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h D γ X => ih h D γ X
  | Retag hk q ih => exact fun h D γ X => ih h D γ X
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

/-- Hence it grows with its argument, as a set. -/
theorem AggQueryIn.mem_evaluatePlain_assign_of_subset {s : String} {n : ℕ} {c m : ℕ}
    {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l)
        (hq : q.recLinear s n) (D : Database T)
    (γ : Fin c → T) {X X' : Relation T n} (hXX : ∀ t, Multiset.Mem X t → Multiset.Mem X' t)
    (u : Tuple T m) (hu : Multiset.Mem (q.evaluatePlain (D.assign s X) γ) u) :
    Multiset.Mem (q.evaluatePlain (D.assign s X') γ) u := by
  have h := AggQueryIn.evaluatePlain_assign_bind_of_recLinear q hq D γ
  have hu' : u ∈ X.bind (fun t => q.evaluatePlain (D.assign s ({t} : Multiset (Tuple T n))) γ) := by
    rw [← h X]; exact hu
  rw [h X']
  obtain ⟨t, ht, hut⟩ := Multiset.mem_bind.mp hu'
  exact Multiset.mem_bind.mpr ⟨t, hXX t ht, hut⟩

/-! ## The rounds of a set recursion reach its fixpoint within its size -/

section SetFix

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
/-- The rounds of a set recursion whose step grows with its argument are
nested. -/
theorem muIter_subset_succ_of_mono (step : Multiset α → Multiset α)
    (hmono : ∀ X Y : Multiset α, X ⊆ Y → step X ⊆ step Y) :
    ∀ j, muIter step j ⊆ muIter step (j + 1)
  | 0 => fun x hx => absurd hx (Multiset.notMem_zero x)
  | j + 1 => by
    show step (muIter step j) ⊆ step (muIter step (j + 1))
    exact hmono _ _ (muIter_subset_succ_of_mono step hmono j)

omit [DecidableEq α] in
theorem muIter_subset_of_le (step : Multiset α → Multiset α)
    (hmono : ∀ X Y : Multiset α, X ⊆ Y → step X ⊆ step Y) {i j : ℕ} (h : i ≤ j) :
    muIter step i ⊆ muIter step j := by
  induction h with
  | refl => exact Multiset.Subset.refl _
  | step h ih => exact Multiset.Subset.trans ih (muIter_subset_succ_of_mono step hmono _)

/-- **The fixpoint is reached within its own size**: a round that is not
yet the fixpoint adds a tuple. -/
theorem muFixIdx_le_card_of_mono (f : Multiset α → Multiset α)
    (hmono : ∀ X Y : Multiset α, X ⊆ Y → f X ⊆ f Y) :
    muFixIdx (fun X => (f X).dedup) ≤ Multiset.card (muFix (fun X => (f X).dedup)) := by
  set step : Multiset α → Multiset α := fun X => (f X).dedup with hstep
  have hmono' : ∀ X Y : Multiset α, X ⊆ Y → step X ⊆ step Y := fun X Y h x hx =>
    Multiset.mem_dedup.mpr (hmono X Y h (Multiset.mem_dedup.mp hx))
  have hnd : ∀ j, (muIter step j).Nodup := fun j => by
    rw [muIter_eq_iterate]; exact nodup_iterate_dedup f j
  -- before the fixpoint index, round `j` has at least `j` tuples
  have hcard : ∀ j, j ≤ muFixIdx step → j ≤ Multiset.card (muIter step j) := by
    intro j
    induction j with
    | zero => exact fun _ => Nat.zero_le _
    | succ j ih =>
      intro hj
      have hne : muIter step (j + 1) ≠ muIter step j := by
        have hnot : j ∉ {i | step^[i + 1] 0 = step^[i] 0} :=
          Nat.notMem_of_lt_sInf (Nat.lt_of_succ_le hj)
        intro heq
        apply hnot
        show step^[j + 1] 0 = step^[j] 0
        rw [← muIter_eq_iterate, ← muIter_eq_iterate]
        exact heq
      have hlt : muIter step j < muIter step (j + 1) :=
        lt_of_le_of_ne ((Multiset.le_iff_subset (hnd j)).mpr
          (muIter_subset_succ_of_mono step hmono' j)) (Ne.symm hne)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih (Nat.le_of_succ_le hj))
        (Multiset.card_lt_card hlt))
  exact hcard _ le_rfl

/-- **Every round past the size of the fixpoint is the fixpoint**, once
the recursion settles. -/
theorem muIter_eq_muFix_of_card_le (f : Multiset α → Multiset α)
    (hmono : ∀ X Y : Multiset α, X ⊆ Y → f X ⊆ f Y)
    (hs : MuSetSettles (fun X => (f X).dedup)) {N : ℕ}
    (hN : Multiset.card (muFix (fun X => (f X).dedup)) ≤ N) :
    muIter (fun X => (f X).dedup) N = muFix (fun X => (f X).dedup) := by
  set step : Multiset α → Multiset α := fun X => (f X).dedup with hstep
  have hfix : step (muIter step (muFixIdx step)) = muIter step (muFixIdx step) := by
    have hmem : step^[muFixIdx step + 1] 0 = step^[muFixIdx step] 0 := Nat.sInf_mem hs
    rw [muIter_eq_iterate]
    exact (Function.iterate_succ_apply' step _ 0).symm.trans hmem
  exact muIter_eq_of_le hfix (le_trans (muFixIdx_le_card_of_mono f hmono) hN)

end SetFix

/-! ## Counters: strictly increasing chains in a finite order -/

section Chains

variable {β : Type} [DecidableEq β] (r : β → β → Prop) [DecidableRel r] (Cb : Multiset β)

/-- The bag of counters a row can hold after `j` moves: the whole set at
first, then the counters strictly above a counter of the previous round. -/
def chainBag : ℕ → Multiset β
  | 0 => Cb
  | j + 1 => (chainBag j).bind (fun c => Cb.filter (fun c' => r c c'))

omit [DecidableEq β] in
/-- A counter of round `j` is the end of a strictly increasing chain of
`j + 1` counters. -/
theorem exists_chain_of_mem_chainBag (htrans : ∀ a b c, r a b → r b c → r a c) :
    ∀ (j : ℕ) (c : β), c ∈ chainBag r Cb j →
      ∃ l : List β, (l ++ [c]).Pairwise r ∧ l.length = j ∧ ∀ x ∈ l ++ [c], x ∈ Cb
  | 0, c, hc => ⟨[], by simp, rfl, fun x hx => by
      rw [List.nil_append, List.mem_singleton] at hx; rw [hx]; exact hc⟩
  | j + 1, c, hc => by
    obtain ⟨c', hc', hcc⟩ := Multiset.mem_bind.mp hc
    obtain ⟨hcC, hlt⟩ := Multiset.mem_filter.mp hcc
    obtain ⟨l, hl, hlen, hmem⟩ := exists_chain_of_mem_chainBag htrans j c' hc'
    refine ⟨l ++ [c'], ?_, by simp [hlen], fun x hx => ?_⟩
    · rw [List.pairwise_append]
      refine ⟨hl, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
      rw [List.mem_singleton] at hy
      rw [hy]
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact htrans x c' c
          ((List.pairwise_append.mp hl).2.2 x hx c' (List.mem_singleton_self c')) hlt
      · exact hlt
    · rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hmem x hx
      · exact hcC

omit [DecidableEq β] in
/-- A counter of any round is a counter. -/
theorem mem_of_mem_chainBag : ∀ (j : ℕ) (c : β), c ∈ chainBag r Cb j → c ∈ Cb
  | 0, c, hc => hc
  | j + 1, c, hc => by
    obtain ⟨c', _, hcc⟩ := Multiset.mem_bind.mp hc
    exact (Multiset.mem_filter.mp hcc).1

/-- So a round past the number of distinct counters holds none. -/
theorem chainBag_eq_zero_of_card_le [Std.Irrefl r] (htrans : ∀ a b c, r a b → r b c → r a c)
    {j : ℕ} (hj : Cb.toFinset.card ≤ j) : chainBag r Cb j = 0 := by
  by_contra hne
  obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨l, hl, hlen, hmem⟩ := exists_chain_of_mem_chainBag r Cb htrans j c hc
  have hnd : (l ++ [c]).Nodup := hl.nodup
  have hsub : (l ++ [c]).toFinset ⊆ Cb.toFinset := fun x hx =>
    Multiset.mem_toFinset.mpr (hmem x (List.mem_toFinset.mp hx))
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_append, hlen] at this
  simp at this
  omega

omit [DecidableEq β] in
/-- And a round before it holds the corresponding element of any chain
listing the counters: the `j`-th element of a strictly increasing listing
is a counter of round `j`. -/
theorem getElem_mem_chainBag (l : List β) (hl : l.Pairwise r) (hmem : ∀ x ∈ l, x ∈ Cb) :
    ∀ (j : ℕ) (hj : j < l.length), l[j] ∈ chainBag r Cb j
  | 0, hj => hmem _ (List.getElem_mem hj)
  | j + 1, hj => by
    show l[j + 1] ∈ (chainBag r Cb j).bind (fun c => Cb.filter (fun c' => r c c'))
    refine Multiset.mem_bind.mpr ⟨l[j], getElem_mem_chainBag l hl hmem j (Nat.lt_of_succ_lt hj),
      Multiset.mem_filter.mpr ⟨hmem _ (List.getElem_mem hj), ?_⟩⟩
    exact List.pairwise_iff_getElem.mp hl j (j + 1) (Nat.lt_of_succ_lt hj) hj (Nat.lt_succ_self j)

end Chains

/-! ## Replacing the recursive relation by a query -/

/-- The holes of a term, the recursive relation's taken out. -/
def subIdx (s : String) (n : ℕ) (l : List (String × ℕ)) : List (String × ℕ) :=
  l.filter (fun p => decide (p ≠ (s, n)))

omit [ValueType T] in
theorem subIdx_append (s : String) (n : ℕ) (l₁ l₂ : List (String × ℕ)) :
    subIdx s n (l₁ ++ l₂) = subIdx s n l₁ ++ subIdx s n l₂ :=
  List.filter_append l₁ l₂

omit [ValueType T] in
theorem subIdx_self (s : String) (n : ℕ) : subIdx s n [(s, n)] = [] := by
  simp [subIdx]

omit [ValueType T] in
theorem subIdx_single_ne {s s' : String} {n n' : ℕ} (h : ¬ (s' = s ∧ n' = n)) :
    subIdx s n [(s', n')] = [(s', n')] := by
  have : (s', n') ≠ (s, n) := fun hc => h ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩
  simp [subIdx, this]

/-- A term, its hole index rewritten. -/
def AggQueryIn.castIdx {c m : ℕ} {κ : Fin m → ColKind} {l l' : List (String × ℕ)} (h : l = l')
    (q : AggQueryIn T c m κ l) : AggQueryIn T c m κ l' := h ▸ q

omit [ValueType T] in
theorem AggQueryIn.castIdx_rfl {c m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (h : l = l)
    (q : AggQueryIn T c m κ l) : q.castIdx h = q := rfl

@[simp] theorem AggQueryIn.evaluatePlain_castIdx {c m : ℕ} {κ : Fin m → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c m κ l) (D : Database T)
    (γ : Fin c → T) : (q.castIdx h).evaluatePlain D γ = q.evaluatePlain D γ := by
  cases h; rfl

@[simp] theorem AggQueryIn.settlesAt_castIdx {c m : ℕ} {κ : Fin m → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c m κ l) (D : Database T)
    (γ : Fin c → T) : (q.castIdx h).SettlesAt D γ ↔ q.SettlesAt D γ := by
  cases h; exact Iff.rfl

omit [ValueType T] in
@[simp] theorem AggQueryIn.usesOnly_castIdx {S : Set OpKind} {c m : ℕ} {κ : Fin m → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c m κ l) :
    (q.castIdx h).usesOnly S ↔ q.usesOnly S := by
  cases h; exact Iff.rfl

omit [ValueType T] in
@[simp] theorem AggQueryIn.hygienic_castIdx {c m : ℕ} {κ : Fin m → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c m κ l) :
    (q.castIdx h).hygienic ↔ q.hygienic := by
  cases h; exact Iff.rfl

@[simp] theorem AggQueryIn.inSig_castIdx {Θ : Set (SeqAggFunc T)} {c m : ℕ} {κ : Fin m → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c m κ l) :
    (q.castIdx h).inSig Θ ↔ q.inSig Θ := by
  cases h; exact Iff.rfl

omit [ValueType T] in
@[simp] theorem AggQueryIn.sumsAllReg_castIdx {c m : ℕ} {κ : Fin m → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c m κ l) :
    (q.castIdx h).sumsAllReg ↔ q.sumsAllReg := by
  cases h; exact Iff.rfl

omit [ValueType T] in
@[simp] theorem AggQueryIn.overSchema_castIdx {sch : Schema} {c m : ℕ} {κ : Fin m → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c m κ l) :
    (q.castIdx h).overSchema sch ↔ q.overSchema sch := by
  cases h; exact Iff.rfl

omit [ValueType T] in
@[simp] theorem AggQueryIn.names_castIdx {c m : ℕ} {κ : Fin m → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c m κ l) :
    (q.castIdx h).names = q.names := by
  cases h; rfl

omit [ValueType T] in
@[simp] theorem AggQueryIn.noMention_castIdx {s : String} {c m : ℕ} {κ : Fin m → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c m κ l) :
    (q.castIdx h).noMention s ↔ q.noMention s := by
  cases h; exact Iff.rfl

omit [ValueType T] in
/-- Admissibility of a selection's predicate survives taking a hole out. -/
theorem SelOK.sub {s : String} {n : ℕ} {l : List (String × ℕ)} {c m : ℕ}
    {κ : Fin m → ColKind} {φ : GenPredIn T c κ} (hφ : SelOK l φ) : SelOK (subIdx s n l) φ := by
  cases hl : subIdx s n l with
  | nil => trivial
  | cons a t =>
    show φ.hasAggAtom = false
    cases l with
    | nil => simp [subIdx] at hl
    | cons b l => exact hφ

/-- **The recursive relation replaced by one row read off the context**:
every hole of its name and arity becomes the parameter leaf reading `pv`,
at the hole's own kinds, so the holes of the result are the term's with
that one taken out; nothing else is touched. -/
def AggQueryIn.substRel (s : String) {c n : ℕ} (pv : Fin n → T ⊕ Fin c) :
    {m : ℕ} → {κ : Fin m → ColKind} → {l : List (String × ℕ)} → AggQueryIn T c m κ l →
    AggQueryIn T c m κ (subIdx s n l)
  | _, _, _, .Hole n' s' κh =>
      if h : s' = s ∧ n' = n then
        AggQueryIn.castIdx (by rw [h.1, h.2, subIdx_self])
          (.Param (fun k => pv (Fin.cast h.2 k)) κh)
      else AggQueryIn.castIdx (subIdx_single_ne h).symm (.Hole n' s' κh)
  | _, _, _, .Param pv' ρ' => .Param pv' ρ'
  | _, _, _, .Proj ps q => .Proj ps (substRel s pv q)
  | _, _, _, .Sel φ q hφ => .Sel φ (substRel s pv q) (SelOK.sub hφ)
  | _, _, _, .Prod q₁ q₂ =>
      AggQueryIn.castIdx (subIdx_append s n _ _).symm (.Prod (substRel s pv q₁) (substRel s pv q₂))
  | _, _, _, .Apply q₁ q₂ => .Apply (substRel s pv q₁) q₂
  | _, _, _, .Sum q₁ q₂ =>
      AggQueryIn.castIdx (subIdx_append s n _ _).symm (.Sum (substRel s pv q₁) (substRel s pv q₂))
  | _, _, _, .Explode k hk q => .Explode k hk (substRel s pv q)
  | _, _, _, .Retag hk q => .Retag hk (substRel s pv q)
  | _, _, _, .Rel n' s' => .Rel n' s'
  | _, _, _, .Empty => .Empty
  | _, _, _, .Dedup q => .Dedup q
  | _, _, _, .Diff q₁ q₂ => .Diff q₁ q₂
  | _, _, _, .Mu s' q₀ q₁ => .Mu s' q₀ q₁
  | _, _, _, .MuSet s' q₀ q₁ => .MuSet s' q₀ q₁
  | _, _, _, .Gamma (lab := lab) (rd := rd) is ts fs q keep ord =>
      .Gamma (lab := lab) (rd := rd) is ts fs q keep ord
  | _, _, _, .GammaScalar (lab := lab) (rd := rd) ts fs q ord =>
      .GammaScalar (lab := lab) (rd := rd) ts fs q ord
  | _, _, _, .GammaNest (lab := lab) (rd := rd) is his p f q =>
      .GammaNest (lab := lab) (rd := rd) is his p f q
  | _, _, _, .ProvSum is his t q => .ProvSum is his t q
  | _, _, _, .GammaTok (lab := lab) (rd := rd) is his ts fs a q keep =>
      .GammaTok (lab := lab) (rd := rd) is his ts fs a q keep
  | _, _, _, .Win (lab := lab) (rd := rd) P O o w t f q hrr dist keep =>
      .Win (hsql := sql_frame%) (lab := lab) (rd := rd) P O o w t f q hrr dist keep
  | _, _, _, .WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q keeps =>
      .WinExpr (hsql := sql_frame%) (lab := lab) (rd := rd) P O o ws ts fs g q keeps

omit [ValueType T] in
/-- A closed query not mentioning the name is unchanged. -/
theorem AggQueryIn.substRel_of_noMention {s : String} {c n : ℕ}
    (pv : Fin n → T ⊕ Fin c) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} (q : AggQueryIn T c m κ), q.noMention s →
      AggQueryIn.substRel s pv q = q := by
  have key : ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
      l = [] → q.noMention s → HEq (AggQueryIn.substRel s pv q) q := by
    intro m κ l q
    induction q with
    | Rel n' s' => exact fun _ _ => HEq.rfl
    | Hole n' s' => exact fun h => absurd h (by simp)
    | Param pv ρ => exact fun _ _ => HEq.rfl
    | Proj ps q ih =>
      intro hl h
      subst hl
      rw [AggQueryIn.substRel, eq_of_heq (ih pv rfl h)]
    | Sel φ q _ ih =>
      intro hl h
      subst hl
      rw [AggQueryIn.substRel, eq_of_heq (ih pv rfl h)]
    | Prod q₁ q₂ ih₁ ih₂ =>
      intro hl h
      obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      subst hl₁ hl₂
      rw [AggQueryIn.substRel, eq_of_heq (ih₁ pv rfl h.1), eq_of_heq (ih₂ pv rfl h.2)]
      exact HEq.rfl
    | Apply q₁ q₂ ih₁ ih₂ =>
      intro hl h
      subst hl
      rw [AggQueryIn.substRel, eq_of_heq (ih₁ pv rfl h.1)]
    | Sum q₁ q₂ ih₁ ih₂ =>
      intro hl h
      obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      subst hl₁ hl₂
      rw [AggQueryIn.substRel, eq_of_heq (ih₁ pv rfl h.1), eq_of_heq (ih₂ pv rfl h.2)]
      exact HEq.rfl
    | Explode k hk q ih =>
      intro hl h
      subst hl
      rw [AggQueryIn.substRel, eq_of_heq (ih pv rfl h)]
    | Retag hk q ih =>
      intro hl h
      subst hl
      rw [AggQueryIn.substRel, eq_of_heq (ih pv rfl h)]
    | Empty => exact fun _ _ => HEq.rfl
    | Dedup q ih => exact fun _ _ => HEq.rfl
    | Diff q₁ q₂ ih₁ ih₂ => exact fun _ _ => HEq.rfl
    | Mu s' q₀ q₁ ih₀ ih₁ => exact fun _ _ => HEq.rfl
    | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun _ _ => HEq.rfl
    | Gamma is ts fs q keep ord ih => exact fun _ _ => HEq.rfl
    | GammaScalar ts fs q ord ih => exact fun _ _ => HEq.rfl
    | GammaNest is his p fn q ih => exact fun _ _ => HEq.rfl
    | ProvSum is his t q ih => exact fun _ _ => HEq.rfl
    | GammaTok is his ts fs a q keep ih => exact fun _ _ => HEq.rfl
    | Win P O o w t fw q hrr dist keep ih => exact fun _ _ => HEq.rfl
    | WinExpr P O o ws ts fs g q keeps ih => exact fun _ _ => HEq.rfl
  intro m κ q h
  exact eq_of_heq (key q rfl h)

/-- **Substituting is assigning**: the term with the relation replaced by
`ρ` reads as the term over the instance binding the name to `ρ`'s
value. -/
theorem AggQueryIn.evaluatePlain_substRel {s : String} {c n : ℕ}
    (pv : Fin n → T ⊕ Fin c) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      ∀ (D : Database T) (γ : Fin c → T),
        (AggQueryIn.substRel s pv q).evaluatePlain D γ
          = q.evaluatePlain
              (D.assign s ({fun k => _root_.Sum.elim id γ (pv k)} : Multiset (Tuple T n))) γ := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' =>
    rintro ⟨rfl, rfl⟩ D γ
    rw [AggQueryIn.substRel, dite_eq_left ⟨rfl, rfl⟩, AggQueryIn.evaluatePlain_castIdx]
    simp only [AggQueryIn.evaluatePlain, Database.find_assign]
    rfl
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih =>
    intro h D γ
    simp only [AggQueryIn.substRel, AggQueryIn.evaluatePlain]
    rw [ih pv h D γ]
  | Sel φ q _ ih =>
    intro h D γ
    simp only [AggQueryIn.substRel, AggQueryIn.evaluatePlain]
    rw [ih pv h.2 D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) D γ
    · simp only [AggQueryIn.substRel, AggQueryIn.evaluatePlain_castIdx, AggQueryIn.evaluatePlain]
      rw [ih₁ pv h₁ D γ, AggQueryIn.substRel_of_noMention pv q₂ h₂,
        AggQueryIn.evaluatePlain_assign_of_noMention _ q₂ h₂]
    · simp only [AggQueryIn.substRel, AggQueryIn.evaluatePlain_castIdx, AggQueryIn.evaluatePlain]
      rw [ih₂ pv h₂ D γ, AggQueryIn.substRel_of_noMention pv q₁ h₁,
        AggQueryIn.evaluatePlain_assign_of_noMention _ q₁ h₁]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h D γ
    simp only [AggQueryIn.substRel, AggQueryIn.evaluatePlain]
    rw [ih₁ pv h.1 D γ]
    refine Multiset.bind_congr fun u _ => ?_
    rw [AggQueryIn.evaluatePlain_assign_of_noMention _ q₂ h.2]
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h D γ => ih pv h D γ
  | Retag hk q ih => exact fun h D γ => ih pv h D γ
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

omit [ValueType T] in
/-- The substituted term mentions nothing the term and `ρ` do not, and
not the recursive name. -/
theorem AggQueryIn.noMention_substRel {s s' : String} {c n : ℕ}
    (pv : Fin n → T ⊕ Fin c) (hρ : (AggQueryIn.Param pv (ColKind.allReg n) : AggQueryIn T c n
        (ColKind.allReg n)).noMention s') :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      (s' = s ∨ q.noMention s') → (AggQueryIn.substRel s pv q).noMention s' := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s'' =>
    rintro ⟨rfl, rfl⟩ _
    rw [AggQueryIn.substRel, dite_eq_left ⟨rfl, rfl⟩, AggQueryIn.noMention_castIdx]
    exact hρ
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h hs => ih pv hρ h hs
  | Sel φ q _ ih => exact fun h hs => ih pv hρ h.2 hs
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) hs
    · rw [AggQueryIn.substRel, AggQueryIn.noMention_castIdx]
      refine ⟨ih₁ pv hρ h₁ (hs.imp_right fun h => h.1), ?_⟩
      rw [AggQueryIn.substRel_of_noMention pv q₂ h₂]
      rcases hs with rfl | hs
      · exact h₂
      · exact hs.2
    · rw [AggQueryIn.substRel, AggQueryIn.noMention_castIdx]
      refine ⟨?_, ih₂ pv hρ h₂ (hs.imp_right fun h => h.2)⟩
      rw [AggQueryIn.substRel_of_noMention pv q₁ h₁]
      rcases hs with rfl | hs
      · exact h₁
      · exact hs.1
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h hs
    refine ⟨ih₁ pv hρ h.1 (hs.imp_right fun h => h.1), ?_⟩
    rcases hs with rfl | hs
    · exact h.2
    · exact hs.2
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h hs => ih pv hρ h hs
  | Retag hk q ih => exact fun h hs => ih pv hρ h hs
  | Mu s'' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s'' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

/-! ## The counters: a power of a unary relation, read lexicographically -/

namespace AggQueryIn

variable {c : ℕ}

/-- `E^K`, the `K`-fold product of a unary relation. -/
def pow (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) :
    (K : ℕ) → AggQueryIn T c K (ColKind.allReg K)
  | 0 => unitC
  | K + 1 => AggQueryIn.prodA (pow EQ K) EQ

/-- The values of a unary relation. -/
def unaryVals (E : Multiset (Tuple T 1)) : Multiset T := E.map (fun y => y 0)

/-- **A row of `E^K` is a tuple of values of `E`.** -/
theorem mem_pow (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T) :
    ∀ (K : ℕ) (u : Tuple T K),
      Multiset.Mem ((pow EQ K).evaluatePlain D γ) u
        ↔ ∀ k, u k ∈ unaryVals (EQ.evaluatePlain D γ)
  | 0, u => by
    rw [pow, evaluatePlain_unitC D γ u]
    exact ⟨fun _ k => k.elim0, fun _ => Multiset.mem_singleton_self u⟩
  | K + 1, u => by
    rw [pow, AggQueryIn.evaluatePlain_prodA, Relation.Mem_hMul, mem_pow EQ D γ K]
    constructor
    · rintro ⟨h₁, h₂⟩ k
      refine Fin.lastCases ?_ (fun i => ?_) k
      · show u (Fin.natAdd K 0) ∈ _
        exact Multiset.mem_map.mpr ⟨_, h₂, rfl⟩
      · exact h₁ i
    · intro h
      refine ⟨fun i => h (Fin.castAdd 1 i), ?_⟩
      obtain ⟨y, hy, hyu⟩ := Multiset.mem_map.mp (h (Fin.natAdd K 0))
      have : (fun i : Fin 1 => u (Fin.natAdd K i)) = y := by
        funext i
        rw [Subsingleton.elim i 0]
        exact hyu.symm
      rw [this]
      exact hy

/-- Its distinct rows number `|E|^K`. -/
theorem card_toFinset_pow (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T)
    (γ : Fin c → T) (K : ℕ) :
    ((pow EQ K).evaluatePlain D γ : Multiset (Tuple T K)).toFinset.card
      = (unaryVals (EQ.evaluatePlain D γ)).toFinset.card ^ K := by
  classical
  have : ((pow EQ K).evaluatePlain D γ : Multiset (Tuple T K)).toFinset
      = Fintype.piFinset (fun _ : Fin K => (unaryVals (EQ.evaluatePlain D γ)).toFinset) := by
    ext u
    rw [Multiset.mem_toFinset, Fintype.mem_piFinset]
    show Multiset.Mem ((pow EQ K).evaluatePlain D γ) u ↔ _
    rw [mem_pow]
    exact forall_congr' fun k => Multiset.mem_toFinset.symm
  rw [this, Fintype.card_piFinset]
  simp

end AggQueryIn

/-! ## The lexicographic order on the counters is a total order -/

namespace OrderSpec

/-- Two values are peers in an `ASC` column exactly when they are equal:
the null is unique, so two nulls are equal, and a null is no peer of a
value. -/
theorem OrderCol.peer_ASC_iff (a b : T) : OrderCol.ASC.peer a b = true ↔ a = b := by
  constructor
  · intro h
    simp only [OrderCol.peer, Bool.and_eq_true] at h
    obtain ⟨h₁, h₂⟩ := h
    unfold OrderCol.le at h₁ h₂
    cases ha : ValueType.isNull a <;> cases hb : ValueType.isNull b <;>
      simp only [ha, hb, OrderCol.ASC, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
        Bool.not_false] at h₁ h₂
    · exact le_antisymm h₁ h₂
    · obtain ⟨ν, hν⟩ : ∃ ν : T, (ValueType.nullVal : Option T) = some ν :=
        ⟨a, (ValueType.isNull_iff_nullVal a).mp ha⟩
      rw [ValueType.eq_nullVal_of_isNull hν ha, ValueType.eq_nullVal_of_isNull hν hb]
  · rintro rfl
    simp [OrderCol.peer]

theorem leOn_peer_of_both (o : OrderSpec p) (x y : Tuple T p) :
    ∀ l : List (Fin p), o.leOn l x y = true → o.leOn l y x = true →
      ∀ k ∈ l, (o k).peer (x k) (y k) = true
  | [], _, _, k, hk => absurd hk (List.not_mem_nil)
  | k' :: l, h₁, h₂, k, hk => by
    simp only [leOn] at h₁ h₂
    by_cases hp : (o k').peer (x k') (y k') = true
    · rw [ite_eq_left hp] at h₁
      rw [OrderCol.peer_comm, ite_eq_left hp] at h₂
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hp
      · exact leOn_peer_of_both o x y l h₁ h₂ k hk
    · rw [ite_eq_right hp] at h₁
      rw [OrderCol.peer_comm, ite_eq_right hp] at h₂
      exact absurd (by simp only [OrderCol.peer, Bool.and_eq_true]; exact ⟨h₁, h₂⟩) hp

/-- **The ascending clause is antisymmetric**, hence a total order on the
tuples. -/
theorem le_antisymm_asc {p : ℕ} {x y : Tuple T p} (h₁ : (OrderSpec.asc p).le x y = true)
    (h₂ : (OrderSpec.asc p).le y x = true) : x = y := by
  funext k
  exact (OrderCol.peer_ASC_iff _ _).mp
    (leOn_peer_of_both (OrderSpec.asc p) x y (List.finRange p) h₁ h₂ k (List.mem_finRange k))

theorem lt_trans' (o : OrderSpec p) {x y z : Tuple T p} (h₁ : o.lt x y = true)
    (h₂ : o.lt y z = true) : o.lt x z = true := by
  rw [lt_iff] at h₁ h₂ ⊢
  cases hzx : o.le z x
  · rfl
  · exfalso
    rcases o.le_total x y with hxy | hyx
    · have := o.le_trans hzx hxy
      rw [this] at h₂
      exact absurd h₂ (by simp)
    · rw [hyx] at h₁
      exact absurd h₁ (by simp)

theorem lt_of_le_of_ne_asc {p : ℕ} {x y : Tuple T p} (h : (OrderSpec.asc p).le x y = true)
    (hne : x ≠ y) : (OrderSpec.asc p).lt x y = true := by
  rw [lt_iff]
  cases hyx : (OrderSpec.asc p).le y x
  · rfl
  · exact absurd (le_antisymm_asc h hyx) hne

end OrderSpec

/-- The relation the counters are sorted by. -/
def ascLe (p : ℕ) (x y : Tuple T p) : Prop := (OrderSpec.asc p).le x y = true

/-- And the strict one the rounds move along. -/
def ascLt (p : ℕ) (x y : Tuple T p) : Prop := (OrderSpec.asc p).lt x y = true

instance (p : ℕ) : DecidableRel (ascLe (T := T) p) := fun x y => by
  unfold ascLe; infer_instance

instance (p : ℕ) : DecidableRel (ascLt (T := T) p) := fun x y => by
  unfold ascLt; infer_instance

instance (p : ℕ) : IsTrans (Tuple T p) (ascLe p) := ⟨fun _ _ _ h₁ h₂ => OrderSpec.le_trans _ h₁ h₂⟩
instance (p : ℕ) : Std.Antisymm (ascLe (T := T) p) :=
  ⟨fun _ _ h₁ h₂ => OrderSpec.le_antisymm_asc h₁ h₂⟩
instance (p : ℕ) : Std.Total (ascLe (T := T) p) := ⟨fun x y => OrderSpec.le_total _ x y⟩
instance (p : ℕ) : Std.Irrefl (ascLt (T := T) p) :=
  ⟨fun x h => by unfold ascLt at h; rw [OrderSpec.lt_irrefl] at h; exact absurd h (by simp)⟩

/-- **A listing of a finite set of counters, strictly increasing.** -/
theorem exists_sorted_counters (p : ℕ) (C : Finset (Tuple T p)) :
    ∃ l : List (Tuple T p), l.Pairwise (ascLt p) ∧ l.length = C.card ∧ ∀ x ∈ l, x ∈ C := by
  refine ⟨C.sort (ascLe p), ?_, Finset.length_sort _, fun x hx => (Finset.mem_sort _).mp hx⟩
  have hp := Finset.pairwise_sort (s := C) (r := ascLe p)
  have hnd : (C.sort (ascLe p)).Nodup := Finset.sort_nodup C (ascLe p)
  rw [List.pairwise_iff_getElem] at hp ⊢
  intro i j hi hj hij
  refine OrderSpec.lt_of_le_of_ne_asc (hp i j hi hj hij) fun heq => ?_
  exact absurd ((List.Nodup.getElem_inj_iff hnd).mp heq) (Nat.ne_of_lt hij)

/-! ## The construction -/

namespace AggQueryIn

variable {c : ℕ}

omit [ValueType T] in
@[simp] theorem recLinear_castKind {s : String} {n c m : ℕ} {κ κ' : Fin m → ColKind} {l : List
    (String × ℕ)}
    (h : κ = κ') (q : AggQueryIn T c m κ l) :
    (q.castKind h).recLinear s n ↔ q.recLinear s n := by
  cases h; exact Iff.rfl

omit [ValueType T] in
/-- A substitution keeps a term linear. -/
theorem recLinear_substMap {s : String} {n : ℕ} :
    ∀ {c m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).recLinear s n ↔ q.recLinear s n := by
  intro c m κ l q
  induction q with
  | Rel n' s' => exact fun θ => Iff.rfl
  | Hole n' s' => exact fun θ => Iff.rfl
  | Param pv ρ => exact fun θ => Iff.rfl
  | Empty => exact fun θ => Iff.rfl
  | Proj ps q ih =>
    intro d θ
    rw [AggQueryIn.substMap, recLinear_castKind]
    exact ih θ
  | Sel φ q _ ih =>
    exact fun θ => and_congr (by rw [GenPredIn.hasAggAtom_substMap]) (ih θ)
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun θ => or_congr (and_congr (ih₁ θ) (and_congr Iff.rfl
        (AggQueryIn.noMention_substMap q₂ θ)))
      (and_congr Iff.rfl (and_congr (AggQueryIn.noMention_substMap q₁ θ) (ih₂ θ)))
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun θ => and_congr (ih₁ θ) (AggQueryIn.noMention_substMap q₂ _)
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ => Iff.rfl
  | Dedup q ih => exact fun θ => Iff.rfl
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ => Iff.rfl
  | Explode k hk q ih => exact fun θ => ih θ
  | Retag hk q ih => exact fun θ => ih θ
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun θ => Iff.rfl
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun θ => Iff.rfl
  | Gamma is ts fs q keep ord ih => exact fun θ => Iff.rfl
  | GammaScalar ts fs q ord ih => exact fun θ => Iff.rfl
  | GammaNest is his p fn q ih => exact fun θ => Iff.rfl
  | ProvSum is his t q ih => exact fun θ => Iff.rfl
  | GammaTok is his ts fs a q keep ih => exact fun θ => Iff.rfl
  | Win P O o w t fw q hrr dist keep ih => exact fun θ => Iff.rfl
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ => Iff.rfl

/-- **The substituted term is defined where the term is at `ρ`'s
value.** -/
theorem settlesAt_substRel {s : String} {c n : ℕ} (pv : Fin n → T ⊕ Fin c) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      ∀ (D : Database T) (γ : Fin c → T), (AggQueryIn.Param pv
          (ColKind.allReg n) : AggQueryIn T c n (ColKind.allReg n)).SettlesAt D γ →
        q.SettlesAt (D.assign s ({fun k => _root_.Sum.elim id γ (pv k)} : Multiset (Tuple T n))) γ →
        (AggQueryIn.substRel s pv q).SettlesAt D γ := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' =>
    rintro ⟨rfl, rfl⟩ D γ hρ _
    rw [AggQueryIn.substRel, dite_eq_left ⟨rfl, rfl⟩, AggQueryIn.settlesAt_castIdx]
    exact hρ
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h D γ hρ hq => ih pv h D γ hρ hq
  | Sel φ q _ ih => exact fun h D γ hρ hq => ih pv h.2 D γ hρ hq
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) D γ hρ hq
    · rw [AggQueryIn.substRel, AggQueryIn.settlesAt_castIdx]
      refine ⟨ih₁ pv h₁ D γ hρ hq.1, ?_⟩
      rw [AggQueryIn.substRel_of_noMention pv q₂ h₂]
      exact AggQueryIn.settlesAt_assign_of_noMention _ q₂ h₂ D γ hq.2
    · rw [AggQueryIn.substRel, AggQueryIn.settlesAt_castIdx]
      refine ⟨?_, ih₂ pv h₂ D γ hρ hq.2⟩
      rw [AggQueryIn.substRel_of_noMention pv q₁ h₁]
      exact AggQueryIn.settlesAt_assign_of_noMention _ q₁ h₁ D γ hq.1
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h D γ hρ hq
    refine ⟨ih₁ pv h.1 D γ hρ hq.1, fun u hu => ?_⟩
    have hu' : Multiset.Mem (q₁.evaluatePlain (D.assign s (singleton fun k => _root_.Sum.elim id γ
        (pv k) : Multiset (Tuple T n))) γ) u := by
      rw [← AggQueryIn.evaluatePlain_substRel pv q₁ h.1 D γ]; exact hu
    exact AggQueryIn.settlesAt_assign_of_noMention _ q₂ h.2 D _ (hq.2 u hu')
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h D γ hρ hq => ih pv h D γ hρ hq
  | Retag hk q ih => exact fun h D γ hρ hq => ih pv h D γ hρ hq
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

/-- **A linear term defined at a relation is defined at a sub-relation.** -/
theorem settlesAt_assign_of_subset {s : String} {n : ℕ} :
    ∀ {c m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      ∀ (D : Database T) (γ : Fin c → T) {X X' : Relation T n},
        (∀ t, Multiset.Mem X t → Multiset.Mem X' t) →
        q.SettlesAt (D.assign s X') γ → q.SettlesAt (D.assign s X) γ := by
  intro c m κ l q
  induction q with
  | Rel n' s' => exact fun _ _ _ _ _ _ _ => trivial
  | Hole n' s' => exact fun _ _ _ _ _ _ _ => trivial
  | Param pv ρ => exact fun _ _ _ _ _ _ _ => trivial
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h D γ _ _ hXX hq => ih h D γ hXX hq
  | Sel φ q _ ih => exact fun h D γ _ _ hXX hq => ih h.2 D γ hXX hq
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) D γ X X' hXX hq
    · exact ⟨ih₁ h₁ D γ hXX hq.1, AggQueryIn.settlesAt_of_noMention q₂ h₂
        (fun k t ht => (Database.find_assign_of_ne s t X' D (fun hc => ht.elim (fun h => h hc.2)
            (fun h => by simp at h))).trans
          (Database.find_assign_of_ne s t X D (fun hc => ht.elim (fun h => h hc.2)
              (fun h => by simp at h))).symm) γ hq.2⟩
    · exact ⟨AggQueryIn.settlesAt_of_noMention q₁ h₁
        (fun k t ht => (Database.find_assign_of_ne s t X' D (fun hc => ht.elim (fun h => h hc.2)
            (fun h => by simp at h))).trans
          (Database.find_assign_of_ne s t X D (fun hc => ht.elim (fun h => h hc.2)
              (fun h => by simp at h))).symm) γ hq.1,
        ih₂ h₂ D γ hXX hq.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h D γ X X' hXX hq
    refine ⟨ih₁ h.1 D γ hXX hq.1, fun u hu => ?_⟩
    exact AggQueryIn.settlesAt_of_noMention q₂ h.2
      (fun k t ht => (Database.find_assign_of_ne s t X' D (fun hc => ht.elim (fun h => h hc.2)
          (fun h => by simp at h))).trans
        (Database.find_assign_of_ne s t X D (fun hc => ht.elim (fun h => h hc.2)
            (fun h => by simp at h))).symm) _
      (hq.2 u (AggQueryIn.mem_evaluatePlain_assign_of_subset q₁ h.1 D γ hXX u hu))
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h D γ _ _ hXX hq => ih h D γ hXX hq
  | Retag hk q ih => exact fun h D γ _ _ hXX hq => ih h D γ hXX hq
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

omit [ValueType T] in
theorem noMention_pow (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) {s : String}
    (h : EQ.noMention s) : ∀ K, (pow EQ K).noMention s
  | 0 => by rw [pow, unitC, AggQueryIn.noMention_castKind]; trivial
  | K + 1 => by
    rw [pow]
    exact AggQueryIn.noMention_prodA _ _ (noMention_pow EQ h K) h

theorem settlesAt_pow (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T)
    (h : EQ.SettlesAt D γ) : ∀ K, (pow EQ K).SettlesAt D γ
  | 0 => by rw [pow, unitC, AggQueryIn.settlesAt_castKind]; trivial
  | K + 1 => by
    rw [pow]
    exact AggQueryIn.settlesAt_prodA _ _ D γ (settlesAt_pow EQ D γ h K) h

/-- The columns of the right side of the apply the round is built on. -/
def dropLeft (n K : ℕ) : Tuple T ((n + K) + (n + K)) → Tuple T (n + K) :=
  fun w j => w (Fin.natAdd (n + K) j)

/-- The tuple part of a row of the simulation. -/
def leftPart (n K : ℕ) (u : Tuple T (n + K)) : Tuple T n := fun i => u (Fin.castAdd K i)

/-- And its counter. -/
def rightPart (n K : ℕ) (u : Tuple T (n + K)) : Tuple T K := fun k => u (Fin.natAdd n k)

omit [ValueType T] in
@[simp] theorem leftPart_append (n K : ℕ) (t : Tuple T n) (m : Tuple T K) :
    leftPart n K (Fin.append t m) = t := by
  funext i; exact Fin.append_left t m i

omit [ValueType T] in
@[simp] theorem rightPart_append (n K : ℕ) (t : Tuple T n) (m : Tuple T K) :
    rightPart n K (Fin.append t m) = m := by
  funext k; exact Fin.append_right t m k

/-- **The current row's tuple part**, read off the outer columns of the
apply: the parameters a hole of the recursive term is replaced by. -/
def rowPv (n K : ℕ) : Fin n → T ⊕ Fin ((n + K) + c) :=
  fun i => Sum.inr (Fin.castAdd c (Fin.castAdd K i))

omit [ValueType T] in
theorem rowPv_vals (n K : ℕ) (u : Tuple T (n + K)) (γ : Fin c → T) :
    (fun k => _root_.Sum.elim id (Fin.append u γ : Tuple T ((n + K) + c)) (rowPv (c := c) n K k))
      = leftPart n K u := by
  funext i
  show (Fin.append u γ : Tuple T ((n + K) + c)) (Fin.castAdd c (Fin.castAdd K i)) = _
  rw [Fin.append_left]
  rfl

/-- **The counter moves up**: the row's counter is strictly above the
current row's, lexicographically. -/
def ltSel (n K : ℕ) : GenPredIn T ((n + K) + c) (ColKind.allReg K) :=
  OrderSpec.ltPredOn (OrderSpec.asc K)
    (fun k => TermGIn.outer (Fin.castAdd c (Fin.natAdd n k)))
    (fun k => TermGIn.index k rfl) (List.finRange K)

theorem holdsPlain_ltSel (n K : ℕ) (u : Tuple T (n + K)) (γ : Fin c → T) (y : Tuple T K)
    (hu : ∀ k, ValueType.isNull (rightPart n K u k) = false)
    (hy : ∀ k, ValueType.isNull (y k) = false) :
    (ltSel (c := c) n K).holdsPlain y (Fin.append u γ) ↔ ascLt K (rightPart n K u) y := by
  have hx : ∀ k, (TermGIn.outer (T := T) (κ := ColKind.allReg K)
      (Fin.castAdd c (Fin.natAdd n k))).evalPlain y (Fin.append u γ) = rightPart n K u k :=
    fun k => by
      show (Fin.append u γ : Tuple T ((n + K) + c)) (Fin.castAdd c (Fin.natAdd n k)) = _
      rw [Fin.append_left]
      rfl
  rw [ltSel, OrderSpec.ltPredOn, OrderSpec.holdsPlain_ltPredOnOf (OrderSpec.asc K) _
    (fun k => TermGIn.outer (Fin.castAdd c (Fin.natAdd n k))) (fun k => TermGIn.index k rfl) y
    (Fin.append u γ) (fun k => OrderCol.holdsPlain_ltPred_of (OrderSpec.asc K k)
      (TermGIn.outer (Fin.castAdd c (Fin.natAdd n k))) (TermGIn.index k rfl) y (Fin.append u γ)
      (by rw [hx]; exact hu k) (hy k))
    (fun k a b => OrderSpec.OrderCol.peer_ASC_iff a b)]
  rw [show (fun k => (TermGIn.outer (T := T) (κ := ColKind.allReg K)
      (Fin.castAdd c (Fin.natAdd n k))).evalPlain y (Fin.append u γ)) = rightPart n K u from
    funext hx]
  show OrderSpec.le (OrderSpec.asc K) y (rightPart n K u) = false ↔ _
  unfold ascLt
  rw [OrderSpec.lt_iff]

/-- **One round of the simulation**: for each row of the recursive
relation, the term at the row's tuple part, paired with every counter
above the row's. -/
def simBody (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) :
    AggQueryIn T c (n + K) (ColKind.allReg (n + K)) [(s', n + K)] :=
  (AggQueryIn.Proj (fun j : Fin (n + K) =>
      ProjColIn.term (TermGIn.index (Fin.natAdd (n + K) j) (by rw [Fin.append_right]; rfl)))
    (AggQueryIn.Apply (AggQueryIn.Hole (n + K) s')
      (AggQueryIn.prodA
        (AggQueryIn.castIdx (subIdx_self s n)
          (AggQueryIn.substRel s (rowPv n K) (L.substMap (applyOuter T c (n + K)))))
        (AggQueryIn.Sel (ltSel n K) ((pow EQ K).substMap (applyOuter T c (n + K))))))).castKind
    (funext fun _ => rfl)

/-- The counters of the simulation, and the values they are made of. -/
theorem nonNull_pow (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (D : Database T) (γ : Fin c → T)
    (hE : ∀ e ∈ unaryVals (EQ.evaluatePlain D γ), ValueType.isNull e = false) (K : ℕ)
    (y : Tuple T K) (hy : Multiset.Mem ((pow EQ K).evaluatePlain D γ) y) :
    ∀ k, ValueType.isNull (y k) = false :=
  fun k => hE _ ((mem_pow EQ D γ K y).mp hy k)

/-- **What a round computes**, on a relation whose counters are
counters: for each row, the term at the row's tuple part, each of its
rows paired with every counter above the row's. -/
theorem evaluatePlain_simBody (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (hL : L.recLinear s n) (hLs : L.noMention s')
    (hEs : EQ.noMention s') (D : Database T) (γ : Fin c → T)
    (hE : ∀ e ∈ unaryVals (EQ.evaluatePlain D γ), ValueType.isNull e = false)
    (Y : Relation T (n + K))
    (hY : ∀ y, Multiset.Mem Y y → ∀ k, ValueType.isNull (rightPart n K y k) = false) :
    ((simBody s s' n K EQ L).evaluatePlain (D.assign s' Y) γ : Multiset (Tuple T (n + K)))
      = Y.bind (fun y =>
          (L.evaluatePlain (D.assign s ({leftPart n K y} : Multiset (Tuple T n))) γ
              : Multiset (Tuple T n)).bind (fun a =>
            (Multiset.filter (fun m => ascLt K (rightPart n K y) m)
                ((pow EQ K).evaluatePlain D γ)).map
              (fun m => (Fin.append a m : Tuple T (n + K))))) := by
  rw [simBody, AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (dropLeft n K) ((AggQueryIn.Apply (AggQueryIn.Hole (n + K) s')
    (AggQueryIn.prodA
      (AggQueryIn.castIdx (subIdx_self s n)
        (AggQueryIn.substRel s (rowPv n K) (L.substMap (applyOuter T c (n + K)))))
      (AggQueryIn.Sel (ltSel n K) ((pow EQ K).substMap (applyOuter T c (n + K)))))).evaluatePlain
        (D.assign s' Y) γ) = _
  simp only [AggQueryIn.evaluatePlain, Database.find_assign, AggQueryIn.evaluatePlain_prodA]
  rw [Multiset.map_bind]
  refine Multiset.bind_congr fun u hu => ?_
  rw [Multiset.map_map]
  refine Eq.trans (Eq.trans (Multiset.map_congr rfl (fun v _ => ?_)) (Multiset.map_id' _)) ?_
  · show dropLeft n K (Fin.append u v) = v
    funext j
    exact Fin.append_right u v j
  -- the left factor: the term at the row's tuple part
  have hleft : (AggQueryIn.castIdx (subIdx_self s n) (AggQueryIn.substRel s (rowPv n K)
      (L.substMap (applyOuter T c (n + K))))).evaluatePlain (D.assign s' Y) (Fin.append u γ)
      = L.evaluatePlain (D.assign s ({leftPart n K u} : Multiset (Tuple T n))) γ := by
    rw [AggQueryIn.evaluatePlain_castIdx,
      AggQueryIn.evaluatePlain_substRel (rowPv n K) _ ((recLinear_substMap L _).mpr hL),
      rowPv_vals, AggQueryIn.evaluatePlain_substMap, substVal_applyOuter]
    refine AggQueryIn.evaluatePlain_congr_of_noMention L hLs (fun k t ht => ?_) γ
    by_cases hc : k = n ∧ t = s
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Database.find_assign, Database.find_assign]
    · rw [Database.find_assign_of_ne s t _ _ hc, Database.find_assign_of_ne s t _ _ hc,
        Database.find_assign_of_ne s' t Y D (fun hc' => ht.elim (fun h => h hc'.2) (fun h => hc
            ⟨(Prod.mk.inj (List.mem_singleton.mp h)).2, (Prod.mk.inj
                (List.mem_singleton.mp h)).1⟩))]
  -- the right factor: the counters above the row's
  have hright : ((pow EQ K).substMap (applyOuter T c (n + K))).evaluatePlain (D.assign s' Y)
      (Fin.append u γ) = (pow EQ K).evaluatePlain D γ := by
    rw [AggQueryIn.evaluatePlain_substMap, substVal_applyOuter,
      AggQueryIn.evaluatePlain_assign_of_noMention Y _ (noMention_pow EQ hEs K)]
  rw [Relation.hMul_eq_bind, hleft, hright]
  refine Multiset.bind_congr fun a _ => ?_
  refine congrArg (Multiset.map _) (Multiset.filter_congr fun m hm => ?_)
  exact holdsPlain_ltSel n K u γ m (hY u hu) (nonNull_pow EQ D γ hE K m hm)

end AggQueryIn

/-! ## The simulation, and what it computes -/

namespace AggQueryIn

variable {c : ℕ}

/-- The product of two relations, as the bag of appended rows. -/
def pairRel {n K : ℕ} (A : Multiset (Tuple T n)) (M : Multiset (Tuple T K)) :
    Multiset (Tuple T (n + K)) :=
  A.bind (fun a => M.map (fun m => (Fin.append a m : Tuple T (n + K))))

omit [ValueType T] in
theorem mem_pairRel {n K : ℕ} (A : Multiset (Tuple T n)) (M : Multiset (Tuple T K))
    (y : Tuple T (n + K)) :
    y ∈ pairRel A M ↔ ∃ a ∈ A, ∃ m ∈ M, y = Fin.append a m := by
  unfold pairRel
  rw [Multiset.mem_bind]
  constructor
  · rintro ⟨a, ha, hy⟩
    obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hy
    exact ⟨a, ha, m, hm, rfl⟩
  · rintro ⟨a, ha, m, hm, rfl⟩
    exact ⟨a, ha, Multiset.mem_map.mpr ⟨m, hm, rfl⟩⟩

omit [ValueType T] in
theorem pairRel_zero {n K : ℕ} (A : Multiset (Tuple T n)) :
    pairRel A (0 : Multiset (Tuple T K)) = 0 := by
  unfold pairRel
  simp only [Multiset.map_zero, Multiset.bind_zero]

omit [ValueType T] in
theorem mem_map_leftPart_pairRel {n K : ℕ} (A : Multiset (Tuple T n)) (M : Multiset (Tuple T K))
    (x : Tuple T n) : x ∈ (pairRel A M).map (leftPart n K) ↔ x ∈ A ∧ M ≠ 0 := by
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, m, hm, rfl⟩ := (mem_pairRel A M y).mp hy
    rw [leftPart_append]
    exact ⟨ha, fun h => by rw [h] at hm; exact Multiset.notMem_zero m hm⟩
  · rintro ⟨hx, hM⟩
    obtain ⟨m, hm⟩ := Multiset.exists_mem_of_ne_zero hM
    exact ⟨Fin.append x m, (mem_pairRel A M _).mpr ⟨x, hx, m, hm, rfl⟩, leftPart_append n K x m⟩

omit [ValueType T] in
/-- **Applying a term to the tuple part and a move to the counter part,
row by row, is the product of the two.** -/
theorem bind_pairRel {n K n' K' : ℕ} (A : Multiset (Tuple T n)) (M : Multiset (Tuple T K))
    (f : Tuple T n → Multiset (Tuple T n')) (g : Tuple T K → Multiset (Tuple T K')) :
    (pairRel A M).bind (fun y => (f (leftPart n K y)).bind (fun a' =>
        (g (rightPart n K y)).map (fun m' => (Fin.append a' m' : Tuple T (n' + K')))))
      = pairRel (A.bind f) (M.bind g) := by
  unfold pairRel
  rw [Multiset.bind_assoc, Multiset.bind_assoc]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.bind_map]
  simp only [leftPart_append, rightPart_append]
  rw [Multiset.bind_bind]
  refine Multiset.bind_congr fun a' _ => ?_
  exact (Multiset.map_bind M g _).symm

/-- **The simulation**: a bag recursion over rows pairing a tuple with a
counter, from `(q₀ ⊎ C) × E^K`, each round applying the term to the
tuple part and moving the counter up. -/
def sim (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) :
    AggQueryIn T c (n + K) (ColKind.allReg (n + K)) :=
  AggQueryIn.Mu s' (AggQueryIn.prodA BQ (pow EQ K)) (simBody s s' n K EQ L)

omit [ValueType T] in
theorem dedupG_kinds (n : ℕ) :
    (fun j => (Fin.append (ColKind.allReg n) (fun _ : Fin 0 => ColKind.agg)) j)
      = ColKind.allReg (n + 0) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun z => z.elim0) j
  rw [Fin.append_left]
  rfl

/-- **Duplicate elimination as a grouping** by every column with no
aggregate: the shape the bases without `ε` use. -/
def dedupG {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n)) :
    AggQueryIn T c n (ColKind.allReg n) :=
  (AggQueryIn.Gamma (lab := 0) (rd := q.readsOuter) (fun k => k) (fun j : Fin 0 => j.elim0) (fun
      j : Fin 0 => j.elim0)
      q).castKind
    (dedupG_kinds n)

theorem evaluatePlain_dedupG {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n)) (D : Database T)
    (γ : Fin c → T) : (dedupG q).evaluatePlain D γ = (q.evaluatePlain D γ).dedup := by
  rw [dedupG, AggQueryIn.evaluatePlain_castKind]
  exact (AggQueryIn.dedup_plainEquiv_gamma q D γ).symm

theorem settlesAt_dedupG {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n)) (D : Database T)
    (γ : Fin c → T) : (dedupG q).SettlesAt D γ ↔ q.SettlesAt D γ := by
  rw [dedupG, AggQueryIn.settlesAt_castKind]
  exact Iff.rfl

/-- Its tuple parts, without duplicates: the set recursion's value. -/
def simResult (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) :
    AggQueryIn T c n (ColKind.allReg n) :=
  dedupG ((AggQueryIn.Proj (fun i : Fin n =>
      ProjColIn.term (TermGIn.index (Fin.castAdd K i) rfl)) (sim s s' n K EQ BQ L)).castKind
    (funext fun _ => rfl))

/-- The term applied to one row of the recursive relation. -/
noncomputable def rowTerm (s : String) (n : ℕ) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (D : Database T) (γ : Fin c → T) : Tuple T n → Multiset (Tuple T n) :=
  fun t => L.evaluatePlain (D.assign s ({t} : Multiset (Tuple T n))) γ

/-- One round of the simulation, as a function of the recursive relation. -/
noncomputable def simStep (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (D : Database T) (γ : Fin c → T) :
    Multiset (Tuple T (n + K)) → Multiset (Tuple T (n + K)) :=
  fun Y => (simBody s s' n K EQ L).evaluatePlain (D.assign s' Y) γ

/-- The counters. -/
noncomputable def counters (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K : ℕ) (D : Database T)
    (γ : Fin c → T) : Multiset (Tuple T K) :=
  (pow EQ K).evaluatePlain D γ

section Rounds

variable (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
  (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
  (hL : L.recLinear s n) (hLs : L.noMention s') (hEs : EQ.noMention s')
  (D : Database T) (γ : Fin c → T)
  (hE : ∀ e ∈ unaryVals (EQ.evaluatePlain D γ), ValueType.isNull e = false)

include hL hLs hEs hE in
/-- **The rounds of the simulation**: the term iterated on the base, as a
bag, paired with the counters of the round. -/
theorem simStep_iterate (B : Multiset (Tuple T n)) :
    ∀ j, (simStep s s' n K EQ L D γ)^[j] (pairRel B (counters EQ K D γ))
      = pairRel ((fun X : Multiset (Tuple T n) => X.bind (rowTerm s n L D γ))^[j] B)
          (chainBag (ascLt K) (counters EQ K D γ) j)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', simStep_iterate B j, Function.iterate_succ_apply']
    simp only [simStep]
    rw [evaluatePlain_simBody s s' n K EQ L hL hLs hEs D γ hE _ (fun y hy k => ?_)]
    · simp only [chainBag]
      exact bind_pairRel _ _ (rowTerm s n L D γ)
        (fun m => (counters EQ K D γ).filter (fun m' => ascLt K m m'))
    · obtain ⟨a, _, m, hm, rfl⟩ := (mem_pairRel _ _ y).mp hy
      rw [rightPart_append]
      exact nonNull_pow EQ D γ hE K m (mem_of_mem_chainBag (ascLt K) _ j m hm) k

include hL hLs hEs hE in
/-- An empty round stays empty. -/
theorem simStep_zero : simStep s s' n K EQ L D γ 0 = 0 := by
  simp only [simStep]
  rw [evaluatePlain_simBody s s' n K EQ L hL hLs hEs D γ hE 0 (fun y hy => absurd hy
    (Multiset.notMem_zero y))]
  exact Multiset.zero_bind _

include hL hLs hEs hE in
/-- **The simulation always settles**: past the number of distinct
counters no row has a counter left. -/
theorem simStep_iterate_eq_zero (B : Multiset (Tuple T n)) :
    (simStep s s' n K EQ L D γ)^[(counters EQ K D γ).toFinset.card + 1]
      (pairRel B (counters EQ K D γ)) = 0 := by
  rw [Function.iterate_succ_apply', simStep_iterate s s' n K EQ L hL hLs hEs D γ hE B,
    chainBag_eq_zero_of_card_le (ascLt K) _ (fun _ _ _ => OrderSpec.lt_trans' _) le_rfl,
    pairRel_zero]
  exact simStep_zero s s' n K EQ L hL hLs hEs D γ hE

omit [ValueType T] in
/-- Membership in the sum of the rounds. -/
theorem mem_muSum {α : Type} (step : Multiset α → Multiset α) (M : Multiset α) (x : α) :
    ∀ b, x ∈ muSum step b M ↔ ∃ j, j ≤ b ∧ x ∈ step^[j] M
  | 0 => by
    show x ∈ M ↔ _
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨j, hj, h⟩ => by rw [Nat.le_zero.mp hj] at h; exact h⟩
  | b + 1 => by
    rw [muSum_succ, Multiset.mem_add, mem_muSum step M x b]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, Nat.le_succ_of_le hj, h⟩
      · exact ⟨b + 1, le_rfl, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact Or.inl ⟨j, Nat.le_of_lt_succ hj, h⟩
      · exact Or.inr h

/-- A counter chain of each length below the number of counters. -/
theorem chainBag_ne_zero_of_lt {j : ℕ} (hj : LT.lt j (counters EQ K D γ).toFinset.card) :
    chainBag (ascLt K) (counters EQ K D γ) j ≠ 0 := by
  obtain ⟨l, hl, hlen, hmem⟩ := exists_sorted_counters K (counters EQ K D γ).toFinset
  have hj' : LT.lt j l.length := by rw [hlen]; exact hj
  exact fun h => by
    have := getElem_mem_chainBag (ascLt K) (counters EQ K D γ) l hl
      (fun x hx => Multiset.mem_toFinset.mp (hmem x hx)) j hj'
    rw [h] at this
    exact Multiset.notMem_zero _ this

include hL hLs hEs hE in
/-- **What the simulation's tuples are**: the rounds of the term on the
base, up to the number of counters. -/
theorem mem_simResult (B : Multiset (Tuple T n))
    (hB : (BQ.evaluatePlain D γ : Multiset (Tuple T n)) = B) (x : Tuple T n) :
    Multiset.Mem ((simResult s s' n K EQ BQ L).evaluatePlain D γ) x
      ↔ ∃ j, LT.lt j (counters EQ K D γ).toFinset.card
          ∧ x ∈ (fun X : Multiset (Tuple T n) => X.bind (rowTerm s n L D γ))^[j] B := by
  have hbase : ((AggQueryIn.prodA BQ (pow EQ K)).evaluatePlain D γ : Multiset (Tuple T (n + K)))
        = pairRel B (counters EQ K D γ) := by
    rw [AggQueryIn.evaluatePlain_prodA, Relation.hMul_eq_bind, hB]
    rfl
  rw [simResult, evaluatePlain_dedupG]
  change x ∈ Multiset.dedup (Multiset.map (fun u : Tuple T (n + K) =>
      (fun i => (ProjColIn.term (TermGIn.index (Fin.castAdd K i) rfl)
        : ProjColIn T c (ColKind.allReg (n + K))).evalPlain u γ : Tuple T n))
    (muSumFix (simStep s s' n K EQ L D γ)
      ((AggQueryIn.prodA BQ (pow EQ K)).evaluatePlain D γ))) ↔ _
  rw [Multiset.mem_dedup, hbase,
    muSumFix_eq_of_empty (simStep_zero s s' n K EQ L hL hLs hEs D γ hE)
      (simStep_iterate_eq_zero s s' n K EQ L hL hLs hEs D γ hE B)]
  have hleft : (fun u : Tuple T (n + K) => (fun i => (ProjColIn.term
      (TermGIn.index (Fin.castAdd K i) rfl) : ProjColIn T c (ColKind.allReg (n + K))).evalPlain u γ
        : Tuple T n)) = leftPart n K :=
    rfl
  rw [hleft, Multiset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨j, hj, hyj⟩ := (mem_muSum _ _ y _).mp hy
    rw [simStep_iterate s s' n K EQ L hL hLs hEs D γ hE B j] at hyj
    obtain ⟨a, ha, m, hm, rfl⟩ := (mem_pairRel _ _ y).mp hyj
    rw [leftPart_append]
    refine ⟨j, ?_, ha⟩
    by_contra hjN
    rw [chainBag_eq_zero_of_card_le (ascLt K) _ (fun _ _ _ => OrderSpec.lt_trans' _)
      (Nat.le_of_not_lt hjN)] at hm
    exact Multiset.notMem_zero m hm
  · rintro ⟨j, hj, hx⟩
    obtain ⟨m, hm⟩ := Multiset.exists_mem_of_ne_zero (chainBag_ne_zero_of_lt K EQ D γ hj)
    refine ⟨Fin.append x m, ?_, leftPart_append n K x m⟩
    rw [mem_muSum]
    refine ⟨j, Nat.le_of_lt hj, ?_⟩
    rw [simStep_iterate s s' n K EQ L hL hLs hEs D γ hE B j]
    exact (mem_pairRel _ _ _).mpr ⟨x, hx, m, hm, rfl⟩

include hL hLs hEs hE in
/-- **The simulation is defined** wherever its base and its counters are,
and the term is defined at every row the rounds reach. -/
theorem settlesAt_simResult (hBQ : BQ.SettlesAt D γ) (hEQ : EQ.SettlesAt D γ)
    (hLset : ∀ (j : ℕ) (t : Tuple T n), LT.lt j (counters EQ K D γ).toFinset.card →
      t ∈ (fun X : Multiset (Tuple T n) => X.bind (rowTerm s n L D γ))^[j]
        (BQ.evaluatePlain D γ : Multiset (Tuple T n)) →
      L.SettlesAt (D.assign s ({t} : Multiset (Tuple T n))) γ) :
    (simResult s s' n K EQ BQ L).SettlesAt D γ := by
  have hbase : ((AggQueryIn.prodA BQ (pow EQ K)).evaluatePlain D γ : Multiset (Tuple T (n + K)))
        = pairRel (BQ.evaluatePlain D γ) (counters EQ K D γ) := by
    rw [AggQueryIn.evaluatePlain_prodA, Relation.hMul_eq_bind]
    rfl
  rw [simResult, settlesAt_dedupG, AggQueryIn.settlesAt_castKind]
  show (sim s s' n K EQ BQ L).SettlesAt D γ
  rw [sim]
  refine ⟨?_, simStep_zero s s' n K EQ L hL hLs hEs D γ hE, ?_, fun k => ?_⟩
  · exact AggQueryIn.settlesAt_prodA _ _ D γ hBQ (settlesAt_pow EQ D γ hEQ K)
  · refine ⟨(counters EQ K D γ).toFinset.card, ?_⟩
    rw [hbase]
    exact simStep_iterate_eq_zero s s' n K EQ L hL hLs hEs D γ hE _
  · have hk : (fun X => (simBody s s' n K EQ L).evaluatePlain (D.assign s' X) γ)^[k]
        ((AggQueryIn.prodA BQ (pow EQ K)).evaluatePlain D γ)
        = pairRel ((fun X : Multiset (Tuple T n) => X.bind (rowTerm s n L D γ))^[k]
            (BQ.evaluatePlain D γ)) (chainBag (ascLt K) (counters EQ K D γ) k) := by
      rw [hbase]
      exact simStep_iterate s s' n K EQ L hL hLs hEs D γ hE _ k
    rw [hk]
    rw [simBody, AggQueryIn.settlesAt_castKind]
    refine ⟨trivial, fun u hu => ?_⟩
    have hu' : Multiset.Mem (pairRel ((fun X : Multiset (Tuple T n) =>
        X.bind (rowTerm s n L D γ))^[k] (BQ.evaluatePlain D γ))
        (chainBag (ascLt K) (counters EQ K D γ) k)) u := by
      simpa only [AggQueryIn.evaluatePlain, Database.find_assign] using hu
    obtain ⟨a, ha, m, hm, rfl⟩ := (mem_pairRel _ _ u).mp hu'
    have hk' : LT.lt k (counters EQ K D γ).toFinset.card := by
      by_contra hjN
      rw [chainBag_eq_zero_of_card_le (ascLt K) _ (fun _ _ _ => OrderSpec.lt_trans' _)
        (Nat.le_of_not_lt hjN)] at hm
      exact Multiset.notMem_zero m hm
    refine AggQueryIn.settlesAt_prodA _ _ _ _ ?_ ?_
    · rw [AggQueryIn.settlesAt_castIdx]
      refine AggQueryIn.settlesAt_substRel (rowPv n K) _
        ((recLinear_substMap L _).mpr hL) _ _ trivial ?_
      · rw [rowPv_vals, AggQueryIn.settlesAt_substMap, substVal_applyOuter,
          leftPart_append]
        refine AggQueryIn.settlesAt_of_noMention L hLs (fun k' t ht => ?_) γ (hLset k a hk' ha)
        by_cases hc : k' = n ∧ t = s
        · obtain ⟨rfl, rfl⟩ := hc
          rw [Database.find_assign, Database.find_assign]
        · rw [Database.find_assign_of_ne s t _ _ hc, Database.find_assign_of_ne s t _ _ hc,
            Database.find_assign_of_ne s' t _ D (fun hc' => ht.elim (fun h => h hc'.2)
                (fun h => hc ⟨(Prod.mk.inj (List.mem_singleton.mp h)).2, (Prod.mk.inj
                    (List.mem_singleton.mp h)).1⟩))]
    · show ((pow EQ K).substMap (applyOuter T c (n + K))).SettlesAt _ _
      rw [AggQueryIn.settlesAt_substMap, substVal_applyOuter]
      exact AggQueryIn.settlesAt_of_noMention _ (noMention_pow EQ hEs K)
        (fun k' t ht => (Database.find_assign_of_ne s' t _ D (fun hc => ht.elim (fun h => h hc.2)
            (fun h => by simp at h))).symm) γ
        (settlesAt_pow EQ D γ hEQ K)

end Rounds

end AggQueryIn

/-! ## The set recursion's rounds, as the term iterated on the base -/

section BagStep

variable {α : Type} [DecidableEq α]

/-- The step of a set recursion `μ^∪R.(B, L(R))` with `L` linear, as a
bag before the duplicate elimination. -/
def bagStep (B : Multiset α) (L₁ : α → Multiset α) (X : Multiset α) : Multiset α :=
  B + X.bind L₁

omit [DecidableEq α] in
theorem bagStep_mono (B : Multiset α) (L₁ : α → Multiset α) :
    ∀ X Y : Multiset α, X ⊆ Y → bagStep B L₁ X ⊆ bagStep B L₁ Y := by
  intro X Y h x hx
  unfold bagStep at hx ⊢
  rw [Multiset.mem_add] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨t, ht, hxt⟩ := Multiset.mem_bind.mp hx
    exact Or.inr (Multiset.mem_bind.mpr ⟨t, h ht, hxt⟩)

/-- **Round `m` of the set recursion holds the first `m` iterates of the
term on the base.** -/
theorem mem_muIter_bagStep (B : Multiset α) (L₁ : α → Multiset α) :
    ∀ (m : ℕ) (x : α), x ∈ muIter (fun X => (bagStep B L₁ X).dedup) m
      ↔ ∃ j, LT.lt j m ∧ x ∈ (fun X : Multiset α => X.bind L₁)^[j] B := by
  intro m
  induction m with
  | zero =>
    intro x
    exact ⟨fun h => absurd h (Multiset.notMem_zero x),
      fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j)⟩
  | succ m ih =>
    intro x
    show x ∈ (bagStep B L₁ (muIter _ m)).dedup ↔ _
    rw [Multiset.mem_dedup]
    unfold bagStep
    rw [Multiset.mem_add, Multiset.mem_bind]
    constructor
    · rintro (hx | ⟨t, ht, hxt⟩)
      · exact ⟨0, Nat.succ_pos m, hx⟩
      · obtain ⟨j, hj, htj⟩ := (ih t).mp ht
        refine ⟨j + 1, Nat.succ_lt_succ hj, ?_⟩
        rw [Function.iterate_succ_apply']
        exact Multiset.mem_bind.mpr ⟨t, htj, hxt⟩
    · rintro ⟨j, hj, hx⟩
      cases j with
      | zero => exact Or.inl hx
      | succ j =>
        rw [Function.iterate_succ_apply'] at hx
        obtain ⟨t, ht, hxt⟩ := Multiset.mem_bind.mp hx
        exact Or.inr ⟨t, (ih t).mpr ⟨j, Nat.lt_of_succ_lt_succ hj, ht⟩, hxt⟩

end BagStep

/-! ## The simulation computes the set recursion -/

namespace AggQueryIn

variable {c : ℕ}

/-- **`μ^∪` from `μ^⊎`** (the correctness of the construction): for a
set recursion `μ^∪R.(q₀, q₁)` whose term splits as
`L ⊎ C` with `L` linear, a base query computing `q₀ ⊎ C`, and a counter
relation `E` of non-null values with `|E|^K` at least the size of the
fixpoint, the simulation's tuples are the fixpoint, wherever the
recursion is defined. -/
theorem evaluatePlain_simResult (s s' : String) (n K : ℕ)
    (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (BQ qC q₀ : AggQueryIn T c n (ColKind.allReg n))
    (L q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (hL : L.recLinear s n)
        (hLs : L.noMention s') (hEs : EQ.noMention s')
    (hC : qC.noMention s) (D : Database T) (γ : Fin c → T)
    (hset : (AggQueryIn.MuSet s q₀ q₁).SettlesAt D γ)
    (hsplit : ∀ X : Relation T n, q₁.SettlesAt (D.assign s X) γ →
      (q₁.evaluatePlain (D.assign s X) γ : Multiset (Tuple T n))
        = L.evaluatePlain (D.assign s X) γ + qC.evaluatePlain (D.assign s X) γ)
    (hB : (BQ.evaluatePlain D γ : Multiset (Tuple T n))
      = q₀.evaluatePlain D γ + qC.evaluatePlain D γ)
    (hE : ∀ e ∈ unaryVals (EQ.evaluatePlain D γ), ValueType.isNull e = false)
    (hcard : Multiset.card ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ)
      ≤ (unaryVals (EQ.evaluatePlain D γ)).toFinset.card ^ K) :
    (simResult s s' n K EQ BQ L).evaluatePlain D γ
      = (AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ
    ∧ ∀ (j : ℕ) (t : Tuple T n), LT.lt j (counters EQ K D γ).toFinset.card →
        t ∈ (fun X : Multiset (Tuple T n) => X.bind (rowTerm s n L D γ))^[j]
          (BQ.evaluatePlain D γ : Multiset (Tuple T n)) →
        Multiset.Mem ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ) t := by
  classical
  obtain ⟨-, hs, hk⟩ := hset
  -- the set recursion's step, and the bag step it is the duplicate elimination of
  have hround : ∀ j, muIter (fun X => (q₀.evaluatePlain D γ
      + q₁.evaluatePlain (D.assign s X) γ).dedup) j
      = muIter (fun X => (bagStep (q₀.evaluatePlain D γ + qC.evaluatePlain D γ)
          (rowTerm s n L D γ) X).dedup) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [muIter, muIter, ← ih]
      refine congrArg Multiset.dedup ?_
      rw [hsplit _ (hk j), AggQueryIn.evaluatePlain_assign_of_noMention _ qC hC,
        AggQueryIn.evaluatePlain_assign_bind_of_recLinear L hL D γ]
      have hac : ∀ a b d : Multiset (Tuple T n), a + (b + d) = (a + d) + b :=
        fun a b d => by ac_rfl
      exact hac _ _ _
  have hsF : MuSetSettles (fun X => (bagStep (q₀.evaluatePlain D γ + qC.evaluatePlain D γ)
      (rowTerm s n L D γ) X).dedup) := by
    obtain ⟨j, hj⟩ := hs
    refine ⟨j, ?_⟩
    rw [← muIter_eq_iterate, ← muIter_eq_iterate, ← hround, ← hround, muIter_eq_iterate,
      muIter_eq_iterate]
    exact hj
  have hfix : (AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ
      = muFix (fun X => (bagStep (q₀.evaluatePlain D γ + qC.evaluatePlain D γ)
          (rowTerm s n L D γ) X).dedup) :=
    muFix_congr_of_iterate hs hround
  have hN : (counters EQ K D γ).toFinset.card
      = (unaryVals (EQ.evaluatePlain D γ)).toFinset.card ^ K :=
    card_toFinset_pow EQ D γ K
  have hXN := muIter_eq_muFix_of_card_le _
    (bagStep_mono (q₀.evaluatePlain D γ + qC.evaluatePlain D γ) (rowTerm s n L D γ)) hsF
    (N := (counters EQ K D γ).toFinset.card) (by rw [← hfix, hN]; exact hcard)
  -- both sides are sets with the same members
  have hnd₁ : ((simResult s s' n K EQ BQ L).evaluatePlain D γ : Multiset (Tuple T n)).Nodup := by
    rw [simResult, evaluatePlain_dedupG]
    exact Multiset.nodup_dedup _
  have hnd₂ : ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ : Multiset (Tuple T n)).Nodup := by
    show (muIter _ (muFixIdx _)).Nodup
    rw [muIter_eq_iterate]
    exact nodup_iterate_dedup _ _
  refine ⟨(Multiset.Nodup.ext hnd₁ hnd₂).mpr fun x => ?_, fun j t hj ht => ?_⟩
  · refine Iff.trans (mem_simResult s s' n K EQ BQ L hL hLs hEs D γ hE _ hB x) ?_
    rw [hfix, ← hXN, mem_muIter_bagStep]
  · rw [hfix, ← hXN]
    rw [hB] at ht
    exact (mem_muIter_bagStep _ _ _ _).mpr ⟨j, hj, ht⟩

end AggQueryIn

omit [ValueType T] in
/-- A leaf's name is a name of the query. -/
theorem AggQueryIn.snd_mem_names_of_mem_leaves :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
        (p : ℕ × String),
      p ∈ q.leaves → p.2 ∈ q.names := by
  intro c n κ l q
  induction q with
  | Rel k s =>
    intro p hp
    rw [List.mem_singleton.mp hp]
    exact Finset.mem_singleton_self s
  | Hole k s =>
    intro p hp
    rw [List.mem_singleton.mp hp]
    exact Finset.mem_singleton_self s
  | Param pv ρ => exact fun p hp => absurd hp List.not_mem_nil
  | Empty => exact fun p hp => absurd hp (List.not_mem_nil)
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro p hp
    exact (List.mem_append.mp hp).elim (fun h => Finset.mem_union_left _ (ih₁ p h))
      (fun h => Finset.mem_union_right _ (ih₂ p h))
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro p hp
    exact (List.mem_append.mp hp).elim (fun h => Finset.mem_union_left _ (ih₁ p h))
      (fun h => Finset.mem_union_right _ (ih₂ p h))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro p hp
    exact (List.mem_append.mp hp).elim (fun h => Finset.mem_union_left _ (ih₁ p h))
      (fun h => Finset.mem_union_right _ (ih₂ p h))
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro p hp
    exact (List.mem_append.mp hp).elim (fun h => Finset.mem_union_left _ (ih₁ p h))
      (fun h => Finset.mem_union_right _ (ih₂ p h))
  | Explode k hk q ih => exact ih
  | Retag hk q ih => exact ih
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro p hp
    exact Finset.mem_insert_of_mem ((List.mem_append.mp hp).elim
      (fun h => Finset.mem_union_left _ (ih₀ p h))
      (fun h => Finset.mem_union_right _ (ih₁ p (List.mem_of_mem_filter h))))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro p hp
    exact Finset.mem_insert_of_mem ((List.mem_append.mp hp).elim
      (fun h => Finset.mem_union_left _ (ih₀ p h))
      (fun h => Finset.mem_union_right _ (ih₁ p (List.mem_of_mem_filter h))))
  | Gamma is ts fs q keep ord ih => exact ih
  | GammaScalar ts fs q ord ih => exact ih
  | GammaNest is his p fn q ih => exact ih
  | ProvSum is his t q ih => exact ih
  | GammaTok is his ts fs a q keep ih => exact ih
  | Win P O o w t fw q hrr dist keep ih => exact ih
  | WinExpr P O o ws ts fs g q keeps ih => exact ih

omit [ValueType T] in
/-- A query over a schema reads each leaf at the arity the schema
declares; a body reads its recursive name at the recursion's arity. -/
theorem AggQueryIn.find_of_mem_leaves_of_overSchema :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
        (q : AggQueryIn T c n κ l) {sch : Schema},
      q.overSchema sch → ∀ p ∈ q.leaves, sch p.2 = some p.1 := by
  intro c n κ l q
  induction q with
  | Rel k s =>
    intro sch ho p hp
    rw [List.mem_singleton.mp hp]
    exact ho
  | Hole k s =>
    intro sch ho p hp
    rw [List.mem_singleton.mp hp]
    exact ho
  | Param pv ρ => exact fun _ p hp => absurd hp List.not_mem_nil
  | Empty => exact fun _ p hp => absurd hp (List.not_mem_nil)
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro sch ho p hp
    exact (List.mem_append.mp hp).elim (ih₁ ho.1 p) (ih₂ ho.2 p)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro sch ho p hp
    exact (List.mem_append.mp hp).elim (ih₁ ho.1 p) (ih₂ ho.2 p)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro sch ho p hp
    exact (List.mem_append.mp hp).elim (ih₁ ho.1 p) (ih₂ ho.2 p)
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro sch ho p hp
    exact (List.mem_append.mp hp).elim (ih₁ ho.1 p) (ih₂ ho.2 p)
  | Explode k hk q ih => exact ih
  | Retag hk q ih => exact ih
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro sch ho p hp
    refine (List.mem_append.mp hp).elim (ih₀ ho.2.1 p) (fun h => ?_)
    obtain ⟨h, hne⟩ := List.mem_filter.mp h
    have h' : (if p.2 = s then some _ else sch p.2) = some p.1 := ih₁ ho.2.2.2 p h
    by_cases hs : p.2 = s
    · rw [ite_eq_left hs, Option.some.injEq] at h'
      exact absurd (Prod.ext h'.symm hs) (by simpa using hne)
    · rwa [ite_eq_right hs] at h'
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro sch ho p hp
    refine (List.mem_append.mp hp).elim (ih₀ ho.2.1 p) (fun h => ?_)
    obtain ⟨h, hne⟩ := List.mem_filter.mp h
    have h' : (if p.2 = s then some _ else sch p.2) = some p.1 := ih₁ ho.2.2.2 p h
    by_cases hs : p.2 = s
    · rw [ite_eq_left hs, Option.some.injEq] at h'
      exact absurd (Prod.ext h'.symm hs) (by simpa using hne)
    · rwa [ite_eq_right hs] at h'
  | Gamma is ts fs q keep ord ih => exact ih
  | GammaScalar ts fs q ord ih => exact ih
  | GammaNest is his p fn q ih => exact ih
  | ProvSum is his t q ih => exact ih
  | GammaTok is his ts fs a q keep ih => exact ih
  | Win P O o w t fw q hrr dist keep ih => exact ih
  | WinExpr P O o ws ts fs g q keeps ih => exact ih

/-! ## The counter relation

The simulation runs its counter over `E^K` for a unary relation `E` of
non-null values with `|E|^K` at least the size of the fixpoint. `E` is
computed from what the fixpoint's values can be – the values of the base
(so of `q₀` and of `C`), of the relations the term reads off the instance,
the term's constants and the context's values – with two constants of the
domain so that it holds at least two values, and a selection keeping the
non-null ones. -/

namespace AggQueryIn

variable {c : ℕ}

/-- The sum of a list of queries. -/
def listSum {n : ℕ} : List (AggQueryIn T c n (ColKind.allReg n)) →
    AggQueryIn T c n (ColKind.allReg n)
  | [] => emptyRel n
  | q :: l => AggQueryIn.Sum q (listSum l)

theorem mem_listSum {n : ℕ} :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))) (D : Database T) (γ : Fin c → T)
      (x : Tuple T n), Multiset.Mem ((listSum l).evaluatePlain D γ) x
        ↔ ∃ q ∈ l, Multiset.Mem (q.evaluatePlain D γ) x
  | [], D, γ, x => by
    rw [listSum, evaluatePlain_emptyRel]
    exact ⟨fun h => absurd h (Multiset.notMem_zero x),
      fun ⟨_, hq, _⟩ => absurd hq List.not_mem_nil⟩
  | q :: l, D, γ, x => by
    have ih := mem_listSum l D γ x
    show Multiset.Mem ((AggQueryIn.Sum q (listSum l)).evaluatePlain D γ) x ↔ _
    rw [AggQueryIn.evaluatePlain]
    refine Iff.trans Multiset.mem_add ?_
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_congr Iff.rfl ih

theorem settlesAt_listSum {n : ℕ} :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))) (D : Database T) (γ : Fin c → T),
      (∀ q ∈ l, q.SettlesAt D γ) → (listSum l).SettlesAt D γ
  | [], D, γ, _ => settlesAt_emptyRel n D γ
  | q :: l, D, γ, h => ⟨h q (List.mem_cons_self), settlesAt_listSum l D γ
      (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))⟩

theorem usesOnly_listSum {S : Set OpKind} (hS : sumMuOps ⊆ S) {n : ℕ} :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))), (∀ q ∈ l, q.usesOnly S) →
      (listSum l).usesOnly (insert OpKind.union S)
  | [], _ => AggQueryIn.usesOnly_mono (Set.subset_insert _ _) _ (usesOnly_emptyRel hS n)
  | q :: l, h => ⟨Set.mem_insert _ _,
      AggQueryIn.usesOnly_mono (Set.subset_insert _ _) _ (h q List.mem_cons_self),
      usesOnly_listSum hS l (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))⟩

theorem hygienic_listSum {n : ℕ} :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))), (∀ q ∈ l, q.hygienic) →
      (listSum l).hygienic
  | [], _ => hygienic_emptyRel n
  | q :: l, h => ⟨h q List.mem_cons_self,
      hygienic_listSum l (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))⟩

theorem inSig_listSum {Θ : Set (SeqAggFunc T)} {n : ℕ} :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))), (∀ q ∈ l, q.inSig Θ) →
      (listSum l).inSig Θ
  | [], _ => inSig_emptyRel Θ n
  | q :: l, h => ⟨h q List.mem_cons_self,
      inSig_listSum l (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))⟩

theorem sumsAllReg_listSum {n : ℕ} :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))), (∀ q ∈ l, q.sumsAllReg) →
      (listSum l).sumsAllReg
  | [], _ => by rw [listSum, emptyRel, AggQueryIn.sumsAllReg_castKind]; trivial
  | q :: l, h => ⟨rfl, h q List.mem_cons_self,
      sumsAllReg_listSum l (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))⟩

theorem winsDerivable_listSum {n : ℕ} :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))), (∀ q ∈ l, q.WinsDerivable) →
      (listSum l).WinsDerivable
  | [], _ => winsDerivable_emptyRel n
  | q :: l, h => ⟨h q List.mem_cons_self,
      winsDerivable_listSum l (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))⟩

theorem overSchema_listSum {sch : Schema} {n : ℕ} :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))), (∀ q ∈ l, q.overSchema sch) →
      (listSum l).overSchema sch
  | [], _ => overSchema_emptyRel sch n
  | q :: l, h => ⟨h q List.mem_cons_self,
      overSchema_listSum l (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))⟩

theorem mem_names_listSum {n : ℕ} :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))) (x : String),
      x ∈ (listSum l).names → ∃ q ∈ l, x ∈ q.names
  | [], x, h => by rw [listSum, names_emptyRel] at h; exact absurd h (Finset.notMem_empty x)
  | q :: l, x, h => by
    rcases Finset.mem_union.mp h with h | h
    · exact ⟨q, List.mem_cons_self, h⟩
    · obtain ⟨q', hq', h'⟩ := mem_names_listSum l x h
      exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩

theorem noMention_listSum {n : ℕ} (t : String) :
    ∀ (l : List (AggQueryIn T c n (ColKind.allReg n))), (∀ q ∈ l, q.noMention t) →
      (listSum l).noMention t
  | [], _ => noMention_emptyRel n t
  | q :: l, h => ⟨h q List.mem_cons_self,
      noMention_listSum t l (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))⟩

/-- Column `i` of a query, as a unary relation. -/
def colRel {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n)) (i : Fin n) :
    AggQueryIn T c 1 (ColKind.allReg 1) :=
  (AggQueryIn.Proj (fun _ : Fin 1 => ProjColIn.term (TermGIn.index i rfl)) q).castKind
    (funext fun _ => rfl)

/-- A constant, as a one-row unary relation. -/
def constRel (a : T) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  (AggQueryIn.Proj (fun _ : Fin 1 => ProjColIn.term (TermGIn.const a))
    (unitC : AggQueryIn T c 0 _)).castKind (funext fun _ => rfl)

/-- A context value, as a one-row unary relation. -/
def outerRel (j : Fin c) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  (AggQueryIn.Proj (fun _ : Fin 1 => ProjColIn.term (TermGIn.outer j))
    (unitC : AggQueryIn T c 0 _)).castKind (funext fun _ => rfl)

/-- `x IS NOT NULL`, spelled `x = x`: the comparison is unknown exactly
at the null. -/
def nonNullPred : GenPredIn T c (ColKind.allReg 1) :=
  GenPredIn.cmp CompOp.eq (TermGIn.index 0 rfl) (TermGIn.index 0 rfl)

theorem holdsPlain_nonNullPred (y : Tuple T 1) (γ : Fin c → T) :
    (nonNullPred (c := c)).holdsPlain y γ ↔ ValueType.isNull (y 0) = false := by
  show CompOp.eq.eval3 (y 0) (y 0) = Kleene.true ↔ _
  by_cases h : ValueType.isNull (y 0) = true
  · rw [CompOp.eval3_of_isNull_left rfl h]
    simp [h]
  · have h' : ValueType.isNull (y 0) = false := Bool.eq_false_iff.mpr h
    rw [CompOp.eval3_eq_true_iff _ h' h']
    simp [h', CompOp.eval]

/-- The unary relations the counter relation is the union of. -/
def counterParts {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n)) (ls : List (ℕ × String))
    (cs : List T) : List (AggQueryIn T c 1 (ColKind.allReg 1)) :=
  (List.finRange n).map (colRel B)
    ++ ls.flatMap (fun p => (List.finRange p.1).map (colRel (AggQueryIn.Rel p.1 p.2)))
    ++ cs.map constRel ++ (List.finRange c).map outerRel

/-- **The counter relation**: the non-null values among the columns of
`B`, the columns of the relations `ls` names, the constants `cs` and the
context's values. -/
def counterRel {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n)) (ls : List (ℕ × String))
    (cs : List T) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  AggQueryIn.Sel nonNullPred (listSum (counterParts B ls cs))

theorem mem_unaryVals_colRel {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n)) (i : Fin n)
    (D : Database T) (γ : Fin c → T) (u : Tuple T n) (hu : Multiset.Mem (q.evaluatePlain D γ) u) :
    u i ∈ unaryVals ((colRel q i).evaluatePlain D γ) := by
  rw [colRel, AggQueryIn.evaluatePlain_castKind]
  show u i ∈ Multiset.map _ (Multiset.map _ (q.evaluatePlain D γ))
  rw [Multiset.map_map]
  exact Multiset.mem_map.mpr ⟨u, hu, rfl⟩

theorem mem_unaryVals_constRel (a : T) (D : Database T) (γ : Fin c → T) :
    a ∈ unaryVals ((constRel (c := c) a).evaluatePlain D γ) := by
  rw [constRel, AggQueryIn.evaluatePlain_castKind]
  show a ∈ Multiset.map _ (Multiset.map _ ((unitC : AggQueryIn T c 0 _).evaluatePlain D γ))
  rw [evaluatePlain_unitC D γ (fun j => j.elim0), Multiset.map_singleton, Multiset.map_singleton]
  exact Multiset.mem_singleton_self _

theorem mem_unaryVals_outerRel (j : Fin c) (D : Database T) (γ : Fin c → T) :
    γ j ∈ unaryVals ((outerRel (T := T) j).evaluatePlain D γ) := by
  rw [outerRel, AggQueryIn.evaluatePlain_castKind]
  show γ j ∈ Multiset.map _ (Multiset.map _ ((unitC : AggQueryIn T c 0 _).evaluatePlain D γ))
  rw [evaluatePlain_unitC D γ (fun j => j.elim0), Multiset.map_singleton, Multiset.map_singleton]
  exact Multiset.mem_singleton_self _

/-- Membership in the counter relation. -/
theorem mem_unaryVals_counterRel {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n))
    (ls : List (ℕ × String)) (cs : List T) (D : Database T) (γ : Fin c → T) (a : T) :
    a ∈ unaryVals ((counterRel B ls cs).evaluatePlain D γ)
      ↔ ValueType.isNull a = false
        ∧ ∃ q ∈ counterParts B ls cs, a ∈ unaryVals (q.evaluatePlain D γ) := by
  rw [counterRel]
  show a ∈ Multiset.map _ (Multiset.filter _ ((listSum (counterParts B ls cs)).evaluatePlain D γ))
    ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy, hnn⟩ := Multiset.mem_filter.mp hy
    refine ⟨(holdsPlain_nonNullPred y γ).mp hnn, ?_⟩
    obtain ⟨q, hq, hyq⟩ := (mem_listSum _ D γ y).mp hy
    exact ⟨q, hq, Multiset.mem_map.mpr ⟨y, hyq, rfl⟩⟩
  · rintro ⟨hnn, q, hq, ha⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ha
    refine ⟨y, Multiset.mem_filter.mpr ⟨?_, (holdsPlain_nonNullPred y γ).mpr hnn⟩, rfl⟩
    exact (mem_listSum _ D γ y).mpr ⟨q, hq, hy⟩

/-- Every value of the counter relation is non-null. -/
theorem nonNull_counterRel {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n))
    (ls : List (ℕ × String)) (cs : List T) (D : Database T) (γ : Fin c → T) :
    ∀ e ∈ unaryVals ((counterRel B ls cs).evaluatePlain D γ), ValueType.isNull e = false :=
  fun e he => ((mem_unaryVals_counterRel B ls cs D γ e).mp he).1

/-- A non-null value of a column of `B` is a counter value. -/
theorem mem_counterRel_of_mem_B {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n))
    (ls : List (ℕ × String)) (cs : List T) (D : Database T) (γ : Fin c → T) (u : Tuple T n)
    (hu : Multiset.Mem (B.evaluatePlain D γ) u) (i : Fin n) (hnn : ValueType.isNull (u i) = false) :
    u i ∈ unaryVals ((counterRel B ls cs).evaluatePlain D γ) :=
  (mem_unaryVals_counterRel B ls cs D γ _).mpr ⟨hnn, colRel B i,
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))),
    mem_unaryVals_colRel B i D γ u hu⟩

/-- A non-null value of a relation `ls` names is a counter value. -/
theorem mem_counterRel_of_mem_leaf {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n))
    (ls : List (ℕ × String)) (cs : List T) (D : Database T) (γ : Fin c → T) (p : ℕ × String)
    (hp : p ∈ ls) (r : Relation T p.1) (hr : D.find p.1 p.2 = some r) (u : Tuple T p.1)
    (hu : Multiset.Mem r u) (i : Fin p.1) (hnn : ValueType.isNull (u i) = false) :
    u i ∈ unaryVals ((counterRel B ls cs).evaluatePlain D γ) := by
  obtain ⟨k, t⟩ := p
  refine (mem_unaryVals_counterRel B ls cs D γ _).mpr ⟨hnn, colRel (AggQueryIn.Rel k t) i,
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(k, t), hp, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩))),
    mem_unaryVals_colRel _ i D γ u ?_⟩
  show Multiset.Mem (match D.find k t with
    | none => (0 : Relation T k) | some rn => rn) u
  rw [hr]
  exact hu

/-- A non-null constant of `cs` is a counter value. -/
theorem mem_counterRel_of_mem_consts {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n))
    (ls : List (ℕ × String)) (cs : List T) (D : Database T) (γ : Fin c → T) (a : T)
    (ha : a ∈ cs) (hnn : ValueType.isNull a = false) :
    a ∈ unaryVals ((counterRel B ls cs).evaluatePlain D γ) :=
  (mem_unaryVals_counterRel B ls cs D γ _).mpr ⟨hnn, constRel a,
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩)),
    mem_unaryVals_constRel a D γ⟩

/-- A non-null context value is a counter value. -/
theorem mem_counterRel_of_outer {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n))
    (ls : List (ℕ × String)) (cs : List T) (D : Database T) (γ : Fin c → T) (j : Fin c)
    (hnn : ValueType.isNull (γ j) = false) :
    γ j ∈ unaryVals ((counterRel B ls cs).evaluatePlain D γ) :=
  (mem_unaryVals_counterRel B ls cs D γ _).mpr ⟨hnn, outerRel j,
    List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩),
    mem_unaryVals_outerRel j D γ⟩

end AggQueryIn

namespace AggQueryIn

variable {c : ℕ}

omit [ValueType T] in
/-- The parts of the counter relation, one by one. -/
theorem mem_counterParts {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n)) (ls : List (ℕ × String))
    (cs : List T) (q : AggQueryIn T c 1 (ColKind.allReg 1)) (hq : q ∈ counterParts B ls cs) :
    (∃ i, q = colRel B i) ∨ (∃ p ∈ ls, ∃ i, q = colRel (AggQueryIn.Rel p.1 p.2) i)
      ∨ (∃ a ∈ cs, q = constRel a) ∨ (∃ j, q = outerRel j) := by
  rcases List.mem_append.mp hq with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
        exact Or.inl ⟨i, rfl⟩
      · obtain ⟨p, hp, h⟩ := List.mem_flatMap.mp h
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
        exact Or.inr (Or.inl ⟨p, hp, i, rfl⟩)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      exact Or.inr (Or.inr (Or.inl ⟨a, ha, rfl⟩))
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
    exact Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))

theorem settlesAt_unitC (D : Database T) (γ : Fin c → T) :
    (unitC : AggQueryIn T c 0 _).SettlesAt D γ := by
  rw [unitC, AggQueryIn.settlesAt_castKind]; trivial

omit [ValueType T] in
theorem hygienic_unitC : (unitC : AggQueryIn T c 0 _).hygienic := by
  rw [unitC, AggQueryIn.hygienic_castKind]; trivial

theorem winsDerivable_unitC : (unitC : AggQueryIn T c 0 _).WinsDerivable := by
  rw [unitC, AggQueryIn.winsDerivable_castKind]; trivial

omit [ValueType T] in
theorem sumsAllReg_unitC : (unitC : AggQueryIn T c 0 _).sumsAllReg := by
  rw [unitC, AggQueryIn.sumsAllReg_castKind]; trivial

omit [ValueType T] in
theorem names_unitC : (unitC : AggQueryIn T c 0 _).names = ∅ := by
  rw [unitC, AggQueryIn.names_castKind]; rfl

omit [ValueType T] in
theorem noMention_unitC (t : String) : (unitC : AggQueryIn T c 0 _).noMention t := by
  rw [unitC, AggQueryIn.noMention_castKind]; trivial

section CounterStructure

variable {n : ℕ} (B : AggQueryIn T c n (ColKind.allReg n)) (ls : List (ℕ × String)) (cs : List T)

theorem settlesAt_counterRel (D : Database T) (γ : Fin c → T) (hB : B.SettlesAt D γ) :
    (counterRel B ls cs).SettlesAt D γ := by
  refine settlesAt_listSum _ D γ (fun q hq => ?_)
  rcases mem_counterParts B ls cs q hq with ⟨i, rfl⟩ | ⟨p, _, i, rfl⟩ | ⟨a, _, rfl⟩ | ⟨j, rfl⟩
  · rw [colRel, AggQueryIn.settlesAt_castKind]; exact hB
  · rw [colRel, AggQueryIn.settlesAt_castKind]; trivial
  · rw [constRel, AggQueryIn.settlesAt_castKind]; exact settlesAt_unitC D γ
  · rw [outerRel, AggQueryIn.settlesAt_castKind]; exact settlesAt_unitC D γ

theorem usesOnly_counterRel {S : Set OpKind} (hS : sumMuOps ⊆ S) (hB : B.usesOnly S) :
    (counterRel B ls cs).usesOnly (insert OpKind.union S) := by
  have hproj : OpKind.proj ∈ S := hS (by simp [sumMuOps])
  refine ⟨Set.mem_insert_of_mem _ (hS (by simp [sumMuOps])),
    usesOnly_listSum hS _ (fun q hq => ?_)⟩
  rcases mem_counterParts B ls cs q hq with ⟨i, rfl⟩ | ⟨p, _, i, rfl⟩ | ⟨a, _, rfl⟩ | ⟨j, rfl⟩
  · rw [colRel, AggQueryIn.usesOnly_castKind]; exact ⟨⟨hproj, fun _ => rfl⟩, hB⟩
  · rw [colRel, AggQueryIn.usesOnly_castKind]; exact ⟨⟨hproj, fun _ => rfl⟩, trivial⟩
  · rw [constRel, AggQueryIn.usesOnly_castKind]; exact ⟨⟨hproj, fun _ => rfl⟩, usesOnly_unitC hS⟩
  · rw [outerRel, AggQueryIn.usesOnly_castKind]; exact ⟨⟨hproj, fun _ => rfl⟩, usesOnly_unitC hS⟩

theorem hygienic_counterRel (hB : B.hygienic) : (counterRel B ls cs).hygienic := by
  refine hygienic_listSum _ (fun q hq => ?_)
  rcases mem_counterParts B ls cs q hq with ⟨i, rfl⟩ | ⟨p, _, i, rfl⟩ | ⟨a, _, rfl⟩ | ⟨j, rfl⟩
  · rw [colRel, AggQueryIn.hygienic_castKind]; exact hB
  · rw [colRel, AggQueryIn.hygienic_castKind]; trivial
  · rw [constRel, AggQueryIn.hygienic_castKind]; exact hygienic_unitC
  · rw [outerRel, AggQueryIn.hygienic_castKind]; exact hygienic_unitC

theorem inSig_counterRel {Θ : Set (SeqAggFunc T)} (hB : B.inSig Θ) :
    (counterRel B ls cs).inSig Θ := by
  refine ⟨rfl, inSig_listSum _ (fun q hq => ?_)⟩
  rcases mem_counterParts B ls cs q hq with ⟨i, rfl⟩ | ⟨p, _, i, rfl⟩ | ⟨a, _, rfl⟩ | ⟨j, rfl⟩
  · rw [colRel, AggQueryIn.inSig_castKind]; exact ⟨fun _ => rfl, hB⟩
  · rw [colRel, AggQueryIn.inSig_castKind]; exact ⟨fun _ => rfl, trivial⟩
  · rw [constRel, AggQueryIn.inSig_castKind]; exact ⟨fun _ => rfl, inSig_unitC Θ⟩
  · rw [outerRel, AggQueryIn.inSig_castKind]; exact ⟨fun _ => rfl, inSig_unitC Θ⟩

theorem sumsAllReg_counterRel (hB : B.sumsAllReg) : (counterRel B ls cs).sumsAllReg := by
  refine sumsAllReg_listSum _ (fun q hq => ?_)
  rcases mem_counterParts B ls cs q hq with ⟨i, rfl⟩ | ⟨p, _, i, rfl⟩ | ⟨a, _, rfl⟩ | ⟨j, rfl⟩
  · rw [colRel, AggQueryIn.sumsAllReg_castKind]; exact hB
  · rw [colRel, AggQueryIn.sumsAllReg_castKind]; trivial
  · rw [constRel, AggQueryIn.sumsAllReg_castKind]; exact sumsAllReg_unitC
  · rw [outerRel, AggQueryIn.sumsAllReg_castKind]; exact sumsAllReg_unitC

theorem winsDerivable_counterRel (hB : B.WinsDerivable) : (counterRel B ls cs).WinsDerivable := by
  refine winsDerivable_listSum _ (fun q hq => ?_)
  rcases mem_counterParts B ls cs q hq with ⟨i, rfl⟩ | ⟨p, _, i, rfl⟩ | ⟨a, _, rfl⟩ | ⟨j, rfl⟩
  · rw [colRel, AggQueryIn.winsDerivable_castKind]; exact hB
  · rw [colRel, AggQueryIn.winsDerivable_castKind]; trivial
  · rw [constRel, AggQueryIn.winsDerivable_castKind]; exact winsDerivable_unitC
  · rw [outerRel, AggQueryIn.winsDerivable_castKind]; exact winsDerivable_unitC

theorem overSchema_counterRel {sch : Schema} (hB : B.overSchema sch)
    (hls : ∀ p ∈ ls, sch p.2 = some p.1) : (counterRel B ls cs).overSchema sch := by
  refine overSchema_listSum _ (fun q hq => ?_)
  rcases mem_counterParts B ls cs q hq with ⟨i, rfl⟩ | ⟨p, hp, i, rfl⟩ | ⟨a, _, rfl⟩ | ⟨j, rfl⟩
  · rw [colRel, AggQueryIn.overSchema_castKind]; exact hB
  · rw [colRel, AggQueryIn.overSchema_castKind]; exact hls p hp
  · rw [constRel, AggQueryIn.overSchema_castKind]; exact overSchema_unitC sch
  · rw [outerRel, AggQueryIn.overSchema_castKind]; exact overSchema_unitC sch

theorem mem_names_counterRel (x : String) (hx : x ∈ (counterRel B ls cs).names) :
    x ∈ B.names ∨ ∃ p ∈ ls, x = p.2 := by
  obtain ⟨q, hq, hx⟩ := mem_names_listSum _ x hx
  rcases mem_counterParts B ls cs q hq with ⟨i, rfl⟩ | ⟨p, hp, i, rfl⟩ | ⟨a, _, rfl⟩ | ⟨j, rfl⟩
  · rw [colRel, AggQueryIn.names_castKind] at hx; exact Or.inl hx
  · rw [colRel, AggQueryIn.names_castKind] at hx
    exact Or.inr ⟨p, hp, Finset.mem_singleton.mp hx⟩
  · rw [constRel, AggQueryIn.names_castKind] at hx
    exact absurd ((names_unitC (T := T) (c := c)) ▸ hx) (Finset.notMem_empty x)
  · rw [outerRel, AggQueryIn.names_castKind] at hx
    exact absurd ((names_unitC (T := T) (c := c)) ▸ hx) (Finset.notMem_empty x)

theorem noMention_counterRel (t : String) (hB : B.noMention t) (hls : ∀ p ∈ ls, p.2 ≠ t) :
    (counterRel B ls cs).noMention t := by
  refine noMention_listSum t _ (fun q hq => ?_)
  rcases mem_counterParts B ls cs q hq with ⟨i, rfl⟩ | ⟨p, hp, i, rfl⟩ | ⟨a, _, rfl⟩ | ⟨j, rfl⟩
  · rw [colRel, AggQueryIn.noMention_castKind]; exact hB
  · rw [colRel, AggQueryIn.noMention_castKind]; exact hls p hp
  · rw [constRel, AggQueryIn.noMention_castKind]; exact noMention_unitC t
  · rw [outerRel, AggQueryIn.noMention_castKind]; exact noMention_unitC t

end CounterStructure

end AggQueryIn

/-! ## What the simulation is made of

The structural facts the pass needs of the simulation: which classes it
uses, that its recursion is restricted, its signature, its schema, its
names. Each is read off its parts. -/

namespace AggQueryIn

variable {c : ℕ}

section SubstRel

variable {s : String} {n : ℕ} (pv : Fin n → T ⊕ Fin c)

omit [ValueType T] in
theorem usesOnly_substRel {S : Set OpKind} (hρ : (AggQueryIn.Param pv
    (ColKind.allReg n) : AggQueryIn T c n (ColKind.allReg n)).usesOnly S) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      q.usesOnly S → (AggQueryIn.substRel s pv q).usesOnly S := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' =>
    rintro ⟨rfl, rfl⟩ _
    rw [AggQueryIn.substRel, dite_eq_left ⟨rfl, rfl⟩, AggQueryIn.usesOnly_castIdx]
    exact hρ
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h hq => ⟨hq.1, ih pv hρ h hq.2⟩
  | Sel φ q _ ih => exact fun h hq => ⟨hq.1, ih pv hρ h.2 hq.2⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) hq
    · rw [AggQueryIn.substRel, AggQueryIn.usesOnly_castIdx]
      refine ⟨hq.1, ih₁ pv hρ h₁ hq.2.1, ?_⟩
      rw [AggQueryIn.substRel_of_noMention pv q₂ h₂]; exact hq.2.2
    · rw [AggQueryIn.substRel, AggQueryIn.usesOnly_castIdx]
      refine ⟨hq.1, ?_, ih₂ pv hρ h₂ hq.2.2⟩
      rw [AggQueryIn.substRel_of_noMention pv q₁ h₁]; exact hq.2.1
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h hq => ⟨hq.1, ih₁ pv hρ h.1 hq.2.1, hq.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h hq => ih pv hρ h hq
  | Retag hk q ih => exact fun h hq => ih pv hρ h hq
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

omit [ValueType T] in
theorem hygienic_substRel (hρ : (AggQueryIn.Param pv (ColKind.allReg n) : AggQueryIn T c n
    (ColKind.allReg n)).hygienic) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      q.hygienic → (AggQueryIn.substRel s pv q).hygienic := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' =>
    rintro ⟨rfl, rfl⟩ _
    rw [AggQueryIn.substRel, dite_eq_left ⟨rfl, rfl⟩, AggQueryIn.hygienic_castIdx]
    exact hρ
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h hq => ih pv hρ h hq
  | Sel φ q _ ih => exact fun h hq => ih pv hρ h.2 hq
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) hq
    · rw [AggQueryIn.substRel, AggQueryIn.hygienic_castIdx]
      refine ⟨ih₁ pv hρ h₁ hq.1, ?_⟩
      rw [AggQueryIn.substRel_of_noMention pv q₂ h₂]; exact hq.2
    · rw [AggQueryIn.substRel, AggQueryIn.hygienic_castIdx]
      refine ⟨?_, ih₂ pv hρ h₂ hq.2⟩
      rw [AggQueryIn.substRel_of_noMention pv q₁ h₁]; exact hq.1
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h hq => ⟨ih₁ pv hρ h.1 hq.1, hq.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h hq => ih pv hρ h hq
  | Retag hk q ih => exact fun h hq => ih pv hρ h hq
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

theorem inSig_substRel {Θ : Set (SeqAggFunc T)} (hρ : (AggQueryIn.Param pv
    (ColKind.allReg n) : AggQueryIn T c n (ColKind.allReg n)).inSig Θ) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      q.inSig Θ → (AggQueryIn.substRel s pv q).inSig Θ := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' =>
    rintro ⟨rfl, rfl⟩ _
    rw [AggQueryIn.substRel, dite_eq_left ⟨rfl, rfl⟩, AggQueryIn.inSig_castIdx]
    exact hρ
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h hq => ⟨hq.1, ih pv hρ h hq.2⟩
  | Sel φ q _ ih => exact fun h hq => ⟨hq.1, ih pv hρ h.2 hq.2⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) hq
    · rw [AggQueryIn.substRel, AggQueryIn.inSig_castIdx]
      refine ⟨ih₁ pv hρ h₁ hq.1, ?_⟩
      rw [AggQueryIn.substRel_of_noMention pv q₂ h₂]; exact hq.2
    · rw [AggQueryIn.substRel, AggQueryIn.inSig_castIdx]
      refine ⟨?_, ih₂ pv hρ h₂ hq.2⟩
      rw [AggQueryIn.substRel_of_noMention pv q₁ h₁]; exact hq.1
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h hq => ⟨ih₁ pv hρ h.1 hq.1, hq.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h hq => ih pv hρ h hq
  | Retag hk q ih => exact fun h hq => ih pv hρ h hq
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

omit [ValueType T] in
theorem sumsAllReg_substRel (hρ : (AggQueryIn.Param pv (ColKind.allReg n) : AggQueryIn T c n
    (ColKind.allReg n)).sumsAllReg) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      q.sumsAllReg → (AggQueryIn.substRel s pv q).sumsAllReg := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' =>
    rintro ⟨rfl, rfl⟩ _
    rw [AggQueryIn.substRel, dite_eq_left ⟨rfl, rfl⟩, AggQueryIn.sumsAllReg_castIdx]
    exact hρ
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h hq => ih pv hρ h hq
  | Sel φ q _ ih => exact fun h hq => ih pv hρ h.2 hq
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) hq
    · rw [AggQueryIn.substRel, AggQueryIn.sumsAllReg_castIdx]
      refine ⟨ih₁ pv hρ h₁ hq.1, ?_⟩
      rw [AggQueryIn.substRel_of_noMention pv q₂ h₂]; exact hq.2
    · rw [AggQueryIn.substRel, AggQueryIn.sumsAllReg_castIdx]
      refine ⟨?_, ih₂ pv hρ h₂ hq.2⟩
      rw [AggQueryIn.substRel_of_noMention pv q₁ h₁]; exact hq.1
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h hq => ⟨ih₁ pv hρ h.1 hq.1, hq.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h hq => ih pv hρ h hq
  | Retag hk q ih => exact fun h hq => ih pv hρ h hq
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

omit [ValueType T] in
/-- **The substituted term is well-formed over the ambient schema**: the
term is over the schema with the recursive name declared, and the
substitute is over the schema. -/
theorem overSchema_substRel {sch : Schema} (hρ : (AggQueryIn.Param pv
    (ColKind.allReg n) : AggQueryIn T c n (ColKind.allReg n)).overSchema sch) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      q.overSchema (sch.update s n) → (AggQueryIn.substRel s pv q).overSchema sch := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' =>
    rintro ⟨rfl, rfl⟩ _
    rw [AggQueryIn.substRel, dite_eq_left ⟨rfl, rfl⟩, AggQueryIn.overSchema_castIdx]
    exact hρ
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h hq => ih pv hρ h hq
  | Sel φ q _ ih => exact fun h hq => ih pv hρ h.2 hq
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) hq
    · rw [AggQueryIn.substRel, AggQueryIn.overSchema_castIdx]
      refine ⟨ih₁ pv hρ h₁ hq.1, ?_⟩
      rw [AggQueryIn.substRel_of_noMention pv q₂ h₂]
      exact AggQueryIn.overSchema_of_update_of_noMention q₂ (fun _ h => by simp at h) h₂ hq.2
    · rw [AggQueryIn.substRel, AggQueryIn.overSchema_castIdx]
      refine ⟨?_, ih₂ pv hρ h₂ hq.2⟩
      rw [AggQueryIn.substRel_of_noMention pv q₁ h₁]
      exact AggQueryIn.overSchema_of_update_of_noMention q₁ (fun _ h => by simp at h) h₁ hq.1
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun h hq => ⟨ih₁ pv hρ h.1 hq.1,
      AggQueryIn.overSchema_of_update_of_noMention q₂ (fun _ h => by simp at h) h.2 hq.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h hq => ih pv hρ h hq
  | Retag hk q ih => exact fun h hq => ih pv hρ h hq
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

omit [ValueType T] in
theorem mem_names_substRel :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      ∀ x, x ∈ (AggQueryIn.substRel s pv q).names → x ∈ q.names ∨ x ∈ (AggQueryIn.Param pv
          (ColKind.allReg n) : AggQueryIn T c n (ColKind.allReg n)).names := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' =>
    rintro ⟨rfl, rfl⟩ x hx
    rw [AggQueryIn.substRel, dite_eq_left ⟨rfl, rfl⟩, AggQueryIn.names_castIdx] at hx
    exact Or.inr hx
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h x hx => ih pv h x hx
  | Sel φ q _ ih => exact fun h x hx => ih pv h.2 x hx
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) x hx
    · rw [AggQueryIn.substRel, AggQueryIn.names_castIdx] at hx
      rw [AggQueryIn.substRel_of_noMention pv q₂ h₂] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (ih₁ pv h₁ x hx).imp_left (Finset.mem_union_left _)
      · exact Or.inl (Finset.mem_union_right _ hx)
    · rw [AggQueryIn.substRel, AggQueryIn.names_castIdx] at hx
      rw [AggQueryIn.substRel_of_noMention pv q₁ h₁] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Or.inl (Finset.mem_union_left _ hx)
      · exact (ih₂ pv h₂ x hx).imp_left (Finset.mem_union_right _)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h x hx
    have hx : x ∈ (AggQueryIn.Apply (AggQueryIn.substRel s pv q₁) q₂).names := hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (ih₁ pv h.1 x hx).imp_left (Finset.mem_union_left _)
    · exact Or.inl (Finset.mem_union_right _ hx)
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h x hx => ih pv h x hx
  | Retag hk q ih => exact fun h x hx => ih pv h x hx
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

end SubstRel

section Pow

variable (EQ : AggQueryIn T c 1 (ColKind.allReg 1))

omit [ValueType T] in
theorem usesOnly_pow {S : Set OpKind} (hS : sumMuOps ⊆ S) (h : EQ.usesOnly S) :
    ∀ K, (pow EQ K).usesOnly S
  | 0 => usesOnly_unitC hS
  | K + 1 => by
    rw [pow]
    exact AggQueryIn.usesOnly_prodA _ _ (hS (by simp [sumMuOps])) (usesOnly_pow hS h K) h

omit [ValueType T] in
theorem hygienic_pow (h : EQ.hygienic) : ∀ K, (pow EQ K).hygienic
  | 0 => hygienic_unitC
  | K + 1 => by
    rw [pow]
    exact AggQueryIn.hygienic_prodA _ _ (hygienic_pow h K) h

theorem inSig_pow {Θ : Set (SeqAggFunc T)} (h : EQ.inSig Θ) : ∀ K, (pow EQ K).inSig Θ
  | 0 => inSig_unitC Θ
  | K + 1 => by
    rw [pow]
    exact AggQueryIn.inSig_prodA _ _ (inSig_pow h K) h

omit [ValueType T] in
theorem sumsAllReg_prodA {n₁ n₂ : ℕ} (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁))
    (q₂ : AggQueryIn T c n₂ (ColKind.allReg n₂)) (h₁ : q₁.sumsAllReg) (h₂ : q₂.sumsAllReg) :
    (AggQueryIn.prodA q₁ q₂).sumsAllReg := by
  rw [AggQueryIn.prodA, AggQueryIn.sumsAllReg_castKind]
  exact ⟨h₁, (AggQueryIn.sumsAllReg_substMap _ _).mpr h₂⟩

omit [ValueType T] in
theorem sumsAllReg_pow (h : EQ.sumsAllReg) : ∀ K, (pow EQ K).sumsAllReg
  | 0 => sumsAllReg_unitC
  | K + 1 => by
    rw [pow]
    exact sumsAllReg_prodA _ _ (sumsAllReg_pow h K) h

omit [ValueType T] in
theorem overSchema_pow {sch : Schema} (h : EQ.overSchema sch) : ∀ K, (pow EQ K).overSchema sch
  | 0 => overSchema_unitC sch
  | K + 1 => by
    rw [pow]
    exact AggQueryIn.overSchema_prodA _ _ (overSchema_pow h K) h

omit [ValueType T] in
theorem mem_names_pow : ∀ K (x : String), x ∈ (pow EQ K).names → x ∈ EQ.names
  | 0, x, hx => by
    rw [pow, names_unitC] at hx
    exact absurd hx (Finset.notMem_empty x)
  | K + 1, x, hx => by
    rw [pow, AggQueryIn.names_prodA] at hx
    exact (Finset.mem_union.mp hx).elim (mem_names_pow K x) id

end Pow

section Parts

variable (n K : ℕ)

theorem noFun_ltSel : (ltSel (T := T) (c := c) n K).noFun = true := by
  rw [ltSel, OrderSpec.ltPredOn]
  exact OrderSpec.noFun_ltPredOnOf (fun k => OrderCol.noFun_ltPred _ rfl rfl)
    (fun _ => rfl) (fun _ => rfl) _

end Parts

section DedupG

variable {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n))

omit [ValueType T] in
theorem usesOnly_dedupG {S : Set OpKind} (hg : OpKind.gamma ∈ S) (h : q.usesOnly S) :
    (dedupG q).usesOnly S := by
  rw [dedupG, AggQueryIn.usesOnly_castKind]; exact ⟨hg, h⟩

omit [ValueType T] in
theorem hygienic_dedupG (h : q.hygienic) : (dedupG q).hygienic := by
  rw [dedupG, AggQueryIn.hygienic_castKind]; exact h

theorem inSig_dedupG {Θ : Set (SeqAggFunc T)} (h : q.inSig Θ) : (dedupG q).inSig Θ := by
  rw [dedupG, AggQueryIn.inSig_castKind]
  exact ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, h⟩

omit [ValueType T] in
theorem sumsAllReg_dedupG (h : q.sumsAllReg) : (dedupG q).sumsAllReg := by
  rw [dedupG, AggQueryIn.sumsAllReg_castKind]; exact h

omit [ValueType T] in
theorem overSchema_dedupG {sch : Schema} (h : q.overSchema sch) : (dedupG q).overSchema sch := by
  rw [dedupG, AggQueryIn.overSchema_castKind]; exact h

omit [ValueType T] in
theorem names_dedupG : (dedupG q).names = q.names := by
  rw [dedupG, AggQueryIn.names_castKind]; rfl

omit [ValueType T] in
theorem noMention_dedupG (t : String) (h : q.noMention t) : (dedupG q).noMention t := by
  rw [dedupG, AggQueryIn.noMention_castKind]; exact h

end DedupG

end AggQueryIn

namespace AggQueryIn

variable {c : ℕ}

section SimStructure

variable (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
  (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
  (hL : L.recLinear s n)

include hL in
theorem usesOnly_simResult {S : Set OpKind} (hS : sumMuOps ⊆ S) (hLu : L.usesOnly S)
    (hBu : BQ.usesOnly S) (hEu : EQ.usesOnly S) : (simResult s s' n K EQ BQ L).usesOnly S := by
  have hproj : OpKind.proj ∈ S := hS (by simp [sumMuOps])
  have hsel : OpKind.sel ∈ S := hS (by simp [sumMuOps])
  have happly : OpKind.apply ∈ S := hS (by simp [sumMuOps])
  refine usesOnly_dedupG _ (hS (by simp [sumMuOps])) ?_
  rw [AggQueryIn.usesOnly_castKind]
  refine ⟨⟨hproj, fun _ => rfl⟩, hS (by simp [sumMuOps]),
    AggQueryIn.usesOnly_prodA _ _ happly hBu (usesOnly_pow EQ hS hEu K), ?_⟩
  rw [simBody, AggQueryIn.usesOnly_castKind]
  refine ⟨⟨hproj, fun _ => rfl⟩, happly, trivial, AggQueryIn.usesOnly_prodA _ _ happly ?_ ?_⟩
  · rw [AggQueryIn.usesOnly_castIdx]
    exact usesOnly_substRel (rowPv n K)
      (by exact ⟨hS (by simp [sumMuOps]), hS (by simp [sumMuOps]), hS (by simp [sumMuOps])⟩) _
          ((recLinear_substMap L _).mpr hL)
      ((AggQueryIn.usesOnly_substMap _ _).mpr hLu)
  · exact ⟨hsel, (AggQueryIn.usesOnly_substMap _ _).mpr (usesOnly_pow EQ hS hEu K)⟩

include hL in
theorem hygienic_simResult (hLr : L.hygienic) (hBr : BQ.hygienic)
    (hEr : EQ.hygienic) (hLs : L.noMention s') (hBs : BQ.noMention s')
    (hEs : EQ.noMention s') :
    (simResult s s' n K EQ BQ L).hygienic := by
  refine hygienic_dedupG _ ?_
  rw [AggQueryIn.hygienic_castKind]
  refine ⟨AggQueryIn.noMention_prodA _ _ hBs (noMention_pow EQ hEs K), ?_,
    AggQueryIn.hygienic_prodA _ _ hBr (hygienic_pow EQ hEr K), ?_⟩
  · rw [simBody, AggQueryIn.noMention_castKind]
    refine ⟨trivial, AggQueryIn.noMention_prodA _ _ ?_ ?_⟩
    · rw [AggQueryIn.noMention_castIdx]
      exact AggQueryIn.noMention_substRel (rowPv n K) (by trivial) _
        ((recLinear_substMap L _).mpr hL) (Or.inr ((AggQueryIn.noMention_substMap _ _).mpr hLs))
    · exact (AggQueryIn.noMention_substMap _ _).mpr (noMention_pow EQ hEs K)
  · rw [simBody, AggQueryIn.hygienic_castKind]
    refine ⟨trivial, AggQueryIn.hygienic_prodA _ _ ?_ ?_⟩
    · rw [AggQueryIn.hygienic_castIdx]
      exact hygienic_substRel (rowPv n K) (by trivial) _ ((recLinear_substMap L _).mpr hL)
        ((AggQueryIn.hygienic_substMap _ _).mpr hLr)
    · exact (AggQueryIn.hygienic_substMap _ _).mpr (hygienic_pow EQ hEr K)

include hL in
theorem inSig_simResult {Θ : Set (SeqAggFunc T)} (hLi : L.inSig Θ) (hBi : BQ.inSig Θ)
    (hEi : EQ.inSig Θ) : (simResult s s' n K EQ BQ L).inSig Θ := by
  refine inSig_dedupG _ ?_
  rw [AggQueryIn.inSig_castKind]
  refine ⟨fun _ => rfl, AggQueryIn.inSig_prodA _ _ hBi (inSig_pow EQ hEi K), ?_⟩
  rw [simBody, AggQueryIn.inSig_castKind]
  refine ⟨fun _ => rfl, trivial, AggQueryIn.inSig_prodA _ _ ?_ ?_⟩
  · rw [AggQueryIn.inSig_castIdx]
    exact inSig_substRel (rowPv n K) (by trivial) _ ((recLinear_substMap L _).mpr hL)
      ((AggQueryIn.inSig_substMap _ _).mpr hLi)
  · exact ⟨noFun_ltSel n K, (AggQueryIn.inSig_substMap _ _).mpr (inSig_pow EQ hEi K)⟩

include hL in
theorem sumsAllReg_simResult (hLa : L.sumsAllReg) (hBa : BQ.sumsAllReg) (hEa : EQ.sumsAllReg) :
    (simResult s s' n K EQ BQ L).sumsAllReg := by
  refine sumsAllReg_dedupG _ ?_
  rw [AggQueryIn.sumsAllReg_castKind]
  refine ⟨sumsAllReg_prodA _ _ hBa (sumsAllReg_pow EQ hEa K), ?_⟩
  rw [simBody, AggQueryIn.sumsAllReg_castKind]
  refine ⟨trivial, sumsAllReg_prodA _ _ ?_ ?_⟩
  · rw [AggQueryIn.sumsAllReg_castIdx]
    exact sumsAllReg_substRel (rowPv n K) (by trivial) _ ((recLinear_substMap L _).mpr hL)
      ((AggQueryIn.sumsAllReg_substMap _ _).mpr hLa)
  · exact (AggQueryIn.sumsAllReg_substMap _ _).mpr (sumsAllReg_pow EQ hEa K)

include hL in
/-- **The simulation is well-formed over the schema** the recursion is
written over, its own recursive name being fresh. -/
theorem overSchema_simResult {sch : Schema} (hs' : sch s' = none) (hss : s' ≠ s)
    (hLo : L.overSchema (sch.update s n)) (hLn : s' ∉ L.names) (hBo : BQ.overSchema sch)
    (hEo : EQ.overSchema sch) (hEn : s' ∉ EQ.names) :
    (simResult s s' n K EQ BQ L).overSchema sch := by
  refine overSchema_dedupG _ ?_
  rw [AggQueryIn.overSchema_castKind]
  refine ⟨hs', AggQueryIn.overSchema_prodA _ _ hBo (overSchema_pow EQ hEo K), ?_, ?_⟩
  · rw [simBody, AggQueryIn.noMention_castKind]
    refine ⟨trivial, AggQueryIn.noMention_prodA _ _ ?_ ?_⟩
    · rw [AggQueryIn.noMention_castIdx]
      exact AggQueryIn.noMention_substRel (rowPv n K) (by trivial) _
        ((recLinear_substMap L _).mpr hL) (Or.inr ((AggQueryIn.noMention_substMap _ _).mpr
          (AggQueryIn.noMention_of_not_mem_names L hLn)))
    · exact (AggQueryIn.noMention_substMap _ _).mpr (noMention_pow EQ
        (AggQueryIn.noMention_of_not_mem_names EQ hEn) K)
  rw [simBody, AggQueryIn.overSchema_castKind]
  refine ⟨Schema.update_self sch s' (n + K), AggQueryIn.overSchema_prodA _ _ ?_ ?_⟩
  · rw [AggQueryIn.overSchema_castIdx]
    refine overSchema_substRel (rowPv n K) (by trivial) _ ((recLinear_substMap L _).mpr hL) ?_
    rw [Schema.update_comm sch hss, AggQueryIn.overSchema_substMap]
    exact AggQueryIn.overSchema_update_of_not_mem_names L hLo hLn
  · show ((pow EQ K).substMap (applyOuter T c (n + K))).overSchema _
    rw [AggQueryIn.overSchema_substMap]
    exact AggQueryIn.overSchema_update_of_not_mem_names (pow EQ K) (overSchema_pow EQ hEo K)
      (fun h => hEn (mem_names_pow EQ K s' h))

include hL in
theorem mem_names_simResult (x : String) (hx : x ∈ (simResult s s' n K EQ BQ L).names) :
    x = s' ∨ x ∈ L.names ∨ x ∈ BQ.names ∨ x ∈ EQ.names := by
  rw [simResult, names_dedupG, AggQueryIn.names_castKind] at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Or.inl rfl
  rcases Finset.mem_union.mp hx with hx | hx
  · rw [AggQueryIn.names_prodA] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr (mem_names_pow EQ K x hx)))
  · rw [simBody, AggQueryIn.names_castKind] at hx
    have hx : x ∈ Union.union ({s'} : Finset String)
        (AggQueryIn.prodA (AggQueryIn.castIdx (subIdx_self s n)
            (AggQueryIn.substRel s (rowPv n K) (L.substMap (applyOuter T c (n + K)))))
          (AggQueryIn.Sel (ltSel n K) ((pow EQ K).substMap (applyOuter T c (n + K))))).names := hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl (Finset.mem_singleton.mp hx)
    rw [AggQueryIn.names_prodA, AggQueryIn.names_castIdx] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases mem_names_substRel (rowPv n K) _ ((recLinear_substMap L _).mpr hL) x hx with hx | hx
      · rw [AggQueryIn.names_substMap] at hx
        exact Or.inr (Or.inl hx)
      · exact absurd hx (Finset.notMem_empty x)
    · have hx : x ∈ ((pow EQ K).substMap (applyOuter T c (n + K))).names := hx
      rw [AggQueryIn.names_substMap] at hx
      exact Or.inr (Or.inr (Or.inr (mem_names_pow EQ K x hx)))

include hL in
theorem noMention_simResult (t : String) (hLt : L.noMention t)
    (hBt : BQ.noMention t) (hEt : EQ.noMention t) : (simResult s s' n K EQ BQ L).noMention t := by
  refine noMention_dedupG _ t ?_
  rw [AggQueryIn.noMention_castKind]
  refine ⟨AggQueryIn.noMention_prodA _ _ hBt (noMention_pow EQ hEt K), ?_⟩
  rw [simBody, AggQueryIn.noMention_castKind]
  refine ⟨trivial, AggQueryIn.noMention_prodA _ _ ?_ ?_⟩
  · rw [AggQueryIn.noMention_castIdx]
    exact AggQueryIn.noMention_substRel (rowPv n K) (by trivial) _
      ((recLinear_substMap L _).mpr hL) (Or.inr ((AggQueryIn.noMention_substMap _ _).mpr hLt))
  · exact (AggQueryIn.noMention_substMap _ _).mpr (noMention_pow EQ hEt K)

end SimStructure

end AggQueryIn

/-! ## Bridges for the pass -/

namespace AggQueryIn

variable {c : ℕ}

omit [ValueType T] in
/-- **A recursive term with no union is linear**: with one hole, the
recursive relation at its arity, and no `⊎` on the way down to it. -/
theorem recLinear_of_usesOnly {S : Set OpKind} (hSu : OpKind.union ∉ S) {s : String} {n : ℕ} :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
      l = [(s, n)] → q.noMention s → q.usesOnly S → q.recLinear s n := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun hl => absurd hl (by simp)
  | Hole n' s' =>
    intro hl _ _
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.singleton_inj.mp hl)
    exact ⟨rfl, rfl⟩
  | Param pv ρ => exact fun hl => absurd hl (by simp)
  | Empty => exact fun hl => absurd hl (by simp)
  | Proj ps q ih => exact fun hl hn hu => ih hl hn hu.2
  | Sel φ q hφ ih =>
    exact fun hl hn hu => ⟨SelOK.noAggAtom hφ (by rw [hl]; simp), ih hl hn hu.2⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hl hn hu
    rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
    · exact Or.inl ⟨ih₁ hl₁ hn.1 hu.2.1, hl₂, hn.2⟩
    · exact Or.inr ⟨hl₁, hn.1, ih₂ hl₂ hn.2 hu.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hl hn hu => ⟨ih₁ hl hn.1 hu.2.1, hn.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun _ _ hu => absurd hu.1 hSu
  | Dedup q ih => exact fun hl => absurd hl (by simp)
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hl => absurd hl (by simp)
  | Explode k hk q ih => exact fun hl hn hu => ih hl hn hu
  | Retag hk q ih => exact fun hl hn hu => ih hl hn hu
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | Gamma is ts fs q keep ord ih => exact fun hl => absurd hl (by simp)
  | GammaScalar ts fs q ord ih => exact fun hl => absurd hl (by simp)
  | GammaNest is his p fn q ih => exact fun hl => absurd hl (by simp)
  | ProvSum is his t q ih => exact fun hl => absurd hl (by simp)
  | GammaTok is his ts fs a q keep ih => exact fun hl => absurd hl (by simp)
  | Win P O o w t fw q hrr dist keep ih => exact fun hl => absurd hl (by simp)
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hl => absurd hl (by simp)

end AggQueryIn

/-! ## The set recursion replaced

The simulation as the pass needs it: where the target classes hold no
`μ^∪`, a set recursion is replaced by
the simulation – its base the rewritten base and closed part summed, its
term the rewritten body, its counter the counter relation over the values
the fixpoint can hold – and the unions the counter relation is built with
go by the bag recursion afterwards. -/

namespace AggQueryIn

variable {c : ℕ}

/-- **The handler**, for any target holding the union's basis and no
union. -/
theorem muSetHandler {S : Set OpKind} (hS : sumMuOps ⊆ S) (hnu : OpKind.union ∉ S)
    (cnt : SeqAggFunc T) (hcnt : cnt.ReadsCount) : MuSetHandler (T := T) S {cnt} := by
  intro c n s q₀ q₀' qC q₁ q₁' f hf hfs hf0₀ hf0₁ hq₀n hq₁n sch hsch hss ho₀ ho₁ hh₀ hh₁ hi₀ hi₁
    hCn h₀n hb₀ hb₁ hbC he₀ he₁
  classical
  -- the width of the counter: the fixpoint has polynomially many rows in
  -- the number of values the counter runs over
  obtain ⟨fb, ⟨a, b, hab⟩, hbound⟩ := AggQueryIn.exists_card_bound_muSet hcnt s q₀ q₁
    ⟨hi₀, hi₁⟩ ⟨hq₀n, hq₁n, hh₀, hh₁⟩
  set K : ℕ := a + 2 * b with hK
  have hS' : sumMuOps ⊆ insert OpKind.union S := subset_trans hS (Set.subset_insert _ _)
  have hmono : ∀ {c n : ℕ} {l : List (String × ℕ)} (p : AggQueryIn T c n (ColKind.allReg n) l),
      p.usesOnly S → p.usesOnly (insert OpKind.union S) :=
    fun p hp => AggQueryIn.usesOnly_mono (Set.subset_insert _ _) p hp
  have hsar : ∀ {c n : ℕ} {l : List (String × ℕ)} (p : AggQueryIn T c n (ColKind.allReg n) l),
      p.usesOnly S → p.sumsAllReg := fun p hp => AggQueryIn.sumsAllReg_of_usesOnly hnu p hp
  -- the supply: its first third for the base's union, one name for the
  -- simulation's recursion, its last third for the unions of the counter
  have hg0₀ : ∀ i, tri (tri f 0) 0 i ∉ q₀'.names :=
    fun i => tri_notMem hf (by omega) (by omega) (by omega) hb₀.names hf0₀ (3 * i + 0)
  have hg0C : ∀ i, tri (tri f 0) 0 i ∉ qC.names :=
    fun i => tri_notMem hf (by omega) (by omega) (by omega) hbC.names hf0₁ (3 * i + 0)
  obtain ⟨base, hsfb, heb⟩ := (exists_sumFree_aux hS (AggQueryIn.Sum q₀' qC)
    ⟨Set.mem_insert _ _, hmono q₀' hb₀.usesOnly, hmono qC hbC.usesOnly⟩
    ⟨hb₀.hygienic, hbC.hygienic⟩ ⟨hb₀.inSig, hbC.inSig⟩
    ⟨rfl, hsar q₀' hb₀.usesOnly, hsar qC hbC.usesOnly⟩ (tri (tri f 0) 0)
    (tri_injective (tri_injective hf 0) 0)
    (fun i h => (Finset.mem_union.mp h).elim (hg0₀ i) (hg0C i))).1 rfl
  -- the simulation's own recursive name
  set s' : String := tri (tri f 0) 1 0 with hs'def
  have hs'f : s' = f 3 := rfl
  have hss' : s' ≠ s := fun h => hfs 3 (hs'f ▸ h).symm
  have hs'q₀ : s' ∉ q₀.names := hf0₀ 3
  have hs'q₁ : s' ∉ q₁.names := hf0₁ 3
  have hs'q₀' : s' ∉ q₀'.names := fun h => by
    rcases hb₀.names s' h with h' | ⟨i, hi⟩
    · exact hs'q₀ h'
    · have := hf hi; omega
  have hs'q₁' : s' ∉ q₁'.names := fun h => by
    rcases hb₁.names s' h with h' | ⟨i, hi⟩
    · exact hs'q₁ h'
    · have := hf hi; omega
  have hs'qC : s' ∉ qC.names := fun h => by
    rcases hbC.names s' h with h' | ⟨i, hi⟩
    · exact hs'q₁ h'
    · have := hf hi; omega
  have hs'base : s' ∉ base.names := fun h => by
    rcases hsfb.names s' h with h' | ⟨i, hi⟩
    · exact (Finset.mem_union.mp h').elim hs'q₀' hs'qC
    · have := hf hi; omega
  -- the counter relation
  set ls : List (ℕ × String) := (AggQueryIn.MuSet s q₀ q₁).leaves with hls
  set cs : List T := (Union.union q₀.allConsts q₁.allConsts).toList ++ [0, ValueType.nonzero]
    with hcs
  set EQ : AggQueryIn T c 1 (ColKind.allReg 1) := counterRel base ls cs with hEQ
  have hls_leaves : ∀ p ∈ ls, p ∈ (AggQueryIn.MuSet s q₀ q₁).leaves := fun p hp => hp
  have hls_name : ∀ p ∈ ls, p.2 = s ∨ p.2 ∈ q₀.names ∨ p.2 ∈ q₁.names := fun p hp => by
    have h := AggQueryIn.snd_mem_names_of_mem_leaves (AggQueryIn.MuSet s q₀ q₁) p hp
    rcases Finset.mem_insert.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_union.mp h)
  have hs'EQ : s' ∉ EQ.names := fun h => by
    rcases mem_names_counterRel base ls cs s' h with h' | ⟨p, hp, hp'⟩
    · exact hs'base h'
    · rcases hls_name p hp with h | h | h
      · exact hss' (hp' ▸ h)
      · exact hs'q₀ (hp' ▸ h)
      · exact hs'q₁ (hp' ▸ h)
  -- the term is linear
  have hL : q₁'.recLinear s n :=
    recLinear_of_usesOnly hnu q₁' rfl (hb₁.nom s (ne_tri hfs 2) hq₁n) hb₁.usesOnly
  have hq₁s' : q₁.noMention s' := AggQueryIn.noMention_of_not_mem_names q₁ hs'q₁
  have hLs' : q₁'.noMention s' := AggQueryIn.noMention_of_not_mem_names q₁' hs'q₁'
  have hbs' : base.noMention s' := AggQueryIn.noMention_of_not_mem_names base hs'base
  have hEs' : EQ.noMention s' := AggQueryIn.noMention_of_not_mem_names EQ hs'EQ
  -- the simulation, its unions removed
  have hg2 : ∀ i, tri (tri f 0) 2 i ∉ (simResult s s' n K EQ base q₁').names := by
    intro i h
    rcases mem_names_simResult s s' n K EQ base q₁' hL _ h with h | h | h | h
    · have := hf h; omega
    · rcases hb₁.names _ h with h' | ⟨k, hk⟩
      · exact hf0₁ _ h'
      · have := hf hk; omega
    · rcases hsfb.names _ h with h' | ⟨k, hk⟩
      · rcases Finset.mem_union.mp h' with h' | h'
        · rcases hb₀.names _ h' with h'' | ⟨k, hk⟩
          · exact hf0₀ _ h''
          · have := hf hk; omega
        · rcases hbC.names _ h' with h'' | ⟨k, hk⟩
          · exact hf0₁ _ h''
          · have := hf hk; omega
      · have := hf hk; omega
    · rcases mem_names_counterRel base ls cs _ h with h' | ⟨p, hp, hp'⟩
      · rcases hsfb.names _ h' with h'' | ⟨k, hk⟩
        · rcases Finset.mem_union.mp h'' with h'' | h''
          · rcases hb₀.names _ h'' with h''' | ⟨k, hk⟩
            · exact hf0₀ _ h'''
            · have := hf hk; omega
          · rcases hbC.names _ h'' with h''' | ⟨k, hk⟩
            · exact hf0₁ _ h'''
            · have := hf hk; omega
        · have := hf hk; omega
      · rcases hls_name p hp with h | h | h
        · exact ne_tri (ne_tri hfs 0) 2 i (hp' ▸ h).symm
        · exact hf0₀ _ (hp' ▸ h)
        · exact hf0₁ _ (hp' ▸ h)
  obtain ⟨q', hsf, he'⟩ := (exists_sumFree_aux hS (simResult s s' n K EQ base q₁')
    (usesOnly_simResult s s' n K EQ base q₁' hL hS' (hmono q₁' hb₁.usesOnly)
      (hmono base hsfb.usesOnly) (usesOnly_counterRel base ls cs hS hsfb.usesOnly))
    (hygienic_simResult s s' n K EQ base q₁' hL hb₁.hygienic hsfb.hygienic
      (hygienic_counterRel base ls cs hsfb.hygienic) hLs' hbs' hEs')
    (inSig_simResult s s' n K EQ base q₁' hL hb₁.inSig hsfb.inSig
      (inSig_counterRel base ls cs hsfb.inSig))
    (sumsAllReg_simResult s s' n K EQ base q₁' hL (hsar q₁' hb₁.usesOnly)
      (hsar base hsfb.usesOnly) (sumsAllReg_counterRel base ls cs (hsar base hsfb.usesOnly)))
    (tri (tri f 0) 2) (tri_injective (tri_injective hf 0) 2) hg2).1 rfl
  refine ⟨q', ?_, fun D γ hset => ?_⟩
  · exact {
      usesOnly := hsf.usesOnly
      hygienic := hsf.hygienic
      inSig := hsf.inSig
      over := fun sch₂ hsch₂ ho₂ => by
        refine hsf.over sch₂ (fun i => hsch₂ _) ?_
        have hbo : base.overSchema sch₂ := hsfb.over sch₂ (fun i => hsch₂ _)
          ⟨hb₀.over sch₂ (sch_tri hsch₂ 1) ho₂.2.1,
            AggQueryIn.overSchema_of_update_of_noMention qC (fun _ h => by simp at h) hCn
              (hbC.over (sch₂.update s n) (update_fresh (sch_tri hsch₂ 2)
                  (ne_tri hfs 2)) ho₂.2.2.2)⟩
        refine overSchema_simResult s s' n K EQ base q₁' hL (hsch₂ 3) hss'
          (hb₁.over (sch₂.update s n) (update_fresh (sch_tri hsch₂ 2) (ne_tri hfs 2)) ho₂.2.2.2)
          hs'q₁' hbo ?_ hs'EQ
        exact overSchema_counterRel base ls cs hbo (fun p hp =>
          AggQueryIn.find_of_mem_leaves_of_overSchema (AggQueryIn.MuSet s q₀ q₁) ho₂ p
            (hls_leaves p hp))
      names := fun x hx => by
        rcases hsf.names x hx with hx | ⟨i, rfl⟩
        swap
        · exact Or.inr ⟨_, rfl⟩
        rcases mem_names_simResult s s' n K EQ base q₁' hL x hx with rfl | hx | hx | hx
        · exact Or.inr ⟨3, rfl⟩
        · rcases hb₁.names x hx with h | ⟨i, hi⟩
          · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
          · exact Or.inr ⟨_, hi⟩
        · rcases hsfb.names x hx with h | ⟨i, hi⟩
          · rcases Finset.mem_union.mp h with h | h
            · rcases hb₀.names x h with h | ⟨i, hi⟩
              · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
              · exact Or.inr ⟨_, hi⟩
            · rcases hbC.names x h with h | ⟨i, hi⟩
              · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
              · exact Or.inr ⟨_, hi⟩
          · exact Or.inr ⟨_, hi⟩
        · rcases mem_names_counterRel base ls cs x hx with h | ⟨p, hp, rfl⟩
          · rcases hsfb.names x h with h | ⟨i, hi⟩
            · rcases Finset.mem_union.mp h with h | h
              · rcases hb₀.names x h with h | ⟨i, hi⟩
                · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
                · exact Or.inr ⟨_, hi⟩
              · rcases hbC.names x h with h | ⟨i, hi⟩
                · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
                · exact Or.inr ⟨_, hi⟩
            · exact Or.inr ⟨_, hi⟩
          · exact Or.inl (AggQueryIn.snd_mem_names_of_mem_leaves (AggQueryIn.MuSet s q₀ q₁) p hp)
      nom := fun t ht hn => by
        refine hsf.nom t (fun i => ht _) ?_
        have hbt : base.noMention t := hsfb.nom t (fun i => ht _)
          ⟨hb₀.nom t (ne_tri ht 1) hn.1, hbC.nom t (ne_tri ht 2) hn.2⟩
        refine noMention_simResult s s' n K EQ base q₁' hL t
          (hb₁.nom t (ne_tri ht 2) hn.2) hbt ?_
        exact noMention_counterRel base ls cs t hbt (fun p hp hpt => absurd
          (AggQueryIn.mem_index_of_mem_leaves (AggQueryIn.MuSet s q₀ q₁) hn p hp hpt)
          List.not_mem_nil) }
  · -- correctness: the recursion's rounds are defined, so are the pieces
    obtain ⟨hq₀s, hsR, hkR⟩ := hset
    have h0 := hkR 0
    obtain ⟨hq₀'s, he₀eq⟩ := he₀ D γ hq₀s
    have hqCs : qC.SettlesAt D γ :=
      AggQueryIn.settlesAt_assign_of_noMention _ qC hCn D γ (he₁ _ γ h0).2.1
    obtain ⟨hbases, hbaseeq⟩ := heb D γ ⟨hq₀'s, hqCs⟩
    have hB : (base.evaluatePlain D γ : Multiset (Tuple T n))
        = q₀.evaluatePlain D γ + qC.evaluatePlain D γ := by
      rw [← hbaseeq]
      show q₀'.evaluatePlain D γ + qC.evaluatePlain D γ = _
      rw [he₀eq]
    have hE : ∀ e ∈ unaryVals (EQ.evaluatePlain D γ), ValueType.isNull e = false :=
      nonNull_counterRel base ls cs D γ
    have hEQs : EQ.SettlesAt D γ := settlesAt_counterRel base ls cs D γ hbases
    have hsplit : ∀ X : Relation T n, q₁.SettlesAt (D.assign s X) γ →
        (q₁.evaluatePlain (D.assign s X) γ : Multiset (Tuple T n))
          = q₁'.evaluatePlain (D.assign s X) γ + qC.evaluatePlain (D.assign s X) γ :=
      fun X h => (he₁ _ γ h).2.2
    -- the fixpoint's values, and its size
    set E : Multiset T := unaryVals (EQ.evaluatePlain D γ) with hEdef
    set B : Finset T := E.toFinset ∪ (ValueType.nullVal : Option T).toFinset with hBdef
    have hin : ∀ a : T, (ValueType.isNull a = false → a ∈ E) → a ∈ B := by
      intro a ha
      by_cases hnull : ValueType.isNull a = true
      · refine Finset.mem_union_right _ ?_
        rw [(ValueType.isNull_iff_nullVal a).mp hnull]
        exact Finset.mem_singleton_self a
      · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr (ha (Bool.eq_false_iff.mpr hnull)))
    have hνB : ∀ ν : T, ValueType.nullVal = some ν → ν ∈ B := fun ν hν => by
      refine Finset.mem_union_right _ ?_
      rw [hν]
      exact Finset.mem_singleton_self ν
    have h0E : (0 : T) ∈ E := mem_counterRel_of_mem_consts base ls cs D γ 0
      (List.mem_append_right _ (by simp)) ValueType.isNull_zero
    have hnzE : (ValueType.nonzero : T) ∈ E := mem_counterRel_of_mem_consts base ls cs D γ _
      (List.mem_append_right _ (by simp)) ValueType.isNull_nonzero
    have h0B : (0 : T) ∈ B := hin 0 (fun _ => h0E)
    have hγB : ∀ j, γ j ∈ B :=
      fun j => hin _ (fun hnn => mem_counterRel_of_outer base ls cs D γ j hnn)
    have hDB : ∀ p ∈ (AggQueryIn.MuSet s q₀ q₁).leaves, ∀ r : Relation T p.1,
        D.find p.1 p.2 = some r → ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B :=
      fun p hp r hr u hu j => hin _ (fun hnn =>
        mem_counterRel_of_mem_leaf base ls cs D γ p hp r hr u hu j hnn)
    have hcB : ∀ a ∈ (AggQueryIn.MuSet s q₀ q₁).allConsts, a ∈ B := fun a ha => hin a (fun hnn =>
      mem_counterRel_of_mem_consts base ls cs D γ a
        (List.mem_append_left _ (Finset.mem_toList.mpr ha)) hnn)
    have hFcard := hbound B D γ hνB h0B hγB hDB hcB
    have h2 : 2 ≤ E.toFinset.card :=
      Finset.one_lt_card.mpr ⟨0, Multiset.mem_toFinset.mpr h0E, ValueType.nonzero,
        Multiset.mem_toFinset.mpr hnzE, ValueType.nonzero_ne_zero.symm⟩
    have hBcard : B.card ≤ E.toFinset.card + 1 := by
      refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
      cases (ValueType.nullVal : Option T) <;> simp
    have hcard : Multiset.card ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ)
        ≤ (unaryVals (EQ.evaluatePlain D γ)).toFinset.card ^ K := by
      refine le_trans hFcard (le_trans (hab B.card) ?_)
      have he2 : E.toFinset.card + 2 ≤ E.toFinset.card ^ 2 := by
        rw [pow_two]
        exact le_trans (by omega) (Nat.mul_le_mul_right E.toFinset.card h2)
      calc a * (B.card + 1) ^ b ≤ a * (E.toFinset.card + 2) ^ b :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ ≤ E.toFinset.card ^ a * (E.toFinset.card ^ 2) ^ b :=
            Nat.mul_le_mul (le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left h2 a))
              (Nat.pow_le_pow_left he2 b)
        _ = E.toFinset.card ^ K := by rw [← pow_mul, ← pow_add, hK]
    obtain ⟨heq, hmemF⟩ := evaluatePlain_simResult s s' n K EQ base qC q₀ q₁' q₁ hL hLs' hEs'
      hCn D γ ⟨hq₀s, hsR, hkR⟩ hsplit hB hE hcard
    have hsimS : (simResult s s' n K EQ base q₁').SettlesAt D γ := by
      refine settlesAt_simResult s s' n K EQ base q₁' hL hLs' hEs' D γ hE hbases hEQs
        (fun j t hj ht => ?_)
      have htF := hmemF j t hj ht
      have hq₁F : q₁.SettlesAt (D.assign s ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ)) γ :=
        hkR _
      exact AggQueryIn.settlesAt_assign_of_subset q₁' hL D γ
        (fun u hu => by rw [Multiset.mem_singleton.mp hu]; exact htF) (he₁ _ γ hq₁F).1
    obtain ⟨hq's, hq'eq⟩ := he' D γ hsimS
    exact ⟨hq's, heq.symm.trans hq'eq⟩

end AggQueryIn

/-! ## The whole algebra with one recursion -/

omit [ValueType T] in
theorem union_notMem_sumMuOps : OpKind.union ∉ AggQueryIn.sumMuOps := by
  simp [AggQueryIn.sumMuOps]

/-- **The basis of the whole algebra in the minimal universe**: the
construction's classes and the windows, `{∅, Π, σ, apply, γ, win, μ^⊎}`.
`basisRecOps_generatesOnRec` says it generates, and
`Provenance.RecursionBasisTheorem` that no proper subset does. -/
def basisRecOps : Set OpKind := insert OpKind.win AggQueryIn.sumMuOps

theorem union_notMem_basisRecOps : OpKind.union ∉ basisRecOps := by
  simp [basisRecOps, AggQueryIn.sumMuOps]

theorem muSet_notMem_basisRecOps : OpKind.muSet ∉ basisRecOps := by
  simp [basisRecOps, AggQueryIn.sumMuOps]

/-- **`μ^∪` is not needed, for every restricted term**: over a schema
declaring finitely many names, every query of the
whole algebra in the minimal universe with restricted recursions is
matched over `∅`, `Π`, `σ`, the apply, `γ`, `win` and `μ^⊎` – defined
wherever the query is and equal to it there. A set recursion is simulated
by a bag recursion whose counter runs over the instance's values at the
recursion's leaves, the recursion's constants and its context: the
fixpoint is duplicate-free over those values and the counts the recursion
computes, of which there are polynomially many
(`AggQueryIn.exists_card_bound_muSet`, off the order types of
`Provenance.Genericity`), so a counter of a width fixed by the query
covers it. With the necessary classes (`required_mem_of_generatesOnRec`),
a basis of the whole algebra in the minimal universe is `∅`, `Π`, `γ`,
`μ^⊎`, one of `σ` and `−`, one of `×`
and the apply, and `win` (`Provenance.WinRow`); `μ^∪` is in none. -/
theorem basisRecOps_generatesOnRec (sch : Schema) (cnt : SeqAggFunc T) (hcnt : cnt.IsCount) :
    GeneratesOnRec T sch cnt basisRecOps := by
  intro n κ q ho hq hi
  have hr : q.hygienic := q.hygienic_of_overSchema _ ho
  obtain ⟨f, hf, hfsch, hfr⟩ := AggQueryIn.exists_freshSupply sch q.names
  have hS : AggQueryIn.sumMuOps ⊆ basisRecOps := Set.subset_insert _ _
  obtain ⟨q', hb, he⟩ := (AggQueryIn.exists_basisRec_aux hS union_notMem_basisRecOps
    (Or.inr (AggQueryIn.muSetHandler hS union_notMem_basisRecOps cnt hcnt.readsCount)) cnt
    (Set.mem_singleton cnt) hcnt.counts q hq hr hi (Or.inl (Set.mem_insert _ _)) f hf hfr sch hfsch
    ho).1 rfl
  exact ⟨_, q', hb.over sch hfsch ho, hb.usesOnly, hb.inSig,
    AggQueryIn.Extends.of_settles (fun D γ hs => he D γ hs)⟩

/-- **And without the window class**, for the windows an apply derives
(`evaluatePlain_winByApplyOf`): the six classes `∅`, `Π`, `σ`, the apply, `γ` and `μ^⊎` match
every query of the whole algebra in the minimal universe whose windows
are derivable (`AggQueryIn.WinsDerivable`). -/
theorem sumMuOps_generatesOnRec_of_winsDerivable (sch : Schema)
    (cnt : SeqAggFunc T) (hcnt : cnt.IsCount)
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ) (ho : q.overSchema sch)
    (hq : q.usesOnly plainRecOps) (hi : q.inMinimalSig cnt) (hw : q.WinsDerivable) :
    ∃ q' : AggQuery T n (ColKind.allReg n),
      q'.overSchema sch ∧ q'.usesOnly AggQueryIn.sumMuOps ∧ q'.inMinimalSig cnt ∧ q'.Extends q := by
  have hr : q.hygienic := q.hygienic_of_overSchema _ ho
  obtain ⟨f, hf, hfsch, hfr⟩ := AggQueryIn.exists_freshSupply sch q.names
  obtain ⟨q', hb, he⟩ := (AggQueryIn.exists_basisRec_aux (subset_refl _) union_notMem_sumMuOps
    (Or.inr (AggQueryIn.muSetHandler (subset_refl _) union_notMem_sumMuOps cnt hcnt.readsCount)) cnt
    (Set.mem_singleton cnt) hcnt.counts q hq hr hi (Or.inr hw) f hf hfr sch hfsch ho).1 rfl
  exact ⟨q', hb.over sch hfsch ho, hb.usesOnly, hb.inSig,
    AggQueryIn.Extends.of_settles (fun D γ hs => he D γ hs)⟩
