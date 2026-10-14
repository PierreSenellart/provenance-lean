import Provenance.Genericity

/-!
# The rounds of a bag recursion that settles are bounded

A recursive term reads its hole once, so it is *linear* in the recursive
relation: a round of a bag recursion is the previous round bound through
a function of the row (`AggQueryIn.bind_of_body`). A row of round `j` is
therefore the end of a path of `j` steps from the base, and a path longer
than the number of rows the rounds can hold repeats a row, whose segment
then pumps forever: a recursion that settles does so within `|V|^m`
rounds, `V` the values its rounds hold (`bindStep_round_eq_zero_of_settles`),
and its value is the sum of that many rounds (`AggQueryIn.mu_eq_muSum_of_valsIn`).

This is what any bounded simulation of a bag recursion rests on – a
simulation that settles everywhere and agrees with the recursion wherever
the recursion settles.
-/

variable {T : Type} [ValueType T]

/-! ## A body is linear in its hole -/

/-- **A recursive term is linear in its hole**: read at a round `X`, it is
`X` bound through a function of the row, plus what it reads at the empty
round. The hole occurs once, under projections, selections, products,
the left of an apply and unions, each of which distributes over the bind. -/
theorem AggQueryIn.bind_of_body {s : String} {m : ℕ} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      l = [(s, m)] → q.noMention s → ∀ (D : Database T) (γ : Fin c → T),
      ∃ (F : Tuple T m → Multiset (Tuple T n)) (C : Multiset (Tuple T n)),
        ∀ X : Multiset (Tuple T m),
          (q.evaluatePlain (D.assign s X) γ : Multiset (Tuple T n)) = X.bind F + C := by
  intro c n κ l q
  induction q with
  | Rel n' s' => exact fun hl => absurd hl (by simp)
  | Hole n' s' =>
    intro hl _ D γ
    have hs : s' = s := (Prod.mk.inj (List.singleton_inj.mp hl)).1
    have hn : n' = m := (Prod.mk.inj (List.singleton_inj.mp hl)).2
    subst hs; subst hn
    refine ⟨fun t => {t}, 0, fun X => ?_⟩
    show (match (D.assign s' X).find n' s' with
      | none => (0 : Multiset (Tuple T n')) | some r => r) = _
    rw [Database.find_assign]
    show X = X.bind (fun t => {t}) + 0
    rw [Multiset.bind_singleton, Multiset.map_id', add_zero]
  | Empty => exact fun hl => absurd hl (by simp)
  | Proj ps q ih =>
    intro hl hr D γ
    obtain ⟨F, C, h⟩ := ih hl hr D γ
    refine ⟨fun t => (F t).map (fun u => fun j => (ps j).evalPlain u γ),
      C.map (fun u => fun j => (ps j).evalPlain u γ), fun X => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [h X, Multiset.map_add, Multiset.map_bind]
  | Sel φ q hφ ih =>
    intro hl hr D γ
    obtain ⟨F, C, h⟩ := ih hl hr D γ
    refine ⟨fun t => @Multiset.filter _ (fun u => φ.holdsPlain u γ)
        (fun u => φ.decHoldsPlain u γ) (F t),
      @Multiset.filter _ (fun u => φ.holdsPlain u γ) (fun u => φ.decHoldsPlain u γ) C,
      fun X => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [h X, Multiset.filter_add, Multiset.filter_bind]
  | Prod q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l₁ l₂
    intro hl hr D γ
    rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₂
      obtain ⟨F, C, h⟩ := ih₁ h₁ hr.1 D γ
      refine ⟨fun t => (F t).bind (fun a => (q₂.evaluatePlain D γ : Multiset (Tuple T n₂)).map
          (fun v => (Fin.append a v : Tuple T (n₁ + n₂)))),
        C.bind (fun a => (q₂.evaluatePlain D γ : Multiset (Tuple T n₂)).map
          (fun v => (Fin.append a v : Tuple T (n₁ + n₂)))), fun X => ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hr.2 D γ, Relation.hMul_eq_bind, h X,
        Multiset.add_bind, Multiset.bind_assoc]
    · subst h₁
      obtain ⟨F, C, h⟩ := ih₂ h₂ hr.2 D γ
      refine ⟨fun t => (q₁.evaluatePlain D γ : Multiset (Tuple T n₁)).bind (fun a => (F t).map
          (fun v => (Fin.append a v : Tuple T (n₁ + n₂)))),
        (q₁.evaluatePlain D γ : Multiset (Tuple T n₁)).bind (fun a => C.map
          (fun v => (Fin.append a v : Tuple T (n₁ + n₂)))), fun X => ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₁ hr.1 D γ, Relation.hMul_eq_bind, h X]
      simp only [Multiset.map_add, Multiset.bind_add, Multiset.map_bind]
      rw [Multiset.bind_bind]
  | Apply q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₂ l₁
    intro hl hr D γ
    obtain ⟨F, C, h⟩ := ih₁ hl hr.1 D γ
    refine ⟨fun t => (F t).bind (fun a =>
        (q₂.evaluatePlain D (Fin.append a γ) : Multiset (Tuple T n₂)).map
          (fun v => (Fin.append a v : Tuple T (n₁ + n₂)))),
      C.bind (fun a => (q₂.evaluatePlain D (Fin.append a γ) : Multiset (Tuple T n₂)).map
          (fun v => (Fin.append a v : Tuple T (n₁ + n₂)))), fun X => ?_⟩
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hr.2 D]
    rw [h X, Multiset.add_bind, Multiset.bind_assoc]
  | Sum q₁ q₂ ih₁ ih₂ =>
    rename_i c' n' κ' l₁ l₂
    intro hl hr D γ
    rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₂
      obtain ⟨F, C, h⟩ := ih₁ h₁ hr.1 D γ
      refine ⟨F, @HAdd.hAdd (Multiset (Tuple T n')) (Multiset (Tuple T n')) (Multiset (Tuple T n'))
        instHAdd C (q₂.evaluatePlain D γ), fun X => ?_⟩
      rw [AggQueryIn.evaluatePlain]
      rw [h X, AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hr.2 D γ]
      show @HAdd.hAdd (Multiset (Tuple T n')) (Multiset (Tuple T n')) (Multiset (Tuple T n'))
        instHAdd (X.bind F + C) (q₂.evaluatePlain D γ) = _
      rw [add_assoc]
    · subst h₁
      obtain ⟨F, C, h⟩ := ih₂ h₂ hr.2 D γ
      refine ⟨F, @HAdd.hAdd (Multiset (Tuple T n')) (Multiset (Tuple T n')) (Multiset (Tuple T n'))
        instHAdd (q₁.evaluatePlain D γ) C, fun X => ?_⟩
      rw [AggQueryIn.evaluatePlain]
      rw [h X, AggQueryIn.evaluatePlain_assign_of_noMention X q₁ hr.1 D γ]
      show @HAdd.hAdd (Multiset (Tuple T n')) (Multiset (Tuple T n')) (Multiset (Tuple T n'))
        instHAdd (q₁.evaluatePlain D γ) (X.bind F + C) = _
      rw [add_left_comm]
  | Dedup q ih => exact fun hl => absurd hl (by simp)
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hl => absurd hl (by simp)
  | Explode k hk q ih =>
    intro hl hr D γ
    obtain ⟨F, C, h⟩ := ih hl hr D γ
    exact ⟨F, C, fun X => by rw [AggQueryIn.evaluatePlain]; exact h X⟩
  | Retag hk q ih =>
    intro hl hr D γ
    obtain ⟨F, C, h⟩ := ih hl hr D γ
    exact ⟨F, C, fun X => by rw [AggQueryIn.evaluatePlain]; exact h X⟩
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | Gamma is ts fs q keep ord ih => exact fun hl => absurd hl (by simp)
  | GammaScalar ts fs q ord ih => exact fun hl => absurd hl (by simp)
  | GammaNest is his p f q ih => exact fun hl => absurd hl (by simp)
  | ProvSum is his t q ih => exact fun hl => absurd hl (by simp)
  | GammaTok is his ts fs a q keep ih => exact fun hl => absurd hl (by simp)
  | Win P O o w t f q hrr dist keep ih => exact fun hl => absurd hl (by simp)
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hl => absurd hl (by simp)

/-! ## Paths through the rounds of a bind -/

section Rounds

variable {α : Type}

/-- The round function of a linear term with nothing read at the empty
round: a round is the previous one bound through `F`. -/
def bindStep (F : α → Multiset α) : Multiset α → Multiset α := fun X => X.bind F

theorem bindStep_zero (F : α → Multiset α) : bindStep F 0 = 0 := Multiset.zero_bind F

theorem bindStep_iterate_succ (F : α → Multiset α) (M : Multiset α) (j : ℕ) :
    Nat.iterate (bindStep F) (j + 1) M = (Nat.iterate (bindStep F) (j) M).bind F :=
  Function.iterate_succ_apply' _ _ _

/-- **A row of round `j` is the end of a path of `j` steps from the base.** -/
theorem exists_path_of_mem_round (F : α → Multiset α) (M : Multiset α) :
    ∀ (j : ℕ) (t : α), t ∈ Nat.iterate (bindStep F) (j) M →
      ∃ p : ℕ → α, p 0 ∈ M ∧ (∀ i, LT.lt i j → p (i + 1) ∈ F (p i)) ∧ p j = t := by
  intro j
  induction j with
  | zero => exact fun t ht => ⟨fun _ => t, ht, fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩
  | succ j ih =>
    intro t ht
    rw [bindStep_iterate_succ, Multiset.mem_bind] at ht
    obtain ⟨t', ht', htt'⟩ := ht
    obtain ⟨p, hp0, hp, hpj⟩ := ih t' ht'
    refine ⟨Function.update p (j + 1) t, ?_, fun i hi => ?_, Function.update_self _ _ _⟩
    · rw [Function.update_of_ne (Nat.zero_ne_add_one j)]; exact hp0
    · rcases Nat.lt_or_ge i j with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hp i h
      · obtain rfl : i = j := le_antisymm (Nat.lt_succ_iff.mp hi) h
        rw [Function.update_self, Function.update_of_ne (by omega), hpj]
        exact htt'

/-- **Following a path from a round forward**: the `i`-th row of a path
whose start is in round `r` is in round `r + i`. -/
theorem mem_round_of_path (F : α → Multiset α) (M : Multiset α) (p : ℕ → α) (j : ℕ)
    (hp : ∀ i, LT.lt i j → p (i + 1) ∈ F (p i)) {r : ℕ} (hr : p 0 ∈ Nat.iterate (bindStep F) (r) M) :
    ∀ i, i ≤ j → p i ∈ Nat.iterate (bindStep F) (r + i) M := by
  intro i
  induction i with
  | zero => exact fun _ => hr
  | succ i ih =>
    intro hi
    rw [← Nat.add_assoc, bindStep_iterate_succ, Multiset.mem_bind]
    exact ⟨p i, ih (Nat.le_of_succ_le hi), hp i (Nat.lt_of_succ_le hi)⟩

/-- **A repeated row pumps**: if a path visits the same row at `a < b`,
that row is in round `b + k (b - a)` for every `k`. -/
theorem mem_round_pump (F : α → Multiset α) (M : Multiset α) (p : ℕ → α) {a b : ℕ}
    (hab : LT.lt a b) (hp : ∀ i, LT.lt i b → p (i + 1) ∈ F (p i)) (hrep : p a = p b)
    (hb : p b ∈ Nat.iterate (bindStep F) (b) M) :
    ∀ k, p b ∈ Nat.iterate (bindStep F) (b + k * (b - a)) M := by
  intro k
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    -- the segment from `a` to `b`, started at round `b + k (b - a)`
    have hseg := mem_round_of_path F M (fun i => p (a + i)) (b - a)
      (fun i hi => by
        show p (a + i + 1) ∈ F (p (a + i))
        exact hp (a + i) (by omega))
      (r := b + k * (b - a)) (by simpa [hrep] using ih) (b - a) (le_refl _)
    have he : a + (b - a) = b := by omega
    rw [he] at hseg
    have hk : b + (k + 1) * (b - a) = b + k * (b - a) + (b - a) := by
      rw [Nat.succ_mul]; omega
    rw [hk]
    exact hseg

end Rounds

/-! ## The bound -/

/-- **A bag recursion that settles does so within `|V|^m` rounds**, `V`
holding every value of every round: a row of round `|V|^m` ends a path of
`|V|^m + 1` rows over `V^m`, two of which coincide, and the segment
between them pumps a non-empty round past every bound. -/
theorem bindStep_round_eq_zero_of_settles {m : ℕ} (F : Tuple T m → Multiset (Tuple T m))
    (M : Multiset (Tuple T m)) (V : Finset T)
    (hV : ∀ j, ∀ u ∈ Nat.iterate (bindStep F) (j) M, ∀ i, u i ∈ V)
    (hs : MuSettles (bindStep F) M) :
    Nat.iterate (bindStep F) (V.card ^ m) M = 0 := by
  classical
  by_contra hne
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨p, hp0, hp, -⟩ := exists_path_of_mem_round F M _ t ht
  have hround : ∀ i, i ≤ V.card ^ m → p i ∈ Nat.iterate (bindStep F) (i) M := fun i hi => by
    simpa using mem_round_of_path F M p _ hp (r := 0) (by simpa using hp0) i hi
  -- two rows of the path coincide
  have hc : LT.lt (Fintype.piFinset (fun _ : Fin m => V)).card (Finset.range (V.card ^ m + 1)).card := by
    rw [Finset.card_range, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    exact Nat.lt_succ_self _
  obtain ⟨x, hx, y, hy, hxy, hpxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
    (f := p) (fun i hi => Fintype.mem_piFinset.mpr
      (fun k => hV i (p i) (hround i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) k))
  rw [Finset.mem_range] at hx hy
  -- the earlier one pumps
  have hpump : ∀ (a b : ℕ), LT.lt a b → LT.lt b (V.card ^ m + 1) → p a = p b → False := by
    intro a b hab hbB hrep
    obtain ⟨K, hK⟩ := hs
    have hall := mem_round_pump F M p hab (fun i hi => hp i (by omega)) hrep
      (hround b (Nat.lt_succ_iff.mp hbB)) (K + 1)
    have hzero : Nat.iterate (bindStep F) (b + (K + 1) * (b - a)) M = 0 :=
      iterate_eq_zero_of_le (bindStep_zero F) hK (by
        have h1 : K + 1 ≤ (K + 1) * (b - a) := Nat.le_mul_of_pos_right _ (by omega)
        omega)
    rw [hzero] at hall
    exact Multiset.notMem_zero _ hall
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact hpump x y h hy hpxy
  · exact hpump y x h hx hpxy.symm

omit [ValueType T] in
/-- The rounds of a step keep their values in `V` as soon as the step does. -/
theorem iterate_valsIn {m : ℕ} (step : Multiset (Tuple T m) → Multiset (Tuple T m))
    (M : Multiset (Tuple T m)) (V : Finset T)
    (hM : ∀ u ∈ M, ∀ i, u i ∈ V)
    (hstep : ∀ X : Multiset (Tuple T m), (∀ u ∈ X, ∀ i, u i ∈ V) → ∀ u ∈ step X, ∀ i, u i ∈ V) :
    ∀ j, ∀ u ∈ Nat.iterate step j M, ∀ i, u i ∈ V := by
  intro j
  induction j with
  | zero => exact hM
  | succ j ih => rw [Function.iterate_succ_apply']; exact hstep _ ih

/-- **A bag recursion that settles is the sum of `|V|^m` rounds**, `V`
holding every value of every round: the round function of a body that
reads nothing at the empty round is a bind (`AggQueryIn.bind_of_body`),
so the bound applies. -/
theorem AggQueryIn.mu_eq_muSum_of_valsIn {c m : ℕ} (s : String)
    (q₀ : AggQueryIn T c m (ColKind.allReg m)) (q₁ : AggQueryIn T c m (ColKind.allReg m) [(s, m)])
    (hr : q₁.noMention s) (D : Database T) (γ : Fin c → T) (V : Finset T)
    (h0 : q₁.evaluatePlain (D.assign s (0 : Relation T m)) γ = 0)
    (hs : MuSettles (fun X => q₁.evaluatePlain (D.assign s X) γ) (q₀.evaluatePlain D γ))
    (hV : ∀ j, ∀ u, Multiset.Mem
      (Nat.iterate (fun X : Multiset (Tuple T m) => (q₁.evaluatePlain (D.assign s X) γ : Multiset (Tuple T m))) j
        (q₀.evaluatePlain D γ)) u → ∀ i, u i ∈ V) :
    ((AggQueryIn.Mu s q₀ q₁).evaluatePlain D γ : Multiset (Tuple T m))
      = muSum (fun X => q₁.evaluatePlain (D.assign s X) γ) (V.card ^ m) (q₀.evaluatePlain D γ) := by
  obtain ⟨F, C, h⟩ := AggQueryIn.bind_of_body q₁ rfl hr D γ
  have hC : C = 0 := by
    have := h 0
    rw [Multiset.zero_bind, zero_add] at this
    exact this.symm.trans h0
  have hstep : (fun X : Multiset (Tuple T m) => (q₁.evaluatePlain (D.assign s X) γ
      : Multiset (Tuple T m))) = bindStep F := by
    funext X
    rw [h X, hC, add_zero]
    rfl
  have hB : Nat.iterate (fun X : Multiset (Tuple T m) => (q₁.evaluatePlain (D.assign s X) γ
      : Multiset (Tuple T m))) (V.card ^ m) (q₀.evaluatePlain D γ) = 0 := by
    rw [hstep]
    refine bindStep_round_eq_zero_of_settles F _ V (fun j u hu i => ?_) (hstep ▸ hs)
    rw [← hstep] at hu
    exact hV j u hu i
  rw [AggQueryIn.evaluatePlain]
  refine muSumFix_eq_of_empty h0 ?_
  rw [Function.iterate_succ_apply', hB]
  exact h0
