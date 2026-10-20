import Provenance.SymGamma

/-!
# The order of cells, and the symbolic window

A window sorts its partition by an `ORDER BY` clause and reads frames off
that order. Over symbolic rows the clause reads, for each order column,
`3 + k` columns of its cell (`Sym.keyIdx`): the value column, the two
columns placing a code against its value, and the rank. Read
lexicographically with the column's own direction and null placement,
they sort the cells as the values they stand for (`Sym.leOn_key`).
-/

variable {T : Type} [ValueType T]

omit [ValueType T] in
/-- **The indices before `j`**: `finRange` split at `j`, every index of the
first part below it. -/
theorem List.finRange_split {k : ℕ} (j : Fin k) :
    ∃ s t : List (Fin k), List.finRange k = s ++ j :: t ∧ ∀ x ∈ s, LT.lt x j := by
  obtain ⟨s, t, h⟩ := List.append_of_mem (List.mem_finRange j)
  refine ⟨s, t, h, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hlen : s.length < (List.finRange k).length := by rw [h]; simp
  have hj : (List.finRange k)[s.length]'hlen = j := by
    rw [List.getElem_of_eq h]; simp
  have hx' : (List.finRange k)[i]'(by rw [h]; simp; omega) = s[i] := by
    rw [List.getElem_of_eq h, List.getElem_append_left]
  have hjv : j.val = s.length := by
    have := congrArg Fin.val hj
    simp only [List.getElem_finRange, Fin.val_cast] at this
    exact this.symm
  rw [← hx', Fin.lt_def]
  simp only [List.getElem_finRange, Fin.val_cast]
  omega

namespace OrderSpec

variable {p : ℕ}

/-- **Peers all along, the comparison holds.** -/
theorem leOn_of_peers (o : OrderSpec p) (x y : Tuple T p) :
    ∀ (l : List (Fin p)), (∀ j ∈ l, (o j).peer (x j) (y j) = true) → o.leOn l x y = true
  | [], _ => rfl
  | j :: l, h => by
    simp only [OrderSpec.leOn]
    rw [h j List.mem_cons_self, ite_eq_left rfl]
    exact leOn_of_peers o x y l (fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- **The first column whose values are not peers decides.** -/
theorem leOn_of_first (o : OrderSpec p) (x y : Tuple T p) (j₀ : Fin p) (l₂ : List (Fin p)) :
    ∀ (l₁ : List (Fin p)), (∀ j ∈ l₁, (o j).peer (x j) (y j) = true) →
      (o j₀).peer (x j₀) (y j₀) = false →
      o.leOn (l₁ ++ j₀ :: l₂) x y = (o j₀).le (x j₀) (y j₀)
  | [], _, h₀ => by
    simp only [List.nil_append, OrderSpec.leOn, h₀]
    rfl
  | j :: l₁, h, h₀ => by
    simp only [List.cons_append, OrderSpec.leOn]
    rw [h j List.mem_cons_self, ite_eq_left rfl]
    exact leOn_of_first o x y j₀ l₂ l₁ (fun i hi => h i (List.mem_cons_of_mem _ hi)) h₀

/-- **The first column whose values are not peers decides the clause.** -/
theorem le_of_first_idx (o : OrderSpec p) (x y : Tuple T p) (j₀ : Fin p)
    (hb : ∀ j : Fin p, LT.lt j j₀ → (o j).peer (x j) (y j) = true)
    (h₀ : (o j₀).peer (x j₀) (y j₀) = false) : o.le x y = (o j₀).le (x j₀) (y j₀) := by
  obtain ⟨s, t, hst, hs⟩ := List.finRange_split j₀
  unfold OrderSpec.le
  rw [hst]
  exact leOn_of_first o x y j₀ t s (fun j hj => hb j (hs j hj)) h₀

/-- Peers in every column, the clause holds. -/
theorem le_of_all_peers (o : OrderSpec p) (x y : Tuple T p)
    (h : ∀ j : Fin p, (o j).peer (x j) (y j) = true) : o.le x y = true :=
  leOn_of_peers o x y _ (fun j _ => h j)

end OrderSpec

omit [ValueType T] in
/-- The indices of `a + b` columns: the first `a`, then the last `b`. -/
theorem List.finRange_add_eq (a b : ℕ) :
    List.finRange (a + b) = (List.finRange a).map (Fin.castAdd b)
      ++ (List.finRange b).map (Fin.natAdd a) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_finRange, List.getElem_append, List.length_map,
      List.length_finRange, List.getElem_map]
    split
    · rfl
    · rename_i h
      ext
      simp
      omega

namespace Sym

variable {k : ℕ}

/-- **The columns of a cell an order reads**: its value, the two columns
placing it against its value, and its rank. -/
def keyIdx (k : ℕ) : Fin (3 + k) → Fin (7 + k) :=
  Fin.append ![iV k, iSA k, iSB k] (fun j => iR j)

/-! ## Order columns on non-null values -/

theorem OrderCol.le_of_nonNull (cl : OrderCol) {a b : T} (ha : ValueType.isNull a = false)
    (hb : ValueType.isNull b = false) :
    cl.le a b = if cl.desc then decide (LE.le b a) else decide (LE.le a b) := by
  simp [OrderCol.le, ha, hb]

/-- **Two pairs of non-null values ordered alike compare alike.** -/
theorem OrderCol.le_congr_of_order (cl : OrderCol) {a b a' b' : T}
    (ha : ValueType.isNull a = false) (hb : ValueType.isNull b = false)
    (ha' : ValueType.isNull a' = false) (hb' : ValueType.isNull b' = false)
    (hlt : LT.lt a b ↔ LT.lt a' b') (heq : a = b ↔ a' = b') : cl.le a b = cl.le a' b' := by
  rw [OrderCol.le_of_nonNull cl ha hb, OrderCol.le_of_nonNull cl ha' hb']
  have hle : LE.le a b ↔ LE.le a' b' := by
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hlt, heq]
  have hge : LE.le b a ↔ LE.le b' a' := by
    rw [← not_lt, ← not_lt, hlt]
  split
  · exact decide_eq_decide.mpr hge
  · exact decide_eq_decide.mpr hle

/-- Two non-null values are peers exactly when equal. -/
theorem OrderCol.peer_iff_of_nonNull (cl : OrderCol) {a b : T} (ha : ValueType.isNull a = false)
    (hb : ValueType.isNull b = false) : cl.peer a b = true ↔ a = b := by
  unfold OrderCol.peer
  rw [Bool.and_eq_true, OrderCol.le_of_nonNull cl ha hb, OrderCol.le_of_nonNull cl hb ha]
  split <;> simp only [decide_eq_true_eq] <;> exact ⟨fun h => le_antisymm (by tauto) (by tauto),
    fun h => ⟨h ▸ le_refl _, h ▸ le_refl _⟩⟩

/-! ## The key of a cell -/

/-- **The key of a cell**: the columns an order reads. -/
def keyOf (e : Tuple T (7 + k)) : Tuple T (3 + k) := fun q => e (keyIdx k q)

/-- The key column of the value. -/
abbrev q0 (k : ℕ) : Fin (3 + k) := Fin.castAdd k 0
/-- The key column placing a code first. -/
abbrev q1 (k : ℕ) : Fin (3 + k) := Fin.castAdd k 1
/-- The key column placing a code second. -/
abbrev q2 (k : ℕ) : Fin (3 + k) := Fin.castAdd k 2

theorem finRange_key :
    List.finRange (3 + k) = [q0 k, q1 k, q2 k] ++ (List.finRange k).map (Fin.natAdd 3) := by
  rw [List.finRange_add_eq]
  rfl

section Keys

variable (C : Finset T)

theorem keyOf_conc_0 (a : T) : keyOf (enc C k (.conc a)) (q0 k) = a := rfl
theorem keyOf_conc_1 (a : T) : keyOf (enc C k (.conc a)) (q1 k) = sLo := rfl
theorem keyOf_conc_2 (a : T) : keyOf (enc C k (.conc a)) (q2 k) = sHi := rfl
theorem keyOf_conc_R (a : T) (j : Fin k) :
    keyOf (enc C k (.conc a)) (Fin.natAdd 3 j) = 0 := by
  simp [keyOf, keyIdx, Fin.append_right, enc]
theorem keyOf_fresh_0 (l : WithBot T) (r : ℕ) :
    keyOf (enc C k (.fresh l r)) (q0 k) = lval C l := rfl
theorem keyOf_fresh_1 (l : WithBot T) (r : ℕ) :
    keyOf (enc C k (.fresh l r)) (q1 k) = posA (.fresh l r) := rfl
theorem keyOf_fresh_2 (l : WithBot T) (r : ℕ) :
    keyOf (enc C k (.fresh l r)) (q2 k) = sLo := rfl
theorem keyOf_fresh_R (l : WithBot T) (r : ℕ) (j : Fin k) :
    keyOf (enc C k (.fresh l r)) (Fin.natAdd 3 j) = therm k r j := by
  simp [keyOf, keyIdx, Fin.append_right, enc]

end Keys

/-! ## The ranks, read lexicographically -/

theorem leOn_map {p p' : ℕ} (o : OrderSpec p) (f : Fin p' → Fin p) (x y : Tuple T p) :
    ∀ l : List (Fin p'), o.leOn (l.map f) x y = OrderSpec.leOn (fun j => o (f j) : OrderSpec p') l
      (fun j => x (f j)) (fun j => y (f j))
  | List.nil => rfl
  | List.cons j l => by
    simp only [List.map_cons, OrderSpec.leOn]
    rw [leOn_map o f x y l]

theorem therm_peer (cl : OrderCol) (r r' : ℕ) (j : Fin k) :
    cl.peer (therm (T := T) k r j) (therm (T := T) k r' j) = true
      ↔ therm (T := T) k r j = therm (T := T) k r' j := by
  have hn : ∀ r j, ValueType.isNull (therm (T := T) k r j) = false := fun r j => by
    rcases therm_def (T := T) k r j with h | h <;> rw [h]
    · exact isNull_sLo
    · exact isNull_sHi
  exact OrderCol.peer_iff_of_nonNull cl (hn r j) (hn r' j)

/-- **Two unary ranks compare as the ranks**, in the column's direction. -/
theorem leOn_therm (cl : OrderCol) {r r' : ℕ} (hr : r < k) (hr' : r' < k) :
    OrderSpec.leOn (fun _ => cl) (List.finRange k) (therm (T := T) k r) (therm k r')
      = if cl.desc then decide (LE.le r' r) else decide (LE.le r r') := by
  rcases lt_trichotomy r r' with h | rfl | h
  · obtain ⟨s, t, hst, hs⟩ := List.finRange_split (⟨r, hr⟩ : Fin k)
    rw [hst, OrderSpec.leOn_of_first _ _ _ _ _ _ (fun j hj => (therm_peer cl r r' j).mpr (by
        have := hs j hj
        rw [Fin.lt_def] at this
        unfold therm
        rw [ite_eq_left this, ite_eq_left (lt_trans this h)]))]
    · simp only [therm, lt_irrefl, ite_false, h, ite_true]
      rw [OrderCol.le_of_nonNull cl isNull_sLo isNull_sHi]
      split <;> simp [not_le.mpr sLo_lt_sHi, le_of_lt sLo_lt_sHi, not_le.mpr h, le_of_lt h]
    · rw [← Bool.not_eq_true, therm_peer]
      simp only [therm, lt_irrefl, ite_false, h, ite_true]
      exact sLo_ne_sHi
  · rw [OrderSpec.leOn_of_peers _ _ _ _ (fun j _ => (therm_peer cl r r j).mpr rfl)]
    split <;> simp
  · obtain ⟨s, t, hst, hs⟩ := List.finRange_split (⟨r', hr'⟩ : Fin k)
    rw [hst, OrderSpec.leOn_of_first _ _ _ _ _ _ (fun j hj => (therm_peer cl r r' j).mpr (by
        have := hs j hj
        rw [Fin.lt_def] at this
        unfold therm
        rw [ite_eq_left (lt_trans this h), ite_eq_left this]))]
    · simp only [therm, lt_irrefl, ite_false, h, ite_true]
      rw [OrderCol.le_of_nonNull cl isNull_sHi isNull_sLo]
      split <;> simp [not_le.mpr sLo_lt_sHi, le_of_lt sLo_lt_sHi, not_le.mpr h, le_of_lt h]
    · rw [← Bool.not_eq_true, therm_peer]
      simp only [therm, lt_irrefl, ite_false, h, ite_true]
      exact sLo_ne_sHi.symm

/-! ## The key read lexicographically -/

theorem leOn_append_of_peers {p : ℕ} (o : OrderSpec p) (x y : Tuple T p) (l₂ : List (Fin p)) :
    ∀ l₁ : List (Fin p), (∀ j ∈ l₁, (o j).peer (x j) (y j) = true) →
      o.leOn (l₁ ++ l₂) x y = o.leOn l₂ x y
  | List.nil, _ => rfl
  | List.cons j l₁, h => by
    simp only [List.cons_append, OrderSpec.leOn]
    rw [h j List.mem_cons_self, ite_eq_left rfl]
    exact leOn_append_of_peers o x y l₂ l₁ (fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- The lexicographic reading of two keys with one column direction. -/
abbrev leKey (cl : OrderCol) (X Y : Tuple T (3 + k)) : Bool :=
  OrderSpec.leOn (fun _ => cl) (List.finRange (3 + k)) X Y

theorem leKey_0 (cl : OrderCol) (X Y : Tuple T (3 + k))
    (h : cl.peer (X (q0 k)) (Y (q0 k)) = false) :
    leKey cl X Y = cl.le (X (q0 k)) (Y (q0 k)) := by
  unfold leKey
  rw [finRange_key]
  exact OrderSpec.leOn_of_first _ _ _ _ _ [] (fun j hj => absurd hj List.not_mem_nil) h

theorem leKey_1 (cl : OrderCol) (X Y : Tuple T (3 + k)) (h₀ : cl.peer (X (q0 k)) (Y (q0 k)) = true)
    (h : cl.peer (X (q1 k)) (Y (q1 k)) = false) :
    leKey cl X Y = cl.le (X (q1 k)) (Y (q1 k)) := by
  unfold leKey
  rw [finRange_key]
  exact OrderSpec.leOn_of_first _ _ _ _ _ [q0 k]
    (fun j hj => by rw [List.mem_singleton.mp hj]; exact h₀) h

theorem leKey_2 (cl : OrderCol) (X Y : Tuple T (3 + k)) (h₀ : cl.peer (X (q0 k)) (Y (q0 k)) = true)
    (h₁ : cl.peer (X (q1 k)) (Y (q1 k)) = true) (h : cl.peer (X (q2 k)) (Y (q2 k)) = false) :
    leKey cl X Y = cl.le (X (q2 k)) (Y (q2 k)) := by
  unfold leKey
  rw [finRange_key, show [q0 k, q1 k, q2 k] ++ (List.finRange k).map (Fin.natAdd 3)
    = [q0 k, q1 k] ++ q2 k :: (List.finRange k).map (Fin.natAdd 3) from rfl]
  exact OrderSpec.leOn_of_first _ _ _ _ _ [q0 k, q1 k]
    (fun j hj => by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact h₀
      · rw [List.mem_singleton.mp hj]; exact h₁) h

theorem leKey_3 (cl : OrderCol) (X Y : Tuple T (3 + k)) (h₀ : cl.peer (X (q0 k)) (Y (q0 k)) = true)
    (h₁ : cl.peer (X (q1 k)) (Y (q1 k)) = true) (h₂ : cl.peer (X (q2 k)) (Y (q2 k)) = true) :
    leKey cl X Y = OrderSpec.leOn (fun _ => cl) (List.finRange k)
      (fun j => X (Fin.natAdd 3 j)) (fun j => Y (Fin.natAdd 3 j)) := by
  unfold leKey
  rw [finRange_key, leOn_append_of_peers _ _ _ _ _ (fun j hj => by
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h₀
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h₁
    rw [List.mem_singleton.mp hj]; exact h₂), leOn_map]

/-! ## The value facts the key rests on -/

section Facts

variable {C : Finset T}

/-- **The least non-null value of the cut** is the bound of the gap below
everything, and is below every non-null value of the cut. -/
theorem lval_bot_le {a : T} (ha : a ∈ C) (han : ValueType.isNull a = false) :
    lval C ⊥ ∈ C ∧ ValueType.isNull (lval C ⊥) = false
      ∧ ∀ b ∈ C, ValueType.isNull b = false → LE.le (lval C ⊥) b := by
  have hne : (C.filter (fun t : T => ValueType.isNull t = false
      ∧ LT.lt (⊥ : WithBot T) (t : WithBot T))).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, han, WithBot.bot_lt_coe a⟩⟩
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have hmem := Finset.mem_of_min hm
  obtain ⟨hmC, hmn, -⟩ := Finset.mem_filter.mp hmem
  have hl : lval C ⊥ = m := by
    show wtVal (upOf C ⊥) = m
    unfold upOf
    rw [hm]; rfl
  rw [hl]
  refine ⟨hmC, hmn, fun b hb hbn => ?_⟩
  exact Finset.min_le_of_eq (Finset.mem_filter.mpr ⟨hb, hbn, WithBot.bot_lt_coe b⟩) hm

/-- A fresh value with no lower bound is below every non-null value of the
cut. -/
theorem lt_of_lo_bot {u : T} (hu : IsFresh C u) (hl : lo C u = ⊥) {b : T} (hb : b ∈ C)
    (hbn : ValueType.isNull b = false) : LT.lt u b := by
  rcases lt_or_gt_of_ne (ne_of_fresh hu hb) with h | h
  · have := (lt_iff_le_lo hb hbn).mp h
    rw [hl] at this
    exact absurd this (by simp)
  · exact h

end Facts

/-! ## The order of keys is the order of values -/

section KeyOrder

variable {C : Finset T}

theorem isNull_posA (x : Code T) : ValueType.isNull (posA x) = false := by
  cases x with
  | conc a => exact isNull_sLo
  | fresh l r => cases l <;> first | exact isNull_sLo | exact isNull_sHi

/-- **Two concrete cells' keys compare as their values.** -/
theorem leKey_conc_conc (cl : OrderCol) (a b : T) :
    leKey cl (keyOf (enc C k (.conc a))) (keyOf (enc C k (.conc b))) = cl.le a b := by
  by_cases hp : cl.peer a b = true
  · rw [leKey_3 cl _ _ hp (by rw [keyOf_conc_1, keyOf_conc_1]; exact OrderCol.peer_rfl _ _)
      (by rw [keyOf_conc_2, keyOf_conc_2]; exact OrderCol.peer_rfl _ _)]
    rw [OrderSpec.leOn_of_peers _ _ _ _ (fun j _ => by
      rw [keyOf_conc_R, keyOf_conc_R]; exact OrderCol.peer_rfl _ _)]
    unfold OrderCol.peer at hp
    exact ((Bool.and_eq_true _ _).mp hp).1.symm
  · exact leKey_0 cl _ _ (by rw [keyOf_conc_0, keyOf_conc_0]; simpa using hp)

theorem le_null_left (cl : OrderCol) {a b b' : T} (ha : ValueType.isNull a = true)
    (hb : ValueType.isNull b = false) (hb' : ValueType.isNull b' = false) :
    cl.le a b = cl.le a b' := by
  simp [OrderCol.le, ha, hb, hb']

theorem le_null_right (cl : OrderCol) {a a' b : T} (hb : ValueType.isNull b = true)
    (ha : ValueType.isNull a = false) (ha' : ValueType.isNull a' = false) :
    cl.le a b = cl.le a' b := by
  simp [OrderCol.le, ha, hb, ha']

theorem peer_null_nonNull (cl : OrderCol) {a b : T} (ha : ValueType.isNull a = true)
    (hb : ValueType.isNull b = false) : cl.peer a b = false :=
  OrderCol.not_peer_isNull cl ha hb

theorem peer_nonNull_null (cl : OrderCol) {a b : T} (ha : ValueType.isNull a = false)
    (hb : ValueType.isNull b = true) : cl.peer a b = false := by
  rw [OrderCol.peer_comm]; exact OrderCol.not_peer_isNull cl hb ha

theorem peer_false_of_ne (cl : OrderCol) {a b : T} (ha : ValueType.isNull a = false)
    (hb : ValueType.isNull b = false) (h : a ≠ b) : cl.peer a b = false := by
  rw [← Bool.not_eq_true, OrderCol.peer_iff_of_nonNull cl ha hb]; exact h

theorem peer_true_of_eq (cl : OrderCol) {a b : T} (h : a = b) : cl.peer a b = true := by
  subst h; exact OrderCol.peer_rfl _ _

/-- **A concrete cell's key against a fresh cell's compares as the values.** -/
theorem leKey_conc_fresh (cl : OrderCol) {par : Fin k → T} {i : Fin k} (hi : IsFresh C (par i))
    {a : T} (ha : a ∈ C ∨ ValueType.isNull a = true) :
    leKey cl (keyOf (enc C k (.conc a))) (keyOf (enc C k (code C par i))) = cl.le a (par i) := by
  rw [code_of_fresh hi]
  have hun := hi.2
  have hne : a ≠ par i := fresh_ne hi ha
  have hlvn := isNull_lval_lo (C := C) (par i)
  by_cases han : ValueType.isNull a = true
  · rw [leKey_0 cl _ _ (by rw [keyOf_conc_0, keyOf_fresh_0]; exact peer_null_nonNull cl han hlvn),
      keyOf_conc_0, keyOf_fresh_0]
    exact le_null_left cl han hlvn hun
  have han' : ValueType.isNull a = false := by simpa using han
  have haC : a ∈ C := ha.resolve_right han
  cases hl : lo C (par i) with
  | bot =>
    obtain ⟨hmC, hmn, hmin⟩ := lval_bot_le haC han'
    have hua : LT.lt (par i) a := lt_of_lo_bot hi hl haC han'
    by_cases ham : a = lval C ⊥
    · rw [leKey_2 cl _ _ (by rw [keyOf_conc_0, keyOf_fresh_0]; exact peer_true_of_eq cl ham)
        (by rw [keyOf_conc_1, keyOf_fresh_1]; exact peer_true_of_eq cl rfl)
        (by
          rw [keyOf_conc_2, keyOf_fresh_2]
          exact peer_false_of_ne cl isNull_sHi isNull_sLo sLo_ne_sHi.symm),
        keyOf_conc_2, keyOf_fresh_2]
      refine OrderCol.le_congr_of_order cl isNull_sHi isNull_sLo han' hun ?_ ?_
      · exact ⟨fun h => absurd h (not_lt.mpr sLo_lt_sHi.le), fun h => absurd (h.trans hua)
          (lt_irrefl _)⟩
      · exact ⟨fun h => absurd h sLo_ne_sHi.symm, fun h => absurd h hne⟩
    · rw [leKey_0 cl _ _ (by
          rw [keyOf_conc_0, keyOf_fresh_0]
          exact peer_false_of_ne cl han' hmn ham),
        keyOf_conc_0, keyOf_fresh_0]
      refine OrderCol.le_congr_of_order cl han' hmn han' hun ?_ ?_
      · exact ⟨fun h => absurd (hmin a haC han') (not_le.mpr h), fun h => absurd (h.trans hua)
          (lt_irrefl _)⟩
      · exact ⟨fun h => absurd h ham, fun h => absurd h hne⟩
  | coe l =>
    obtain ⟨hlC, hln, hlu⟩ := lo_eq_coe hl
    have hle : LT.lt a (par i) ↔ LE.le a l := by
      rw [lt_iff_le_lo haC han', hl, WithBot.coe_le_coe]
    by_cases hal : a = l
    · rw [leKey_1 cl _ _ (by rw [keyOf_conc_0, keyOf_fresh_0]; exact peer_true_of_eq cl hal)
        (by
          rw [keyOf_conc_1, keyOf_fresh_1]
          exact peer_false_of_ne cl isNull_sLo isNull_sHi sLo_ne_sHi),
        keyOf_conc_1, keyOf_fresh_1]
      refine OrderCol.le_congr_of_order cl isNull_sLo isNull_sHi han' hun ?_ ?_
      · exact ⟨fun _ => hal ▸ hlu, fun _ => sLo_lt_sHi⟩
      · exact ⟨fun h => absurd h sLo_ne_sHi, fun h => absurd h hne⟩
    · rw [leKey_0 cl _ _ (by
          rw [keyOf_conc_0, keyOf_fresh_0]
          exact peer_false_of_ne cl han' hln hal),
        keyOf_conc_0, keyOf_fresh_0]
      refine OrderCol.le_congr_of_order cl han' hln han' hun ?_ ?_
      · exact ⟨fun h => h.trans hlu, fun h => lt_of_le_of_ne (hle.mp h) hal⟩
      · exact ⟨fun h => absurd h hal, fun h => absurd h hne⟩

/-- **A fresh cell's key against a concrete cell's compares as the values.** -/
theorem leKey_fresh_conc (cl : OrderCol) {par : Fin k → T} {i : Fin k} (hi : IsFresh C (par i))
    {a : T} (ha : a ∈ C ∨ ValueType.isNull a = true) :
    leKey cl (keyOf (enc C k (code C par i))) (keyOf (enc C k (.conc a))) = cl.le (par i) a := by
  rw [code_of_fresh hi]
  have hun := hi.2
  have hne : par i ≠ a := (fresh_ne hi ha).symm
  have hlvn := isNull_lval_lo (C := C) (par i)
  by_cases han : ValueType.isNull a = true
  · rw [leKey_0 cl _ _ (by rw [keyOf_conc_0, keyOf_fresh_0]; exact peer_nonNull_null cl hlvn han),
      keyOf_conc_0, keyOf_fresh_0]
    exact le_null_right cl han hlvn hun
  have han' : ValueType.isNull a = false := by simpa using han
  have haC : a ∈ C := ha.resolve_right han
  cases hl : lo C (par i) with
  | bot =>
    obtain ⟨hmC, hmn, hmin⟩ := lval_bot_le haC han'
    have hua : LT.lt (par i) a := lt_of_lo_bot hi hl haC han'
    by_cases ham : a = lval C ⊥
    · rw [leKey_2 cl _ _ (by rw [keyOf_conc_0, keyOf_fresh_0]; exact peer_true_of_eq cl ham.symm)
        (by rw [keyOf_conc_1, keyOf_fresh_1]; exact peer_true_of_eq cl rfl)
        (by
          rw [keyOf_conc_2, keyOf_fresh_2]
          exact peer_false_of_ne cl isNull_sLo isNull_sHi sLo_ne_sHi),
        keyOf_conc_2, keyOf_fresh_2]
      refine OrderCol.le_congr_of_order cl isNull_sLo isNull_sHi hun han' ?_ ?_
      · exact ⟨fun _ => hua, fun _ => sLo_lt_sHi⟩
      · exact ⟨fun h => absurd h sLo_ne_sHi, fun h => absurd h hne⟩
    · rw [leKey_0 cl _ _ (by
          rw [keyOf_conc_0, keyOf_fresh_0]
          exact peer_false_of_ne cl hmn han' (Ne.symm ham)),
        keyOf_conc_0, keyOf_fresh_0]
      refine OrderCol.le_congr_of_order cl hmn han' hun han' ?_ ?_
      · exact ⟨fun _ => hua, fun _ => lt_of_le_of_ne (hmin a haC han') (Ne.symm ham)⟩
      · exact ⟨fun h => absurd h.symm ham, fun h => absurd h hne⟩
  | coe l =>
    obtain ⟨hlC, hln, hlu⟩ := lo_eq_coe hl
    have hle : LT.lt a (par i) ↔ LE.le a l := by
      rw [lt_iff_le_lo haC han', hl, WithBot.coe_le_coe]
    by_cases hal : a = l
    · rw [leKey_1 cl _ _ (by rw [keyOf_conc_0, keyOf_fresh_0]; exact peer_true_of_eq cl hal.symm)
        (by
          rw [keyOf_conc_1, keyOf_fresh_1]
          exact peer_false_of_ne cl isNull_sHi isNull_sLo sLo_ne_sHi.symm),
        keyOf_conc_1, keyOf_fresh_1]
      refine OrderCol.le_congr_of_order cl isNull_sHi isNull_sLo hun han' ?_ ?_
      · exact ⟨fun h => absurd h (not_lt.mpr sLo_lt_sHi.le),
          fun h => absurd (h.trans (hal ▸ hlu)) (lt_irrefl _)⟩
      · exact ⟨fun h => absurd h sLo_ne_sHi.symm, fun h => absurd h hne⟩
    · rw [leKey_0 cl _ _ (by
          rw [keyOf_conc_0, keyOf_fresh_0]
          exact peer_false_of_ne cl hln han' (Ne.symm hal)),
        keyOf_conc_0, keyOf_fresh_0]
      refine OrderCol.le_congr_of_order cl hln han' hun han' ?_ ?_
      · refine ⟨fun h => ?_, fun h => hlu.trans h⟩
        rcases lt_or_gt_of_ne hne with h' | h'
        · exact h'
        · exact absurd (hle.mp h') (not_le.mpr h)
      · exact ⟨fun h => absurd h.symm hal, fun h => absurd h hne⟩

/-- **Two fresh cells' keys compare as their values.** -/
theorem leKey_fresh_fresh (cl : OrderCol) {par : Fin k → T} {i j : Fin k}
    (hi : IsFresh C (par i)) (hj : IsFresh C (par j)) :
    leKey cl (keyOf (enc C k (code C par i))) (keyOf (enc C k (code C par j)))
      = cl.le (par i) (par j) := by
  rw [code_of_fresh hi, code_of_fresh hj]
  have hun := hi.2
  have hun' := hj.2
  have hli := isNull_lval_lo (C := C) (par i)
  have hlj := isNull_lval_lo (C := C) (par j)
  by_cases hll : lo C (par i) = lo C (par j)
  · rw [leKey_3 cl _ _ (by rw [keyOf_fresh_0, keyOf_fresh_0, hll]; exact peer_true_of_eq cl rfl)
      (by
        rw [keyOf_fresh_1, keyOf_fresh_1, hll]
        exact peer_true_of_eq cl (by cases lo C (par j) <;> rfl))
      (by rw [keyOf_fresh_2, keyOf_fresh_2]; exact peer_true_of_eq cl rfl)]
    simp only [keyOf_fresh_R]
    rw [leOn_therm cl (rank_code_lt i) (rank_code_lt j), OrderCol.le_of_nonNull cl hun hun']
    have hlt := lt_iff_rank_lt (mem_image par i) (mem_image par j) hi hj hll
    have heq := eq_iff_rank_eq (mem_image par i) (mem_image par j) hi hj hll
    have hlt' := lt_iff_rank_lt (mem_image par j) (mem_image par i) hj hi hll.symm
    have heq' := eq_iff_rank_eq (mem_image par j) (mem_image par i) hj hi hll.symm
    split
    · refine decide_eq_decide.mpr ?_
      rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hlt', heq']
    · refine decide_eq_decide.mpr ?_
      rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hlt, heq]
  have hne : par i ≠ par j := fun h => hll (h ▸ rfl)
  cases hl : lo C (par i) with
  | bot =>
    cases hl' : lo C (par j) with
    | bot => exact absurd (hl.trans hl'.symm) hll
    | coe l₂ =>
      obtain ⟨hl₂C, hl₂n, -⟩ := lo_eq_coe hl'
      obtain ⟨hmC, hmn, hmin⟩ := lval_bot_le hl₂C hl₂n
      have hu : LT.lt (par i) (par j) := lt_of_lo_lt (by rw [hl, hl']; exact WithBot.bot_lt_coe l₂)
      by_cases hm : lval C ⊥ = l₂
      · rw [leKey_1 cl _ _ (by rw [keyOf_fresh_0, keyOf_fresh_0]; exact peer_true_of_eq cl hm)
          (by
            rw [keyOf_fresh_1, keyOf_fresh_1]
            exact peer_false_of_ne cl isNull_sLo isNull_sHi sLo_ne_sHi),
          keyOf_fresh_1, keyOf_fresh_1]
        exact OrderCol.le_congr_of_order cl isNull_sLo isNull_sHi hun hun'
          ⟨fun _ => hu, fun _ => sLo_lt_sHi⟩ ⟨fun h => absurd h sLo_ne_sHi, fun h => absurd h hne⟩
      · rw [leKey_0 cl _ _ (by
            rw [keyOf_fresh_0, keyOf_fresh_0]
            exact peer_false_of_ne cl hmn hl₂n hm),
          keyOf_fresh_0, keyOf_fresh_0]
        exact OrderCol.le_congr_of_order cl hmn hl₂n hun hun'
          ⟨fun _ => hu, fun _ => lt_of_le_of_ne (hmin l₂ hl₂C hl₂n) hm⟩
          ⟨fun h => absurd h hm, fun h => absurd h hne⟩
  | coe l₁ =>
    obtain ⟨hl₁C, hl₁n, -⟩ := lo_eq_coe hl
    cases hl' : lo C (par j) with
    | bot =>
      obtain ⟨hmC, hmn, hmin⟩ := lval_bot_le hl₁C hl₁n
      have hu : LT.lt (par j) (par i) := lt_of_lo_lt (by rw [hl, hl']; exact WithBot.bot_lt_coe l₁)
      by_cases hm : lval C ⊥ = l₁
      · rw [leKey_1 cl _ _ (by rw [keyOf_fresh_0, keyOf_fresh_0]; exact peer_true_of_eq cl hm.symm)
          (by
            rw [keyOf_fresh_1, keyOf_fresh_1]
            exact peer_false_of_ne cl isNull_sHi isNull_sLo sLo_ne_sHi.symm),
          keyOf_fresh_1, keyOf_fresh_1]
        exact OrderCol.le_congr_of_order cl isNull_sHi isNull_sLo hun hun'
          ⟨fun h => absurd h (not_lt.mpr sLo_lt_sHi.le), fun h => absurd (h.trans hu) (lt_irrefl _)⟩
          ⟨fun h => absurd h sLo_ne_sHi.symm, fun h => absurd h hne⟩
      · rw [leKey_0 cl _ _ (by
            rw [keyOf_fresh_0, keyOf_fresh_0]
            exact peer_false_of_ne cl hl₁n hmn (Ne.symm hm)),
          keyOf_fresh_0, keyOf_fresh_0]
        exact OrderCol.le_congr_of_order cl hl₁n hmn hun hun'
          ⟨fun h => absurd (h.trans_le (hmin l₁ hl₁C hl₁n)) (lt_irrefl _),
            fun h => absurd (h.trans hu) (lt_irrefl _)⟩
          ⟨fun h => absurd h.symm hm, fun h => absurd h hne⟩
    | coe l₂ =>
      obtain ⟨hl₂C, hl₂n, -⟩ := lo_eq_coe hl'
      have h12 : l₁ ≠ l₂ := fun h => hll (by rw [hl, hl', h])
      rw [leKey_0 cl _ _ (by
          rw [keyOf_fresh_0, keyOf_fresh_0]
          exact peer_false_of_ne cl hl₁n hl₂n h12),
        keyOf_fresh_0, keyOf_fresh_0]
      refine OrderCol.le_congr_of_order cl hl₁n hl₂n hun hun' ⟨fun h => ?_, fun h => ?_⟩
        ⟨fun h => absurd h h12, fun h => absurd h hne⟩
      · exact lt_of_lo_lt (by rw [hl, hl']; exact WithBot.coe_lt_coe.mpr h)
      · have := lo_mono (C := C) h.le
        rw [hl, hl', WithBot.coe_le_coe] at this
        exact lt_of_le_of_ne this h12

/-- **The keys of two cells compare as the values they stand for**, in
every column direction and null placement. -/
theorem leKey_dec (cl : OrderCol) {par : Fin k → T} {x y : Code T} (hx : CodeOK C par x)
    (hy : CodeOK C par y) :
    leKey cl (keyOf (enc C k x)) (keyOf (enc C k y)) = cl.le (dec C par x) (dec C par y) := by
  rcases hx with ⟨i, hi, rfl⟩ | ⟨a, ha, rfl⟩ <;> rcases hy with ⟨j, hj, rfl⟩ | ⟨b, hb, rfl⟩
  · rw [dec_code, dec_code]; exact leKey_fresh_fresh cl hi hj
  · rw [dec_code]; exact leKey_fresh_conc cl hi hb
  · rw [dec_code]; exact leKey_conc_fresh cl hj ha
  · exact leKey_conc_conc cl a b

/-- **The key columns of two cells are peers throughout exactly when the
values they stand for are peers.** -/
theorem keyPeer_iff (cl : OrderCol) {par : Fin k → T} {x y : Code T} (hx : CodeOK C par x)
    (hy : CodeOK C par y) :
    (∀ q, cl.peer (keyOf (enc C k x) q) (keyOf (enc C k y) q) = true)
      ↔ cl.peer (dec C par x) (dec C par y) = true := by
  constructor
  · intro h
    unfold OrderCol.peer
    rw [← leKey_dec cl hx hy, ← leKey_dec cl hy hx, Bool.and_eq_true]
    exact ⟨OrderSpec.leOn_of_peers _ _ _ _ (fun q _ => h q),
      OrderSpec.leOn_of_peers _ _ _ _ (fun q _ => by rw [OrderCol.peer_comm]; exact h q)⟩
  · intro h q
    by_cases hn : ValueType.isNull (dec C par x) = true
    · -- both null concrete cells
      have hxc : ∃ a, ValueType.isNull a = true ∧ x = .conc a := by
        rcases hx with ⟨i, hi, rfl⟩ | ⟨a, -, rfl⟩
        · rw [dec_code, hi.2] at hn; exact absurd hn (by decide)
        · exact ⟨a, hn, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hxc
      have hyn : ValueType.isNull (dec C par y) = true := by
        by_contra hc
        rw [show dec C par (.conc a) = a from rfl] at h
        exact absurd h (by rw [peer_null_nonNull cl ha (by simpa using hc)]; decide)
      have hyc : ∃ b, ValueType.isNull b = true ∧ y = .conc b := by
        rcases hy with ⟨j, hj, rfl⟩ | ⟨b, -, rfl⟩
        · rw [dec_code, hj.2] at hyn; exact absurd hyn (by decide)
        · exact ⟨b, hyn, rfl⟩
      obtain ⟨b, hb, rfl⟩ := hyc
      refine Fin.addCases (fun q' => ?_) (fun j => ?_) q
      · match q' with
        | ⟨0, _⟩ => exact OrderCol.peer_of_isNull cl ha hb
        | ⟨1, _⟩ => exact OrderCol.peer_rfl _ _
        | ⟨2, _⟩ => exact OrderCol.peer_rfl _ _
      · rw [keyOf_conc_R, keyOf_conc_R]; exact OrderCol.peer_rfl _ _
    · have hxn : ValueType.isNull (dec C par x) = false := by simpa using hn
      have hyn : ValueType.isNull (dec C par y) = false := by
        by_contra hc
        have : ValueType.isNull (dec C par y) = true := by simpa using hc
        rw [OrderCol.peer_comm, peer_null_nonNull cl this hxn] at h
        exact absurd h (by decide)
      have heq : dec C par x = dec C par y := (OrderCol.peer_iff_of_nonNull cl hxn hyn).mp h
      have hvx : Valid C par x := by
        rcases hx with ⟨i, hi, rfl⟩ | ⟨a, ha, rfl⟩
        · exact Or.inl ⟨i, hi, rfl⟩
        · exact Or.inr ⟨a, ha.resolve_right (by
            have : ValueType.isNull a = false := hxn
            simp [this]), hxn, rfl⟩
      have hvy : Valid C par y := by
        rcases hy with ⟨i, hi, rfl⟩ | ⟨a, ha, rfl⟩
        · exact Or.inl ⟨i, hi, rfl⟩
        · exact Or.inr ⟨a, ha.resolve_right (by
            have : ValueType.isNull a = false := hyn
            simp [this]), hyn, rfl⟩
      rw [(Code.eq_iff hvx hvy).mpr heq]
      exact OrderCol.peer_rfl _ _

end KeyOrder

/-! ## A clause over the keys of its columns' cells -/

section Expand

variable {C : Finset T} {p : ℕ}

/-- **The clause read over the keys**: each of its columns becomes the
`3 + k` columns of its cell's key, with the column's direction and null
placement. -/
def expandSpec (o : OrderSpec p) : OrderSpec (p * (3 + k)) :=
  fun z => o (finProdFinEquiv.symm z).1

/-- The keys of the cells a clause reads, flattened. -/
def flatKey (X : Fin p → Tuple T (7 + k)) : Tuple T (p * (3 + k)) :=
  fun z => keyOf (X (finProdFinEquiv.symm z).1) (finProdFinEquiv.symm z).2

omit [ValueType T] in
theorem lt_pair_of_lt {w : ℕ} {ℓ ℓ₀ : Fin p} {q q₀ : Fin w}
    (h : LT.lt (finProdFinEquiv (ℓ, q)) (finProdFinEquiv (ℓ₀, q₀))) :
    LT.lt ℓ ℓ₀ ∨ (ℓ = ℓ₀ ∧ LT.lt q q₀) := by
  rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val] at h
  by_cases hl : ℓ.val < ℓ₀.val
  · exact Or.inl hl
  · by_cases he : ℓ.val = ℓ₀.val
    · refine Or.inr ⟨Fin.ext he, ?_⟩
      simp only at h
      rw [he] at h
      exact Fin.lt_def.mpr (by omega)
    · exfalso
      have hgt : ℓ₀.val + 1 ≤ ℓ.val := by omega
      have := Nat.mul_le_mul_left w hgt
      have hq₀ := q₀.isLt
      simp only at h
      rw [Nat.mul_add, Nat.mul_one] at this
      omega

/-- **The clause over the keys orders the rows as the clause orders the
values the cells stand for.** -/
theorem le_expand (o : OrderSpec p) {par : Fin k → T} (cx cy : Fin p → Code T)
    (hx : ∀ ℓ, CodeOK C par (cx ℓ)) (hy : ∀ ℓ, CodeOK C par (cy ℓ)) :
    (expandSpec o).le (flatKey (fun ℓ => enc C k (cx ℓ))) (flatKey (fun ℓ => enc C k (cy ℓ)))
      = o.le (fun ℓ => dec C par (cx ℓ)) (fun ℓ => dec C par (cy ℓ)) := by
  classical
  -- a column of the flattened keys is a key column of one cell
  have hcol : ∀ ℓ q, (expandSpec (k := k) o (finProdFinEquiv (ℓ, q))).peer
      (flatKey (fun ℓ => enc C k (cx ℓ)) (finProdFinEquiv (ℓ, q)))
      (flatKey (fun ℓ => enc C k (cy ℓ)) (finProdFinEquiv (ℓ, q)))
      = (o ℓ).peer (keyOf (enc C k (cx ℓ)) q) (keyOf (enc C k (cy ℓ)) q) := by
    intro ℓ q
    simp [expandSpec, flatKey]
  by_cases hall : ∀ ℓ, (o ℓ).peer (dec C par (cx ℓ)) (dec C par (cy ℓ)) = true
  · rw [OrderSpec.le_of_all_peers _ _ _ hall, OrderSpec.le_of_all_peers]
    intro z
    obtain ⟨⟨ℓ, q⟩, rfl⟩ := finProdFinEquiv.surjective z
    rw [hcol]
    exact (keyPeer_iff (o ℓ) (hx ℓ) (hy ℓ)).mpr (hall ℓ) q
  push Not at hall
  -- the first column not peer
  let S := Finset.univ.filter (fun ℓ => (o ℓ).peer (dec C par (cx ℓ)) (dec C par (cy ℓ)) ≠ true)
  have hS : S.Nonempty := by
    obtain ⟨ℓ, hℓ⟩ := hall
    exact ⟨ℓ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ⟩⟩
  let ℓ₀ := S.min' hS
  have hℓ₀ : (o ℓ₀).peer (dec C par (cx ℓ₀)) (dec C par (cy ℓ₀)) = false := by
    have := (Finset.mem_filter.mp (S.min'_mem hS)).2
    simpa using this
  have hbelow : ∀ ℓ, LT.lt ℓ ℓ₀ → (o ℓ).peer (dec C par (cx ℓ)) (dec C par (cy ℓ)) = true := by
    intro ℓ hℓ
    by_contra hc
    exact absurd (S.min'_le ℓ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)) (not_le.mpr hℓ)
  rw [OrderSpec.le_of_first_idx _ _ _ ℓ₀ hbelow hℓ₀]
  -- inside its block, the first key column not peer
  have hblk : ¬ ∀ q, (o ℓ₀).peer (keyOf (enc C k (cx ℓ₀)) q) (keyOf (enc C k (cy ℓ₀)) q) = true :=
    fun h => by rw [(keyPeer_iff (o ℓ₀) (hx ℓ₀) (hy ℓ₀)).mp h] at hℓ₀; exact absurd hℓ₀ (by decide)
  push Not at hblk
  let Sq := Finset.univ.filter (fun q => (o ℓ₀).peer (keyOf (enc C k (cx ℓ₀)) q)
    (keyOf (enc C k (cy ℓ₀)) q) ≠ true)
  have hSq : Sq.Nonempty := by
    obtain ⟨q, hq⟩ := hblk
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
  let q₀ := Sq.min' hSq
  have hq₀ : (o ℓ₀).peer (keyOf (enc C k (cx ℓ₀)) q₀) (keyOf (enc C k (cy ℓ₀)) q₀) = false := by
    have := (Finset.mem_filter.mp (Sq.min'_mem hSq)).2
    simpa using this
  have hqbelow : ∀ q, LT.lt q q₀ →
      (o ℓ₀).peer (keyOf (enc C k (cx ℓ₀)) q) (keyOf (enc C k (cy ℓ₀)) q) = true := by
    intro q hq
    by_contra hc
    exact absurd (Sq.min'_le q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)) (not_le.mpr hq)
  rw [OrderSpec.le_of_first_idx _ _ _ (finProdFinEquiv (ℓ₀, q₀)) (fun z hz => by
      obtain ⟨⟨ℓ, q⟩, rfl⟩ := finProdFinEquiv.surjective z
      rw [hcol]
      rcases lt_pair_of_lt hz with hl | ⟨rfl, hq⟩
      · exact (keyPeer_iff (o ℓ) (hx ℓ) (hy ℓ)).mpr (hbelow ℓ hl) q
      · exact hqbelow q hq) (by rw [hcol]; exact hq₀)]
  -- the block's key decides, as the cell's values do
  have hkey := leKey_dec (o ℓ₀) (hx ℓ₀) (hy ℓ₀)
  unfold leKey at hkey
  rw [← hkey]
  show _ = OrderSpec.le (fun _ => o ℓ₀) (keyOf (enc C k (cx ℓ₀))) (keyOf (enc C k (cy ℓ₀)))
  rw [OrderSpec.le_of_first_idx _ _ _ q₀ hqbelow hq₀]
  simp [expandSpec, flatKey]

/-- **A frame condition read over the keys.** -/
def expandCond : FrameCond p → FrameCond (p * (3 + k))
  | .whole => .whole
  | .le o => .le (expandSpec o)
  | .lt o => .lt (expandSpec o)
  | .ge o => .ge (expandSpec o)
  | .gt o => .gt (expandSpec o)
  | .and a b => .and (expandCond a) (expandCond b)
  | .or a b => .or (expandCond a) (expandCond b)
  | .orAll cs => .orAll (fun j => expandCond (cs j))

/-- **A frame condition over the keys holds as it does over the values.** -/
theorem holds_expandCond {par : Fin k → T} (cx cy : Fin p → Code T)
    (hx : ∀ ℓ, CodeOK C par (cx ℓ)) (hy : ∀ ℓ, CodeOK C par (cy ℓ)) :
    ∀ c : FrameCond p, (expandCond (k := k) c).holds (flatKey (fun ℓ => enc C k (cx ℓ)))
        (flatKey (fun ℓ => enc C k (cy ℓ)))
      = c.holds (fun ℓ => dec C par (cx ℓ)) (fun ℓ => dec C par (cy ℓ))
  | .whole => rfl
  | .le o => le_expand o cx cy hx hy
  | .lt o => by
    show (!(expandSpec (k := k) o).le (flatKey (fun ℓ => enc C k (cy ℓ)))
      (flatKey (fun ℓ => enc C k (cx ℓ))))
      = (!o.le (fun ℓ => dec C par (cy ℓ)) (fun ℓ => dec C par (cx ℓ)))
    rw [le_expand o cy cx hy hx]
  | .ge o => le_expand o cy cx hy hx
  | .gt o => by
    show (!(expandSpec (k := k) o).le (flatKey (fun ℓ => enc C k (cx ℓ)))
      (flatKey (fun ℓ => enc C k (cy ℓ))))
      = (!o.le (fun ℓ => dec C par (cx ℓ)) (fun ℓ => dec C par (cy ℓ)))
    rw [le_expand o cx cy hx hy]
  | .and a b => by
    show ((expandCond a).holds _ _ && (expandCond b).holds _ _) = (a.holds _ _ && b.holds _ _)
    rw [holds_expandCond cx cy hx hy a, holds_expandCond cx cy hx hy b]
  | .or a b => by
    show ((expandCond a).holds _ _ || (expandCond b).holds _ _) = (a.holds _ _ || b.holds _ _)
    rw [holds_expandCond cx cy hx hy a, holds_expandCond cx cy hx hy b]
  | .orAll cs => by
    show (List.finRange _).any (fun j => (expandCond (cs j)).holds _ _)
      = (List.finRange _).any (fun j => (cs j).holds _ _)
    congr 1
    funext j
    exact holds_expandCond cx cy hx hy (cs j)

end Expand

/-! ## The window over symbolic rows -/

omit [ValueType T] in
theorem Multiset.mem_of_mem_erase_any {α : Type} (i : DecidableEq α) {s : Multiset α} {a b : α}
    (h : b ∈ @Multiset.erase α i s a) : b ∈ s := by
  let := i
  exact Multiset.mem_of_mem_erase h

omit [ValueType T] in
/-- **Erasing an image is imaging the erasure**, an injective map, whatever
decidable equality each side is read with. -/
theorem Multiset.map_erase_inj' {α β : Type} (i₁ : DecidableEq β) (i₂ : DecidableEq α)
    {f : α → β} (hf : Function.Injective f) (s : Multiset α) (a : α) :
    @Multiset.erase β i₁ (s.map f) (f a) = (@Multiset.erase α i₂ s a).map f := by
  have := (@Multiset.map_erase α β i₂ i₁ f hf a s).symm
  exact this

section Window

variable {C : Finset T} {c n m p : ℕ}

/-- A counting aggregate over a frame reads how many of its kept values are
not null. -/
theorem windowValueOpt_readsCount {c' n' : ℕ} {f : SeqAggFunc T} (hf : f.ReadsCount)
    (P : Tuple (Fin n') m) (O : Tuple (Fin n') p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c' n') (keep : Option (Selection T n')) (R : Multiset (Tuple T n'))
    (u : Tuple T n') (γ : Fin c' → T) :
    ValueFrame.windowValueOpt P O o w t f keep R u γ
      = hf.choose ((((ValueFrame.frameOf id P O w R u).filter
          (fun y => Selection.keepsOpt keep y = true)).map (fun v => t.eval v γ)).countP
            (fun x => ValueType.isNull x = false)) := by
  cases keep with
  | none =>
    show f ((ValueFrame.frameListOf (α := Tuple T n') id P O o w R u).map _) = _
    rw [hf.choose_spec, ← ValueFrame.frameListOf_coe id P O o w R u, Multiset.filter_coe,
      Multiset.map_coe, Multiset.coe_countP]
    refine congrArg hf.choose ?_
    rw [List.filter_eq_self.mpr (fun _ _ => by simp [Selection.keepsOpt])]
    exact List.countP_congr (fun x _ => by simp)
  | some φ =>
    show f (((ValueFrame.frameListOf (α := Tuple T n') id P O o w R u).filter φ.keeps).map _) = _
    rw [hf.choose_spec, ← ValueFrame.frameListOf_coe id P O o w R u, Multiset.filter_coe,
      Multiset.map_coe, Multiset.coe_countP]
    refine congrArg hf.choose ?_
    simp [Selection.keepsOpt]

/-- **The order columns of a symbolic window**: the key columns of the
cells the clause reads. -/
def winOIdx (O : Tuple (Fin n) p) : Tuple (Fin ((k + n) * (7 + k))) (p * (3 + k)) :=
  fun z => ci (Fin.natAdd k (O (finProdFinEquiv.symm z).1)) (keyIdx k (finProdFinEquiv.symm z).2)

theorem key_winOIdx (C : Finset T) (O : Tuple (Fin n) p) (par : Fin k → T) (v : Tuple T n) :
    Tuple.key (winOIdx O) (rowEnc C par v)
      = flatKey (fun ℓ => enc C k (vcode C par (v (O ℓ)))) := by
  funext z
  show cellOf (rowEnc C par v) (Fin.natAdd k (O (finProdFinEquiv.symm z).1))
    (keyIdx k (finProdFinEquiv.symm z).2) = _
  rw [rowEnc, cellOf_ofCells, Fin.append_right]
  rfl

/-- **The frame expanded over the keys.** -/
def expandFrame (w : ValueFrame T p) : ValueFrame T (p * (3 + k)) :=
  ⟨expandCond w.cond, w.self⟩

omit [ValueType T] in
/-- **A frame of SQL read over the keys is one**, under the clause read over
the keys: each comparison is the same comparison under the expanded clause. -/
theorem isSQLUnder_expandFrame {o : OrderSpec p} {w : ValueFrame T p}
    (h : w.IsSQLUnder o) : (expandFrame (k := k) w).IsSQLUnder (expandSpec o) := by
  cases h with
  | noOthers hc => cases hc <;> sql_frame_under
  | current hc => cases hc <;> sql_frame_under
  | group hc => cases hc <;> sql_frame_under
  | ties hc => cases hc <;> sql_frame_under
  | before => sql_frame_under
  | after => sql_frame_under

omit [ValueType T] in
theorem isSQL_expandFrame {o : OrderSpec p} {w : ValueFrame T p} (h : w.IsSQL o) :
    (expandFrame (k := k) w).IsSQL (expandSpec o) :=
  h.imp isSQLUnder_expandFrame isSQLUnder_expandFrame

/-- `sql_frame` also sees through a frame read over the keys. -/
macro_rules
  | `(tactic| sql_frame) => `(tactic| (apply Sym.isSQL_expandFrame; sql_frame))

/-- **The frame of an encoded row is the encoding of the frame.** -/
theorem frameOf_slice (par : Fin k → T) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) {Q : Multiset (Tuple T ((k + n) * (7 + k)))} {R : Multiset (Tuple T n)}
    (hsl : Q.filter (fun r => descP (P := 0) r = descEnc C par) = R.map (rowEnc C par))
    (hR : ∀ v ∈ R, ∀ i, GoodVal (C := C) par (v i)) {v : Tuple T n} (hv : v ∈ R) :
    ValueFrame.frameOf id (gKeyIdx P) (winOIdx O) (expandFrame (k := k) w) Q (rowEnc C par v)
      = (ValueFrame.frameOf id P O w R v).map (rowEnc C par) := by
  classical
  have hinj := rowEnc_injective (C := C) (n := n) par
  -- the rows of the partition the condition keeps
  have hfil : Q.filter (fun y => Tuple.key (gKeyIdx P) (id y)
        = Tuple.key (gKeyIdx P) (id (rowEnc C par v))
        ∧ (expandFrame (k := k) w).ρ (Tuple.key (winOIdx O) (id y))
          (Tuple.key (winOIdx O) (id (rowEnc C par v))) = true)
      = (R.filter (fun y => Tuple.key P (id y) = Tuple.key P (id v)
        ∧ w.ρ (Tuple.key O (id y)) (Tuple.key O (id v)) = true)).map (rowEnc C par) := by
    have h1 : Q.filter (fun y => Tuple.key (gKeyIdx P) (id y)
          = Tuple.key (gKeyIdx P) (id (rowEnc C par v))
          ∧ (expandFrame (k := k) w).ρ (Tuple.key (winOIdx O) (id y))
            (Tuple.key (winOIdx O) (id (rowEnc C par v))) = true)
        = (Q.filter (fun r => descP (P := 0) r = descEnc C par)).filter (fun y =>
          Tuple.key (gKeyIdx P) (id y) = Tuple.key (gKeyIdx P) (id (rowEnc C par v))
          ∧ (expandFrame (k := k) w).ρ (Tuple.key (winOIdx O) (id y))
            (Tuple.key (winOIdx O) (id (rowEnc C par v))) = true) := by
      rw [Multiset.filter_filter]
      refine Multiset.filter_congr (fun y _ => ⟨fun h => ⟨h, ?_⟩, And.left⟩)
      have hk := congrArg keyDesc h.1
      simp only [id] at hk
      erw [keyDesc_key P y, keyDesc_key P (rowEnc C par v)] at hk
      rw [hk, ← rowEncP_elim0, descP_rowEncP]
    rw [h1, hsl, Multiset.filter_map]
    congr 1
    refine Multiset.filter_congr (fun y hy => ?_)
    simp only [Function.comp, id]
    show Tuple.key (gKeyIdx P) (rowEnc C par y) = Tuple.key (gKeyIdx P) (rowEnc C par v)
      ∧ (expandCond w.cond).holds (Tuple.key (winOIdx O) (rowEnc C par y))
          (Tuple.key (winOIdx O) (rowEnc C par v)) = true ↔ _
    rw [key_rowEnc_encK, key_rowEnc_encK, (encK_injective C par).eq_iff, key_winOIdx, key_winOIdx,
      holds_expandCond _ _ (fun ℓ => codeOK_vcode (hR y hy (O ℓ)))
        (fun ℓ => codeOK_vcode (hR v hv (O ℓ)))]
    simp only [dec_vcode]
    rfl
  unfold ValueFrame.frameOf
  simp only [id]
  rw [show (expandFrame (k := k) w).s (Tuple.key (winOIdx O) (rowEnc C par v)) = w.self from rfl,
    show w.s (Tuple.key O v) = w.self from rfl]
  simp only [id] at hfil
  rw [hfil, Multiset.map_erase_inj' _ _ hinj]
  split
  · rw [Multiset.map_cons]
  · rfl

/-- **The window's value at an encoded row is its value at the row.** -/
theorem windowValue_slice (par : Fin k → T) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T (k + c) n) (ht : t.noFun = true)
    {f : SeqAggFunc T} (hf : f.ReadsCount) (keep : Option (Selection T n))
    (hkeep : ∀ φ, keep = some φ → φ.noFun = true ∧ ∀ a ∈ φ.consts, CG C a)
    {Q : Multiset (Tuple T ((k + n) * (7 + k)))} {R : Multiset (Tuple T n)}
    (hsl : Q.filter (fun r => descP (P := 0) r = descEnc C par) = R.map (rowEnc C par))
    (hR : ∀ v ∈ R, ∀ i, GoodVal (C := C) par (v i)) {v : Tuple T n} (hv : v ∈ R)
    (o' : OrderSpec (p * (3 + k))) (γ : Fin c → T) :
    ValueFrame.windowValueOpt (gKeyIdx P) (winOIdx O) o' (expandFrame (k := k) w) (termV t) f
        (keep.map (fun φ => (transSel 0 φ).toSel)) Q (rowEnc C par v) γ
      = ValueFrame.windowValueOpt P O o w t f keep R v (Fin.append par γ) := by
  rw [windowValueOpt_readsCount hf, windowValueOpt_readsCount hf,
    frameOf_slice par P O w hsl hR hv]
  refine congrArg hf.choose ?_
  rw [Multiset.filter_map, Multiset.map_map, Multiset.countP_map, Multiset.countP_map,
    Multiset.filter_filter, Multiset.filter_filter]
  congr 1
  apply Multiset.filter_congr
  intro y hy
  have hyR : y ∈ R := by
    unfold ValueFrame.frameOf at hy
    split at hy
    · rcases Multiset.mem_cons.mp hy with rfl | hy
      · exact hv
      · exact Multiset.mem_of_mem_filter (Multiset.mem_of_mem_erase_any _ hy)
    · exact Multiset.mem_of_mem_filter (Multiset.mem_of_mem_erase_any _ hy)
  simp only [Function.comp]
  rw [keepsOpt_transSel par keep hkeep y (hR y hyR), isNull_termV C t ht par y γ]

/-- **The cells of a window's row**: the input row's cells, then the
window's value as a concrete cell. -/
def wOutSA (n : ℕ) : Fin ((k + (n + 1)) * (7 + k) + 0) → SA T c ((k + n) * (7 + k) + 1) :=
  fun x => Fin.addCases (motive := fun _ => SA T c _)
    (fun i₀ => .col (Fin.castAdd 1 (ci (Fin.castAdd n i₀) (finProdFinEquiv.symm x).2)))
    (fun t => Fin.lastCases (motive := fun _ => SA T c _)
      (concCols (.col (Fin.natAdd _ 0)) (finProdFinEquiv.symm x).2)
      (fun t' => .col (Fin.castAdd 1 (ci (Fin.natAdd k t') (finProdFinEquiv.symm x).2))) t)
    (finProdFinEquiv.symm x).1

theorem wOutSA_eval (C : Finset T) (par : Fin k → T) (v : Tuple T n) (a : T) (γ : Fin c → T)
    (ha : CG C a) :
    (fun x => (wOutSA (k := k) n x).eval (Fin.snoc (rowEnc C par v) a) γ)
      = rowEncP C par (Fin.snoc v a : Tuple T (n + 1)) (Fin.elim0 : Tuple T 0) := by
  refine rowEncP_ext C par _ _ _ (fun i j => ?_) (fun z => z.elim0)
  show (wOutSA n (Fin.castAdd 0 (finProdFinEquiv (i, j)))).eval _ γ = _
  unfold wOutSA
  rw [show Fin.castAdd 0 (finProdFinEquiv (i, j)) = finProdFinEquiv (i, j) from rfl,
    Equiv.symm_apply_apply]
  refine Fin.addCases (fun i₀ => ?_) (fun t => ?_) i
  · rw [Fin.addCases_left, Fin.append_left]
    show (Fin.snoc (rowEnc C par v) a : Tuple T _) (Fin.castSucc _) = _
    rw [Fin.snoc_castSucc]
    show cellOf (rowEnc C par v) (Fin.castAdd n i₀) j = _
    rw [rowEnc, cellOf_ofCells, Fin.append_left]
  · rw [Fin.addCases_right, Fin.append_right]
    refine Fin.lastCases ?_ (fun t' => ?_) t
    · rw [Fin.lastCases_last, concCols_eval]
      show enc C k (.conc ((Fin.snoc (rowEnc C par v) a : Tuple T _) (Fin.last _))) j = _
      rw [Fin.snoc_last, Fin.snoc_last, vcode_of_mem par ha]
    · rw [Fin.lastCases_castSucc]
      show (Fin.snoc (rowEnc C par v) a : Tuple T _) (Fin.castSucc _) = _
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      show cellOf (rowEnc C par v) (Fin.natAdd k t') j = _
      rw [rowEnc, cellOf_ofCells, Fin.append_right]

theorem descP_wOutSA (r : Tuple T ((k + n) * (7 + k))) (a : T) (γ : Fin c → T) :
    descP (P := 0) (fun y => (wOutSA (k := k) n y).eval (Fin.snoc r a) γ) = descP (P := 0) r := by
  funext y
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [descP, ofCells, Equiv.symm_apply_apply]
  show (wOutSA n (Fin.castAdd 0 (finProdFinEquiv (Fin.castAdd (n + 1) i, j)))).eval _ γ
    = r (cc 0 (Fin.castAdd n i) j)
  unfold wOutSA
  rw [show Fin.castAdd 0 (finProdFinEquiv (Fin.castAdd (n + 1) i, j))
      = finProdFinEquiv (Fin.castAdd (n + 1) i, j) from rfl,
    Equiv.symm_apply_apply, Fin.addCases_left]
  show (Fin.snoc r a : Tuple T _) (Fin.castSucc _) = _
  rw [Fin.snoc_castSucc]
  rfl

/-- **The rows a window over an all-regular input emits.** -/
noncomputable def winRows {c' n' : ℕ} (P : Tuple (Fin n') m) (O : Tuple (Fin n') p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c' n') (f : SeqAggFunc T)
    (keep : Option (Selection T n')) (R : Multiset (Tuple T n')) (γ : Fin c' → T) :
    Multiset (Tuple T (n' + 1)) :=
  R.map (fun u => Fin.snoc u (ValueFrame.windowValueOpt P O o w t f keep R u γ))

/-- **The symbolic window's slice**: the encodings of the window's rows,
its values being values of the cut. -/
theorem sliceIs_symWin (par : Fin k → T) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T (k + c) n) (ht : t.noFun = true)
    {f : SeqAggFunc T} (hf : f.ReadsCount) (keep : Option (Selection T n))
    (hkeep : ∀ φ, keep = some φ → φ.noFun = true ∧ ∀ a ∈ φ.consts, CG C a)
    (Q : Multiset (Tuple T ((k + n) * (7 + k)))) (R : Multiset (Tuple T n))
    (hR : ∀ v ∈ R, ∀ i, GoodVal (C := C) par (v i))
    (hQ : SliceIs (P := 0) C par Q (R.map fun v => (v, (Fin.elim0 : Tuple T 0))))
    (γ : Fin c → T)
    (hcnt : ∀ v ∈ R, CG C (ValueFrame.windowValueOpt P O o w t f keep R v (Fin.append par γ))) :
    SliceIs (P := 0) C par ((winRows (gKeyIdx P) (winOIdx O) (expandSpec o) (expandFrame (k := k) w)
        (termV t) f (keep.map (fun φ => (transSel 0 φ).toSel)) Q γ).map
          (fun x y => (wOutSA (k := k) n y).eval x γ))
      ((winRows P O o w t f keep R (Fin.append par γ)).map
        fun v => (v, (Fin.elim0 : Tuple T 0))) := by
  have hsl := slice_eq_map_rowEnc hQ
  unfold SliceIs slice encAll winRows
  rw [Multiset.map_map, Multiset.filter_map]
  simp only [Function.comp, descP_wOutSA]
  erw [hsl]
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun v hv => ?_)
  simp only [Function.comp]
  rw [windowValue_slice par P O o w t ht hf keep hkeep hsl hR hv, wOutSA_eval C par v _ γ
    (hcnt v hv)]

end Window

end Sym
