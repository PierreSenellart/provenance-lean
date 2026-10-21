module

public import Provenance.Genericity
public import Mathlib.Tactic.FinCases

/-!
# The selection row: `σ` is the only operator reading the order

A well-kinded query of the minimal universe (`AggQueryIn.wellKinded`: a
term reads a parameter as a plain value only where it is not aggregate)
that uses no selection and never reads an aggregate column as a key
(`AggQueryIn.noExplode`) is *order-blind*:
its regular columns commute with every injective map of the values that
fixes the query's constants and the zero the aggregate columns are read
as, whatever the map does to the order. Nothing but a selection reads the
order into a regular column, a key or a difference: the windows and the
ordered aggregations read it, but into an aggregate column, which such a
query never reads back.

The commutation is `AggQueryIn.evaluatePlain_orderBlind`, the
faithfulness commutation of `Provenance.Genericity` with the order
dropped from the map and the selection dropped from the syntax, and
stated on the regular reading `ColKind.readTuple` of the rows. The
witness is `σ_{#1<#2}(S)`: on the one-row instance `{(a, b)}` with
`a < b` it keeps the row, on `{(b, a)}` it keeps nothing, and the swap of
`a` and `b` carries one instance to the other (`ltWitness_breaks`). So
no selection-free query expresses it (`ltWitness_not_expressible`), and
`σ` is in every basis whose produced queries read no aggregate column as
a key (`sel_mem_of_generatesOnRecNoExplode`).
-/

@[expose] public section

variable {T : Type} [ValueType T]

/-! ## The regular reading of a row -/

theorem ColKind.readTuple_append {n₁ n₂ : ℕ} (κ₁ : Fin n₁ → ColKind) (κ₂ : Fin n₂ → ColKind)
    (u : Tuple T n₁) (v : Tuple T n₂) :
    ColKind.readTuple (Fin.append κ₁ κ₂) (Fin.append u v : Tuple T (n₁ + n₂))
      = Fin.append (ColKind.readTuple κ₁ u) (ColKind.readTuple κ₂ v) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · show (match (Fin.append κ₁ κ₂ (Fin.castAdd n₂ i)).base with
      | ColKind.agg => 0 | _ => Fin.append u v (Fin.castAdd n₂ i)) = _
    rw [Fin.append_left, Fin.append_left, Fin.append_left]; rfl
  · show (match (Fin.append κ₁ κ₂ (Fin.natAdd n₁ j)).base with
      | ColKind.agg => 0 | _ => Fin.append u v (Fin.natAdd n₁ j)) = _
    rw [Fin.append_right, Fin.append_right, Fin.append_right]; rfl

theorem ColKind.readTuple_snoc_agg {n : ℕ} (κ : Fin n → ColKind) (u : Tuple T n) (x : T) :
    ColKind.readTuple (Fin.snoc κ ColKind.agg) (Fin.snoc u x : Tuple T (n + 1))
      = (Fin.snoc (ColKind.readTuple κ u) 0 : Tuple T (n + 1)) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · show (match ((Fin.snoc κ ColKind.agg : Fin (n + 1) → ColKind) (Fin.last n)).base with
      | ColKind.agg => 0 | _ => (Fin.snoc u x : Tuple T (n + 1)) (Fin.last n)) = _
    rw [Fin.snoc_last, Fin.snoc_last, Fin.snoc_last]; rfl
  · show (match ((Fin.snoc κ ColKind.agg : Fin (n + 1) → ColKind) (Fin.castSucc i)).base with
      | ColKind.agg => 0 | _ => (Fin.snoc u x : Tuple T (n + 1)) (Fin.castSucc i)) = _
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl

/-- Two kind vectors with the same value arms read a row alike. -/
theorem ColKind.readTuple_congr_base {n : ℕ} {κ κ' : Fin n → ColKind}
    (h : ∀ k, (κ k).base = (κ' k).base) (u : Tuple T n) :
    ColKind.readTuple κ' u = ColKind.readTuple κ u := by
  funext k
  show (match (κ' k).base with | ColKind.agg => 0 | _ => u k)
    = (match (κ k).base with | ColKind.agg => 0 | _ => u k)
  rw [h k]

/-- A kind vector with no aggregate column reads a row as itself. -/
theorem ColKind.readTuple_of_ne_agg {n : ℕ} {κ : Fin n → ColKind}
    (h : ∀ k, κ k ≠ ColKind.agg) (u : Tuple T n) : ColKind.readTuple κ u = u := by
  funext k
  show (match (κ k).base with | ColKind.agg => 0 | _ => u k) = u k
  rw [ColKind.base_eq_reg_of_ne_agg (h k)]

/-- A function-free term reads regular and provenance columns only, so it
reads the regular reading of a row as the row. -/
theorem TermGIn.evalPlain_readTuple {c k : ℕ} {κ : Fin k → ColKind} (t : TermGIn T c κ)
    (ht : t.noFun = true) (u : Tuple T k) (γ : Fin c → T) :
    t.evalPlain (ColKind.readTuple κ u) γ = t.evalPlain u γ := by
  cases t with
  | const a => rfl
  | outer j => rfl
  | index j hj =>
    show (match (κ j).base with | ColKind.agg => 0 | _ => u j) = u j
    rw [hj]; rfl
  | provIndex j hj =>
    show (match (κ j).base with | ColKind.agg => 0 | _ => u j) = u j
    rw [hj]; rfl
  | cmpAgg _ _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | chiGate _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | add _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | sub _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | mul _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | caseWhen _ _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | coalesce _ _ => exact absurd ht (by simp [TermGIn.noFun])

/-- A function-free projection column of regular or provenance kind reads
the regular reading of a row as the row. -/
theorem ProjColIn.evalPlain_readTuple {c k : ℕ} {κ : Fin k → ColKind} (p : ProjColIn T c κ)
    (hp : p.noFun = true) (hk : p.kind.base ≠ ColKind.agg) (u : Tuple T k) (γ : Fin c → T) :
    p.evalPlain (ColKind.readTuple κ u) γ = p.evalPlain u γ := by
  cases p with
  | term t => exact TermGIn.evalPlain_readTuple t hp u γ
  | token _ _ => exact absurd rfl hk
  | aggTerm _ _ _ => exact absurd rfl hk
  | aggTermOf _ _ _ => exact absurd rfl hk
  | provTerm t => exact TermGIn.evalPlain_readTuple t hp u γ

/-- The regular reading of a projected row is a function of the regular
reading of the row: an aggregate output column reads as `0`, a regular
one as its term over the regular reading. -/
theorem ColKind.readTuple_proj {c k m : ℕ} {κ : Fin k → ColKind} (ps : Tuple (ProjColIn T c κ) m)
    (hps : ∀ j, (ps j).noFun = true) (u : Tuple T k) (γ : Fin c → T) :
    ColKind.readTuple (fun j => (ps j).kind) (fun j => (ps j).evalPlain u γ)
      = fun j => match ((ps j).kind).base with
        | ColKind.agg => 0
        | _ => (ps j).evalPlain (ColKind.readTuple κ u) γ := by
  funext j
  show (match ((ps j).kind).base with | ColKind.agg => 0 | _ => (ps j).evalPlain u γ) = _
  cases hk : ((ps j).kind).base with
  | agg => rfl
  | reg => exact (ProjColIn.evalPlain_readTuple (ps j) (hps j) (by rw [hk]; decide) u γ).symm
  | prov => exact (ProjColIn.evalPlain_readTuple (ps j) (hps j) (by rw [hk]; decide) u γ).symm

/-! ## The commutation -/

omit [ValueType T] in
/-- An injective map of values is injective on rows. -/
theorem Tuple.comp_injective {τ : T → T} (hτ : Function.Injective τ) (k : ℕ) :
    Function.Injective (fun u : Tuple T k => (τ ∘ u : Tuple T k)) :=
  fun _ _ h => funext (fun i => hτ (congrFun h i))

/-- A bind over rows read through their regular readings, carried along
the commutation of those readings. -/
theorem bind_reg {α : Type} {n : ℕ} {κ : Fin n → ColKind} {τ : T → T}
    {X X' : Multiset (Tuple T n)}
    (hX : X'.map (ColKind.readTuple κ)
      = (X.map (ColKind.readTuple κ)).map (fun u => (τ ∘ u : Tuple T n)))
    (F : Tuple T n → Multiset α) :
    X'.bind (fun u => F (ColKind.readTuple κ u))
      = X.bind (fun u => F (τ ∘ ColKind.readTuple κ u)) := by
  rw [← Multiset.bind_map, hX, Multiset.bind_map, Multiset.bind_map]

theorem ColKind.readTuple_apply_agg {n : ℕ} {κ : Fin n → ColKind} (u : Tuple T n) {k : Fin n}
    (h : (κ k).base = ColKind.agg) : ColKind.readTuple κ u k = 0 := by
  show (match (κ k).base with | ColKind.agg => 0 | _ => u k) = 0
  rw [h]

theorem ColKind.readTuple_apply_ne {n : ℕ} {κ : Fin n → ColKind} (u : Tuple T n) {k : Fin n}
    (h : (κ k).base ≠ ColKind.agg) : ColKind.readTuple κ u k = u k := by
  show (match (κ k).base with | ColKind.agg => 0 | _ => u k) = u k
  cases hb : (κ k).base with
  | agg => exact absurd hb h
  | reg => rfl
  | prov => rfl

omit [ValueType T] in
theorem HoleKinds.assign_self (HK : HoleKinds) (s : String) {n : ℕ} (κ : Fin n → ColKind) :
    HK.assign s κ s n = κ := by
  funext k
  simp [HoleKinds.assign]

omit [ValueType T] in
/-- Two multisets whose readings agree up to a map are related row by row. -/
theorem rel_of_map_eq {α β γ' : Type} {X' : Multiset α} {X : Multiset β} {f : α → γ'}
    {g : β → γ'} (h : X'.map f = X.map g) : Multiset.Rel (fun a b => f a = g b) X' X :=
  Multiset.rel_map.mp (Multiset.rel_eq.mpr h)

omit [ValueType T] in
theorem map_eq_of_rel' {α β γ' : Type} {X' : Multiset α} {X : Multiset β} {f : α → γ'}
    {g : β → γ'} (h : Multiset.Rel (fun a b => f a = g b) X' X) : X'.map f = X.map g :=
  Multiset.rel_eq.mp (Multiset.rel_map.mpr h)

omit [ValueType T] in
/-- A bind over two related multisets, each related pair giving images
that agree up to a map. -/
theorem bind_eq_of_rel {α β γ' δ : Type} {R : α → β → Prop} {X' : Multiset α}
    {X : Multiset β} (h : Multiset.Rel R X' X) {G' : α → Multiset δ} {G : β → Multiset γ'}
    {φ : γ' → δ} (hG : ∀ a b, R a b → G' a = (G b).map φ) :
    X'.bind G' = (X.bind G).map φ := by
  induction h with
  | zero => simp
  | cons hab _ ih => rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.map_add, hG _ _ hab, ih]

omit [ValueType T] in
/-- A leaf of a child that is not one of the child's holes is no hole of
its siblings either, when the child does not mention their names. -/
theorem AggQueryIn.leaf_not_hole {c n : ℕ} {κ : Fin n → ColKind} {l L : List (String × ℕ)}
    {q : AggQueryIn T c n κ l} (hN : ∀ p ∈ L, q.noMention p.1) {p : ℕ × String}
    (hp : p ∈ q.leaves) (hl : (p.2, p.1) ∉ l) : (p.2, p.1) ∉ L :=
  fun hL => hl (AggQueryIn.mem_index_of_mem_leaves q (hN _ hL) p hp rfl)

/-- **Order-blindness**: a well-kinded query with no selection, reading
no aggregate column as a key, in a signature with no function on values,
commutes on its regular columns with every injective map of the values
that fixes `0` and its constants – whatever the map does to the order.
The aggregate columns are read as `0` on both sides (`ColKind.readTuple`),
being the only place the order enters. The instance hypotheses are those
of `AggQueryIn.evaluatePlain_faithful`: the leaves of `D'` are those of
`D` mapped, except at the holes, whose rounds may carry aggregate
columns and are asked to agree on their regular reading only; and the
two contexts agree, up to the map, at the parameters that are not
aggregate, which are the only ones a term reads as a plain value
(`AggQueryIn.wellKinded`). An aggregate parameter is read by the leaf
`AggQueryIn.Param` alone, into an aggregate column. -/
theorem AggQueryIn.evaluatePlain_orderBlind {Θ : Set (SeqAggFunc T)} {S : Set OpKind}
    (hsel : OpKind.sel ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.inSig Θ → q.noExplode → q.hygienic →
      ∀ {ρc : Fin c → ColKind} {HK : HoleKinds}, q.wellKinded ρc HK →
      ∀ {τ : T → T}, Function.Injective τ → τ 0 = 0 →
      ∀ (D D' : Database T) (γ γ' : Fin c → T),
        (∀ p ∈ q.leaves, (p.2, p.1) ∉ l →
          D'.find p.1 p.2 = (D.find p.1 p.2).map (Relation.mapVals τ)) →
        (∀ p ∈ l, q.noMention p.1) →
        (∀ p ∈ l, (D'.find p.2 p.1).map (fun r =>
            (r : Multiset (Tuple T p.2)).map (ColKind.readTuple (HK p.1 p.2)))
          = (D.find p.2 p.1).map (fun r =>
            ((r : Multiset (Tuple T p.2)).map (ColKind.readTuple (HK p.1 p.2))).map
              (fun u => (τ ∘ u : Tuple T p.2)))) →
        (∀ k, (ρc k).base ≠ ColKind.agg → γ' k = τ (γ k)) →
        (∀ a ∈ q.allConsts, τ a = a) →
        ((q.evaluatePlain D' γ' : Multiset (Tuple T n)).map (ColKind.readTuple κ))
          = ((q.evaluatePlain D γ : Multiset (Tuple T n)).map (ColKind.readTuple κ)).map
              (fun u => (τ ∘ u : Tuple T n)) := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ _ _ _ ρc HK _ τ hτ h0 D D' γ γ' hD' _ _ _ hc
    have hf := hD' (n, s) (List.mem_singleton_self _) (fun h => absurd h List.not_mem_nil)
    simp only [ColKind.map_readTuple_allReg]
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain]
    cases hf0 : D.find n s with
    | none =>
      rw [hf0, Option.map_none] at hf
      rw [hf]
      exact (Multiset.map_zero _).symm
    | some rn =>
      rw [hf0, Option.map_some] at hf
      rw [hf]
      rfl
  | Hole n s κh =>
    intro _ _ _ _ ρc HK hwk τ hτ h0 D D' γ γ' _ _ hH _ _
    have hf := hH (s, n) (List.mem_singleton_self _)
    have hk : ∀ M : Multiset (Tuple T n),
        M.map (ColKind.readTuple κh) = M.map (ColKind.readTuple (HK s n)) :=
      fun M => Multiset.map_congr rfl (fun u _ =>
        (ColKind.readTuple_congr_base (fun k => hwk k) u).symm)
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain]
    cases h1 : D.find n s with
    | none =>
      rw [h1, Option.map_none] at hf
      cases h2 : D'.find n s with
      | none => simp
      | some r' => rw [h2] at hf; exact absurd hf (by simp)
    | some r =>
      rw [h1, Option.map_some] at hf
      cases h2 : D'.find n s with
      | none => rw [h2] at hf; exact absurd hf (by simp)
      | some r' =>
        rw [h2, Option.map_some, Option.some.injEq] at hf
        show (r' : Multiset (Tuple T n)).map (ColKind.readTuple κh)
          = ((r : Multiset (Tuple T n)).map (ColKind.readTuple κh)).map _
        rw [hk, hk]
        exact hf
  | Param pv ρ =>
    intro _ _ _ _ ρc HK hwk τ hτ h0 D D' γ γ' _ _ _ hγ hc
    simp only [AggQueryIn.evaluatePlain]
    rw [Multiset.map_singleton, Multiset.map_singleton, Multiset.map_singleton]
    refine congrArg (fun u => ({u} : Multiset (Tuple T _))) (funext fun k => ?_)
    show ColKind.readTuple ρ (fun k => _root_.Sum.elim id γ' (pv k)) k
      = τ (ColKind.readTuple ρ (fun k => _root_.Sum.elim id γ (pv k)) k)
    by_cases hb : (ρ k).base = ColKind.agg
    · rw [ColKind.readTuple_apply_agg _ hb, ColKind.readTuple_apply_agg _ hb, h0]
    · rw [ColKind.readTuple_apply_ne _ hb, ColKind.readTuple_apply_ne _ hb]
      have hk := hwk k
      cases hpk : pv k with
      | inl a =>
        exact (hc a (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
          by rw [hpk]; exact Finset.mem_singleton_self a⟩)).symm
      | inr j =>
        rw [hpk] at hk
        exact hγ j (fun hj => hb (hk.trans hj))
  | Empty =>
    intro _ _ _ _ _ _ _ τ hτ h0 D D' γ γ' _ _ _ _ _
    simp only [AggQueryIn.evaluatePlain]
    rfl
  | Proj ps q ih =>
    rename_i c' k m κ' l'
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have ih' := ih hq.2 hs.2 ha hh hwk.2 hτ h0 D D' γ γ' hD' hN hH hγ
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    have hcol : ∀ j, ∀ a ∈ (ps j).consts, τ a = a := fun j a ha =>
      hc a (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩))
    -- the regular reading of a projected row, through the regular reading of the row
    obtain ⟨G, hG⟩ : ∃ G : (Fin c' → T) → Tuple T k → Tuple T m,
        G = fun γ₀ w => fun j => match ((ps j).kind).base with
          | ColKind.agg => 0
          | _ => (ps j).evalPlain w γ₀ := ⟨_, rfl⟩
    have hread : ∀ (γ₀ : Fin c' → T) (u : Tuple T k),
        ColKind.readTuple (fun j => (ps j).kind) (fun j => (ps j).evalPlain u γ₀)
          = G γ₀ (ColKind.readTuple κ' u) := by
      intro γ₀ u
      rw [hG]
      exact ColKind.readTuple_proj ps hs.1 u γ₀
    have hGτ : ∀ w : Tuple T k, G γ' (τ ∘ w) = fun j => τ (G γ w j) := by
      intro w
      rw [hG]
      funext j
      show (match ((ps j).kind).base with
          | ColKind.agg => 0 | _ => (ps j).evalPlain (τ ∘ w) γ')
        = τ (match ((ps j).kind).base with | ColKind.agg => 0 | _ => (ps j).evalPlain w γ)
      have hctx : (ps j).evalPlain (τ ∘ w) γ' = (ps j).evalPlain (τ ∘ w) (τ ∘ γ) :=
        ProjColIn.evalPlain_congr_outerOk (fun k hk => hγ k hk) (τ ∘ w) (ps j) (hwk.1 j)
      cases ((ps j).kind).base
      · exact hctx.trans (FaithfulOn.projColIn_evalPlain (ps j) (hs.1 j) (hcol j) w γ)
      · exact h0.symm
      · exact hctx.trans (FaithfulOn.projColIn_evalPlain (ps j) (hs.1 j) (hcol j) w γ)
    simp only [AggQueryIn.evaluatePlain]
    calc ((q.evaluatePlain D' γ' : Multiset (Tuple T k)).map
            (fun u => fun j => (ps j).evalPlain u γ')).map
          (ColKind.readTuple (fun j => (ps j).kind))
        = ((q.evaluatePlain D' γ' : Multiset (Tuple T k)).map (ColKind.readTuple κ')).map
            (G γ') := by
          rw [Multiset.map_map, Multiset.map_map]
          exact Multiset.map_congr rfl (fun u _ => hread γ' u)
      _ = (((q.evaluatePlain D γ : Multiset (Tuple T k)).map (ColKind.readTuple κ')).map
            (fun u => (τ ∘ u : Tuple T k))).map (G γ') := by rw [ih']
      _ = ((q.evaluatePlain D γ : Multiset (Tuple T k)).map (ColKind.readTuple κ')).map
            (fun w => (fun j => τ (G γ w j) : Tuple T m)) := by
          rw [Multiset.map_map]
          exact Multiset.map_congr rfl (fun w _ => hGτ w)
      _ = (((q.evaluatePlain D γ : Multiset (Tuple T k)).map
            (fun u => fun j => (ps j).evalPlain u γ)).map
              (ColKind.readTuple (fun j => (ps j).kind))).map (fun u => (τ ∘ u : Tuple T m)) := by
          rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
          refine Multiset.map_congr rfl (fun u _ => ?_)
          show (fun j => τ (G γ (ColKind.readTuple κ' u) j) : Tuple T m)
            = fun j => τ (ColKind.readTuple (fun j => (ps j).kind)
              (fun j => (ps j).evalPlain u γ) j)
          rw [hread γ u]
  | Sel φ q hφ ih => exact fun hq => absurd hq.1 hsel
  | Prod q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l₁ l₂
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have h₁ := ih₁ hq.2.1 hs.1 ha.1 hh.1 hwk.1 hτ h0 D D' γ γ'
      (fun p hp hl => hD' p (List.mem_append_left _ hp) (fun h => (List.mem_append.mp h).elim hl
        (AggQueryIn.leaf_not_hole (fun p' hp' => (hN p' (List.mem_append_right _ hp')).1) hp hl)))
      (fun p hp => (hN p (List.mem_append_left _ hp)).1)
      (fun p hp => hH p (List.mem_append_left _ hp)) hγ
      (fun a ha => hc a (Finset.mem_union_left _ ha))
    have h₂ := ih₂ hq.2.2 hs.2 ha.2 hh.2 hwk.2 hτ h0 D D' γ γ'
      (fun p hp hl => hD' p (List.mem_append_right _ hp) (fun h => (List.mem_append.mp h).elim
        (AggQueryIn.leaf_not_hole (fun p' hp' => (hN p' (List.mem_append_left _ hp')).2) hp hl) hl))
      (fun p hp => (hN p (List.mem_append_right _ hp)).2)
      (fun p hp => hH p (List.mem_append_right _ hp)) hγ
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain, Relation.hMul_eq_bind,
      Relation.hMul_eq_bind, Multiset.map_bind, Multiset.map_bind, Multiset.map_bind]
    -- each side reads its rows through their regular readings
    have hin : ∀ (X : Multiset (Tuple T n₂)) (u : Tuple T n₁),
        (X.map (fun v => (Fin.append u v : Tuple T (n₁ + n₂)))).map
            (ColKind.readTuple (Fin.append κ₁ κ₂))
          = (X.map (ColKind.readTuple κ₂)).map
              (fun w => (Fin.append (ColKind.readTuple κ₁ u) w : Tuple T (n₁ + n₂))) := by
      intro X u
      rw [Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl (fun v _ => ColKind.readTuple_append κ₁ κ₂ u v)
    obtain ⟨F, hF⟩ : ∃ F : Tuple T n₁ → Multiset (Tuple T (n₁ + n₂)),
        F = fun w => (((q₂.evaluatePlain D γ : Multiset (Tuple T n₂)).map
            (ColKind.readTuple κ₂)).map
          (fun v => (τ ∘ v : Tuple T n₂))).map (fun v => (Fin.append w v : Tuple T (n₁ + n₂))) :=
      ⟨_, rfl⟩
    have hL : ∀ u : Tuple T n₁,
        ((q₂.evaluatePlain D' γ' : Multiset (Tuple T n₂)).map
          (fun v => (Fin.append u v : Tuple T (n₁ + n₂)))).map (ColKind.readTuple
              (Fin.append κ₁ κ₂))
        = F (ColKind.readTuple κ₁ u) := by
      intro u
      rw [hin, h₂, hF]
    simp only [hL]
    rw [bind_reg h₁ F]
    refine Multiset.bind_congr (fun u _ => ?_)
    rw [hF, hin]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    exact (Tuple.comp_append τ (ColKind.readTuple κ₁ u) (ColKind.readTuple κ₂ v)).symm
  | Apply q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l₁
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have h₁ := ih₁ hq.2.1 hs.1 ha.1 hh.1 hwk.1 hτ h0 D D' γ γ'
      (fun p hp hl => hD' p (List.mem_append_left _ hp) hl)
      (fun p hp => (hN p hp).1) hH hγ
      (fun a ha => hc a (Finset.mem_union_left _ ha))
    -- the left rows correspond on their regular reading, and so do the
    -- contexts the right side reads at them
    have hrel := rel_of_map_eq (f := ColKind.readTuple κ₁)
      (g := fun u => (τ ∘ ColKind.readTuple κ₁ u : Tuple T n₁))
      (h₁.trans (Multiset.map_map _ _ _))
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain, Multiset.map_bind, Multiset.map_bind]
    refine bind_eq_of_rel hrel (fun u' u hu => ?_)
    have hctx : ∀ k, (Fin.append κ₁ ρc k).base ≠ ColKind.agg →
        Fin.append u' γ' k = τ (Fin.append u γ k) := by
      intro k
      refine Fin.addCases (fun i hi => ?_) (fun j hj => ?_) k
      · rw [Fin.append_left] at hi
        rw [Fin.append_left, Fin.append_left]
        have := congrFun hu i
        rwa [ColKind.readTuple_apply_ne _ hi, Function.comp_apply,
          ColKind.readTuple_apply_ne _ hi] at this
      · rw [Fin.append_right] at hj
        rw [Fin.append_right, Fin.append_right]
        exact hγ j hj
    have h₂ := ih₂ hq.2.2 hs.2 ha.2 hh.2 hwk.2 hτ h0 D D' (Fin.append u γ) (Fin.append u' γ')
      (fun p hp _ => hD' p (List.mem_append_right _ hp)
        (AggQueryIn.leaf_not_hole (fun p' hp' => (hN p' hp').2) hp List.not_mem_nil))
      (fun p hp => absurd hp List.not_mem_nil) (fun p hp => absurd hp List.not_mem_nil) hctx
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    have hu' : ColKind.readTuple κ₁ u' = (τ ∘ ColKind.readTuple κ₁ u : Tuple T n₁) := hu
    simp only [Multiset.map_map]
    calc _ = ((q₂.evaluatePlain D' (Fin.append u' γ') : Multiset (Tuple T n₂)).map
              (ColKind.readTuple κ₂)).map
              (fun v => (Fin.append (ColKind.readTuple κ₁ u') v : Tuple T (n₁ + n₂))) := by
            rw [Multiset.map_map]
            exact Multiset.map_congr rfl (fun v _ => ColKind.readTuple_append κ₁ κ₂ u' v)
      _ = _ := by
            rw [h₂, Multiset.map_map, Multiset.map_map]
            refine Multiset.map_congr rfl (fun v _ => ?_)
            simp only [Function.comp_apply]
            rw [ColKind.readTuple_append, hu', Tuple.comp_append]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain]
    show Multiset.map _ (_ + _) = Multiset.map _ (Multiset.map _ (_ + _))
    rw [Multiset.map_add, Multiset.map_add, Multiset.map_add,
      ih₁ hq.2.1 hs.1 ha.1 hh.1 hwk.1 hτ h0 D D' γ γ'
        (fun p hp hl => hD' p (List.mem_append_left _ hp) (fun h => (List.mem_append.mp h).elim hl
          (AggQueryIn.leaf_not_hole (fun p' hp' => (hN p' (List.mem_append_right _ hp')).1) hp hl)))
        (fun p hp => (hN p (List.mem_append_left _ hp)).1)
        (fun p hp => hH p (List.mem_append_left _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_left _ ha)),
      ih₂ hq.2.2 hs.2 ha.2 hh.2 hwk.2 hτ h0 D D' γ γ'
        (fun p hp hl => hD' p (List.mem_append_right _ hp) (fun h => (List.mem_append.mp h).elim
          (AggQueryIn.leaf_not_hole (fun p' hp' => (hN p'
              (List.mem_append_left _ hp')).2) hp hl) hl))
        (fun p hp => (hN p (List.mem_append_right _ hp)).2)
        (fun p hp => hH p (List.mem_append_right _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_right _ ha))]
  | Dedup q ih =>
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have h := ih hq.2 hs ha hh hwk hτ h0 D D' γ γ' hD' hN hH hγ hc
    simp only [ColKind.map_readTuple_allReg] at h ⊢
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain, h]
    exact Multiset.dedup_map_of_injOn (fun x _ y _ hxy => Tuple.comp_injective hτ _ hxy)
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have h₁ := ih₁ hq.2.1 hs.1 ha.1 hh.1 hwk.1 hτ h0 D D' γ γ'
      (fun p hp hl => hD' p (List.mem_append_left _ hp) hl)
      (fun p hp => absurd hp List.not_mem_nil) (fun p hp => absurd hp List.not_mem_nil) hγ
      (fun a ha => hc a (Finset.mem_union_left _ ha))
    have h₂ := ih₂ hq.2.2 hs.2 ha.2 hh.2 hwk.2 hτ h0 D D' γ γ'
      (fun p hp hl => hD' p (List.mem_append_right _ hp) hl)
      (fun p hp => absurd hp List.not_mem_nil) (fun p hp => absurd hp List.not_mem_nil) hγ
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    simp only [ColKind.map_readTuple_allReg] at h₁ h₂ ⊢
    simp only [AggQueryIn.evaluatePlain]
    rw [h₁, h₂, Multiset.filter_map]
    congr 1
    refine Multiset.filter_congr (fun u _ => ?_)
    show (τ ∘ u : Tuple T _) ∉ Multiset.map _ _ ↔ u ∉ _
    rw [not_iff_not]
    exact Multiset.mem_map_of_injective (Tuple.comp_injective hτ _)
  | Explode k hk q ih => exact fun _ _ ha => ha.elim
  | Retag hk q ih =>
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have h := ih hq hs ha hh hwk hτ h0 D D' γ γ' hD' hN hH hγ hc
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain]
    rw [Multiset.map_congr rfl (fun u _ => ColKind.readTuple_congr_base hk u),
      Multiset.map_congr rfl (fun u _ => ColKind.readTuple_congr_base hk u)]
    exact h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m κm
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have hc₀ : ∀ a ∈ q₀.allConsts, τ a = a := fun a ha => hc a (Finset.mem_union_left _ ha)
    have hc₁ : ∀ a ∈ q₁.allConsts, τ a = a := fun a ha => hc a (Finset.mem_union_right _ ha)
    -- the rounds correspond row by row on their regular reading
    have hbody : ∀ (X' X : Multiset (Tuple T m)),
        Multiset.Rel (fun a' a => ColKind.readTuple κm a'
          = (τ ∘ ColKind.readTuple κm a : Tuple T m)) X' X →
        Multiset.Rel (fun a' a => ColKind.readTuple κm a'
          = (τ ∘ ColKind.readTuple κm a : Tuple T m))
          (q₁.evaluatePlain (D'.assign s X') γ') (q₁.evaluatePlain (D.assign s X) γ) := by
      intro X' X hX
      refine rel_of_map_eq ((ih₁ hq.2.2 hs.2 ha.2 hh.2.2.2 hwk.2 hτ h0 (D.assign s X)
        (D'.assign s X') γ γ' ?_ ?_ ?_ hγ hc₁).trans (Multiset.map_map _ _ _))
      · rintro ⟨k, t⟩ hp hl
        have hkt : ¬ (k = m ∧ t = s) := fun h => hl (by
          obtain ⟨rfl, rfl⟩ := h; exact List.mem_singleton_self _)
        rw [Database.find_assign_of_ne s t _ D hkt, Database.find_assign_of_ne s t _ D' hkt]
        exact hD' (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp,
          decide_eq_true (fun h => hkt (Prod.mk.inj h))⟩)) (fun h => absurd h List.not_mem_nil)
      · intro p hp
        rw [List.mem_singleton.mp hp]
        exact hh.2.1
      · intro p hp
        rw [List.mem_singleton.mp hp]
        show ((D'.assign s X').find m s).map _ = ((D.assign s X).find m s).map _
        rw [Database.find_assign, Database.find_assign, Option.map_some, Option.map_some,
          HoleKinds.assign_self]
        exact congrArg some ((map_eq_of_rel' hX).trans
          (Multiset.map_map (fun u => (τ ∘ u : Tuple T m)) (ColKind.readTuple κm) X).symm)
    have hM := ih₀ hq.2.1 hs.1 ha.1 hh.2.2.1 hwk.1 hτ h0 D D' γ γ'
      (fun p hp hl => hD' p (List.mem_append_left _ hp) hl)
      (fun p hp => absurd hp List.not_mem_nil) (fun p hp => absurd hp List.not_mem_nil) hγ hc₀
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain]
    refine (map_eq_of_rel' (muSumFix_rel
      (R := fun a' a => ColKind.readTuple κm a' = (τ ∘ ColKind.readTuple κm a : Tuple T m))
      (rel_of_map_eq (g := fun a => (τ ∘ ColKind.readTuple κm a : Tuple T m))
        (hM.trans (Multiset.map_map _ _ _)))
      (fun k X' hX => hbody X' _ hX))).trans
      (Multiset.map_map (fun u => (τ ∘ u : Tuple T m)) (ColKind.readTuple κm) _).symm
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have hc₀ : ∀ a ∈ q₀.allConsts, τ a = a := fun a ha => hc a (Finset.mem_union_left _ ha)
    have hc₁ : ∀ a ∈ q₁.allConsts, τ a = a := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hbody : ∀ X : Relation T m,
        (q₁.evaluatePlain (D'.assign s (Relation.mapVals τ X)) γ' : Multiset (Tuple T m))
          = (q₁.evaluatePlain (D.assign s X) γ : Multiset (Tuple T m)).map
              (fun u => (τ ∘ u : Tuple T m)) := by
      intro X
      have := ih₁ hq.2.2 hs.2 ha.2 hh.2.2.2 hwk.2 hτ h0 (D.assign s X)
        (D'.assign s (Relation.mapVals τ X)) γ γ'
        (by
          rintro ⟨k, t⟩ hp hl
          have hkt : ¬ (k = m ∧ t = s) := fun h => hl (by
            obtain ⟨rfl, rfl⟩ := h; exact List.mem_singleton_self _)
          rw [Database.find_assign_of_ne s t _ D hkt, Database.find_assign_of_ne s t _ D' hkt]
          exact hD' (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp,
            decide_eq_true (fun h => hkt (Prod.mk.inj h))⟩)) (fun h => absurd h List.not_mem_nil))
        (fun p hp => by rw [List.mem_singleton.mp hp]; exact hh.2.1)
        (fun p hp => by
          rw [List.mem_singleton.mp hp]
          show ((D'.assign s _).find m s).map _ = ((D.assign s X).find m s).map _
          rw [Database.find_assign, Database.find_assign, Option.map_some, Option.map_some,
            HoleKinds.assign_self]
          simp only [ColKind.map_readTuple_allReg]
          rfl)
        hγ hc₁
      simpa only [ColKind.map_readTuple_allReg] using this
    have hM := ih₀ hq.2.1 hs.1 ha.1 hh.2.2.1 hwk.1 hτ h0 D D' γ γ'
      (fun p hp hl => hD' p (List.mem_append_left _ hp) hl)
      (fun p hp => absurd hp List.not_mem_nil) (fun p hp => absurd hp List.not_mem_nil) hγ hc₀
    simp only [ColKind.map_readTuple_allReg] at hM ⊢
    obtain ⟨step, hstep⟩ : ∃ step : Multiset (Tuple T m) → Multiset (Tuple T m),
      step = fun X => (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup := ⟨_, rfl⟩
    obtain ⟨step', hstep'⟩ : ∃ step' : Multiset (Tuple T m) → Multiset (Tuple T m),
      step' = fun X => (q₀.evaluatePlain D' γ'
        + q₁.evaluatePlain (D'.assign s X) γ').dedup := ⟨_, rfl⟩
    have hstepapp : ∀ X, step X = (q₀.evaluatePlain D γ + q₁.evaluatePlain
        (D.assign s X) γ).dedup :=
      fun X => by rw [hstep]
    have hstep'app : ∀ X, step' X
        = (q₀.evaluatePlain D' γ' + q₁.evaluatePlain (D'.assign s X) γ').dedup :=
      fun X => by rw [hstep']
    have hiter : ∀ k, muIter step' k = (muIter step k).map (fun u => (τ ∘ u : Tuple T m)) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [muIter, muIter, ih, hstep'app, hstepapp]
        show ((q₀.evaluatePlain D' γ' : Multiset (Tuple T m))
          + q₁.evaluatePlain (D'.assign s (Relation.mapVals τ (muIter step k))) γ').dedup
          = _
        rw [hM, hbody, ← Multiset.map_add]
        exact Multiset.dedup_map_of_injOn (fun x _ y _ hxy => Tuple.comp_injective hτ _ hxy)
    have hidx : muFixIdx step' = muFixIdx step := by
      unfold muFixIdx
      congr 1
      ext j
      show step'^[j + 1] 0 = step'^[j] 0 ↔ step^[j + 1] 0 = step^[j] 0
      rw [← muIter_eq_iterate, ← muIter_eq_iterate, ← muIter_eq_iterate, ← muIter_eq_iterate,
        hiter, hiter]
      exact (Multiset.map_injective (Tuple.comp_injective hτ _)).eq_iff
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain]
    erw [← hstep', ← hstep]
    unfold muFix
    rw [hidx]
    exact hiter _
  | Gamma is ts fs q keep ord ih =>
    rename_i c' m n₁ n₂ _ _
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have hr := ih hq.2 hs.2.2.2 ha hh hwk.2 hτ h0 D D' γ γ' hD' hN hH hγ
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    simp only [ColKind.map_readTuple_allReg] at hr
    simp only [AggQueryIn.evaluatePlain]
    rw [hr, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    -- the keys of the mapped input are the mapped keys
    have hkeys : ((q.evaluatePlain D γ : Multiset (Tuple T m)).map
          ((fun u => (fun k => u (is k) : Tuple T n₁)) ∘ fun u => (τ ∘ u : Tuple T m))).dedup
        = (((q.evaluatePlain D γ : Multiset (Tuple T m)).map
          (fun u => (fun k => u (is k) : Tuple T n₁))).dedup).map (fun g =>
              (τ ∘ g : Tuple T n₁)) := by
      erw [← Multiset.dedup_map_of_injOn (fun x _ y _ hxy => Tuple.comp_injective hτ n₁ hxy)]
      rw [Multiset.map_map]
      rfl
    erw [hkeys]
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun g _ => ?_)
    show ColKind.readTuple (Fin.append (fun _ => ColKind.reg) (fun _ => ColKind.agg))
        (Fin.append (τ ∘ g) _ : Tuple T (n₁ + n₂))
      = τ ∘ ColKind.readTuple (Fin.append (fun _ => ColKind.reg) (fun _ => ColKind.agg))
          (Fin.append g _ : Tuple T (n₁ + n₂))
    have hreg : ∀ k : Fin n₁, (fun _ : Fin n₁ => ColKind.reg) k ≠ ColKind.agg :=
      fun _ h => ColKind.noConfusion h
    rw [ColKind.readTuple_append, ColKind.readTuple_append, Tuple.comp_append,
      ColKind.readTuple_of_ne_agg hreg, ColKind.readTuple_of_ne_agg hreg]
    congr 1
    funext j
    show (0 : T) = τ 0
    exact h0.symm
  | GammaScalar ts fs q ord ih =>
    rename_i c' m n₂ _ _
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    simp only [AggQueryIn.evaluatePlain]
    show Multiset.map _ (Multiset.ofList [_]) = Multiset.map _ (Multiset.map _
        (Multiset.ofList [_]))
    simp only [Multiset.map_coe, List.map_cons, List.map_nil]
    congr 2
    funext j
    show (0 : T) = τ 0
    exact h0.symm
  | GammaNest is his p f q ih =>
    rename_i c' m n₁ κ' _ _
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have hr := ih hq.2 hs.2.2 ha hh hwk.2 hτ h0 D D' γ γ' hD' hN hH hγ
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    simp only [AggQueryIn.evaluatePlain]
    -- a key reads regular columns, so it reads the regular reading of the row
    have hkey : ∀ u : Tuple T m, (fun k => u (is k) : Tuple T n₁)
        = fun k => ColKind.readTuple κ' u (is k) := by
      intro u
      funext k
      show u (is k) = (match (κ' (is k)).base with | ColKind.agg => 0 | _ => u (is k))
      rw [ColKind.base_eq_reg_of_ne_agg (his k)]
    have hkeys : ∀ (X : Multiset (Tuple T m)),
        (X.map (fun u : Tuple T m => (fun k => u (is k) : Tuple T n₁))).dedup
          = ((X.map (ColKind.readTuple κ')).map
              (fun w : Tuple T m => (fun k => w (is k) : Tuple T n₁))).dedup := by
      intro X
      rw [Multiset.map_map]
      exact congrArg Multiset.dedup (Multiset.map_congr rfl (fun u _ => hkey u))
    -- the keys of the mapped input are the mapped keys
    have hk : ((q.evaluatePlain D' γ' : Multiset (Tuple T m)).map
          (fun u : Tuple T m => (fun k => u (is k) : Tuple T n₁))).dedup
        = (((q.evaluatePlain D γ : Multiset (Tuple T m)).map
            (fun u : Tuple T m => (fun k => u (is k) : Tuple T n₁))).dedup).map
            (fun g => (τ ∘ g : Tuple T n₁)) := by
      rw [hkeys, hr, Multiset.map_map, hkeys (q.evaluatePlain D γ)]
      erw [← Multiset.dedup_map_of_injOn (fun x _ y _ hxy => Tuple.comp_injective hτ n₁ hxy)]
      simp only [Multiset.map_map]
      rfl
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    erw [hk]
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun g _ => ?_)
    show ColKind.readTuple (Fin.append (fun k => κ' (is k)) (fun _ : Fin 1 => ColKind.agg))
        (Fin.append (τ ∘ g) _ : Tuple T (n₁ + 1))
      = τ ∘ ColKind.readTuple (Fin.append (fun k => κ' (is k)) (fun _ : Fin 1 => ColKind.agg))
          (Fin.append g _ : Tuple T (n₁ + 1))
    rw [ColKind.readTuple_append, ColKind.readTuple_append, Tuple.comp_append,
      ColKind.readTuple_of_ne_agg (fun k => his k), ColKind.readTuple_of_ne_agg (fun k => his k)]
    congr 1
    funext j
    show (0 : T) = τ 0
    exact h0.symm
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    rename_i c' n' m' p' κ' _ _ _
    intro hq hs ha hh ρc HK hwk τ hτ h0 D D' γ γ' hD' hN hH hγ hc
    have hr := ih hq.2 hs.2.2.2.2 ha hh hwk.2 hτ h0 D D' γ γ' hD' hN hH hγ
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    simp only [AggQueryIn.evaluatePlain]
    have hrow : ∀ (X : Multiset (Tuple T n')) (F : Tuple T n' → T),
        (X.map (fun u => (Fin.snoc u (F u) : Tuple T (n' + 1)))).map
            (ColKind.readTuple (Fin.snoc κ' ColKind.agg))
          = (X.map (ColKind.readTuple κ')).map (fun w => (Fin.snoc w 0 : Tuple T (n' + 1))) := by
      intro X F
      rw [Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl (fun u _ => ColKind.readTuple_snoc_agg κ' u (F u))
    erw [hrow, hrow]
    rw [hr]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun w _ => ?_)
    show (Fin.snoc (τ ∘ ColKind.readTuple κ' w) 0 : Tuple T (n' + 1))
      = τ ∘ (Fin.snoc (ColKind.readTuple κ' w) 0 : Tuple T (n' + 1))
    rw [Fin.comp_snoc, h0]
  | WinExpr P O o ws ts fs g q keeps ih => exact fun _ hs => hs.elim


/-! ## The witness -/

/-- The one-row instance `S = {(a, b)}`. -/
def dPair (a b : ℕ) : Database ℕ := [("S", ⟨2, ({![a, b]} : Multiset (Tuple ℕ 2))⟩)]

theorem find_dPair (a b : ℕ) :
    (dPair a b).find 2 "S" = some ({![a, b]} : Multiset (Tuple ℕ 2)) :=
  Database.find_assign "S" _ []

theorem find_dPair_ne (a b : ℕ) {k : ℕ} {t : String} (h : ¬ (k = 2 ∧ t = "S")) :
    (dPair a b).find k t = none :=
  Database.find_assign_of_ne "S" t _ [] h

/-- `σ_{#1<#2}(S)`, the witness: the one selection whose atom reads the order. -/
def ltWitness : AggQuery ℕ 2 (ColKind.allReg 2) :=
  AggQueryIn.Sel (GenPredIn.cmp CompOp.lt (TermGIn.index 0 rfl) (TermGIn.index 1 rfl))
    (AggQueryIn.Rel 2 "S")

theorem usesOnly_ltWitness : ltWitness.usesOnly plainRecOps :=
  ⟨by simp [plainRecOps, plainOps, basisDD, basisOps], trivial⟩

theorem overSchema_ltWitness : ltWitness.overSchema schemaS := rfl

theorem inSig_ltWitness (Θ : Set (SeqAggFunc ℕ)) : ltWitness.inSig Θ := ⟨rfl, trivial⟩

theorem settlesAt_ltWitness (D : Database ℕ) (γ : Fin 0 → ℕ) : ltWitness.SettlesAt D γ :=
  trivial

/-- On `{(a, b)}` the witness keeps the row iff `a < b`. -/
theorem evaluatePlain_ltWitness (a b : ℕ) :
    (ltWitness.evaluatePlain (dPair a b) : Multiset (Tuple ℕ 2))
      = if LT.lt a b then ({![a, b]} : Multiset (Tuple ℕ 2)) else 0 := by
  simp only [ltWitness, AggQueryIn.evaluatePlain, find_dPair]
  show Multiset.filter _ ({![a, b]} : Multiset (Tuple ℕ 2)) = _
  rw [Multiset.filter_singleton]
  simp only [GenPredIn.holdsPlain, GenPredIn.evalPlain3, TermGIn.evalPlain, CompOp.eval3,
    CompOp.strict, CompOp.eval]
  have hn : ∀ x : ℕ, ValueType.isNull x = false := fun _ => rfl
  simp [hn]

/-- **The witness breaks order-blindness**: the swap of `a < b` carries
`{(a, b)}` to `{(b, a)}`, where it keeps nothing. -/
theorem ltWitness_breaks {a b : ℕ} (hab : LT.lt a b) :
    (ltWitness.evaluatePlain (dPair b a) : Multiset (Tuple ℕ 2))
      ≠ (ltWitness.evaluatePlain (dPair a b) : Multiset (Tuple ℕ 2)).map
          (fun u => (Equiv.swap a b ∘ u : Tuple ℕ 2)) := by
  rw [evaluatePlain_ltWitness, evaluatePlain_ltWitness, ite_eq_left hab,
    ite_eq_right (not_lt.mpr (le_of_lt hab))]
  intro h
  exact absurd (congrArg Multiset.card h) (by simp)

/-- Two values outside a finite set of naturals, in order, neither zero. -/
theorem exists_two_fresh (A : Finset ℕ) :
    ∃ a b : ℕ, LT.lt a b ∧ a ∉ A ∧ b ∉ A ∧ a ≠ 0 ∧ b ≠ 0 := by
  obtain ⟨a, ha, ha0⟩ : ∃ a, a ∉ A ∧ a ≠ 0 := by
    obtain ⟨a, ha⟩ := (insert 0 A).exists_notMem
    exact ⟨a, fun h => ha (Finset.mem_insert_of_mem h), fun h => ha
        (h ▸ Finset.mem_insert_self _ _)⟩
  obtain ⟨b, hb⟩ := (insert 0 (A ∪ Finset.range (a + 1))).exists_notMem
  refine ⟨a, b, ?_, ha, fun h => hb (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)), ha0,
    fun h => hb (h ▸ Finset.mem_insert_self _ _)⟩
  by_contra hlt
  exact hb (Finset.mem_insert_of_mem (Finset.mem_union_right _
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (not_lt.mp hlt)))))

/-- **No selection-free query expresses the witness.** A query over `ℕ`
with no selection, reading no aggregate column as a key or as an apply's
parameter, in a signature
with no function on values, is not plain-equivalent to `σ_{#1<#2}(S)`:
on two fresh values `a < b` it answers alike, up to the swap, on
`{(a, b)}` and on `{(b, a)}`, and the witness does not. -/
theorem ltWitness_not_expressible {Θ : Set (SeqAggFunc ℕ)} {S : Set OpKind}
    (hsel : OpKind.sel ∉ S) {κ : Fin 2 → ColKind} (q : AggQuery ℕ 2 κ)
    (hq : q.usesOnly S) (hs : q.inSig Θ) (ha : q.noExplode) (hh : q.hygienic)
    (hwk : q.wellKinded (ColKind.allReg 0) HoleKinds.empty) :
    ¬ ∀ D : Database ℕ, q.evaluatePlain D = ltWitness.evaluatePlain D := by
  intro heq
  obtain ⟨a, b, hab, haA, hbA, ha0, hb0⟩ := exists_two_fresh q.allConsts
  have hτ0 : Equiv.swap a b 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm ha0) (Ne.symm hb0)
  have hτc : ∀ x ∈ q.allConsts, Equiv.swap a b x = x := fun x hx =>
    Equiv.swap_apply_of_ne_of_ne (fun h => haA (h ▸ hx)) (fun h => hbA (h ▸ hx))
  have hD' : ∀ p ∈ q.leaves, (dPair b a).find p.1 p.2
      = ((dPair a b).find p.1 p.2).map (Relation.mapVals (Equiv.swap a b)) := by
    rintro ⟨k, t⟩ _
    by_cases hkt : k = 2 ∧ t = "S"
    · obtain ⟨rfl, rfl⟩ := hkt
      rw [find_dPair, find_dPair, Option.map_some]
      congr 1
      show ({![b, a]} : Multiset (Tuple ℕ 2)) = ({![a, b]} : Multiset (Tuple ℕ 2)).map _
      rw [Multiset.map_singleton]
      congr 1
      funext i
      fin_cases i
      · exact (Equiv.swap_apply_left a b).symm
      · exact (Equiv.swap_apply_right a b).symm
    · rw [find_dPair_ne a b hkt, find_dPair_ne b a hkt]
      rfl
  have h := AggQueryIn.evaluatePlain_orderBlind hsel q hq hs ha hh hwk
    (Equiv.swap a b).injective hτ0 (dPair a b) (dPair b a) (fun _ => 0) (fun _ => 0)
    (fun p hp _ => hD' p hp) (fun p hp => absurd hp List.not_mem_nil)
    (fun p hp => absurd hp List.not_mem_nil) (fun k => k.elim0) hτc
  rw [heq, heq, evaluatePlain_ltWitness, evaluatePlain_ltWitness, ite_eq_left hab,
    ite_eq_right (not_lt.mpr (le_of_lt hab))] at h
  have := congrArg Multiset.card h
  simp at this

/-! ## The row -/

/-- **Generation with no aggregate column read as a key**: the
whole-algebra generation predicate (`GeneratesOnRec`) with the produced
query also asked to be `noExplode` and well-kinded. This is the scope of
the annotated generation, where the alternatives are not an operator of
the source language; over it the selection is in every basis, which the
plain construction putting `−` in place of `σ` (`basisRecDiffOps_isBasis`)
escapes only by reading aggregate columns as keys. An apply's right side
reading an aggregate column of its left side as a plain value would escape
it the same way – a window's rank read as a parameter compares two values
against a constant with a difference – and well-kindedness is what refuses
that reading: an aggregate parameter is read by the leaf
`AggQueryIn.Param`, into an aggregate column. -/
def GeneratesAtNoExplode (T : Type) [ValueType T] (sch : Schema) (cnt : SeqAggFunc T)
    (S : Set OpKind) {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ) : Prop :=
  q.overSchema sch → q.usesOnly plainRecOps → q.inMinimalSig cnt →
    ∃ (κ' : Fin n → ColKind) (q' : AggQuery T n κ'),
      q'.overSchema sch ∧ q'.usesOnly S ∧ q'.inMinimalSig cnt ∧ q'.noExplode
        ∧ q'.wellKinded (ColKind.allReg 0) HoleKinds.empty ∧ q'.Extends q

/-- The alternatives-free generation of every query of the algebra. -/
def GeneratesOnRecNoExplode (T : Type) [ValueType T] (sch : Schema)
    (cnt : SeqAggFunc T) (S : Set OpKind) : Prop :=
  ∀ {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ), GeneratesAtNoExplode T sch cnt S q

theorem GeneratesOnRecNoExplode.toGeneratesOnRec {sch : Schema} {cnt : SeqAggFunc T}
    {S : Set OpKind} (h : GeneratesOnRecNoExplode T sch cnt S) : GeneratesOnRec T sch cnt S := by
  intro n κ q ho hq hi
  obtain ⟨κ', q', h₁, h₂, h₃, -, -, h₅⟩ := h q ho hq hi
  exact ⟨κ', q', h₁, h₂, h₃, h₅⟩

/-- **The selection row, in the scope where no aggregate column is read as
a key**: `σ` is in every generating set. -/
theorem sel_mem_of_generatesAtNoExplode {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (hS : GeneratesAtNoExplode ℕ schemaS cnt S ltWitness) : OpKind.sel ∈ S := by
  by_contra hsel
  obtain ⟨κ', q', ho', hu', hsig', ha', hwk', he⟩ := hS overSchema_ltWitness usesOnly_ltWitness
    (inSig_ltWitness _)
  refine ltWitness_not_expressible hsel q' hu' hsig' ha'
    (AggQueryIn.hygienic_of_overSchema q' _ ho') hwk' (fun D => ?_)
  exact (he.settles D (fun _ => 0) (settlesAt_ltWitness D _)).2.symm

/-- **The selection row, in the scope where no aggregate column is read as
a key**: `σ` is in every generating set. -/
theorem sel_mem_of_generatesOnRecNoExplode {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (hS : GeneratesOnRecNoExplode ℕ schemaS cnt S) : OpKind.sel ∈ S :=
  sel_mem_of_generatesAtNoExplode (hS _)
