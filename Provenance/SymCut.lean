import Provenance.SymEnvBuild

/-!
# The cut a query's symbolic evaluation is taken relative to

The symbolic evaluation of a query is correct relative to a cut holding
every value the evaluation compares, groups or makes up (`Sym.Good`): the
values of the relations it reads, its constants, the null, the context's
values, and the values its aggregations compute. The last are computed
**by symbolic evaluations themselves**: a grouping's counts, at every
parameter row, are read off the symbolic evaluation of its input relative
to the cut of that input, which is smaller. So the cut is defined by
recursion on the query (`Sym.cutQ`), each aggregation adding the values
its symbolic counterpart computes, and it is proved to make the
evaluation good (`Sym.good_cutQ`).
-/

variable {T : Type} [ValueType T]

namespace Sym

section Unions

variable {c : ℕ}

/-- **The union of finitely many unary relations.** -/
def unionFin (f : ℕ → String) : (n : ℕ) → (Fin n → AggQueryIn T c 1 (ColKind.allReg 1)) →
    AggQueryIn T c 1 (ColKind.allReg 1)
  | 0, _ => AggQueryIn.emptyRel 1
  | n + 1, F => AggQueryIn.sumByMuX (f 0) (f 1) (F 0) (unionFin (fun i => f (i + 2)) n
      (fun i => F i.succ))

theorem noMention_unionFin (f : ℕ → String) {s : String} :
    ∀ (n : ℕ) (F : Fin n → AggQueryIn T c 1 (ColKind.allReg 1)), (∀ i, (F i).noMention s) →
      (unionFin f n F).noMention s
  | 0, _, _ => AggQueryIn.noMention_emptyRel 1 s
  | n + 1, _, h => AggQueryIn.noMention_sumByMuX _ _ _ _ (h 0)
      (noMention_unionFin _ n _ (fun i => h i.succ))

theorem mem_unionFin (f : ℕ → String) (D : Database T) (γ : Fin c → T) :
    ∀ (n : ℕ) (F : Fin n → AggQueryIn T c 1 (ColKind.allReg 1)),
      (∀ i j, (F i).noMention (f j)) → ∀ x,
      Multiset.Mem ((unionFin f n F).evaluatePlain D γ) x ↔ ∃ i, Multiset.Mem ((F i).evaluatePlain
        D γ) x
  | 0, _, _, x => by
    rw [unionFin, AggQueryIn.evaluatePlain_emptyRel]
    exact ⟨fun h => absurd h (Multiset.notMem_zero x), fun ⟨i, _⟩ => i.elim0⟩
  | n + 1, F, hF, x => by
    rw [unionFin, AggQueryIn.evaluatePlain_sumByMuX _ _ _ _ (hF 0 0)
      (noMention_unionFin _ n _ (fun i => hF i.succ 1))]
    show x ∈ (_ + _ : Multiset _) ↔ _
    rw [Multiset.mem_add]
    refine Iff.trans (or_congr Iff.rfl (mem_unionFin _ D γ n _ (fun i j => hF i.succ (j + 2)) x)) ?_
    constructor
    · rintro (h | ⟨i, h⟩)
      · exact ⟨0, h⟩
      · exact ⟨i.succ, h⟩
    · rintro ⟨i, h⟩
      refine Fin.cases (fun h => Or.inl h) (fun i h => Or.inr ⟨i, h⟩) i h

/-- The union of two unary relations. -/
def u2 (f : ℕ → String) (a b : AggQueryIn T c 1 (ColKind.allReg 1)) :
    AggQueryIn T c 1 (ColKind.allReg 1) :=
  AggQueryIn.sumByMuX (f 0) (f 1) a b

theorem noMention_u2 (f : ℕ → String) {a b : AggQueryIn T c 1 (ColKind.allReg 1)} {s : String}
    (ha : a.noMention s) (hb : b.noMention s) : (u2 f a b).noMention s :=
  AggQueryIn.noMention_sumByMuX _ _ _ _ ha hb

theorem valsU_u2 (f : ℕ → String) (a b : AggQueryIn T c 1 (ColKind.allReg 1))
    (ha : a.noMention (f 0)) (hb : b.noMention (f 1)) (D : Database T) (γ : Fin c → T) :
    valsU ((u2 f a b).evaluatePlain D γ)
      = Union.union (valsU (a.evaluatePlain D γ)) (valsU (b.evaluatePlain D γ)) := by
  rw [u2, AggQueryIn.evaluatePlain_sumByMuX _ _ _ _ ha hb]
  unfold valsU
  rw [Multiset.map_add, Multiset.toFinset_add]

/-- **The values of every column of a relation.** -/
def valsOf (f : ℕ → String) {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n)) :
    AggQueryIn T c 1 (ColKind.allReg 1) :=
  unionFin f n (fun i => projQ (fun _ => SA.col i) q)

theorem noMention_valsOf (f : ℕ → String) {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n))
    {s : String} (h : q.noMention s) : (valsOf f q).noMention s :=
  noMention_unionFin _ n _ (fun _ => noMention_projQ _ _ h)

theorem mem_valsU_valsOf (f : ℕ → String) {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n))
    (hf : ∀ i, q.noMention (f i)) (D : Database T) (γ : Fin c → T) (a : T) :
    a ∈ valsU ((valsOf f q).evaluatePlain D γ) ↔
      ∃ y, Multiset.Mem (q.evaluatePlain D γ) y ∧ ∃ i, y i = a := by
  rw [mem_valsU]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := (mem_unionFin f D γ n _ (fun _ j => noMention_projQ _ _ (hf j)) x).mp hx
    rw [evaluatePlain_projQ] at hi
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hi
    exact ⟨y, hy, i, rfl⟩
  · rintro ⟨y, hy, i, rfl⟩
    refine ⟨fun _ => y i, (mem_unionFin f D γ n _ (fun _ j => noMention_projQ _ _ (hf j)) _).mpr
      ⟨i, ?_⟩, rfl⟩
    rw [evaluatePlain_projQ]
    exact Multiset.mem_map.mpr ⟨y, hy, rfl⟩

/-- **The context's values.** -/
def ambQ (f : ℕ → String) (c : ℕ) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  unionFin f c (fun j => projQ (fun _ => SA.amb j) AggQueryIn.unitC)

theorem mem_valsU_ambQ (f : ℕ → String) (D : Database T) (γ : Fin c → T) (j : Fin c) :
    γ j ∈ valsU ((ambQ f c).evaluatePlain D γ) := by
  refine mem_valsU.mpr ⟨fun _ => γ j, (mem_unionFin f D γ c _
    (fun _ _ => noMention_projQ _ _ (AggQueryIn.noMention_unitC _)) _).mpr ⟨j, ?_⟩, rfl⟩
  rw [evaluatePlain_projQ]
  erw [AggQueryIn.evaluatePlain_unitC D γ Fin.elim0]
  exact Multiset.mem_map.mpr ⟨Fin.elim0, Multiset.mem_singleton_self _, rfl⟩

theorem noMention_ambQ (f : ℕ → String) (s : String) : (ambQ (T := T) f c).noMention s :=
  noMention_unionFin _ c _ (fun _ => noMention_projQ _ _ (AggQueryIn.noMention_unitC _))

/-- **The null, if the domain has one.** -/
def nullQ : AggQueryIn T c 1 (ColKind.allReg 1) :=
  match (ValueType.nullVal : Option T) with
  | some ν => constQ ν
  | none => AggQueryIn.emptyRel 1

theorem mem_valsU_nullQ (D : Database T) (γ : Fin c → T) (a : T)
    (ha : ValueType.isNull a = true) : a ∈ valsU ((nullQ (c := c)).evaluatePlain D γ) := by
  have hν := (ValueType.isNull_iff_nullVal a).mp ha
  unfold nullQ
  split
  · rename_i ν h
    rw [hν] at h
    cases h
    exact mem_valsU.mpr ⟨fun _ => a, Multiset.mem_singleton_self _, rfl⟩
  · rename_i h
    rw [hν] at h
    cases h

theorem noMention_nullQ (s : String) : (nullQ (T := T) (c := c)).noMention s := by
  unfold nullQ
  split
  · exact noMention_constQ _ s
  · exact AggQueryIn.noMention_emptyRel 1 s

/-- **Finitely many constants.** -/
noncomputable def constsQ (f : ℕ → String) (S : Finset T) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  unionFin f S.toList.length (fun i => constQ (S.toList.get i))

theorem mem_valsU_constsQ (f : ℕ → String) (S : Finset T) (D : Database T) (γ : Fin c → T) (a : T)
    (ha : a ∈ S) : a ∈ valsU ((constsQ f S).evaluatePlain D γ) := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr ha)
  refine mem_valsU.mpr ⟨fun _ => a, (mem_unionFin f D γ _ _
    (fun _ _ => noMention_constQ _ _) _).mpr ⟨i, ?_⟩, rfl⟩
  rw [evaluatePlain_constQ, hi]
  exact Multiset.mem_singleton_self _

theorem noMention_constsQ (f : ℕ → String) (S : Finset T) (s : String) :
    (constsQ (c := c) f S).noMention s :=
  noMention_unionFin _ _ _ (fun _ => noMention_constQ _ _)

end Unions

/-! ## The aggregations of the symbolic evaluation, before their cells -/

section Raw

variable {k c : ℕ} (env : SymEnv T k c) (f : ℕ → String)

/-- **A symbolic grouping's rows**: the keys' cells, then the aggregate
values themselves. -/
noncomputable def gammaRaw {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
    (ts : Tuple (TermIn T (k + c) m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T (k + c) m (ColKind.allReg m)) (keep : Fin n₂ → Option (Selection T m)) :
    AggQueryIn T c ((k * (7 + k) + n₁ * (7 + k)) + n₂) (ColKind.allReg _) :=
  AggQueryIn.allRegOf (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) (gKeyIdx is)
    (fun j => termV (ts j)) fs (sym env f q)
    (fun j => (keep j).map (fun φ => (transSel 0 φ).toSel)) .unord)

theorem sym_Gamma {m n₁ n₂ : ℕ} {lab : ℕ} {rd : Fin (k + c) → Bool} (is : Tuple (Fin m) n₁)
    (ts : Tuple (TermIn T (k + c) m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T (k + c) m (ColKind.allReg m)) (keep : Fin n₂ → Option (Selection T m))
    (ord : GroupOrder T m) :
    sym env f (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord)
      = projQ (gOutSA _ _) (gammaRaw env f is ts fs q keep) := by
  rw [sym]; rfl

theorem evaluatePlain_gammaRaw {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
    (ts : Tuple (TermIn T (k + c) m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T (k + c) m (ColKind.allReg m)) (keep : Fin n₂ → Option (Selection T m))
    (D : Database T) (γ : Fin c → T) :
    ((gammaRaw env f is ts fs q keep).evaluatePlain D γ : Multiset _)
      = gammaRows (gKeyIdx is) (fun j => termV (ts j)) fs
          (fun j => (keep j).map (fun φ => (transSel 0 φ).toSel)) .unord
          ((sym env f q).evaluatePlain D γ) γ := by
  rw [gammaRaw, AggQueryIn.evaluatePlain_allRegOf]; rfl

/-- **A symbolic second-level grouping's rows.** -/
noncomputable def nestRaw {m n₁ : ℕ} {κ : Fin m → ColKind} (is : Tuple (Fin m) n₁)
    (p : ProjColIn T (k + c) κ) (g : Multiset T → T) (q : AggQueryIn T (k + c) m κ) :
    AggQueryIn T c ((k * (7 + k) + n₁ * (7 + k)) + 1) (ColKind.allReg _) :=
  AggQueryIn.allRegOf (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) (gKeyIdx is)
    (fun _ h => by cases h) (projV p) g (sym env f q))

theorem sym_GammaNest {m n₁ : ℕ} {κ : Fin m → ColKind} {lab : ℕ} {rd : Fin (k + c) → Bool}
    (is : Tuple (Fin m) n₁) (his : ∀ k', κ (is k') ≠ ColKind.agg) (p : ProjColIn T (k + c) κ)
    (g : Multiset T → T) (q : AggQueryIn T (k + c) m κ) :
    sym env f (AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p g q)
      = projQ (gOutSA _ 1) (nestRaw env f is p g q) := by
  rw [sym]; rfl

theorem evaluatePlain_nestRaw {m n₁ : ℕ} {κ : Fin m → ColKind} (is : Tuple (Fin m) n₁)
    (p : ProjColIn T (k + c) κ) (g : Multiset T → T) (q : AggQueryIn T (k + c) m κ)
    (D : Database T) (γ : Fin c → T) :
    ((nestRaw env f is p g q).evaluatePlain D γ : Multiset _)
      = nestRows (κ' := ColKind.allReg ((k + m) * (7 + k))) (gKeyIdx is) (projV p) g
          ((sym env f q).evaluatePlain D γ) γ := by
  rw [nestRaw, AggQueryIn.evaluatePlain_allRegOf]; rfl

/-- **A symbolic scalar aggregation's rows**, over the padded union. -/
noncomputable def scalarRaw {m n₂ : ℕ} (ts : Tuple (TermIn T (k + c) m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) {κ : Fin m → ColKind} (q : AggQueryIn T (k + c) m κ) :
    AggQueryIn T c (k * (7 + k) + n₂) (ColKind.allReg _) :=
  AggQueryIn.allRegOf (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) sKeyIdx
    (fun j => (termV (ts j)).widen 1) fs
    (AggQueryIn.sumByMuX (AggQueryIn.tri f 0 0) (AggQueryIn.tri f 0 1)
      ((AggQueryIn.Proj (projSA (padSA m)) env.Desc).castKind (projSA_kind _))
      ((AggQueryIn.Proj (projSA (tagSA ValueType.nonzero)) (sym env (AggQueryIn.tri f 1)
        q)).castKind
        (projSA_kind _)))
    (fun _ => some tagSel) .unord)

theorem sym_GammaScalar {m n₂ : ℕ} {lab : ℕ} {rd : Fin (k + c) → Bool}
    (ts : Tuple (TermIn T (k + c) m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T (k + c) m (ColKind.allReg m)) (ord : GroupOrder T m) :
    sym env f (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord)
      = projQ (sOutSA n₂) (scalarRaw env f ts fs q) := by
  rw [sym]; rfl

theorem evaluatePlain_scalarRaw {m n₂ : ℕ} (ts : Tuple (TermIn T (k + c) m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) {κ : Fin m → ColKind} (q : AggQueryIn T (k + c) m κ)
    (h₀ : env.Desc.noMention (AggQueryIn.tri f 0 0))
    (h₁ : (sym env (AggQueryIn.tri f 1) q).noMention (AggQueryIn.tri f 0 1))
    (D : Database T) (γ : Fin c → T) :
    ((scalarRaw env f ts fs q).evaluatePlain D γ : Multiset _)
      = gammaRows sKeyIdx (fun j => (termV (ts j)).widen 1) fs (fun _ => some tagSel) .unord
          ((((env.Desc.evaluatePlain D γ : Multiset (Tuple T (k * (7 + k)))).map (padRow m)).map
              (fun r => Fin.append r (fun _ : Fin 1 => (0 : T))))
            + ((sym env (AggQueryIn.tri f 1) q).evaluatePlain D γ
                : Multiset (Tuple T ((k + m) * (7 + k)))).map
              (fun r => Fin.append r (fun _ : Fin 1 => ValueType.nonzero))) γ := by
  have hpadE : ((AggQueryIn.Proj (projSA (padSA (T := T) (c := c) m)) env.Desc).castKind
      (projSA_kind _)).evaluatePlain D γ
      = (((env.Desc.evaluatePlain D γ : Multiset (Tuple T (k * (7 + k)))).map (padRow m)).map
          (fun r => Fin.append r (fun _ : Fin 1 => (0 : T)))) := by
    rw [evaluatePlain_projSA, Multiset.map_map]
    exact Multiset.map_congr rfl (fun d _ => eval_padSA m d γ)
  have hdatE : ((AggQueryIn.Proj (projSA (tagSA (T := T) (c := c) ValueType.nonzero))
      (sym env (AggQueryIn.tri f 1) q)).castKind (projSA_kind _)).evaluatePlain D γ
      = (((sym env (AggQueryIn.tri f 1) q).evaluatePlain D γ
          : Multiset (Tuple T ((k + m) * (7 + k)))).map
        (fun r => Fin.append r (fun _ : Fin 1 => ValueType.nonzero))) := by
    rw [evaluatePlain_projSA]
    exact Multiset.map_congr rfl (fun r _ => eval_tagSA _ r γ)
  rw [scalarRaw, AggQueryIn.evaluatePlain_allRegOf]
  simp only [AggQueryIn.evaluatePlain]
  rw [AggQueryIn.evaluatePlain_sumByMuX _ _ _ _ (by rw [AggQueryIn.noMention_castKind]; exact h₀)
    (by rw [AggQueryIn.noMention_castKind]; exact h₁), hpadE, hdatE]
  rfl

/-- **A symbolic window's rows**: the input's cells, then the window's
value itself. -/
noncomputable def winRaw {n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) {hsql : w.IsSQL o} (t : TermIn T (k + c) n) (g : SeqAggFunc T) {κ : Fin n
      → ColKind}
    (q : AggQueryIn T (k + c) n κ) (dist : Bool) (keep : Option (Selection T n)) :
    AggQueryIn T c ((k + n) * (7 + k) + 1) (ColKind.allReg _) :=
  AggQueryIn.allRegOf (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false)
    (gKeyIdx P)
    (winOIdx O) (expandSpec o) (expandFrame (k := k) w) (termV t) g (sym env f q)
    (winReadsReg_allReg _ _ _) dist (keep.map (fun φ => (transSel 0 φ).toSel)))

theorem sym_Win {n m p : ℕ} {κ' : Fin n → ColKind} {lab : ℕ} {rd : Fin (k + c) → Bool}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) {hsql :
      w.IsSQL o}
    (t : TermIn T (k + c) n) (g : SeqAggFunc T) (q : AggQueryIn T (k + c) n κ')
    (hrr : WinReadsReg κ' P O t) (dist : Bool) (keep : Option (Selection T n)) :
    sym env f (AggQueryIn.Win (hsql := sql_frame%) (lab := lab) (rd := rd) P O o w t g q hrr dist
      keep)
      = projQ (wOutSA n) (winRaw (hsql := sql_frame%) env f P O o w t g q dist keep) := by
  rw [sym]; rfl

theorem evaluatePlain_winRaw {n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) {hsql : w.IsSQL o} (t : TermIn T (k + c) n) (g :
      SeqAggFunc T)
    {κ : Fin n → ColKind} (q : AggQueryIn T (k + c) n κ) (dist : Bool)
    (keep : Option (Selection T n)) (D : Database T) (γ : Fin c → T) :
    ((winRaw (hsql := sql_frame%) env f P O o w t g q dist keep).evaluatePlain D γ : Multiset _)
      = winRows (gKeyIdx P) (winOIdx O) (expandSpec o) (expandFrame (k := k) w) (termV t)
          (if dist then g.distinct else g) (keep.map (fun φ => (transSel 0 φ).toSel))
          ((sym env f q).evaluatePlain D γ) γ := by
  rw [winRaw, AggQueryIn.evaluatePlain_allRegOf]
  simp only [AggQueryIn.evaluatePlain, ColKind.readTuple_allReg, Multiset.map_id']
  rfl

end Raw

/-! ## The cut -/

/-- An eighth of a supply of names. -/
def part (f : ℕ → String) (j : ℕ) : ℕ → String := fun i => f (8 * i + j)

/-- The values of some columns of a relation. -/
def colsQ {c N p : ℕ} (f : ℕ → String) (q : AggQueryIn T c N (ColKind.allReg N)) (idx : Fin p →
    Fin N) :
    AggQueryIn T c 1 (ColKind.allReg 1) :=
  unionFin f p (fun j => projQ (fun _ => SA.col (idx j)) q)

/-- **A cut**: the null, the context's values, finitely many constants and
the values a query computes. -/
noncomputable def cutOf {c : ℕ} (f : ℕ → String) (S : Finset T)
    (core : AggQueryIn T c 1 (ColKind.allReg 1)) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  u2 (part f 0) (u2 (part f 1) nullQ (ambQ (part f 2) c)) (u2 (part f 3) (constsQ (part f 4) S)
    core)

variable {k c : ℕ}

/-- **The values a query reads and computes**: those of the relations it
reads and those its aggregations compute, read off their symbolic
counterparts relative to the cut of their input. -/
noncomputable def cutCore (cnt : SeqAggFunc T) (f : ℕ → String) :
    {n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T (k + c) n κ l → AggQueryIn T c 1 (ColKind.allReg 1)
  | _, _, _, .Rel n s => valsOf f (AggQueryIn.Rel n s)
  | _, _, _, .Hole _ _ _ => AggQueryIn.emptyRel 1
  | _, _, _, .Param _ _ => AggQueryIn.emptyRel 1
  | _, _, _, .Empty => AggQueryIn.emptyRel 1
  | _, _, _, .Proj _ q => cutCore cnt f q
  | _, _, _, .Sel _ q _ => cutCore cnt f q
  | _, _, _, .Prod q₁ q₂ => u2 (part f 0) (cutCore cnt (part f 1) q₁) (cutCore cnt (part f 2) q₂)
  | _, _, _, .Explode _ _ q => cutCore cnt f q
  | _, _, _, .Retag _ q => cutCore cnt f q
  | _, _, _, .Mu _ q₀ q₁ => u2 (part f 0) (cutCore cnt (part f 1) q₀) (cutCore cnt (part f 2) q₁)
  | _, _, _, .Gamma is ts fs q keep ord =>
    u2 (part f 0) (cutCore cnt (part f 1) q)
      (colsQ (part f 2) (gammaRaw (envOf (part f 3) cnt k (cutOf (part f 4)
        (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) is ts fs q keep ord).allConsts
        (cutCore cnt (part f 1) q))) (part f 5) is ts fs q keep) (fun j => Fin.natAdd _ j))
  | _, _, _, .GammaScalar ts fs q ord =>
    u2 (part f 0) (cutCore cnt (part f 1) q)
      (colsQ (part f 2) (scalarRaw (envOf (part f 3) cnt k (cutOf (part f 4)
        (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ts fs q ord).allConsts
        (cutCore cnt (part f 1) q))) (part f 5) ts fs q) (fun j => Fin.natAdd _ j))
  | _, _, _, .GammaNest is his p g q =>
    u2 (part f 0) (cutCore cnt (part f 1) q)
      (colsQ (part f 2) (nestRaw (envOf (part f 3) cnt k (cutOf (part f 4)
        (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) is his p g q).allConsts
        (cutCore cnt (part f 1) q))) (part f 5) is p g q) (fun j : Fin 1 => Fin.natAdd _ j))
  | _, _, _, .Win P O o w t g q hrr dist keep =>
    u2 (part f 0) (cutCore cnt (part f 1) q)
      (colsQ (part f 2) (winRaw (hsql := sql_frame%) (envOf (part f 3) cnt k (cutOf (part f 4)
        (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) P O o w t g q hrr
          dist keep).allConsts
        (cutCore cnt (part f 1) q))) (part f 5) P O o w t g q dist keep)
        (fun _ : Fin 1 => Fin.last _))
  | _, _, _, .Apply _ _ => AggQueryIn.emptyRel 1
  | _, _, _, .Sum _ _ => AggQueryIn.emptyRel 1
  | _, _, _, .Dedup _ => AggQueryIn.emptyRel 1
  | _, _, _, .Diff _ _ => AggQueryIn.emptyRel 1
  | _, _, _, .MuSet _ _ _ => AggQueryIn.emptyRel 1
  | _, _, _, .GammaTok _ _ _ _ _ _ _ => AggQueryIn.emptyRel 1
  | _, _, _, .ProvSum _ _ _ _ => AggQueryIn.emptyRel 1
  | _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => AggQueryIn.emptyRel 1
  termination_by _ _ _ q => sizeOf q

/-- **The cut of a query.** -/
noncomputable def cutQ (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (q : AggQueryIn T (k + c) n κ l) : AggQueryIn T c 1 (ColKind.allReg 1)
      :=
  cutOf (part f 0) q.allConsts (cutCore cnt (part f 1) q)

/-! ## What the cut names -/

theorem noMention_colsQ {c N p : ℕ} (f : ℕ → String) (q : AggQueryIn T c N (ColKind.allReg N))
    (idx : Fin p → Fin N) {s : String} (h : q.noMention s) : (colsQ f q idx).noMention s :=
  noMention_unionFin _ p _ (fun _ => noMention_projQ _ _ h)

theorem noMention_cutOf {c : ℕ} (f : ℕ → String) (S : Finset T)
    {core : AggQueryIn T c 1 (ColKind.allReg 1)} {s : String} (h : core.noMention s) :
    (cutOf f S core).noMention s :=
  noMention_u2 _ (noMention_u2 _ (noMention_nullQ s) (noMention_ambQ _ s))
    (noMention_u2 _ (noMention_constsQ _ S s) h)

theorem noMention_sym {k c : ℕ} (env : SymEnv T k c) {s : String} (henv : EnvNoMention env s)
    (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T (k + c) n κ l) (hq : q.noMention s) : (sym env f q).noMention s :=
  (noMention_sym_aux env henv _ f q le_rfl hq).1

/-- **The cut names only what the query names.** -/
theorem noMention_cutCore (cnt : SeqAggFunc T) {s : String} :
    ∀ (N : ℕ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
      (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N → q.noMention s →
      (cutCore cnt f q).noMention s := by
  intro N
  induction N with
  | zero =>
    intro f n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro f n κ l q hq hm
    have henv : ∀ (g g' : ℕ → String) (S : Finset T) {m : ℕ} {κ' : Fin m → ColKind}
        (p : AggQueryIn T (k + c) m κ'), sizeOf p ≤ N → p.noMention s →
        EnvNoMention (envOf g cnt k (cutOf g' S (cutCore cnt (part f 1) p))) s :=
      by
        intro g g' S m κ' p hp hpm
        exact envNoMention_envOf _ cnt k _ (noMention_cutOf _ S (ih _ p hp hpm))
    cases q with
    | Rel n s' =>
      rw [cutCore]
      exact noMention_valsOf _ _ hm
    | Hole => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | Param => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | Empty => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | Proj ps q => rw [cutCore]; exact ih f q (by simp at hq; omega) hm
    | Sel φ q _ => rw [cutCore]; exact ih f q (by simp at hq; omega) hm
    | Prod q₁ q₂ =>
      rw [cutCore]
      exact noMention_u2 _ (ih _ q₁ (by simp at hq; omega) hm.1) (ih _ q₂ (by simp at hq; omega)
          hm.2)
    | Explode _ _ q => rw [cutCore]; exact ih f q (by simp at hq; omega) hm
    | Retag _ q => rw [cutCore]; exact ih f q (by simp at hq; omega) hm
    | Mu _ q₀ q₁ =>
      rw [cutCore]
      exact noMention_u2 _ (ih _ q₀ (by simp at hq; omega) hm.1) (ih _ q₁ (by simp at hq; omega)
          hm.2)
    | Gamma is ts fs q keep ord =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [cutCore]
      refine noMention_u2 _ (ih _ q hs hm) (noMention_colsQ _ _ _ ?_)
      rw [gammaRaw, AggQueryIn.noMention_allRegOf]
      exact noMention_sym _ (henv _ _ _ q hs hm) _ q hm
    | GammaScalar ts fs q ord =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [cutCore]
      refine noMention_u2 _ (ih _ q hs hm) (noMention_colsQ _ _ _ ?_)
      rw [scalarRaw, AggQueryIn.noMention_allRegOf]
      refine AggQueryIn.noMention_sumByMuX _ _ _ _ ?_ ?_
      · rw [AggQueryIn.noMention_castKind]; exact (henv _ _ _ q hs hm).2.1
      · rw [AggQueryIn.noMention_castKind]; exact noMention_sym _ (henv _ _ _ q hs hm) _ q hm
    | GammaNest is his p g q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [cutCore]
      refine noMention_u2 _ (ih _ q hs hm) (noMention_colsQ _ _ _ ?_)
      rw [nestRaw, AggQueryIn.noMention_allRegOf]
      exact noMention_sym _ (henv _ _ _ q hs hm) _ q hm
    | Win P O o w t g q hrr dist keep =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [cutCore]
      refine noMention_u2 _ (ih _ q hs hm) (noMention_colsQ _ _ _ ?_)
      rw [winRaw, AggQueryIn.noMention_allRegOf]
      exact noMention_sym _ (henv _ _ _ q hs hm) _ q hm
    | Apply => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | Sum => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | Dedup => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | Diff => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | MuSet => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | GammaTok => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | ProvSum => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s
    | WinExpr => rw [cutCore]; exact AggQueryIn.noMention_emptyRel 1 s

/-! ## What the cut holds -/

/-- **A cut holds the null, the context's values, its constants and the
values of its core.** -/
theorem mem_cutOf {c : ℕ} (f : ℕ → String) (S : Finset T) (core : AggQueryIn T c 1 (ColKind.allReg
    1))
    (hcore : ∀ i, core.noMention (f i)) (D : Database T) (γ : Fin c → T) :
    (∀ a : T, ValueType.isNull a = true → a ∈ valsU ((cutOf f S core).evaluatePlain D γ))
      ∧ (∀ j, γ j ∈ valsU ((cutOf f S core).evaluatePlain D γ))
      ∧ S ⊆ valsU ((cutOf f S core).evaluatePlain D γ)
      ∧ valsU (core.evaluatePlain D γ) ⊆ valsU ((cutOf f S core).evaluatePlain D γ) := by
  have h1 := valsU_u2 (part f 0) (u2 (part f 1) nullQ (ambQ (part f 2) c))
    (u2 (part f 3) (constsQ (part f 4) S) core)
    (noMention_u2 _ (noMention_nullQ _) (noMention_ambQ _ _))
    (noMention_u2 _ (noMention_constsQ _ S _) (hcore _)) D γ
  have h2 := valsU_u2 (part f 1) nullQ (ambQ (part f 2) c) (noMention_nullQ _) (noMention_ambQ _ _)
    D γ
  have h3 := valsU_u2 (part f 3) (constsQ (part f 4) S) core (noMention_constsQ _ S _) (hcore _) D γ
  rw [cutOf]
  rw [h1, h2, h3]
  refine ⟨fun a ha => ?_, fun j => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_valsU_nullQ D γ a ha))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_valsU_ambQ _ D γ j))
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (mem_valsU_constsQ _ S D γ a ha))
  · exact Finset.mem_union_right _ (Finset.mem_union_right _ ha)

theorem valsU_colsQ {c N p : ℕ} (f : ℕ → String) (q : AggQueryIn T c N (ColKind.allReg N))
    (idx : Fin p → Fin N) (hf : ∀ i, q.noMention (f i)) (D : Database T) (γ : Fin c → T) (a : T) :
    a ∈ valsU ((colsQ f q idx).evaluatePlain D γ) ↔
      ∃ y, Multiset.Mem (q.evaluatePlain D γ) y ∧ ∃ j, y (idx j) = a := by
  rw [mem_valsU]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := (mem_unionFin f D γ p _ (fun _ j => noMention_projQ _ _ (hf j)) x).mp hx
    rw [evaluatePlain_projQ] at hi
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hi
    exact ⟨y, hy, i, rfl⟩
  · rintro ⟨y, hy, i, rfl⟩
    refine ⟨fun _ => y (idx i), (mem_unionFin f D γ p _ (fun _ j => noMention_projQ _ _ (hf j))
        _).mpr
      ⟨i, ?_⟩, rfl⟩
    rw [evaluatePlain_projQ]
    exact Multiset.mem_map.mpr ⟨y, hy, rfl⟩

/-! ## The cut makes the evaluation good -/

/-- **The classes of the basis with products in place of the apply**:
`∅`, `Π`, `σ`, `×`, `γ`, `win`, `μ^⊎`. -/
def basisProdOps : Set OpKind :=
  {OpKind.empty, OpKind.proj, OpKind.sel, OpKind.prod, OpKind.gamma, OpKind.win, OpKind.muBag}

/-- **What a cut is asked of a query**: the null, the context's values,
the query's constants and the values of its core. -/
def CutOK {c' n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (cnt : SeqAggFunc T)
    (f : ℕ → String) (q : AggQueryIn T (k + c') n κ l) (C : Finset T) (D : Database T)
    (γ : Fin c' → T) : Prop :=
  (∀ a : T, ValueType.isNull a = true → a ∈ C) ∧ (∀ j, γ j ∈ C) ∧ q.allConsts ⊆ C
    ∧ valsU ((cutCore cnt f q).evaluatePlain D γ) ⊆ C

/-- The symbolic evaluation relative to a node's cut names only what the
query names. -/
theorem noMention_symCut (cnt : SeqAggFunc T) (f : ℕ → String) (S : Finset T) {m : ℕ}
    {κ' : Fin m → ColKind} (q : AggQueryIn T (k + c) m κ') {s : String} (hs : q.noMention s) :
    (sym (envOf (part f 3) cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) (part f 5)
      q).noMention s :=
  noMention_sym _ (envNoMention_envOf _ cnt k _ (noMention_cutOf _ S
    (noMention_cutCore cnt _ _ q le_rfl hs))) _ q hs

/-- **The cut makes the evaluation good**, in both modes: a closed query at
every parameter row where it settles, a recursive term at every round. -/
theorem good_cutCore (Θ : Set (SeqAggFunc T)) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) :
    ∀ (N : ℕ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
      (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N → q.usesOnly basisProdOps → SymSrc Θ q →
      (∀ i, q.noMention (f i)) →
      ∀ (C : Finset T) (D : Database T) (γ : Fin c → T), CutOK cnt f q C D γ →
      ∀ par : Fin k → T,
        (l = [] → q.SettlesAt D (Fin.append par γ) → Good (CG C) q D (Fin.append par γ))
        ∧ (∀ (s : String) (m : ℕ), l = [(s, m)] → q.noMention s → ∀ X : Relation T m,
            q.SettlesAt (D.assign s X) (Fin.append par γ) →
            Good (CG C) q (D.assign s X) (Fin.append par γ)) := by
  intro N
  induction N with
  | zero =>
    intro f n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro f n κ l q hq hU hsrc hfr C D γ hC par
    obtain ⟨hCn, hCa, hCk, hCc⟩ := hC
    have hnil : ∀ {s : String} {m : ℕ}, ([] : List (String × ℕ)) ≠ [(s, m)] := by simp
    -- the symbolic evaluation of a closed input, relative to the cut of its node
    have hsym : ∀ {m : ℕ} {κ' : Fin m → ColKind} (q : AggQueryIn T (k + c) m κ') (S : Finset T)
        (g : ℕ → String), (∀ i, q.noMention (g i)) →
        sizeOf q ≤ N → q.usesOnly basisProdOps → SymSrc Θ q →
        (∀ i, q.noMention (f i)) → q.allConsts ⊆ S → q.SettlesAt D (Fin.append par γ) →
        SliceIs (P := 0) (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1) q)).evaluatePlain D
          γ)) par
          ((sym (envOf (part f 3) cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) g
            q).evaluatePlain D γ)
          ((q.evaluatePlain D (Fin.append par γ) : Multiset (Tuple T m)).map
            (fun v => (v, Fin.elim0)))
        ∧ (∀ v, Multiset.Mem (q.evaluatePlain D (Fin.append par γ)) v → ∀ i,
            GoodVal (C := valsU ((cutOf (part f 4) S (cutCore cnt (part f 1) q)).evaluatePlain D γ))
              par (v i))
        ∧ S ⊆ valsU ((cutOf (part f 4) S (cutCore cnt (part f 1) q)).evaluatePlain D γ)
        ∧ (∀ j, CG (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1) q)).evaluatePlain D γ))
            (γ j))
        ∧ EnvOK (envOf (part f 3) cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) D γ := by
      intro m κ' q S g hg hs hUq hsq hfq hSq hset
      have hcore : ∀ s, q.noMention s → (cutOf (part f 4) S (cutCore cnt (part f 1) q)).noMention
          s :=
        fun s hs' => noMention_cutOf _ S (noMention_cutCore cnt _ _ q le_rfl hs')
      have facts := mem_cutOf (part f 4) S (cutCore cnt (part f 1) q)
        (fun i => noMention_cutCore cnt _ _ q le_rfl (hfq _)) D γ
      have hgood := (ih (part f 1) q hs hUq hsq (fun i => hfq _) _ D γ
        ⟨facts.1, facts.2.1, hSq.trans facts.2.2.1, facts.2.2.2⟩ par).1 rfl hset
      have henv := envOK_envOf (part f 3) hc k _ (fun i => hcore _ (hfq _)) D γ facts.1
      have hfr' : ∀ i, q.noMention (g i) ∧ EnvNoMention (envOf (part f 3) cnt k
          (cutOf (part f 4) S (cutCore cnt (part f 1) q))) (g i) :=
        fun i => ⟨hg i, envNoMention_envOf _ cnt k _ (hcore _ (hg i))⟩
      obtain ⟨hS, hG⟩ := (sym_correct_aux _ Θ _ g q le_rfl hsq hfr' D γ par henv
        (fun j => Or.inl (facts.2.1 j))).1 rfl hgood hset
      exact ⟨hS, hG, facts.2.2.1, fun j => Or.inl (facts.2.1 j), henv⟩
    cases q with
    | Rel n s' =>
      refine ⟨fun _ _ v hv i => Or.inl (hCc ?_), fun s m hl => absurd hl hnil⟩
      rw [cutCore]
      exact (mem_valsU_valsOf f (AggQueryIn.Rel (c := c) n s') hfr D γ _).mpr ⟨v, hv, i, rfl⟩
    | Hole n s' κ' =>
      exact ⟨fun hl => absurd hl.symm hnil, fun _ _ _ _ _ _ => trivial⟩
    | Param pv ρ =>
      refine ⟨fun _ _ j a ha => Or.inl (hCk ?_), fun s m hl => absurd hl hnil⟩
      show a ∈ Finset.univ.biUnion _
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by rw [ha]; simp⟩
    | Empty => exact ⟨fun _ _ => trivial, fun s m hl => absurd hl hnil⟩
    | Apply q₁ q₂ => exact absurd hU.1 (by simp [basisProdOps])
    | Sum q₁ q₂ => exact absurd hU.1 (by simp [basisProdOps])
    | Dedup q => exact absurd hU.1 (by simp [basisProdOps])
    | Diff q₁ q₂ => exact absurd hU.1 (by simp [basisProdOps])
    | MuSet s' q₀ q₁ => exact absurd hU.1 (by simp [basisProdOps])
    | GammaTok is his ts fs a q keep => exact hU.elim
    | ProvSum is his t q => exact hU.elim
    | WinExpr P O o ws ts fs g q keeps => exact hsrc.1.elim
    | Proj ps q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      have hC' : CutOK cnt f q C D γ :=
        ⟨hCn, hCa, fun a ha => hCk (Finset.mem_union_right _ ha), by rw [cutCore] at hCc; exact hCc⟩
      obtain ⟨hcl, hbd⟩ := ih f q hs hU.2 ⟨hsrc.1.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfr C D γ
        hC' par
      have hcs : ∀ j, ∀ a ∈ (ps j).consts, CG C a := fun j a ha =>
        Or.inl (hCk (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩)))
      exact ⟨fun hl hset => ⟨hcs, hcl hl hset⟩, fun s m hl hnm X hset => ⟨hcs, hbd s m hl hnm X
          hset⟩⟩
    | Sel φ q hφ =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      have hC' : CutOK cnt f q C D γ :=
        ⟨hCn, hCa, fun a ha => hCk (Finset.mem_union_right _ ha), by rw [cutCore] at hCc; exact hCc⟩
      obtain ⟨hcl, hbd⟩ := ih f q hs hU.2 ⟨hsrc.1.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfr C D γ
        hC' par
      have hcs : ∀ a ∈ φ.consts, CG C a := fun a ha => Or.inl (hCk (Finset.mem_union_left _ ha))
      exact ⟨fun hl hset => ⟨hcs, hcl hl hset⟩, fun s m hl hnm X hset => ⟨hcs, hbd s m hl hnm X
          hset⟩⟩
    | Explode i hi q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      have hC' : CutOK cnt f q C D γ := ⟨hCn, hCa, hCk, by rw [cutCore] at hCc; exact hCc⟩
      exact ih f q hs hU ⟨hsrc.1, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfr C D γ hC' par
    | Retag h q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      have hC' : CutOK cnt f q C D γ := ⟨hCn, hCa, hCk, by rw [cutCore] at hCc; exact hCc⟩
      exact ih f q hs hU ⟨hsrc.1, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfr C D γ hC' par
    | Prod q₁ q₂ =>
      rename_i n₁ n₂ κ₁ κ₂ l₁ l₂
      have hs₁ : sizeOf q₁ ≤ N := by simp at hq; omega
      have hs₂ : sizeOf q₂ ≤ N := by simp at hq; omega
      rw [cutCore] at hCc
      rw [valsU_u2 (part f 0) (cutCore cnt (part f 1) q₁) (cutCore cnt (part f 2) q₂)
        (noMention_cutCore cnt _ _ q₁ le_rfl (hfr _).1)
        (noMention_cutCore cnt _ _ q₂ le_rfl (hfr _).2)] at hCc
      have hC₁ : CutOK cnt (part f 1) q₁ C D γ :=
        ⟨hCn, hCa, fun a ha => hCk (Finset.mem_union_left _ ha),
          fun a ha => hCc (Finset.mem_union_left _ ha)⟩
      have hC₂ : CutOK cnt (part f 2) q₂ C D γ :=
        ⟨hCn, hCa, fun a ha => hCk (Finset.mem_union_right _ ha),
          fun a ha => hCc (Finset.mem_union_right _ ha)⟩
      obtain ⟨hcl₁, hbd₁⟩ := ih (part f 1) q₁ hs₁ hU.2.1
        ⟨hsrc.1.1, hsrc.2.1, hsrc.2.2.1.1, hsrc.2.2.2.1⟩ (fun i => (hfr _).1) C D γ hC₁ par
      obtain ⟨hcl₂, hbd₂⟩ := ih (part f 2) q₂ hs₂ hU.2.2
        ⟨hsrc.1.2, hsrc.2.1, hsrc.2.2.1.2, hsrc.2.2.2.2⟩ (fun i => (hfr _).2) C D γ hC₂ par
      refine ⟨fun hl hset => ?_, fun s m hl hnm X hset => ?_⟩
      · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hl
        exact ⟨hcl₁ rfl hset.1, hcl₂ rfl hset.2⟩
      · rcases List.append_eq_singleton' hl with ⟨h₁, rfl⟩ | ⟨rfl, h₂⟩
        · refine ⟨hbd₁ s m h₁ hnm.1 X hset.1, ?_⟩
          exact (good_assign_of_noMention _ X q₂ hnm.2 D _).mpr
            (hcl₂ rfl (AggQueryIn.settlesAt_assign_of_noMention X q₂ hnm.2 D _ hset.2))
        · refine ⟨?_, hbd₂ s m h₂ hnm.2 X hset.2⟩
          exact (good_assign_of_noMention _ X q₁ hnm.1 D _).mpr
            (hcl₁ rfl (AggQueryIn.settlesAt_assign_of_noMention X q₁ hnm.1 D _ hset.1))
    | Mu s' q₀ q₁ =>
      have hs₀ : sizeOf q₀ ≤ N := by simp at hq; omega
      have hs₁ : sizeOf q₁ ≤ N := by simp at hq; omega
      rw [cutCore] at hCc
      rw [valsU_u2 (part f 0) (cutCore cnt (part f 1) q₀) (cutCore cnt (part f 2) q₁)
        (noMention_cutCore cnt _ _ q₀ le_rfl (hfr _).1)
        (noMention_cutCore cnt _ _ q₁ le_rfl (hfr _).2)] at hCc
      have hC₀ : CutOK cnt (part f 1) q₀ C D γ :=
        ⟨hCn, hCa, fun a ha => hCk (Finset.mem_union_left _ ha),
          fun a ha => hCc (Finset.mem_union_left _ ha)⟩
      have hC₁ : CutOK cnt (part f 2) q₁ C D γ :=
        ⟨hCn, hCa, fun a ha => hCk (Finset.mem_union_right _ ha),
          fun a ha => hCc (Finset.mem_union_right _ ha)⟩
      obtain ⟨hnm₀, hnm₁, hhy₀, hhy₁⟩ := hsrc.2.2.2
      obtain ⟨hcl₀, -⟩ := ih (part f 1) q₀ hs₀ hU.2.1
        ⟨hsrc.1.1, hsrc.2.1, hsrc.2.2.1.1, hhy₀⟩ (fun i => (hfr _).1) C D γ hC₀ par
      obtain ⟨-, hbd₁⟩ := ih (part f 2) q₁ hs₁ hU.2.2
        ⟨hsrc.1.2, hsrc.2.1, hsrc.2.2.1.2, hhy₁⟩ (fun i => (hfr _).2) C D γ hC₁ par
      refine ⟨fun _ hset => ⟨hcl₀ rfl hset.1, fun j => hbd₁ s' _ rfl hnm₁ _ (hset.2.2.2 j)⟩,
        fun s m hl => absurd hl hnil⟩
    | Gamma is ts fs q keep ord =>
      rename_i m n₁ n₂ lab rd
      have hs : sizeOf q ≤ N := by simp at hq; omega
      set S := (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) is ts fs q keep ord).allConsts
        with hSdef
      have hSq : q.allConsts ⊆ S := Finset.subset_union_right
      have hSC : S ⊆ C := hCk
      have hsrc' : SymSrc Θ q := ⟨hsrc.1.2.2.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩
      have hgrNM : ∀ s, q.noMention s → (gammaRaw (envOf (part f 3) cnt k (cutOf (part f 4) S
          (cutCore cnt (part f 1) q))) (part f 5) is ts fs q keep).noMention s := by
        intro s hs'
        unfold gammaRaw
        rw [AggQueryIn.noMention_allRegOf]
        exact noMention_symCut cnt f S q hs'
      rw [cutCore] at hCc
      rw [valsU_u2 (part f 0) (cutCore cnt (part f 1) q) (colsQ (part f 2) (gammaRaw (envOf (part
        f 3)
        cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) (part f 5) is ts fs q keep)
        (fun j => Fin.natAdd _ j)) (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_colsQ _ _ _ (hgrNM _ (hfr _)))] at hCc
      have hC' : CutOK cnt (part f 1) q C D γ :=
        ⟨hCn, hCa, hSq.trans hSC, fun a ha => hCc (Finset.mem_union_left _ ha)⟩
      obtain ⟨hcl, -⟩ := ih (part f 1) q hs hU.2 hsrc' (fun i => hfr _) C D γ hC' par
      refine ⟨fun _ hset => ⟨hcl rfl hset, fun j φ hφ a ha => Or.inl (hSC ?_), fun y hy j => ?_⟩,
        fun s m hl => absurd hl hnil⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_univ _, ?_⟩))
        rw [hφ]; exact ha
      · obtain ⟨hS, hG, hSC', -, -⟩ := hsym q S (part f 5) (fun i => hfr _) hs hU.2 hsrc'
          (fun i => hfr i) hSq hset
        have hkeep : ∀ j φ, keep j = some φ → φ.noFun = true
            ∧ ∀ a ∈ φ.consts, CG (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1)
              q)).evaluatePlain
              D γ)) a := by
          intro j φ hφ
          refine ⟨by have := hsrc.1.2.2.1 j; rw [hφ] at this; exact this, fun a ha => Or.inl (hSC'
              ?_)⟩
          refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨j, Finset.mem_univ _, ?_⟩))
          rw [hφ]; exact ha
        have heq := gammaRows_slice par is ts fs keep ord hsrc.1.1 (fun j => hsrc.2.1 _
            (hsrc.1.2.1 j))
          hkeep _ _ hG hS γ
        have hrow : Multiset.Mem ((gammaRaw (envOf (part f 3) cnt k (cutOf (part f 4) S
              (cutCore cnt (part f 1) q))) (part f 5) is ts fs q keep).evaluatePlain D γ)
            (Fin.append (encK (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1)
              q)).evaluatePlain D γ)) par (fun t => y (Fin.castAdd n₂ t)))
              (fun j => y (Fin.natAdd n₁ j))) := by
          rw [evaluatePlain_gammaRaw]
          refine Multiset.mem_of_mem_filter (p := fun x => keyDesc (M := n₁ * (7 + k))
            (fun i => x (Fin.castAdd n₂ i)) = descEnc (valsU ((cutOf (part f 4) S
              (cutCore cnt (part f 1) q)).evaluatePlain D γ)) par) ?_
          rw [heq]
          exact Multiset.mem_map_of_mem _ hy
        refine Or.inl (hCc (Finset.mem_union_right _ ?_))
        refine (valsU_colsQ _ _ _ (fun i => hgrNM _ (hfr _)) D γ _).mpr ⟨_, hrow, j, ?_⟩
        exact Fin.append_right _ _ j
    | GammaNest is his p g q =>
      rename_i m n₁ κq lab rd
      have hs : sizeOf q ≤ N := by simp at hq; omega
      set S := (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) is his p g q).allConsts
        with hSdef
      have hSq : q.allConsts ⊆ S := Finset.subset_union_right
      have hSC : S ⊆ C := hCk
      have hsrc' : SymSrc Θ q := ⟨hsrc.1.2.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩
      have hrNM : ∀ s, q.noMention s → (nestRaw (envOf (part f 3) cnt k (cutOf (part f 4) S
          (cutCore cnt (part f 1) q))) (part f 5) is p g q).noMention s := by
        intro s hs'
        unfold nestRaw
        rw [AggQueryIn.noMention_allRegOf]
        exact noMention_symCut cnt f S q hs'
      rw [cutCore] at hCc
      rw [valsU_u2 (part f 0) (cutCore cnt (part f 1) q) (colsQ (part f 2) (nestRaw (envOf (part f
        3)
        cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) (part f 5) is p g q)
        (fun j : Fin 1 => Fin.natAdd _ j)) (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_colsQ _ _ _ (hrNM _ (hfr _)))] at hCc
      have hC' : CutOK cnt (part f 1) q C D γ :=
        ⟨hCn, hCa, hSq.trans hSC, fun a ha => hCc (Finset.mem_union_left _ ha)⟩
      obtain ⟨hcl, -⟩ := ih (part f 1) q hs hU.2 hsrc' (fun i => hfr _) C D γ hC' par
      refine ⟨fun _ hset => ⟨hcl rfl hset, fun a ha => Or.inl (hSC (Finset.mem_union_left _ ha)),
        fun y hy => ?_⟩, fun s m hl => absurd hl hnil⟩
      obtain ⟨hS, hG, hSC', hamb', -⟩ := hsym q S (part f 5) (fun i => hfr _) hs hU.2 hsrc'
        (fun i => hfr i) hSq hset
      obtain ⟨g', hg', hgΘ, rfl⟩ := hsrc.1.2.1
      have heq := nestRows_slice par is p hsrc.1.1
        (fun a ha => Or.inl (hSC' (Finset.mem_union_left _ ha))) g' hg' (hsrc.2.1 _ hgΘ) _ _ hS γ
        (fun j => hamb' j)
      have hrow : Multiset.Mem ((nestRaw (envOf (part f 3) cnt k (cutOf (part f 4) S
            (cutCore cnt (part f 1) q))) (part f 5) is p (SeqAggFunc.onBag g' hg')
              q).evaluatePlain D γ)
          (Fin.append (encK (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1)
            q)).evaluatePlain D γ)) par (fun t => y (Fin.castAdd 1 t)))
            (fun j => y (Fin.natAdd n₁ j))) := by
        rw [evaluatePlain_nestRaw]
        refine Multiset.mem_of_mem_filter (p := fun x => keyDesc (M := n₁ * (7 + k))
          (fun i => x (Fin.castAdd 1 i)) = descEnc (valsU ((cutOf (part f 4) S
            (cutCore cnt (part f 1) q)).evaluatePlain D γ)) par) ?_
        rw [heq]
        exact Multiset.mem_map_of_mem _ hy
      refine Or.inl (hCc (Finset.mem_union_right _ ?_))
      refine (valsU_colsQ _ _ _ (fun i => hrNM _ (hfr _)) D γ _).mpr ⟨_, hrow, 0, ?_⟩
      exact Fin.append_right _ _ 0
    | GammaScalar ts fs q ord =>
      rename_i m lab rd
      have hs : sizeOf q ≤ N := by simp at hq; omega
      set S := (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ts fs q ord).allConsts
        with hSdef
      have hSq : q.allConsts ⊆ S := Finset.subset_union_right
      have hSC : S ⊆ C := hCk
      have hsrc' : SymSrc Θ q := ⟨hsrc.1.2.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩
      have henvNM : ∀ s, q.noMention s → EnvNoMention (envOf (part f 3) cnt k (cutOf (part f 4) S
          (cutCore cnt (part f 1) q))) s := fun s hs' =>
        envNoMention_envOf _ cnt k _ (noMention_cutOf _ S (noMention_cutCore cnt _ _ q le_rfl hs'))
      have hrNM : ∀ s, q.noMention s → (scalarRaw (envOf (part f 3) cnt k (cutOf (part f 4) S
          (cutCore cnt (part f 1) q))) (part f 5) ts fs q).noMention s := by
        intro s hs'
        unfold scalarRaw
        rw [AggQueryIn.noMention_allRegOf]
        refine AggQueryIn.noMention_sumByMuX _ _ _ _ ?_ ?_
        · rw [AggQueryIn.noMention_castKind]; exact (henvNM s hs').2.1
        · rw [AggQueryIn.noMention_castKind]; exact noMention_sym _ (henvNM s hs') _ q hs'
      rw [cutCore] at hCc
      rw [valsU_u2 (part f 0) (cutCore cnt (part f 1) q) (colsQ (part f 2) (scalarRaw (envOf
        (part f 3) cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) (part f 5) ts fs q)
        (fun j => Fin.natAdd _ j)) (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_colsQ _ _ _ (hrNM _ (hfr _)))] at hCc
      have hC' : CutOK cnt (part f 1) q C D γ :=
        ⟨hCn, hCa, hSq.trans hSC, fun a ha => hCc (Finset.mem_union_left _ ha)⟩
      obtain ⟨hcl, -⟩ := ih (part f 1) q hs hU.2 hsrc' (fun i => hfr _) C D γ hC' par
      refine ⟨fun _ hset => ⟨hcl rfl hset, fun y hy i => ?_⟩, fun s m hl => absurd hl hnil⟩
      obtain ⟨hS, -, -, -, hnd, hdesc, -⟩ := hsym q S (AggQueryIn.tri (part f 5) 1) (fun i => hfr _)
        hs hU.2 hsrc' (fun i => hfr i) hSq hset
      have hpad : (((((envOf (part f 3) cnt k (cutOf (part f 4) S (cutCore cnt (part f 1)
            q))).Desc.evaluatePlain D γ : Multiset (Tuple T (k * (7 + k)))).map (padRow m)).map
              (fun r => descP (P := 0) r)).Nodup
          ∧ descEnc (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1) q)).evaluatePlain D γ)) par
            ∈ (((envOf (part f 3) cnt k (cutOf (part f 4) S (cutCore cnt (part f 1)
              q))).Desc.evaluatePlain D γ : Multiset (Tuple T (k * (7 + k)))).map (padRow m)).map
                (fun r => descP (P := 0) r)) := by
        rw [Multiset.map_map]
        simp only [Function.comp, descP_padRow, Multiset.map_id']
        exact ⟨hnd, hdesc par⟩
      have heq := gammaScalar_slice par ts fs ord hsrc.1.1 (fun j => hsrc.2.1 _ (hsrc.1.2.1 j))
        _ _ hS _ hpad γ
      have hy' : y = fun j => (fs j) ((Relation.groupSeqOrd (fun k' : Fin 0 => k'.elim0) ord
          (q.evaluatePlain D (Fin.append par γ)) (fun k' : Fin 0 => k'.elim0)).map
            (fun v => (ts j).eval v (Fin.append par γ))) :=
        List.mem_singleton.mp (Multiset.mem_coe.mp hy)
      have hrow : Multiset.Mem ((scalarRaw (envOf (part f 3) cnt k (cutOf (part f 4) S
            (cutCore cnt (part f 1) q))) (part f 5) ts fs q).evaluatePlain D γ)
          (Fin.append (descEnc (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1)
            q)).evaluatePlain D γ)) par) y) := by
        rw [evaluatePlain_scalarRaw _ (part f 5) ts fs q (henvNM _ (hfr _)).2.1
          (noMention_sym _ (henvNM _ (hfr _)) _ q (hfr _))]
        refine Multiset.mem_of_mem_filter (p := fun x => (fun i => x (Fin.castAdd n i)
          : Tuple T (k * (7 + k))) = descEnc (valsU ((cutOf (part f 4) S
            (cutCore cnt (part f 1) q)).evaluatePlain D γ)) par) ?_
        rw [heq, hy']
        exact Multiset.mem_singleton_self _
      refine Or.inl (hCc (Finset.mem_union_right _ ?_))
      refine (valsU_colsQ _ _ _ (fun i => hrNM _ (hfr _)) D γ _).mpr ⟨_, hrow, i, ?_⟩
      exact Fin.append_right _ _ i
    | Win P O o w t g q hrr dist keep =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨hκ, hwq⟩ := hsrc.2.2.1
      subst hκ
      set S := (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) P O o w t g
        q hrr dist
        keep).allConsts
        with hSdef
      have hSq : q.allConsts ⊆ S := Finset.subset_union_right
      have hSC : S ⊆ C := hCk
      have hsrc' : SymSrc Θ q := ⟨hsrc.1.2.2.2.2, hsrc.2.1, hwq, hsrc.2.2.2⟩
      have hrNM : ∀ s, q.noMention s → (winRaw (hsql := sql_frame%) (envOf (part f 3) cnt k (cutOf
          (part f 4) S
          (cutCore cnt (part f 1) q))) (part f 5) P O o w t g q dist keep).noMention s := by
        intro s hs'
        unfold winRaw
        rw [AggQueryIn.noMention_allRegOf]
        exact noMention_symCut cnt f S q hs'
      rw [cutCore] at hCc
      rw [valsU_u2 (part f 0) (cutCore cnt (part f 1) q) (colsQ (part f 2) (winRaw (envOf (part f 3)
        cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) (part f 5) P O o w t g q dist keep)
        (fun _ : Fin 1 => Fin.last _)) (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_colsQ _ _ _ (hrNM _ (hfr _)))] at hCc
      have hC' : CutOK cnt (part f 1) q C D γ :=
        ⟨hCn, hCa, hSq.trans hSC, fun a ha => hCc (Finset.mem_union_left _ ha)⟩
      obtain ⟨hcl, -⟩ := ih (part f 1) q hs hU.2 hsrc' (fun i => hfr _) C D γ hC' par
      have hkeepC : ∀ φ, keep = some φ → ∀ a ∈ φ.consts, a ∈ S := by
        intro φ hφ a ha
        refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        rw [hφ]; exact ha
      refine ⟨fun _ hset => ⟨hcl rfl hset, fun φ hφ a ha => Or.inl (hSC (hkeepC φ hφ a ha)),
        fun y hy => ?_⟩, fun s m hl => absurd hl hnil⟩
      obtain ⟨hS, hG, hSC', -, -⟩ := hsym q S (part f 5) (fun i => hfr _) hs hU.2 hsrc'
        (fun i => hfr i) hSq hset
      have hf : (if dist then g.distinct else g).ReadsCount := by
        have := hsrc.1.2.1
        cases dist
        · exact hsrc.2.1 _ this
        · exact hsrc.2.1 _ this
      have hkeep : ∀ φ, keep = some φ → φ.noFun = true
          ∧ ∀ a ∈ φ.consts, CG (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1)
            q)).evaluatePlain D γ)) a :=
        fun φ hφ => ⟨by have := hsrc.1.2.2.1; rw [hφ] at this; exact this,
          fun a ha => Or.inl (hSC' (hkeepC φ hφ a ha))⟩
      have hsl := slice_eq_map_rowEnc hS
      have hy' : Multiset.Mem (Multiset.map (fun u => (Fin.snoc u (ValueFrame.windowValueOpt P O o
          w t
          (if dist then g.distinct else g) keep (q.evaluatePlain D (Fin.append par γ))
            u (Fin.append par γ)) : Tuple T _)) (q.evaluatePlain D (Fin.append par γ))) y := by
        have := hy
        simp only [AggQueryIn.evaluatePlain, ColKind.readTuple_allReg, Multiset.map_id'] at this
        exact this
      obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hy'
      have hwv := windowValue_slice par P O o w hsrc.1.2.2.2.1 t hsrc.1.1 hf keep hkeep hsl hG hu
          (expandSpec o) γ
      have hrin : Multiset.Mem ((sym (envOf (part f 3) cnt k (cutOf (part f 4) S
          (cutCore cnt (part f 1) q))) (part f 5) q).evaluatePlain D γ)
          (rowEnc (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1) q)).evaluatePlain D γ))
          par u) := by
        refine Multiset.mem_of_mem_filter (p := fun r => descP (P := 0) r = descEnc
          (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1) q)).evaluatePlain D γ)) par) ?_
        rw [hsl]
        exact Multiset.mem_map_of_mem _ hu
      have hrow : Multiset.Mem ((winRaw (hsql := sql_frame%) (envOf (part f 3) cnt k (cutOf (part
          f 4) S
            (cutCore cnt (part f 1) q))) (part f 5) P O o w t g q dist keep).evaluatePlain D γ)
          (Fin.snoc (rowEnc (valsU ((cutOf (part f 4) S (cutCore cnt (part f 1) q)).evaluatePlain
            D γ)) par u) (ValueFrame.windowValueOpt P O o w t (if dist then g.distinct else g) keep
              (q.evaluatePlain D (Fin.append par γ)) u (Fin.append par γ))) := by
        rw [evaluatePlain_winRaw, ← hwv]
        exact Multiset.mem_map_of_mem _ hrin
      refine Or.inl (hCc (Finset.mem_union_right _ ?_))
      refine (valsU_colsQ _ _ _ (fun i => hrNM _ (hfr _)) D γ _).mpr ⟨_, hrow, 0, ?_⟩
      simp only [Fin.snoc_last]

/-! ## The table of a query -/

/-- **The environment of a query's table**: built from the query's cut. -/
noncomputable def tabEnv (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) : SymEnv T k c :=
  envOf (part f 0) cnt k (cutQ cnt (part f 1) q)

/-- **The table of a query**: its symbolic evaluation relative to its
cut, the encodings of its rows at every type of parameter row. -/
noncomputable def tabQ (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) : AggQueryIn T c ((k + n) * (7 + k)) (ColKind.allReg _) :=
  sym (tabEnv cnt f q) (part f 2) q

theorem noMention_cutQ (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) {s : String} (hs : q.noMention s) :
    (cutQ cnt f q).noMention s :=
  noMention_cutOf _ _ (noMention_cutCore cnt _ _ q le_rfl hs)

theorem envNoMention_tabEnv (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) {s : String} (hs : q.noMention s) :
    EnvNoMention (tabEnv cnt f q) s :=
  envNoMention_envOf _ cnt k _ (noMention_cutQ cnt _ q hs)

theorem noMention_tabQ (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) {s : String} (hs : q.noMention s) : (tabQ cnt f q).noMention s :=
  noMention_sym _ (envNoMention_tabEnv cnt f q hs) _ q hs

/-- **The table holds, under each parameter row's descriptor, the
encodings of the rows the query computes at that row**, wherever the
query settles. -/
theorem tabQ_correct (Θ : Set (SeqAggFunc T)) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T (k + c) n κ)
    (hU : q.usesOnly basisProdOps) (hsrc : SymSrc Θ q)
    (hf : ∀ i, q.noMention (f i)) (D : Database T) (γ : Fin c → T) (par : Fin k → T)
    (hset : q.SettlesAt D (Fin.append par γ)) :
    SliceIs (P := 0) (cutAt (tabEnv cnt f q) D γ) par ((tabQ cnt f q).evaluatePlain D γ)
      ((q.evaluatePlain D (Fin.append par γ) : Multiset (Tuple T n)).map (fun v => (v, Fin.elim0)))
    ∧ (∀ v, Multiset.Mem (q.evaluatePlain D (Fin.append par γ)) v → ∀ i,
        GoodVal (C := cutAt (tabEnv cnt f q) D γ) par (v i)) := by
  have hcore : ∀ i, (cutCore cnt (part (part f 1) 1) q).noMention (part (part f 1) 0 i) :=
    fun i => noMention_cutCore cnt _ _ q le_rfl (hf _)
  have facts := mem_cutOf (part (part f 1) 0) q.allConsts (cutCore cnt (part (part f 1) 1) q)
    hcore D γ
  have hgood := (good_cutCore Θ hc _ (part (part f 1) 1) q le_rfl hU hsrc (fun i => hf _)
    (cutAt (tabEnv cnt f q) D γ) D γ ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2⟩ par).1 rfl hset
  have henv := envOK_envOf (part f 0) hc k (cutQ cnt (part f 1) q)
    (fun i => noMention_cutQ cnt _ q (hf _)) D γ facts.1
  exact (sym_correct_aux _ Θ _ (part f 2) q le_rfl hsrc
    (fun i => ⟨hf _, envNoMention_tabEnv cnt f q (hf _)⟩) D γ par henv
    (fun j => Or.inl (facts.2.1 j))).1 rfl hgood hset

end Sym
