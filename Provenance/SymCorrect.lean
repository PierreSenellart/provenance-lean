import Provenance.SymTab
import Provenance.RoundBound

/-!
# The symbolic evaluation is correct

Under the descriptor of a parameter row, the symbolic evaluation of a query
holds the encodings of the rows the query computes at that row
(`Sym.sym_correct`), provided the environment is sound (`Sym.EnvOK`: the
descriptors without repetition and every parameter row's among them, and
enough counters for every bag recursion) and every value the evaluation
compares or groups is good (`Sym.Good`): a value of the cut, the null, or a
component of the parameter row. What makes the second hold is the cut, a
separate matter.
-/

variable {T : Type} [ValueType T]

namespace Sym

/-! ## What the evaluation asks of the query and of the values -/

/-- **Every window reads an all-regular input**, which is what the windows
the passes build do. -/
def winAllReg : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => winAllReg q
  | _, _, _, _, .Sel _ q _ => winAllReg q
  | _, _, _, _, .Prod q₁ q₂ => winAllReg q₁ ∧ winAllReg q₂
  | _, _, _, _, .Apply q₁ q₂ => winAllReg q₁ ∧ winAllReg q₂
  | _, _, _, _, .Sum q₁ q₂ => winAllReg q₁ ∧ winAllReg q₂
  | _, _, _, _, .Dedup q => winAllReg q
  | _, _, _, _, .Diff q₁ q₂ => winAllReg q₁ ∧ winAllReg q₂
  | _, _, _, _, .Explode _ _ q => winAllReg q
  | _, _, _, _, .Mu _ q₀ q₁ => winAllReg q₀ ∧ winAllReg q₁
  | _, _, _, _, .MuSet _ q₀ q₁ => winAllReg q₀ ∧ winAllReg q₁
  | _, _, _, _, .Gamma _ _ _ q _ _ => winAllReg q
  | _, _, _, _, .GammaScalar _ _ q _ => winAllReg q
  | _, _, _, _, .GammaNest _ _ _ _ q => winAllReg q
  | _, _, _, _, .ProvSum _ _ _ q => winAllReg q
  | _, _, _, _, .Retag _ q => winAllReg q
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => winAllReg q
  | _, _, _, _, @AggQueryIn.Win _ _ n _ _ κ _ _ _ _ _ _ _ _ q _ _ _ =>
      κ = ColKind.allReg n ∧ winAllReg q
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => winAllReg q

/-- **Every value the evaluation of a query compares, groups or emits from
nowhere is a value of the cut** (`CG`): the values of the relations it
reads, the constants, the values its aggregations compute; and under a
recursion, at every round. -/
def Good (G : T → Prop) : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Database T → (Fin c → T) → Prop
  | _, _, _, _, q@(.Rel _ _), D, γ =>
      ∀ v, Multiset.Mem (q.evaluatePlain D γ) v → ∀ i, G (v i)
  | _, _, _, _, .Hole _ _ _, _, _ => True
  | _, _, _, _, .Param pv _, _, _ => ∀ j a, pv j = .inl a → G a
  | _, _, _, _, .Empty, _, _ => True
  | _, _, _, _, .Proj ps q, D, γ => (∀ j, ∀ a ∈ (ps j).consts, G a) ∧ Good G q D γ
  | _, _, _, _, .Sel φ q _, D, γ => (∀ a ∈ φ.consts, G a) ∧ Good G q D γ
  | _, _, _, _, .Prod q₁ q₂, D, γ => Good G q₁ D γ ∧ Good G q₂ D γ
  | _, _, _, _, .Apply _ _, _, _ => False
  | _, _, _, _, .Sum _ _, _, _ => False
  | _, _, _, _, .Dedup _, _, _ => False
  | _, _, _, _, .Diff _ _, _, _ => False
  | _, _, _, _, .Explode _ _ q, D, γ => Good G q D γ
  | _, _, _, _, .Mu s q₀ q₁, D, γ => Good G q₀ D γ
      ∧ ∀ j, Good G q₁ (D.assign s ((fun X => q₁.evaluatePlain (D.assign s X) γ)^[j]
          (q₀.evaluatePlain D γ))) γ
  | _, _, _, _, .MuSet _ _ _, _, _ => False
  | _, _, _, _, .Gamma (n₁ := n₁) (n₂ := n₂) (lab := lab) (rd := rd) is ts fs q' keep ord, D, γ =>
      Good G q' D γ ∧ (∀ j φ, keep j = some φ → ∀ a ∈ φ.consts, G a)
      ∧ ∀ y, Multiset.Mem ((AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q' keep
        ord).evaluatePlain D γ) y → ∀ j : Fin n₂, G (y (Fin.natAdd n₁ j))
  | _, _, _, _, q@(.GammaScalar _ _ q' _), D, γ => Good G q' D γ
      ∧ ∀ y, Multiset.Mem (q.evaluatePlain D γ) y → ∀ i, G (y i)
  | _, _, _, _, .GammaNest (n₁ := n₁) (lab := lab) (rd := rd) is his p g q', D, γ =>
      Good G q' D γ ∧ (∀ a ∈ p.consts, G a)
      ∧ ∀ y, Multiset.Mem ((AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p g
        q').evaluatePlain D γ) y → G (y (Fin.natAdd n₁ (0 : Fin 1)))
  | _, _, _, _, .ProvSum _ _ _ _, _, _ => False
  | _, _, _, _, .Retag _ q, D, γ => Good G q D γ
  | _, _, _, _, .GammaTok _ _ _ _ _ _ _, _, _ => False
  | _, _, _, _, q@(.Win _ _ _ _ _ _ q' _ _ keep), D, γ => Good G q' D γ
      ∧ (∀ φ, keep = some φ → ∀ a ∈ φ.consts, G a)
      ∧ ∀ y, Multiset.Mem (q.evaluatePlain D γ) y → G (y (Fin.last _))
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ _ _, _, _ => False

/-- The cut at an instance, as a finite set of values. -/
noncomputable def cutAt {k c : ℕ} (env : SymEnv T k c) (D : Database T) (γ : Fin c → T) :
    Finset T :=
  ((env.CQ.evaluatePlain D γ : Multiset (Tuple T 1)).map (fun y => y 0)).toFinset

/-- **The environment is sound at an instance**: the descriptors are listed
once each and hold every parameter row's, and every arity of a bag
recursion has a list of counters long enough for the rounds it can run. -/
def EnvOK {k c : ℕ} (env : SymEnv T k c) (D : Database T) (γ : Fin c → T) : Prop :=
  (env.Desc.evaluatePlain D γ : Multiset (Tuple T (k * (7 + k)))).Nodup
    ∧ (∀ par : Fin k → T, Multiset.Mem (env.Desc.evaluatePlain D γ) (descEnc (cutAt env D γ) par))
    ∧ ∀ n, ∃ cs : List (Tuple T (env.ctrK n)), cs.Nodup ∧ ∃ h : 0 < cs.length,
        LE.le (((cutAt env D γ).card + k + 1) ^ n) cs.length
        ∧ (env.Lq n).evaluatePlain D γ = ({cs[0]'h} : Multiset _)
        ∧ (env.Sq n).evaluatePlain D γ = (succRel cs : Multiset _)

/-! ## The relations the symbolic evaluation names -/

/-- The environment names no relation `s`. -/
def EnvNoMention {k c : ℕ} (env : SymEnv T k c) (s : String) : Prop :=
  env.CQ.noMention s ∧ env.Desc.noMention s ∧ ∀ n, (env.Lq n).noMention s ∧ (env.Sq n).noMention s

omit [ValueType T] in
theorem noMention_prodR {c a b : ℕ} {l₁ l₂ : List (String × ℕ)} {s : String}
    (q₁ : AggQueryIn T c a (ColKind.allReg a) l₁) (q₂ : AggQueryIn T c b (ColKind.allReg b) l₂) :
    (prodR q₁ q₂).noMention s ↔ q₁.noMention s ∧ q₂.noMention s := by
  rw [prodR, AggQueryIn.noMention_castKind]; exact Iff.rfl

/-- **The symbolic evaluation names only the relations the query and the
environment name.** -/
theorem noMention_sym_aux {k c : ℕ} (env : SymEnv T k c) {s : String}
    (henv : EnvNoMention env s) :
    ∀ (N : ℕ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
      (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N → q.noMention s →
      (sym env f q).noMention s ∧ ∀ P s' m, (symB env f P s' m q).noMention s := by
  have hjunk : ∀ {N M : ℕ} (s' : String), (junkB (T := T) (c := c) N M s').noMention s := by
    intro N M s'
    rw [junkB, AggQueryIn.noMention_castKind]
    exact trivial
  have hempty : ∀ N, (AggQueryIn.emptyRel (T := T) (c := c) N).noMention s :=
    fun N => AggQueryIn.noMention_emptyRel N s
  intro N
  induction N with
  | zero =>
    intro f n κ l q hq hm
    cases q <;> simp at hq
  | succ N ih =>
    intro f n κ l q hq hm
    cases q with
    | Rel n s' =>
      refine ⟨?_, fun P s' m => by rw [symB]; exact hjunk _⟩
      rw [sym, AggQueryIn.noMention_castKind]
      exact (noMention_prodR _ _).mpr ⟨henv.2.1, hm⟩
    | Hole n s'' κ =>
      refine ⟨by rw [sym]; exact hempty _, fun P s' m => ?_⟩
      rw [symB]
      split
      · rename_i h; subst h; exact trivial
      · exact hjunk _
    | Param pv ρ =>
      refine ⟨?_, fun P s' m => by rw [symB]; exact hjunk _⟩
      rw [sym, AggQueryIn.noMention_castKind]
      exact henv.2.1
    | Empty => exact ⟨by rw [sym]; exact hempty _, fun P s' m => by rw [symB]; exact hjunk _⟩
    | Proj ps q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨h₁, h₂⟩ := ih f q hs hm
      refine ⟨?_, fun P s' m => ?_⟩
      · rw [sym, AggQueryIn.noMention_castKind]; exact h₁
      · rw [symB, AggQueryIn.noMention_castKind]; exact h₂ P s' m
    | Sel φ q hφ =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨h₁, h₂⟩ := ih f q hs hm
      exact ⟨by rw [sym]; exact h₁, fun P s' m => by rw [symB]; exact h₂ P s' m⟩
    | Prod q₁ q₂ =>
      have hs₁ : sizeOf q₁ ≤ N := by simp at hq; omega
      have hs₂ : sizeOf q₂ ≤ N := by simp at hq; omega
      obtain ⟨h₁, h₁'⟩ := ih (AggQueryIn.tri f 1) q₁ hs₁ hm.1
      obtain ⟨h₂, h₂'⟩ := ih (AggQueryIn.tri f 2) q₂ hs₂ hm.2
      refine ⟨?_, fun P s' m => ?_⟩
      · rw [sym, AggQueryIn.noMention_castKind]
        exact (noMention_prodR _ _).mpr ⟨h₁, h₂⟩
      · rw [symB]
        split
        · rw [AggQueryIn.noMention_castKind]
          exact (noMention_prodR _ _).mpr ⟨h₁, h₂' P s' m⟩
        · rw [AggQueryIn.noMention_castKind]
          exact (noMention_prodR _ _).mpr ⟨h₁' P s' m, h₂⟩
    | Apply q₁ q₂ =>
      exact ⟨by rw [sym]; exact hempty _, fun P s' m => by rw [symB]; exact hjunk _⟩
    | Sum q₁ q₂ =>
      exact ⟨by rw [sym]; exact hempty _, fun P s' m => by rw [symB]; exact hjunk _⟩
    | Dedup q =>
      exact ⟨by rw [sym]; exact hempty _, fun P s' m => by rw [symB]; exact hjunk _⟩
    | Diff q₁ q₂ =>
      exact ⟨by rw [sym]; exact hempty _, fun P s' m => by rw [symB]; exact hjunk _⟩
    | Explode i h q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨h₁, h₂⟩ := ih f q hs hm
      exact ⟨by rw [sym]; exact h₁, fun P s' m => by rw [symB]; exact h₂ P s' m⟩
    | Retag h q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨h₁, h₂⟩ := ih f q hs hm
      exact ⟨by rw [sym]; exact h₁, fun P s' m => by rw [symB]; exact h₂ P s' m⟩
    | Mu s'' q₀ q₁ =>
      have hs₀ : sizeOf q₀ ≤ N := by simp at hq; omega
      have hs₁ : sizeOf q₁ ≤ N := by simp at hq; omega
      obtain ⟨h₀, -⟩ := ih (AggQueryIn.tri f 1) q₀ hs₀ hm.1
      obtain ⟨-, h₁⟩ := ih (AggQueryIn.tri f 2) q₁ hs₁ hm.2
      refine ⟨?_, fun P s' m => by rw [symB]; exact hjunk _⟩
      rw [sym, symMuQ, AggQueryIn.noMention_castKind]
      refine ⟨(noMention_prodR _ _).mpr ⟨h₀, (henv.2.2 _).1⟩, ?_⟩
      rw [stepQ, AggQueryIn.noMention_castKind]
      exact (noMention_prodR _ _).mpr ⟨h₁ _ _ _, (henv.2.2 _).2⟩
    | MuSet s'' q₀ q₁ =>
      exact ⟨by rw [sym]; exact hempty _, fun P s' m => by rw [symB]; exact hjunk _⟩
    | Gamma is ts fs q keep ord =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨h₁, -⟩ := ih f q hs hm
      refine ⟨?_, fun P s' m => by rw [symB]; exact hjunk _⟩
      rw [sym, AggQueryIn.noMention_castKind]
      show (AggQueryIn.allRegOf _).noMention s
      rw [AggQueryIn.noMention_allRegOf]
      exact h₁
    | GammaScalar ts fs q ord =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨h₁, -⟩ := ih (AggQueryIn.tri f 1) q hs hm
      refine ⟨?_, fun P s' m => by rw [symB]; exact hjunk _⟩
      rw [sym, AggQueryIn.noMention_castKind]
      show (AggQueryIn.allRegOf _).noMention s
      rw [AggQueryIn.noMention_allRegOf]
      refine AggQueryIn.noMention_sumByMuX _ _ _ _ ?_ ?_
      · rw [AggQueryIn.noMention_castKind]; exact henv.2.1
      · rw [AggQueryIn.noMention_castKind]; exact h₁
    | GammaNest is his p g q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨h₁, -⟩ := ih f q hs hm
      refine ⟨?_, fun P s' m => by rw [symB]; exact hjunk _⟩
      rw [sym, AggQueryIn.noMention_castKind]
      show (AggQueryIn.allRegOf _).noMention s
      rw [AggQueryIn.noMention_allRegOf]
      exact h₁
    | GammaTok is his ts fs a q keep =>
      exact ⟨by rw [sym]; exact hempty _, fun P s' m => by rw [symB]; exact hjunk _⟩
    | ProvSum is his t q =>
      exact ⟨by rw [sym]; exact hempty _, fun P s' m => by rw [symB]; exact hjunk _⟩
    | Win P O o w t g q hrr dist keep =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨h₁, -⟩ := ih f q hs hm
      refine ⟨?_, fun P s' m => by rw [symB]; exact hjunk _⟩
      rw [sym, AggQueryIn.noMention_castKind]
      show (AggQueryIn.allRegOf _).noMention s
      rw [AggQueryIn.noMention_allRegOf]
      exact h₁
    | WinExpr P O o ws ts fs g q keeps =>
      exact ⟨by rw [sym]; exact hempty _, fun P s' m => by rw [symB]; exact hjunk _⟩

/-! ## A symbolic recursive term keeps each row's further columns -/

/-- The rows of the empty recursive term: none. -/
theorem evaluatePlain_junkB {c N M : ℕ} (s : String) (D : Database T) (γ : Fin c → T) :
    (junkB (T := T) (c := c) N M s).evaluatePlain D γ = 0 := by
  rw [junkB, AggQueryIn.evaluatePlain_castKind]
  show Multiset.map _ (Multiset.filter _ _) = 0
  rw [Multiset.filter_eq_nil.mpr (fun y _ h => by
    have : CompOp.syneq.eval3 (0 : T) ValueType.nonzero = Kleene.true := h
    rw [CompOp.syneq_eval3_eq_true_iff] at this
    exact ValueType.nonzero_ne_zero this.symm)]
  rfl

theorem descP_symProjSA_suf {k c n m P : ℕ} (srcs : Fin m → CS T k c n) (γ : Fin c → T)
    (r : Tuple T ((k + n) * (7 + k) + P)) :
    suf (N := (k + m) * (7 + k)) (fun x => (symProjSA P srcs x).eval r γ) = suf r := by
  funext z
  show (symProjSA P srcs (Fin.natAdd _ z)).eval r γ = r (Fin.natAdd _ z)
  rw [symProjSA, Fin.addCases_right]
  rfl

/-- **Every row a symbolic recursive term emits carries the further columns
of a row it reads.** -/
theorem symB_pres_aux {k c : ℕ} (env : SymEnv T k c) :
    ∀ (N : ℕ) (f : ℕ → String) (P : ℕ) (s : String) (m : ℕ) {n : ℕ} {κ : Fin n → ColKind}
      {l : List (String × ℕ)} (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N →
      ∀ (D : Database T) (γ : Fin c → T) (Y : Multiset (Tuple T ((k + m) * (7 + k) + P)))
        (y : Tuple T ((k + n) * (7 + k) + P)),
        Multiset.Mem ((symB env f P s m q).evaluatePlain (D.assign s Y) γ) y →
        ∃ x ∈ Y, suf (N := (k + m) * (7 + k)) x = suf (N := (k + n) * (7 + k)) y := by
  intro N
  induction N with
  | zero =>
    intro f P s m n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro f P s m n κ l q hq D γ Y y hy
    have hj : ∀ {N' M' : ℕ} (y' : Tuple T N'), ¬ Multiset.Mem ((junkB (T := T) (c := c) N' M'
        s).evaluatePlain
        (D.assign s Y) γ) y' := fun y' h => by
      rw [evaluatePlain_junkB] at h; exact Multiset.notMem_zero _ h
    cases q with
    | Hole n' s' κ' =>
      rw [symB] at hy
      split at hy
      · rename_i h
        subst h
        refine ⟨y, ?_, rfl⟩
        have : ((AggQueryIn.Hole ((k + n) * (7 + k) + P) s : AggQueryIn T c _ _ _).evaluatePlain
            (D.assign s Y) γ : Multiset (Tuple T _)) = Y := by
          simp only [AggQueryIn.evaluatePlain, Database.find_assign]
        rw [this] at hy
        exact hy
      · exact absurd hy (hj _)
    | Proj ps q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [symB, AggQueryIn.evaluatePlain_castKind] at hy
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
      obtain ⟨x, hx, hxr⟩ := ih f P s m q hs D γ Y r hr
      refine ⟨x, hx, ?_⟩
      rw [hxr]
      show suf r = suf (fun j => (projSA (symProjSA P (fun j => projCS (ps j))) j).evalPlain r γ)
      simp only [evalPlain_projSA]
      rw [descP_symProjSA_suf]
    | Sel φ q hφ =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [symB] at hy
      exact ih f P s m q hs D γ Y y (Multiset.mem_of_mem_filter hy)
    | Prod q₁ q₂ =>
      rename_i n₁ n₂ κ₁ κ₂ l₁ l₂
      have hs₁ : sizeOf q₁ ≤ N := by simp at hq; omega
      have hs₂ : sizeOf q₂ ≤ N := by simp at hq; omega
      rw [symB] at hy
      split at hy
      · rw [AggQueryIn.evaluatePlain_castKind] at hy
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
        have hw' := Multiset.mem_of_mem_filter hw
        rw [evaluatePlain_prodR] at hw'
        obtain ⟨r₁, -, hw'⟩ := Multiset.mem_bind.mp hw'
        obtain ⟨r₂, hr₂, rfl⟩ := Multiset.mem_map.mp hw'
        obtain ⟨x, hx, hxr⟩ := ih (AggQueryIn.tri f 2) P s m q₂ hs₂ D γ Y r₂ hr₂
        refine ⟨x, hx, ?_⟩
        rw [hxr]
        funext z
        show r₂ (Fin.natAdd _ z) = (projSA (joinRSA 0 P) (Fin.natAdd _ z)).evalPlain _ γ
        rw [evalPlain_projSA, joinRSA, Fin.addCases_right]
        show _ = Fin.append r₁ r₂ (Fin.natAdd _ (Fin.natAdd _ z))
        rw [Fin.append_right]
      · rw [AggQueryIn.evaluatePlain_castKind] at hy
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
        have hw' := Multiset.mem_of_mem_filter hw
        rw [evaluatePlain_prodR] at hw'
        obtain ⟨r₁, hr₁, hw'⟩ := Multiset.mem_bind.mp hw'
        obtain ⟨r₂, -, rfl⟩ := Multiset.mem_map.mp hw'
        obtain ⟨x, hx, hxr⟩ := ih (AggQueryIn.tri f 1) P s m q₁ hs₁ D γ Y r₁ hr₁
        refine ⟨x, hx, ?_⟩
        rw [hxr]
        funext z
        show r₁ (Fin.natAdd _ z) = (projSA (joinLSA P 0) (Fin.natAdd _ z)).evalPlain _ γ
        rw [evalPlain_projSA, joinLSA, Fin.addCases_right]
        show _ = Fin.append r₁ r₂ (Fin.castAdd _ (Fin.natAdd _ z))
        rw [Fin.append_left]
    | Explode i h q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [symB] at hy
      exact ih f P s m q hs D γ Y y hy
    | Retag h q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [symB] at hy
      exact ih f P s m q hs D γ Y y hy
    | _ => rw [symB] at hy; exact absurd hy (hj _)

/-! ## The correctness of the symbolic evaluation -/

/-- **The environment reads the same off an instance with a recursive name
bound**, naming no such relation. -/
theorem envOK_assign {k c : ℕ} (env : SymEnv T k c) {s : String} (henv : EnvNoMention env s)
    {m : ℕ} (X : Relation T m) (D : Database T) (γ : Fin c → T) :
    cutAt env (D.assign s X) γ = cutAt env D γ ∧ (EnvOK env D γ → EnvOK env (D.assign s X) γ) := by
  have hcut : cutAt env (D.assign s X) γ = cutAt env D γ := by
    unfold cutAt
    rw [AggQueryIn.evaluatePlain_assign_of_noMention X env.CQ henv.1 D γ]
  refine ⟨hcut, fun ⟨hnd, hdesc, hctr⟩ => ⟨?_, fun par => ?_, fun n => ?_⟩⟩
  · rw [AggQueryIn.evaluatePlain_assign_of_noMention X env.Desc henv.2.1 D γ]; exact hnd
  · rw [AggQueryIn.evaluatePlain_assign_of_noMention X env.Desc henv.2.1 D γ, hcut]
    exact hdesc par
  · obtain ⟨cs, hcs, h0, hle, hL, hS⟩ := hctr n
    refine ⟨cs, hcs, h0, hcut ▸ hle, ?_, ?_⟩
    · rw [AggQueryIn.evaluatePlain_assign_of_noMention X (env.Lq n) (henv.2.2 n).1 D γ]; exact hL
    · rw [AggQueryIn.evaluatePlain_assign_of_noMention X (env.Sq n) (henv.2.2 n).2 D γ]; exact hS

/-- **A projection by arguments, read.** -/
theorem evaluatePlain_projSA {c N M : ℕ} {l : List (String × ℕ)}
    (F : Fin M → SA T c N) (q : AggQueryIn T c N (ColKind.allReg N) l)
    (h : (fun j => (projSA F j).kind) = ColKind.allReg M) (D : Database T) (γ : Fin c → T) :
    ((AggQueryIn.Proj (projSA F) q).castKind h).evaluatePlain D γ
      = (q.evaluatePlain D γ : Multiset (Tuple T N)).map (fun x i => (F i).eval x γ) := by
  rw [AggQueryIn.evaluatePlain_castKind]
  show Multiset.map _ _ = _
  exact Multiset.map_congr rfl (fun x _ => funext fun i => Sym.evalPlain_projSA F x γ i)

omit [ValueType T] in
theorem pvCS_val {k c m : ℕ} (pv : Fin m → T ⊕ Fin (k + c)) (par : Fin k → T) (γ : Fin c → T) :
    (fun j => (pvCS pv j).val par γ (Fin.elim0 : Tuple T 0))
      = (fun j => _root_.Sum.elim id (Fin.append par γ) (pv j)) := by
  funext j
  unfold pvCS
  cases pv j with
  | inl a => rfl
  | inr o =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) o
    · simp only [Fin.addCases_left, CS.val, _root_.Sum.elim_inr, Fin.append_left]
    · simp only [Fin.addCases_right, CS.val, _root_.Sum.elim_inr, Fin.append_right]

omit [ValueType T] in
theorem pvCS_const {k c m : ℕ} (pv : Fin m → T ⊕ Fin (k + c)) (j : Fin m) {a : T}
    (h : pvCS pv j = .const a) : pv j = .inl a := by
  unfold pvCS at h
  cases hp : pv j with
  | inl b => rw [hp] at h; cases h; rfl
  | inr o =>
    rw [hp] at h
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) o h
    · simp at hi
    · simp at hi

/-- The value of a source is good where the row is. -/
theorem goodVal_cs {k c n : ℕ} {C : Finset T} (s : CS T k c n) (par : Fin k → T) (γ : Fin c → T)
    (v : Tuple T n) (hv : ∀ i, GoodVal (C := C) par (v i)) (hamb : ∀ j, CG C (γ j))
    (hc : ∀ a, s = .const a → CG C a) : GoodVal (C := C) par (s.val par γ v) :=
  goodVal_val s par γ v hv hamb hc

/-- The padding row a scalar aggregation adds under a descriptor: the
descriptor's cells, then constant cells. -/
def padRow {k : ℕ} (m : ℕ) (d : Tuple T (k * (7 + k))) : Tuple T ((k + m) * (7 + k)) :=
  fun x => Fin.addCases (motive := fun _ => T) (fun i₀ => d (ci i₀ (finProdFinEquiv.symm x).2))
    (fun _ => 0) (finProdFinEquiv.symm x).1

theorem eval_padSA {k c : ℕ} (m : ℕ) (d : Tuple T (k * (7 + k))) (γ : Fin c → T) :
    (fun i => (padSA (T := T) (c := c) m i).eval d γ)
      = Fin.append (padRow m d) (fun _ : Fin 1 => (0 : T)) := by
  funext x
  refine Fin.addCases (fun y => ?_) (fun z => ?_) x
  · rw [Fin.append_left]
    show (padSA m (Fin.castSucc y)).eval d γ = _
    unfold padSA padRow
    rw [Fin.lastCases_castSucc]
    generalize finProdFinEquiv.symm y = ij
    obtain ⟨i, j⟩ := ij
    refine Fin.addCases (fun i₀ => ?_) (fun t => ?_) i
    · simp only [Fin.addCases_left, SA.eval]
    · simp only [Fin.addCases_right, SA.eval]
  · rw [Fin.append_right, Subsingleton.elim z 0]
    show (padSA m (Fin.last _)).eval d γ = 0
    unfold padSA
    rw [Fin.lastCases_last]
    rfl

theorem descP_padRow {k : ℕ} (m : ℕ) (d : Tuple T (k * (7 + k))) :
    descP (n := m) (P := 0) (padRow m d) = d := by
  funext x
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  show padRow m d (cc 0 (Fin.castAdd m (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = d (finProdFinEquiv (i, j))
  rw [Equiv.symm_apply_apply]
  show Fin.addCases (motive := fun _ => T) _ _
    (finProdFinEquiv.symm (finProdFinEquiv (Fin.castAdd m i, j))).1 = _
  rw [Equiv.symm_apply_apply, Fin.addCases_left]
  show d (ci i (finProdFinEquiv.symm (finProdFinEquiv (Fin.castAdd m i, j))).2) = _
  rw [Equiv.symm_apply_apply]
  rfl

omit [ValueType T] in
theorem eval_tagSA {c N : ℕ} (a : T) (r : Tuple T N) (γ : Fin c → T) :
    (fun i => (tagSA (c := c) a i).eval r γ) = Fin.append r (fun _ : Fin 1 => a) := by
  funext x
  refine Fin.addCases (fun y => ?_) (fun z => ?_) x
  · rw [Fin.append_left]
    show (tagSA a (Fin.castSucc y)).eval r γ = _
    unfold tagSA
    rw [Fin.lastCases_castSucc]
    rfl
  · rw [Fin.append_right, Subsingleton.elim z 0]
    show (tagSA a (Fin.last _)).eval r γ = a
    unfold tagSA
    rw [Fin.lastCases_last]
    rfl

/-- The encodings of a relation are their own slice. -/
theorem sliceIs_encAll {k n P : ℕ} (C : Finset T) (par : Fin k → T)
    (R : Multiset (Tuple T n × Tuple T P)) : SliceIs C par (encAll C par R) R := by
  unfold SliceIs slice
  exact Multiset.filter_eq_self.mpr (fun r hr => by
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hr
    exact descP_rowEncP C par x.1 x.2)

/-- The good values, as a finite set. -/
noncomputable def goodSet {k : ℕ} (C : Finset T) (par : Fin k → T) : Finset T :=
  Union.union (Union.union C (Finset.univ.image par)) (ValueType.nullVal : Option T).toFinset

theorem mem_goodSet {k : ℕ} {C : Finset T} {par : Fin k → T} {b : T}
    (h : GoodVal (C := C) par b) : b ∈ goodSet C par := by
  unfold goodSet
  rcases h with ⟨i, rfl⟩ | h | h
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ i)))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
  · exact Finset.mem_union_right _ (Option.mem_toFinset.mpr
      ((ValueType.isNull_iff_nullVal b).mp h))

theorem card_goodSet_le {k : ℕ} (C : Finset T) (par : Fin k → T) :
    LE.le (goodSet C par).card (C.card + k + 1) := by
  unfold goodSet
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · refine (Finset.card_union_le _ _).trans (Nat.add_le_add le_rfl ?_)
    exact Finset.card_image_le.trans (by simp)
  · rw [Option.card_toFinset]
    cases (ValueType.nullVal : Option T) <;> simp

/-- **What the symbolic evaluation asks of its input query**: a signature
whose aggregates count, windows over all-regular inputs, and restricted
recursions. -/
def SymSrc {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (Θ : Set (SeqAggFunc T))
    (q : AggQueryIn T c n κ l) : Prop :=
  q.inSig Θ ∧ (∀ g ∈ Θ, g.ReadsCount) ∧ winAllReg q ∧ q.hygienic

/-! ## Goodness depends on the instance only where the query reads it -/

/-- **Two instances agreeing where a query reads make it good alike.** -/
theorem good_congr_of_noMention (G : T → Prop) {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention s → ∀ {D D' : Database T}, Database.AgreeOff s l D D' →
      ∀ γ : Fin c → T, Good G q D γ ↔ Good G q D' γ := by
  have hassign : ∀ {D D' : Database T} (s' : String) {m : ℕ} (Y : Relation T m),
      Database.AgreeOff s [] D D' →
      Database.AgreeOff s [(s', m)] (D.assign s' Y) (D'.assign s' Y) :=
    fun s' _ Y h => Database.AgreeOff.assign s' Y h
  have hL : ∀ {l₁ l₂ : List (String × ℕ)} {D D' : Database T},
      Database.AgreeOff s (l₁ ++ l₂) D D' → Database.AgreeOff s l₁ D D' :=
    fun h => h.mono (fun _ hp => List.mem_append_left _ hp)
  have hR : ∀ {l₁ l₂ : List (String × ℕ)} {D D' : Database T},
      Database.AgreeOff s (l₁ ++ l₂) D D' → Database.AgreeOff s l₂ D D' :=
    fun h => h.mono (fun _ hp => List.mem_append_right _ hp)
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro hq D D' h γ
    show (∀ v, _ → _) ↔ (∀ v, _ → _)
    rw [AggQueryIn.evaluatePlain_congr_of_noMention _ hq h γ]
  | Hole n s' => intro _ _ _ _ _; exact Iff.rfl
  | Param pv ρ => intro _ _ _ _ _; exact Iff.rfl
  | Empty => intro _ _ _ _ _; exact Iff.rfl
  | Proj ps q ih => intro hq D D' h γ; exact and_congr Iff.rfl (ih hq h γ)
  | Sel φ q _ ih => intro hq D D' h γ; exact and_congr Iff.rfl (ih hq h γ)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq D D' h γ; exact and_congr (ih₁ hq.1 (hL h) γ) (ih₂ hq.2 (hR h) γ)
  | Apply q₁ q₂ _ _ => intro _ _ _ _ _; exact Iff.rfl
  | Sum q₁ q₂ _ _ => intro _ _ _ _ _; exact Iff.rfl
  | Dedup q _ => intro _ _ _ _ _; exact Iff.rfl
  | Diff q₁ q₂ _ _ => intro _ _ _ _ _; exact Iff.rfl
  | Explode k hk q ih => intro hq D D' h γ; exact ih hq h γ
  | Retag hk q ih => intro hq D D' h γ; exact ih hq h γ
  | Mu s' q₀ q₁ ih₀ ih₁ =>
    intro hq D D' h γ
    have hstep : (fun X => q₁.evaluatePlain (D.assign s' X) γ)
        = (fun X => q₁.evaluatePlain (D'.assign s' X) γ) :=
      funext fun X => AggQueryIn.evaluatePlain_congr_of_noMention _ hq.2 (hassign s' X h) γ
    have hbase := AggQueryIn.evaluatePlain_congr_of_noMention _ hq.1 h γ
    show (Good G q₀ D γ ∧ ∀ j, Good G q₁ (D.assign s' ((fun X => q₁.evaluatePlain (D.assign s' X)
        γ)^[j] (q₀.evaluatePlain D γ))) γ) ↔ (Good G q₀ D' γ ∧ ∀ j, Good G q₁ (D'.assign s'
          ((fun X => q₁.evaluatePlain (D'.assign s' X) γ)^[j] (q₀.evaluatePlain D' γ))) γ)
    rw [← hstep, ← hbase]
    exact and_congr (ih₀ hq.1 h γ) (forall_congr' fun j => ih₁ hq.2 (hassign s' _ h) γ)
  | MuSet s' q₀ q₁ _ _ => intro _ _ _ _ _; exact Iff.rfl
  | Gamma is ts fs q keep ord ih =>
    intro hq D D' h γ
    refine and_congr (ih hq h γ) (and_congr Iff.rfl ?_)
    rw [AggQueryIn.evaluatePlain_congr_of_noMention _ hq h γ]
  | GammaScalar ts fs q ord ih =>
    intro hq D D' h γ
    refine and_congr (ih hq h γ) ?_
    rw [AggQueryIn.evaluatePlain_congr_of_noMention _ hq h γ]
  | GammaNest is his p g q ih =>
    intro hq D D' h γ
    refine and_congr (ih hq h γ) (and_congr Iff.rfl ?_)
    rw [AggQueryIn.evaluatePlain_congr_of_noMention _ hq h γ]
  | ProvSum is his t q _ => intro _ _ _ _ _; exact Iff.rfl
  | GammaTok is his ts fs a q keep _ => intro _ _ _ _ _; exact Iff.rfl
  | Win P O o w t g q hrr dist keep ih =>
    intro hq D D' h γ
    refine and_congr (ih hq h γ) (and_congr Iff.rfl ?_)
    rw [AggQueryIn.evaluatePlain_congr_of_noMention _ hq h γ]
  | WinExpr P O o ws ts fs g q keeps _ => intro _ _ _ _ _; exact Iff.rfl

theorem good_assign_of_noMention (G : T → Prop) {s : String} {m : ℕ} (X : Relation T m)
    {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ) (hq : q.noMention s) (D : Database T)
    (γ : Fin c → T) : Good G q (D.assign s X) γ ↔ Good G q D γ :=
  good_congr_of_noMention G q hq
    (fun _k s' hs' =>
      Database.find_assign_of_ne s s' X D (fun hc => (hs'.resolve_right List.not_mem_nil) hc.2)) γ

/-- **The symbolic evaluation is correct**, in both modes: a closed query's
symbolic relation holds, under the descriptor of a parameter row, the
encodings of the rows the query computes there; a recursive term's maps a
round holding the encodings of a round to the encodings of the next. -/
theorem sym_correct_aux {k c : ℕ} (env : SymEnv T k c) (Θ : Set (SeqAggFunc T)) :
    ∀ (N : ℕ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
      (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N → SymSrc Θ q →
      (∀ i, q.noMention (f i) ∧ EnvNoMention env (f i)) →
      ∀ (D : Database T) (γ : Fin c → T) (par : Fin k → T), EnvOK env D γ →
        (∀ j, CG (cutAt env D γ) (γ j)) →
        (l = [] → Good (CG (cutAt env D γ)) q D (Fin.append par γ) →
          q.SettlesAt D (Fin.append par γ) →
          SliceIs (P := 0) (cutAt env D γ) par ((sym env f q).evaluatePlain D γ)
            ((q.evaluatePlain D (Fin.append par γ) : Multiset (Tuple T n)).map
              (fun v => (v, Fin.elim0)))
          ∧ ∀ v, Multiset.Mem (q.evaluatePlain D (Fin.append par γ)) v →
            ∀ i, GoodVal (C := cutAt env D γ) par (v i))
        ∧ (∀ (s s' : String) (m : ℕ), l = [(s, m)] → q.noMention s → q.noMention s' →
          EnvNoMention env s' →
          ∀ (P : ℕ) (Y : Multiset (Tuple T ((k + m) * (7 + k) + P))) (X : Multiset (Tuple T m))
            (e : Tuple T P), (∀ v ∈ X, ∀ i, GoodVal (C := cutAt env D γ) par (v i)) →
          SliceIs (cutAt env D γ) par Y (X.map (fun v => (v, e))) →
          Good (CG (cutAt env D γ)) q (D.assign s X) (Fin.append par γ) →
          q.SettlesAt (D.assign s X) (Fin.append par γ) →
          SliceIs (cutAt env D γ) par ((symB env f P s' m q).evaluatePlain (D.assign s' Y) γ)
            ((q.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T n)).map
              (fun v => (v, e)))
          ∧ ∀ v, Multiset.Mem (q.evaluatePlain (D.assign s X) (Fin.append par γ)) v →
            ∀ i, GoodVal (C := cutAt env D γ) par (v i)) := by
  intro N
  induction N with
  | zero =>
    intro f n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro f n κ l q hq hsrc hfresh D γ par henv hamb
    obtain ⟨hnd, hdesc, hctr⟩ := henv
    have hnil : ∀ {s : String} {m : ℕ}, ([] : List (String × ℕ)) ≠ [(s, m)] := by simp
    have hcons : ∀ {s s' : String} {m m' : ℕ}, [(s', m')] = [(s, m)] → s' = s ∧ m' = m :=
      fun h => by simpa using h
    have hsl0 : ∀ {N' : ℕ}, slice (n := N') (P := 0) (0 : Multiset (Tuple T ((k + N') * (7 + k) +
        0)))
        (descEnc (cutAt env D γ) par) = 0 := fun {_} => Multiset.filter_zero _
    cases q with
    | Rel n s' =>
      refine ⟨fun _ hgood _ => ?_, fun s s' m hl => absurd hl hnil⟩
      obtain ⟨R, hRdef⟩ : ∃ R : Multiset (Tuple T n),
          R = (AggQueryIn.Rel n s').evaluatePlain D (Fin.append par γ) := ⟨_, rfl⟩
      have hR : ∀ v ∈ R, ∀ i, CG (cutAt env D γ) (v i) := fun v hv => hgood v (hRdef ▸ hv)
      refine ⟨?_, fun v hv i => Or.inr (hR v (hRdef ▸ hv) i)⟩
      have hRR : (AggQueryIn.Rel (T := T) (c := c) n s').evaluatePlain D γ
          = (AggQueryIn.Rel (T := T) (c := k + c) n s').evaluatePlain D (Fin.append par γ) := rfl
      rw [sym, evaluatePlain_projSA, evaluatePlain_prodR, hRR, ← hRdef]
      exact sliceIs_leaf par γ hnd (hdesc par) R hR
    | Hole n s₀ κ =>
      refine ⟨fun hl => absurd hl.symm hnil, fun s s' m hl hnm hnm' henvs P Y X e hX hY _ _ => ?_⟩
      obtain ⟨rfl, rfl⟩ := hcons hl
      have hsrc' : ((AggQueryIn.Hole n s₀ κ).evaluatePlain (D.assign s₀ X) (Fin.append par γ)
          : Multiset (Tuple T n)) = X := by
        simp only [AggQueryIn.evaluatePlain, Database.find_assign]
      rw [hsrc']
      refine ⟨?_, hX⟩
      rw [symB, dite_eq_left rfl]
      have : ((AggQueryIn.Hole ((k + n) * (7 + k) + P) s' : AggQueryIn T c _ _ _).evaluatePlain
          (D.assign s' Y) γ : Multiset (Tuple T _)) = Y := by
        simp only [AggQueryIn.evaluatePlain, Database.find_assign]
      rw [this]
      exact hY
    | Param pv ρ =>
      refine ⟨fun _ hgood _ => ?_, fun s s' m hl => absurd hl hnil⟩
      have hc : ∀ j a, pvCS pv j = .const a → CG (cutAt env D γ) a :=
        fun j a h => hgood j a (pvCS_const pv j h)
      have hS := sliceIs_symProj par 0 (pvCS pv) γ hamb hc (sliceIs_desc par hnd (hdesc par))
      rw [Multiset.map_singleton, pvCS_val] at hS
      have hsrc' : ({fun j => _root_.Sum.elim id (Fin.append par γ) (pv j)} : Multiset (Tuple T n))
          = (AggQueryIn.Param pv κ).evaluatePlain D (Fin.append par γ) := rfl
      rw [← hsrc', Multiset.map_singleton]
      refine ⟨?_, fun v hv i => ?_⟩
      · rw [sym, evaluatePlain_projSA]
        exact hS
      · rw [Multiset.mem_singleton.mp hv]
        have := goodVal_cs (pvCS pv i) par γ (Fin.elim0 : Tuple T 0) (fun j => j.elim0) hamb
          (hc i)
        rwa [show (pvCS pv i).val par γ Fin.elim0 = _root_.Sum.elim id (Fin.append par γ) (pv i)
          from congrFun (pvCS_val pv par γ) i] at this
    | Empty =>
      refine ⟨fun _ _ _ => ?_, fun s s' m hl => absurd hl hnil⟩
      refine ⟨?_, fun v hv => absurd hv (Multiset.notMem_zero _)⟩
      rw [sym, AggQueryIn.evaluatePlain_emptyRel]
      show slice 0 _ = encAll _ _ (Multiset.map _ 0)
      rw [Multiset.map_zero]
      rfl
    | Apply q₁ q₂ =>
      exact ⟨fun _ hg _ => hg.elim, fun s s' m _ _ _ _ P Y X e _ _ hg _ => hg.elim⟩
    | Sum q₁ q₂ =>
      exact ⟨fun _ hg _ => hg.elim, fun s s' m _ _ _ _ P Y X e _ _ hg _ => hg.elim⟩
    | Dedup q =>
      exact ⟨fun _ hg _ => hg.elim, fun s s' m _ _ _ _ P Y X e _ _ hg _ => hg.elim⟩
    | Diff q₁ q₂ =>
      exact ⟨fun _ hg _ => hg.elim, fun s s' m _ _ _ _ P Y X e _ _ hg _ => hg.elim⟩
    | MuSet s' q₀ q₁ =>
      exact ⟨fun _ hg _ => hg.elim, fun s s' m _ _ _ _ P Y X e _ _ hg _ => hg.elim⟩
    | GammaTok is his ts fs a q keep =>
      exact ⟨fun _ hg _ => hg.elim, fun s s' m _ _ _ _ P Y X e _ _ hg _ => hg.elim⟩
    | ProvSum is his t q =>
      exact ⟨fun _ hg _ => hg.elim, fun s s' m _ _ _ _ P Y X e _ _ hg _ => hg.elim⟩
    | WinExpr P O o ws ts fs g q keeps =>
      exact ⟨fun _ hg _ => hg.elim, fun s s' m _ _ _ _ P Y X e _ _ hg _ => hg.elim⟩
    | Proj ps q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨hcl, hbd⟩ := ih f q hs ⟨hsrc.1.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfresh D γ par
        ⟨hnd, hdesc, hctr⟩ hamb
      have hnf : ∀ j, (ps j).noFun = true := hsrc.1.1
      have hc : (∀ j, ∀ a ∈ (ps j).consts, CG (cutAt env D γ) a) →
          ∀ j a, projCS (ps j) = .const a → CG (cutAt env D γ) a :=
        fun h j a ha => h j a (projCS_const (ps j) (hnf j) ha)
      have hval : ∀ (u : Tuple T _), (fun j => (projCS (ps j)).val par γ u)
          = (fun j => (ps j).evalPlain u (Fin.append par γ)) :=
        fun u => funext fun j => projCS_val (ps j) (hnf j) par γ u
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl hnm hnm' henvs P Y X e hX hY hgood hset => ?_⟩
      · obtain ⟨hS, hG⟩ := hcl hl hgood.2 hset
        have := sliceIs_symProj par 0 (fun j => projCS (ps j)) γ hamb (hc hgood.1) hS
        rw [Multiset.map_map] at this
        refine ⟨?_, fun v hv i => ?_⟩
        · rw [sym, evaluatePlain_projSA]
          have hfun : ((fun x : Tuple T _ × Tuple T 0 => ((fun j => (projCS (ps j)).val par γ x.1
              : Tuple T n), x.2)) ∘ (fun v => (v, (Fin.elim0 : Tuple T 0))))
              = ((fun v => (v, (Fin.elim0 : Tuple T 0))) ∘
                (fun u j => (ps j).evalPlain u (Fin.append par γ))) :=
            funext fun u => by simp only [Function.comp, hval]
          rw [hfun, ← Multiset.map_map] at this
          exact this
        · obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hv
          show GoodVal (C := cutAt env D γ) par ((ps i).evalPlain u (Fin.append par γ))
          rw [← projCS_val (ps i) (hnf i) par γ u]
          exact goodVal_cs _ par γ u (hG u hu) hamb (hc hgood.1 i)
      · obtain ⟨hS, hG⟩ := hbd s s' m hl hnm hnm' henvs P Y X e hX hY hgood.2 hset
        have := sliceIs_symProj par P (fun j => projCS (ps j)) γ hamb (hc hgood.1) hS
        rw [Multiset.map_map] at this
        refine ⟨?_, fun v hv i => ?_⟩
        · rw [symB, evaluatePlain_projSA]
          have hfun : ((fun x : Tuple T _ × Tuple T P => ((fun j => (projCS (ps j)).val par γ x.1
              : Tuple T n), x.2)) ∘ (fun v => (v, e)))
              = ((fun v => (v, e)) ∘ (fun u j => (ps j).evalPlain u (Fin.append par γ))) :=
            funext fun u => by simp only [Function.comp, hval]
          rw [hfun, ← Multiset.map_map] at this
          exact this
        · obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hv
          show GoodVal (C := cutAt env D γ) par ((ps i).evalPlain u (Fin.append par γ))
          rw [← projCS_val (ps i) (hnf i) par γ u]
          exact goodVal_cs _ par γ u (hG u hu) hamb (hc hgood.1 i)
    | Sel φ q hφ =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨hcl, hbd⟩ := ih f q hs ⟨hsrc.1.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfresh D γ par
        ⟨hnd, hdesc, hctr⟩ hamb
      have hnf : φ.noFun = true := hsrc.1.1
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl hnm hnm' henvs P Y X e hX hY hgood hset => ?_⟩
      · obtain ⟨hS, hG⟩ := hcl hl hgood.2 hset
        have := sliceIs_symSel par 0 φ hnf hgood.1 γ hamb (fun x hx i => by
          obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hx
          exact hG u hu i) hS
        refine ⟨?_, fun v hv i => hG v (Multiset.mem_of_mem_filter hv) i⟩
        rw [sym]
        have h1 : ((AggQueryIn.Sel (transPred 0 φ).toGen (sym env f q)).evaluatePlain D γ
            : Multiset (Tuple T _)) = ((sym env f q).evaluatePlain D γ : Multiset (Tuple T
              _)).filter
              (fun r => (transPred 0 φ).eval3 r γ = Kleene.true) :=
          Multiset.filter_congr (fun r _ => by rw [GenPredIn.holdsPlain, SP.evalPlain3_toGen])
        have h2 : (((AggQueryIn.Sel φ q hφ).evaluatePlain D (Fin.append par γ)
            : Multiset (Tuple T n)).map (fun v => (v, (Fin.elim0 : Tuple T 0))))
            = ((q.evaluatePlain D (Fin.append par γ) : Multiset (Tuple T n)).map
              (fun v => (v, (Fin.elim0 : Tuple T 0)))).filter
                (fun x => φ.evalPlain3 x.1 (Fin.append par γ) = Kleene.true) := by
          rw [Multiset.filter_map]; rfl
        erw [h1, h2]
        exact this
      · obtain ⟨hS, hG⟩ := hbd s s' m hl hnm hnm' henvs P Y X e hX hY hgood.2 hset
        have := sliceIs_symSel par P φ hnf hgood.1 γ hamb (fun x hx i => by
          obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hx
          exact hG u hu i) hS
        refine ⟨?_, fun v hv i => hG v (Multiset.mem_of_mem_filter hv) i⟩
        rw [symB]
        have h1 : ((AggQueryIn.Sel (transPred P φ).toGen (symB env f P s' m q)
            (SelOK.of_noAggAtom (SP.hasAggAtom_toGen _))).evaluatePlain (D.assign s' Y) γ
            : Multiset (Tuple T _)) = ((symB env f P s' m q).evaluatePlain (D.assign s' Y) γ
              : Multiset (Tuple T _)).filter (fun r => (transPred P φ).eval3 r γ = Kleene.true) :=
          Multiset.filter_congr (fun r _ => by rw [GenPredIn.holdsPlain, SP.evalPlain3_toGen])
        have h2 : (((AggQueryIn.Sel φ q hφ).evaluatePlain (D.assign s X) (Fin.append par γ)
            : Multiset (Tuple T n)).map (fun v => (v, e)))
            = ((q.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T n)).map
              (fun v => (v, e))).filter
                (fun x => φ.evalPlain3 x.1 (Fin.append par γ) = Kleene.true) := by
          rw [Multiset.filter_map]; rfl
        erw [h1, h2]
        exact this
    | Explode i hi q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨hcl, hbd⟩ := ih f q hs ⟨hsrc.1, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfresh D γ par
        ⟨hnd, hdesc, hctr⟩ hamb
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl hnm hnm' henvs P Y X e hX hY hgood hset => ?_⟩
      · rw [sym]; exact hcl hl hgood hset
      · rw [symB]; exact hbd s s' m hl hnm hnm' henvs P Y X e hX hY hgood hset
    | Retag h q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨hcl, hbd⟩ := ih f q hs ⟨hsrc.1, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfresh D γ par
        ⟨hnd, hdesc, hctr⟩ hamb
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl hnm hnm' henvs P Y X e hX hY hgood hset => ?_⟩
      · rw [sym]; exact hcl hl hgood hset
      · rw [symB]; exact hbd s s' m hl hnm hnm' henvs P Y X e hX hY hgood hset
    | Prod q₁ q₂ =>
      rename_i n₁ n₂ κ₁ κ₂ l₁ l₂
      have hs₁ : sizeOf q₁ ≤ N := by simp at hq; omega
      have hs₂ : sizeOf q₂ ≤ N := by simp at hq; omega
      have hsrc₁ : SymSrc Θ q₁ := ⟨hsrc.1.1, hsrc.2.1, hsrc.2.2.1.1, hsrc.2.2.2.1⟩
      have hsrc₂ : SymSrc Θ q₂ := ⟨hsrc.1.2, hsrc.2.1, hsrc.2.2.1.2, hsrc.2.2.2.2⟩
      have hf₁ : ∀ i, q₁.noMention (AggQueryIn.tri f 1 i) ∧ EnvNoMention env (AggQueryIn.tri f 1
          i) :=
        fun i => ⟨(hfresh _).1.1, (hfresh _).2⟩
      have hf₂ : ∀ i, q₂.noMention (AggQueryIn.tri f 2 i) ∧ EnvNoMention env (AggQueryIn.tri f 2
          i) :=
        fun i => ⟨(hfresh _).1.2, (hfresh _).2⟩
      -- the product of two relations, as a bind
      have hprod : ∀ (D' : Database T) (γ' : Fin (k + c) → T),
          ((AggQueryIn.Prod q₁ q₂).evaluatePlain D' γ' : Multiset (Tuple T (n₁ + n₂)))
            = (q₁.evaluatePlain D' γ' : Multiset (Tuple T n₁)).bind (fun u =>
              (q₂.evaluatePlain D' γ' : Multiset (Tuple T n₂)).map (fun w => Fin.append u w)) :=
        fun D' γ' => by
          show q₁.evaluatePlain D' γ' * q₂.evaluatePlain D' γ' = _
          rw [Relation.hMul_eq_bind]
      have hgoodApp : ∀ (R₁ : Multiset (Tuple T n₁)) (R₂ : Multiset (Tuple T n₂)),
          (∀ u ∈ R₁, ∀ i, GoodVal (C := cutAt env D γ) par (u i)) →
          (∀ w ∈ R₂, ∀ i, GoodVal (C := cutAt env D γ) par (w i)) →
          ∀ v ∈ R₁.bind (fun u => R₂.map (fun w => (Fin.append u w : Tuple T (n₁ + n₂)))),
            ∀ i, GoodVal (C := cutAt env D γ) par (v i) := by
        intro R₁ R₂ h₁ h₂ v hv i
        obtain ⟨u, hu, hv⟩ := Multiset.mem_bind.mp hv
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hv
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [Fin.append_left]; exact h₁ u hu j
        · rw [Fin.append_right]; exact h₂ w hw j
      have hfil : ∀ {P₁ P₂ : ℕ} (M : Multiset (Tuple T (((k + n₁) * (7 + k) + P₁)
          + ((k + n₂) * (7 + k) + P₂)))),
          M.filter (fun r => ((descEqSP (n₁ := n₁) (n₂ := n₂) P₁ P₂).toGen).holdsPlain r γ)
            = M.filter (fun r => (descEqSP (n₁ := n₁) (n₂ := n₂) P₁ P₂).eval3 r γ = Kleene.true) :=
        fun M => Multiset.filter_congr (fun r _ => by
          rw [GenPredIn.holdsPlain, SP.evalPlain3_toGen])
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl hnm hnm' henvs P Y X e hX hY hgood hset => ?_⟩
      · obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
        obtain ⟨hS₁, hG₁⟩ := (ih (AggQueryIn.tri f 1) q₁ hs₁ hsrc₁ hf₁ D γ par ⟨hnd, hdesc,
            hctr⟩
          hamb).1 hl₁ hgood.1 hset.1
        obtain ⟨hS₂, hG₂⟩ := (ih (AggQueryIn.tri f 2) q₂ hs₂ hsrc₂ hf₂ D γ par ⟨hnd, hdesc,
            hctr⟩
          hamb).1 hl₂ hgood.2 hset.2
        have hJ := sliceIs_joinL par γ hS₁ hS₂
        erw [hprod]
        refine ⟨?_, hgoodApp _ _ hG₁ hG₂⟩
        rw [sym, evaluatePlain_projSA]
        show SliceIs _ par (Multiset.map _ (Multiset.filter _
          ((prodR (sym env (AggQueryIn.tri f 1) q₁) (sym env (AggQueryIn.tri f 2) q₂)).evaluatePlain
            D γ))) _
        rw [evaluatePlain_prodR]
        erw [hfil]
        have hR : (((q₁.evaluatePlain D (Fin.append par γ) : Multiset (Tuple T n₁)).bind (fun u =>
            (q₂.evaluatePlain D (Fin.append par γ) : Multiset (Tuple T n₂)).map
              (fun w => (Fin.append u w : Tuple T (n₁ + n₂))))).map
                (fun v => (v, (Fin.elim0 : Tuple T 0))))
            = ((q₁.evaluatePlain D (Fin.append par γ) : Multiset (Tuple T n₁)).map
                (fun v => (v, (Fin.elim0 : Tuple T 0)))).bind (fun x₁ =>
              ((q₂.evaluatePlain D (Fin.append par γ) : Multiset (Tuple T n₂)).map
                (fun v => (v, (Fin.elim0 : Tuple T 0)))).map
                (fun x₂ => ((Fin.append x₁.1 x₂.1 : Tuple T (n₁ + n₂)), x₁.2))) := by
          rw [Multiset.map_bind, Multiset.bind_map]
          simp only [Multiset.map_map, Function.comp]
          rfl
        erw [hR]
        exact hJ
      · have hsymeq : ∀ {n' : ℕ} {κ' : Fin n' → ColKind} {l' : List (String × ℕ)}
            (q' : AggQueryIn T (k + c) n' κ' l') (f' : ℕ → String), q'.noMention s' →
            ((sym env f' q').evaluatePlain (D.assign s' Y) γ : Multiset (Tuple T _))
              = (sym env f' q').evaluatePlain D γ := by
          intro n' κ' l' q' f' hq'
          exact AggQueryIn.evaluatePlain_assign_of_noMention Y _
            (noMention_sym_aux env henvs (sizeOf q') f' q' le_rfl hq').1 D γ
        by_cases hl₁ : l₁ = []
        · subst hl₁
          have hl₂ : l₂ = [(s, m)] := hl
          have hq₁eq := AggQueryIn.evaluatePlain_assign_of_noMention X q₁ hnm.1 D (Fin.append par γ)
          obtain ⟨hS₁, hG₁⟩ := (ih (AggQueryIn.tri f 1) q₁ hs₁ hsrc₁ hf₁ D γ par ⟨hnd, hdesc, hctr⟩
            hamb).1 rfl ((good_assign_of_noMention _ X q₁ hnm.1 D _).mp hgood.1)
            (AggQueryIn.settlesAt_assign_of_noMention X q₁ hnm.1 D _ hset.1)
          rw [← hq₁eq] at hS₁ hG₁
          rw [← hsymeq q₁ _ hnm'.1] at hS₁
          obtain ⟨hS₂, hG₂⟩ := (ih (AggQueryIn.tri f 2) q₂ hs₂ hsrc₂ hf₂ D γ par ⟨hnd,
              hdesc, hctr⟩
            hamb).2 s s' m hl₂ hnm.2 hnm'.2 henvs P Y X e hX hY hgood.2 hset.2
          have hJ := sliceIs_joinR par γ hS₁ hS₂
          erw [hprod]
          refine ⟨?_, hgoodApp _ _ hG₁ hG₂⟩
          rw [symB, ite_eq_left rfl, evaluatePlain_projSA]
          show SliceIs _ par (Multiset.map _ (Multiset.filter _
            ((prodR (sym env (AggQueryIn.tri f 1) q₁) (symB env (AggQueryIn.tri f 2) P s' m
              q₂)).evaluatePlain
              (D.assign s' Y) γ))) _
          rw [evaluatePlain_prodR]
          erw [hfil]
          have hR : (((q₁.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T
              n₁)).bind
              (fun u => (q₂.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T
                n₂)).map
                (fun w => (Fin.append u w : Tuple T (n₁ + n₂))))).map (fun v => (v, e)))
              = ((q₁.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T n₁)).map
                  (fun v => (v, (Fin.elim0 : Tuple T 0)))).bind (fun x₁ =>
                ((q₂.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T n₂)).map
                  (fun v => (v, e))).map
                  (fun x₂ => ((Fin.append x₁.1 x₂.1 : Tuple T (n₁ + n₂)), x₂.2))) := by
            rw [Multiset.map_bind, Multiset.bind_map]
            simp only [Multiset.map_map, Function.comp]
            rfl
          erw [hR]
          exact hJ
        · rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
          swap
          · exact absurd h₁ hl₁
          · subst h₂
            have hq₂eq := AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hnm.2 D
              (Fin.append par γ)
            obtain ⟨hS₂, hG₂⟩ := (ih (AggQueryIn.tri f 2) q₂ hs₂ hsrc₂ hf₂ D γ par
              ⟨hnd, hdesc, hctr⟩ hamb).1 rfl ((good_assign_of_noMention _ X q₂ hnm.2 D _).mp
                hgood.2)
              (AggQueryIn.settlesAt_assign_of_noMention X q₂ hnm.2 D _ hset.2)
            rw [← hq₂eq] at hS₂ hG₂
            rw [← hsymeq q₂ _ hnm'.2] at hS₂
            obtain ⟨hS₁, hG₁⟩ := (ih (AggQueryIn.tri f 1) q₁ hs₁ hsrc₁ hf₁ D γ par
              ⟨hnd, hdesc, hctr⟩ hamb).2 s s' m h₁ hnm.1 hnm'.1 henvs P Y X e hX hY hgood.1 hset.1
            have hJ := sliceIs_joinL par γ hS₁ hS₂
            erw [hprod]
            refine ⟨?_, hgoodApp _ _ hG₁ hG₂⟩
            rw [symB, ite_eq_right hl₁, evaluatePlain_projSA]
            show SliceIs _ par (Multiset.map _ (Multiset.filter _
              ((prodR (symB env (AggQueryIn.tri f 1) P s' m q₁) (sym env (AggQueryIn.tri f 2)
                q₂)).evaluatePlain
                (D.assign s' Y) γ))) _
            rw [evaluatePlain_prodR]
            erw [hfil]
            have hR : (((q₁.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T
                n₁)).bind
                (fun u => (q₂.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T
                  n₂)).map
                  (fun w => (Fin.append u w : Tuple T (n₁ + n₂))))).map (fun v => (v, e)))
                = ((q₁.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T n₁)).map
                    (fun v => (v, e))).bind (fun x₁ =>
                  ((q₂.evaluatePlain (D.assign s X) (Fin.append par γ) : Multiset (Tuple T n₂)).map
                    (fun v => (v, (Fin.elim0 : Tuple T 0)))).map
                    (fun x₂ => ((Fin.append x₁.1 x₂.1 : Tuple T (n₁ + n₂)), x₁.2))) := by
              rw [Multiset.map_bind, Multiset.bind_map]
              simp only [Multiset.map_map, Function.comp]
              rfl
            erw [hR]
            exact hJ
    | Gamma is ts fs q keep ord =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨hcl, -⟩ := ih f q hs ⟨hsrc.1.2.2.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfresh D γ
          par
        ⟨hnd, hdesc, hctr⟩ hamb
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl => absurd hl hnil⟩
      obtain ⟨hS, hG⟩ := hcl rfl hgood.1 hset
      have hkeep : ∀ j φ, keep j = some φ → φ.noFun = true ∧ ∀ a ∈ φ.consts, CG (cutAt env D γ) a :=
        fun j φ h => ⟨by have := hsrc.1.2.2.1 j; rw [h] at this; exact this, hgood.2.1 j φ h⟩
      have := sliceIs_symGamma par is ts fs keep ord hsrc.1.1 (fun j => hsrc.2.1 _ (hsrc.1.2.1 j))
        hkeep _ _ hG hS γ (fun y hy j => hgood.2.2 y hy j)
      refine ⟨?_, fun v hv i => ?_⟩
      swap
      · refine Fin.addCases (fun i₁ => ?_) (fun j => Or.inr (hgood.2.2 v hv j)) i
        obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hv
        obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hg)
        rw [Fin.append_left]
        exact hG u hu _
      rw [sym, evaluatePlain_projSA, AggQueryIn.evaluatePlain_allRegOf]
      exact this
    | GammaNest is his p g q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨hcl, -⟩ := ih f q hs ⟨hsrc.1.2.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩ hfresh D γ par
        ⟨hnd, hdesc, hctr⟩ hamb
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl => absurd hl hnil⟩
      obtain ⟨hS, hG⟩ := hcl rfl hgood.1 hset
      obtain ⟨g', hg', hgΘ, rfl⟩ := hsrc.1.2.1
      have := sliceIs_symGammaNest par is p hsrc.1.1 hgood.2.1 g' hg' (hsrc.2.1 _ hgΘ) _ _ hS γ hamb
        (fun y hy => hgood.2.2 y hy)
      refine ⟨?_, fun v hv i => ?_⟩
      swap
      · refine Fin.addCases (fun i₁ => ?_) (fun j => ?_) i
        · obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hv
          obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hg)
          rw [Fin.append_left]
          exact hG u hu _
        · rw [Subsingleton.elim j 0]; exact Or.inr (hgood.2.2 v hv)
      rw [sym, evaluatePlain_projSA, AggQueryIn.evaluatePlain_allRegOf]
      exact this
    | Win P O o w t g q hrr dist keep =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨hκ, hwq⟩ := hsrc.2.2.1
      subst hκ
      obtain ⟨hcl, -⟩ := ih f q hs ⟨hsrc.1.2.2.2, hsrc.2.1, hwq, hsrc.2.2.2⟩ hfresh D γ par
        ⟨hnd, hdesc, hctr⟩ hamb
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl => absurd hl hnil⟩
      obtain ⟨hS, hG⟩ := hcl rfl hgood.1 hset
      have hf : (if dist then g.distinct else g).ReadsCount := by
        have := hsrc.1.2.1
        cases dist
        · exact hsrc.2.1 _ this
        · exact hsrc.2.1 _ this
      have hkeep : ∀ φ, keep = some φ → φ.noFun = true ∧ ∀ a ∈ φ.consts, CG (cutAt env D γ) a :=
        fun φ h => ⟨by have := hsrc.1.2.2.1; rw [h] at this; exact this, hgood.2.1 φ h⟩
      have := sliceIs_symWin par P O o w t hsrc.1.1 hf keep hkeep _ _ hG hS γ (fun v hv => by
        have := hgood.2.2 (Fin.snoc v (ValueFrame.windowValueOpt P O o w t
          (if dist then g.distinct else g) keep
          ((q.evaluatePlain D (Fin.append par γ)).map (ColKind.readTuple (ColKind.allReg _)))
          (ColKind.readTuple (ColKind.allReg _) v) (Fin.append par γ)))
          (Multiset.mem_map_of_mem _ hv)
        simpa using this)
      refine ⟨?_, fun v hv i => ?_⟩
      · rw [sym, evaluatePlain_projSA]
        simp only [AggQueryIn.evaluatePlain_allRegOf, AggQueryIn.evaluatePlain,
          ColKind.readTuple_allReg, Multiset.map_id'] at this ⊢
        exact this
      · obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hv
        refine Fin.lastCases ?_ (fun i => ?_) i
        · exact Or.inr (hgood.2.2 _ (Multiset.mem_map_of_mem _ hu))
        · rw [Fin.snoc_castSucc]; exact hG u hu i
    | GammaScalar ts fs q ord =>
      rename_i m _ _
      have hs : sizeOf q ≤ N := by simp at hq; omega
      have hf₁ : ∀ i, q.noMention (AggQueryIn.tri f 1 i) ∧ EnvNoMention env (AggQueryIn.tri f 1 i)
          :=
        fun i => ⟨(hfresh _).1, (hfresh _).2⟩
      obtain ⟨hcl, -⟩ := ih (AggQueryIn.tri f 1) q hs ⟨hsrc.1.2.2, hsrc.2.1, hsrc.2.2.1, hsrc.2.2.2⟩
        hf₁ D γ par ⟨hnd, hdesc, hctr⟩ hamb
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl => absurd hl hnil⟩
      obtain ⟨hS, -⟩ := hcl rfl hgood.1 hset
      obtain ⟨Q, hQ⟩ : ∃ Q : Multiset (Tuple T ((k + m) * (7 + k))),
          Q = (sym env (AggQueryIn.tri f 1) q).evaluatePlain D γ := ⟨_, rfl⟩
      obtain ⟨Dq, hDq⟩ : ∃ Dq : Multiset (Tuple T (k * (7 + k))),
          Dq = env.Desc.evaluatePlain D γ := ⟨_, rfl⟩
      have hpadE : ((AggQueryIn.Proj (projSA (padSA (T := T) (c := c) m)) env.Desc).castKind
          (projSA_kind _)).evaluatePlain D γ
          = ((Dq.map (padRow m)).map (fun r => Fin.append r (fun _ : Fin 1 => (0 : T)))
            : Multiset _) := by
        rw [evaluatePlain_projSA, Multiset.map_map, ← hDq]
        exact Multiset.map_congr rfl (fun d _ => eval_padSA m d γ)
      have hdatE : ((AggQueryIn.Proj (projSA (tagSA (T := T) (c := c) ValueType.nonzero))
          (sym env (AggQueryIn.tri f 1) q)).castKind (projSA_kind _)).evaluatePlain D γ
          = (Q.map (fun r => Fin.append r (fun _ : Fin 1 => ValueType.nonzero)) : Multiset _) := by
        rw [evaluatePlain_projSA, ← hQ]
        exact Multiset.map_congr rfl (fun r _ => eval_tagSA _ r γ)
      have hm₁ : ((AggQueryIn.Proj (projSA (padSA (T := T) (c := c) m)) env.Desc).castKind
          (projSA_kind _)).noMention (AggQueryIn.tri f 0 0) := by
        rw [AggQueryIn.noMention_castKind]; exact (hfresh 0).2.2.1
      have hm₂ : ((AggQueryIn.Proj (projSA (tagSA (T := T) (c := c) ValueType.nonzero))
          (sym env (AggQueryIn.tri f 1) q)).castKind (projSA_kind _)).noMention
            (AggQueryIn.tri f 0 1) := by
        rw [AggQueryIn.noMention_castKind]
        exact (noMention_sym_aux env (hfresh 3).2 _ _ q le_rfl (hfresh 3).1).1
      have hpad : ((Dq.map (padRow m)).map (fun r => descP (P := 0) r)).Nodup
          ∧ descEnc (cutAt env D γ) par ∈ (Dq.map (padRow m)).map (fun r => descP (P := 0) r) := by
        rw [Multiset.map_map]
        simp only [Function.comp, descP_padRow, Multiset.map_id']
        exact ⟨hDq ▸ hnd, hDq ▸ hdesc par⟩
      have := sliceIs_symGammaScalar par ts fs ord hsrc.1.1 (fun j => hsrc.2.1 _ (hsrc.1.2.1 j))
        Q _ (hQ ▸ hS) _ hpad γ (fun j => hgood.2 _ (Multiset.mem_coe.2 (List.mem_singleton_self
          _)) j)
      refine ⟨?_, fun v hv i => ?_⟩
      · rw [sym, evaluatePlain_projSA, AggQueryIn.evaluatePlain_allRegOf]
        simp only [AggQueryIn.evaluatePlain]
        rw [AggQueryIn.evaluatePlain_sumByMuX _ _ _ _ hm₁ hm₂, hpadE, hdatE]
        exact this
      · exact Or.inr (hgood.2 v hv i)
    | Mu s' q₀ q₁ =>
      have hs₀ : sizeOf q₀ ≤ N := by simp at hq; omega
      have hs₁ : sizeOf q₁ ≤ N := by simp at hq; omega
      obtain ⟨hnm₀, hnm₁, hhy₀, hhy₁⟩ := hsrc.2.2.2
      have hsrc₀ : SymSrc Θ q₀ := ⟨hsrc.1.1, hsrc.2.1, hsrc.2.2.1.1, hhy₀⟩
      have hsrc₁ : SymSrc Θ q₁ := ⟨hsrc.1.2, hsrc.2.1, hsrc.2.2.1.2, hhy₁⟩
      have hf₀ : ∀ i, q₀.noMention (AggQueryIn.tri f 1 i) ∧ EnvNoMention env (AggQueryIn.tri f 1
          i) :=
        fun i => ⟨(hfresh _).1.1, (hfresh _).2⟩
      have hf₁ : ∀ i, q₁.noMention (AggQueryIn.tri f 2 i) ∧ EnvNoMention env (AggQueryIn.tri f 2
          i) :=
        fun i => ⟨(hfresh _).1.2, (hfresh _).2⟩
      refine ⟨fun hl hgood hset => ?_, fun s s' m hl => absurd hl hnil⟩
      obtain ⟨hset₀, hz, hms, hsetk⟩ := hset
      obtain ⟨hS₀, hG₀⟩ := (ih (AggQueryIn.tri f 1) q₀ hs₀ hsrc₀ hf₀ D γ par
        ⟨hnd, hdesc, hctr⟩ hamb).1 rfl hgood.1 hset₀
      obtain ⟨X₀, hX₀⟩ : ∃ X₀ : Multiset (Tuple T n),
          X₀ = q₀.evaluatePlain D (Fin.append par γ) := ⟨_, rfl⟩
      obtain ⟨step, hstep⟩ : ∃ step : Multiset (Tuple T n) → Multiset (Tuple T n),
          step = fun X => (q₁.evaluatePlain (D.assign s' X) (Fin.append par γ)
            : Multiset (Tuple T n)) := ⟨_, rfl⟩
      have hbody := (ih (AggQueryIn.tri f 2) q₁ hs₁ hsrc₁ hf₁ D γ par
        ⟨hnd, hdesc, hctr⟩ hamb).2 s' (AggQueryIn.tri f 0 0) n rfl hnm₁ (hfresh 0).1.2 (hfresh 0).2
          (env.ctrK n)
      obtain ⟨cs, hcs, hne, hle, hL, hSv⟩ := hctr n
      have hgoodR : ∀ j, ∀ v ∈ step^[j] X₀, ∀ i, GoodVal (C := cutAt env D γ) par (v i) := by
        intro j
        induction j with
        | zero => intro v hv; exact hG₀ v (hX₀ ▸ hv)
        | succ j ihj =>
          rw [Function.iterate_succ_apply']
          intro v hv
          have := (hbody _ (step^[j] X₀) cs[0] ihj
            (sliceIs_encAll _ par ((step^[j] X₀).map (fun v => (v, cs[0]))))
            (by subst hstep hX₀; exact hgood.2 j) (by subst hstep hX₀; exact hsetk j)).2
          rw [hstep] at hv this
          exact this v hv
      obtain ⟨F, C', hFC⟩ := AggQueryIn.bind_of_body q₁ rfl hnm₁ D (Fin.append par γ)
      have hC' : C' = 0 := by
        have := hFC 0
        rw [Multiset.zero_bind, zero_add] at this
        exact this.symm.trans hz
      have hsb : step = bindStep F := by
        rw [hstep]
        funext X
        rw [hFC X, hC', add_zero]
        rfl
      have h0 : step 0 = 0 := by rw [hsb]; exact bindStep_zero F
      have hset' : step^[cs.length] X₀ = 0 := by
        refine iterate_eq_zero_of_le h0 ?_ (le_trans (Nat.pow_le_pow_left
          (card_goodSet_le (cutAt env D γ) par) n) hle)
        rw [hsb]
        refine bindStep_round_eq_zero_of_settles F X₀ _ (fun j u hu i => ?_) ?_
        · rw [← hsb] at hu
          exact mem_goodSet (hgoodR j u hu i)
        · rw [← hsb, hstep, hX₀]
          exact hms
      have := sliceIs_symMu (C := cutAt env D γ) (AggQueryIn.tri f 0 0) (sym env (AggQueryIn.tri f
          1) q₀)
        (symB env (AggQueryIn.tri f 2) (env.ctrK n) (AggQueryIn.tri f 0 0) n q₁) (env.Lq n)
          (env.Sq n)
        (((hfresh 0).2.2.2 n).2) D γ step X₀ (hX₀ ▸ hS₀)
        (fun Y y hy => symB_pres_aux env _ _ _ _ _ q₁ le_rfl D γ Y y hy) cs hcs hne
        (fun j _ Y e hY => by
          have h := (hbody Y (step^[j] X₀) e (hgoodR j) hY
            (by subst hstep hX₀; exact hgood.2 j) (by subst hstep hX₀; exact hsetk j)).1
          conv_rhs at h => rw [show (q₁.evaluatePlain (D.assign s' (step^[j] X₀))
            (Fin.append par γ) : Multiset (Tuple T n)) = step (step^[j] X₀) by rw [hstep]]
          exact h)
        hL hSv h0 hset'
      have hmem : ∀ v, Multiset.Mem (muSumFix step X₀) v → ∃ j, v ∈ step^[j] X₀ := by
        intro v hv
        have hk : step^[cs.length + 1] X₀ = 0 := iterate_eq_zero_of_le h0 hset' (Nat.le_succ _)
        rw [muSumFix_eq_of_empty h0 hk, muSum_eq_sum'] at hv
        obtain ⟨j, -, hj⟩ := Multiset.mem_sum.mp hv
        exact ⟨j, hj⟩
      refine ⟨?_, fun v hv i => ?_⟩
      · rw [sym]
        subst hstep hX₀
        exact this
      · subst hstep hX₀
        obtain ⟨j, hj⟩ := hmem v hv
        exact hgoodR j v hj i

/-- **The symbolic evaluation is correct** on a closed query: under the
descriptor of a parameter row, its symbolic relation holds the encodings
of the rows the query computes at that row. -/
theorem sym_correct {k c : ℕ} (env : SymEnv T k c) (Θ : Set (SeqAggFunc T)) (f : ℕ → String)
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T (k + c) n κ) (hsrc : SymSrc Θ q)
    (hfresh : ∀ i, q.noMention (f i) ∧ EnvNoMention env (f i))
    (D : Database T) (γ : Fin c → T) (par : Fin k → T) (henv : EnvOK env D γ)
    (hamb : ∀ j, CG (cutAt env D γ) (γ j))
    (hgood : Good (CG (cutAt env D γ)) q D (Fin.append par γ))
    (hset : q.SettlesAt D (Fin.append par γ)) :
    SliceIs (P := 0) (cutAt env D γ) par ((sym env f q).evaluatePlain D γ)
      ((q.evaluatePlain D (Fin.append par γ) : Multiset (Tuple T n)).map
        (fun v => (v, Fin.elim0))) :=
  ((sym_correct_aux env Θ _ f q le_rfl hsrc hfresh D γ par henv hamb).1 rfl hgood hset).1

end Sym
