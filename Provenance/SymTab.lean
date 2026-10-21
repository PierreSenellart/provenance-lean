module

public import Provenance.SymMu

/-!
# The symbolic evaluation of a query, operator by operator

`Sym.sym` maps a query whose context starts with `k` parameter
components to a closed symbolic relation (`Provenance.SymOps`), and
`Sym.symB` a recursive term to a symbolic term carrying `P` further
columns through its rounds – the counter of a bounded recursion
(`Provenance.SymMu`). The translation reads the relation of descriptors
and the counters off an environment (`Sym.SymEnv`): what it is asked of
those is stated where it is used, by the correctness theorem.

A construction outside the fragment the translation is for – an apply, a
union, a difference, a duplicate elimination, a set recursion, the
rewritten world's operators – translates to an empty relation: such a
query is not a symbolic evaluation's input, and the correctness theorem
excludes it by hypothesis.
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

/-- **What the symbolic evaluation reads off its environment**: the cut, the
relation of descriptors, and for each arity of a bag recursion the width of
its counters, the least counter and the successor relation. -/
structure SymEnv (T : Type) [ValueType T] (k c : ℕ) where
  /-- The cut, as a unary relation. -/
  CQ : AggQueryIn T c 1 (ColKind.allReg 1)
  /-- The descriptors. -/
  Desc : AggQueryIn T c (k * (7 + k)) (ColKind.allReg (k * (7 + k)))
  /-- The width of the counters of a recursion of each arity. -/
  ctrK : ℕ → ℕ
  /-- The least counter. -/
  Lq : (n : ℕ) → AggQueryIn T c (ctrK n) (ColKind.allReg (ctrK n))
  /-- The successor relation of the counters. -/
  Sq : (n : ℕ) → AggQueryIn T c (ctrK n + ctrK n) (ColKind.allReg (ctrK n + ctrK n))

variable {k c : ℕ}

/-- An empty relation that reads a hole, for the recursive terms the
translation has no case for. -/
def junkB (N M : ℕ) (s : String) : AggQueryIn T c N (ColKind.allReg N) [(s, M)] :=
  (AggQueryIn.Proj (fun _ : Fin N => ProjColIn.term (TermGIn.const (0 : T)))
    (AggQueryIn.Sel (GenPredIn.cmp CompOp.syneq (.const 0) (.const ValueType.nonzero))
      (AggQueryIn.Hole M s) (SelOK.of_noAggAtom rfl))).castKind (funext fun _ => rfl)

/-- The source of a parameter leaf's column. -/
def pvCS {m : ℕ} (pv : Fin m → T ⊕ Fin (k + c)) (j : Fin m) : CS T k c 0 :=
  match pv j with
  | .inl a => .const a
  | .inr o => Fin.addCases (motive := fun _ => CS T k c 0) (fun i => .par i) (fun j' => .amb j') o

/-- The row of a symbolic relation with one more column, the tag. -/
def tagSA {N : ℕ} (a : T) : Fin (N + 1) → SA T c N :=
  Fin.lastCases (.const a) (fun i => .col i)

/-- **A padding row of a scalar aggregation's union**: a descriptor,
constant cells, and the tag `0`. -/
def padSA (m : ℕ) : Fin ((k + m) * (7 + k) + 1) → SA T c (k * (7 + k)) :=
  Fin.lastCases (.const 0) (fun x => Fin.addCases (motive := fun _ => SA T c _)
    (fun i₀ => .col (ci i₀ (finProdFinEquiv.symm x).2))
    (fun _ => .const 0) (finProdFinEquiv.symm x).1)

mutual

/-- **The symbolic evaluation of a closed query.** -/
noncomputable def sym (env : SymEnv T k c) (f : ℕ → String) :
    {n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T (k + c) n κ l → AggQueryIn T c ((k + n) * (7 + k)) (ColKind.allReg _)
  | _, _, _, .Rel n s =>
    (AggQueryIn.Proj (projSA (leafSA (k := k) n))
      (prodR env.Desc (AggQueryIn.Rel n s))).castKind (projSA_kind _)
  | _, _, _, .Param pv _ =>
    (AggQueryIn.Proj (projSA (symProjSA (n := 0) 0 (pvCS pv))) env.Desc).castKind (projSA_kind _)
  | _, _, _, .Proj ps q =>
    (AggQueryIn.Proj (projSA (symProjSA 0 (fun j => projCS (ps j)))) (sym env f q)).castKind
      (projSA_kind _)
  | _, _, _, .Sel φ q _ => AggQueryIn.Sel (transPred 0 φ).toGen (sym env f q)
  | _, _, _, .Prod q₁ q₂ =>
    (AggQueryIn.Proj (projSA (joinLSA 0 0))
      (AggQueryIn.Sel (descEqSP 0 0).toGen
        (prodR (sym env (AggQueryIn.tri f 1) q₁) (sym env (AggQueryIn.tri f 2) q₂)))).castKind
      (projSA_kind _)
  | _, _, _, .Explode _ _ q => sym env f q
  | _, _, _, .Retag _ q => sym env f q
  | _, _, _, @AggQueryIn.Mu _ _ n _ _ q₀ q₁ =>
    symMuQ (AggQueryIn.tri f 0 0) (sym env (AggQueryIn.tri f 1) q₀)
      (symB env (AggQueryIn.tri f 2) (env.ctrK n) (AggQueryIn.tri f 0 0) n q₁) (env.Lq n) (env.Sq n)
  | _, _, _, .Gamma is ts fs q keep _ =>
    (AggQueryIn.Proj (projSA (gOutSA _ _))
      (AggQueryIn.allRegOf (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) (gKeyIdx is)
        (fun j => termV (ts j)) fs (sym env f q)
        (fun j => (keep j).map (fun φ => (transSel 0 φ).toSel)) .unord))).castKind
      (projSA_kind _)
  | _, _, _, @AggQueryIn.GammaScalar _ _ m n₂ _ _ ts fs q _ =>
    (AggQueryIn.Proj (projSA (sOutSA n₂))
      (AggQueryIn.allRegOf (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) sKeyIdx
        (fun j => (termV (ts j)).widen 1) fs
        (AggQueryIn.sumByMuX (AggQueryIn.tri f 0 0) (AggQueryIn.tri f 0 1)
          ((AggQueryIn.Proj (projSA (padSA m)) env.Desc).castKind (projSA_kind _))
          ((AggQueryIn.Proj (projSA (tagSA ValueType.nonzero))
            (sym env (AggQueryIn.tri f 1) q)).castKind (projSA_kind _)))
        (fun _ => some tagSel) .unord))).castKind (projSA_kind _)
  | _, _, _, .GammaNest is _ p g q =>
    (AggQueryIn.Proj (projSA (gOutSA _ 1))
      (AggQueryIn.allRegOf (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) (gKeyIdx is)
        (fun _ h => by cases h) (projV p) g (sym env f q)))).castKind (projSA_kind _)
  | _, _, _, @AggQueryIn.Win _ _ n _ _ _ _ _ P O o w hs t g q _ dist keep =>
    (AggQueryIn.Proj (projSA (wOutSA n))
      (AggQueryIn.allRegOf (AggQueryIn.Win (hsql := isSQL_expandFrame hs) (lab := 0) (rd := fun _
        => false) (gKeyIdx P)
        (winOIdx O) (expandSpec o) (expandFrame w) (termV t) g (sym env f q)
        (winReadsReg_allReg _ _ _) dist (keep.map (fun φ => (transSel 0 φ).toSel))))).castKind
      (projSA_kind _)
  | _, _, _, .Hole _ _ _ => AggQueryIn.emptyRel _
  | _, _, _, .Empty => AggQueryIn.emptyRel _
  | _, _, _, .Apply _ _ => AggQueryIn.emptyRel _
  | _, _, _, .Sum _ _ => AggQueryIn.emptyRel _
  | _, _, _, .Dedup _ => AggQueryIn.emptyRel _
  | _, _, _, .Diff _ _ => AggQueryIn.emptyRel _
  | _, _, _, .MuSet _ _ _ => AggQueryIn.emptyRel _
  | _, _, _, .GammaTok _ _ _ _ _ _ _ => AggQueryIn.emptyRel _
  | _, _, _, .ProvSum _ _ _ _ => AggQueryIn.emptyRel _
  | _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => AggQueryIn.emptyRel _
  termination_by _ _ _ q => sizeOf q

/-- **The symbolic evaluation of a recursive term**, carrying `P` further
columns through it. -/
noncomputable def symB (env : SymEnv T k c) (f : ℕ → String) (P : ℕ) (s : String) (m : ℕ) :
    {n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T (k + c) n κ l →
      AggQueryIn T c ((k + n) * (7 + k) + P) (ColKind.allReg _) [(s, (k + m) * (7 + k) + P)]
  | _, _, _, @AggQueryIn.Hole _ _ n s' _ =>
    if h : n = m then by subst h; exact AggQueryIn.Hole ((k + n) * (7 + k) + P) s
    else junkB _ _ s
  | _, _, _, .Proj ps q =>
    (AggQueryIn.Proj (projSA (symProjSA P (fun j => projCS (ps j)))) (symB env f P s m q)).castKind
      (projSA_kind _)
  | _, _, _, .Sel φ q _ =>
    AggQueryIn.Sel (transPred P φ).toGen (symB env f P s m q)
      (SelOK.of_noAggAtom (SP.hasAggAtom_toGen _))
  | _, _, _, @AggQueryIn.Prod _ _ n₁ n₂ _ _ l₁ _ q₁ q₂ =>
    if l₁ = [] then
      (AggQueryIn.Proj (projSA (joinRSA 0 P))
        (AggQueryIn.Sel (descEqSP 0 P).toGen
          (prodR (sym env (AggQueryIn.tri f 1) q₁) (symB env (AggQueryIn.tri f 2) P s m q₂))
          (SelOK.of_noAggAtom (SP.hasAggAtom_toGen _)))).castKind (projSA_kind _)
    else
      (AggQueryIn.Proj (projSA (joinLSA P 0))
        (AggQueryIn.Sel (descEqSP P 0).toGen
          (prodR (symB env (AggQueryIn.tri f 1) P s m q₁) (sym env (AggQueryIn.tri f 2) q₂))
          (SelOK.of_noAggAtom (SP.hasAggAtom_toGen _)))).castKind (projSA_kind _)
  | _, _, _, .Explode _ _ q => symB env f P s m q
  | _, _, _, .Retag _ q => symB env f P s m q
  | _, _, _, .Rel _ _ => junkB _ _ s
  | _, _, _, .Param _ _ => junkB _ _ s
  | _, _, _, .Empty => junkB _ _ s
  | _, _, _, .Apply _ _ => junkB _ _ s
  | _, _, _, .Sum _ _ => junkB _ _ s
  | _, _, _, .Dedup _ => junkB _ _ s
  | _, _, _, .Diff _ _ => junkB _ _ s
  | _, _, _, .Mu _ _ _ => junkB _ _ s
  | _, _, _, .MuSet _ _ _ => junkB _ _ s
  | _, _, _, .Gamma _ _ _ _ _ _ => junkB _ _ s
  | _, _, _, .GammaScalar _ _ _ _ => junkB _ _ s
  | _, _, _, .GammaNest _ _ _ _ _ => junkB _ _ s
  | _, _, _, .GammaTok _ _ _ _ _ _ _ => junkB _ _ s
  | _, _, _, .ProvSum _ _ _ _ => junkB _ _ s
  | _, _, _, .Win _ _ _ _ _ _ _ _ _ _ => junkB _ _ s
  | _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => junkB _ _ s
  termination_by _ _ _ q => sizeOf q

end

end Sym
