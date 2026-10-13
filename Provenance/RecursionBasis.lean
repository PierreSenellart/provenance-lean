/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.BasisAssembly

/-!
# The recursions in the classification

`sec:basis` grades the two recursion operators as it grades the others.
This module carries the row of `μ^⊎`, the recursion of SQL's `WITH
RECURSIVE … UNION ALL`: **in the minimal signature, a query without it
has at most `p(n)` tuples over an instance of `n` tuples, multiplicities
included, for a polynomial `p` of the query**, and a bag recursion breaks
that, counting the *derivations* of a tuple rather than deriving it once.

The witness is the document's: a chain of `n` diamonds, `4n` edges and no
duplicate row, over which reachability from the source reaches the sink
by `2ⁿ` paths, so the sink carries that multiplicity. The query is
`μ^⊎R.(S, Π_{#3}(σ_{#1=#2}(R × E)))`, which is SQL's

```sql
WITH RECURSIVE R(x) AS (SELECT * FROM S UNION ALL
                        SELECT E.t FROM R, E WHERE R.x = E.s)
SELECT * FROM R
```

and the rounds are the layers of the graph: the recursion's `i`-th round
holds the nodes at distance `i` from the source, each with its number of
paths, and the round past the sink is empty, which is where SQL's
iteration stops (`MuSettles`).
-/

variable {T : Type} [ValueType T]

/-! ## The instance: a chain of diamonds -/

/-- A row of arity one, written so that the rows a projection builds are
it on the nose: `Fin.cons` reduces only under a case on the index, which
would leave every computation below short of a `funext`. -/
def node (a : ℕ) : Tuple ℕ 1 := fun _ => a

/-- The schema of the witness: a source relation and an edge relation. -/
def schemaSE : Schema :=
  fun s => if s = "S" then some 1 else if s = "E" then some 2 else none

/-- **The edges of a chain of `n` diamonds.** Diamond `i` runs from `3i`
to `3(i+1)` through the two nodes `3i+1` and `3i+2`, so its four edges
are distinct, no two diamonds share an edge, and the instance holds no
duplicate row: the blow-up below is not one the instance already had. -/
def diamondEdges : ℕ → Multiset (Tuple ℕ 2)
  | 0 => 0
  | n + 1 =>
      diamondEdges n
        + ({![3 * n, 3 * n + 1], ![3 * n, 3 * n + 2],
            ![3 * n + 1, 3 * n + 3],
            ![3 * n + 2, 3 * n + 3]} : Multiset (Tuple ℕ 2))

/-- The chain has `4n` edges. -/
theorem card_diamondEdges (n : ℕ) :
    Multiset.card (diamondEdges n) = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Multiset.card (diamondEdges n
      + ({![3 * n, 3 * n + 1], ![3 * n, 3 * n + 2],
          ![3 * n + 1, 3 * n + 3],
          ![3 * n + 2, 3 * n + 3]} : Multiset (Tuple ℕ 2))) = _
    rw [Multiset.card_add, ih,
      show Multiset.card ({![3 * n, 3 * n + 1], ![3 * n, 3 * n + 2],
          ![3 * n + 1, 3 * n + 3],
          ![3 * n + 2, 3 * n + 3]} : Multiset (Tuple ℕ 2)) = 4 from rfl]
    omega

/-- **The instance**: the source `(0)` and the chain's edges. -/
def dChain (n : ℕ) : Database ℕ :=
  [("S", ⟨1, ({node 0} : Multiset (Tuple ℕ 1))⟩), ("E", ⟨2, diamondEdges n⟩)]

theorem find_dChain_S (n : ℕ) :
    (dChain n).find 1 "S" = some ({node 0} : Multiset (Tuple ℕ 1)) := by
  show Database.find.f 1 "S" (dChain n) = _
  rw [dChain, Database.find.f, dite_eq_left ⟨rfl, rfl⟩]
  rfl

theorem find_dChain_E (n : ℕ) :
    (dChain n).find 2 "E" = some (diamondEdges n) := by
  show Database.find.f 2 "E" (dChain n) = _
  rw [dChain, Database.find.f, dite_eq_right (by simp)]
  show Database.find.f 2 "E" [("E", ⟨2, diamondEdges n⟩)] = _
  rw [Database.find.f, dite_eq_left ⟨rfl, rfl⟩]
  rfl

/-- The instance has `4n + 1` rows. -/
theorem size_dChain (n : ℕ) : (dChain n).size = 4 * n + 1 := by
  rw [Database.size, dChain]
  show (1 : ℕ) + (Multiset.card (diamondEdges n) + 0) = _
  rw [card_diamondEdges]
  omega

/-! ## The query, and one round of it -/

/-- The recursion's body: `Π_{#3}(σ_{#1=#2}(R × E))`, the successors of
the previous round. -/
def reachStep : AggQueryIn ℕ 0 1 (ColKind.allReg 1) [("R", 1)] :=
  AggQueryIn.Proj (fun _ : Fin 1 =>
      ProjColIn.term (TermGIn.index (2 : Fin (1 + 2)) rfl))
    (AggQueryIn.Sel
      (GenPredIn.cmp CompOp.syneq (TermGIn.index (0 : Fin (1 + 2)) rfl)
        (TermGIn.index (1 : Fin (1 + 2)) rfl))
      (AggQueryIn.Prod (AggQueryIn.Hole 1 "R") (AggQueryIn.Rel 2 "E")))

/-- **The witness**: `μ^⊎R.(S, Π_{#3}(σ_{#1=#2}(R × E)))`. -/
def chainWitness : AggQuery ℕ 1 (ColKind.allReg 1) :=
  AggQueryIn.Mu "R" (AggQueryIn.Rel 1 "S") reachStep

/-- The successors of a node, as rows of arity one. -/
def succs (E : Multiset (Tuple ℕ 2)) (a : ℕ) : Multiset (Tuple ℕ 1) :=
  (E.filter (fun e => a = e 0)).map (fun e => node (e 1))

/-- **One round**: every row of the previous round contributes its
successors, with its own multiplicity. -/
theorem evaluatePlain_reachStep (n : ℕ) (X : Multiset (Tuple ℕ 1)) :
    reachStep.evaluatePlain ((dChain n).assign "R" X) (fun j => j.elim0)
      = X.bind (fun u => succs (diamondEdges n) (u 0)) := by
  have hR : (AggQueryIn.Rel (T := ℕ) (c := 0) 1 "R").evaluatePlain
      ((dChain n).assign "R" X) (fun j => j.elim0) = X := by
    show (match ((dChain n).assign "R" X).find 1 "R" with
      | none => (0 : Multiset (Tuple ℕ 1)) | some r => r) = _
    rw [Database.find_assign]
  have hE : (AggQueryIn.Rel (T := ℕ) (c := 0) 2 "E").evaluatePlain
      ((dChain n).assign "R" X) (fun j => j.elim0) = diamondEdges n := by
    show (match ((dChain n).assign "R" X).find 2 "E" with
      | none => (0 : Multiset (Tuple ℕ 2)) | some r => r) = _
    rw [Database.find_assign_of_ne "R" "E" X (dChain n) (by simp),
      find_dChain_E]
  show Multiset.map (fun w : Tuple ℕ (1 + 2) => (fun _ : Fin 1 =>
        (ProjColIn.term (TermGIn.index (2 : Fin (1 + 2)) rfl)).evalPlain w
          (fun j => j.elim0)) : Tuple ℕ (1 + 2) → Tuple ℕ 1)
      (Multiset.filter (fun w : Tuple ℕ (1 + 2) =>
          (GenPredIn.cmp CompOp.syneq (TermGIn.index (0 : Fin (1 + 2)) rfl)
            (TermGIn.index (1 : Fin (1 + 2)) rfl)).holdsPlain w
              (fun j => j.elim0))
        ((AggQueryIn.Rel (T := ℕ) (c := 0) 1 "R").evaluatePlain
            ((dChain n).assign "R" X) (fun j => j.elim0)
          * (AggQueryIn.Rel (T := ℕ) (c := 0) 2 "E").evaluatePlain
            ((dChain n).assign "R" X) (fun j => j.elim0))) = _
  rw [hR, hE, Relation.hMul_eq_bind, Multiset.filter_bind, Multiset.map_bind]
  refine Multiset.bind_congr (fun u _ => ?_)
  rw [Multiset.filter_map, Multiset.map_map, succs]
  refine congrArg₂ Multiset.map rfl ?_
  refine Multiset.filter_congr (fun e _ => ?_)
  show (CompOp.syneq.eval3 (u 0) (e 0) = Kleene.true) ↔ _
  rw [CompOp.syneq_eval3_eq_true_iff]

/-! ## The successors of a node in the chain -/

/-- The four edges of diamond `i`. -/
def diamond (i : ℕ) : Multiset (Tuple ℕ 2) :=
  {![3 * i, 3 * i + 1], ![3 * i, 3 * i + 2],
    ![3 * i + 1, 3 * i + 3], ![3 * i + 2, 3 * i + 3]}

theorem diamondEdges_succ (n : ℕ) :
    diamondEdges (n + 1) = diamondEdges n + diamond n := rfl

theorem succs_add (E F : Multiset (Tuple ℕ 2)) (a : ℕ) :
    succs (E + F) a = succs E a + succs F a := by
  rw [succs, succs, succs, Multiset.filter_add, Multiset.map_add]

/-- A node outside diamond `j`'s sources has no successor there. -/
private theorem succs_diamond_of_ne {j a : ℕ} (h0 : a ≠ 3 * j)
    (h1 : a ≠ 3 * j + 1) (h2 : a ≠ 3 * j + 2) : succs (diamond j) a = 0 := by
  unfold succs diamond
  simp only [Multiset.insert_eq_cons]
  rw [Multiset.filter_cons_of_neg _ (by simpa using h0),
    Multiset.filter_cons_of_neg _ (by simpa using h0),
    Multiset.filter_cons_of_neg _ (by simpa using h1),
    Multiset.filter_singleton, ite_eq_right (by simpa using h2)]
  rfl

/-- The entry node of diamond `i` branches to its two sides. -/
private theorem succs_diamond_v (i : ℕ) :
    succs (diamond i) (3 * i)
      = ({node (3 * i + 1), node (3 * i + 2)} : Multiset (Tuple ℕ 1)) := by
  unfold succs diamond
  simp only [Multiset.insert_eq_cons]
  rw [Multiset.filter_cons_of_pos _ (by simp),
    Multiset.filter_cons_of_pos _ (by simp),
    Multiset.filter_cons_of_neg _ (by simp),
    Multiset.filter_singleton, ite_eq_right (by simp)]
  rfl

/-- And each side leads to the exit node. -/
private theorem succs_diamond_a (i : ℕ) :
    succs (diamond i) (3 * i + 1)
      = ({node (3 * i + 3)} : Multiset (Tuple ℕ 1)) := by
  unfold succs diamond
  simp only [Multiset.insert_eq_cons]
  rw [Multiset.filter_cons_of_neg _ (by simp),
    Multiset.filter_cons_of_neg _ (by simp),
    Multiset.filter_cons_of_pos _ (by simp),
    Multiset.filter_singleton, ite_eq_right (by simp)]
  rfl

private theorem succs_diamond_b (i : ℕ) :
    succs (diamond i) (3 * i + 2)
      = ({node (3 * i + 3)} : Multiset (Tuple ℕ 1)) := by
  unfold succs diamond
  simp only [Multiset.insert_eq_cons]
  rw [Multiset.filter_cons_of_neg _ (by simp),
    Multiset.filter_cons_of_neg _ (by simp),
    Multiset.filter_cons_of_neg _ (by simp),
    Multiset.filter_singleton, ite_eq_left (by simp)]
  rfl

/-- **Past the chain there is nothing**: the nodes of the first `m`
diamonds are below `3m`, so no edge leaves a node from there on. -/
theorem succs_chain_eq_zero_of_ge {m a : ℕ} (h : 3 * m ≤ a) :
    succs (diamondEdges m) a = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [diamondEdges_succ, succs_add, ih (by omega),
      succs_diamond_of_ne (by omega) (by omega) (by omega)]
    rfl

/-- **The entry node of diamond `i` branches**, in the chain of `n`. -/
theorem succs_chain_v {i n : ℕ} (h : i < n) :
    succs (diamondEdges n) (3 * i)
      = ({node (3 * i + 1), node (3 * i + 2)} : Multiset (Tuple ℕ 1)) := by
  induction n with
  | zero => exact absurd h (by omega)
  | succ m ih =>
    rw [diamondEdges_succ, succs_add]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · rw [ih hlt, succs_diamond_of_ne (by omega) (by omega) (by omega),
        add_zero]
    · rw [succs_chain_eq_zero_of_ge (le_refl (3 * i)), succs_diamond_v,
        zero_add]

/-- **And each side of it leads to the exit node.** -/
theorem succs_chain_a {i n : ℕ} (h : i < n) :
    succs (diamondEdges n) (3 * i + 1)
      = ({node (3 * i + 3)} : Multiset (Tuple ℕ 1)) := by
  induction n with
  | zero => exact absurd h (by omega)
  | succ m ih =>
    rw [diamondEdges_succ, succs_add]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · rw [ih hlt, succs_diamond_of_ne (by omega) (by omega) (by omega),
        add_zero]
    · rw [succs_chain_eq_zero_of_ge (by omega), succs_diamond_a, zero_add]

theorem succs_chain_b {i n : ℕ} (h : i < n) :
    succs (diamondEdges n) (3 * i + 2)
      = ({node (3 * i + 3)} : Multiset (Tuple ℕ 1)) := by
  induction n with
  | zero => exact absurd h (by omega)
  | succ m ih =>
    rw [diamondEdges_succ, succs_add]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · rw [ih hlt, succs_diamond_of_ne (by omega) (by omega) (by omega),
        add_zero]
    · rw [succs_chain_eq_zero_of_ge (by omega), succs_diamond_b, zero_add]

/-! ## The rounds are the layers of the chain -/

/-- Binding a bag of copies of one row. -/
theorem bind_replicate {α β : Type} (k : ℕ) (x : α) (f : α → Multiset β) :
    (Multiset.replicate k x).bind f = k • f x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Multiset.replicate_succ, Multiset.cons_bind, ih, succ_nsmul']

/-- The round function of the witness over the chain of `n` diamonds. -/
noncomputable def chainStep (n : ℕ) :
    Multiset (Tuple ℕ 1) → Multiset (Tuple ℕ 1) :=
  fun X => reachStep.evaluatePlain ((dChain n).assign "R" X) (fun j => j.elim0)

theorem chainStep_eq (n : ℕ) (X : Multiset (Tuple ℕ 1)) :
    chainStep n X = X.bind (fun u => succs (diamondEdges n) (u 0)) :=
  evaluatePlain_reachStep n X

theorem chainStep_zero (n : ℕ) : chainStep n 0 = 0 := by
  rw [chainStep_eq]
  rfl

/-- One round over a bag of copies of one node. -/
theorem chainStep_replicate (n k a : ℕ) :
    chainStep n (Multiset.replicate k (node a))
      = k • succs (diamondEdges n) a := by
  rw [chainStep_eq, bind_replicate]
  rfl

theorem chainStep_add (n : ℕ) (X Y : Multiset (Tuple ℕ 1)) :
    chainStep n (X + Y) = chainStep n X + chainStep n Y := by
  rw [chainStep_eq, chainStep_eq, chainStep_eq, Multiset.add_bind]

/-- A bag of copies of two rows. -/
private theorem nsmul_pair {α : Type} (k : ℕ) (a b : α) :
    k • ({a, b} : Multiset α)
      = Multiset.replicate k a + Multiset.replicate k b := by
  rw [show ({a, b} : Multiset α) = {a} + {b} from (Multiset.singleton_add a _).symm,
    nsmul_add, Multiset.nsmul_singleton, Multiset.nsmul_singleton]

/-- **The even rounds**: the entry node of diamond `i`, with one copy per
path to it – `2ⁱ` of them, the diamonds doubling the count. -/
theorem chainStep_iterate_even {n : ℕ} : ∀ i : ℕ, i ≤ n →
    (chainStep n)^[2 * i] ({node 0} : Multiset (Tuple ℕ 1))
      = Multiset.replicate (2 ^ i) (node (3 * i)) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    have hi : i < n := by omega
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by omega,
      Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (by omega), chainStep_replicate, succs_chain_v hi, nsmul_pair,
      chainStep_add, chainStep_replicate, chainStep_replicate,
      succs_chain_a hi, succs_chain_b hi, Multiset.nsmul_singleton,
      ← Multiset.replicate_add,
      show 2 ^ i + 2 ^ i = 2 ^ (i + 1) from by ring,
      show 3 * i + 3 = 3 * (i + 1) from by ring]

/-- **The odd rounds**: the two sides of diamond `i`. -/
theorem chainStep_iterate_odd {n : ℕ} (i : ℕ) (h : i < n) :
    (chainStep n)^[2 * i + 1] ({node 0} : Multiset (Tuple ℕ 1))
      = Multiset.replicate (2 ^ i) (node (3 * i + 1))
        + Multiset.replicate (2 ^ i) (node (3 * i + 2)) := by
  rw [Function.iterate_succ_apply', chainStep_iterate_even i (by omega),
    chainStep_replicate, succs_chain_v h, nsmul_pair]

/-- **And the round past the sink is empty**, which is where SQL's
iteration stops. -/
theorem chainStep_iterate_eq_zero {n j : ℕ} (h : 2 * n + 1 ≤ j) :
    (chainStep n)^[j] ({node 0} : Multiset (Tuple ℕ 1)) = 0 := by
  refine iterate_eq_zero_of_le (chainStep_zero n) ?_ h
  rw [Function.iterate_succ_apply', chainStep_iterate_even n (le_refl n),
    chainStep_replicate, succs_chain_eq_zero_of_ge (le_refl (3 * n))]
  simp

/-- **The recursion settles**: the graph is acyclic, so the rounds end. -/
theorem muSettles_chain (n : ℕ) :
    MuSettles (chainStep n) ({node 0} : Multiset (Tuple ℕ 1)) :=
  ⟨2 * n, chainStep_iterate_eq_zero (by omega)⟩

/-! ## The sink's multiplicity -/

theorem node_inj {a b : ℕ} (h : node a = node b) : a = b := congrFun h 0

@[simp] theorem node_eq_iff {a b : ℕ} : node a = node b ↔ a = b :=
  ⟨node_inj, fun h => by rw [h]⟩

/-- **The sink is reached in the last round only**, by `2ⁿ` paths. -/
theorem count_chainStep_iterate (n j : ℕ) :
    Multiset.count (node (3 * n))
        ((chainStep n)^[j] ({node 0} : Multiset (Tuple ℕ 1)))
      = if j = 2 * n then 2 ^ n else 0 := by
  rcases lt_or_ge j (2 * n + 1) with hlt | hge
  · rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hj : j = 2 * i := by omega
      subst hj
      rw [chainStep_iterate_even i (by omega), Multiset.count_replicate]
      by_cases hin : i = n
      · subst hin
        rw [ite_eq_left (by simp), ite_eq_left rfl]
      · rw [ite_eq_right (by simp; omega), ite_eq_right (by omega)]
    · subst hi
      rw [chainStep_iterate_odd i (by omega), Multiset.count_add,
        Multiset.count_replicate, Multiset.count_replicate,
        ite_eq_right (by simp; omega), ite_eq_right (by simp; omega),
        ite_eq_right (by omega)]
  · rw [chainStep_iterate_eq_zero hge, ite_eq_right (by omega)]
    rfl

/-- Every round up to the sink's is non-empty. -/
theorem chainStep_iterate_ne_zero {n j : ℕ} (h : j ≤ 2 * n) :
    (chainStep n)^[j] ({node 0} : Multiset (Tuple ℕ 1)) ≠ 0 := by
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hj : j = 2 * i := by omega
    subst hj
    rw [chainStep_iterate_even i (by omega)]
    refine fun hc => absurd (Multiset.card_eq_zero.mpr hc) ?_
    rw [Multiset.card_replicate]
    simp
  · subst hi
    rw [chainStep_iterate_odd i (by omega)]
    refine fun hc => absurd (Multiset.card_eq_zero.mpr hc) ?_
    rw [Multiset.card_add, Multiset.card_replicate, Multiset.card_replicate]
    simp

/-- So the recursion runs at least to it. -/
theorem le_muRounds_chain (n : ℕ) :
    2 * n ≤ muRounds (chainStep n) ({node 0} : Multiset (Tuple ℕ 1)) := by
  have hne : {k | (chainStep n)^[k + 1] ({node 0} : Multiset (Tuple ℕ 1)) = 0}.Nonempty :=
    ⟨2 * n, chainStep_iterate_eq_zero (by omega)⟩
  refine Nat.le_of_not_lt (fun hlt => ?_)
  exact absurd (Nat.sInf_mem hne)
    (chainStep_iterate_ne_zero (n := n) (j := muRounds (chainStep n) _ + 1)
      (by omega))

/-! ## The row: no polynomial bounds a bag recursion -/

theorem count_muSum (n b : ℕ) :
    Multiset.count (node (3 * n))
        (muSum (chainStep n) b ({node 0} : Multiset (Tuple ℕ 1)))
      = if 2 * n ≤ b then 2 ^ n else 0 := by
  induction b with
  | zero =>
    show Multiset.count (node (3 * n)) ({node 0} : Multiset (Tuple ℕ 1)) = _
    by_cases hn : n = 0
    · subst hn
      rw [ite_eq_left (by omega), Multiset.count_singleton,
        ite_eq_left (by rfl)]
      rfl
    · rw [ite_eq_right (by omega), Multiset.count_singleton,
        ite_eq_right (by simp; omega)]
  | succ b ih =>
    rw [muSum_succ, Multiset.count_add, ih, count_chainStep_iterate]
    split_ifs <;> omega

/-- **The sink of the chain carries `2ⁿ` copies**: one per path through
the `n` diamonds, which is what a bag recursion counts. -/
theorem count_chainWitness (n : ℕ) :
    Multiset.count (node (3 * n))
        (chainWitness.evaluatePlain (dChain n) (fun j => j.elim0)) = 2 ^ n := by
  have hS : (AggQueryIn.Rel (T := ℕ) (c := 0) 1 "S").evaluatePlain (dChain n)
      (fun j => j.elim0) = ({node 0} : Multiset (Tuple ℕ 1)) := by
    show (match (dChain n).find 1 "S" with
      | none => (0 : Multiset (Tuple ℕ 1)) | some r => r) = _
    rw [find_dChain_S]
  show Multiset.count (node (3 * n))
      (muSumFix (chainStep n)
        ((AggQueryIn.Rel (T := ℕ) (c := 0) 1 "S").evaluatePlain (dChain n)
          (fun j => j.elim0))) = _
  rw [hS, muSumFix, count_muSum, ite_eq_left (le_muRounds_chain n)]

/-- Hence the result has at least `2ⁿ` rows. -/
theorem le_card_chainWitness (n : ℕ) :
    2 ^ n ≤ Multiset.card
      (chainWitness.evaluatePlain (dChain n) (fun j => j.elim0)) := by
  rw [← count_chainWitness n]
  exact Multiset.count_le_card _ _

/-- `m² ≤ 2^m` from `m = 4` on. -/
private theorem sq_le_two_pow {m : ℕ} (h : 4 ≤ m) : m ^ 2 ≤ 2 ^ m := by
  induction m, h using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hsq : 4 * m ≤ m * m := Nat.mul_le_mul_right m hm
    have h2 : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
    have h3 : m ^ 2 = m * m := by ring
    rw [h2, pow_succ]
    rw [h3] at ih
    omega

/-- **No polynomial catches `2ⁿ`**, the instance of the chain of `n`
diamonds having `4n + 1` rows. -/
private theorem exists_lt_two_pow (c k : ℕ) :
    ∃ n : ℕ, c * (4 * n + 2) ^ k < 2 ^ n := by
  refine ⟨(k + 1) * max 4 (max (c + 1) (4 * (k + 1) + 2)), ?_⟩
  set m := max 4 (max (c + 1) (4 * (k + 1) + 2)) with hmdef
  have hm4 : 4 ≤ m := le_max_left _ _
  have hmc : c + 1 ≤ m :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hmk : 4 * (k + 1) + 2 ≤ m :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hA : 4 * ((k + 1) * m) + 2 ≤ 2 ^ m := by
    refine le_trans ?_ (sq_le_two_pow hm4)
    have hmm : (4 * (k + 1) + 2) * m ≤ m * m := Nat.mul_le_mul_right m hmk
    have h2 : m ^ 2 = m * m := by ring
    have hexp : (4 * (k + 1) + 2) * m = 4 * ((k + 1) * m) + 2 * m := by ring
    rw [h2]
    omega
  have hc : c < 2 ^ m :=
    lt_of_lt_of_le (by omega) (le_of_lt (Nat.lt_two_pow_self))
  calc c * (4 * ((k + 1) * m) + 2) ^ k
      ≤ c * (2 ^ m) ^ k := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hA k)
    _ < 2 ^ m * (2 ^ m) ^ k := by
        rw [← pow_mul]
        exact (Nat.mul_lt_mul_right (Nat.two_pow_pos (m * k))).mpr hc
    _ = 2 ^ ((k + 1) * m) := by
        rw [← pow_mul, ← pow_add, show m + m * k = (k + 1) * m from by ring]

/-- **`μ^⊎` is in every basis** (`tab:basisclasses`'s row): a bag
recursion counts the *derivations* of a tuple, and over the chain of `n`
diamonds – `4n + 1` rows, none of them duplicated – the sink has `2ⁿ` of
them, which no polynomial in the size of the instance bounds. Every
other operator of the minimal signature keeps the result polynomial. -/
theorem chainWitness_no_polynomial_bound :
    ¬ ∃ c k : ℕ, ∀ n : ℕ,
      Multiset.card (chainWitness.evaluatePlain (dChain n) (fun j => j.elim0))
        ≤ c * ((dChain n).size + 1) ^ k := by
  rintro ⟨c, k, h⟩
  obtain ⟨n, hn⟩ := exists_lt_two_pow c k
  have hb := h n
  rw [size_dChain, show 4 * n + 1 + 1 = 4 * n + 2 from by omega] at hb
  exact absurd (le_trans (le_card_chainWitness n) hb) (not_le.mpr hn)

/-! ## Half of the invariant: the operators that are not a recursion

`tab:basisclasses`'s `μ^⊎` row is the *invariant* that a query without
it has at most `p(n)` tuples over an instance of `n` tuples,
multiplicities included. The operators other than the two recursions
bound their result by sums and products of the bounds of their
arguments, in numbers fixed by the query, and an apply by the bound of
its left side times that of its right side – which does not depend on
the parameters, so the bound is uniform in the context. That is this
section; the set recursion is the other half, and is where the minimal
signature comes in.
-/

/-- **No recursion.** -/
def AggQueryIn.noRec : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noRec
  | _, _, _, _, .Sel _ q _ => q.noRec
  | _, _, _, _, .Prod q₁ q₂ => q₁.noRec ∧ q₂.noRec
  | _, _, _, _, .Apply q₁ q₂ => q₁.noRec ∧ q₂.noRec
  | _, _, _, _, .Sum q₁ q₂ => q₁.noRec ∧ q₂.noRec
  | _, _, _, _, .Dedup q => q.noRec
  | _, _, _, _, .Diff q₁ q₂ => q₁.noRec ∧ q₂.noRec
  | _, _, _, _, .Alt _ _ q => q.noRec
  | _, _, _, _, .Mu _ _ _ => False
  | _, _, _, _, .MuSet _ _ _ => False
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noRec
  | _, _, _, _, .GammaScalar _ _ q _ => q.noRec
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noRec
  | _, _, _, _, .ProvSum _ _ _ q => q.noRec
  | _, _, _, _, .Retag _ q => q.noRec
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noRec
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noRec
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noRec

/-- Raising the degree only weakens a bound. -/
private theorem poly_le_poly {b k k' m : ℕ} (h : k ≤ k') :
    b * (m + 1) ^ k ≤ b * (m + 1) ^ k' :=
  Nat.mul_le_mul_left b (Nat.pow_le_pow_right (by omega) h)

/-- **A recursion-free query has polynomially many rows**, multiplicities
included, and the polynomial is uniform in the context: an apply's right
side is bounded independently of the parameters it reads. -/
theorem AggQueryIn.exists_polyBound :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l), q.noRec →
      ∃ b k : ℕ, ∀ (D : Database T) (γ : Fin c → T),
        Multiset.card (q.evaluatePlain D γ) ≤ b * (D.size + 1) ^ k := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    refine fun _ => ⟨1, 1, fun D γ => ?_⟩
    show Multiset.card (match D.find n s with
      | none => (0 : Relation T n) | some rn => rn) ≤ _
    cases hf : D.find n s with
    | none => exact Nat.zero_le _
    | some rn =>
      refine le_trans (Database.card_le_size D hf) ?_
      rw [pow_one, one_mul]
      omega
  | Hole n s =>
    refine fun _ => ⟨1, 1, fun D γ => ?_⟩
    show Multiset.card (match D.find n s with
      | none => (0 : Relation T n) | some rn => rn) ≤ _
    cases hf : D.find n s with
    | none => exact Nat.zero_le _
    | some rn =>
      refine le_trans (Database.card_le_size D hf) ?_
      rw [pow_one, one_mul]
      omega
  | Empty => exact fun _ => ⟨0, 0, fun _ _ => Nat.zero_le _⟩
  | Proj ps q ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => by
      show Multiset.card (Multiset.map _ (q.evaluatePlain D γ)) ≤ _
      rw [Multiset.card_map]; exact hb D γ⟩
  | Sel φ q _ ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => le_trans
      (Multiset.card_le_card (Multiset.filter_le _ _)) (hb D γ)⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    refine fun hq => ?_
    obtain ⟨b₁, k₁, hb₁⟩ := ih₁ hq.1
    obtain ⟨b₂, k₂, hb₂⟩ := ih₂ hq.2
    refine ⟨b₁ * b₂, k₁ + k₂, fun D γ => ?_⟩
    show Multiset.card (q₁.evaluatePlain D γ * q₂.evaluatePlain D γ) ≤ _
    rw [Relation.card_hMul, pow_add,
      show b₁ * b₂ * ((D.size + 1) ^ k₁ * (D.size + 1) ^ k₂)
        = b₁ * (D.size + 1) ^ k₁ * (b₂ * (D.size + 1) ^ k₂) from by ring]
    exact Nat.mul_le_mul (hb₁ D γ) (hb₂ D γ)
  | Apply q₁ q₂ ih₁ ih₂ =>
    refine fun hq => ?_
    obtain ⟨b₁, k₁, hb₁⟩ := ih₁ hq.1
    obtain ⟨b₂, k₂, hb₂⟩ := ih₂ hq.2
    refine ⟨b₁ * b₂, k₁ + k₂, fun D γ => ?_⟩
    show Multiset.card ((q₁.evaluatePlain D γ).bind (fun u =>
      Multiset.map _ (q₂.evaluatePlain D (Fin.append u γ)))) ≤ _
    rw [Multiset.card_bind, pow_add,
      show b₁ * b₂ * ((D.size + 1) ^ k₁ * (D.size + 1) ^ k₂)
        = b₁ * (D.size + 1) ^ k₁ * (b₂ * (D.size + 1) ^ k₂) from by ring]
    refine le_trans (Multiset.sum_le_card_nsmul _ (b₂ * (D.size + 1) ^ k₂)
      (fun x hx => ?_)) ?_
    · obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hx
      show Multiset.card (Multiset.map (fun v => Fin.append u v)
        (q₂.evaluatePlain D (Fin.append u γ))) ≤ _
      rw [Multiset.card_map]
      exact hb₂ D (Fin.append u γ)
    · rw [smul_eq_mul, Multiset.card_map]
      exact Nat.mul_le_mul_right _ (hb₁ D γ)
  | Sum q₁ q₂ ih₁ ih₂ =>
    refine fun hq => ?_
    obtain ⟨b₁, k₁, hb₁⟩ := ih₁ hq.1
    obtain ⟨b₂, k₂, hb₂⟩ := ih₂ hq.2
    refine ⟨b₁ + b₂, max k₁ k₂, fun D γ => ?_⟩
    show Multiset.card (q₁.evaluatePlain D γ + q₂.evaluatePlain D γ) ≤ _
    rw [Relation.card_add, Nat.add_mul]
    exact Nat.add_le_add
      (le_trans (hb₁ D γ) (poly_le_poly (le_max_left _ _)))
      (le_trans (hb₂ D γ) (poly_le_poly (le_max_right _ _)))
  | Dedup q ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => le_trans (Multiset.card_dedup_le _) (hb D γ)⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih₁ hq.1
    exact ⟨b, k, fun D γ => le_trans
      (Multiset.card_le_card (Multiset.filter_le _ _)) (hb D γ)⟩
  | Alt k hk q ih => exact fun hq => ih hq
  | Retag hk q ih => exact fun hq => ih hq
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | Gamma is ts fs q keep ord ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => by
      show Multiset.card (Multiset.map _ (Multiset.dedup
        (Multiset.map _ (q.evaluatePlain D γ)))) ≤ _
      rw [Multiset.card_map]
      exact le_trans (le_trans (Multiset.card_dedup_le _)
        (le_of_eq (Multiset.card_map _ _))) (hb D γ)⟩
  | GammaScalar ts fs q ord ih =>
    refine fun _ => ⟨1, 0, fun D γ => ?_⟩
    show Multiset.card (Multiset.ofList [_]) ≤ _
    rw [pow_zero, one_mul]
    rfl
  | GammaNest is his p f q ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => by
      show Multiset.card (Multiset.map _ (Multiset.dedup
        (Multiset.map _ (q.evaluatePlain D γ)))) ≤ _
      rw [Multiset.card_map]
      exact le_trans (le_trans (Multiset.card_dedup_le _)
        (le_of_eq (Multiset.card_map _ _))) (hb D γ)⟩
  | ProvSum is his t q ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => by
      show Multiset.card (Multiset.map _ (Multiset.dedup
        (Multiset.map _ (q.evaluatePlain D γ)))) ≤ _
      rw [Multiset.card_map]
      exact le_trans (le_trans (Multiset.card_dedup_le _)
        (le_of_eq (Multiset.card_map _ _))) (hb D γ)⟩
  | GammaTok is his ts fs a q keep ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => by
      show Multiset.card (Multiset.map _ (Multiset.dedup
        (Multiset.map _ (q.evaluatePlain D γ)))) ≤ _
      rw [Multiset.card_map]
      exact le_trans (le_trans (Multiset.card_dedup_le _)
        (le_of_eq (Multiset.card_map _ _))) (hb D γ)⟩
  | Win P O o w t f q hrr dist keep ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => by
      show Multiset.card (Multiset.map _ (q.evaluatePlain D γ)) ≤ _
      rw [Multiset.card_map]; exact hb D γ⟩
  | WinExpr P O o ws ts fs g q keeps ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => by
      show Multiset.card (OccFam.toMultiset _) ≤ _
      rw [OccFam.card_toMultiset]
      exact le_trans (le_of_eq (OccFam.size_ofSorted _)) (hb D γ)⟩

/-! ## What the values of a result can be

`tab:basisclasses`'s `μ^⊎` row reads the *values* of a result, not only
its size: in the minimal signature a value is one of the instance, a
constant of the query, or a count, and a count is bounded by the size of
what it counts. That is what bounds a **set** recursion, whose fixpoint
has no bound in terms of its arguments': a duplicate-free relation of
arity `k` over `|V|` values has at most `|V|^k` rows.
-/

/-- Every value of the relation lies in `V`. The argument is spelled as
a multiset and not as a `Relation`, which is an opaque `def` that
instance search for `∈` and `≤` cannot see through. -/
def Relation.valsIn {n : ℕ} (r : Multiset (Tuple T n)) (V : Finset T) :
    Prop :=
  ∀ u ∈ r, ∀ j, u j ∈ V

omit [ValueType T] in
theorem Relation.valsIn_of_le {n : ℕ} {r r' : Multiset (Tuple T n)}
    {V : Finset T} (h : r ≤ r') (hr' : Relation.valsIn r' V) :
    Relation.valsIn r V :=
  fun u hu j => hr' u (Multiset.mem_of_le h hu) j

/-- **An aggregate that is a count**: its value is a function of the
number of non-null values it reads, which is what the minimal signature
has in place of an arbitrary aggregate. -/
def SeqAggFunc.IsCount (cnt : SeqAggFunc T) : Prop :=
  ∃ g : ℕ → T,
    ∀ L : List T, cnt L = g (L.countP (fun x => !ValueType.isNull x))

/-- The values a count can take over a sequence of at most `m` values. -/
def countVals (g : ℕ → T) (m : ℕ) : Finset T := (Finset.range (m + 1)).image g

theorem mem_countVals {g : ℕ → T} {m : ℕ} {i : ℕ} (h : i ≤ m) :
    g i ∈ countVals g m :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

theorem countVals_subset {g : ℕ → T} {m m' : ℕ} (h : m ≤ m') :
    countVals g m ⊆ countVals g m' :=
  Finset.image_subset_image (fun i hi => Finset.mem_range.mpr
    (by have := Finset.mem_range.mp hi; omega))

/-- **A group is no larger than its relation**, clause and `ORDER BY`
included: both read a listing of a part of it. -/
theorem length_groupSeqOptOrd_le {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (ord : GroupOrder T m) (r : Multiset (Tuple T m)) (g : Tuple T n₁)
    (keep : Option (Selection T m)) :
    (Relation.groupSeqOptOrd is ord r g keep).length ≤ Multiset.card r := by
  have hbase : (Relation.groupSeq is r g).length ≤ Multiset.card r := by
    rw [Relation.groupSeq, length_sortList]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have hord : (Relation.groupSeqOrd is ord r g).length ≤ Multiset.card r :=
    le_trans (le_of_eq (Relation.groupSeqOrd_perm is ord r g).length_eq) hbase
  cases keep with
  | none => exact hord
  | some φ => exact le_trans (List.length_filter_le _ _) hord

/-- Erasing a row leaves no more. The decidable equality is an explicit
argument: the frame machinery's comes from the domain's order, where
instance search finds the pointwise one. -/
private theorem card_erase_le' {α : Type} (i : DecidableEq α)
    (s : Multiset α) (a : α) :
    Multiset.card (@Multiset.erase α i s a) ≤ Multiset.card s :=
  Multiset.card_le_card (@Multiset.erase_le α i a s)

/-- And consing it back adds at most one. -/
private theorem card_cons_erase_le {α : Type} (i : DecidableEq α)
    (s : Multiset α) (a : α) :
    Multiset.card (a ::ₘ @Multiset.erase α i s a) ≤ Multiset.card s + 1 := by
  rw [Multiset.card_cons]
  exact Nat.add_le_add_right (card_erase_le' i s a) 1

/-- **And a frame is no larger than its relation and the current row.**
The row itself is in its frame or not, which is the `+ 1`. -/
theorem length_frameListOf_le {n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (X : Multiset (Tuple T n)) (x : Tuple T n) :
    (ValueFrame.frameListOf (α := Tuple T n) id P O o w X x).length
      ≤ Multiset.card X + 1 := by
  rw [ValueFrame.frameListOf]
  refine le_trans (le_of_eq (OrderSpec.sortSeq_perm _).length_eq) ?_
  rw [length_sortList]
  unfold ValueFrame.frameOf
  by_cases hs : w.s (Tuple.key O (id x)) = true
  · rw [ite_eq_left hs]
    refine le_trans (card_cons_erase_le _ _ x) ?_
    exact Nat.add_le_add_right
      (Multiset.card_le_card (Multiset.filter_le _ X)) 1
  · rw [ite_eq_right hs]
    refine le_trans (card_erase_le' _ _ x) ?_
    exact le_trans (Multiset.card_le_card (Multiset.filter_le _ X))
      (Nat.le_succ _)

/-! ### Where the values of a recursion-free result lie -/

private theorem poly_mono {b₁ b k₁ k m : ℕ} (hb : b₁ ≤ b) (hk : k₁ ≤ k) :
    b₁ * (m + 1) ^ k₁ ≤ b * (m + 1) ^ k :=
  Nat.mul_le_mul hb (Nat.pow_le_pow_right (by omega) hk)

omit [ValueType T] in
private theorem append_mem {V : Finset T} {n₁ n₂ : ℕ} {u : Tuple T n₁}
    {v : Tuple T n₂} (hu : ∀ j, u j ∈ V) (hv : ∀ j, v j ∈ V) :
    ∀ j, (Fin.append u v : Tuple T (n₁ + n₂)) j ∈ V := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]; exact hu i
  · rw [Fin.append_right]; exact hv i

omit [ValueType T] in
private theorem snoc_mem {V : Finset T} {n : ℕ} {u : Tuple T n} {a : T}
    (hu : ∀ j, u j ∈ V) (ha : a ∈ V) :
    ∀ j, (Fin.snoc u a : Tuple T (n + 1)) j ∈ V := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]; exact ha
  · rw [Fin.snoc_castSucc]; exact hu i

/-- A count over a sequence no longer than `m` is one of the values a
count takes there. -/
private theorem count_mem_countVals {cnt : SeqAggFunc T} {g : ℕ → T}
    (hg : ∀ L : List T, cnt L = g (L.countP (fun x => !ValueType.isNull x)))
    {L : List T} {m : ℕ} (h : L.length ≤ m) : cnt L ∈ countVals g m := by
  rw [hg L]
  exact mem_countVals (le_trans List.countP_le_length h)

/-- **The values of a recursion-free result**: in the minimal signature
they are values of the instance, values the context supplies, constants
of the query, or counts – and a count is bounded by the size of what it
counts, which `AggQueryIn.exists_polyBound` bounds by a polynomial. -/
theorem AggQueryIn.exists_valsIn {cnt : SeqAggFunc T} {g : ℕ → T}
    (hg : ∀ L : List T, cnt L = g (L.countP (fun x => !ValueType.isNull x))) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noRec → q.inSig {cnt} →
      ∃ b k : ℕ, ∀ (D : Database T) (γ : Fin c → T) (V : Finset T),
        (∀ (m : ℕ) (s : String) (r : Relation T m), D.find m s = some r →
            Relation.valsIn r V) →
        (∀ j, γ j ∈ V) → q.constsIn V →
        countVals g (b * (D.size + 1) ^ k) ⊆ V →
        Relation.valsIn (q.evaluatePlain D γ) V := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    refine fun _ _ => ⟨0, 0, fun D γ V hD _ _ _ => ?_⟩
    show Relation.valsIn (match D.find n s with
      | none => (0 : Relation T n) | some rn => rn) V
    cases hf : D.find n s with
    | none => exact fun u hu => absurd hu (by simp)
    | some rn => exact hD n s rn hf
  | Hole n s =>
    refine fun _ _ => ⟨0, 0, fun D γ V hD _ _ _ => ?_⟩
    show Relation.valsIn (match D.find n s with
      | none => (0 : Relation T n) | some rn => rn) V
    cases hf : D.find n s with
    | none => exact fun u hu => absurd hu (by simp)
    | some rn => exact hD n s rn hf
  | Empty =>
    refine fun _ _ => ⟨0, 0, fun _ _ _ _ _ _ _ u hu => ?_⟩
    exact absurd (show u ∈ (0 : Multiset (Tuple T 0)) from hu) (by simp)
  | Proj ps q ih =>
    refine fun hq hs => ?_
    obtain ⟨b, k, hb⟩ := ih hq hs.2
    refine ⟨b, k, fun D γ V hD hγ hc hV u hu j => ?_⟩
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hu
    exact (ps j).evalPlain_mem_of_noFun (hs.1 j) (hc.1 j) v
      (fun i => hb D γ V hD hγ hc.2 hV v hv i) γ hγ
  | Sel φ q _ ih =>
    refine fun hq hs => ?_
    obtain ⟨b, k, hb⟩ := ih hq hs.2
    exact ⟨b, k, fun D γ V hD hγ hc hV =>
      Relation.valsIn_of_le (Multiset.filter_le _ _) (hb D γ V hD hγ hc hV)⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    refine fun hq hs => ?_
    obtain ⟨b₁, k₁, hb₁⟩ := ih₁ hq.1 hs.1
    obtain ⟨b₂, k₂, hb₂⟩ := ih₂ hq.2 hs.2
    refine ⟨b₁ + b₂, max k₁ k₂, fun D γ V hD hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain, Relation.hMul_eq_bind] at hu
    obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
    refine append_mem (hb₁ D γ V hD hγ hc.1 ?_ v hv)
      (hb₂ D γ V hD hγ hc.2 ?_ w hw)
    · exact le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV
    · exact le_trans (countVals_subset
        (poly_mono (by omega) (le_max_right _ _))) hV
  | Apply q₁ q₂ ih₁ ih₂ =>
    refine fun hq hs => ?_
    obtain ⟨b₁, k₁, hb₁⟩ := ih₁ hq.1 hs.1
    obtain ⟨b₂, k₂, hb₂⟩ := ih₂ hq.2 hs.2
    refine ⟨b₁ + b₂, max k₁ k₂, fun D γ V hD hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain] at hu
    obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
    have hv' : ∀ j, v j ∈ V := hb₁ D γ V hD hγ hc.1
      (le_trans (countVals_subset (poly_mono (by omega) (le_max_left _ _))) hV)
      v hv
    refine append_mem hv' (hb₂ D (Fin.append v γ) V hD
      (append_mem hv' hγ) hc.2 ?_ w hw)
    exact le_trans (countVals_subset
      (poly_mono (by omega) (le_max_right _ _))) hV
  | Sum q₁ q₂ ih₁ ih₂ =>
    refine fun hq hs => ?_
    obtain ⟨b₁, k₁, hb₁⟩ := ih₁ hq.1 hs.1
    obtain ⟨b₂, k₂, hb₂⟩ := ih₂ hq.2 hs.2
    refine ⟨b₁ + b₂, max k₁ k₂, fun D γ V hD hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain] at hu
    rw [Multiset.mem_add] at hu
    rcases hu with h | h
    · exact hb₁ D γ V hD hγ hc.1 (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV) u h
    · exact hb₂ D γ V hD hγ hc.2 (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_right _ _))) hV) u h
  | Dedup q ih =>
    refine fun hq hs => ?_
    obtain ⟨b, k, hb⟩ := ih hq hs
    exact ⟨b, k, fun D γ V hD hγ hc hV =>
      Relation.valsIn_of_le (Multiset.dedup_le _) (hb D γ V hD hγ hc hV)⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    refine fun hq hs => ?_
    obtain ⟨b, k, hb⟩ := ih₁ hq.1 hs.1
    exact ⟨b, k, fun D γ V hD hγ hc hV =>
      Relation.valsIn_of_le (Multiset.filter_le _ _)
        (hb D γ V hD hγ hc.1 hV)⟩
  | Alt k hk q ih =>
    refine fun hq hs => ?_
    obtain ⟨b, k', hb⟩ := ih hq hs
    exact ⟨b, k', fun D γ V hD hγ hc hV => hb D γ V hD hγ hc hV⟩
  | Retag hk q ih =>
    refine fun hq hs => ?_
    obtain ⟨b, k, hb⟩ := ih hq hs
    exact ⟨b, k, fun D γ V hD hγ hc hV => hb D γ V hD hγ hc hV⟩
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq _ => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq _ => hq.elim
  | Gamma is ts fs q keep ord ih =>
    refine fun hq hs => ?_
    obtain ⟨bv, kv, hbv⟩ := ih hq hs.2.2.2
    obtain ⟨bc, kc, hbc⟩ := AggQueryIn.exists_polyBound q hq
    refine ⟨bv + bc, max kv kc, fun D γ V hD hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain] at hu
    obtain ⟨gg, hgg, rfl⟩ := Multiset.mem_map.mp hu
    rw [Multiset.mem_dedup] at hgg
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hgg
    have hvV : ∀ i, v i ∈ V := hbv D γ V hD hγ hc
      (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV) v hv
    refine append_mem (fun i => hvV (is i)) (fun j => ?_)
    rw [show fs j = cnt from Set.mem_singleton_iff.mp (hs.2.1 j)]
    refine hV (count_mem_countVals hg ?_)
    rw [List.length_map]
    exact le_trans (length_groupSeqOptOrd_le is ord _ _ (keep j))
      (le_trans (hbc D γ) (poly_mono (by omega) (le_max_right _ _)))
  | GammaScalar ts fs q ord ih =>
    refine fun hq hs => ?_
    obtain ⟨bc, kc, hbc⟩ := AggQueryIn.exists_polyBound q hq
    refine ⟨bc, kc, fun D γ V hD hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain] at hu
    obtain rfl := Multiset.mem_singleton.mp hu
    intro j
    show fs j _ ∈ V
    rw [show fs j = cnt from Set.mem_singleton_iff.mp (hs.2.1 j)]
    refine hV (count_mem_countVals hg ?_)
    rw [List.length_map]
    exact le_trans (length_groupSeqOptOrd_le (fun k : Fin 0 => k.elim0) ord _
      (fun k : Fin 0 => k.elim0) none) (hbc D γ)
  | GammaNest is his p f q ih =>
    refine fun hq hs => ?_
    obtain ⟨bv, kv, hbv⟩ := ih hq hs.2.2
    obtain ⟨bc, kc, hbc⟩ := AggQueryIn.exists_polyBound q hq
    obtain ⟨g', hsym, hmem, rfl⟩ := hs.2.1
    rw [Set.mem_singleton_iff] at hmem
    refine ⟨bv + bc, max kv kc, fun D γ V hD hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain] at hu
    obtain ⟨gg, hgg, rfl⟩ := Multiset.mem_map.mp hu
    rw [Multiset.mem_dedup] at hgg
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hgg
    have hvV : ∀ i, v i ∈ V := hbv D γ V hD hγ hc
      (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV) v hv
    refine append_mem (fun i => hvV (is i)) (fun _ => ?_)
    obtain ⟨L, hL⟩ := Quotient.exists_rep
      (((q.evaluatePlain D γ).filter (fun w =>
        (fun k => w (is k) : Tuple T _) = (fun k => v (is k) : Tuple T _))).map
        (fun w => p.evalPlain w γ))
    rw [← hL, show SeqAggFunc.onBag g' hsym (Quotient.mk _ L) = g' L from rfl,
      hmem]
    refine hV (count_mem_countVals hg ?_)
    have hcard : (L : Multiset T).card
        = Multiset.card (Multiset.map (fun w => p.evalPlain w γ)
          (Multiset.filter (fun w =>
            (fun k => w (is k) : Tuple T _)
              = (fun k => v (is k) : Tuple T _)) (q.evaluatePlain D γ))) :=
      congrArg Multiset.card hL
    rw [show L.length = (L : Multiset T).card from rfl, hcard,
      Multiset.card_map]
    exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _))
      (le_trans (hbc D γ) (poly_mono (by omega) (le_max_right _ _)))
  | Win P O o w t f q hrr dist keep ih =>
    refine fun hq hs => ?_
    obtain ⟨bv, kv, hbv⟩ := ih hq hs.2.2.2
    obtain ⟨bc, kc, hbc⟩ := AggQueryIn.exists_polyBound q hq
    refine ⟨bv + bc + 1, max kv kc, fun D γ V hD hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain] at hu
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hu
    have hvV : ∀ i, v i ∈ V := hbv D γ V hD hγ hc
      (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV) v hv
    have hfc : (if dist then f.distinct else f) = cnt := by
      cases dist with
      | false => exact Set.mem_singleton_iff.mp hs.2.1
      | true => exact Set.mem_singleton_iff.mp hs.2.1
    have hlen : ∀ L : List T, L.length
        ≤ Multiset.card (q.evaluatePlain D γ) + 1 →
        cnt L ∈ V := by
      intro L hL
      refine hV (count_mem_countVals hg (le_trans hL ?_))
      refine le_trans (Nat.add_le_add_right (le_trans (hbc D γ)
        (poly_mono (le_refl bc) (le_max_right kv kc))) 1) ?_
      have h1 : 1 ≤ (D.size + 1) ^ max kv kc :=
        Nat.one_le_pow _ _ (by omega)
      calc bc * (D.size + 1) ^ max kv kc + 1
          ≤ bc * (D.size + 1) ^ max kv kc + 1 * (D.size + 1) ^ max kv kc := by
            omega
        _ = (bc + 1) * (D.size + 1) ^ max kv kc := by ring
        _ ≤ (bv + bc + 1) * (D.size + 1) ^ max kv kc :=
            Nat.mul_le_mul_right _ (by omega)
    refine snoc_mem hvV ?_
    · rw [hfc]
      cases keep with
      | none =>
        rw [ValueFrame.windowValueOpt_none, ValueFrame.windowValue]
        refine hlen _ ?_
        rw [List.length_map]
        exact le_trans (length_frameListOf_le P O o w _ _)
          (Nat.add_le_add_right (le_of_eq (Multiset.card_map _ _)) 1)
      | some φ =>
        rw [ValueFrame.windowValueOpt_some, ValueFrame.windowValueWhen]
        refine hlen _ ?_
        rw [List.length_map]
        exact le_trans (List.length_filter_le _ _)
          (le_trans (length_frameListOf_le P O o w _ _)
            (Nat.add_le_add_right (le_of_eq (Multiset.card_map _ _)) 1))
  | ProvSum is his t q ih => exact fun _ hs => hs.elim
  | GammaTok is his ts fs a q keep ih => exact fun _ hs => hs.elim
  | WinExpr P O o ws ts fs gf q keeps ih => exact fun _ hs => hs.elim

/-! ## The set recursion

A set recursion's fixpoint has no bound in terms of its arguments': it
iterates. What bounds it is its *values* – a duplicate-free relation of
arity `k` over `|V|` values has at most `|V|^k` rows – and the rounds'
values close on a set the instance fixes, which is what SQL's
restriction on a recursive term buys. The body is read in the instance
extended by the previous round, so the value lemma is needed in that
form: `AggQueryIn.exists_valsIn_assign`.

One storey of recursion is what is proved here
(`AggQueryIn.recSimple`): the bodies of a set recursion are
recursion-free, so the counts inside them are counts over queries the
recursion does not feed. A deeper nesting would ask the same of the
inner bodies and is not done.
-/

/-- **A duplicate-free relation over `|V|` values has at most `|V|ⁿ`
rows.** -/
theorem card_le_pow_of_nodup_valsIn {n : ℕ} {r : Multiset (Tuple T n)}
    {V : Finset T} (hnd : r.Nodup) (hv : Relation.valsIn r V) :
    Multiset.card r ≤ V.card ^ n := by
  classical
  have hsub : r.toFinset ⊆ Fintype.piFinset (fun _ : Fin n => V) := by
    intro u hu
    exact Fintype.mem_piFinset.mpr
      (fun i => hv u (Multiset.mem_toFinset.mp hu) i)
  refine le_trans (le_of_eq (Multiset.toFinset_card_of_nodup hnd).symm) ?_
  refine le_trans (Finset.card_le_card hsub) (le_of_eq ?_)
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **The only recursion is a set recursion of one storey**: no `μ^⊎`,
and every `μ^∪` has recursion-free bodies in which the recursive
relation occurs under no aggregation, window, duplicate elimination or
difference. -/
def AggQueryIn.recSimple : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.recSimple
  | _, _, _, _, .Sel _ q _ => q.recSimple
  | _, _, _, _, .Prod q₁ q₂ => q₁.recSimple ∧ q₂.recSimple
  | _, _, _, _, .Apply q₁ q₂ => q₁.recSimple ∧ q₂.recSimple
  | _, _, _, _, .Sum q₁ q₂ => q₁.recSimple ∧ q₂.recSimple
  | _, _, _, _, .Dedup q => q.recSimple
  | _, _, _, _, .Diff q₁ q₂ => q₁.recSimple ∧ q₂.recSimple
  | _, _, _, _, .Alt _ _ q => q.recSimple
  | _, _, _, _, .Mu _ _ _ => False
  | _, _, _, _, .MuSet s q₀ q₁ =>
      q₀.noRec ∧ q₁.noRec ∧ q₀.recGuarded s ∧ q₁.recGuarded s
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.recSimple
  | _, _, _, _, .GammaScalar _ _ q _ => q.recSimple
  | _, _, _, _, .GammaNest _ _ _ _ q => q.recSimple
  | _, _, _, _, .ProvSum _ _ _ q => q.recSimple
  | _, _, _, _, .Retag _ q => q.recSimple
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.recSimple
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.recSimple
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.recSimple

omit [ValueType T] in
/-- A recursion-free query is one of these. -/
theorem AggQueryIn.recSimple_of_noRec :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noRec → q.recSimple := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Alt k hk q ih => exact ih
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | Gamma is ts fs q keep ord ih => exact ih
  | GammaScalar ts fs q ord ih => exact ih
  | GammaNest is his p f q ih => exact ih
  | ProvSum is his t q ih => exact ih
  | Retag hk q ih => exact ih
  | GammaTok is his ts fs a q keep ih => exact ih
  | Win P O o w t f q hrr dist keep ih => exact ih
  | WinExpr P O o ws ts fs g q keeps ih => exact ih

/-- **The values of a guarded body read in the extended instance.** The
recursive reference contributes the previous round's values; every count
is one over a query the recursion does not feed, so it is read off the
instance the recursion started from and bounded there. -/
theorem AggQueryIn.exists_valsIn_assign {cnt : SeqAggFunc T} {g : ℕ → T}
    (hg : ∀ L : List T, cnt L = g (L.countP (fun x => !ValueType.isNull x)))
    {s : String} {mX : ℕ} (X : Relation T mX) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noRec → q.inSig {cnt} → q.recGuarded s →
      ∃ b k : ℕ, ∀ (D : Database T) (γ : Fin c → T) (V : Finset T),
        (∀ (m : ℕ) (s' : String) (r : Relation T m), D.find m s' = some r →
            Relation.valsIn r V) →
        Relation.valsIn X V → (∀ j, γ j ∈ V) → q.constsIn V →
        countVals g (b * (D.size + 1) ^ k) ⊆ V →
        Relation.valsIn (q.evaluatePlain (D.assign s X) γ) V := by
  intro c n κ l q
  induction q with
  | Rel n s' =>
    refine fun _ _ _ => ⟨0, 0, fun D γ V hD hX _ _ _ => ?_⟩
    show Relation.valsIn (match (D.assign s X).find n s' with
      | none => (0 : Relation T n) | some rn => rn) V
    by_cases hc : n = mX ∧ s' = s
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Database.find_assign]
      exact hX
    · rw [Database.find_assign_of_ne s s' X D hc]
      cases hf : D.find n s' with
      | none => exact fun u hu => absurd hu (by simp)
      | some rn => exact hD n s' rn hf
  | Hole n s' =>
    refine fun _ _ _ => ⟨0, 0, fun D γ V hD hX _ _ _ => ?_⟩
    show Relation.valsIn (match (D.assign s X).find n s' with
      | none => (0 : Relation T n) | some rn => rn) V
    by_cases hc : n = mX ∧ s' = s
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Database.find_assign]
      exact hX
    · rw [Database.find_assign_of_ne s s' X D hc]
      cases hf : D.find n s' with
      | none => exact fun u hu => absurd hu (by simp)
      | some rn => exact hD n s' rn hf
  | Empty =>
    refine fun _ _ _ => ⟨0, 0, fun _ _ _ _ _ _ _ _ u hu => ?_⟩
    exact absurd (show u ∈ (0 : Multiset (Tuple T 0)) from hu) (by simp)
  | Proj ps q ih =>
    refine fun hq hs hrg => ?_
    obtain ⟨b, k, hb⟩ := ih hq hs.2 hrg
    refine ⟨b, k, fun D γ V hD hX hγ hc hV u hu j => ?_⟩
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hu
    exact (ps j).evalPlain_mem_of_noFun (hs.1 j) (hc.1 j) v
      (fun i => hb D γ V hD hX hγ hc.2 hV v hv i) γ hγ
  | Sel φ q _ ih =>
    refine fun hq hs hrg => ?_
    obtain ⟨b, k, hb⟩ := ih hq hs.2 hrg
    exact ⟨b, k, fun D γ V hD hX hγ hc hV =>
      Relation.valsIn_of_le (Multiset.filter_le _ _)
        (hb D γ V hD hX hγ hc hV)⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    refine fun hq hs hrg => ?_
    obtain ⟨b₁, k₁, hb₁⟩ := ih₁ hq.1 hs.1 hrg.1
    obtain ⟨b₂, k₂, hb₂⟩ := ih₂ hq.2 hs.2 hrg.2
    refine ⟨b₁ + b₂, max k₁ k₂, fun D γ V hD hX hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain, Relation.hMul_eq_bind] at hu
    obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
    refine append_mem (hb₁ D γ V hD hX hγ hc.1 ?_ v hv)
      (hb₂ D γ V hD hX hγ hc.2 ?_ w hw)
    · exact le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV
    · exact le_trans (countVals_subset
        (poly_mono (by omega) (le_max_right _ _))) hV
  | Apply q₁ q₂ ih₁ ih₂ =>
    refine fun hq hs hrg => ?_
    obtain ⟨b₁, k₁, hb₁⟩ := ih₁ hq.1 hs.1 hrg.1
    obtain ⟨b₂, k₂, hb₂⟩ := ih₂ hq.2 hs.2 hrg.2
    refine ⟨b₁ + b₂, max k₁ k₂, fun D γ V hD hX hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain] at hu
    obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
    have hv' : ∀ j, v j ∈ V := hb₁ D γ V hD hX hγ hc.1
      (le_trans (countVals_subset (poly_mono (by omega) (le_max_left _ _))) hV)
      v hv
    refine append_mem hv' (hb₂ D (Fin.append v γ) V hD hX
      (append_mem hv' hγ) hc.2 ?_ w hw)
    exact le_trans (countVals_subset
      (poly_mono (by omega) (le_max_right _ _))) hV
  | Sum q₁ q₂ ih₁ ih₂ =>
    refine fun hq hs hrg => ?_
    obtain ⟨b₁, k₁, hb₁⟩ := ih₁ hq.1 hs.1 hrg.1
    obtain ⟨b₂, k₂, hb₂⟩ := ih₂ hq.2 hs.2 hrg.2
    refine ⟨b₁ + b₂, max k₁ k₂, fun D γ V hD hX hγ hc hV u hu => ?_⟩
    rw [AggQueryIn.evaluatePlain] at hu
    rw [Multiset.mem_add] at hu
    rcases hu with h | h
    · exact hb₁ D γ V hD hX hγ hc.1 (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV) u h
    · exact hb₂ D γ V hD hX hγ hc.2 (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_right _ _))) hV) u h
  | Dedup q ih =>
    refine fun hq hs hrg => ?_
    obtain ⟨b, k, hb⟩ := AggQueryIn.exists_valsIn hg q hq hs
    refine ⟨b, k, fun D γ V hD hX hγ hc hV => ?_⟩
    rw [AggQueryIn.evaluatePlain,
      AggQueryIn.evaluatePlain_assign_of_noMention X q hrg D γ]
    exact Relation.valsIn_of_le (Multiset.dedup_le _) (hb D γ V hD hγ hc hV)
  | Diff q₁ q₂ ih₁ ih₂ =>
    refine fun hq hs hrg => ?_
    obtain ⟨b, k, hb⟩ := AggQueryIn.exists_valsIn hg q₁ hq.1 hs.1
    refine ⟨b, k, fun D γ V hD hX hγ hc hV => ?_⟩
    rw [AggQueryIn.evaluatePlain,
      AggQueryIn.evaluatePlain_assign_of_noMention X q₁ hrg.1 D γ,
      AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hrg.2 D γ]
    exact Relation.valsIn_of_le (Multiset.filter_le _ _)
      (hb D γ V hD hγ hc.1 hV)
  | Alt k hk q ih =>
    refine fun hq hs hrg => ?_
    obtain ⟨b, k', hb⟩ := ih hq hs hrg
    exact ⟨b, k', fun D γ V hD hX hγ hc hV => hb D γ V hD hX hγ hc hV⟩
  | Retag hk q ih =>
    refine fun hq hs hrg => ?_
    obtain ⟨b, k, hb⟩ := ih hq hs hrg
    exact ⟨b, k, fun D γ V hD hX hγ hc hV => hb D γ V hD hX hγ hc hV⟩
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun hq _ _ => hq.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun hq _ _ => hq.elim
  | ProvSum is his t q ih => exact fun _ hs _ => hs.elim
  | GammaTok is his ts fs a q keep ih => exact fun _ hs _ => hs.elim
  | WinExpr P O o ws ts fs gf q keeps ih => exact fun _ hs _ => hs.elim
  | Gamma is ts fs q keep ord ih =>
    refine fun hq hs hrg => ?_
    obtain ⟨b, k, hb⟩ := AggQueryIn.exists_valsIn hg q hq hs.2.2.2
    obtain ⟨bc, kc, hbc⟩ := AggQueryIn.exists_polyBound q hq
    refine ⟨b + bc, max k kc, fun D γ V hD hX hγ hc hV => ?_⟩
    rw [AggQueryIn.evaluatePlain,
      AggQueryIn.evaluatePlain_assign_of_noMention X q hrg D γ]
    intro u hu
    obtain ⟨gg, hgg, rfl⟩ := Multiset.mem_map.mp hu
    rw [Multiset.mem_dedup] at hgg
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hgg
    have hvV : ∀ i, v i ∈ V := hb D γ V hD hγ hc
      (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV) v hv
    refine append_mem (fun i => hvV (is i)) (fun j => ?_)
    rw [show fs j = cnt from Set.mem_singleton_iff.mp (hs.2.1 j)]
    refine hV (count_mem_countVals hg ?_)
    rw [List.length_map]
    exact le_trans (length_groupSeqOptOrd_le is ord _ _ (keep j))
      (le_trans (hbc D γ) (poly_mono (by omega) (le_max_right _ _)))
  | GammaScalar ts fs q ord ih =>
    refine fun hq hs hrg => ?_
    obtain ⟨bc, kc, hbc⟩ := AggQueryIn.exists_polyBound q hq
    refine ⟨bc, kc, fun D γ V hD hX hγ hc hV => ?_⟩
    rw [AggQueryIn.evaluatePlain,
      AggQueryIn.evaluatePlain_assign_of_noMention X q hrg D γ]
    intro u hu
    obtain rfl := Multiset.mem_singleton.mp hu
    intro j
    show fs j _ ∈ V
    rw [show fs j = cnt from Set.mem_singleton_iff.mp (hs.2.1 j)]
    refine hV (count_mem_countVals hg ?_)
    rw [List.length_map]
    exact le_trans (length_groupSeqOptOrd_le (fun k : Fin 0 => k.elim0) ord _
      (fun k : Fin 0 => k.elim0) none) (hbc D γ)
  | GammaNest is his p f q ih =>
    refine fun hq hs hrg => ?_
    obtain ⟨b, k, hb⟩ := AggQueryIn.exists_valsIn hg q hq hs.2.2
    obtain ⟨bc, kc, hbc⟩ := AggQueryIn.exists_polyBound q hq
    obtain ⟨g', hsym, hmem, rfl⟩ := hs.2.1
    rw [Set.mem_singleton_iff] at hmem
    refine ⟨b + bc, max k kc, fun D γ V hD hX hγ hc hV => ?_⟩
    rw [AggQueryIn.evaluatePlain,
      AggQueryIn.evaluatePlain_assign_of_noMention X q hrg D γ]
    intro u hu
    obtain ⟨gg, hgg, rfl⟩ := Multiset.mem_map.mp hu
    rw [Multiset.mem_dedup] at hgg
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hgg
    have hvV : ∀ i, v i ∈ V := hb D γ V hD hγ hc
      (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV) v hv
    refine append_mem (fun i => hvV (is i)) (fun _ => ?_)
    obtain ⟨L, hL⟩ := Quotient.exists_rep
      (((q.evaluatePlain D γ).filter (fun w =>
        (fun k => w (is k) : Tuple T _) = (fun k => v (is k) : Tuple T _))).map
        (fun w => p.evalPlain w γ))
    rw [← hL, show SeqAggFunc.onBag g' hsym (Quotient.mk _ L) = g' L from rfl,
      hmem]
    refine hV (count_mem_countVals hg ?_)
    have hcard : (L : Multiset T).card
        = Multiset.card (Multiset.map (fun w => p.evalPlain w γ)
          (Multiset.filter (fun w =>
            (fun k => w (is k) : Tuple T _)
              = (fun k => v (is k) : Tuple T _)) (q.evaluatePlain D γ))) :=
      congrArg Multiset.card hL
    rw [show L.length = (L : Multiset T).card from rfl, hcard,
      Multiset.card_map]
    exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _))
      (le_trans (hbc D γ) (poly_mono (by omega) (le_max_right _ _)))
  | Win P O o w t f q hrr dist keep ih =>
    refine fun hq hs hrg => ?_
    obtain ⟨b, k, hb⟩ := AggQueryIn.exists_valsIn hg q hq hs.2.2.2
    obtain ⟨bc, kc, hbc⟩ := AggQueryIn.exists_polyBound q hq
    refine ⟨b + bc + 1, max k kc, fun D γ V hD hX hγ hc hV => ?_⟩
    rw [AggQueryIn.evaluatePlain,
      AggQueryIn.evaluatePlain_assign_of_noMention X q hrg D γ]
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hu
    have hvV : ∀ i, v i ∈ V := hb D γ V hD hγ hc
      (le_trans (countVals_subset
        (poly_mono (by omega) (le_max_left _ _))) hV) v hv
    have hfc : (if dist then f.distinct else f) = cnt := by
      cases dist with
      | false => exact Set.mem_singleton_iff.mp hs.2.1
      | true => exact Set.mem_singleton_iff.mp hs.2.1
    have hlen : ∀ L : List T, L.length
        ≤ Multiset.card (q.evaluatePlain D γ) + 1 → cnt L ∈ V := by
      intro L hL
      refine hV (count_mem_countVals hg (le_trans hL ?_))
      refine le_trans (Nat.add_le_add_right (le_trans (hbc D γ)
        (poly_mono (le_refl bc) (le_max_right k kc))) 1) ?_
      have h1 : 1 ≤ (D.size + 1) ^ max k kc := Nat.one_le_pow _ _ (by omega)
      calc bc * (D.size + 1) ^ max k kc + 1
          ≤ bc * (D.size + 1) ^ max k kc
            + 1 * (D.size + 1) ^ max k kc := by omega
        _ = (bc + 1) * (D.size + 1) ^ max k kc := by ring
        _ ≤ (b + bc + 1) * (D.size + 1) ^ max k kc :=
            Nat.mul_le_mul_right _ (by omega)
    refine snoc_mem hvV ?_
    rw [hfc]
    cases keep with
    | none =>
      rw [ValueFrame.windowValueOpt_none, ValueFrame.windowValue]
      refine hlen _ ?_
      rw [List.length_map]
      exact le_trans (length_frameListOf_le P O o w _ _)
        (Nat.add_le_add_right (le_of_eq (Multiset.card_map _ _)) 1)
    | some φ =>
      rw [ValueFrame.windowValueOpt_some, ValueFrame.windowValueWhen]
      refine hlen _ ?_
      rw [List.length_map]
      exact le_trans (List.length_filter_le _ _)
        (le_trans (length_frameListOf_le P O o w _ _)
          (Nat.add_le_add_right (le_of_eq (Multiset.card_map _ _)) 1))

/-! ### The values the instance holds, as a set of polynomial size

The card of a set recursion's fixpoint is `|V|ⁿ` for the set `V` its
rounds close on, so the invariant needs `V` *built* and not quantified
over: a universally quantified set can be arbitrarily large, and a set
asked to contain the counts over its own size cannot exist. The set is
the instance's values at the arities the query reads, the query's
constants, and the counts up to the bound – and it is the **count bound
that grows** from one level of recursion to the next, which is what
keeps the construction from circling.
-/

/-- The values of a tuple. -/
def Tuple.valsL {k : ℕ} (u : Tuple T k) : List T := (List.finRange k).map u

omit [ValueType T] in
theorem Tuple.mem_valsL {k : ℕ} (u : Tuple T k) (j : Fin k) :
    u j ∈ u.valsL :=
  List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

omit [ValueType T] in
theorem Tuple.length_valsL {k : ℕ} (u : Tuple T k) : u.valsL.length = k := by
  rw [Tuple.valsL, List.length_map, List.length_finRange]

/-- The values of a relation, as a bag. -/
def Relation.valsM {k : ℕ} (r : Multiset (Tuple T k)) : Multiset T :=
  r.bind (fun u => (u.valsL : Multiset T))

omit [ValueType T] in
theorem Relation.card_valsM {k : ℕ} (r : Multiset (Tuple T k)) :
    Multiset.card (Relation.valsM r) = Multiset.card r * k := by
  rw [Relation.valsM, Multiset.card_bind]
  have hmap : (Multiset.map
      (Multiset.card ∘ fun u : Tuple T k => (u.valsL : Multiset T)) r)
      = r.map (fun _ => k) :=
    Multiset.map_congr rfl (fun u _ => by
      show Multiset.card ((u.valsL : Multiset T)) = k
      rw [Multiset.coe_card, Tuple.length_valsL])
  rw [hmap, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]

omit [ValueType T] in
theorem Relation.mem_valsM {k : ℕ} {r : Multiset (Tuple T k)} {u : Tuple T k}
    (hu : u ∈ r) (j : Fin k) : u j ∈ Relation.valsM r :=
  Multiset.mem_bind.mpr ⟨u, hu, Multiset.mem_coe.mpr (Tuple.mem_valsL u j)⟩

/-- The values an instance holds in its relations of arity at most `A`. -/
def Database.instValsM (A : ℕ) : Database T → Multiset T
  | [] => 0
  | (_, ⟨m, M⟩) :: tl =>
      (if m ≤ A then Relation.valsM M else 0) + Database.instValsM A tl

/-- And as a set. -/
def Database.instVals (A : ℕ) (D : Database T) : Finset T :=
  (Database.instValsM A D).toFinset

/-- **It has at most `A · n` values** over an instance of `n` rows: the
relations' sizes add up to `n`, and each row holds at most `A` of
them. -/
theorem Database.card_instVals_le (A : ℕ) (D : Database T) :
    (Database.instVals A D).card ≤ A * D.size := by
  refine le_trans (Multiset.toFinset_card_le _) ?_
  induction D with
  | nil => exact Nat.zero_le _
  | cons e tl ih =>
    obtain ⟨s, m, M⟩ := e
    rw [Database.instValsM, Database.size, List.map_cons, List.sum_cons,
      Multiset.card_add, Nat.mul_add]
    refine Nat.add_le_add ?_ ih
    by_cases hm : m ≤ A
    · rw [ite_eq_left hm, Relation.card_valsM, Nat.mul_comm]
      exact Nat.mul_le_mul_right _ hm
    · rw [ite_eq_right hm]
      exact Nat.zero_le _

/-- **And it holds the values of every relation the query may read.** -/
theorem Database.valsIn_instVals (A : ℕ) :
    ∀ (D : Database T) {k : ℕ} {s : String} {r : Relation T k}, k ≤ A →
      D.find k s = some r → Relation.valsIn r (Database.instVals A D)
  | [], k, s, r, _, h => absurd h (fun hc =>
      Option.some_ne_none r ((show (none : Option (Relation T k)) = some r
        from hc).symm))
  | (s', ⟨m, M⟩) :: tl, k, s, r, hk, h => by
    by_cases hc : k = m ∧ s = s'
    · obtain ⟨rfl, rfl⟩ := hc
      have h' : Database.find k s ((s, ⟨k, M⟩) :: tl) = some M := by
        show Database.find.f k s ((s, ⟨k, M⟩) :: tl) = some M
        rw [Database.find.f, dite_eq_left ⟨rfl, rfl⟩]
        rfl
      rw [h'] at h
      obtain rfl : r = M := (Option.some.inj h).symm
      intro u hu j
      refine Multiset.mem_toFinset.mpr ?_
      show u j ∈ (if k ≤ A then Relation.valsM r else 0)
        + Database.instValsM A tl
      rw [ite_eq_left hk]
      exact Multiset.mem_add.mpr (Or.inl (Relation.mem_valsM hu j))
    · have htl : Database.find k s tl = some r := by
        have hstep : Database.find k s ((s', ⟨m, M⟩) :: tl)
            = Database.find k s tl := by
          show Database.find.f k s ((s', ⟨m, M⟩) :: tl)
            = Database.find.f k s tl
          rw [Database.find.f, dite_eq_right hc]
        rw [hstep] at h
        exact h
      intro u hu j
      refine Multiset.mem_toFinset.mpr ?_
      show u j ∈ (if m ≤ A then Relation.valsM M else 0)
        + Database.instValsM A tl
      refine Multiset.mem_add.mpr (Or.inr ?_)
      exact Multiset.mem_toFinset.mp
        (Database.valsIn_instVals A tl hk htl u hu j)

/-- **The arities the query reads are at most `A`.** -/
def AggQueryIn.aritiesLe (A : ℕ) : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel k _ => k ≤ A
  | _, _, _, _, .Hole k _ => k ≤ A
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.aritiesLe A
  | _, _, _, _, .Sel _ q _ => q.aritiesLe A
  | _, _, _, _, .Prod q₁ q₂ => q₁.aritiesLe A ∧ q₂.aritiesLe A
  | _, _, _, _, .Apply q₁ q₂ => q₁.aritiesLe A ∧ q₂.aritiesLe A
  | _, _, _, _, .Sum q₁ q₂ => q₁.aritiesLe A ∧ q₂.aritiesLe A
  | _, _, _, _, .Dedup q => q.aritiesLe A
  | _, _, _, _, .Diff q₁ q₂ => q₁.aritiesLe A ∧ q₂.aritiesLe A
  | _, _, _, _, .Alt _ _ q => q.aritiesLe A
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.aritiesLe A ∧ q₁.aritiesLe A
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.aritiesLe A ∧ q₁.aritiesLe A
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.aritiesLe A
  | _, _, _, _, .GammaScalar _ _ q _ => q.aritiesLe A
  | _, _, _, _, .GammaNest _ _ _ _ q => q.aritiesLe A
  | _, _, _, _, .ProvSum _ _ _ q => q.aritiesLe A
  | _, _, _, _, .Retag _ q => q.aritiesLe A
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.aritiesLe A
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.aritiesLe A
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.aritiesLe A

/-! ## The card and the values of a result, set recursions included

What pins the `μ^⊎` row to `μ^⊎` alone is that a query of the minimal
signature **without** it – set recursions allowed – still has
polynomially many rows. A set recursion's fixpoint has no bound in terms
of its arguments' sizes, only in terms of its *values*: a duplicate-free
relation of arity `n` over `|V|` values has at most `|V|^n` rows
(`card_le_pow_of_nodup_valsIn`). So the card and the values have to be
bounded together, by one induction that carries two statements: of a
query, that its result's card is polynomial and its values lie in any
set holding the instance's values (at the arities the query reads), the
context's, the query's constants and the counts up to that polynomial;
and of a recursive term, that its result read in the instance extended
by a round has its values in any such set holding the round's values
too. The second is what the first needs at a set recursion – the rounds
then never leave the set – and the first is what the second needs for
the sides of a term that do not read the recursive relation, which
`sec:plain`'s restriction keeps the counts in: every count inside a
recursive term is over a query the recursion does not feed, read off the
instance the recursion started from (`settlesAt_assign_of_noMention`,
`evaluatePlain_assign_of_noMention`). -/

omit [ValueType T] in
theorem Relation.valsIn_mono {n : ℕ} {r : Multiset (Tuple T n)}
    {V V' : Finset T} (h : V ⊆ V') (hr : Relation.valsIn r V) :
    Relation.valsIn r V' :=
  fun u hu j => h (hr u hu j)

theorem card_countVals_le (g : ℕ → T) (m : ℕ) : (countVals g m).card ≤ m + 1 :=
  le_trans Finset.card_image_le (le_of_eq (Finset.card_range _))

/-- The largest arity a query reads. -/
def AggQueryIn.maxArity : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → ℕ
  | _, _, _, _, .Rel k _ => k
  | _, _, _, _, .Hole k _ => k
  | _, _, _, _, .Empty => 0
  | _, _, _, _, .Proj _ q => q.maxArity
  | _, _, _, _, .Sel _ q _ => q.maxArity
  | _, _, _, _, .Prod q₁ q₂ => max q₁.maxArity q₂.maxArity
  | _, _, _, _, .Apply q₁ q₂ => max q₁.maxArity q₂.maxArity
  | _, _, _, _, .Sum q₁ q₂ => max q₁.maxArity q₂.maxArity
  | _, _, _, _, .Dedup q => q.maxArity
  | _, _, _, _, .Diff q₁ q₂ => max q₁.maxArity q₂.maxArity
  | _, _, _, _, .Alt _ _ q => q.maxArity
  | _, _, _, _, .Mu _ q₀ q₁ => max q₀.maxArity q₁.maxArity
  | _, _, _, _, .MuSet _ q₀ q₁ => max q₀.maxArity q₁.maxArity
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.maxArity
  | _, _, _, _, .GammaScalar _ _ q _ => q.maxArity
  | _, _, _, _, .GammaNest _ _ _ _ q => q.maxArity
  | _, _, _, _, .ProvSum _ _ _ q => q.maxArity
  | _, _, _, _, .Retag _ q => q.maxArity
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.maxArity
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.maxArity
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.maxArity

omit [ValueType T] in
theorem AggQueryIn.aritiesLe_mono {A A' : ℕ} (h : A ≤ A') :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.aritiesLe A → q.aritiesLe A' := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun hq => le_trans hq h
  | Hole n s => exact fun hq => le_trans hq h
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Alt k hk q ih => exact ih
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.1, ih₁ hq.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.1, ih₁ hq.2⟩
  | Gamma is ts fs q keep ord ih => exact ih
  | GammaScalar ts fs q ord ih => exact ih
  | GammaNest is his p f q ih => exact ih
  | ProvSum is his t q ih => exact ih
  | Retag hk q ih => exact ih
  | GammaTok is his ts fs a q keep ih => exact ih
  | Win P O o w t f q hrr dist keep ih => exact ih
  | WinExpr P O o ws ts fs g q keeps ih => exact ih

omit [ValueType T] in
theorem AggQueryIn.aritiesLe_maxArity :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.aritiesLe q.maxArity := by
  intro c n κ l q
  induction q with
  | Rel n s => exact le_refl n
  | Hole n s => exact le_refl n
  | Empty => exact trivial
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact ⟨AggQueryIn.aritiesLe_mono (le_max_left _ _) q₁ ih₁,
      AggQueryIn.aritiesLe_mono (le_max_right _ _) q₂ ih₂⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact ⟨AggQueryIn.aritiesLe_mono (le_max_left _ _) q₁ ih₁,
      AggQueryIn.aritiesLe_mono (le_max_right _ _) q₂ ih₂⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact ⟨AggQueryIn.aritiesLe_mono (le_max_left _ _) q₁ ih₁,
      AggQueryIn.aritiesLe_mono (le_max_right _ _) q₂ ih₂⟩
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact ⟨AggQueryIn.aritiesLe_mono (le_max_left _ _) q₁ ih₁,
      AggQueryIn.aritiesLe_mono (le_max_right _ _) q₂ ih₂⟩
  | Alt k hk q ih => exact ih
  | Mu s q₀ q₁ ih₀ ih₁ =>
    exact ⟨AggQueryIn.aritiesLe_mono (le_max_left _ _) q₀ ih₀,
      AggQueryIn.aritiesLe_mono (le_max_right _ _) q₁ ih₁⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact ⟨AggQueryIn.aritiesLe_mono (le_max_left _ _) q₀ ih₀,
      AggQueryIn.aritiesLe_mono (le_max_right _ _) q₁ ih₁⟩
  | Gamma is ts fs q keep ord ih => exact ih
  | GammaScalar ts fs q ord ih => exact ih
  | GammaNest is his p f q ih => exact ih
  | ProvSum is his t q ih => exact ih
  | Retag hk q ih => exact ih
  | GammaTok is his ts fs a q keep ih => exact ih
  | Win P O o w t f q hrr dist keep ih => exact ih
  | WinExpr P O o ws ts fs g q keeps ih => exact ih

private theorem projCol_consts_subset {c n m : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (ps : Tuple (ProjColIn T c κ) m) (q : AggQueryIn T c n κ l) (j : Fin m) :
    (ps j).consts ⊆ (AggQueryIn.Proj ps q).consts :=
  fun _ hx => Finset.mem_union_left _
    (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hx⟩)

/-- **The card and the values of a result of the minimal signature,
without `μ^⊎`**, in the two forms the induction carries (see the section
heading): for a query, and for a recursive term read in the instance
extended by a round. -/
theorem AggQueryIn.exists_polyBound_rec_aux {S : Set OpKind}
    (hmb : OpKind.muBag ∉ S) {cnt : SeqAggFunc T} {g : ℕ → T}
    (hg : ∀ L : List T, cnt L = g (L.countP (fun x => !ValueType.isNull x)))
    (A : ℕ) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.hygienic → q.inSig {cnt} → q.aritiesLe A →
      (∃ b k : ℕ, ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
        Multiset.card (q.evaluatePlain D γ) ≤ b * (D.size + 1) ^ k
        ∧ ∀ V : Finset T,
          (∀ (m : ℕ) (s : String) (r : Relation T m), m ≤ A →
              D.find m s = some r → Relation.valsIn r V) →
          (∀ j, γ j ∈ V) → q.consts ⊆ V →
          countVals g (b * (D.size + 1) ^ k) ⊆ V →
          Relation.valsIn (q.evaluatePlain D γ) V)
      ∧ (∀ (s : String) (m : ℕ), l = [(s, m)] → q.noMention s →
        ∃ b k : ℕ, ∀ (D : Database T) (γ : Fin c → T)
          (X : Relation T m) (V : Finset T),
          (∀ (m : ℕ) (s' : String) (r : Relation T m), m ≤ A →
              D.find m s' = some r → Relation.valsIn r V) →
          Relation.valsIn X V → (∀ j, γ j ∈ V) → q.consts ⊆ V →
          countVals g (b * (D.size + 1) ^ k) ⊆ V →
          q.SettlesAt (D.assign s X) γ →
          Relation.valsIn (q.evaluatePlain (D.assign s X) γ) V) := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ _ _ ha
    refine ⟨⟨1, 1, fun D γ _ => ⟨?_, fun V hD _ _ _ => ?_⟩⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · show Multiset.card (match D.find n s with
        | none => (0 : Relation T n) | some rn => rn) ≤ _
      cases hf : D.find n s with
      | none => exact Nat.zero_le _
      | some rn =>
        refine le_trans (Database.card_le_size D hf) ?_
        rw [pow_one, one_mul]
        omega
    · show Relation.valsIn (match D.find n s with
        | none => (0 : Relation T n) | some rn => rn) V
      cases hf : D.find n s with
      | none => exact fun u hu => absurd hu (by simp)
      | some rn => exact hD n s rn ha hf
  | Hole n s =>
    intro _ _ _ ha
    refine ⟨⟨1, 1, fun D γ _ => ⟨?_, fun V hD _ _ _ => ?_⟩⟩,
      fun s' m hl _ => ?_⟩
    · show Multiset.card (match D.find n s with
        | none => (0 : Relation T n) | some rn => rn) ≤ _
      cases hf : D.find n s with
      | none => exact Nat.zero_le _
      | some rn =>
        refine le_trans (Database.card_le_size D hf) ?_
        rw [pow_one, one_mul]
        omega
    · show Relation.valsIn (match D.find n s with
        | none => (0 : Relation T n) | some rn => rn) V
      cases hf : D.find n s with
      | none => exact fun u hu => absurd hu (by simp)
      | some rn => exact hD n s rn ha hf
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.singleton_inj.mp hl)
      refine ⟨0, 0, fun D γ X V _ hX _ _ _ _ => ?_⟩
      show Relation.valsIn (match (D.assign s X).find n s with
        | none => (0 : Relation T n) | some rn => rn) V
      rw [Database.find_assign]
      exact hX
  | Empty =>
    intro _ _ _ _
    exact ⟨⟨0, 0, fun _ _ _ => ⟨Nat.zero_le _, fun _ _ _ _ _ u hu =>
      absurd (show u ∈ (0 : Multiset (Tuple T 0)) from hu) (by simp)⟩⟩,
      fun _ _ h _ => absurd h (by simp)⟩
  | Proj ps q ih =>
    intro hq hr hsig ha
    obtain ⟨⟨b, k, hM⟩, hb⟩ := ih hq.2 hr hsig.2 ha
    refine ⟨⟨b, k, fun D γ hs => ⟨?_, fun V hD hγ hc hV u hu j => ?_⟩⟩,
      fun s m hl hnm => ?_⟩
    · show Multiset.card (Multiset.map _ (q.evaluatePlain D γ)) ≤ _
      rw [Multiset.card_map]
      exact (hM D γ hs).1
    · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hu
      exact (ps j).evalPlain_mem_of_noFun (hsig.1 j)
        ((ps j).constsIn_of_subset (subset_trans (projCol_consts_subset ps q j) hc))
        v (fun i => (hM D γ hs).2 V hD hγ
          (subset_trans Finset.subset_union_right hc) hV v hv i) γ hγ
    · obtain ⟨b', k', hB⟩ := hb s m hl hnm
      refine ⟨b', k', fun D γ X V hD hX hγ hc hV hs u hu j => ?_⟩
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hu
      exact (ps j).evalPlain_mem_of_noFun (hsig.1 j)
        ((ps j).constsIn_of_subset (subset_trans (projCol_consts_subset ps q j) hc))
        v (fun i => hB D γ X V hD hX hγ
          (subset_trans Finset.subset_union_right hc) hV hs v hv i) γ hγ
  | Sel φ q _ ih =>
    intro hq hr hsig ha
    obtain ⟨⟨b, k, hM⟩, hb⟩ := ih hq.2 hr hsig.2 ha
    refine ⟨⟨b, k, fun D γ hs => ⟨?_, fun V hD hγ hc hV => ?_⟩⟩,
      fun s m hl hnm => ?_⟩
    · exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _))
        (hM D γ hs).1
    · exact Relation.valsIn_of_le (Multiset.filter_le _ _)
        ((hM D γ hs).2 V hD hγ hc hV)
    · obtain ⟨b', k', hB⟩ := hb s m hl hnm
      exact ⟨b', k', fun D γ X V hD hX hγ hc hV hs =>
        Relation.valsIn_of_le (Multiset.filter_le _ _)
          (hB D γ X V hD hX hγ hc hV hs)⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hr hsig ha
    obtain ⟨⟨b₁, k₁, hM₁⟩, hb₁⟩ := ih₁ hq.2.1 hr.1 hsig.1 ha.1
    obtain ⟨⟨b₂, k₂, hM₂⟩, hb₂⟩ := ih₂ hq.2.2 hr.2 hsig.2 ha.2
    refine ⟨⟨b₁ * b₂ + b₁ + b₂, k₁ + k₂, fun D γ hs =>
      ⟨?_, fun V hD hγ hc hV u hu => ?_⟩⟩, fun s m hl hnm => ?_⟩
    · show Multiset.card (q₁.evaluatePlain D γ * q₂.evaluatePlain D γ) ≤ _
      rw [Relation.card_hMul]
      refine le_trans (Nat.mul_le_mul (hM₁ D γ hs.1).1 (hM₂ D γ hs.2).1) ?_
      rw [pow_add, show b₁ * (D.size + 1) ^ k₁ * (b₂ * (D.size + 1) ^ k₂)
        = b₁ * b₂ * ((D.size + 1) ^ k₁ * (D.size + 1) ^ k₂) from by ring]
      exact Nat.mul_le_mul_right _ (by omega)
    · rw [AggQueryIn.evaluatePlain, Relation.hMul_eq_bind] at hu
      obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
      refine append_mem ((hM₁ D γ hs.1).2 V hD hγ
          (subset_trans Finset.subset_union_left hc) ?_ v hv)
        ((hM₂ D γ hs.2).2 V hD hγ
          (subset_trans Finset.subset_union_right hc) ?_ w hw)
      · exact subset_trans (countVals_subset
          (poly_mono (by omega) (Nat.le_add_right _ _))) hV
      · exact subset_trans (countVals_subset
          (poly_mono (by omega) (Nat.le_add_left _ _))) hV
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨b₁', k₁', hB₁⟩ := hb₁ s m hl₁ h₁
        refine ⟨b₁' + b₂, max k₁' k₂, fun D γ X V hD hX hγ hc hV hs u hu => ?_⟩
        rw [AggQueryIn.evaluatePlain, Relation.hMul_eq_bind] at hu
        obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
        rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₂ h₂ D γ] at hw
        refine append_mem (hB₁ D γ X V hD hX hγ
            (subset_trans Finset.subset_union_left hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_left _ _))) hV) hs.1 v hv)
          ((hM₂ D γ (AggQueryIn.settlesAt_assign_of_noMention X q₂ h₂ D γ hs.2)).2
            V hD hγ (subset_trans Finset.subset_union_right hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_right _ _))) hV) w hw)
      · subst hl₁
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨b₂', k₂', hB₂⟩ := hb₂ s m hl₂ h₂
        refine ⟨b₁ + b₂', max k₁ k₂', fun D γ X V hD hX hγ hc hV hs u hu => ?_⟩
        rw [AggQueryIn.evaluatePlain, Relation.hMul_eq_bind] at hu
        obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
        rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₁ h₁ D γ] at hv
        refine append_mem
          ((hM₁ D γ (AggQueryIn.settlesAt_assign_of_noMention X q₁ h₁ D γ hs.1)).2
            V hD hγ (subset_trans Finset.subset_union_left hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_left _ _))) hV) v hv)
          (hB₂ D γ X V hD hX hγ (subset_trans Finset.subset_union_right hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_right _ _))) hV) hs.2 w hw)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hr hsig ha
    obtain ⟨⟨b₁, k₁, hM₁⟩, hb₁⟩ := ih₁ hq.2.1 hr.1 hsig.1 ha.1
    obtain ⟨⟨b₂, k₂, hM₂⟩, hb₂⟩ := ih₂ hq.2.2 hr.2 hsig.2 ha.2
    refine ⟨⟨b₁ * b₂ + b₁ + b₂, k₁ + k₂, fun D γ hs =>
      ⟨?_, fun V hD hγ hc hV u hu => ?_⟩⟩, fun s m hl hnm => ?_⟩
    · show Multiset.card ((q₁.evaluatePlain D γ).bind (fun u =>
        Multiset.map _ (q₂.evaluatePlain D (Fin.append u γ)))) ≤ _
      rw [Multiset.card_bind]
      refine le_trans (Multiset.sum_le_card_nsmul _ (b₂ * (D.size + 1) ^ k₂)
        (fun x hx => ?_)) ?_
      · obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hx
        show Multiset.card (Multiset.map (fun v => Fin.append u v)
          (q₂.evaluatePlain D (Fin.append u γ))) ≤ _
        rw [Multiset.card_map]
        exact (hM₂ D (Fin.append u γ) (hs.2 u hu)).1
      · rw [smul_eq_mul, Multiset.card_map]
        refine le_trans (Nat.mul_le_mul_right _ (hM₁ D γ hs.1).1) ?_
        rw [pow_add, show b₁ * (D.size + 1) ^ k₁ * (b₂ * (D.size + 1) ^ k₂)
          = b₁ * b₂ * ((D.size + 1) ^ k₁ * (D.size + 1) ^ k₂) from by ring]
        exact Nat.mul_le_mul_right _ (by omega)
    · rw [AggQueryIn.evaluatePlain] at hu
      obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
      have hv' : ∀ j, v j ∈ V := (hM₁ D γ hs.1).2 V hD hγ
        (subset_trans Finset.subset_union_left hc)
        (subset_trans (countVals_subset
          (poly_mono (by omega) (Nat.le_add_right _ _))) hV) v hv
      refine append_mem hv' ((hM₂ D (Fin.append v γ) (hs.2 v hv)).2 V hD
        (append_mem hv' hγ) (subset_trans Finset.subset_union_right hc)
        (subset_trans (countVals_subset
          (poly_mono (by omega) (Nat.le_add_left _ _))) hV) w hw)
    · obtain ⟨b₁', k₁', hB₁⟩ := hb₁ s m hl hnm.1
      refine ⟨b₁' + b₂, max k₁' k₂, fun D γ X V hD hX hγ hc hV hs u hu => ?_⟩
      rw [AggQueryIn.evaluatePlain] at hu
      obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
      have hv' : ∀ j, v j ∈ V := hB₁ D γ X V hD hX hγ
        (subset_trans Finset.subset_union_left hc)
        (subset_trans (countVals_subset
          (poly_mono (by omega) (le_max_left _ _))) hV) hs.1 v hv
      rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hnm.2 D] at hw
      refine append_mem hv' ((hM₂ D (Fin.append v γ)
        (AggQueryIn.settlesAt_assign_of_noMention X q₂ hnm.2 D _ (hs.2 v hv))).2
        V hD (append_mem hv' hγ) (subset_trans Finset.subset_union_right hc)
        (subset_trans (countVals_subset
          (poly_mono (by omega) (le_max_right _ _))) hV) w hw)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hr hsig ha
    obtain ⟨⟨b₁, k₁, hM₁⟩, hb₁⟩ := ih₁ hq.2.1 hr.1 hsig.1 ha.1
    obtain ⟨⟨b₂, k₂, hM₂⟩, hb₂⟩ := ih₂ hq.2.2 hr.2 hsig.2 ha.2
    refine ⟨⟨b₁ + b₂, max k₁ k₂, fun D γ hs =>
      ⟨?_, fun V hD hγ hc hV u hu => ?_⟩⟩, fun s m hl hnm => ?_⟩
    · show Multiset.card (q₁.evaluatePlain D γ + q₂.evaluatePlain D γ) ≤ _
      rw [Relation.card_add, Nat.add_mul]
      exact Nat.add_le_add
        (le_trans (hM₁ D γ hs.1).1 (poly_le_poly (le_max_left _ _)))
        (le_trans (hM₂ D γ hs.2).1 (poly_le_poly (le_max_right _ _)))
    · rw [AggQueryIn.evaluatePlain, Multiset.mem_add] at hu
      rcases hu with h | h
      · exact (hM₁ D γ hs.1).2 V hD hγ (subset_trans Finset.subset_union_left hc)
          (subset_trans (countVals_subset
            (poly_mono (by omega) (le_max_left _ _))) hV) u h
      · exact (hM₂ D γ hs.2).2 V hD hγ (subset_trans Finset.subset_union_right hc)
          (subset_trans (countVals_subset
            (poly_mono (by omega) (le_max_right _ _))) hV) u h
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨b₁', k₁', hB₁⟩ := hb₁ s m hl₁ h₁
        refine ⟨b₁' + b₂, max k₁' k₂, fun D γ X V hD hX hγ hc hV hs u hu => ?_⟩
        rw [AggQueryIn.evaluatePlain, Multiset.mem_add] at hu
        rcases hu with h | h
        · exact hB₁ D γ X V hD hX hγ (subset_trans Finset.subset_union_left hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_left _ _))) hV) hs.1 u h
        · rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₂ h₂ D γ] at h
          exact (hM₂ D γ (AggQueryIn.settlesAt_assign_of_noMention X q₂ h₂ D γ hs.2)).2
            V hD hγ (subset_trans Finset.subset_union_right hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_right _ _))) hV) u h
      · subst hl₁
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨b₂', k₂', hB₂⟩ := hb₂ s m hl₂ h₂
        refine ⟨b₁ + b₂', max k₁ k₂', fun D γ X V hD hX hγ hc hV hs u hu => ?_⟩
        rw [AggQueryIn.evaluatePlain, Multiset.mem_add] at hu
        rcases hu with h | h
        · rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₁ h₁ D γ] at h
          exact (hM₁ D γ (AggQueryIn.settlesAt_assign_of_noMention X q₁ h₁ D γ hs.1)).2
            V hD hγ (subset_trans Finset.subset_union_left hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_left _ _))) hV) u h
        · exact hB₂ D γ X V hD hX hγ (subset_trans Finset.subset_union_right hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_right _ _))) hV) hs.2 u h
  | Dedup q ih =>
    intro hq hr hsig ha
    obtain ⟨⟨b, k, hM⟩, -⟩ := ih hq.2 hr hsig ha
    exact ⟨⟨b, k, fun D γ hs =>
      ⟨le_trans (Multiset.card_dedup_le _) (hM D γ hs).1,
        fun V hD hγ hc hV => Relation.valsIn_of_le (Multiset.dedup_le _)
          ((hM D γ hs).2 V hD hγ hc hV)⟩⟩, fun _ _ h _ => absurd h (by simp)⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hr hsig ha
    obtain ⟨⟨b, k, hM⟩, -⟩ := ih₁ hq.2.1 hr.1 hsig.1 ha.1
    exact ⟨⟨b, k, fun D γ hs =>
      ⟨le_trans (Multiset.card_le_card (Multiset.filter_le _ _)) (hM D γ hs.1).1,
        fun V hD hγ hc hV => Relation.valsIn_of_le (Multiset.filter_le _ _)
          ((hM D γ hs.1).2 V hD hγ (subset_trans Finset.subset_union_left hc) hV)⟩⟩,
      fun _ _ h _ => absurd h (by simp)⟩
  | Alt k hk q ih => intro hq hr hsig ha; exact ih hq hr hsig ha
  | Retag hk q ih => intro hq hr hsig ha; exact ih hq hr hsig ha
  | Mu s q₀ q₁ ih₀ ih₁ => intro hq; exact absurd hq.1 hmb
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' n'
    intro hq hr hsig ha
    refine ⟨?_, fun _ _ h _ => absurd h (by simp)⟩
    obtain ⟨⟨b₀, k₀, hM₀⟩, -⟩ := ih₀ hq.2.1 hr.2.2.1 hsig.1 ha.1
    obtain ⟨-, hb₁⟩ := ih₁ hq.2.2 hr.2.2.2 hsig.2 ha.2
    obtain ⟨b₁, k₁, hB₁⟩ := hb₁ s n' rfl hr.2.1
    set Kc := (AggQueryIn.MuSet s q₀ q₁).consts.card with hKc
    set K₀ := max (max k₀ k₁) 1 with hK₀
    set B₀ := A + Kc + (b₀ + b₁) + 1 + c' with hB₀
    refine ⟨B₀ ^ n' + (b₀ + b₁), K₀ * n' + K₀, fun D γ hs => ?_⟩
    -- The rounds never leave a set holding the base's and the body's values.
    have hrounds : ∀ V : Finset T,
        (∀ (m : ℕ) (s' : String) (r : Relation T m), m ≤ A →
            D.find m s' = some r → Relation.valsIn r V) →
        (∀ j, γ j ∈ V) → (AggQueryIn.MuSet s q₀ q₁).consts ⊆ V →
        countVals g ((b₀ + b₁) * (D.size + 1) ^ max k₀ k₁) ⊆ V →
        ∀ j, Relation.valsIn (muIter (fun X : Multiset (Tuple T n') =>
          (q₀.evaluatePlain D γ
            + q₁.evaluatePlain (D.assign s X) γ).dedup) j) V := by
      intro V hD hγ hc hV j
      induction j with
      | zero => exact fun u hu => absurd hu (Multiset.notMem_zero u)
      | succ j ih =>
        show Relation.valsIn (Multiset.dedup (q₀.evaluatePlain D γ
          + q₁.evaluatePlain (D.assign s _) γ)) V
        refine Relation.valsIn_of_le (Multiset.dedup_le _) (fun u hu => ?_)
        rcases Multiset.mem_add.mp hu with h | h
        · exact (hM₀ D γ hs.1).2 V hD hγ (subset_trans Finset.subset_union_left hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_left _ _))) hV) u h
        · exact hB₁ D γ _ V hD ih hγ (subset_trans Finset.subset_union_right hc)
            (subset_trans (countVals_subset
              (poly_mono (by omega) (le_max_right _ _))) hV) (hs.2.2 j) u h
    have hvals : ∀ V : Finset T,
        (∀ (m : ℕ) (s' : String) (r : Relation T m), m ≤ A →
            D.find m s' = some r → Relation.valsIn r V) →
        (∀ j, γ j ∈ V) → (AggQueryIn.MuSet s q₀ q₁).consts ⊆ V →
        countVals g ((b₀ + b₁) * (D.size + 1) ^ max k₀ k₁) ⊆ V →
        Relation.valsIn ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ) V :=
      fun V hD hγ hc hV => hrounds V hD hγ hc hV _
    have hmaxK : max k₀ k₁ ≤ K₀ * n' + K₀ :=
      le_trans (le_max_left _ _) (Nat.le_add_left _ _)
    refine ⟨?_, fun V hD hγ hc hV => hvals V hD hγ hc
      (subset_trans (countVals_subset (poly_mono (by omega) hmaxK)) hV)⟩
    -- The card, off the value set of polynomial size.
    set V₀ : Finset T := Union.union (Union.union (Union.union
      (Database.instVals A D) (AggQueryIn.MuSet s q₀ q₁).consts)
      (countVals g ((b₀ + b₁) * (D.size + 1) ^ max k₀ k₁)))
      (Finset.univ.image γ) with hV₀
    have hF : Relation.valsIn ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ) V₀ :=
      hvals V₀
        (fun m s' r hm hf => Relation.valsIn_mono
          (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ hx)))
          (Database.valsIn_instVals A D hm hf))
        (fun j => Finset.mem_union_right _
          (Finset.mem_image_of_mem γ (Finset.mem_univ j)))
        (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ hx)))
        (fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx))
    have hnd : ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ).Nodup := by
      show (muFix (fun X : Multiset (Tuple T n') =>
        (q₀.evaluatePlain D γ
          + q₁.evaluatePlain (D.assign s X) γ).dedup)).Nodup
      rw [muFix, muIter_eq_iterate]
      exact nodup_iterate_dedup _ _
    have hpow1 : 1 ≤ (D.size + 1) ^ K₀ := Nat.one_le_pow _ _ (by omega)
    have hpowS : D.size + 1 ≤ (D.size + 1) ^ K₀ := by
      calc D.size + 1 = (D.size + 1) ^ 1 := (pow_one _).symm
        _ ≤ (D.size + 1) ^ K₀ := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hpowM : (D.size + 1) ^ max k₀ k₁ ≤ (D.size + 1) ^ K₀ :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hcardV : V₀.card ≤ B₀ * (D.size + 1) ^ K₀ := by
      have h1 : (Database.instVals A D).card ≤ A * D.size :=
        Database.card_instVals_le A D
      have h2 : (countVals g ((b₀ + b₁) * (D.size + 1) ^ max k₀ k₁)).card
          ≤ (b₀ + b₁) * (D.size + 1) ^ max k₀ k₁ + 1 := card_countVals_le _ _
      have h3 : (Finset.univ.image γ).card ≤ c' :=
        le_trans Finset.card_image_le (by simp)
      have hU : V₀.card ≤ A * D.size + Kc
          + ((b₀ + b₁) * (D.size + 1) ^ max k₀ k₁ + 1) + c' :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add
          (le_trans (Finset.card_union_le _ _) (Nat.add_le_add
            (le_trans (Finset.card_union_le _ _) (Nat.add_le_add h1 (le_refl _)))
            h2)) h3)
      refine le_trans hU ?_
      have ha' : A * D.size ≤ A * (D.size + 1) ^ K₀ :=
        Nat.mul_le_mul_left _ (le_trans (Nat.le_succ _) hpowS)
      have hk' : Kc ≤ Kc * (D.size + 1) ^ K₀ := Nat.le_mul_of_pos_right _ hpow1
      have hm' : (b₀ + b₁) * (D.size + 1) ^ max k₀ k₁
          ≤ (b₀ + b₁) * (D.size + 1) ^ K₀ := Nat.mul_le_mul_left _ hpowM
      have hc' : c' ≤ c' * (D.size + 1) ^ K₀ := Nat.le_mul_of_pos_right _ hpow1
      rw [hB₀, show (A + Kc + (b₀ + b₁) + 1 + c') * (D.size + 1) ^ K₀
        = A * (D.size + 1) ^ K₀ + Kc * (D.size + 1) ^ K₀
          + ((b₀ + b₁) * (D.size + 1) ^ K₀ + (D.size + 1) ^ K₀)
          + c' * (D.size + 1) ^ K₀ from by ring]
      omega
    calc Multiset.card ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ)
        ≤ V₀.card ^ n' := card_le_pow_of_nodup_valsIn hnd hF
      _ ≤ (B₀ * (D.size + 1) ^ K₀) ^ n' := Nat.pow_le_pow_left hcardV n'
      _ = B₀ ^ n' * (D.size + 1) ^ (K₀ * n') := by rw [mul_pow, ← pow_mul]
      _ ≤ (B₀ ^ n' + (b₀ + b₁)) * (D.size + 1) ^ (K₀ * n' + K₀) :=
          Nat.mul_le_mul (Nat.le_add_right _ _)
            (Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _))
  | Gamma is ts fs q keep ord ih =>
    intro hq hr hsig ha
    obtain ⟨⟨b, k, hM⟩, -⟩ := ih hq.2 hr hsig.2.2.2 ha
    refine ⟨⟨b, k, fun D γ hs => ⟨?_, fun V hD hγ hc hV u hu => ?_⟩⟩,
      fun _ _ h _ => absurd h (by simp)⟩
    · show Multiset.card (Multiset.map _ (Multiset.dedup
        (Multiset.map _ (q.evaluatePlain D γ)))) ≤ _
      rw [Multiset.card_map]
      exact le_trans (le_trans (Multiset.card_dedup_le _)
        (le_of_eq (Multiset.card_map _ _))) (hM D γ hs).1
    · rw [AggQueryIn.evaluatePlain] at hu
      obtain ⟨gg, hgg, rfl⟩ := Multiset.mem_map.mp hu
      rw [Multiset.mem_dedup] at hgg
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hgg
      have hvV : ∀ i, v i ∈ V := (hM D γ hs).2 V hD hγ hc hV v hv
      refine append_mem (fun i => hvV (is i)) (fun j => ?_)
      rw [show fs j = cnt from Set.mem_singleton_iff.mp (hsig.2.1 j)]
      refine hV (count_mem_countVals hg ?_)
      rw [List.length_map]
      exact le_trans (length_groupSeqOptOrd_le is ord _ _ (keep j)) (hM D γ hs).1
  | GammaScalar ts fs q ord ih =>
    intro hq hr hsig ha
    obtain ⟨⟨b, k, hM⟩, -⟩ := ih hq.2 hr hsig.2.2 ha
    refine ⟨⟨b + 1, k, fun D γ hs => ⟨?_, fun V hD hγ hc hV u hu => ?_⟩⟩,
      fun _ _ h _ => absurd h (by simp)⟩
    · show Multiset.card (Multiset.ofList [_]) ≤ _
      have h1 : 1 ≤ (D.size + 1) ^ k := Nat.one_le_pow _ _ (by omega)
      calc Multiset.card (Multiset.ofList [_]) = 1 := rfl
        _ ≤ (b + 1) * (D.size + 1) ^ k := by
          rw [Nat.add_mul, one_mul]; omega
    · rw [AggQueryIn.evaluatePlain] at hu
      obtain rfl := Multiset.mem_singleton.mp hu
      intro j
      show fs j _ ∈ V
      rw [show fs j = cnt from Set.mem_singleton_iff.mp (hsig.2.1 j)]
      refine hV (count_mem_countVals hg ?_)
      rw [List.length_map]
      exact le_trans (length_groupSeqOptOrd_le (fun k : Fin 0 => k.elim0) ord _
        (fun k : Fin 0 => k.elim0) none)
        (le_trans (hM D γ hs).1 (poly_mono (Nat.le_succ b) (le_refl k)))
  | GammaNest is his p f q ih =>
    intro hq hr hsig ha
    obtain ⟨⟨b, k, hM⟩, -⟩ := ih hq.2 hr hsig.2.2 ha
    obtain ⟨g', hsym, hmem, rfl⟩ := hsig.2.1
    rw [Set.mem_singleton_iff] at hmem
    refine ⟨⟨b, k, fun D γ hs => ⟨?_, fun V hD hγ hc hV u hu => ?_⟩⟩,
      fun _ _ h _ => absurd h (by simp)⟩
    · show Multiset.card (Multiset.map _ (Multiset.dedup
        (Multiset.map _ (q.evaluatePlain D γ)))) ≤ _
      rw [Multiset.card_map]
      exact le_trans (le_trans (Multiset.card_dedup_le _)
        (le_of_eq (Multiset.card_map _ _))) (hM D γ hs).1
    · rw [AggQueryIn.evaluatePlain] at hu
      obtain ⟨gg, hgg, rfl⟩ := Multiset.mem_map.mp hu
      rw [Multiset.mem_dedup] at hgg
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hgg
      have hvV : ∀ i, v i ∈ V := (hM D γ hs).2 V hD hγ hc hV v hv
      refine append_mem (fun i => hvV (is i)) (fun _ => ?_)
      obtain ⟨L, hL⟩ := Quotient.exists_rep
        (((q.evaluatePlain D γ).filter (fun w =>
          (fun k => w (is k) : Tuple T _) = (fun k => v (is k) : Tuple T _))).map
          (fun w => p.evalPlain w γ))
      rw [← hL, show SeqAggFunc.onBag g' hsym (Quotient.mk _ L) = g' L from rfl,
        hmem]
      refine hV (count_mem_countVals hg ?_)
      have hcard : (L : Multiset T).card
          = Multiset.card (Multiset.map (fun w => p.evalPlain w γ)
            (Multiset.filter (fun w =>
              (fun k => w (is k) : Tuple T _)
                = (fun k => v (is k) : Tuple T _)) (q.evaluatePlain D γ))) :=
        congrArg Multiset.card hL
      rw [show L.length = (L : Multiset T).card from rfl, hcard,
        Multiset.card_map]
      exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _)) (hM D γ hs).1
  | ProvSum is his t q ih => intro _ _ hsig; exact hsig.elim
  | GammaTok is his ts fs a q keep ih => intro _ _ hsig; exact hsig.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq hr hsig ha
    obtain ⟨⟨b, k, hM⟩, -⟩ := ih hq.2 hr hsig.2.2.2 ha
    refine ⟨⟨b + 1, k, fun D γ hs => ⟨?_, fun V hD hγ hc hV u hu => ?_⟩⟩,
      fun _ _ h _ => absurd h (by simp)⟩
    · show Multiset.card (Multiset.map _ (q.evaluatePlain D γ)) ≤ _
      rw [Multiset.card_map]
      exact le_trans (hM D γ hs).1 (poly_mono (Nat.le_succ b) (le_refl k))
    · rw [AggQueryIn.evaluatePlain] at hu
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hu
      have hvV : ∀ i, v i ∈ V := (hM D γ hs).2 V hD hγ hc
        (subset_trans (countVals_subset (poly_mono (Nat.le_succ b) (le_refl k))) hV)
        v hv
      have hfc : (if dist then f.distinct else f) = cnt := by
        cases dist with
        | false => exact Set.mem_singleton_iff.mp hsig.2.1
        | true => exact Set.mem_singleton_iff.mp hsig.2.1
      have hlen : ∀ L : List T, L.length
          ≤ Multiset.card (q.evaluatePlain D γ) + 1 → cnt L ∈ V := by
        intro L hL
        refine hV (count_mem_countVals hg (le_trans hL ?_))
        have h1 : 1 ≤ (D.size + 1) ^ k := Nat.one_le_pow _ _ (by omega)
        calc Multiset.card (q.evaluatePlain D γ) + 1
            ≤ b * (D.size + 1) ^ k + 1 := Nat.add_le_add_right (hM D γ hs).1 1
          _ ≤ b * (D.size + 1) ^ k + (D.size + 1) ^ k := by omega
          _ = (b + 1) * (D.size + 1) ^ k := by ring
      refine snoc_mem hvV ?_
      rw [hfc]
      cases keep with
      | none =>
        rw [ValueFrame.windowValueOpt_none, ValueFrame.windowValue]
        refine hlen _ ?_
        rw [List.length_map]
        exact le_trans (length_frameListOf_le P O o w _ _)
          (Nat.add_le_add_right (le_of_eq (Multiset.card_map _ _)) 1)
      | some φ =>
        rw [ValueFrame.windowValueOpt_some, ValueFrame.windowValueWhen]
        refine hlen _ ?_
        rw [List.length_map]
        exact le_trans (List.length_filter_le _ _)
          (le_trans (length_frameListOf_le P O o w _ _)
            (Nat.add_le_add_right (le_of_eq (Multiset.card_map _ _)) 1))
  | WinExpr P O o ws ts fs gf q keeps ih => intro _ _ hsig; exact hsig.elim

/-- **Without `μ^⊎`, a query of the minimal signature has polynomially
many rows wherever it is defined**, set recursions included. -/
theorem AggQueryIn.exists_polyBound_rec {S : Set OpKind}
    (hmb : OpKind.muBag ∉ S) {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
    (hq : q.usesOnly S) (hr : q.hygienic) (hsig : q.inSig {cnt}) :
    ∃ b k : ℕ, ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
      Multiset.card (q.evaluatePlain D γ) ≤ b * (D.size + 1) ^ k := by
  obtain ⟨g, hg⟩ := hcnt
  obtain ⟨b, k, h⟩ := (AggQueryIn.exists_polyBound_rec_aux hmb hg q.maxArity q
    hq hr hsig (AggQueryIn.aritiesLe_maxArity q)).1
  exact ⟨b, k, fun D γ hs => (h D γ hs).1⟩

/-! ## The row: a basis of the whole algebra holds a recursion

`thm:plainbasis`'s second half grades the recursions as classes like the
others. The witness is the chain of diamonds: a class set holding neither
recursion generates only queries whose answers are polynomial in the
instance (`AggQueryIn.exists_polyBound`), and the sink of the chain has
`2ⁿ` rows.

The four rows that do **not** survive a recursion carry the two classes'
absence as a hypothesis (`Π`, `×`/apply, `⊎`, and `σ`/`−`); `γ` survives
it with a proof (over an empty instance every round is empty), and `∅`
survives `μ^⊎` but not `μ^∪` – a scalar aggregation inside a set
recursion makes a row from the empty round without naming a relation and
without `∅`, which `tab:basisclasses`'s `∅` row does not account for.
-/

omit [ValueType T] in
/-- **A query over classes holding neither recursion is
recursion-free.** -/
theorem AggQueryIn.noRec_of_usesOnly {S : Set OpKind}
    (hmb : OpKind.muBag ∉ S) (hms : OpKind.muSet ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.noRec := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun hq => ih hq.2
  | Sel φ q _ ih => exact fun hq => ih hq.2
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Dedup q ih => exact fun hq => ih hq.2
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Alt k hk q ih => exact fun hq => ih hq
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hmb
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hms
  | Gamma is ts fs q keep ord ih => exact fun hq => ih hq.2
  | GammaScalar ts fs q ord ih => exact fun hq => ih hq.2
  | GammaNest is his p f q ih => exact fun hq => ih hq.2
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Retag hk q ih => exact fun hq => ih hq
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | Win P O o w t f q hrr dist keep ih => exact fun hq => ih hq.2
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hq => ih hq.2

/-- **The scope of the classification with the recursions.** -/
def plainRecOps : Set OpKind :=
  insert OpKind.muBag (insert OpKind.muSet plainOps)

/-- **A generating set of the whole algebra**, over a schema, **in the
minimal universe** `𝒜(∅, {count})` (Pierre, 2026-10-12: the
classification with the recursions is done there and only there): every
query of the algebra over `sch` in the minimal signature, with derivable
windows, is matched by one in the minimal signature using only the
classes of `S`, which is **defined wherever the query is and agrees with
it there** (`AggQueryIn.SettlesAt`). A query of the whole algebra is a
partial function of the instance, so this is what equivalence means for
it; nothing is asked where the query is undefined. The counting aggregate
`cnt` is a parameter with `SeqAggFunc.IsCount` as its specification
where a row needs it, as everywhere in the classification. -/
def GeneratesOnRec (T : Type) [ValueType T] (sch : Schema)
    (cnt : SeqAggFunc T) (S : Set OpKind) : Prop :=
  ∀ {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ),
    q.overSchema sch → q.usesOnly plainRecOps → q.inMinimalSig cnt →
      ∃ q' : AggQuery T n (ColKind.allReg n),
        q'.overSchema sch ∧ q'.usesOnly S ∧ q'.inMinimalSig cnt ∧ q'.Extends q

/-! ## The rows of `tab:basisclasses` for the whole algebra

Each row below is the statement that a class is in every basis of the
whole algebra in the minimal universe. The witnesses are the plain
fragment's (`Provenance.BasisAssembly`), every one of them in the
minimal signature and recursion-free, hence restricted and defined
everywhere; the invariants are the ones of `Provenance.PlainBasis`
extended through the recursions. What is **not** here is `⊎`: its
thin-instance invariant fails with a recursion
(`μ^⊎R.(S, Π_c(σ_{#1≠c}(R)))` over `{a}` has the rows `a` and `c`),
and the class is indeed not necessary – with a bag recursion the union
is a derived operator (`Provenance.SumByMu`). -/

private theorem settlesAt_of_plain {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (hq : q.usesOnly plainOps) :
    ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ :=
  AggQueryIn.settlesAt_of_usesOnly (S := plainOps)
    (by simp [plainOps, basisDD, basisOps])
    (by simp [plainOps, basisDD, basisOps]) q hq

private theorem plainOps_subset_plainRecOps : plainOps ⊆ plainRecOps :=
  fun x hx => by
    simp only [plainRecOps]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx)

omit [ValueType T] in
private theorem usesOnly_unit_plain :
    (AggQueryIn.unit : AggQuery T 0 (ColKind.allReg 0)).usesOnly plainOps := by
  unfold AggQueryIn.unit
  rw [AggQueryIn.usesOnly_castKind]
  exact ⟨by simp [plainOps, basisDD, basisOps],
    show OpKind.empty ∈ plainOps by simp [plainOps, basisDD, basisOps]⟩

private theorem inSig_unit {Θ : Set (SeqAggFunc T)} :
    (AggQueryIn.unit : AggQuery T 0 (ColKind.allReg 0)).inSig Θ := by
  unfold AggQueryIn.unit
  rw [AggQueryIn.inSig_castKind]
  exact ⟨fun j => j.elim0, fun j => j.elim0, trivial⟩

/-- **`∅` is in every basis of the whole algebra**: over the empty schema
a query can name no relation, and a recursion's base is a query of the
ambient schema, so the base of every recursion there has `∅` for its
only leaf. -/
theorem empty_mem_of_generatesOnRec {cnt : SeqAggFunc T} {S : Set OpKind}
    (hS : GeneratesOnRec T Schema.empty cnt S) : OpKind.empty ∈ S := by
  obtain ⟨q', hsch, hu', -, -⟩ := hS (AggQueryIn.unit : AggQuery T 0 _)
    AggQueryIn.overSchema_unit
    (AggQueryIn.usesOnly_mono plainOps_subset_plainRecOps _ usesOnly_unit_plain)
    inSig_unit
  exact AggQueryIn.usesEmpty_of_overSchema_empty q' hsch hu'

/-- **`γ` is in every basis of the whole algebra**: without it the
all-empty instance has an empty answer, every round of a recursion
included, and the unit has a row there. -/
theorem gamma_mem_of_generatesOnRec {cnt : SeqAggFunc T} {sch : Schema}
    {S : Set OpKind} (hS : GeneratesOnRec T sch cnt S) : OpKind.gamma ∈ S := by
  by_contra hg
  obtain ⟨q', -, hu', -, he⟩ := hS (AggQueryIn.unit : AggQuery T 0 _)
    AggQueryIn.overSchema_unit
    (AggQueryIn.usesOnly_mono plainOps_subset_plainRecOps _ usesOnly_unit_plain)
    inSig_unit
  refine AggQueryIn.evaluatePlain_unit_ne_zero ([] : Database T)
    (fun j => j.elim0) (Eq.trans (he ([] : Database T) (fun j => j.elim0)
      (settlesAt_of_plain _ usesOnly_unit_plain _ _)).2 ?_)
  exact AggQueryIn.evaluatePlain_eq_zero_of_allEmpty hg q' hu'
    ([] : Database T) Database.allEmpty_nil (fun j => j.elim0)

/-- **One of `σ` and `−` is in every basis of the whole algebra**:
without both, a query over the schema is empty on every instance or
non-empty on every full one wherever it is defined, and a selection on
a value is neither. -/
theorem sel_or_diff_mem_of_generatesOnRec {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (hS : GeneratesOnRec ℕ schemaR cnt S) :
    OpKind.sel ∈ S ∨ OpKind.diff ∈ S := by
  by_contra h
  obtain ⟨hsel, hdiff⟩ := not_or.mp h
  have hplain : selWitness.usesOnly plainOps :=
    ⟨by simp [plainOps, basisDD, basisOps], trivial⟩
  obtain ⟨q', hsch, hu', -, he⟩ := hS selWitness (by rfl)
    (AggQueryIn.usesOnly_mono plainOps_subset_plainRecOps _ hplain)
    ⟨rfl, trivial⟩
  refine selWitness_breaks ?_
  rcases AggQueryIn.zero_or_ne_zero_of_noSelDiff hsel hdiff q' hu' hsch with
    h0 | h1
  · exact Or.inl (fun D γ =>
      (he D γ (settlesAt_of_plain _ hplain D γ)).2.trans
        (h0 D γ (he D γ (settlesAt_of_plain _ hplain D γ)).1))
  · exact Or.inr (fun D γ hfull hc =>
      h1 D γ hfull (he D γ (settlesAt_of_plain _ hplain D γ)).1
        ((he D γ (settlesAt_of_plain _ hplain D γ)).2.symm.trans hc))

/-- **`Π` is in every basis of the whole algebra**: without it
multiplicities are bounded by the query wherever it is defined – a
recursive term then reads the previous round tuple by tuple, so a bag
recursion that settles is its base – and a projection of a relation
with a repeated column has unbounded ones. -/
theorem proj_mem_of_generatesOnRec {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (hS : GeneratesOnRec ℕ schemaS cnt S) : OpKind.proj ∈ S := by
  by_contra hp
  have hplain : projWitness.usesOnly plainOps :=
    ⟨⟨by simp [plainOps, basisDD, basisOps], fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rfl⟩, trivial⟩
  obtain ⟨q', hsch, hu', -, he⟩ := hS projWitness (by rfl)
    (AggQueryIn.usesOnly_mono plainOps_subset_plainRecOps _ hplain)
    ⟨fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rfl, trivial⟩
  refine projWitness_unbounded_multiplicity ⟨q'.multBound, fun D hnd u => ?_⟩
  rw [(he D (fun j => j.elim0) (settlesAt_of_plain _ hplain D _)).2]
  exact AggQueryIn.count_le_multBound hp q' hu' (q'.hygienic_of_overSchema _ hsch) D hnd
    (fun j => j.elim0)
    (he D (fun j => j.elim0) (settlesAt_of_plain _ hplain D _)).1 u

/-- **One of `×` and the apply is in every basis of the whole algebra**:
in the minimal universe a recursive term reads the previous round row by
row and its orbits repeat within a bound the query fixes, so an answer
stays linear in the instance, and a relation joined with itself is
quadratic. -/
theorem prod_or_apply_mem_of_generatesOnRec {cnt : SeqAggFunc ℕ}
    {S : Set OpKind} (hS : GeneratesOnRec ℕ schemaR cnt S) :
    OpKind.prod ∈ S ∨ OpKind.apply ∈ S := by
  by_contra h
  obtain ⟨hp, ha⟩ := not_or.mp h
  have hplain : prodWitness.usesOnly plainOps :=
    ⟨by simp [plainOps, basisDD, basisOps], trivial, trivial⟩
  obtain ⟨q', hsch, hu', hsig', he⟩ := hS prodWitness ⟨by rfl, by rfl⟩
    (AggQueryIn.usesOnly_mono plainOps_subset_plainRecOps _ hplain)
    ⟨trivial, trivial⟩
  refine prodWitness_no_linear_bound ⟨q'.sizeBound, fun D => ?_⟩
  rw [(he D (fun j => j.elim0) (settlesAt_of_plain _ hplain D _)).2]
  exact AggQueryIn.card_le_sizeBound hp ha q' hu' (q'.hygienic_of_overSchema _ hsch)
    (AggQueryIn.recNoFun_of_inSig q' hsig') D (fun j => j.elim0)
    (he D (fun j => j.elim0) (settlesAt_of_plain _ hplain D _)).1

theorem overSchema_chainWitness : chainWitness.overSchema schemaSE := by
  refine ⟨rfl, rfl, ⟨trivial, show "E" ≠ "R" by decide⟩, ?_⟩
  exact ⟨rfl, rfl⟩

theorem usesOnly_chainWitness : chainWitness.usesOnly plainRecOps := by
  refine ⟨by simp [plainRecOps, plainOps, basisDD, basisOps], trivial, ?_⟩
  exact ⟨⟨by simp [plainRecOps, plainOps, basisDD, basisOps], fun _ => rfl⟩,
    by simp [plainRecOps, plainOps, basisDD, basisOps],
    by simp [plainRecOps, plainOps, basisDD, basisOps], trivial, trivial⟩

theorem winsDerivable_chainWitness : chainWitness.WinsDerivable :=
  ⟨trivial, trivial, trivial⟩


/-- The base of the witness is the source. -/
theorem evaluatePlain_chainBase (n : ℕ) :
    (AggQueryIn.Rel (T := ℕ) (c := 0) 1 "S").evaluatePlain (dChain n)
      (fun j => j.elim0) = ({node 0} : Multiset (Tuple ℕ 1)) := by
  show (match (dChain n).find 1 "S" with
    | none => (0 : Multiset (Tuple ℕ 1)) | some r => r) = _
  rw [find_dChain_S]

/-- **The witness is defined on every chain**: its rounds end. -/
theorem settlesAt_chainWitness (n : ℕ) :
    chainWitness.SettlesAt (dChain n) (fun j => j.elim0) := by
  refine ⟨trivial, chainStep_zero n, ?_, fun _ => ?_⟩
  · show MuSettles (chainStep n) ((AggQueryIn.Rel (T := ℕ) (c := 0) 1
      "S").evaluatePlain (dChain n) (fun j => j.elim0))
    rw [evaluatePlain_chainBase]
    exact muSettles_chain n
  · exact AggQueryIn.settlesAt_of_usesOnly (S := plainOps)
      (by simp [plainOps, basisDD, basisOps])
      (by simp [plainOps, basisDD, basisOps]) reachStep
      ⟨⟨by simp [plainOps, basisDD, basisOps], fun _ => rfl⟩,
        by simp [plainOps, basisDD, basisOps],
        by simp [plainOps, basisDD, basisOps], trivial, trivial⟩ _ _

/-- The witness is in every signature: no function on values, no
aggregate. -/
theorem inSig_chainWitness {Θ : Set (SeqAggFunc ℕ)} : chainWitness.inSig Θ :=
  ⟨trivial, fun _ => rfl, rfl, trivial, trivial⟩

/-- **`μ^⊎` is in every basis of the whole algebra** (`tab:basisclasses`'s
row): without it, a query of the minimal universe has polynomially many
rows wherever it is defined – set recursions included, their rows being
the duplicate-free tuples over a value set of polynomial size – and the
sink of a chain of `n` diamonds has `2ⁿ`. The one row that reads what
`cnt` is: a count. -/
theorem muBag_mem_of_generatesOnRec {cnt : SeqAggFunc ℕ}
    (hcnt : cnt.IsCount) {S : Set OpKind}
    (hS : GeneratesOnRec ℕ schemaSE cnt S) : OpKind.muBag ∈ S := by
  by_contra hmb
  obtain ⟨q', hsch, hu', hsig', he⟩ := hS chainWitness overSchema_chainWitness
    usesOnly_chainWitness inSig_chainWitness
  obtain ⟨b, k, hb⟩ := AggQueryIn.exists_polyBound_rec hmb hcnt q' hu' (q'.hygienic_of_overSchema _ hsch) hsig'
  refine chainWitness_no_polynomial_bound ⟨b, k, fun n => ?_⟩
  rw [(he (dChain n) (fun j => j.elim0) (settlesAt_chainWitness n)).2]
  exact hb (dChain n) (fun j => j.elim0)
    (he (dChain n) (fun j => j.elim0) (settlesAt_chainWitness n)).1
