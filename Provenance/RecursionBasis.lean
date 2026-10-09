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
def reachStep : AggQuery ℕ 1 (ColKind.allReg 1) :=
  AggQueryIn.Proj (fun _ : Fin 1 =>
      ProjColIn.term (TermGIn.index (2 : Fin (1 + 2)) rfl))
    (AggQueryIn.Sel
      (GenPredIn.cmp CompOp.syneq (TermGIn.index (0 : Fin (1 + 2)) rfl)
        (TermGIn.index (1 : Fin (1 + 2)) rfl))
      (AggQueryIn.Prod (AggQueryIn.Rel 1 "R") (AggQueryIn.Rel 2 "E")))

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
    ¬ ∃ c k : ℕ, ∀ D : Database ℕ,
      Multiset.card (chainWitness.evaluatePlain D (fun j => j.elim0))
        ≤ c * (D.size + 1) ^ k := by
  rintro ⟨c, k, h⟩
  obtain ⟨n, hn⟩ := exists_lt_two_pow c k
  have hb := h (dChain n)
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
def AggQueryIn.noRec : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → Prop
  | _, _, _, .Rel _ _ => True
  | _, _, _, .Empty => True
  | _, _, _, .Proj _ q => q.noRec
  | _, _, _, .Sel _ q => q.noRec
  | _, _, _, .Prod q₁ q₂ => q₁.noRec ∧ q₂.noRec
  | _, _, _, .Apply q₁ q₂ => q₁.noRec ∧ q₂.noRec
  | _, _, _, .Sum q₁ q₂ => q₁.noRec ∧ q₂.noRec
  | _, _, _, .Dedup q => q.noRec
  | _, _, _, .Diff q₁ q₂ => q₁.noRec ∧ q₂.noRec
  | _, _, _, .Alt _ _ q => q.noRec
  | _, _, _, .Mu _ _ _ => False
  | _, _, _, .MuSet _ _ _ => False
  | _, _, _, .Gamma _ _ _ q _ _ => q.noRec
  | _, _, _, .GammaScalar _ _ q _ => q.noRec
  | _, _, _, .GammaNest _ _ _ _ q => q.noRec
  | _, _, _, .ProvSum _ _ _ q => q.noRec
  | _, _, _, .Retag _ q => q.noRec
  | _, _, _, .GammaTok _ _ _ _ _ q _ => q.noRec
  | _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noRec
  | _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noRec

/-- Raising the degree only weakens a bound. -/
private theorem poly_le_poly {b k k' m : ℕ} (h : k ≤ k') :
    b * (m + 1) ^ k ≤ b * (m + 1) ^ k' :=
  Nat.mul_le_mul_left b (Nat.pow_le_pow_right (by omega) h)

/-- **A recursion-free query has polynomially many rows**, multiplicities
included, and the polynomial is uniform in the context: an apply's right
side is bounded independently of the parameters it reads. -/
theorem AggQueryIn.exists_polyBound :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ), q.noRec →
      ∃ b k : ℕ, ∀ (D : Database T) (γ : Fin c → T),
        Multiset.card (q.evaluatePlain D γ) ≤ b * (D.size + 1) ^ k := by
  intro c n κ q
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
  | Empty => exact fun _ => ⟨0, 0, fun _ _ => Nat.zero_le _⟩
  | Proj ps q ih =>
    refine fun hq => ?_
    obtain ⟨b, k, hb⟩ := ih hq
    exact ⟨b, k, fun D γ => by
      show Multiset.card (Multiset.map _ (q.evaluatePlain D γ)) ≤ _
      rw [Multiset.card_map]; exact hb D γ⟩
  | Sel φ q ih =>
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
