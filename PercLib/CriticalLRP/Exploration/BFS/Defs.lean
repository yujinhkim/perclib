/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Definition of deterministic BFS generations, queried histories and extended powers.

Accepted from independent submission `smwpalb9h` direction D2.
No generation-moment induction or cluster-moment finiteness is asserted here.
-/
module

/-
Private swarm module (member m2, swarm smwpalb9h), direction 2.

Deterministic BFS generation/exploration on the repository's *actual* product:
`PercLib.Percolation.Bond.Config V = Set (Sym2 V)` with `cluster ω o` the open
cluster of `o` in `SimpleGraph.fromEdgeSet ω`.  No local finiteness, no degree
bound, no host graph.

Definitions follow the accepted outline: `A k` frontier, `P k` processed,
`U k` undiscovered, `G (k+1) = A (k+1)`, and the queried edge set
`E(A k, U k)`.  The "revealed" set `R k` of the outline (edges incident to
`P k`) is `revealed`; the actually queried edges are `seen`.
-/
public import PercLib.Percolation.Bond.Basic
public import Mathlib.Data.Set.Card.Arithmetic

set_option autoImplicit false


@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

/-- State of the frontier exploration: `A` is the current frontier (discovered,
not yet processed), `P` the processed set, `U` the undiscovered set. -/
structure State (V : Type*) where
  /-- Frontier: discovered but not yet processed vertices. -/
  A : Set V
  /-- Processed vertices. -/
  P : Set V
  /-- Undiscovered vertices. -/
  U : Set V

/-- The new generation reached from frontier `A` into undiscovered `U`. -/
def newGen (ω : Config V) (A U : Set V) : Set V :=
  {y ∈ U | ∃ x ∈ A, s(x, y) ∈ ω}

/-- One exploration step: reveal all edges from the frontier into the
undiscovered set, move the frontier to the new generation. -/
def step (ω : Config V) (st : State V) : State V where
  A := newGen ω st.A st.U
  P := st.P ∪ st.A
  U := st.U \ newGen ω st.A st.U

/-- The exploration state after `k` steps.  `A 0 = {o}`, `P 0 = ∅`,
`U 0 = {o}ᶜ` exactly as in the outline. -/
def state (ω : Config V) (o : V) : ℕ → State V
  | 0 => ⟨{o}, ∅, {o}ᶜ⟩
  | n + 1 => step ω (state ω o n)

/-- Frontier `A k`. -/
def A (ω : Config V) (o : V) (k : ℕ) : Set V := (state ω o k).A

/-- Processed set `P k`. -/
def P (ω : Config V) (o : V) (k : ℕ) : Set V := (state ω o k).P

/-- Undiscovered set `U k`. -/
def U (ω : Config V) (o : V) (k : ℕ) : Set V := (state ω o k).U

/-- The generation `G (k+1) = A (k+1)` discovered at step `k`. -/
def gen (ω : Config V) (o : V) (k : ℕ) : Set V := A ω o (k + 1)

/-- The finite-horizon discovered set `{o} ∪ ⋃_{j<k} G (j+1) = P k ∪ A k`. -/
def horizon (ω : Config V) (o : V) (k : ℕ) : Set V := P ω o k ∪ A ω o k

/-- The edge set `E(A,U)` of pairs with one endpoint in `A` and one in `U`. -/
def edgeSet (A U : Set V) : Set (Sym2 V) :=
  {e | ∃ x ∈ A, ∃ y ∈ U, e = s(x, y)}

/-- The edges queried at step `k`: the set `E(A k, U k)`. -/
def queried (ω : Config V) (o : V) (k : ℕ) : Set (Sym2 V) :=
  edgeSet (A ω o k) (U ω o k)

/-- The edge set `R k` of the outline: all edges incident to the processed set. -/
def revealed (ω : Config V) (o : V) (k : ℕ) : Set (Sym2 V) :=
  {e | ∃ v ∈ P ω o k, v ∈ e}

/-- The actually queried edges before step `k`: `⋃_{j<k} E(A j, U j)`. -/
def seen (ω : Config V) (o : V) (k : ℕ) : Set (Sym2 V) :=
  ⋃ j : {j : ℕ // j < k}, queried ω o j

/-! ### Unfolding lemmas -/

@[simp] theorem A_zero (ω : Config V) (o : V) : A ω o 0 = {o} := rfl
@[simp] theorem P_zero (ω : Config V) (o : V) : P ω o 0 = ∅ := rfl
@[simp] theorem U_zero (ω : Config V) (o : V) : U ω o 0 = {o}ᶜ := rfl

theorem A_succ (ω : Config V) (o : V) (k : ℕ) :
    A ω o (k + 1) = {y ∈ U ω o k | ∃ x ∈ A ω o k, s(x, y) ∈ ω} := rfl

theorem P_succ (ω : Config V) (o : V) (k : ℕ) :
    P ω o (k + 1) = P ω o k ∪ A ω o k := rfl

theorem U_succ (ω : Config V) (o : V) (k : ℕ) :
    U ω o (k + 1) = U ω o k \ A ω o (k + 1) := rfl

@[simp] theorem gen_eq (ω : Config V) (o : V) (k : ℕ) :
    gen ω o k = {y ∈ U ω o k | ∃ x ∈ A ω o k, s(x, y) ∈ ω} := rfl

theorem gen_subset_U (ω : Config V) (o : V) (k : ℕ) : gen ω o k ⊆ U ω o k :=
  fun _ hy => hy.1

theorem horizon_eq (ω : Config V) (o : V) (k : ℕ) :
    horizon ω o k = P ω o k ∪ A ω o k := rfl

theorem state_eq (ω : Config V) (o : V) (k : ℕ) :
    state ω o k = ⟨A ω o k, P ω o k, U ω o k⟩ := by
  cases k <;> rfl

/-! ### Extended power on `ℕ∞`

The frontier moment induction compares `λ^{|G|}` for a generation `G` whose
cardinality is an extended natural.  `epow lam n` is the supremum of the finite
powers `lam ^ k` over `k ≤ n`; on finite `n` it is the usual real power, and it
is the monotone extension used in the infinite-volume limit.
-/

/-- Extended power on `ℕ∞`: the supremum of the finite powers `lam ^ k` for
`k ≤ n`.  For `n = (m : ℕ∞)` this is `lam ^ m`; the definition extends it
monotonically to `n = ⊤`. -/
noncomputable def epow (lam : ℝ≥0∞) (n : ℕ∞) : ℝ≥0∞ :=
  ⨆ k : ℕ, lam ^ (((n ⊓ (k : ℕ∞))).toNat : ℝ)

end PercLib.CriticalLRP.Exploration.BFS
