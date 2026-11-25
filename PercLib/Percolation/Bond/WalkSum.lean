module

public import PercLib.Meta.Tag

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Deterministic walk sums

All weights lie in the extended nonnegative reals. A step from a vertex to itself
is allowed: these statements make no assumption about the diagonal of the kernel.

The general row-sum estimate is deliberately independent of percolation. The
diagonal-masked specialization is the form used for bond percolation.

`walkWeight` is the product along an explicit vertex sequence, and
`walkSum_eq_tsum_walkWeight` identifies its sum with the recursion. These walks
may repeat edges: interpreting the product as an independent-edge probability
requires a separate restriction to paths with distinct edges.

New proofs for PercLib, using the pinned mathlib API located by SCOUT in
issue #17; no upstream proof is copied.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Product of the step weights along an explicit sequence of `n` successive
vertices, starting at `v`. Repeated vertices and self-steps are allowed. -/
def walkWeight (a : V → V → ℝ≥0∞) {n : ℕ} (v : V) (p : Fin n → V) : ℝ≥0∞ :=
  ∏ i : Fin n, a ((Fin.cons v p : Fin (n + 1) → V) i.castSucc) (p i)

@[simp]
theorem walkWeight_zero (a : V → V → ℝ≥0∞) (v : V) (p : Fin 0 → V) :
    walkWeight a v p = 1 := by simp [walkWeight]

@[simp]
theorem walkWeight_cons (a : V → V → ℝ≥0∞) {n : ℕ} (v w : V)
    (p : Fin n → V) :
    walkWeight a v (Fin.cons w p) = a v w * walkWeight a w p := by
  simp [walkWeight, Fin.prod_univ_succ]

/-- Total weight of all length-`n` continuations of a walk starting at `v`.
The empty continuation has weight one. -/
@[tag "I9QY"]
def walkSum (a : V → V → ℝ≥0∞) : ℕ → V → ℝ≥0∞
  | 0, _ => 1
  | n + 1, v => ∑' w, a v w * walkSum a n w

@[simp]
theorem walkSum_zero (a : V → V → ℝ≥0∞) (v : V) : walkSum a 0 v = 1 := rfl

@[simp]
theorem walkSum_succ (a : V → V → ℝ≥0∞) (n : ℕ) (v : V) :
    walkSum a (n + 1) v = ∑' w, a v w * walkSum a n w := rfl

/-- The recursive walk sum is exactly the sum of products over all vertex
sequences. This is the deterministic bridge used when enlarging a path sum. -/
theorem walkSum_eq_tsum_walkWeight (a : V → V → ℝ≥0∞) (n : ℕ) (v : V) :
    walkSum a n v = ∑' p : Fin n → V, walkWeight a v p := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => V)).tsum_eq]
    change walkSum a (n + 1) v =
      ∑' p : V × (Fin n → V), walkWeight a v (Fin.cons p.1 p.2)
    rw [ENNReal.tsum_prod']
    simp_rw [walkWeight_cons, ENNReal.tsum_mul_left, ← ih]
    rfl

/-- A uniform row-sum bound controls the total weight at every fixed walk length.
The bound includes walks with self-steps and holds for arbitrary vertex types. -/
theorem walkSum_le_pow (a : V → V → ℝ≥0∞) (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, a v w) ≤ m) (n : ℕ) (v : V) :
    walkSum a n v ≤ m ^ n := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    calc
      walkSum a (n + 1) v = ∑' w, a v w * walkSum a n w := rfl
      _ ≤ ∑' w, a v w * m ^ n := by
        apply ENNReal.tsum_le_tsum
        intro w
        exact mul_le_mul_right (ih w) _
      _ = (∑' w, a v w) * m ^ n := ENNReal.tsum_mul_right
      _ ≤ m * m ^ n := mul_le_mul_left (hrow v) _
      _ = m ^ (n + 1) := by rw [pow_succ]; ac_rfl

/-- The sum over all lengths is controlled by the geometric series. -/
theorem walkSum_total_le (a : V → V → ℝ≥0∞) (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, a v w) ≤ m) (_hm : m < 1) (v : V) :
    (∑' n : ℕ, walkSum a n v) ≤ (1 - m)⁻¹ := by
  calc
    (∑' n : ℕ, walkSum a n v) ≤ ∑' n : ℕ, m ^ n :=
      ENNReal.tsum_le_tsum (fun n => walkSum_le_pow a m hrow n v)
    _ = (1 - m)⁻¹ := ENNReal.tsum_geometric m

/-- A strictly subunit row bound makes the total walk weight finite. -/
theorem walkSum_total_lt_top (a : V → V → ℝ≥0∞) (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, a v w) ≤ m) (hm : m < 1) (v : V) :
    (∑' n : ℕ, walkSum a n v) < ⊤ := by
  exact lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun n => walkSum_le_pow a m hrow n v))
    (tsum_geometric_lt_top.2 hm)

/-- The off-diagonal part of a kernel, with no hypothesis on the original
diagonal values. Classical decidability is used only to define the mask. -/
def offDiagonal (a : V → V → ℝ≥0∞) (v w : V) : ℝ≥0∞ := by
  classical
  exact if w = v then 0 else a v w

/-- Unfolding the mask gives the explicit row-sum spelling used in P-5. -/
theorem offDiagonal_apply (a : V → V → ℝ≥0∞) (v w : V) :
    offDiagonal a v w = if w = v then 0 else a v w := rfl

@[simp]
theorem offDiagonal_self (a : V → V → ℝ≥0∞) (v : V) :
    offDiagonal a v v = 0 := by
  classical
  simp [offDiagonal]

/-- Excluding the diagonal in the row sum means applying the general estimate
to the kernel whose diagonal has been set to zero. -/
theorem walkSum_masked_le_pow (a : V → V → ℝ≥0∞) (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, offDiagonal a v w) ≤ m)
    (n : ℕ) (v : V) :
    walkSum (offDiagonal a) n v ≤ m ^ n :=
  walkSum_le_pow (offDiagonal a) m hrow n v

/-- Geometric bound for all lengths using only the off-diagonal entries. -/
theorem walkSum_masked_total_le (a : V → V → ℝ≥0∞) (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, offDiagonal a v w) ≤ m)
    (hm : m < 1) (v : V) :
    (∑' n : ℕ, walkSum (offDiagonal a) n v) ≤ (1 - m)⁻¹ :=
  walkSum_total_le (offDiagonal a) m hrow hm v

/-! Non-vacuity and boundary cases. -/

/-- On a single vertex the bound is attained, including nonzero diagonal
weights, the critical value `r = 1`, and the extended value `r = ⊤`. -/
example (r : ℝ≥0∞) (n : ℕ) :
    walkSum (fun (_ _ : Unit) => r) n () = r ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, pow_succ, mul_comm]

/-- Even an infinite original diagonal is irrelevant to the masked bound. -/
example (v : V) :
    (∑' n : ℕ, walkSum
      (offDiagonal (fun x y : V => if y = x then ⊤ else 0)) n v) ≤ 1 := by
  simpa using walkSum_masked_total_le
    (fun x y : V => if y = x then ⊤ else 0) 0 (by simp [offDiagonal])
    (by simp) v

example (v : Bool) :
    (∑' n : ℕ, walkSum (fun (_ _ : Bool) => (0 : ℝ≥0∞)) n v) ≤ 1 := by
  have hrow : ∀ x : Bool, (∑' y : Bool, (0 : ℝ≥0∞)) ≤ 0 := by simp
  simpa using walkSum_total_le (fun (_ _ : Bool) => (0 : ℝ≥0∞)) 0 hrow
    (by norm_num) v

end PercLib.Percolation.Bond

end
