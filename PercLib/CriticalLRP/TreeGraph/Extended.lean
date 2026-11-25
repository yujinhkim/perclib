/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The cluster second-moment bound (I.2.3) with `p = 2` on an *infinite* vertex set, in
`ℝ≥0∞` (so no summability hypotheses are needed). This is the form that applies to the
paper's cut-off models `P_{β,r}` on `ℤ^d`: there the vertex set is infinite but the edge type
is finite (the support of the cut-off kernel `J_r`), so `three_point_tree_graph` applies,
while the sums over `ℤ^d` must be extended sums.

Quantities are the `ℝ≥0∞`-valued counterparts of `twoPoint`, `clusterVolume`, `clusterVolSq`
of `Moments.lean`; for finite `V` they agree with the real-valued versions (each is
`ENNReal.ofReal` of it).
-/
module

public import PercLib.CriticalLRP.TreeGraph.ThreePoint

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset
open scoped ENNReal

noncomputable section

variable {V : Type*} [DecidableEq V] [AddCommGroup V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `P(x ↔ y)` as an element of `ℝ≥0∞`. -/
def twoPointE (p : E → ℝ) (ends : E → Sym2 V) (x y : V) : ℝ≥0∞ :=
  ENNReal.ofReal (prob p {s | Conn ends s x y})

/-- `E|K_x| = ∑_y P(x ↔ y)` as an extended sum. -/
def clusterVolumeE (p : E → ℝ) (ends : E → Sym2 V) (x : V) : ℝ≥0∞ :=
  ∑' y : V, twoPointE p ends x y

/-- `E|K_x|² = ∑_{y,z} P(x ↔ y, x ↔ z)` as an extended sum. -/
def clusterVolSqE (p : E → ℝ) (ends : E → Sym2 V) (x : V) : ℝ≥0∞ :=
  ∑' y : V, ∑' z : V, ENNReal.ofReal (prob p {s | Conn ends s x y ∧ Conn ends s x z})

/-- Translation invariance of the two-point function (the paper's transitivity). -/
theorem tsum_twoPointE_eq (p : E → ℝ) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPointE p ends a b = twoPointE p ends o (b - a)) (w : V) :
    (∑' y : V, twoPointE p ends w y) = ∑' x : V, twoPointE p ends o x := by
  rw [tsum_congr fun y => hinv w y]
  have := Equiv.tsum_eq (Equiv.addRight (-w)) (fun x : V => twoPointE p ends o x)
  simpa [sub_eq_add_neg] using this

/-- **(I.2.1) in the paper's own display form**: the right-hand side is the extended sum over
*all* vertices `w` of the product of the three two-point functions. -/
theorem three_point_tree_graph_tsum (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hBK : BKIncreasing p) (ends : E → Sym2 V) (x y z : V) :
    ENNReal.ofReal (prob p {s | Conn ends s x y ∧ Conn ends s x z})
      ≤ ∑' w : V, twoPointE p ends x w * twoPointE p ends w y * twoPointE p ends w z := by
  refine le_trans (ENNReal.ofReal_le_ofReal (three_point_tree_graph hp hp1 hBK ends x y z)) ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun w _ => mul_nonneg (mul_nonneg
    (prob_nonneg hp hp1 _) (prob_nonneg hp hp1 _)) (prob_nonneg hp hp1 _)]
  refine le_trans (ENNReal.sum_le_tsum (candF ends x y z)) (le_of_eq ?_)
  exact tsum_congr fun w => by
    simp only [twoPointE, ENNReal.ofReal_mul (prob_nonneg hp hp1 _),
      ENNReal.ofReal_mul (mul_nonneg (prob_nonneg hp hp1 _) (prob_nonneg hp hp1 _))]

/-- Factoring the triple extended sum. -/
theorem tsum_factor (T : V → V → ℝ≥0∞) (o w : V) :
    (∑' a : V, ∑' b : V, T o w * T w a * T w b)
      = T o w * ((∑' a : V, T w a) * (∑' a : V, T w a)) := by
  have hb : ∀ a : V, (∑' b : V, T o w * T w a * T w b)
      = (T o w * T w a) * (∑' a : V, T w a) := fun a => ENNReal.tsum_mul_left
  simp only [hb]
  have h2 : (∑' a : V, (T o w * T w a) * (∑' a : V, T w a))
      = (∑' a : V, T o w * T w a) * (∑' a : V, T w a) := ENNReal.tsum_mul_right
  rw [h2, ENNReal.tsum_mul_left, mul_assoc]

/-- **Cluster second-moment bound (I.2.3), `p = 2`, infinite vertex set.**
`E|K_o|² ≤ (E|K_o|)³` as extended sums. -/
theorem second_moment_le_infinite (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hBK : BKIncreasing p) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPointE p ends a b = twoPointE p ends o (b - a)) :
    clusterVolSqE p ends o ≤ (clusterVolumeE p ends o) ^ 3 := by
  classical
  -- step 1: termwise bound via (I.2.1)
  have h1 : ∀ y z : V, ENNReal.ofReal (prob p {s | Conn ends s o y ∧ Conn ends s o z})
      ≤ ∑' w : V, twoPointE p ends o w * twoPointE p ends w y * twoPointE p ends w z := by
    intro y z
    refine le_trans (ENNReal.ofReal_le_ofReal
      (three_point_tree_graph hp hp1 hBK ends o y z)) ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun w _ => mul_nonneg (mul_nonneg
      (prob_nonneg hp hp1 _) (prob_nonneg hp hp1 _)) (prob_nonneg hp hp1 _)]
    refine le_trans (ENNReal.sum_le_tsum (candF ends o y z)) (le_of_eq ?_)
    exact tsum_congr fun w => by
      simp only [twoPointE, ENNReal.ofReal_mul (prob_nonneg hp hp1 _),
        ENNReal.ofReal_mul (mul_nonneg (prob_nonneg hp hp1 _) (prob_nonneg hp hp1 _))]
  -- step 2: sum the termwise bounds and factor
  calc clusterVolSqE p ends o
      = ∑' y : V, ∑' z : V, ENNReal.ofReal
          (prob p {s | Conn ends s o y ∧ Conn ends s o z}) := rfl
    _ ≤ ∑' y : V, ∑' z : V, ∑' w : V,
          twoPointE p ends o w * twoPointE p ends w y * twoPointE p ends w z :=
        ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z => h1 y z
    _ = ∑' w : V, ∑' y : V, ∑' z : V,
          twoPointE p ends o w * twoPointE p ends w y * twoPointE p ends w z := by
        rw [show (∑' y : V, ∑' z : V, ∑' w : V,
              twoPointE p ends o w * twoPointE p ends w y * twoPointE p ends w z)
            = ∑' y : V, ∑' w : V, ∑' z : V,
              twoPointE p ends o w * twoPointE p ends w y * twoPointE p ends w z from
          tsum_congr fun y => ENNReal.tsum_comm]
        exact ENNReal.tsum_comm
    _ = ∑' w : V, twoPointE p ends o w *
          ((∑' y : V, twoPointE p ends w y) * (∑' y : V, twoPointE p ends w y)) :=
        tsum_congr fun w => tsum_factor (twoPointE p ends) o w
    _ = ∑' w : V, twoPointE p ends o w *
          ((∑' y : V, twoPointE p ends o y) * (∑' y : V, twoPointE p ends o y)) := by
        refine tsum_congr fun w => ?_
        simp only [tsum_twoPointE_eq p ends o hinv w]
    _ = (∑' y : V, twoPointE p ends o y) ^ 3 := by
        rw [ENNReal.tsum_mul_right]
        ring

end

end PercLib.CriticalLRP.TreeGraph
