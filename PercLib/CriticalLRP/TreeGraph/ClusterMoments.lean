/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The cluster-moment bound (I.2.3) of Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, Section I.2, p. 22:

    `E_β |K|^p ≤ (2p − 3)!! (E_β |K|)^{2p−1}`   for every integer `p ≥ 1`,

proved here in the cases `p = 1` (trivial) and `p = 2` (the constant is `1!! = 1`), which is
the case obtained from the three-point tree-graph inequality (I.2.1) by summing over the two
free vertices. The cases `p ≥ 3` require the general `(p+1)`-point tree-graph inequality
(I.2.2) together with the enumeration of trees with `p + 1` labelled leaves and all internal
vertices of degree 3 (there are `(2p−3)!!` of them); that is *not* done here and is recorded
as an explicit gap in the report.

Setting: `V` is a finite vertex set (so all the sums below are finite sums). The paper's
"transitive weighted graph" enters through translation invariance of the two-point function
(`hinv` below): `P(a ↔ b) = T(b − a)`. Under that hypothesis the total mass `∑_x P(w ↔ x)`
of the two-point function is independent of `w`, which is the only property of transitivity
used.
-/
module

public import PercLib.CriticalLRP.TreeGraph.ThreePoint

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset

noncomputable section

variable {V : Type*} [DecidableEq V] [Fintype V] [AddCommGroup V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The two-point function and cluster moments -/

/-- The two-point connectivity function `P(x ↔ y)`. -/
def twoPoint (p : E → ℝ) (ends : E → Sym2 V) (x y : V) : ℝ := prob p {s | Conn ends s x y}

/-- The expected cluster volume `E|K_x|`, written as the total mass of the two-point
function: `E|K_x| = ∑_y P(x ↔ y)`. -/
def clusterVolume (p : E → ℝ) (ends : E → Sym2 V) (x : V) : ℝ := ∑ y : V, twoPoint p ends x y

/-- The second moment `E|K_x|² = ∑_{y,z} P(x ↔ y, x ↔ z)` of the cluster volume. -/
def clusterVolSq (p : E → ℝ) (ends : E → Sym2 V) (x : V) : ℝ :=
  ∑ y : V, ∑ z : V, prob p {s | Conn ends s x y ∧ Conn ends s x z}

/-! ### Translation invariance of the two-point function -/

/-- Translation invariance of the two-point function: under a transitive model the two-point
function depends only on the difference of its arguments. It implies that the total mass
`∑_y P(w ↔ y)` does not depend on `w`. -/
theorem twoPoint_total_eq (p : E → ℝ) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint p ends a b = twoPoint p ends o (b - a)) (w : V) :
    ∑ y : V, twoPoint p ends w y = ∑ x : V, twoPoint p ends o x := by
  rw [Finset.sum_congr rfl fun y (_ : y ∈ univ) => hinv w y]
  have hshift : (∑ y : V, twoPoint p ends o (y + -w)) = ∑ x : V, twoPoint p ends o x :=
    Fintype.sum_equiv (Equiv.addRight (-w)) (fun y => twoPoint p ends o (y + -w))
      (fun x => twoPoint p ends o x) fun _ => rfl
  simpa [sub_eq_add_neg] using hshift

/-! ### (I.2.3) for `p = 2` -/

/-- Summation identity behind the `p = 2` moment bound: after inserting the three-point
tree-graph bound and swapping the sums, the triple sum factors. -/
theorem triple_sum_factor (T : V → V → ℝ) (o : V) :
    (∑ y : V, ∑ z : V, ∑ w : V, T o w * T w y * T w z)
      = ∑ w : V, T o w * ((∑ y : V, T w y) * (∑ z : V, T w z)) := by
  have h1 : ∀ y : V, (∑ z : V, ∑ w : V, T o w * T w y * T w z)
      = ∑ w : V, ∑ z : V, T o w * T w y * T w z :=
    fun y => Finset.sum_comm
  calc (∑ y : V, ∑ z : V, ∑ w : V, T o w * T w y * T w z)
      = ∑ y : V, ∑ w : V, ∑ z : V, T o w * T w y * T w z :=
        Finset.sum_congr rfl fun y _ => h1 y
    _ = ∑ w : V, ∑ y : V, ∑ z : V, T o w * T w y * T w z := Finset.sum_comm
    _ = ∑ w : V, T o w * ((∑ y : V, T w y) * (∑ z : V, T w z)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        have step1 : (∑ y : V, ∑ z : V, T o w * T w y * T w z)
            = ∑ y : V, (T o w * T w y) * (∑ z : V, T w z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
        have step2 : (∑ y : V, (T o w * T w y) * (∑ z : V, T w z))
            = (∑ y : V, T o w * T w y) * (∑ z : V, T w z) := (Finset.sum_mul ..).symm
        have step3 : (∑ y : V, T o w * T w y) = T o w * (∑ y : V, T w y) :=
          (Finset.mul_sum ..).symm
        rw [step1, step2, step3]
        ring

/-- **Tree-graph moment bound (I.2.3), `p = 2`.** The second moment of the cluster volume of
`o` is at most the cube of its first moment: `E|K_o|² ≤ (2·2−3)!! (E|K_o|)³ = (E|K_o|)³`.

This is the paper's bound obtained by summing the three-point tree-graph inequality (I.2.1)
over the two free vertices. -/
theorem second_moment_le (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hBK : BKIncreasing p) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint p ends a b = twoPoint p ends o (b - a)) :
    clusterVolSq p ends o ≤ (clusterVolume p ends o) ^ 3 := by
  classical
  set T : V → V → ℝ := twoPoint p ends with hT
  have hT0 : ∀ a b : V, 0 ≤ T a b := fun a b => prob_nonneg hp hp1 _
  -- step 1: insert (I.2.1) termwise and pass to the full sum over `V`
  have hstep : ∀ y z : V, prob p {s | Conn ends s o y ∧ Conn ends s o z}
      ≤ ∑ w : V, T o w * T w y * T w z := by
    intro y z
    refine le_trans (three_point_tree_graph hp hp1 hBK ends o y z) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro w _ _
    exact mul_nonneg (mul_nonneg (hT0 o w) (hT0 w y)) (hT0 w z)
  calc clusterVolSq p ends o
      = ∑ y : V, ∑ z : V, prob p {s | Conn ends s o y ∧ Conn ends s o z} := rfl
    _ ≤ ∑ y : V, ∑ z : V, ∑ w : V, T o w * T w y * T w z :=
        Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun z _ => hstep y z
    _ = ∑ w : V, T o w * ((∑ y : V, T w y) * (∑ z : V, T w z)) := triple_sum_factor T o
    _ = ∑ w : V, T o w * (clusterVolume p ends o * clusterVolume p ends o) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        have hw : (∑ y : V, T w y) = clusterVolume p ends o := by
          simp only [hT, clusterVolume]
          exact twoPoint_total_eq p ends o hinv w
        rw [hw]
    _ = (∑ w : V, T o w) * (clusterVolume p ends o * clusterVolume p ends o) := by
        rw [Finset.sum_mul]
    _ = (clusterVolume p ends o) ^ 3 := by
        have hS : (∑ w : V, T o w) = clusterVolume p ends o := by simp only [hT, clusterVolume]
        rw [hS]
        ring

/-- The first-moment case of (I.2.3), recorded for completeness. -/
theorem first_moment_le (p : E → ℝ) (ends : E → Sym2 V) (o : V) :
    clusterVolume p ends o ≤ (clusterVolume p ends o) ^ 1 := by rw [pow_one]

end

end PercLib.CriticalLRP.TreeGraph
