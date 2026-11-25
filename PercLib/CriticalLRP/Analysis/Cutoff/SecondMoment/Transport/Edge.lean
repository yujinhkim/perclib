/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The per-edge `p = 2` increment as a sum of two oriented pair weights

Swarm `smwvbcnfb`, member `m3`, direction `d3`.

Integration donor: `.ultramath/smwvbcnfb/m3`; independently checked at
`8dbe14ef7e6200b83fb48c8568674f938e03bd50`.

The committed `RussoInf/Merge.flipDiff_clusterVol_sq_eq_cases` gives the *complete* pointwise
`p = 2` increment of `|K_0|²` at a closed edge `s(x,y)` in four cases.  This file rewrites that
identity as a sum over the **two orientations** of the edge,

  `Δ|K_0|² = p2OrientReal ω x y + p2OrientReal ω y x`,

which is the exact object the vertex-side mass transport of `Transport.lean`/`Main.lean` consumes:
`p2OrientReal r ω x y` is the term that becomes `p2Weight r ω x y` after the closed-edge
conditional expectation (i.e. after the `1 - q_e` absorption of
`ExcludedFlux.one_sub_mul_pivotalFlux_eq`).

Consequently the `p = 2` edge sum is *literally* the paper's ordered-pair double sum — no
half-weight, no averaging: the two orientations of an edge are mutually exclusive, and the edge
increment is their sum.  The remaining combinatorial step (unordered `Sym2` edge family ↔ ordered
pairs) is recorded, with its exact shape, in `RESULTS.md`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Basic
public import PercLib.CriticalLRP.RussoInf.Merge

/-!
# Oriented per-edge `p = 2` increment
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

namespace PivotFlux

open Orchestration

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-- In the off-region `0 ↔ x`, `x ↮ y`, the oriented weight is the source's increment
`2 |K_0| |K_y| + |K_y|²` (the radius indicator being discharged by `hdist`). -/
theorem p2OrientReal_eq_of_offRegion {r : ℝ} {ω : Config M.V} {x y : M.V}
    (hx : Connects ω (0 : M.V) x) (hy : ¬ Connects ω x y) (hdist : M.S.dist y x ≤ r) :
    p2OrientReal M r ω x y
      = 2 * (clusterVol ω (0 : M.V)).toReal * (clusterVol ω y).toReal
        + (clusterVol ω y).toReal ^ 2 := by
  simp only [p2OrientReal, hx, hy, hdist, ite_true, ite_false]
  ring

/-- The oriented weight vanishes when the anchor does not reach `x`. -/
theorem p2OrientReal_eq_zero_of_not_connects_left {r : ℝ} {ω : Config M.V} {x y : M.V}
    (hx : ¬ Connects ω (0 : M.V) x) : p2OrientReal M r ω x y = 0 := by
  simp only [p2OrientReal, hx, ite_false]
  ring

/-- The oriented weight vanishes when `x` and `y` are connected (in particular when both lie in
the cluster of `0`, or when `x = y`). -/
theorem p2OrientReal_eq_zero_of_connects {r : ℝ} {ω : Config M.V} {x y : M.V}
    (hy : Connects ω x y) : p2OrientReal M r ω x y = 0 := by
  simp only [p2OrientReal, hy, ite_true]
  ring

/-- The oriented weight vanishes outside the radius window. -/
theorem p2OrientReal_eq_zero_of_dist_gt {r : ℝ} {ω : Config M.V} {x y : M.V}
    (h : r < M.S.dist y x) : p2OrientReal M r ω x y = 0 := by
  simp only [p2OrientReal, ite_eq_right (not_le.mpr h)]
  ring

/-- **The per-edge law: the `p = 2` flip increment is the sum of its two oriented pair weights.**

For a closed edge `s(x,y)` with `x ≠ y` and finite volumes at `0`, `x` and `y`, the increment of
`|K_0|²` is `p2OrientReal ω x y + p2OrientReal ω y x`.  The two orientations are mutually
exclusive (at most one of `0 ↔ x` and `0 ↔ y` can hold while `x ↮ y`), so this is an exact sum and
not an average: the edge sum over the unordered edges of the model is the ordered-pair sum of the
oriented weights. -/
theorem flipDiff_clusterVol_sq_eq_p2OrientReal_add {r : ℝ} {ω : Config M.V} {x y : M.V}
    (hxy : x ≠ y) (he : s(x, y) ∉ ω) (hdist : M.S.dist x y ≤ r)
    (hK : clusterVol ω (0 : M.V) ≠ ⊤) (hKx : clusterVol ω x ≠ ⊤)
    (hKy : clusterVol ω y ≠ ⊤) :
    flipDiff (fun η => (clusterVol η (0 : M.V)).toReal ^ 2) (s(x, y)) ω
      = p2OrientReal M r ω x y + p2OrientReal M r ω y x := by
  rw [flipDiff_clusterVol_sq_eq_cases (o := (0 : M.V)) hxy he hK hKx hKy]
  by_cases hx : x ∈ cluster ω (0 : M.V) <;> by_cases hy : y ∈ cluster ω (0 : M.V)
  · have hc : Connects ω (0 : M.V) x := mem_cluster_iff.mp hx
    have hcy : Connects ω (0 : M.V) y := mem_cluster_iff.mp hy
    have hconn : Connects ω x y := connects_trans (connects_symm hc) hcy
    rw [p2OrientReal_eq_zero_of_connects M (r := r) hconn,
      p2OrientReal_eq_zero_of_connects M (r := r) (connects_symm hconn)]
    simp only [hx, hy, ite_true, ite_false]
    ring
  · have hc : Connects ω (0 : M.V) x := mem_cluster_iff.mp hx
    have hcy : ¬ Connects ω (0 : M.V) y := fun h => hy (mem_cluster_iff.mpr h)
    have hnc : ¬ Connects ω x y := fun h => hcy (connects_trans hc h)
    rw [p2OrientReal_eq_of_offRegion M hc hnc (by rwa [M.S.dist_comm]),
      p2OrientReal_eq_zero_of_not_connects_left M hcy]
    simp only [hx, hy, ite_true, ite_false]
    ring
  · have hc : ¬ Connects ω (0 : M.V) x := fun h => hx (mem_cluster_iff.mpr h)
    have hcy : Connects ω (0 : M.V) y := mem_cluster_iff.mp hy
    have hnc : ¬ Connects ω y x := fun h => hc (connects_trans hcy h)
    rw [p2OrientReal_eq_zero_of_not_connects_left M hc,
      p2OrientReal_eq_of_offRegion M hcy hnc hdist]
    simp only [hx, hy, ite_true, ite_false]
    ring
  · have hc : ¬ Connects ω (0 : M.V) x := fun h => hx (mem_cluster_iff.mpr h)
    have hcy : ¬ Connects ω (0 : M.V) y := fun h => hy (mem_cluster_iff.mpr h)
    rw [p2OrientReal_eq_zero_of_not_connects_left M hc,
      p2OrientReal_eq_zero_of_not_connects_left M hcy]
    simp only [hx, hy, ite_true, ite_false]
    ring

end PivotFlux

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.PivotFlux

#print axioms p2OrientReal_eq_of_offRegion
#print axioms p2OrientReal_eq_zero_of_not_connects_left
#print axioms p2OrientReal_eq_zero_of_connects
#print axioms p2OrientReal_eq_zero_of_dist_gt
#print axioms flipDiff_clusterVol_sq_eq_p2OrientReal_add

end PercLib.CriticalLRP.PivotFlux
