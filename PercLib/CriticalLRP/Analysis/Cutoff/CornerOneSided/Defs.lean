/-
# One-sided cutoff derivative weights and the scalar corner example

Accepted from swarm `smwtvrwnn` member `m8`, direction D1D.
The strict weight is used for left derivatives; the existing closed weight
`SourceModelData.cutEdgeDeriv` is used for right derivatives.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv
public import PercLib.CriticalLRP.CutoffCorner

/-!
Definitions for one-sided derivative calculations at attained cutoff radii.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The strict (left) derivative weight of a cut-off edge.**

This is the `s < r` version of `M.cutEdgeDeriv`: the radius strictly exceeds the edge length, so
the cut-off profile is `K s - K r` in a *two-sided* neighbourhood of `r` and the weight is the
ordinary derivative.  At a corner radius `r = M.S.dist x y` the left derivative of the edge
probability is `0`, which is what this weight gives. -/
noncomputable def cutEdgeDerivLeft (r : ℝ) : Sym2 M.V → ℝ :=
  Sym2.lift ⟨fun x y =>
    if x = y then 0 else
      (if M.S.dist x y < r then
        (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          Real.exp (-((M.betaCrit : ℝ) *
            FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
       else 0), by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · have h' : y ≠ x := fun hh => h hh.symm
      change (if x = y then (0 : ℝ) else
          (if M.S.dist x y < r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0))
        = (if y = x then (0 : ℝ) else
          (if M.S.dist y x < r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist y x)))
           else 0))
      rw [ite_eq_right h, ite_eq_right h', SourceNormData.dist_comm M.S y x]⟩

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.FiniteVolume

/-- The open probability of an edge of length `s` at radius `r`, `q_r(s)`. -/
noncomputable def edgeOpenProb (K : ℝ → ℝ) (β r s : ℝ) : ℝ :=
  longRangeEdgeProbability β (cutoffProfile K r s)

end PercLib.CriticalLRP.FiniteVolume
