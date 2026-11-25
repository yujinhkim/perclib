/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Derivative weight of an actual normalized cutoff edge

The model's off-corner derivative weight, including loop-edge handling. This
method makes no finite- or infinite-volume domination claim.
-/
module

public import PercLib.CriticalLRP.RussoInf.CutoffFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.IntervalAC.Defs

@[expose] public section

noncomputable section

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The `r`-derivative weight of the cut-off edge probability of a single edge, at the actual
source model: `β_c (-K'(r)) e^{-β_c J_r(e)}` on the edges of length `≤ r` whose endpoints are
distinct, and `0` elsewhere (in particular on the loop edges `s(x,x)`, whose kernel value is `0`
for every `r` by construction of `radialSym`).

The length is measured with the model's own norm `M.S.ρ` through `M.S.dist`, not with the
`ℓ^∞` edge length used by the `RussoInf` cut-off instantiation. -/
noncomputable def cutEdgeDeriv (r : ℝ) : Sym2 M.V → ℝ :=
  Sym2.lift ⟨fun x y =>
    if x = y then 0 else
      (if M.S.dist x y ≤ r then
        (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          Real.exp (-((M.betaCrit : ℝ) *
            FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
       else 0), by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · have h' : y ≠ x := fun hh => h hh.symm
      change (if x = y then (0 : ℝ) else
          (if M.S.dist x y ≤ r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0))
        = (if y = x then (0 : ℝ) else
          (if M.S.dist y x ≤ r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist y x)))
           else 0))
      rw [ite_eq_right h, ite_eq_right h', SourceNormData.dist_comm M.S y x]⟩


end SourceModelData

end PercLib.CriticalLRP.Orchestration
