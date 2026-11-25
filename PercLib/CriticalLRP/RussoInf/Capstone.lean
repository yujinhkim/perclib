/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Capstone: absolute summability of the cut-off pivotal flux

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.1.

For the cut-off model `P_{β,r}` on `ℤ^d`, the `r`-derivative of the edge
probability `q_e(r) = 1 - exp(-β J_r(e))` is `β|J'(r)|(1 - q_e)` on the active
edges (`cutoffEdgeDeriv_hasDerivAt`, from `KernelGeometry`), and its total mass
at any vertex is at most `β|J'(r)|(2⌈r⌉₊+1)^d` (`CutoffFlux.cutoff_edgeDeriv_degree`).

Therefore the pivotal flux of the capped cluster-volume functional
`min((min(|K_0|,n))^p, m)` is absolutely summable with the explicit bound
`2 m · β|J'(r)| (2⌈r⌉₊+1)^d · E|K_0|` as soon as `E|K_0|` is finite — the
finiteness input that the paper obtains from sharpness of the phase transition.
-/
module

public import PercLib.CriticalLRP.RussoInf.CutoffFlux
public import PercLib.CriticalLRP.CutoffRusso

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

namespace CutoffFlux

/-- Two `if`-then-else expressions with the same (decidable) condition agree, whatever `Decidable`
instances are used to write them. -/
theorem ite_inst_irrel {α : Type*} {P : Prop} (inst1 inst2 : Decidable P) (a b : α) :
    @ite α P inst1 a b = @ite α P inst2 a b := by
  have h : inst1 = inst2 := Subsingleton.elim inst1 inst2
  rw [h]

variable {d : ℕ}

/-- The derivative weight `cutoffEdgeDeriv` is exactly the `r`-derivative of the cut-off edge
probability, away from the corner `r = ‖e‖` (compare
`FiniteVolume.hasDerivAt_cutoffEdgeProbability_if`). -/
theorem cutoffEdgeDeriv_hasDerivAt {K : ℝ → ℝ} {β K' r : ℝ} {e : Sym2 (Fin d → ℤ)}
    (hne : FiniteVolume.edgeLen e ≠ r) (hK : HasDerivAt K (-K') r) :
    HasDerivAt (fun r' => longRangeEdgeProbability β
        (FiniteVolume.cutoffProfile K r' (FiniteVolume.edgeLen e)))
      (cutoffEdgeDeriv K β K' r e) r := by
  have h := FiniteVolume.hasDerivAt_cutoffEdgeProbability_if (K := K) (K' := K')
    hne hK β
  have hval : cutoffEdgeDeriv K β K' r e
      = (if (FiniteVolume.edgeLen e : ℝ) ≤ r then
          β * K' * Real.exp (-(β * FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)))
        else 0) := by
    unfold cutoffEdgeDeriv
    by_cases h1 : (FiniteVolume.edgeLen e : ℝ) ≤ r
    · rw [ite_eq_left h1, ite_eq_left h1, FiniteVolume.one_sub_cutoffEdgeProbability]
    · rw [ite_eq_right h1, ite_eq_right h1]
  rw [hval]
  exact h

/-- **Absolute summability of the cut-off pivotal flux.**  For the capped cluster-volume functional
of the origin, any per-vertex bound `D` on the derivative weights gives absolute summability of the
pivotal flux with total mass at most `2 m D E|K_0|`.

The per-vertex bound is supplied by `CutoffFlux.cutoff_edgeDeriv_degree` with
`D = β|J'(r)| (2⌈r⌉₊ + 1)^d`; it is kept as an explicit hypothesis because the `if` in the
general-type statement of `tsum_abs_pivotalFlux_le` is elaborated with Lean's classical
`Decidable` instance while the lattice statement uses the `DecidableEq` instance of `Fin d → ℤ`
(`CutoffFlux.ite_inst_irrel` shows that the two `if`-expressions are equal). -/
theorem cutoff_tsum_abs_pivotalFlux_le (μ : Measure (Config (Fin d → ℤ)))
    [IsProbabilityMeasure μ] {c : Sym2 (Fin d → ℤ) → ℝ} {D m : ℝ} (hm : 0 ≤ m) (hD : 0 ≤ D)
    (hdeg : ∀ x : Fin d → ℤ, ∀ u : Finset (Sym2 (Fin d → ℤ)),
      ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (p : ℕ) (n m' : ℝ) (hmm : 0 ≤ m')
    (hvol : ∫⁻ ω, clusterVol ω 0 ∂μ ≠ ⊤) :
    ∑' e : Sym2 (Fin d → ℤ), |c e * pivotalFlux μ (cappedClusterVol 0 p n m') e|
      ≤ 2 * max m' 0 * D * (∫⁻ ω, clusterVol ω 0 ∂μ).toReal := by
  refine tsum_abs_pivotalFlux_le (o := 0) μ c (D := D) (m := max m' 0)
    (le_max_right _ _) hD ?_ (cappedClusterVol_bound 0 p n m' hmm)
    (measurable_cappedClusterVol 0 p n m') (cappedClusterVol_dep 0 p n m') hvol
  intro x u
  refine le_trans (le_of_eq ?_) (hdeg x u)
  refine Finset.sum_congr rfl fun e _ => ?_
  exact congrArg (fun t => |c e| * t) (ite_inst_irrel _ _ _ _)

end CutoffFlux

end PercLib.CriticalLRP
