/-
Finite-volume generalized-norm Russo handoff (swarm `smwtrtcqs`, member `m6`, direction D2).

Instantiation of the finite-volume incremental Russo formula at the **actual source model data**
`SourceModelData`: the edge lengths are the `ρ`-distances `M.S.dist x y` of the source norm (not
Euclidean and not `ℓ∞`), the profile is `M.K` with the source exponent, the inverse temperature is
`M.betaCrit`, and the observables are the `p`-th moments of the anchored finite cluster volume.

This is a finite-volume statement: the edge set is a finite `E` with prescribed lattice endpoints.
It says nothing about the infinite-volume cut-off mass `M.cutMassAt`; see REPORT.md.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FiniteRusso.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.FiniteRusso.ModelDefs

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

open Finset MeasureTheory intervalIntegral
open PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.FiniteVolume.RussoHandoff

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SourceModel

variable (M : SourceModelData)

theorem len_eq {E : Type*} (src dst : E → Fin M.d → ℤ) (e : E) :
    len M src dst e = M.S.dist (src e) (dst e) := rfl

/-- Distinct lattice endpoints are at positive `ρ`-distance: the source norm is a genuine norm. -/
theorem len_pos {E : Type*} {src dst : E → Fin M.d → ℤ} (hne : ∀ e, src e ≠ dst e) (e : E) :
    0 < len M src dst e :=
  M.S.dist_pos (hne e)

theorem betaCrit_coe_nonneg : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg

/-! ### The interval increment at the source norm -/

/-- **Incremental Russo formula over one interval of radii, at the genuine normalized norm.**
For `r₁ ≤ r₂`, the change of the `p`-th finite-volume source cutoff cluster moment is the integral
over the affine path of edge probabilities of the pivotal flux; only edges of norm-length `< r₂`
contribute. -/
theorem moment_increment {E : Type*} [Fintype E] [DecidableEq E] {V : Type*} [Fintype V]
    [DecidableEq V] (src dst : E → Fin M.d → ℤ) (s t : E → V) (x : V) (p : ℕ)
    {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    moment M src dst s t x p r₂ - moment M src dst s t x p r₁
      = ∫ θ in (0 : ℝ)..1,
          ∑ e ∈ univ.filter (fun e => len M src dst e < r₂),
            (param M src dst r₂ e - param M src dst r₁ e)
              * pivotalMass (pathParam (param M src dst r₁) (param M src dst r₂) θ) e
                  (clusterMoment s t x p) := by
  unfold moment param
  exact cutoffMoment_increment_filter r₁ r₂ h

/-- The finite-volume source cutoff moment is nondecreasing in the cut-off radius. -/
theorem moment_mono {E : Type*} [Fintype E] [DecidableEq E] {V : Type*} [Fintype V]
    [DecidableEq V] {src dst : E → Fin M.d → ℤ} (hne : ∀ e, src e ≠ dst e)
    (s t : E → V) (x : V) (p : ℕ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h : r₁ ≤ r₂) :
    moment M src dst s t x p r₁ ≤ moment M src dst s t x p r₂ := by
  unfold moment
  exact cutoffMoment_mono_r (betaCrit_coe_nonneg M) M.K_antitone
    (fun e => len_pos M hne e) hr₁ h

/-- **Flux majorant at the source norm.**  The increment is bounded by the interval integral of the
pivotal flux weighted by `β_c (J_{r₂} − J_{r₁})(‖e‖_ρ)`, the integrated form of the source's
`β|J'(r)|` weight. -/
theorem moment_increment_le {E : Type*} [Fintype E] [DecidableEq E] {V : Type*} [Fintype V]
    [DecidableEq V] {src dst : E → Fin M.d → ℤ} (hne : ∀ e, src e ≠ dst e)
    (s t : E → V) (x : V) (p : ℕ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h : r₁ ≤ r₂) :
    moment M src dst s t x p r₂ - moment M src dst s t x p r₁
      ≤ ∫ θ in (0 : ℝ)..1,
          ∑ e, ((M.betaCrit : ℝ)
              * (cutoffProfile M.K r₂ (len M src dst e)
                  - cutoffProfile M.K r₁ (len M src dst e)))
            * pivotalMass (pathParam (param M src dst r₁) (param M src dst r₂) θ) e
                (clusterMoment s t x p) := by
  unfold moment param
  exact cutoffMoment_increment_le (betaCrit_coe_nonneg M) M.K_antitone
    (fun e => len_pos M hne e) hr₁ h

/-- **Boundary convention at the source norm.**  Edges whose `ρ`-length is at least the upper
endpoint `r₂` have zero weight in the interval; equivalently, the cut-off law has not yet switched
them on at either endpoint. -/
theorem param_eq_zero_of_le (src dst : E → Fin M.d → ℤ) {r : ℝ} {e : E}
    (h : r ≤ len M src dst e) : param M src dst r e = 0 :=
  cutoffParam_eq_zero_of_le e h

end SourceModel

end PercLib.CriticalLRP.FiniteVolume.RussoHandoff
