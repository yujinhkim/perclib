/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.Temperature

/-!
# Uncut susceptibility objects and reduced coefficients for the source model

This file introduces the objects that the missing source input `hsub` of the staged
`SecondMoment/SourceWitness/Sharpness.lean` is about.  Nothing here is a theorem: the
file only names

* `SourceModelData.uncutMean β = E_β |K_0|`, the uncut (susceptibility) first moment of
  the cluster of the origin under the *unt truncated* source law at intensity `β`;
* `SourceModelData.finiteMeanIntensities`, the set of intensities at which that first
  moment is finite;
* `SourceModelData.SubcriticalFiniteMean`, the literal `hsub` hypothesis
  (`∀ β, β < β_c → E_β |K_0| ≠ ⊤`) as a single named proposition, so that statements
  consuming it cannot silently change its content;
* `SourceModelData.cutCoeff t0 r = min 1 (1 - min (1/2) (K r / (2 K t₀)))` and its
  `ℝ≥0` form `SourceModelData.cutCoeffNN t0 r`: the strict coefficient of Definition
  I.1.5 for the cut-off at radius `r`, with the outer `min 1` making it a valid `ℝ≥0`
  coefficient at *every* radius (the inner expression is only shown to be in `(0,1)` at
  the radii where it is used, and `min` is the identity there).

`cutMassAtBeta` (the cutoff first moment at an arbitrary intensity) already exists in
`MomentMonotonicity/Temperature/Defs.lean`; `uncutMean` is its uncut counterpart and
`cutMassAtBeta β r 0 ≤ uncutMean β` for `0 ≤ r` is `SourceModelData.cutMassAtBeta_le_law`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Measure Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP FiniteVolume

namespace SourceModelData

variable (M : SourceModelData)

/-- `χ_β = E_β |K_0|`: the expected cluster volume of the origin under the uncut source
law `M.law β`.  This is the quantity whose finiteness at every subcritical intensity is
the source's sharpness input `hsub`. -/
def uncutMean (β : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)

/-- The set of intensities at which the uncut first moment is finite.  It is a down-set
(`SourceModelData.uncutMean_mono`).  The complementary upper bound ("a finite mean forces
`β ≤ β_c`") is `criticalBeta`'s defining property through
`le_criticalBeta_of_forall_lintegral_ne_top`, which asks for the mean at *every* root; the
root independence that would transfer the root-`0` statement is not formalized here, so no
containment in `[0, β_c]` is claimed. -/
def finiteMeanIntensities : Set ℝ≥0 := {β | M.uncutMean β ≠ ⊤}

/-- The source's sharpness input for the uncut first moment, as one proposition: the
expected cluster volume of the origin is finite at every *strictly* subcritical
intensity.  This is `hsub` of the staged `SourceWitness/Sharpness.lean`; it says nothing
at `β_c` itself and is not implied by vanishing percolation probability. -/
def SubcriticalFiniteMean : Prop := ∀ β : ℝ≥0, β < M.betaCrit → M.uncutMean β ≠ ⊤

/-- The strict coefficient of Definition I.1.5 at cutoff radius `r`, with a harmless
outer `min 1`: at every `r > 0` it equals `1 - min (1/2) (K r / (2 K t₀))`, which is the
coefficient produced by `SourceModelData.cutKernel_le_scaled`. -/
def cutCoeff (t0 r : ℝ) : ℝ := min 1 (1 - min (1 / 2) (M.K r / (2 * M.K t0)))

/-- The `ℝ≥0` coefficient used to state the reduced intensity `β * c_r`. -/
def cutCoeffNN (t0 r : ℝ) : ℝ≥0 := Real.toNNReal (M.cutCoeff t0 r)

end SourceModelData

end PercLib.CriticalLRP.Orchestration
