/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
/-
The conditional `β_c` chain for the explicit source-model witness.

This module composes two already separated inputs and nothing else:

* the nearest-neighbour comparison packet
  `Orchestration/ModelWitness/NNComparison/BetaCritPos.lean`, which proves
  `0 < β_c` for the source-model witness from the named external proposition
  `NNComparison.NNSupercritical d` (`d ≥ 2`);
* `Analysis/Cutoff/OffCorner/LargeRadiusMoments.lean`, which proves the paper's
  off-corner derivative at the witness from `0 < β_c` and pointwise finiteness
  of the uncut first moment at every strictly subcritical parameter.

The nearest-neighbour input and the subcritical first-moment input remain
visible in the statements below.  Neither is proved here, and the theorem does
not assert either one.

The source is T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Definition I.1.3 (the normalized source kernel)
and the sharpness input used in the proof of Lemma I.4.9.
-/
module

public import PercLib.CriticalLRP.Orchestration.ModelWitness.NNComparison.BetaCritPos
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.LargeRadiusMoments

/-!
# The conditional critical-parameter chain at the source witness

For the literal witness `sourceModelWitness d hd α hα`, the two external inputs are

* `NNComparison.NNSupercritical d`, the supercritical half of nearest-neighbour bond
  percolation on `ℤ^d` (`d ≥ 2`), and
* `hsub`, finiteness of the uncut first cluster moment at every `β < β_c`.

The first gives `0 < β_c` through the exact kernel rescaling and the high-temperature
criterion.  The second, together with `0 < β_c`, gives finiteness of the first cutoff
moment at a strictly larger radius, which is the remaining moment input of the landed
off-corner derivative theorem.  The resulting derivative is stated with both inputs still
in its hypotheses; this is a conditional wrapper, not a proof of the paper's main theorem.

The `d ≥ 2` normalisation lemma records that the setter used by the chain is the actual
source witness: its kernel is exactly `2^{-d-α}/(d+α)` times the paper-literal
`lrKernel d α`, and the rescaling constant is positive.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP Orchestration
open NNComparison

/-- **Normalisation-faithful `d ≥ 2` setter.**  The `d ≥ 2` witness used below is the
literal source witness with the paper's two normalisations: the normalized sup norm
`2‖·‖∞` and the source-normalized derivative `|K' r| = r^{-d-α-1}`.  Its kernel is exactly
`rescaleConstant d α • lrKernel d α`, with the positive constant
`rescaleConstant d α = 2^{-d-α}/(d+α)`. -/
theorem sourceModelWitness_two_kernel_eq (d : ℕ) (hd2 : 2 ≤ d) (α : ℝ) (hα : 0 < α) :
    (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).kernel =
      fun e => rescaleConstant d α * lrKernel d α e :=
  sourceModelWitness_kernel_eq (le_trans (by norm_num) hd2) α hα

/-- The rescaling constant of the `d ≥ 2` setter is strictly positive. -/
theorem sourceModelWitness_two_rescaleConstant_pos (d : ℕ) (_hd2 : 2 ≤ d) (α : ℝ)
    (hα : 0 < α) :
    0 < rescaleConstant d α :=
  rescaleConstant_pos hα

/-- **The conditional `β_c` chain with both remaining inputs visible.**  For `d ≥ 2`,
nearest-neighbour supercriticality gives `0 < β_c` for the literal source witness; with
pointwise subcritical first-moment finiteness this gives the paper's off-corner derivative
at every off-corner radius `r0 > 0`.

`hNN` is the named external nearest-neighbour supercriticality proposition and `hsub` is
the subcritical first-moment hypothesis.  Neither is discharged here. -/
theorem sourceModelWitness_betaCrit_pos_and_hasDerivAt_powerLaw_of_NNSupercritical
    (d : ℕ) (hd2 : 2 ≤ d) (α : ℝ) (hα : 0 < α)
    (hNN : NNSupercritical d)
    (hsub : ∀ β : ℝ≥0, β < (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).betaCrit →
      (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).V)
        ∂((sourceModelWitness d (le_trans (by norm_num) hd2) α hα).law β)) ≠ ⊤)
    {r0 : ℝ} (hr0 : 0 < r0)
    (hoff : r0 ∉ (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).cornerRadii) :
    0 < (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).betaCrit ∧
      HasDerivAt (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).cutMassReal
        (((sourceModelWitness d (le_trans (by norm_num) hd2) α hα).betaCrit : ℝ) *
          r0 ^ (-(d : ℝ) - α - 1) *
          (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).exclScalar r0) r0 := by
  have hβ : 0 < (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).betaCrit :=
    sourceModelWitness_betaCrit_pos_of_NNSupercritical d hd2 α hα hNN
  refine ⟨hβ, ?_⟩
  exact sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_subcritical d
    (le_trans (by norm_num) hd2) α hα hβ hsub hr0 hoff

/-- The derivative half of the conditional chain, with both external inputs explicit. -/
theorem sourceModelWitness_hasDerivAt_powerLaw_of_NNSupercritical
    (d : ℕ) (hd2 : 2 ≤ d) (α : ℝ) (hα : 0 < α)
    (hNN : NNSupercritical d)
    (hsub : ∀ β : ℝ≥0, β < (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).betaCrit →
      (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).V)
        ∂((sourceModelWitness d (le_trans (by norm_num) hd2) α hα).law β)) ≠ ⊤)
    {r0 : ℝ} (hr0 : 0 < r0)
    (hoff : r0 ∉ (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).cornerRadii) :
    HasDerivAt (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).cutMassReal
      (((sourceModelWitness d (le_trans (by norm_num) hd2) α hα).betaCrit : ℝ) *
        r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).exclScalar r0) r0 :=
  (sourceModelWitness_betaCrit_pos_and_hasDerivAt_powerLaw_of_NNSupercritical d hd2 α hα
    hNN hsub hr0 hoff).2

end PercLib.CriticalLRP.Orchestration.Witness
