/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvi25ua`, member `m1`, direction (A).

# The uniform-in-radius majorant at the source power-law witness

The two halves of the majorant of `WindowMajorant/Main.lean` are stated for an abstract
`SourceModelData` with the coefficient bound `|coeffRHS t| ≤ C` and finiteness of the fourth cutoff
moment as hypotheses.  At the explicit power-law witness `sourceModelWitness d hd α hα` both are
available with *no* extra input:

* the coefficient bound on `[1/2, ∞)` (hence on `[1/2, 1]`) is the explicit power-law bound
  `abs_coeffRHS_sourceModelWitness_le` with the source constant
  `C = powLawCoeffBound β_c d α (1/2) = |β_c| (1/2)^{-d-α-1}`;
* the fourth cutoff moment at every radius below `2` is `1` (`cutMoment_sourceModelWitness_eq_one`,
  `cutMoment_four_sourceModelWitness`), the cut kernel vanishing below radius `2`.

Consequently, on the fixed off-corner window `[1/2, 1]` and along the canonical box family
`boxEdges d n`, the window fluxes are dominated by the single radius function
`M.windowMajorant C 1` with no remaining mathematical input, and that radius function is interval
integrable as soon as `M.rhsScalarTwo` is measurable in the radius.  The theorem
`hfluxMaj_boxEdges` is exactly the `hfluxMaj` input of the witness-level assembly, with
`G = M.windowMajorant C 1`.

The measurability of `M.rhsScalarTwo` is kept explicit; at the witness it follows from the
fixed-radius window-flux convergence at every positive radius (`hfluxConv_of_cutMoment_four`) by the
`liminf` argument, which is the business of the assembly direction, not of the majorant.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.WindowMajorant.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.Main

/-!
# The majorant on the window `[1/2, 1]` of the power-law witness
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Orchestration

namespace Witness

open PercLib.CriticalLRP.Orchestration

/-- The constant is nonnegative. -/
theorem witnessCoeffConst_nonneg (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    0 ≤ witnessCoeffConst d hd α hα :=
  powLawCoeffBound_nonneg (d := d) (α := α) (β := _) (by norm_num)

/-- The coefficient bound of the witness on `[1/2, 1]`, from the exact power-law bound on the
halfline `[1/2, ∞)`. -/
theorem abs_coeffRHS_sourceModelWitness_le_witnessCoeffConst (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : r ∈ Set.Icc (1 / 2) 1) :
    |(sourceModelWitness d hd α hα).coeffRHS r| ≤ witnessCoeffConst d hd α hα :=
  abs_coeffRHS_sourceModelWitness_le d hd α hα (a := 1 / 2) (by norm_num) hr.1

/-- The fourth cutoff moment of the witness at radius `1` is finite: at every radius below `2` it is
`1`. -/
theorem cutMoment_four_one_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    (sourceModelWitness d hd α hα).cutMoment 4 1 ≠ ⊤ :=
  cutMoment_four_sourceModelWitness d hd α hα (by norm_num)

/-- **The uniform-in-window majorant at the witness, on `Ioc (1/2) 1`.**

For every box window `boxEdges d n` and every radius `t ∈ (1/2, 1]`, the window flux is at most
`M.windowMajorant C 1 t = 2 * (M.rhsScalarTwo t + 3 C (M.cutMoment 4 1).toReal)`, with the explicit
constant `C = witnessCoeffConst d hd α hα`.  No window monotonicity and no flux monotonicity is
used, and no hypothesis remains: the coefficient bound is the power law, and the fourth cutoff
moment at `1` is `1`. -/
theorem hfluxMaj_boxEdges (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    ∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioc (1 / 2) 1 →
      (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t
        ≤ (sourceModelWitness d hd α hα).windowMajorant (witnessCoeffConst d hd α hα) 1 t :=
  (sourceModelWitness d hd α hα).windowFlux_le_windowMajorant_of_cutMoment_four_le
    (a := 1 / 2) (b := 1) (C := witnessCoeffConst d hd α hα) (by norm_num) (by norm_num)
    (cutMoment_four_one_sourceModelWitness d hd α hα)
    (witnessCoeffConst_nonneg d hd α hα)
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le_witnessCoeffConst d hd α hα hr)
    (boxEdges d)

/-- **Interval integrability of the witness majorant on `[1/2, 1]`**, from measurability of
`M.rhsScalarTwo` in the radius. -/
theorem intervalIntegrable_windowMajorant_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α)
    (hmeas : Measurable fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t) :
    IntervalIntegrable
      ((sourceModelWitness d hd α hα).windowMajorant (witnessCoeffConst d hd α hα) 1)
      volume (1 / 2) 1 :=
  (sourceModelWitness d hd α hα).intervalIntegrable_windowMajorant (by norm_num) hmeas
    (witnessCoeffConst_nonneg d hd α hα)
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le_witnessCoeffConst d hd α hα hr)
    (cutMoment_four_one_sourceModelWitness d hd α hα)

/-- **The packaged majorant at the witness**: domination plus interval integrability, on the
off-corner window `[1/2, 1]` and along the canonical box family. -/
theorem isWindowFluxMajorant_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (hmeas : Measurable fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t) :
    (sourceModelWitness d hd α hα).IsWindowFluxMajorant (1 / 2) 1
      (witnessCoeffConst d hd α hα) (boxEdges d) :=
  ⟨hfluxMaj_boxEdges d hd α hα,
    intervalIntegrable_windowMajorant_sourceModelWitness d hd α hα hmeas⟩

end Witness

end Orchestration

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.Witness

#print axioms witnessCoeffConst
#print axioms witnessCoeffConst_nonneg
#print axioms abs_coeffRHS_sourceModelWitness_le_witnessCoeffConst
#print axioms cutMoment_four_one_sourceModelWitness
#print axioms hfluxMaj_boxEdges
#print axioms intervalIntegrable_windowMajorant_sourceModelWitness
#print axioms isWindowFluxMajorant_sourceModelWitness

end PercLib.CriticalLRP.Orchestration.Witness
