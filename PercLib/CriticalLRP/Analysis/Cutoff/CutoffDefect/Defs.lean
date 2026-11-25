/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Campaign `smwttizjk`, member `m5`, direction D7B.

# The cutoff-law defect `𝓔_{1,r}` of Lemma I.4.11 as a named real-valued function

`TriangleAverage.defect` (HEAD) is the defect at the *uncut* critical law
`M.law M.betaCrit`.  The paper's Lemma I.4.11 is, however, a statement about the
range-truncated law `T_{β_c,r}` (Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, §I.4.1–I.4.2), i.e. about `M.cutLaw r`.  Its three statistics are
`E|K|`, `E[|K| Σ_{y∈B_r} |K_y|]` and `E[|K ∩ B_r| |K|²]` under `M.cutLaw r`, which HEAD
provides as `M.cutMassAt r 0`, `E1Sign.pairMass M r` and `E1Sign.connMass M r`.

This file only *names* the resulting real quotient, so that the limit theorems of
`CutoffDefectLimit.lean` read as statements about a single function of `r`.  No
mathematical content is added here.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Defect.Triangle

/-! # The defect at the actual range-truncated critical law -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.CutoffDefect

open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- **The source defect `𝓔_{1,r}` at the actual range-truncated critical law.**

`𝓔_{1,r} = (|B_r| χ_r² - S_r + T_r) / (|B_r| χ_r²)` with `χ_r = E_{β_c,r}|K_0|`,
`S_r = E_{β_c,r}[|K_0| Σ_{y ∈ B_r} |K_y|]` and `T_r = E_{β_c,r}[|K_0 ∩ B_r| |K_0|²]`
(paper, (I.4.7)).  This is `VolumeMoments.cE1` applied to the cutoff statistics, i.e.
the `cE1` of `E1Sign.cE1_mem_Icc_windowOpenTriangle`; it is *not*
`TriangleAverage.defect`, which uses the uncut law. -/
noncomputable def cutE1 (r : ℝ) : ℝ :=
  PercLib.CriticalLRP.VolumeMoments.cE1 (M.cutMassAt r 0).toReal
    (PercLib.CriticalLRP.E1Sign.pairMass M r).toReal
    (PercLib.CriticalLRP.E1Sign.connMass M r).toReal ((M.ball r).ncard : ℝ)

/-- Unfolding lemma for `cutE1`. -/
theorem cutE1_eq (r : ℝ) :
    cutE1 M r =
      PercLib.CriticalLRP.VolumeMoments.cE1 (M.cutMassAt r 0).toReal
        (PercLib.CriticalLRP.E1Sign.pairMass M r).toReal
        (PercLib.CriticalLRP.E1Sign.connMass M r).toReal ((M.ball r).ncard : ℝ) :=
  rfl

end PercLib.CriticalLRP.CutoffDefect
