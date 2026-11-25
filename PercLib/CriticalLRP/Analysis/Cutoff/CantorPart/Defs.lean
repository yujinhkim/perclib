/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Stieltjes measure of the finite-moment cutoff increment

Radius clamping and the actual Stieltjes/Cantor part of cut-mass variation.
These objects are defined before interpreting the defect of a flux identity;
they do not assert that the singular part vanishes or that absolute continuity
is proved.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity

namespace PercLib.CriticalLRP.Orchestration

@[expose] public section

namespace SourceModelData

open MeasureTheory Set Filter
open scoped ENNReal

variable (M : SourceModelData)

/-- The cut mass with the radius clamped into `[a,b]`.  It is monotone and continuous on all of `ℝ`
and agrees with `M.cutMassReal` on `[a,b]`. -/
noncomputable def clampedCutMass (a b : ℝ) : ℝ → ℝ := fun r => M.cutMassReal (max a (min r b))

theorem clampedCutMass_monotone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ} (hbb' : b < b')
    (hfin : M.cutMassAt b' 0 ≠ ⊤) : Monotone (M.clampedCutMass a b) := by
  have hmonoOn : MonotoneOn M.cutMassReal (Icc a b) := M.cutMassReal_mono ha hab
    (ne_top_of_le_ne_top hfin (M.cutMassAt_mono (lt_of_lt_of_le ha hab)
      (lt_trans (lt_of_lt_of_le ha hab) hbb') hbb'.le))
  have hclamp : Monotone fun r : ℝ => max a (min r b) :=
    monotone_const.max (monotone_id.min monotone_const)
  have hmaps : MapsTo (fun r : ℝ => max a (min r b)) univ (Icc a b) := by
    intro r _
    exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have h := hmonoOn.comp (f := fun r : ℝ => max a (min r b)) (s := univ)
    (hclamp.monotoneOn univ) hmaps
  exact monotoneOn_univ.mp h

theorem clampedCutMass_continuous {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ} (hbb' : b < b')
    (hfin : M.cutMassAt b' 0 ≠ ⊤) : Continuous (M.clampedCutMass a b) := by
  have hcont : ContinuousOn M.cutMassReal (Icc a b) := M.continuousOn_cutMassReal ha hbb' hfin
  have hclamp : Continuous fun r : ℝ => max a (min r b) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hmaps : ∀ r : ℝ, max a (min r b) ∈ Icc a b := fun r =>
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have h := hcont.comp_continuous hclamp hmaps
  exact h

theorem clampedCutMass_eq {a b : ℝ} {r : ℝ} (hr : r ∈ Icc a b) :
    M.clampedCutMass a b r = M.cutMassReal r := by
  simp [clampedCutMass, max_eq_right hr.1, min_eq_left hr.2]

/-- The clamped cut mass and the cut mass have the same derivative in the open window. -/
theorem deriv_clampedCutMass {a b : ℝ} {r : ℝ} (hr : r ∈ Ioo a b) :
    deriv (M.clampedCutMass a b) r = deriv M.cutMassReal r := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hr] with y hy
  exact M.clampedCutMass_eq ⟨hy.1.le, hy.2.le⟩


/-- The Stieltjes function of the clamped cut mass. -/
noncomputable def cutMassStieltjes {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ} (hbb' : b < b')
    (hfin : M.cutMassAt b' 0 ≠ ⊤) : StieltjesFunction ℝ :=
  ⟨M.clampedCutMass a b, M.clampedCutMass_monotone ha hab hbb' hfin,
    fun x => (M.clampedCutMass_continuous ha hab hbb' hfin).continuousAt.continuousWithinAt
      (s := Ici x)⟩

/-- The Stieltjes measure of the cut mass on the clamped window. -/
noncomputable def cutMassStieltjesMeasure {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ}
    (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) : Measure ℝ :=
  (M.cutMassStieltjes ha hab hbb' hfin).measure

/-- The **Cantor (singular) part** of the cut-mass Stieltjes measure with respect to Lebesgue
measure.  This is the exact defect in the mass-transport identity for `χ`. -/
noncomputable def cutMassCantorPart {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ}
    (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) : Measure ℝ :=
  (M.cutMassStieltjesMeasure ha hab hbb' hfin).singularPart volume
end SourceModelData

end

end PercLib.CriticalLRP.Orchestration
