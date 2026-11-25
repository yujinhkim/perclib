/-
# Conditional model interface for the weakened majorant hypotheses (D3)

This file records what the analysis of `LocalIntegrableAC.lean` gives **at the model's own
objects** (`M.cutMassReal`, `M.cornerRadii` of `Analysis/Cutoff/IntervalAC/Defs.lean`), by
instantiating the general theorems at `M.cutMassReal`.

**Every model premise remains a hypothesis here.** Nothing in this file proves, or claims, that
`M.cutMassReal` is continuous in the radius, that `M.cornerRadii ∩ Ioo a b` is finite, or that any
derivative bound for `M.cutMassReal` holds. The only content is that the *majorant's* regularity in
the landed `Analysis/Cutoff/IntervalAC.lean` can be weakened from `ContinuousOn g (Icc a b)` to
`ContinuousOn g (Ioo a b)` + `IntervalIntegrable g volume a b`, and — after absolute continuity of
`M.cutMassReal` has been obtained from the pointwise data — removed altogether in favour of an
almost-everywhere bound against an arbitrary interval-integrable majorant.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.LocalAC.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.LocalAC
public import PercLib.CriticalLRP.Analysis.Cutoff.IntervalAC

@[expose] public section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Incremental bound for the cut mass with an endpoint-singular majorant.**

Same conclusion as the landed `SourceModelData.cutMassReal_abs_sub_le_integral`, with the
hypothesis `ContinuousOn g (Icc a b)` replaced by `IntervalIntegrable g volume a b` together with
`ContinuousOn g (Ioo a b)`: the majorant may be singular at the two endpoints of the window and
its values there are irrelevant. Every model premise (`hcont`, `h Dfin`, the off-corner derivative
bound) stays an explicit hypothesis. -/
theorem cutMassReal_abs_sub_le_integral_of_continuousOn_interior {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn M.cutMassReal (Icc a b)) {g : ℝ → ℝ}
    (hgi : IntervalIntegrable g volume a b) (hgc : ContinuousOn g (Ioo a b))
    (hDfin : (M.cornerRadii ∩ Ioo a b).Finite)
    (hgood : ∀ u ∈ Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      |M.cutMassReal y - M.cutMassReal x| ≤ ∫ t in x..y, g t := by
  refine PercLib.CriticalLRP.LocalAC.abs_sub_le_integral_of_finite_exception_majorant
    hab hcont hgi hDfin.toFinset ?_
  intro u hu huD
  have hoff : u ∉ M.cornerRadii := by
    intro hmem
    exact huD (by rw [hDfin.coe_toFinset]; exact ⟨hmem, hu⟩)
  obtain ⟨hd, hb⟩ := hgood u hu hoff
  exact ⟨hd, hb, hgc.continuousAt (isOpen_Ioo.mem_nhds hu)⟩

/-- **Absolute continuity of the cut mass with an endpoint-singular majorant**, from the weakened
hypotheses of `cutMassReal_abs_sub_le_integral_of_continuousOn_interior`. -/
theorem cutMassReal_absolutelyContinuousOn_of_continuousOn_interior {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn M.cutMassReal (Icc a b)) {g : ℝ → ℝ}
    (hgi : IntervalIntegrable g volume a b) (hgc : ContinuousOn g (Ioo a b))
    (hDfin : (M.cornerRadii ∩ Ioo a b).Finite)
    (hgood : ∀ u ∈ Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤ g u) :
    AbsolutelyContinuousOnInterval M.cutMassReal a b :=
  PercLib.CriticalLRP.LocalAC.absolutelyContinuousOnInterval_of_interval_bound hab hgi
    (M.cutMassReal_abs_sub_le_integral_of_continuousOn_interior hab hcont hgi hgc hDfin hgood)

/-- **Fundamental theorem of calculus for the cut mass** with an endpoint-singular majorant. -/
theorem cutMassReal_intervalIntegral_deriv_of_continuousOn_interior {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn M.cutMassReal (Icc a b)) {g : ℝ → ℝ}
    (hgi : IntervalIntegrable g volume a b) (hgc : ContinuousOn g (Ioo a b))
    (hDfin : (M.cornerRadii ∩ Ioo a b).Finite)
    (hgood : ∀ u ∈ Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤ g u) :
    ∫ t in a..b, deriv M.cutMassReal t = M.cutMassReal b - M.cutMassReal a :=
  AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    (M.cutMassReal_absolutelyContinuousOn_of_continuousOn_interior hab hcont hgi hgc hDfin hgood)

/-- **The cut mass with a wild, merely interval-integrable majorant.**

Absolute continuity of the cut mass is obtained from the pointwise off-corner data against the
locally continuous majorant `g₀` (as in the landed Russo interface), and the *quantitative*
incremental bound is then taken against an arbitrary interval-integrable majorant `g` satisfying
only the almost-everywhere bound `|χ'| ≤ g`.  No regularity of the log-error factor enters the
final estimate; all model premises stay explicit hypotheses. -/
theorem cutMassReal_abs_sub_le_integral_of_ae_majorant {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn M.cutMassReal (Icc a b)) {g₀ : ℝ → ℝ}
    (hg₀i : IntervalIntegrable g₀ volume a b) (hg₀c : ContinuousOn g₀ (Ioo a b))
    (hDfin : (M.cornerRadii ∩ Ioo a b).Finite)
    (hgood : ∀ u ∈ Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤ g₀ u)
    {g : ℝ → ℝ} (hgi : IntervalIntegrable g volume a b)
    (hmaj : ∀ᵐ u ∂volume, u ∈ Ioo a b → |deriv M.cutMassReal u| ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      |M.cutMassReal y - M.cutMassReal x| ≤ ∫ t in x..y, g t :=
  PercLib.CriticalLRP.LocalAC.abs_sub_le_integral_of_absolutelyContinuous_of_ae_abs_deriv_le hab
    (M.cutMassReal_absolutelyContinuousOn_of_continuousOn_interior hab hcont hg₀i hg₀c hDfin hgood)
    hgi hmaj

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_abs_sub_le_integral_of_continuousOn_interior
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_absolutelyContinuousOn_of_continuousOn_interior
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_intervalIntegral_deriv_of_continuousOn_interior
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_abs_sub_le_integral_of_ae_majorant
