module
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusEnvelope

/-!
# Interval-integrability of the total pivotal weight from an interior-scale envelope
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)
attribute [local instance] Classical.propDecidable

/-- The weighted touching probability is bounded by the interior-scale envelope. -/
lemma weightedTouch_le_env {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) {r : ℝ} (hr : r ∈ Set.Icc a' b') (e : Sym2 M.V) :
    |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)}) ≤
      (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
        (|M.cutEdgeDeriv ρ e| *
          (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)})) := by
  have hb'0 : 0 < b' := lt_of_lt_of_le ha' ha'b'
  have hscale := M.m1_abs_cutEdgeDeriv_le_scale ha' ha'b' hb'ρ hCb hC0 hKρ hr e
  have hmon := M.m1_real_touchSet_mono_radius (lt_of_lt_of_le ha' hr.1) hb'0 hr.2 e
  have hKρ0 : 0 ≤ -(deriv M.K ρ) := neg_nonneg.mpr (le_of_lt hKρ)
  have hscale0 : 0 ≤
      (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
        |M.cutEdgeDeriv ρ e| :=
    mul_nonneg (mul_nonneg (div_nonneg hC0 hKρ0) (Real.exp_nonneg _)) (abs_nonneg _)
  refine (mul_le_mul hscale (mul_le_mul_of_nonneg_left hmon (by norm_num))
    (by positivity) hscale0).trans_eq (by ring)

/-- The weighted touching probability is measurable in the radius. -/
lemma measurable_weightedTouch (e : Sym2 M.V) :
    Measurable fun r => |M.cutEdgeDeriv r e| *
      (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)}) := by
  apply (M.measurable_cutEdgeDeriv e).abs.mul
  exact measurable_const.mul
    (M.measurable_real_edgeMeasure (measurableSet_touchSet_mem e)
      (isIncreasing_touchSet_mem (o := (0 : M.V)) e))

/-- Compact-window total pivotal weight is bounded-integrable from the same interior-scale data
used for the flux envelope. No continuity hypothesis is imposed. -/
lemma intervalIntegrable_pivotalWeight_of_envelope {a' b' ρ C : ℝ}
    (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤) (y : M.V) :
    IntervalIntegrable (fun r => sMomentWeight (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a' b' := by
  have henv := M.m1_summable_env ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol
  have hmeas : Measurable fun r => ∑' e : Sym2 M.V,
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)}) :=
    Measurable.tsum fun e => M.measurable_weightedTouch e
  have hbound : ∀ r ∈ Set.Icc a' b',
      (∑' e : Sym2 M.V, |M.cutEdgeDeriv r e| *
        (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)})) ≤
        ∑' e : Sym2 M.V,
          (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
            (|M.cutEdgeDeriv ρ e| *
              (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)})) := by
    intro r hr
    have hsum : Summable fun e =>
        |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)}) :=
      Summable.of_nonneg_of_le (fun e => by positivity)
        (fun e => M.weightedTouch_le_env ha' ha'b' hb'ρ hCb hC0 hKρ hr e) henv
    exact hsum.tsum_le_tsum
      (fun e => M.weightedTouch_le_env ha' ha'b' hb'ρ hCb hC0 hKρ hr e) henv
  simp only [sMomentWeight, pivotalWeightOf, Finset.sum_singleton, abs_one,
    max_eq_left (show (0 : ℝ) ≤ 1 by norm_num), mul_one]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha'b']
  refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ ?_ ?_
  · exact hmeas.aestronglyMeasurable
  · exact ∑' e : Sym2 M.V,
      (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
        (|M.cutEdgeDeriv ρ e| *
          (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)}))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun e => by positivity)]
    exact hbound r hr

/-- The endpoint off-corner derivative with the total pivotal-weight dominator supplied on every
compact subinterval by the interior-scale envelope at `β`. The derivative comparison sign at
`β` is an input, not inferred from moment finiteness. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 C : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hC0 : 0 ≤ C) (hCb : ∀ r ∈ Set.Ioo α β, -(deriv M.K r) ≤ C)
    (hKβ : deriv M.K β < 0)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hGcont : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 := by
  apply M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability
    T hTmono hT S hSmono hS hα0 hαr0 hr0β hoff hKd h2β ?_ hcontinf hGcont
  intro y a ha b hb
  have hβ0 : 0 < β := hα0.trans (hb.1.trans hb.2)
  have h1β : M.cutMoment 1 β ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2β
  have hstep : ∀ {a b : ℝ}, a ∈ Set.Ioo α β → b ∈ Set.Ioo α β → a ≤ b →
      IntervalIntegrable (fun r => sMomentWeight (0 : M.V) ({y} : Finset M.V)
        (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a b := by
    intro a b ha hb hab
    apply M.intervalIntegrable_pivotalWeight_of_envelope
      (hα0.trans ha.1) hab hb.2.le
      (fun r hr => hCb r ⟨ha.1.trans_le hr.1, hr.2.trans_lt hb.2⟩)
      hC0 hKβ hβ0 h1β y
  rcases le_total a b with hab | hba
  · exact hstep ha hb hab
  · exact (hstep hb ha hba).symm

end PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms weightedTouch_le_env
#print axioms measurable_weightedTouch
#print axioms intervalIntegrable_pivotalWeight_of_envelope
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope
