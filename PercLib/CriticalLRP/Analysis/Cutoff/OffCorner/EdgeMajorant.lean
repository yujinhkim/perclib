module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairFluxSummable
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SecondMomentFlux
public import PercLib.CriticalLRP.RussoInf.Sharpness

/-!
# Unstandardized off-corner incident edge majorant

At a fixed positive radius, a finite first cutoff moment gives a summable pivotal-mass majorant
using the unstandardized cutoff derivative and the finite incident-support count. This avoids
`gapFloor` and any radius-uniformity assertion.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

/-- The absolute cutoff derivative is at most `β_c (-K')` at a positive radius. -/
theorem abs_cutEdgeDeriv_le {r : ℝ} (hr : 0 < r) (e : Sym2 M.V) :
    |M.cutEdgeDeriv r e| ≤ (M.betaCrit : ℝ) * (-(deriv M.K r)) := by
  classical
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutEdgeDeriv_mk, ite_eq_left rfl, abs_zero]
      exact mul_nonneg M.betaCrit.coe_nonneg (M.neg_deriv_K_nonneg hr)
    · by_cases hdist : M.S.dist x y ≤ r
      · rw [M.cutEdgeDeriv_mk_of_le hxy hdist]
        have hβ : 0 ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
        have hneg : 0 ≤ -(deriv M.K r) := M.neg_deriv_K_nonneg hr
        have harg : -((M.betaCrit : ℝ) * M.cutKernel r s(x, y)) ≤ 0 :=
          neg_nonpos.mpr (mul_nonneg hβ (M.cutKernel_nonneg r _))
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg hβ hneg) (Real.exp_nonneg _))]
        calc (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r s(x, y)))
            ≤ (M.betaCrit : ℝ) * (-(deriv M.K r)) * 1 :=
              mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr harg)
                (mul_nonneg hβ hneg)
          _ = (M.betaCrit : ℝ) * (-(deriv M.K r)) := mul_one _
      · rw [M.cutEdgeDeriv_eq_zero_of_lt_dist (not_le.mp hdist), abs_zero]
        exact mul_nonneg M.betaCrit.coe_nonneg (M.neg_deriv_K_nonneg hr)

/-- A generic finite incident degree gives an actual summable pivotal-mass majorant. -/
theorem summable_weight_touch_of_incident {o : M.V} {r : ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hdeg : ∀ x : M.V, ∀ u : Finset (Sym2 M.V),
      ∑ e ∈ u, |M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (hvol : ∫⁻ ω, clusterVol ω o ∂(M.cutLaw r) ≠ ⊤) :
    Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω o}) := by
  have hdd : 0 ≤ 2 * D := mul_nonneg (by norm_num) hD
  have hhdeg : ∀ x : M.V, ∀ u : Finset (Sym2 M.V),
      ∑ e ∈ u, |2 * M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0) ≤ 2 * D := by
    intro x u
    have hh := hdeg x u
    have heq : (∑ e ∈ u, |2 * M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0)) =
        2 * ∑ e ∈ u, |M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num), mul_assoc]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  refine summable_of_sum_le (c := (2 * D) * (∫⁻ ω, clusterVol ω o ∂(M.cutLaw r)).toReal)
    (fun e => by positivity) (fun u => ?_)
  have hdeg' : ∀ x : M.V, ∀ u : Finset (Sym2 M.V),
      ∑ e ∈ u, |2 * M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0) ≤ 2 * D := by
    intro x u
    calc ∑ e ∈ u, |2 * M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0)
        = ∑ e ∈ u, |2 * M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          split_ifs <;> simp_all
      _ ≤ 2 * D := hhdeg x u
  have h := PercLib.CriticalLRP.sum_abs_weight_touch_le (o := o) (M.cutLaw r)
    (fun e => 2 * M.cutEdgeDeriv r e) hdd hdeg' hvol u
  calc ∑ e ∈ u, |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω o})
      = ∑ e ∈ u, |2 * M.cutEdgeDeriv r e| * (M.cutLaw r).real {ω | e ∈ touchSet ω o} := by
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        ring
    _ ≤ (2 * D) * (∫⁻ ω, clusterVol ω o ∂(M.cutLaw r)).toReal := h

attribute [local instance] Classical.decEq

/-- The unstandardized incident degree is finite at every fixed positive radius, using the
normalized ball cardinality. -/
theorem weight_incident_le {r : ℝ} (hr : 0 < r) (x : M.V) (u : Finset (Sym2 M.V)) :
    ∑ e ∈ u, |M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0)
      ≤ ((M.betaCrit : ℝ) * (-(deriv M.K r))) * ((M.ball r).ncard : ℝ) := by
  have hnn : 0 ≤ (M.betaCrit : ℝ) * (-(deriv M.K r)) :=
    mul_nonneg M.betaCrit.coe_nonneg (M.neg_deriv_K_nonneg hr)
  have hterm : ∀ e ∈ u, |M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0) ≤
      ((M.betaCrit : ℝ) * (-(deriv M.K r))) * (if x ∈ e ∧ inSupport M r e then (1 : ℝ) else 0) := by
    intro e _
    by_cases hx : x ∈ e
    · by_cases hs : inSupport M r e
      · rw [ite_eq_left hx, ite_eq_left ⟨hx, hs⟩, mul_one, mul_one]
        exact M.abs_cutEdgeDeriv_le hr e
      · rw [M.cutEdgeDeriv_eq_zero_of_not_support hs, abs_zero, ite_eq_left hx, zero_mul]
        simp [hs]
    · rw [ite_eq_right hx, mul_zero]
      simp [hx]
  calc ∑ e ∈ u, |M.cutEdgeDeriv r e| * (if x ∈ e then (1 : ℝ) else 0)
      ≤ ∑ e ∈ u, ((M.betaCrit : ℝ) * (-(deriv M.K r))) *
          (if x ∈ e ∧ inSupport M r e then (1 : ℝ) else 0) := Finset.sum_le_sum hterm
    _ = ((M.betaCrit : ℝ) * (-(deriv M.K r))) *
          ∑ e ∈ u, (if x ∈ e ∧ inSupport M r e then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ = ((M.betaCrit : ℝ) * (-(deriv M.K r))) *
          ((u.filter (fun e => x ∈ e ∧ inSupport M r e)).card : ℝ) := by
        rw [Finset.card_filter]
        push_cast
        rfl
    _ ≤ ((M.betaCrit : ℝ) * (-(deriv M.K r))) * ((M.ball r).ncard : ℝ) :=
        mul_le_mul_of_nonneg_left (M.card_filter_incidentSupport_le r x u) hnn

/-- `hdom` from a finite first cutoff moment, without standardized `gapFloor` division. -/
theorem summable_hdom_of_cutMoment {r : ℝ} (hr : 0 < r) (hvol : M.cutMoment 1 r ≠ ⊤) :
    Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)}) := by
  rw [SourceModelData.cutMoment] at hvol
  refine M.summable_weight_touch_of_incident
    (D := ((M.betaCrit : ℝ) * (-(deriv M.K r))) * ((M.ball r).ncard : ℝ))
    (mul_nonneg (mul_nonneg M.betaCrit.coe_nonneg (M.neg_deriv_K_nonneg hr))
      (Nat.cast_nonneg _)) ?_ (by simpa only [pow_one] using hvol)
  intro x u
  convert M.weight_incident_le hr x u using 1
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> rfl

/-- **The conditional off-corner Russo derivative with all three summability inputs derived
from a finite second cutoff moment on the local window.** The remaining regularity, moment,
measurability and continuity inputs of `IntegralFluxInterchange` are unchanged. -/
theorem hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMoment_two
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2 : ∀ r ∈ Set.Ioo α β, M.cutMoment 2 r ≠ ⊤)
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfluxnn : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, 0 ≤
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
    (hfluxintW : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a' b')
    (hGcont : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r) :
    HasDerivAt M.cutMassReal
      ((M.betaCrit : ℝ) * (-(deriv M.K r0)) * (E1Sign.exclMass M r0).toReal) r0 := by
  have hr0 : 0 < r0 := lt_trans hα0 hαr0
  have hm : r0 ∈ Set.Ioo α β := ⟨hαr0, hr0β⟩
  have hd : ∀ r ∈ Set.Ioo α β, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)}) :=
    fun r hr => M.summable_hdom_of_cutMoment (lt_trans hα0 hr.1)
      (M.cutMoment_one_ne_top_of_two (h2 r hr))
  have hv : ∀ r ∈ Set.Ioo α β, Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r :=
    fun r hr => M.summable_sMomentInfFlux_of_cutMoment_two (lt_trans hα0 hr.1)
      (by rw [SourceModelData.attainedRadii_eq_cornerRadii]; exact hoff r hr) (h2 r hr)
  exact M.hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMass T hTmono hT
    S hSmono hS hα0 hαr0 hr0β hoff hKd hd hboundint hmeasK hmeasinf hcontinf
    (fun r hr => by simpa only [M.cutMoment_one_eq_cutMassAt] using
      M.cutMoment_one_ne_top_of_two (h2 r hr)) hfluxnn hv hfluxintW hGcont hr0
    (M.exclMass_ne_top_of_cutMoment_two (h2 r0 hm))

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms abs_cutEdgeDeriv_le
#print axioms summable_weight_touch_of_incident
#print axioms weight_incident_le
#print axioms summable_hdom_of_cutMoment
#print axioms hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMoment_two

end PercLib.CriticalLRP.Orchestration.SourceModelData
