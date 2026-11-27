/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.AeDerivativeHandoff
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.CornerSafe
public import PercLib.CriticalLRP.Analysis.SecondMomentCase1
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Statistics
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Measurability
public import PercLib.CriticalLRP.Analysis.MomentRegularVariation
public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Errors

/-!
# Proposition I.4.2, Case 3, *second* assertion at the literal cutoff law

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Proposition I.4.2 and
Section I.4.1.  `H_r = (β_c/α) r^{-α} E_{β_c,r}|K| − 1` is the normalized first-moment error;
the paper's Case-3 proof shows that `Ē_{1,r} = 1 − (1−E_{0,r})(1−E_{1,r}) → 0` and is
logarithmically integrable, hence so is `H_r` (Lemma I.4.13, first clause).

On disk the *asymptotic* half lives in `CornerSafe.first_moment_asymptotic_ae` (with the
model-level instantiation `SourceModelData.first_moment_asymptotic_ae_of_offCorner_of_hac`),
and the two input defects are available: `PivotFlux.cutE0` is `→ 0` and logarithmically
integrable (`PivotFlux.tendsto_cutE0`, `CaseOne.logIntegrable_cutE0`), and `PivotFlux.cutE1`
is a log-error function under the triangle condition
(`CutoffDefect.isLogErrorFunction_cutE1_unconditional`).  What is *not* on disk is the
transfer to `H_r`: the log-integrability half of Proposition I.4.2.  That is what this file
supplies, together with the resulting `IsLogErrorFunction M.p2H`.

## Contents

* `isLogErrorFunction_cutE0` — `E_{0,r}` is a log-error function (from the two landed halves).
* `isLogErrorFunction_one_sub_mul_of_eventually` — `1 − (1−E₀)(1−E₁)` is a log-error function
  given `E₀, E₁` log-error and `E₀` *eventually* bounded.  The landed
  `CornerSafe.isLogErrorFunction_one_sub_mul` needs a global bound `|E₀| ≤ 1/8`; at the model
  only an eventual bound is available (`E_{0,r} ≈ 1` for small `r`), so this variant is needed.
* `isLogErrorFunction_p2H` — the main theorem: `H_r = M.p2H` is a log-error function at the
  literal model, i.e. `∫^∞ |H_r| dr/r < ∞` and `H_r → 0`.
* `logIntegrable_p2H`, `tendsto_p2H` — the two conjuncts, in the exact shapes of the hypotheses
  `hlogH` and `hP` of `SourceModelData.tendsto_div_two_of_case3` /
  `SourceModelData.secondMoment_asymptotic_case3`.
* `logIntegrable_cutE0` — the `hlogE0` hypothesis, re-exported in the exact shape used there.

## Source scope and remaining hypotheses

Every hypothesis of `isLogErrorFunction_p2H` is one of:

* the standing model data (`T`, `S` exhaustive enumerations, the kernel tail bounds `hlow`,
  `hupp`, the second-moment finiteness `h2`, the continuity bundle `hcontinf`, `hK`, `hex`) —
  exactly the hypothesis list of the landed `first_moment_asymptotic_ae_of_offCorner_of_hac`;
* `hinf : χ_r → ∞` — discharged on disk from a lower two-point power bound
  (`first_moment_asymptotic_ae_of_rpow_lower_of_hac` takes that route);
* `hE1` — the Case-3 defect estimate `E_{1,r} → 0` with log-integrability, i.e. the triangle
  condition, supplied by `CutoffDefect.isLogErrorFunction_cutE1_unconditional`;
* `h0`, `hC` — `Ē_{1,r} → 0` and eventual boundedness, which follow from `hE1` and
  `PivotFlux.tendsto_cutE0` by `CornerSafe.tendsto_one_sub_mul`.

Nothing here uses the second-moment numerator, the ℓ = 3 polygon bound, or any form of the
`p = 3`, `q = 0` moment gap: this is the first-moment half of the Case-3 assembly only.
-/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The standardization error is a log-error function -/

/-- `E_{0,r} = 1 − |K'(r)| |B_r| r^{α+1}` is a logarithmically integrable error function at the
literal model: log-integrability is `CaseOne.logIntegrable_cutE0`, vanishing is
`PivotFlux.tendsto_cutE0`. -/
theorem isLogErrorFunction_cutE0 :
    Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE0 M r) :=
  ⟨CaseOne.logIntegrable_cutE0 M, PivotFlux.tendsto_cutE0 M⟩

/-! ## The composite error `1 − (1−E₀)(1−E₁)` with an eventual bound -/

/-- `1 − (1−E₀)(1−E₁)` is a logarithmically integrable error function whenever `E₀` and `E₁`
are and `E₀` is bounded on a tail.  (The landed `CornerSafe.isLogErrorFunction_one_sub_mul`
asks for `|E₀| ≤ 1/8` on all of `ℝ`, which the model's `E_{0,r}` does not satisfy near `0`.) -/
theorem isLogErrorFunction_one_sub_mul_of_eventually {E0 E1 : ℝ → ℝ}
    (h0 : Analysis.IsLogErrorFunction E0) (h1 : Analysis.IsLogErrorFunction E1)
    {B r₀ : ℝ} (hB : ∀ r : ℝ, r₀ ≤ r → |E0 r| ≤ B) :
    Analysis.IsLogErrorFunction (fun r : ℝ => 1 - (1 - E0 r) * (1 - E1 r)) := by
  have h0m : Measurable E0 := h0.1.1
  have h1m : Measurable E1 := h1.1.1
  have hsum : Analysis.IsLogErrorFunction (fun r : ℝ => E0 r + E1 r) :=
    Analysis.isLogErrorFunction_add h0 h1
  have hprod : Analysis.IsLogErrorFunction (fun r : ℝ => E0 r * E1 r) :=
    CornerSafe.isLogErrorFunction_mul_right_bounded (f := E0) (g := E1) h1 h0m hB
  have hneg : Analysis.IsLogErrorFunction (fun r : ℝ => -(E0 r * E1 r)) :=
    Analysis.isLogErrorFunction_neg hprod
  have hall : Analysis.IsLogErrorFunction (fun r : ℝ => E0 r + E1 r + -(E0 r * E1 r)) :=
    Analysis.isLogErrorFunction_add hsum hneg
  refine Analysis.isLogErrorFunction_congr hall ?_ ?_
  · filter_upwards with r
    ring
  · exact measurable_const.sub ((measurable_const.sub h0m).mul (measurable_const.sub h1m))

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## Proposition I.4.2, Case 3, second assertion at the literal model -/

/-- **`H_r` is a logarithmically integrable error function at the literal cutoff law.**

This is the second assertion of Proposition I.4.2 in Case 3: `∫^∞ |H_r| dr/r < ∞` and
`H_r → 0`, where `H_r = M.p2H r = (β_c/α) r^{-α} E_{β_c,r}|K| − 1`.  The only probabilistic
input is that the truncated-law defect `E_{1,r} = PivotFlux.cutE1 M` is a log-error function
(triangle condition); the standardization error `E_{0,r}` is unconditional. -/
theorem isLogErrorFunction_p2H (hβ : (0 : ℝ) < M.betaCrit)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hinf : Tendsto M.cutMassReal atTop atTop)
    (hE1 : Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE1 M r))
    {C : ℝ} (hC : ∀ t : ℝ, r₀ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0)) :
    Analysis.IsLogErrorFunction M.p2H := by
  have ha₀0 : 0 < a₀ := lt_trans hRpos hRa₀
  have hr₀0 : 0 < r₀ := lt_trans ha₀0 ha₀r₀
  -- positivity of the mass on the tail
  have hpos : ∀ t : ℝ, r₀ ≤ t → 0 < M.cutMassReal t := by
    intro t ht
    have h2t : M.cutMoment 2 t ≠ ⊤ := h2 t (le_trans (le_of_lt ha₀r₀) ht)
    have hfin : M.cutMassAt t 0 ≠ ⊤ :=
      ne_top_of_le_ne_top h2t (E1Sign.cutMassAt_le_cutMoment_two M t)
    have h1le : (1 : ℝ) ≤ M.cutMassReal t := by
      have h := ENNReal.toReal_mono hfin (E1Sign.one_le_cutMassAt M t)
      simpa [SourceModelData.cutMassReal] using h
    linarith
  -- absolute continuity of the mass on the tail
  have hac : ∀ R' : ℝ, r₀ ≤ R' → AbsolutelyContinuousOnInterval M.cutMassReal r₀ R' :=
    M.cutMassReal_absolutelyContinuousOn_of_offCorner T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀
      hlow hupp h2 hcontinf hK hex
  -- the almost-everywhere standardized ODE (I.4.6)
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
      HasDerivAt M.cutMassReal ((M.betaCrit : ℝ) * (1 - I420Case3.cutError M t)
        * t ^ (-M.α - 1) * (M.cutMassReal t) ^ 2) t :=
    M.ae_hasDerivAt_cutMassAt_toReal_ode T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀
      hlow hupp h2 hcontinf hK hex
  -- the composite defect is measurable and a log-error function
  have hmeasErr : Measurable (I420Case3.cutError M) :=
    I420Case3.measurable_cutError_of_measurables M (I420Case3.measurable_cutE0 M)
      (CutoffDefect.measurable_cutE1 (M := M))
  have hE0 : Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE0 M r) :=
    M.isLogErrorFunction_cutE0
  have hE0b : ∀ᶠ r : ℝ in atTop, |PivotFlux.cutE0 M r| ≤ 1 := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hE0.2) 1 zero_lt_one
    filter_upwards [eventually_ge_atTop N] with r hr
    have h := hN r hr
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt h
  obtain ⟨B, hB⟩ := eventually_atTop.1 hE0b
  have herr : Analysis.IsLogErrorFunction (I420Case3.cutError M) := by
    have h := isLogErrorFunction_one_sub_mul_of_eventually hE0 hE1 (B := 1) (r₀ := B) hB
    refine Analysis.isLogErrorFunction_congr h ?_ hmeasErr
    filter_upwards with r
    simp [I420Case3.cutError]
  -- the first-moment asymptotic (Proposition I.4.2, Case 3)
  have hP : Tendsto (fun r : ℝ => M.cutMassReal r
      / (M.α / (M.betaCrit : ℝ) * r ^ M.α)) atTop (𝓝 1) :=
    CornerSafe.first_moment_asymptotic_ae (f := M.cutMassReal) (h := I420Case3.cutError M)
      (A := (M.betaCrit : ℝ)) (α := M.α) (C := C) hβ M.hα hr₀0 hac hpos hinf hae hmeasErr hC h0
  -- global finiteness of the first cutoff moment, hence measurability of both error shapes
  have h1glob : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤ :=
    M.cutMoment_one_ne_top_of_asymptotic (c := M.α / (M.betaCrit : ℝ)) hP
  have hmass : Measurable M.cutMassReal := by
    have h := M.measurable_cutMoment_toReal 1 h1glob
    have hfun : M.cutMassReal = fun r : ℝ => (M.cutMoment 1 r).toReal := by
      funext r
      rw [show M.cutMassReal r = (M.cutMassAt r 0).toReal from rfl,
        SourceModelData.cutMassAt_zero_eq_cutMoment]
    rw [hfun]
    exact h
  have hHmeas : Measurable (fun r : ℝ =>
      (M.betaCrit : ℝ) / M.α * r ^ (-M.α) * M.cutMassReal r - 1) := by
    fun_prop
  -- the log-integrability of the `H_r` shape
  have hcore : Analysis.LogarithmicallyIntegrable (fun r : ℝ =>
      (M.betaCrit : ℝ) / M.α * r ^ (-M.α) * M.cutMassReal r - 1) :=
    CornerSafe.first_moment_error_logIntegrable_ae (f := M.cutMassReal)
      (h := I420Case3.cutError M) (A := (M.betaCrit : ℝ)) (α := M.α) (C := C)
      hβ M.hα hr₀0 hac hpos hinf hae hmeasErr hC h0 herr.1 hHmeas
  -- the two shapes of the normalized error agree
  have hshape : ∀ᶠ r : ℝ in atTop, M.p2H r =
      (M.betaCrit : ℝ) / M.α * r ^ (-M.α) * M.cutMassReal r - 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hβne : (M.betaCrit : ℝ) ≠ 0 := ne_of_gt hβ
    have hαne : M.α ≠ 0 := ne_of_gt M.hα
    have hpow : r ^ (-M.α) = (r ^ M.α)⁻¹ := Real.rpow_neg hr.le M.α
    have hmass' : M.cutMassReal r = (M.cutMoment 1 r).toReal := by
      rw [show M.cutMassReal r = (M.cutMassAt r 0).toReal from rfl,
        SourceModelData.cutMassAt_zero_eq_cutMoment]
    have hden : (M.α / (M.betaCrit : ℝ)) * r ^ M.α ≠ 0 :=
      mul_ne_zero (div_ne_zero hαne hβne) (Real.rpow_pos_of_pos hr M.α).ne'
    simp only [SourceModelData.p2H, hmass', hpow]
    field_simp
  constructor
  · refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le
      (M.measurable_p2H M.hα h1glob) hcore ?_
    filter_upwards [hshape] with r hr
    rw [hr]
  · have hsub : Tendsto (fun r : ℝ => M.cutMassReal r
        / (M.α / (M.betaCrit : ℝ) * r ^ M.α) - 1) atTop (𝓝 0) := by
      have h := hP.sub_const 1
      simpa using h
    refine hsub.congr' ?_
    filter_upwards [hshape, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    rw [hr]
    have hβne : (M.betaCrit : ℝ) ≠ 0 := ne_of_gt hβ
    have hαne : M.α ≠ 0 := ne_of_gt M.hα
    have hpow : r ^ (-M.α) = (r ^ M.α)⁻¹ := Real.rpow_neg hr0.le M.α
    have hden : (M.α / (M.betaCrit : ℝ)) * r ^ M.α ≠ 0 :=
      mul_ne_zero (div_ne_zero hαne hβne) (Real.rpow_pos_of_pos hr0 M.α).ne'
    rw [hpow]
    field_simp

/-- The `hlogH` hypothesis of the Case-3 second-moment assembly. -/
theorem logIntegrable_p2H (hβ : (0 : ℝ) < M.betaCrit)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hinf : Tendsto M.cutMassReal atTop atTop)
    (hE1 : Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE1 M r))
    {C : ℝ} (hC : ∀ t : ℝ, r₀ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0)) :
    Analysis.LogarithmicallyIntegrable M.p2H :=
  (M.isLogErrorFunction_p2H hβ T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀ hlow hupp h2
    hcontinf hK hex hinf hE1 hC h0).1

/-- The `hP` hypothesis of the Case-3 second-moment assembly, in its exact shape. -/
theorem tendsto_cutMassRatio (hβ : (0 : ℝ) < M.betaCrit)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hinf : Tendsto M.cutMassReal atTop atTop)
    {C : ℝ} (hC : ∀ t : ℝ, r₀ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1) := by
  have hP := CornerSafe.first_moment_asymptotic_ae (f := M.cutMassReal)
      (h := I420Case3.cutError M) (A := (M.betaCrit : ℝ)) (α := M.α) (C := C)
      hβ M.hα (lt_trans (lt_trans hRpos hRa₀) ha₀r₀)
      (M.cutMassReal_absolutelyContinuousOn_of_offCorner T hTmono hT S hSmono hS hRpos hRa₀
        ha₀r₀ hlow hupp h2 hcontinf hK hex)
      (fun t ht => by
        have h2t : M.cutMoment 2 t ≠ ⊤ := h2 t (le_trans (le_of_lt ha₀r₀) ht)
        have hfin : M.cutMassAt t 0 ≠ ⊤ :=
          ne_top_of_le_ne_top h2t (E1Sign.cutMassAt_le_cutMoment_two M t)
        have h1le : (1 : ℝ) ≤ M.cutMassReal t := by
          have h := ENNReal.toReal_mono hfin (E1Sign.one_le_cutMassAt M t)
          simpa [SourceModelData.cutMassReal] using h
        linarith)
      hinf
      (M.ae_hasDerivAt_cutMassAt_toReal_ode T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀
        hlow hupp h2 hcontinf hK hex)
      (I420Case3.measurable_cutError_of_measurables M (I420Case3.measurable_cutE0 M)
        (CutoffDefect.measurable_cutE1 (M := M)))
      hC h0
  exact hP

/-- The `hlogE0` hypothesis of the Case-3 second-moment assembly. -/
theorem logIntegrable_cutE0' :
    Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M) :=
  CaseOne.logIntegrable_cutE0 M

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_cutE0
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_one_sub_mul_of_eventually
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_p2H
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2H
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMassRatio

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The three first-moment inputs, bundled

`hP`, `hlogH` and `hlogE0` of `SourceModelData.tendsto_div_two_of_case3` /
`SourceModelData.secondMoment_asymptotic_case3` are exactly the three components below. -/
theorem case3_firstMoment_inputs (hβ : (0 : ℝ) < M.betaCrit)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₁ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₁ : a₀ < r₁)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hinf : Tendsto M.cutMassReal atTop atTop)
    (hE1 : Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE1 M r))
    {C : ℝ} (hC : ∀ t : ℝ, r₁ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
        / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)
      ∧ Analysis.LogarithmicallyIntegrable M.p2H
      ∧ Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M) :=
  ⟨M.tendsto_cutMassRatio hβ T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₁ hlow hupp h2 hcontinf
      hK hex hinf hC h0,
    M.logIntegrable_p2H hβ T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₁ hlow hupp h2 hcontinf
      hK hex hinf hE1 hC h0,
    M.logIntegrable_cutE0'⟩

/-- **Proposition I.4.15, Case 3, with the first-moment inputs discharged.**

Same conclusion as `SourceModelData.secondMoment_asymptotic_case3`, but the three hypotheses
`hP` (`E_{β_c,r}|K| ∼ (α/β_c) r^α`), `hlogH` (`H_r` logarithmically integrable) and `hlogE0`
(`E_{0,r}` logarithmically integrable) are replaced by the first-moment Case-3 inputs of
`case3_firstMoment_inputs`.  The ℓ = 3 numerator input `hcase3` (hence `hT3`) and the per-vertex
gap `hgap` remain exactly as they were: they are the second-moment content. -/
theorem secondMoment_asymptotic_case3_of_firstMoment (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcase3 : ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
        I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal))
    {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    -- first-moment Case-3 inputs, in place of `hP`, `hlogH`, `hlogE0`
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₁ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₁ : a₀ < r₁)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2' : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hinf : Tendsto M.cutMassReal atTop atTop)
    (hE1 : Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE1 M r))
    {C : ℝ} (hC : ∀ t : ℝ, r₁ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨hP, hlogH, hlogE0⟩ := M.case3_firstMoment_inputs (lt_of_le_of_ne (NNReal.coe_nonneg M.betaCrit) (Ne.symm hβ)) T hTmono hT S hSmono hS
    hRpos hRa₀ ha₀r₁ hlow hupp h2' hcontinf hK hex hinf hE1 hC h0
  exact M.secondMoment_asymptotic_case3 hα hr₀ hβ hac hae h1 h2 hP hcase3 hC3 hC4 hc hgap
    hmeasE2 hmeasEbar hlogH hlogE0 hc3 hgm

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! ## Axiom audit (payoff theorems) -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3_firstMoment_inputs
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_firstMoment

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **Proposition I.4.2, Case 3, second assertion, with the truncated-law defect supplied by
the triangle condition.**

Same conclusion as `isLogErrorFunction_p2H`, but the defect hypothesis `hE1` is discharged by
`CutoffDefect.isLogErrorFunction_cutE1_unconditional` (the triangle condition plus the
open-triangle radial log bound), and the vanishing/boundedness of `Ē_{1,r}` is derived from
`PivotFlux.tendsto_cutE0` and `hE1` (`CornerSafe.tendsto_one_sub_mul`) rather than assumed. -/
theorem isLogErrorFunction_p2H_of_triangle (hβ : (0 : ℝ) < M.betaCrit)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hinf : Tendsto M.cutMassReal atTop atTop)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (h1fin : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C₁ p : ℝ} (hC₁ : 0 ≤ C₁) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₁ p) :
    Analysis.IsLogErrorFunction M.p2H := by
  have hE1 : Analysis.IsLogErrorFunction (fun r : ℝ => PivotFlux.cutE1 M r) :=
    CutoffDefect.isLogErrorFunction_cutE1_unconditional M hTri h1fin hC₁ hp hF
  have h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0) :=
    CornerSafe.tendsto_one_sub_mul (PivotFlux.tendsto_cutE0 M) hE1.2
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h0) 1 zero_lt_one
  have hNle : ∀ t : ℝ, max r₀ (max N 1) ≤ t → |I420Case3.cutError M t| ≤ 1 := by
    intro t ht
    have htN : N ≤ t := le_trans (le_trans (le_max_left N 1) (le_max_right r₀ (max N 1))) ht
    have h := hN t htN
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt h
  have ha₀ : a₀ < max r₀ (max N 1) :=
    lt_of_lt_of_le ha₀r₀ (le_max_left r₀ (max N 1))
  exact M.isLogErrorFunction_p2H hβ T hTmono hT S hSmono hS hRpos hRa₀ ha₀ hlow hupp h2
    hcontinf hK hex hinf hE1 (C := 1) hNle h0

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! ## Axiom audit (triangle-condition form) -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_p2H_of_triangle
