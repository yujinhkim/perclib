/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`, direction (2).

The `p`-th moment bound of Proposition I.4.20 (step (I.4.19)) with the everywhere derivative
identity of Lemma I.4.1 replaced by its off-corner (a.e.) form.

`Analysis/Cutoff/OffCorner/AeDerivativeHandoff.lean` shows that the cutoff mass has a radial
derivative only off the (null) set of attained radii, and that this is the form the off-corner
machinery actually supplies.  `VolumeMoments/HigherMoments/Assembly.moment_upper_bound` instead
consumes `hderiv : ∀ x, 0 < x → HasDerivAt (fun r => mom p r) (f' x) x` at *every* positive
radius.  The theorems below are the a.e. replacements:

* `moment_upper_bound_ae` — a.e. derivative plus an a.e. one-sided ODE with measurable defect;
* `moment_upper_bound_ae_eps` — the same from the paper's `∀ ε, ∀ᶠ x, (1+ε)` hypothesis in a.e.
  form, which is the shape produced by `derivative_bound`.

Every probabilistic input other than the derivative identity is unchanged.
-/
module

public import PercLib.CriticalLRP.Analysis.AEHigherMoments.LemmaI422Final
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.Assembly


/-! # Almost-everywhere higher-moment interface: MomentBound -/

set_option autoImplicit false
set_option linter.style.multiGoal false

open MeasureTheory Filter Set Topology
open scoped Topology

@[expose] public section

namespace PercLib.CriticalLRP.Analysis.AE

/-- **Eliminating an `(1+ε)`-for-every-ε a.e. bound.**

If `f' ≤ (1 + ε) P` holds a.e. for every `ε > 0`, then `f' ≤ P` holds a.e.: take the intersection
over `ε = 1/(n+1)` (a countable intersection of null exceptional sets is null) and let `n → ∞`. -/
theorem ae_le_of_forall_ae_one_add_mul {f' P : ℝ → ℝ} {r₀ : ℝ}
    (h : ∀ ε > 0, ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)), f' x ≤ (1 + ε) * P x) :
    ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)), f' x ≤ P x := by
  have hall : ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)),
      ∀ n : ℕ, f' x ≤ (1 + 1 / ((n : ℝ) + 1)) * P x := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact h _ hn
  filter_upwards [hall] with x hx
  have hconst : Tendsto (fun _ : ℕ => f' x) atTop (𝓝 (f' x)) := tendsto_const_nhds
  have hu : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1)) * P x) atTop (𝓝 (1 * P x)) := by
    have h1 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.mul_const (P x)
  have hle : f' x ≤ 1 * P x :=
    le_of_tendsto_of_tendsto hconst hu (Filter.Eventually.of_forall hx)
  simpa using hle

end PercLib.CriticalLRP.Analysis.AE

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

open PercLib.CriticalLRP.Analysis
open PercLib.CriticalLRP.Analysis.AE

/-- **The moment bound of Proposition I.4.20 with an a.e. derivative identity.**

This is `moment_upper_bound` with `hderiv` replaced by

* `AbsolutelyContinuousOnTail (mom p) r₀` and `AeHasDerivAtOnTail (mom p) f' r₀`, and
* the `(1+o(1))` one-sided ODE by its a.e. form with an explicit measurable defect `δ → 0`,

which is the off-corner shape of the radial derivative of a moment.  The conclusion, and every
other hypothesis, are unchanged. -/
theorem moment_upper_bound_ae {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {f' δ : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hac : AbsolutelyContinuousOnTail (fun r => mom p r) r₀)
    (hae : AeHasDerivAtOnTail (fun r => mom p r) f' r₀)
    (hδm : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hfbd : ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)),
      f' x ≤ (1 + δ x) *
        (((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom p r ≤ (1 + ε) * mixedMoment p mom r := by
  obtain ⟨D⟩ := drivingTerm_RVPosData hp hα hmom hmommeas1 hmommeas2 h1 h2
  have hlin : 0 < ((p : ℝ) + 1) * α := by positivity
  have hgap : (0 : ℝ) < ((p : ℝ) - 2) * α := by
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have : 0 < (p : ℝ) - 2 := by linarith
    positivity
  have hlt : ((p : ℝ) + 1) * α < (2 * (p : ℝ) - 1) * α := by
    have := drivingIndex_sub_linearIndex p α
    linarith
  have hhpos : ∀ x, 0 < x → 0 < drivingTerm p α mom x :=
    fun x hx => drivingTerm_pos hp hα (hmom 1 x hx) (hmom 2 x hx)
  have hfpos : ∀ x, 0 < x → 0 < mom p x := fun x hx => hmom p x hx
  intro ε hε
  have h := ae_lemma_I_4_22_of_defect_bound D hlin hlt hr₀ hhpos hfpos hac hae
    hδm hδ0 hδ1 hfbd ε hε
  refine h.mono (fun r hr => ?_)
  have hba : (2 * (p : ℝ) - 1) * α - ((p : ℝ) + 1) * α = ((p : ℝ) - 2) * α :=
    drivingIndex_sub_linearIndex p α
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hkey : drivingTerm p α mom r / ((2 * (p : ℝ) - 1) * α - ((p : ℝ) + 1) * α)
      = mixedMoment p mom r := by
    rw [hba, drivingTerm_eq_smul]
    field_simp
  rwa [hkey] at hr

/-- **The moment bound of Proposition I.4.20 from the paper's `(1+ε)` a.e. ODE.**

Here the one-sided ODE is the a.e. form of the hypothesis that `derivative_bound` produces:
for every `ε > 0`, `f' ≤ (1 + ε) (((p+1) α mom p + drivingTerm)/r)` a.e.  The `ε` is eliminated
by a countable intersection (`ae_le_of_forall_ae_one_add_mul`), leaving the sharp a.e. ODE, so
this is a genuine consequence of `moment_upper_bound_ae` and not a restatement. -/
theorem moment_upper_bound_ae_eps {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {f' : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hac : AbsolutelyContinuousOnTail (fun r => mom p r) r₀)
    (hae : AeHasDerivAtOnTail (fun r => mom p r) f' r₀)
    (hfbd : ∀ ε > 0, ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)),
      f' x ≤ (1 + ε) *
        ((((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x) / x)) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom p r ≤ (1 + ε) * mixedMoment p mom r := by
  refine moment_upper_bound_ae hp hα hmom hmommeas1 hmommeas2 h1 h2 hr₀ hac hae
    (δ := fun _ => 0) measurable_const tendsto_const_nhds (fun x _ => by simp) ?_
  filter_upwards [ae_le_of_forall_ae_one_add_mul hfbd] with x hx
  simpa using hx

end PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Analysis.AE.intervalIntegral_ae_deriv_eq_sub
#print axioms PercLib.CriticalLRP.Analysis.AE.sub_le_integral_of_ae_hasDerivAt_of_le
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_hasDerivAt_div_rpow
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_normalized_increment_le_of_driving_bound
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_eventually_ratio_le_of_driving_bound
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_lemma_I_4_22_of_defect_bound
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_lemma_I_4_22_of_ae_sharp_bound
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_le_of_forall_ae_one_add_mul
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_ae
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_ae_eps
