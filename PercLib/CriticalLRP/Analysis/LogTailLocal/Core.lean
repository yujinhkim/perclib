/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwttizjk`, member `m4`, direction D8.

Norm-agnostic analytic content of the local clause of logarithmic integrability.

Everything here is about functions of one real variable.  The three inputs are:

* antitonicity of the real function (or of an `ℝ≥0∞`-valued function whose `.toReal` is taken);
* finiteness of the `ℝ≥0∞`-valued function at the left endpoint of the interval — needed because
  `ENNReal.toReal` is *not* monotone across `⊤` (`⊤.toReal = 0`), so a supremum can only be
  bounded once finiteness is known;
* measurability, which antitonicity supplies for free.

The output is `IntegrableOn` on each `[R1, R2]` with `0 < R1 ≤ R2`, first for the function itself
and then for the logarithmic density `r ↦ h r / r`.  The model application (the actual
open-triangle tail) is in `LogTailLocal/Source.lean`.

This file does **not** prove any decay at `∞`: local integrability is a compact-interval statement.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Analysis.LogTailLocal.Defs
public import PercLib.CriticalLRP.Analysis.LogTailCore

/-!
# Norm-agnostic analytic content of the local clause

Antitone finiteness gives local integrability; see the header comment above.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology Interval

namespace PercLib.CriticalLRP.Analysis.LogTailLocal

/-! ### Antitone real functions are integrable on compacta -/

/-- An antitone real function is bounded in absolute value on `[a, b]` by the larger of the two
endpoint values in absolute value.  Both endpoint estimates are used, so this is where
antitonicity on the whole interval (rather than at a single point) enters. -/
theorem abs_le_of_antitone {f : ℝ → ℝ} (hf : Antitone f) {a b r : ℝ} (hr : r ∈ Icc a b) :
    |f r| ≤ |f a| ⊔ |f b| := by
  have h1 : f b ≤ f r := hf hr.2
  have h2 : f r ≤ f a := hf hr.1
  have ha : |f a| ≤ |f a| ⊔ |f b| := le_max_left _ _
  have hb : |f b| ≤ |f a| ⊔ |f b| := le_max_right _ _
  rw [abs_le] at ha hb ⊢
  exact ⟨le_trans hb.1 h1, le_trans h2 ha.2⟩

/-- **An antitone real function is integrable on every compact interval.**  Measurability comes from
antitonicity, and the bound from `abs_le_of_antitone`; no continuity, no finiteness hypothesis and
no hypothesis on the order of the endpoints is needed. -/
theorem integrableOn_Icc_of_antitone {f : ℝ → ℝ} (hf : Antitone f) (a b : ℝ) :
    IntegrableOn f (Icc a b) volume :=
  IntegrableOn.of_bound isCompact_Icc.measure_lt_top hf.measurable.aestronglyMeasurable
    (|f a| ⊔ |f b|) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      rw [Real.norm_eq_abs]
      exact abs_le_of_antitone hf hr)

/-- The `∀`-form of `integrableOn_Icc_of_antitone`, i.e. the local-integrability predicate of
`LogTailLocal/Defs.lean` holds for every antitone real function. -/
theorem integrableOnPositiveCompacts_of_antitone {f : ℝ → ℝ} (hf : Antitone f) :
    IntegrableOnPositiveCompacts f :=
  fun _ _ _ _ => integrableOn_Icc_of_antitone hf _ _

/-- The interval-integral form, matching the `∫_r^R` notation of the ODE lemmas. -/
theorem intervalIntegrable_of_antitone {f : ℝ → ℝ} (hf : Antitone f) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable f volume a b :=
  PercLib.CriticalLRP.Analysis.intervalIntegrable_of_integrableOn_uIcc
    (by rw [uIcc_of_le hab]; exact integrableOn_Icc_of_antitone hf a b)

/-! ### The `ℝ≥0∞`-valued case

`ENNReal.toReal` is not monotone across `⊤`, so an antitone `ℝ≥0∞`-valued function has a monotone
`.toReal` only once it is known to be finite.  Finiteness at the left endpoint is enough. -/

/-- Finiteness at the left endpoint propagates to the right, and gives the bound. -/
theorem toReal_le_toReal_of_antitone {g : ℝ → ℝ≥0∞} (hg : Antitone g) {a r : ℝ}
    (hfin : g a ≠ ⊤) (har : a ≤ r) : (g r).toReal ≤ (g a).toReal :=
  ENNReal.toReal_mono hfin (hg har)

/-- An antitone `ℝ≥0∞`-valued function which is finite at `a` has a `.toReal` which is integrable
on `[a, b]`, with the explicit bound `(g a).toReal`.  No positivity of `a` is needed. -/
theorem integrableOn_Icc_toReal_of_antitone {g : ℝ → ℝ≥0∞} (hg : Antitone g) {a : ℝ}
    (hfin : g a ≠ ⊤) (b : ℝ) :
    IntegrableOn (fun r => (g r).toReal) (Icc a b) volume :=
  IntegrableOn.of_bound isCompact_Icc.measure_lt_top
    ((ENNReal.measurable_toReal.comp hg.measurable).aestronglyMeasurable) ((g a).toReal) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact toReal_le_toReal_of_antitone hg hfin hr.1)

/-- **Local integrability of the real-valued tail.**  For an antitone `ℝ≥0∞`-valued `g` that is
finite at every positive radius, `r ↦ (g r).toReal` is integrable on every `[R1, R2]` with
`0 < R1 ≤ R2`.  This is the statement that a finite antitone tail has no local blow-up. -/
theorem integrableOnPositiveCompacts_toReal_of_antitone {g : ℝ → ℝ≥0∞} (hg : Antitone g)
    (hfin : ∀ r : ℝ, 0 < r → g r ≠ ⊤) :
    IntegrableOnPositiveCompacts (fun r => (g r).toReal) :=
  fun _ _ h1 _ => integrableOn_Icc_toReal_of_antitone hg (hfin _ h1) _

/-- The local bound which accompanies the previous theorem: a finite antitone tail is bounded on
`[R1, R2]` by its value at `R1`. -/
theorem boundedOnPositiveCompacts_toReal_of_antitone {g : ℝ → ℝ≥0∞} (hg : Antitone g)
    (hfin : ∀ r : ℝ, 0 < r → g r ≠ ⊤) :
    BoundedOnPositiveCompacts (fun r => (g r).toReal) := by
  intro R1 R2 h1 _
  refine ⟨(g R1).toReal, fun r hr => ?_⟩
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact toReal_le_toReal_of_antitone hg (hfin R1 h1) hr.1

/-! ### The logarithmic density `r ↦ h r / r` -/

/-- Division by `id` preserves integrability on a compact interval strictly to the right of `0`.
Proved through the divisibility of `r ↦ r⁻¹` on such an interval. -/
theorem integrableOn_div_id_of_integrableOn {h : ℝ → ℝ} {a b : ℝ}
    (hint : IntegrableOn h (Icc a b) volume) (ha : 0 < a) :
    IntegrableOn (fun r => h r / r) (Icc a b) volume := by
  have hcont : ContinuousOn (fun r : ℝ => r⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun r hr => ne_of_gt (lt_of_lt_of_le ha hr.1))
  have hmul : IntegrableOn (fun r : ℝ => h r * r⁻¹) (Icc a b) volume :=
    hint.mul_continuousOn hcont isCompact_Icc
  refine hmul.congr_fun (fun r _ => ?_) measurableSet_Icc
  simp only [div_eq_mul_inv]

/-- The weighted local clause follows from the unweighted one, away from `0`. -/
theorem logWeightedIntegrableOnPositiveCompacts_of_integrableOnPositiveCompacts {h : ℝ → ℝ}
    (hh : IntegrableOnPositiveCompacts h) : LogWeightedIntegrableOnPositiveCompacts h :=
  fun _ _ h1 h2 => integrableOn_div_id_of_integrableOn (hh _ _ h1 h2) h1

/-- The weighted local form for a finite antitone `ℝ≥0∞`-valued tail, obtained directly with the
explicit bound `(g R1).toReal / R1`. -/
theorem integrableOn_Icc_toReal_div_of_antitone {g : ℝ → ℝ≥0∞} (hg : Antitone g) {a : ℝ}
    (ha : 0 < a) (hfin : g a ≠ ⊤) (b : ℝ) :
    IntegrableOn (fun r => (g r).toReal / r) (Icc a b) volume :=
  IntegrableOn.of_bound isCompact_Icc.measure_lt_top
    (((ENNReal.measurable_toReal.comp hg.measurable).div measurable_id).aestronglyMeasurable)
    ((g a).toReal / a) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
      have hb : (g r).toReal ≤ (g a).toReal := toReal_le_toReal_of_antitone hg hfin hr.1
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg hr0.le),
        div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul hb
        (by rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le ha hr.1)
        (by positivity) ENNReal.toReal_nonneg)

/-- The weighted local clause for a finite antitone `ℝ≥0∞`-valued tail. -/
theorem logWeightedIntegrableOnPositiveCompacts_toReal_of_antitone {g : ℝ → ℝ≥0∞}
    (hg : Antitone g) (hfin : ∀ r : ℝ, 0 < r → g r ≠ ⊤) :
    LogWeightedIntegrableOnPositiveCompacts (fun r => (g r).toReal) :=
  fun _ _ h1 _ => integrableOn_Icc_toReal_div_of_antitone hg h1 (hfin _ h1) _

/-! ### The improper integral is the limit of the interval integrals

This is the point of keeping the local clause separate: `LogarithmicallyIntegrable h` gives
finiteness of `∫_{Ioi r₀} |h r| / r`, and the local clause gives existence of the interval
integrals, so the source's `∫_{r₀}^∞ h r dr / r` is literally the limit of `∫_{r₀}^{R}`. -/

/-- Absolute convergence of the logarithmic integral implies convergence of the logarithmic
integral. -/
theorem integrableOn_div_id_of_integrableOn_abs {h : ℝ → ℝ} (hm : Measurable h) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (habs : IntegrableOn (fun r => |h r| / r) (Ioi r₀) volume) :
    IntegrableOn (fun r => h r / r) (Ioi r₀) volume := by
  refine Integrable.mono' habs (hm.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := lt_trans hr₀ hr
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]

/-- **The source's improper logarithmic integral.**  Under the global clause
`∫_{Ioi r₀} |h r| / r < ∞` and the local clause, the interval integrals `∫_{r₀}^{R} h r dr / r`
converge to `∫_{Ioi r₀} h r dr / r`.  This identifies the improper integral which the paper's
`∫^∞ h r dr / r` denotes with a limit of ordinary interval integrals. -/
theorem tendsto_intervalIntegral_div_id {h : ℝ → ℝ} (hm : Measurable h) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (habs : IntegrableOn (fun r => |h r| / r) (Ioi r₀) volume) :
    Tendsto (fun R => ∫ r in r₀..R, h r / r) atTop
      (𝓝 (∫ r in Ioi r₀, h r / r)) :=
  intervalIntegral_tendsto_integral_Ioi r₀
    (integrableOn_div_id_of_integrableOn_abs hm hr₀ habs) tendsto_id

/-! ### The norm-agnostic radial tail

The same local clause for the abstract radial tail `radialTailSup nrm F` of `LogTail/Defs.lean`, so
that it is available for any source norm and any radially-indexed family, not only the model's
`∇_r`.  Here finiteness of the tail at every positive radius must be assumed: unlike the model case,
there is no `C (log (1+r)) ^ (-p)` bound available to produce it. -/

/-- The local clause for the abstract radial tail. -/
theorem integrableOnPositiveCompacts_radialTailSup_toReal {ι : Type*} (nrm : ι → ℝ)
    (F : ι → ℝ≥0∞) (hfin : ∀ r : ℝ, 0 < r → radialTailSup nrm F r ≠ ⊤) :
    IntegrableOnPositiveCompacts (fun r => (radialTailSup nrm F r).toReal) :=
  integrableOnPositiveCompacts_toReal_of_antitone (antitone_radialTailSup nrm F) hfin

/-- The weighted local clause for the abstract radial tail. -/
theorem logWeightedIntegrableOnPositiveCompacts_radialTailSup_toReal {ι : Type*} (nrm : ι → ℝ)
    (F : ι → ℝ≥0∞) (hfin : ∀ r : ℝ, 0 < r → radialTailSup nrm F r ≠ ⊤) :
    LogWeightedIntegrableOnPositiveCompacts (fun r => (radialTailSup nrm F r).toReal) :=
  logWeightedIntegrableOnPositiveCompacts_toReal_of_antitone (antitone_radialTailSup nrm F) hfin

/-- **The source-style logarithmic integrability clause is automatic** for an abstract radial tail
which is finite at every positive radius and whose entries decay at the logarithmic rate `p > 1`.
This is the norm-agnostic form of `sourceLogIntegrable_nablaTail`. -/
theorem sourceLogIntegrable_radialTailSup_toReal {ι : Type*} {nrm : ι → ℝ} {F : ι → ℝ≥0∞}
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p) (hF : LogRadialBound nrm F C p) :
    SourceLogIntegrable (fun r => (radialTailSup nrm F r).toReal) :=
  ⟨logarithmicallyIntegrable_radialTailSup hC hp hF,
   integrableOnPositiveCompacts_radialTailSup_toReal nrm F
     (fun _ hr => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
       (radialTailSup_le_logMajorant hC (by linarith) hr hF))⟩

end PercLib.CriticalLRP.Analysis.LogTailLocal
