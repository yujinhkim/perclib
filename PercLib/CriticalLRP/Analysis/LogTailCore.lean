/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwtrtcqs`, member `m8`, direction D7.

The general analytic lemma behind Lemma I.4.3: a pointwise logarithmic-decay bound on a
radially-indexed family of extended nonnegative reals forces its radial tail supremum to be
*logarithmically integrable* in the source sense of `(0,∞) → ℝ`, `∫^∞ |h r| dr / r < ∞`.

Nothing here mentions percolation or a particular norm: the quantitative content is
`∫_{Ioi 2} (log r)^(-p) / r < ∞` for `p > 1`, together with monotonicity of `log (1 + ·)` and the
antitonicity of `x ↦ x ^ (-p)` on `(0,∞)`.  The model application is `OpenTriangleLogTail.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.LogTail.Defs
public import Mathlib
public import PercLib.CriticalLRP.Analysis.RegularVariation

@[expose] public section

open Filter MeasureTheory Real Set
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.Analysis

/-! ### The logarithmic majorant -/

/-- The logarithmic majorant is nonnegative at nonnegative radius. -/
theorem logMajorant_nonneg {C p r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) :
    0 ≤ logMajorant C p r := by
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
  exact mul_nonneg hC (Real.rpow_nonneg h2 _)

/-- The logarithmic majorant is **nonincreasing** in the radius for nonnegative exponent.  This is
the only place where the radial structure enters: it uses `log (1 + ·)` monotone and
`x ↦ x ^ (-p)` antitone on `(0, ∞)`, and nothing at all about the index set. -/
theorem logMajorant_le_logMajorant {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p) {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) : logMajorant C p s ≤ logMajorant C p r := by
  have hb : 0 < Real.log (1 + r) := Real.log_pos (by linarith)
  have hmono : Real.log (1 + r) ≤ Real.log (1 + s) := Real.log_le_log (by linarith) (by linarith)
  have hanti : Real.log (1 + s) ^ (-p) ≤ Real.log (1 + r) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hb hmono (by linarith)
  exact mul_le_mul_of_nonneg_left hanti hC

/-! ### The radial tail supremum -/

/-- The radial tail is antitone in the radius, with no hypothesis whatsoever on `nrm` or `F`. -/
theorem antitone_radialTailSup {ι : Type*} (nrm : ι → ℝ) (F : ι → ℝ≥0∞) :
    Antitone (radialTailSup nrm F) := by
  intro r r' hrr'
  exact iSup_le fun x => iSup_le fun hx => le_iSup₂ (f := fun x (_ : r ≤ nrm x) => F x) x
    (le_trans hrr' hx)

/-- **The tail inherits the pointwise logarithmic bound.**  If every value of `F` at positive
radius is at most `C * (log (1 + nrm x)) ^ (-p)`, then the supremum over `{x | r ≤ nrm x}` is at
most `C * (log (1 + r)) ^ (-p)` for `r > 0`.  This is the "antitone tail" half of the lattice
argument; it is stated for an arbitrary radially-indexed family, so it applies to any source norm
and not only to `ℓ^∞`. -/
theorem radialTailSup_le_logMajorant {ι : Type*} {nrm : ι → ℝ} {F : ι → ℝ≥0∞} {C p : ℝ}
    (hC : 0 ≤ C) (hp : 0 ≤ p) {r : ℝ} (hr : 0 < r) (hF : LogRadialBound nrm F C p) :
    radialTailSup nrm F r ≤ ENNReal.ofReal (logMajorant C p r) := by
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact (hF x (lt_of_lt_of_le hr hx)).trans
    (ENNReal.ofReal_le_ofReal (logMajorant_le_logMajorant hC hp hr hx))

/-! ### The improper integral `∫ (log r)^(-p) / r` -/

/-- **`(log r)^(-p) / r` is integrable on `(2,∞)` when `p > 1`.**  This is the quantitative heart
of logarithmic integrability: the substitution `t = log r` turns `dr / r` into `dt`, and
`∫_{t>log 2} t ^ (-p) dt < ∞` exactly when `p > 1`.  Proved through Mathlib's substitution
formula `integrableOn_comp_log_Ioi`, not by discretising the integral. -/
theorem integrableOn_log_rpow_neg_div_id {p : ℝ} (hp : 1 < p) :
    IntegrableOn (fun r : ℝ => Real.log r ^ (-p) / r) (Ioi 2) := by
  have hsub := integrableOn_comp_log_Ioi (fun u : ℝ => u ^ (-p)) (a := 2) (by norm_num)
  have htarget : IntegrableOn (fun u : ℝ => u ^ (-p)) (Ioi (Real.log 2)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (Real.log_pos (by norm_num))
  have h1 : IntegrableOn (fun x : ℝ => x⁻¹ • (Real.log x) ^ (-p)) (Ioi 2) := hsub.mpr htarget
  simpa only [smul_eq_mul, div_eq_inv_mul] using h1

/-! ### Logarithmic integrability from a pointwise logarithmic bound -/

/-- **Main analytic lemma.**  A measurable real function eventually bounded by
`C * (log (1 + r)) ^ (-p)` with `p > 1` and `C ≥ 0` is logarithmically integrable in the source
sense `∫^∞ |T r| dr / r < ∞`.

No continuity, monotonicity or limit behaviour of `T` beyond the displayed bound is assumed; the
bound is only needed on `r ≥ 2`, which is where `log (1 + r) ≥ log r > 0` lets the majorant be
compared with the integrable model profile `(log r) ^ (-p) / r`. -/
theorem logarithmicallyIntegrable_of_le_logMajorant {T : ℝ → ℝ} (hT : Measurable T)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hnn : ∀ r : ℝ, 2 ≤ r → 0 ≤ T r)
    (hb : ∀ r : ℝ, 2 ≤ r → T r ≤ logMajorant C p r) :
    LogarithmicallyIntegrable T := by
  refine ⟨hT, 2, by norm_num, ?_⟩
  have hmaj : IntegrableOn (fun r : ℝ => C * (Real.log r ^ (-p) / r)) (Ioi 2) :=
    (integrableOn_log_rpow_neg_div_id hp).const_mul C
  refine Integrable.mono' hmaj ?_ ?_
  · exact (hT.abs.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr2 : 2 ≤ r := le_of_lt hr
    have hrpos : 0 < r := by linarith
    have hdec : Real.log (1 + r) ^ (-p) ≤ Real.log r ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (Real.log_pos (by linarith))
        (Real.log_le_log (by linarith) (by linarith)) (by linarith)
    have hb' : T r ≤ C * Real.log r ^ (-p) :=
      (hb r hr2).trans (mul_le_mul_of_nonneg_left hdec hC)
    have hmaj' : 0 ≤ C * (Real.log r ^ (-p) / r) :=
      mul_nonneg hC (div_nonneg (Real.rpow_nonneg (Real.log_pos (by linarith)).le _) hrpos.le)
    have hleft : ‖|T r| / r‖ = T r / r := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg (T r)) hrpos.le),
        abs_of_nonneg (hnn r hr2)]
    simp only [hleft]
    calc T r / r ≤ C * Real.log r ^ (-p) / r := div_le_div_of_nonneg_right hb' hrpos.le
      _ = C * (Real.log r ^ (-p) / r) := by ring

/-- The real-valued radial tail inherits the pointwise logarithmic bound at positive radius. -/
theorem radialTailSup_toReal_le {ι : Type*} {nrm : ι → ℝ} {F : ι → ℝ≥0∞} {C p : ℝ}
    (hC : 0 ≤ C) (hp : 0 ≤ p) {r : ℝ} (hr : 0 < r) (hF : LogRadialBound nrm F C p) :
    (radialTailSup nrm F r).toReal ≤ logMajorant C p r := by
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (radialTailSup_le_logMajorant hC hp hr hF)).trans_eq ?_
  exact ENNReal.toReal_ofReal (logMajorant_nonneg hC hr.le)

/-- The real-valued radial tail is measurable: it is `toReal` applied to an antitone
`ℝ≥0∞`-valued function. -/
theorem measurable_radialTailSup_toReal {ι : Type*} (nrm : ι → ℝ) (F : ι → ℝ≥0∞) :
    Measurable (fun r => (radialTailSup nrm F r).toReal) :=
  ENNReal.measurable_toReal.comp (antitone_radialTailSup nrm F).measurable

/-- **The general radial-tail lemma (norm-agnostic analytic content of Lemma I.4.3).**  For any
index set, any radial function `nrm`, and any `F` decaying at the logarithmic rate `p > 1` at
positive radius, the real-valued tail `r ↦ (sup {F x | r ≤ nrm x}).toReal` is logarithmically
integrable.

Every percolation-specific ingredient (which lattice, which norm, which kernel, and above all the
convolution estimate producing `hF`) is outside this lemma. -/
theorem logarithmicallyIntegrable_radialTailSup {ι : Type*} {nrm : ι → ℝ} {F : ι → ℝ≥0∞}
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p) (hF : LogRadialBound nrm F C p) :
    LogarithmicallyIntegrable (fun r => (radialTailSup nrm F r).toReal) :=
  logarithmicallyIntegrable_of_le_logMajorant (measurable_radialTailSup_toReal nrm F) hC hp
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ hr => radialTailSup_toReal_le hC (by linarith) (by linarith) hF)


/-! ### The polynomial-decay (Case 2) analogue

The same three steps with the majorant `C * r ^ (-a)`, `a > 0`, which is the shape of the
pointwise bound (I.4.11) in Case 2 of `(HD)`.  No logarithmic correction is needed there.
-/

/-- The power majorant is nonincreasing in the radius. -/
theorem powMajorant_le_powMajorant {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) : powMajorant C a s ≤ powMajorant C a r := by
  have hanti : s ^ (-a) ≤ r ^ (-a) := Real.rpow_le_rpow_of_nonpos hr hrs (by linarith)
  exact mul_le_mul_of_nonneg_left hanti hC

/-- The power majorant tends to `0` at infinity for positive exponent. -/
theorem tendsto_powMajorant_zero {C a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => powMajorant C a r) atTop (𝓝 0) := by
  simpa only [powMajorant, mul_zero] using (tendsto_rpow_neg_atTop ha).const_mul C

/-- The tail inherits the polynomial pointwise bound. -/
theorem radialTailSup_le_powMajorant {ι : Type*} {nrm : ι → ℝ} {F : ι → ℝ≥0∞} {C a : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) (hF : PowRadialBound nrm F C a) :
    radialTailSup nrm F r ≤ ENNReal.ofReal (powMajorant C a r) := by
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact (hF x (lt_of_lt_of_le hr hx)).trans
    (ENNReal.ofReal_le_ofReal (powMajorant_le_powMajorant hC ha hr hx))

/-- The real-valued radial tail inherits the polynomial bound at positive radius. -/
theorem radialTailSup_toReal_le_powMajorant {ι : Type*} {nrm : ι → ℝ} {F : ι → ℝ≥0∞} {C a : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) (hF : PowRadialBound nrm F C a) :
    (radialTailSup nrm F r).toReal ≤ powMajorant C a r := by
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (radialTailSup_le_powMajorant hC ha hr hF)).trans_eq ?_
  exact ENNReal.toReal_ofReal (mul_nonneg hC (Real.rpow_nonneg hr.le _))

/-- **`r ^ (-a) / r` is integrable on `(1,∞)` for `a > 0`.** -/
theorem integrableOn_rpow_neg_div_id {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r ^ (-a) / r) (Ioi 1) := by
  have hbase : IntegrableOn (fun r : ℝ => r ^ (-a - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  refine hbase.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr0 : 0 < r := lt_trans one_pos hr
  change r ^ (-a - 1) = r ^ (-a) / r
  rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hr0]
  ring_nf

/-- **Polynomial-decay version of the main analytic lemma** (Case 2 of `(HD)`).  A measurable real
function eventually bounded by `C * r ^ (-a)` with `a > 0` and `C ≥ 0` is logarithmically
integrable. -/
theorem logarithmicallyIntegrable_of_le_powMajorant {T : ℝ → ℝ} (hT : Measurable T)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hnn : ∀ r : ℝ, 1 ≤ r → 0 ≤ T r)
    (hb : ∀ r : ℝ, 1 ≤ r → T r ≤ powMajorant C a r) :
    LogarithmicallyIntegrable T := by
  refine ⟨hT, 1, one_pos, ?_⟩
  have hmaj : IntegrableOn (fun r : ℝ => C * (r ^ (-a) / r)) (Ioi 1) :=
    (integrableOn_rpow_neg_div_id ha).const_mul C
  refine Integrable.mono' hmaj ?_ ?_
  · exact (hT.abs.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr1 : 1 ≤ r := le_of_lt hr
    have hrpos : 0 < r := lt_trans one_pos hr
    have hb' : T r ≤ C * r ^ (-a) := hb r hr1
    have hmaj' : 0 ≤ C * (r ^ (-a) / r) :=
      mul_nonneg hC (div_nonneg (Real.rpow_nonneg hrpos.le _) hrpos.le)
    have hleft : ‖|T r| / r‖ = T r / r := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg (T r)) hrpos.le),
        abs_of_nonneg (hnn r hr1)]
    simp only [hleft]
    calc T r / r ≤ C * r ^ (-a) / r := div_le_div_of_nonneg_right hb' hrpos.le
      _ = C * (r ^ (-a) / r) := by ring

/-- **Error-function form of the polynomial-decay case.** -/
theorem isLogErrorFunction_of_le_powMajorant {T : ℝ → ℝ} (hT : Measurable T)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hnn : ∀ r : ℝ, 1 ≤ r → 0 ≤ T r)
    (hb : ∀ r : ℝ, 1 ≤ r → T r ≤ powMajorant C a r) :
    IsLogErrorFunction T := by
  refine ⟨logarithmicallyIntegrable_of_le_powMajorant hT hC ha hnn hb, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_powMajorant_zero (C := C) ha) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr using hnn r hr
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr using hb r hr

/-- **The radial-tail lemma in polynomial-decay form.** -/
theorem logarithmicallyIntegrable_radialTailSup_pow {ι : Type*} {nrm : ι → ℝ} {F : ι → ℝ≥0∞}
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hF : PowRadialBound nrm F C a) :
    LogarithmicallyIntegrable (fun r => (radialTailSup nrm F r).toReal) :=
  logarithmicallyIntegrable_of_le_powMajorant (measurable_radialTailSup_toReal nrm F) hC ha
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ hr => radialTailSup_toReal_le_powMajorant hC (by linarith) (by linarith) hF)


/-! ### The values tend to zero -/

/-- The logarithmic majorant tends to `0` at infinity for positive exponent. -/
theorem tendsto_logMajorant_zero {C p : ℝ} (hp : 0 < p) :
    Tendsto (fun r : ℝ => logMajorant C p r) atTop (𝓝 0) := by
  have hlog : Tendsto (fun r : ℝ => Real.log (1 + r)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have h2 : Tendsto (fun r : ℝ => (Real.log (1 + r)) ^ (-p)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp hlog
  simpa only [logMajorant, mul_zero] using h2.const_mul C

/-- **The analytic content of Lemma I.4.3, in error-function form.**  A measurable function
eventually bounded by `C * (log (1 + r)) ^ (-p)` with `p > 1` is a logarithmically integrable
error function in the repository's sense `IsLogErrorFunction`. -/
theorem isLogErrorFunction_of_le_logMajorant {T : ℝ → ℝ} (hT : Measurable T)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hnn : ∀ r : ℝ, 2 ≤ r → 0 ≤ T r)
    (hb : ∀ r : ℝ, 2 ≤ r → T r ≤ logMajorant C p r) :
    IsLogErrorFunction T := by
  refine ⟨logarithmicallyIntegrable_of_le_logMajorant hT hC hp hnn hb, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_logMajorant_zero (C := C) (by linarith)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr using hnn r hr
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr using hb r hr


/-- **Error-function form of the general radial-tail lemma.**  Under the same pointwise
logarithmic bound at positive radius the real-valued radial tail is a logarithmically integrable
error function, i.e. it also tends to `0`. -/
theorem isLogErrorFunction_radialTailSup {ι : Type*} {nrm : ι → ℝ} {F : ι → ℝ≥0∞}
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p) (hF : LogRadialBound nrm F C p) :
    IsLogErrorFunction (fun r => (radialTailSup nrm F r).toReal) :=
  isLogErrorFunction_of_le_logMajorant (measurable_radialTailSup_toReal nrm F) hC hp
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ hr => radialTailSup_toReal_le hC (by linarith) (by linarith) hF)

/-- **Error-function form of the radial-tail lemma in polynomial-decay form.** -/
theorem isLogErrorFunction_radialTailSup_pow {ι : Type*} {nrm : ι → ℝ} {F : ι → ℝ≥0∞}
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hF : PowRadialBound nrm F C a) :
    IsLogErrorFunction (fun r => (radialTailSup nrm F r).toReal) :=
  isLogErrorFunction_of_le_powMajorant (measurable_radialTailSup_toReal nrm F) hC ha
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ hr => radialTailSup_toReal_le_powMajorant hC (by linarith) (by linarith) hF)

end PercLib.CriticalLRP.Analysis
