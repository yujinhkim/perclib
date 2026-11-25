/-
# Conditional logarithmic integrability of the cutoff defect

Adapted from the accepted `smwtvrwnn`/`m2` D7C packet at integration HEAD `673b911`.

The paper's Lemma I.4.13 is the separate integral-transformation theorem.  This file proves the
conditional logarithmic-integrability assertion for `𝓔_{1,r}` used in Proposition I.4.2; it does
not restate or prove that integral-transformation theorem.

Source: Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), §I.4.1–I.4.2,
Lemma I.4.13, and the Case 2 / Case 3 analysis of `(HD)` ((I.4.11) and (I.4.13)).

The object is `CutoffDefect.cutE1 M r`, the paper's defect `𝓔_{1,r}` *at the range-truncated
critical law* `T_{β_c,r}` (Definition I.1.5), i.e. `VolumeMoments.cE1` of the three cutoff
statistics `E|K|`, `E[|K|Σ_{y∈B_r}|K_y|]`, `E[|K ∩ B_r||K|²]` and the ball count `|B_r|`.

## What is proved

Norm-free analytic layer (`PercLib.CriticalLRP.Analysis`):

* `measurable_logMajorant`, `isLogErrorFunction_logMajorant` — the profile
  `r ↦ C (log (1+r)) ^ (-p)` is measurable and, for `p > 1`, a logarithmically integrable error
  function (its log-integral is `∫ (log r)^{-p} dr/r`, finite iff `p > 1`; Mathlib's
  `integrableOn_comp_log_Ioi`, packaged at HEAD as `integrableOn_log_rpow_neg_div_id`).
* `isLogErrorFunction_const_mul` — closure of the error-function class under constant multiples.
* `isLogErrorFunction_comp_rpow_add_rpow_neg` — **the source's polynomial rescaling**
  `h ↦ (r ↦ h (r^c) + r^{-c})`, `c > 0`, preserves logarithmic integrability *and* the limit
  `→ 0`.  Power rescaling is Lemma I.4.19 (`logarithmicallyIntegrable_comp_rpow_const_mul`), and
  `r^{-c}` is the explicit polynomial slack; both summands are error functions and the sum is
  closed by `isLogErrorFunction_add`.
* `logMajorant_sqrt_eq_comp_rpow`, `isLogErrorFunction_logMajorant_sqrt_add` — the **composition
  point where `TailLog` enters**: the two-scale radius `√r` of (I.4.13) is literally the power
  rescaling with `c = 1/2`, so the source's `h(r^c) + r^{-c}` applies verbatim to
  `r ↦ logMajorant C p (√r) + r^{-1/2}`.
* `integrableOn_abs_div_of_eventually_le_rpowScale` — if `T` is measurable, eventually
  nonnegative and eventually `T r ≤ K (logMajorant C p (r^c) + r^{-c})` with `p > 1`, then
  `r ↦ |T r| / r` is integrable on a tail.  This is the comparison step turning a two-scale
  rate into a finite logarithmic integral.
* `integrableOn_abs_div_of_eventually_le_rpow_neg` — the polynomial analogue
  (`T r ≤ K r^{-e}`, `e > 0`), used for Case 2 of `(HD)`.
* `integrableOnPositiveCompacts_of_measurable_bounded` — measurability plus local boundedness
  gives the local clause of the source-style predicate.

Model layer (`PercLib.CriticalLRP.CutoffDefect`), all at the actual cut law:

* `arith_absorb` — the elementary absorption `A a + c ≤ max A 1 (c + b)` for `a ≤ b`, `A,c,b ≥ 0`.
* `cutE1_le_rpowScale` — the defect bound (HEAD's `cutE1_le_log_rate`, which is Lemma I.4.11 at
  the truncated law under `∇_{β_c} < ∞` plus `E|K| < ∞` at every large radius, composed with
  `TriangleAverage.normalized_ballSum_le_two_scale`) is dominated by
  `2^d · 2^d · max ∇_0 1 · (logMajorant C p (r^{1/2}) + r^{-1/2})`.
  Here `d ≥ 1` (`SourceModelData.hd`) is exactly what absorbs `r^{-d/2} ≤ r^{-1/2}` for `r ≥ 1`.
* `exists_logErrorFunction_majorant_cutE1` — an explicit *measurable* log-error majorant `G` with
  `|𝓔_{1,r}| ≤ G r` eventually (`G` is the profile above).
* `lintegral_abs_div_cutE1_lt_top` — `∫⁻_{Ioi R} |𝓔_{1,r}| dr/r < ∞` for some `R > 0`, **with no
  measurability of `𝓔_{1,r}` assumed**: the lintegral is monotone under the measurable majorant.
  This is the strongest form of the I.4.13 conclusion that does not presuppose the radius
  regularity of the cutoff moments.
* `integrableOn_cutE1_abs_div` (a.e.-measurability suffices), `logarithmicallyIntegrable_cutE1`,
  `isLogErrorFunction_cutE1` — under the extra input `Measurable (r ↦ cutE1 M r)`, the defect
  itself is logarithmically integrable, and (with the triangle condition, which supplies
  `∇_0 < ∞` through `nablaSup_le_openTriangleSelf`) a log-error function.  The limit `→ 0` is
  HEAD's `cutE1_tendsto_zero_of_triangleCondition_logBound`.
* `sourceLogErrorFunction_cutE1` — the source-style package `SourceLogErrorFunction`
  (global clause + local clause), with local boundedness as a separate named input.
* `exists_tendsto_intervalIntegral_cutE1_div` — **the source's improper integral converges**:
  there is `r₀ > 0` with `∫_{r₀}^{R} 𝓔_{1,r} dr/r → ∫_{Ioi r₀} 𝓔_{1,r} dr/r` as `R → ∞`
  (`LogTailLocal.tendsto_intervalIntegral_div_id`), which is the faithful reading of the paper's
  `∫^∞ 𝓔_{1,r} dr/r`.
* `cutE1_le_powScale`, `logarithmicallyIntegrable_cutE1_of_powRadialBound`,
  `isLogErrorFunction_cutE1_of_powRadialBound` — Case 2 of `(HD)`: pointwise *polynomial* decay
  `∇_{β_c}(0,y) ⪯ ‖y‖^{-a}` gives the same conclusion (`min (d/2) (a/2)` is the surviving
  exponent).
* `measurable_ball_ncard`, `measurable_cutE1_of_measurable_stats` — the measurability input is
  *exactly* measurability in the radius of the three cutoff statistics: the ball count is
  measurable by monotonicity, and `cE1 A S T b = (b A² - S + T)/(b A²)` is a rational function.
* `aemeasurable_cutMassReal` — `r ↦ χ_r` is a.e. measurable on any tail where it is finite
  (monotonicity + `aemeasurable_restrict_of_monotoneOn`).
* `aemeasurable_cutE1_of_aemeasurable_stats` — **the residual measurability input, isolated
  exactly**: a.e. measurability of `pairMass` and `connMass` in the radius (plus finiteness of the
  mass on the tail, needed only because `ENNReal.toReal ⊤ = 0`) already gives a.e. measurability
  of `𝓔_{1,r}`.  `integrableOn_cutE1_abs_div` therefore takes the weaker hypothesis
  `AEMeasurable (r ↦ 𝓔_{1,r}) (volume.restrict (Ioi 1))`, not global `Measurable`.

## Which input closes which gap (the honest ledger)

1. **Two-scale defect rate** (the shape Lemma I.4.13 consumes): closed by HEAD's
   `cutE1_le_log_rate` under `∇_{β_c} < ∞`, eventual `E_{β_c,r}|K| < ∞`, and the pointwise
   `(I.4.13)` bound.  `cutE1_le_rpowScale` only rewrites it into the source's rescaled form.
2. **A.e. bound / majorant**: closed unconditionally by the rate plus nonnegativity of the defect
   (`cutE1_nonneg_eventually`, Lemma I.4.7's sign half at the truncated law).  The resulting
   majorant is measurable and log-integrable (`exists_logErrorFunction_majorant_cutE1`), which is
   what makes `lintegral_abs_div_cutE1_lt_top` unconditional.
3. **Local integrability** (the extra clause of `LogTailLocal.SourceLogErrorFunction`, not part of
   `LogarithmicallyIntegrable`): reduced to `Measurable` + `BoundedOnPositiveCompacts` by
   `integrableOnPositiveCompacts_of_measurable_bounded`.  Both are genuinely open at HEAD for
   `𝓔_{1,r}`; they are *not* consequences of the pointwise rate.
4. **Measurability of `𝓔_{1,r}`**: reduced to measurability of `pairMass` and `connMass` by
   `measurable_cutE1_of_measurable_stats`.  The mass `χ_r` is monotone in `r`
   (`SourceModelData.cutMassAt_mono`), hence measurable on `(0, ∞)`; the lattice-ball count is
   monotone.  Nothing at HEAD makes the two *cluster-dependent* statistics measurable functions
   of the radius, and this file does not pretend otherwise: it carries the hypothesis explicitly.

## Negative evidence / what is deliberately not claimed

* No global `Measurable` of `cutE1` is derived.  `LogarithmicallyIntegrable` *requires* global
  measurability, so `logarithmicallyIntegrable_cutE1` keeps it as a hypothesis while
  `lintegral_abs_div_cutE1_lt_top` shows the integral bound without any measurability, and
  `integrableOn_cutE1_abs_div` only needs `AEMeasurable` on `(1, ∞)`, which
  `aemeasurable_cutE1_of_aemeasurable_stats` reduces to the two open statistics.
* No local boundedness (hence no local clause) of `cutE1` is derived: at HEAD only the cluster
  mass has `continuousAt_cutMassReal` / `cutMassReal_mono`; `pairMass` and `connMass` have no
  radius continuity or monotonicity theorem.
* The pointwise `(HD)` bound `LogRadialBound` is carried, never derived (this is the open
  convolution estimate I.4.12 / I.4.11 of the source, exactly as at HEAD).
* The finite first cutoff moment is carried as `∀ᶠ r, M.cutMoment 1 r ≠ ⊤`, never inferred from
  criticality, `θ = 0`, finite boxes, or `β = β_c`.
* No two-sided corner derivative, no Russo interchange, and no Schur/square-root statement is
  made or used here: this file is an assembly over HEAD's *proved* defect asymptotics.

## Build

`lake env lean --root . -DwarningAsError=true -DautoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true <path>/CutoffDefectLogIntegrable.lean`
from the campaign root, Lean 4.35.0, current Mathlib manifest, four cores, no package build.
All `#print axioms` at the end of the file report only `propext`, `Classical.choice`,
`Quot.sound`.
-/

module

public import PercLib.CriticalLRP.Analysis.LogScaling
public import PercLib.CriticalLRP.Analysis.LogTailCore
public import PercLib.CriticalLRP.Analysis.Lemma_I_4_13
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffDefect.Limit
public import PercLib.CriticalLRP.Analysis.LogTailLocal.Assembly
public import PercLib.CriticalLRP.Analysis.Cutoff.IntervalAC

/-!
Conditional logarithmic integrability of the actual cutoff defect, with the finite-moment,
HD, measurability, and local-boundedness inputs kept explicit.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Analysis

/-- The logarithmic profile `r ↦ C (log (1+r)) ^ (-p)` is measurable. -/
theorem measurable_logMajorant (C p : ℝ) : Measurable (fun r : ℝ => logMajorant C p r) := by
  unfold logMajorant
  fun_prop

/-- **The logarithmic profile is itself a log-integrable error function** when `p > 1` and
`C ≥ 0`. -/
theorem isLogErrorFunction_logMajorant {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p) :
    IsLogErrorFunction (fun r : ℝ => logMajorant C p r) :=
  isLogErrorFunction_of_le_logMajorant (measurable_logMajorant C p) hC hp
    (fun r hr => logMajorant_nonneg hC (by linarith))
    (fun r _ => le_rfl)

/-- Constant multiples of a log-integrable error function are log-integrable error functions. -/
theorem isLogErrorFunction_const_mul {f : ℝ → ℝ} (hf : IsLogErrorFunction f) (K : ℝ) :
    IsLogErrorFunction (fun r => K * f r) := by
  obtain ⟨⟨hfm, r₀, hr₀, hint⟩, h0⟩ := hf
  refine ⟨⟨hfm.const_mul K, r₀, hr₀, ?_⟩, ?_⟩
  · refine (integrableOn_congr_fun (f := fun r => |K| * (|f r| / r))
      (g := fun r => |K * f r| / r) ?_ measurableSet_Ioi).mp (hint.const_mul |K|)
    intro r hr
    change |K| * (|f r| / r) = |K * f r| / r
    rw [abs_mul, mul_div_assoc]
  · simpa only [mul_zero] using h0.const_mul K

/-- **A power-decay comparison.**  An eventually nonnegative function dominated by
`K r^{-e}` with `e > 0` has a finite logarithmic integral. -/
theorem integrableOn_abs_div_of_eventually_le_rpow_neg {T : ℝ → ℝ}
    (hmeas : Measurable T) {K e : ℝ} (he : 0 < e)
    (hnn : ∀ᶠ r : ℝ in atTop, 0 ≤ T r)
    (hb : ∀ᶠ r : ℝ in atTop, T r ≤ K * r ^ (-e)) :
    ∃ R : ℝ, 0 < R ∧ IntegrableOn (fun r => |T r| / r) (Ioi R) := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (hnn.and hb)
  refine ⟨max R₀ 1, lt_max_of_lt_right one_pos, ?_⟩
  have hmaj : IntegrableOn (fun r => K * (r ^ (-e) / r)) (Ioi 1) :=
    (integrableOn_rpow_neg_div_id he).const_mul K
  refine Integrable.mono' (hmaj.mono_set (Ioi_subset_Ioi (le_max_right R₀ 1))) ?_ ?_
  · exact (hmeas.abs.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr1 : (1 : ℝ) < r := lt_of_le_of_lt (le_max_right R₀ 1) hr
    have hr0 : 0 < r := lt_trans one_pos hr1
    obtain ⟨hnnr, hbr⟩ := hR₀ r (le_of_lt (lt_of_le_of_lt (le_max_left R₀ 1) hr))
    rw [Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos hr0, abs_of_nonneg hnnr]
    calc T r / r ≤ K * r ^ (-e) / r := div_le_div_of_nonneg_right hbr hr0.le
      _ = K * (r ^ (-e) / r) := by ring

/-- **The source's polynomial rescaling `h(r^c) + r^{-c}`.**  If `h` is a logarithmically
integrable error function and `c > 0`, then so is `r ↦ h (r^c) + r^{-c}`. -/
theorem isLogErrorFunction_comp_rpow_add_rpow_neg {h : ℝ → ℝ} (hh : IsLogErrorFunction h)
    {c : ℝ} (hc : 0 < c) :
    IsLogErrorFunction (fun r : ℝ => h (r ^ c) + r ^ (-c)) := by
  have h1 : IsLogErrorFunction (fun r : ℝ => h (1 * r ^ c)) :=
    ⟨logarithmicallyIntegrable_comp_rpow_const_mul h hh.1 hc one_pos, hh.2.comp
      (by simpa using tendsto_rpow_atTop hc)⟩
  have h2 : IsLogErrorFunction (fun r : ℝ => 1 * r ^ (-c)) :=
    isLogErrorFunction_const_rpow_neg (a := c) (r₀ := 1) hc one_pos
  have h := isLogErrorFunction_add h1 h2
  simpa only [one_mul] using h

/-- The `(I.4.13)` two-scale composition point: `logMajorant C p (√r)` is the power rescaling
`h (r^{1/2})` of `h = logMajorant C p`. -/
theorem logMajorant_sqrt_eq_comp_rpow (C p r : ℝ) :
    logMajorant C p (Real.sqrt r) = logMajorant C p (r ^ (1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow]

/-- **The source's rescaled tail profile at the defect's own exponent.**  With `c = 1/2`,
`r ↦ logMajorant C p (√r) + r^{-1/2}` is a logarithmically integrable error function: this is
where `TailLog`'s profile is composed with the two-scale radius `√r`. -/
theorem isLogErrorFunction_logMajorant_sqrt_add {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p) :
    IsLogErrorFunction (fun r : ℝ => logMajorant C p (Real.sqrt r) + r ^ (-(1 / 2 : ℝ))) := by
  have h := isLogErrorFunction_comp_rpow_add_rpow_neg
    (isLogErrorFunction_logMajorant hC hp) (c := 1 / 2) (by norm_num)
  simpa only [logMajorant_sqrt_eq_comp_rpow] using h


/-- **A function eventually dominated by `K (logMajorant C p (r^c) + r^{-c})` is log-integrable.**
This is the comparison step which turns a two-scale `(I.4.13)`-type rate into
`∫_{R}^∞ |T r| dr / r < ∞`.  The local measurability input is `Measurable T`; the
nonnegativity and the bound are needed only eventually. -/
theorem integrableOn_abs_div_of_eventually_le_rpowScale {T : ℝ → ℝ}
    (hmeas : AEMeasurable T (volume.restrict (Ioi 1)))
    {K C p c : ℝ} (hC : 0 ≤ C) (hp : 1 < p) (hc : 0 < c)
    (hnn : ∀ᶠ r : ℝ in atTop, 0 ≤ T r)
    (hb : ∀ᶠ r : ℝ in atTop, T r ≤ K * (logMajorant C p (r ^ c) + r ^ (-c))) :
    ∃ R : ℝ, 0 < R ∧ IntegrableOn (fun r => |T r| / r) (Ioi R) := by
  obtain ⟨hLM, r₁, hr₁, hint₁⟩ :=
    (isLogErrorFunction_comp_rpow_add_rpow_neg (isLogErrorFunction_logMajorant hC hp) hc).1
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (hnn.and hb)
  refine ⟨max (max r₁ 1) R₀, lt_max_of_lt_left (lt_max_of_lt_right one_pos), ?_⟩
  have hmaj : IntegrableOn
      (fun r => K * (|logMajorant C p (r ^ c) + r ^ (-c)| / r)) (Ioi r₁) :=
    hint₁.const_mul K
  refine Integrable.mono' (hmaj.mono_set ?_) ?_ ?_
  · intro x hx
    exact lt_of_le_of_lt (le_max_left r₁ 1)
      (lt_of_le_of_lt (le_max_left (max r₁ 1) R₀) hx)
  · have hR1 : (1 : ℝ) ≤ max (max r₁ 1) R₀ :=
      le_trans (le_max_right r₁ 1) (le_max_left (max r₁ 1) R₀)
    refine ((hmeas.abs.div aemeasurable_id).mono_measure ?_).aestronglyMeasurable
    exact Measure.restrict_mono_set volume (fun x hx => lt_of_le_of_lt hR1 hx)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr1 : (1 : ℝ) < r := lt_of_le_of_lt (le_max_right r₁ 1)
      (lt_of_le_of_lt (le_max_left (max r₁ 1) R₀) hr)
    have hr0 : 0 < r := lt_trans one_pos hr1
    obtain ⟨hnnr, hbr⟩ := hR₀ r (le_of_lt (lt_of_le_of_lt (le_max_right (max r₁ 1) R₀) hr))
    have hLMnn : 0 ≤ logMajorant C p (r ^ c) :=
      logMajorant_nonneg hC (Real.rpow_nonneg hr0.le c)
    have hrp : 0 ≤ r ^ (-c) := Real.rpow_nonneg hr0.le _
    have hsum : |logMajorant C p (r ^ c) + r ^ (-c)| = logMajorant C p (r ^ c) + r ^ (-c) :=
      abs_of_nonneg (add_nonneg hLMnn hrp)
    rw [Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos hr0, abs_of_nonneg hnnr, hsum]
    calc T r / r ≤ K * (logMajorant C p (r ^ c) + r ^ (-c)) / r :=
          div_le_div_of_nonneg_right hbr hr0.le
      _ = K * ((logMajorant C p (r ^ c) + r ^ (-c)) / r) := by ring

end PercLib.CriticalLRP.Analysis

namespace PercLib.CriticalLRP.Analysis

/-- Measurability plus local boundedness gives local integrability on the compacta of
`(0, ∞)`; this is the general form of the local clause used above. -/
theorem integrableOnPositiveCompacts_of_measurable_bounded {f : ℝ → ℝ} (hmeas : Measurable f)
    (hbdd : LogTailLocal.BoundedOnPositiveCompacts f) :
    LogTailLocal.IntegrableOnPositiveCompacts f := by
  intro R1 R2 h1 h2
  obtain ⟨C, hC⟩ := hbdd R1 R2 h1 h2
  exact IntegrableOn.of_bound isCompact_Icc.measure_lt_top hmeas.aestronglyMeasurable C (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs]
    exact hC r hr)

end PercLib.CriticalLRP.Analysis

namespace PercLib.CriticalLRP.CutoffDefect

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.Orchestration.SourceModelData
open PercLib.CriticalLRP.BallAverage
open PercLib.CriticalLRP.Analysis

variable (M : SourceModelData)

/-- Elementary absorption: for `A, a, b, c ≥ 0` with `a ≤ b`,
`A * a + c ≤ max A 1 * (c + b)`. -/
theorem arith_absorb {A a b c : ℝ} (hA0 : 0 ≤ A) (hab : a ≤ b) (hb0 : 0 ≤ b) (hc : 0 ≤ c) :
    A * a + c ≤ max A 1 * (c + b) := by
  have h1 : A * a ≤ A * b := mul_le_mul_of_nonneg_left hab hA0
  have h2 : A * b ≤ max A 1 * b := mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  have h3 : c ≤ max A 1 * c := by
    have : (1 : ℝ) ≤ max A 1 := le_max_right _ _
    nlinarith
  nlinarith [h1, h2, h3]

/-- **The I.4.13 rate in the source's rescaled form.**  The defect bound `cutE1_le_log_rate`
is dominated by `K (logMajorant C p (r^{1/2}) + r^{-1/2})` eventually, with an explicit
constant `K = 2^d · 2^d · max ∇_0 1`.  The exponent `1/2` is exactly `(HD)`'s two-scale
`√r` (paper, (I.4.13)), and `d ≥ 1` is what lets `r^{-d/2}` be absorbed by `r^{-1/2}`. -/
theorem cutE1_le_rpowScale
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C p) :
    ∀ᶠ r : ℝ in atTop, cutE1 M r ≤
      ((2 : ℝ) ^ M.d * (2 : ℝ) ^ M.d *
          max ((nablaSup M (openTriangleNabla M) 0).toReal) 1) *
        (logMajorant C p (r ^ (1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))) := by
  filter_upwards [cutE1_le_log_rate M hT h1 hC (by linarith) hF, eventually_ge_atTop (1 : ℝ)]
    with r hle hr1
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hA0 : 0 ≤ (nablaSup M (openTriangleNabla M) 0).toReal := ENNReal.toReal_nonneg
  have hd : (1 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast M.hd
  have hpow : r ^ (-(M.d : ℝ) / 2) ≤ r ^ (-(1 / 2 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hr1 ?_
    linarith
  have hLM : 0 ≤ logMajorant C p (r ^ (1 / 2 : ℝ)) :=
    logMajorant_nonneg hC (Real.rpow_nonneg hr0.le _)
  have hrp : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hr0.le _
  rw [Real.sqrt_eq_rpow] at hle
  have hstep : (nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2)
      + logMajorant C p (r ^ (1 / 2 : ℝ)) ≤
      max ((nablaSup M (openTriangleNabla M) 0).toReal) 1 *
        (logMajorant C p (r ^ (1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))) := by
    have h := arith_absorb (A := (nablaSup M (openTriangleNabla M) 0).toReal)
      (a := r ^ (-(M.d : ℝ) / 2)) (b := r ^ (-(1 / 2 : ℝ)))
      (c := logMajorant C p (r ^ (1 / 2 : ℝ))) hA0 hpow hrp hLM
    linarith
  calc cutE1 M r
      ≤ (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
          ((nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2)
            + logMajorant C p (r ^ (1 / 2 : ℝ)))) := hle
    _ ≤ (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
          (max ((nablaSup M (openTriangleNabla M) 0).toReal) 1 *
            (logMajorant C p (r ^ (1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        exact hstep
    _ = ((2 : ℝ) ^ M.d * (2 : ℝ) ^ M.d *
          max ((nablaSup M (openTriangleNabla M) 0).toReal) 1) *
        (logMajorant C p (r ^ (1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))) := by ring


/-- **An explicit measurable logarithmic-error majorant for the defect.**  Under the `(I.4.13)`
pointwise logarithmic bound, `|𝓔_{1,r}|` is eventually dominated by the *measurable*
log-integrable error function
`r ↦ 2^d · 2^d · max ∇_0 1 · (logMajorant C p (r^{1/2}) + r^{-1/2})`.

This is the form of the conclusion which needs no measurability of `𝓔_{1,r}` itself: the
majorant is measurable and log-integrable on its own, so `∫⁻ |𝓔_{1,r}| dr/r` is finite by
monotonicity of the lintegral (see `lintegral_abs_div_cutE1_lt_top`). -/
theorem exists_logErrorFunction_majorant_cutE1
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C p) :
    ∃ G : ℝ → ℝ, Analysis.IsLogErrorFunction G ∧ (∀ᶠ r : ℝ in atTop, 0 ≤ G r) ∧
      ∀ᶠ r : ℝ in atTop, |cutE1 M r| ≤ G r := by
  have hbase : Analysis.IsLogErrorFunction
      (fun r : ℝ => logMajorant C p (r ^ (1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))) :=
    Analysis.isLogErrorFunction_comp_rpow_add_rpow_neg
      (Analysis.isLogErrorFunction_logMajorant hC hp) (by norm_num)
  refine ⟨fun r : ℝ => ((2 : ℝ) ^ M.d * (2 : ℝ) ^ M.d *
      max ((nablaSup M (openTriangleNabla M) 0).toReal) 1) *
        (logMajorant C p (r ^ (1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))),
    Analysis.isLogErrorFunction_const_mul hbase _, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    have hK0 : (0 : ℝ) ≤ (2 : ℝ) ^ M.d * (2 : ℝ) ^ M.d *
        max ((nablaSup M (openTriangleNabla M) 0).toReal) 1 :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (le_trans zero_le_one (le_max_right _ _))
    have hLM : 0 ≤ logMajorant C p (r ^ (1 / 2 : ℝ)) :=
      logMajorant_nonneg hC (Real.rpow_nonneg hr0.le _)
    have hrp : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hr0.le _
    exact mul_nonneg hK0 (add_nonneg hLM hrp)
  · filter_upwards [cutE1_le_rpowScale M hT h1 hC hp hF, cutE1_nonneg_eventually M h1]
      with r hle hnn
    rw [abs_of_nonneg hnn]
    exact hle

/-- **The logarithmic lintegral of the defect is finite, with no measurability input.**
`∫⁻_{Ioi R} |𝓔_{1,r}| dr/r < ∞` for a radius `R` past the eventual regime: the measurable
majorant of `exists_logErrorFunction_majorant_cutE1` is log-integrable, and the lintegral is
monotone.  This is the strongest form of the I.4.13 conclusion which does not presuppose
measurability of the defect in the radius. -/
theorem lintegral_abs_div_cutE1_lt_top
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C p) :
    ∃ R : ℝ, 0 < R ∧ ∫⁻ r in Ioi R, ENNReal.ofReal (|cutE1 M r| / r) < ⊤ := by
  obtain ⟨G, hG, hGnn, hdom⟩ := exists_logErrorFunction_majorant_cutE1 M hT h1 hC hp hF
  obtain ⟨hGmeas, r₀, hr₀, hGint⟩ := hG.1
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 hGnn
  obtain ⟨R₂, hR₂⟩ := eventually_atTop.1 hdom
  set R : ℝ := max (max r₀ R₁) (max 1 R₂) with hRdef
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left 1 R₂) (le_max_right _ _)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRr₀ : r₀ ≤ R := le_trans (le_max_left r₀ R₁) (le_max_left _ _)
  have hRR₁ : R₁ ≤ R := le_trans (le_max_right r₀ R₁) (le_max_left _ _)
  have hRR₂ : R₂ ≤ R := le_trans (le_max_right 1 R₂) (le_max_right _ _)
  refine ⟨R, hR0, ?_⟩
  have hInt : IntegrableOn (fun r => G r / r) (Ioi R) := by
    have h : IntegrableOn (fun r => |G r| / r) (Ioi R) :=
      hGint.mono_set (fun x hx => lt_of_le_of_lt hRr₀ hx)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := lt_trans hR0 hr
    change |G r| / r = G r / r
    rw [abs_of_nonneg (hR₁ r (le_of_lt (lt_of_le_of_lt hRR₁ hr)))]
  have hmono : ∫⁻ r in Ioi R, ENNReal.ofReal (|cutE1 M r| / r) ≤
      ∫⁻ r in Ioi R, ENNReal.ofReal (G r / r) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans hR0 hr
    exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (hR₂ r (le_of_lt (lt_of_le_of_lt hRR₂ hr))) hr0.le)
  have hnn : ∀ᵐ r ∂(volume.restrict (Ioi R)), 0 ≤ G r / r :=
    (ae_restrict_mem measurableSet_Ioi).mono fun r hr =>
      div_nonneg (hR₁ r (le_of_lt (lt_of_le_of_lt hRR₁ hr))) (le_of_lt (lt_trans hR0 hr))
  have hEq := ofReal_integral_eq_lintegral_ofReal hInt hnn
  refine lt_of_le_of_lt hmono ?_
  rw [← hEq]
  exact ENNReal.ofReal_lt_top

/-- **The tail logarithmic integral of the defect is finite.**  Under the `(I.4.13)` pointwise
logarithmic bound on the uncut open triangle, the signed two-scale rate
`cutE1_le_log_rate` places `𝓔_{1,r}` between `0` and `K (logMajorant C p (r^{1/2}) + r^{-1/2})`,
whose logarithmic integral converges; hence `r ↦ |𝓔_{1,r}| / r` is integrable near `∞`.

The measurability of `r ↦ 𝓔_{1,r}` is a separate input (`hmeas`), not derived here: at HEAD the
cut-off moments `E1Sign.pairMass` and `E1Sign.connMass` are not known to be measurable in the
radius.  See `cutE1_abs_div_integrableOn_iff` and the file header for the exact decomposition. -/
theorem integrableOn_cutE1_abs_div
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C p)
    (hmeas : AEMeasurable (fun r => cutE1 M r) (volume.restrict (Ioi 1))) :
    ∃ R : ℝ, 0 < R ∧ IntegrableOn (fun r => |cutE1 M r| / r) (Ioi R) :=
  Analysis.integrableOn_abs_div_of_eventually_le_rpowScale hmeas
    (K := (2 : ℝ) ^ M.d * (2 : ℝ) ^ M.d *
      max ((nablaSup M (openTriangleNabla M) 0).toReal) 1)
    (C := C) (p := p) (c := 1 / 2) hC hp (by norm_num)
    (cutE1_nonneg_eventually M h1) (cutE1_le_rpowScale M hT h1 hC hp hF)

/-- **`𝓔_{1,r}` is logarithmically integrable** (paper, p. 26): its logarithmic density
`r ↦ |𝓔_{1,r}| / r` is integrable on a tail of `(0, ∞)`. -/
theorem logarithmicallyIntegrable_cutE1
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C p)
    (hmeas : Measurable (fun r => cutE1 M r)) :
    Analysis.LogarithmicallyIntegrable (fun r => cutE1 M r) :=
  ⟨hmeas, integrableOn_cutE1_abs_div M hT h1 hC hp hF hmeas.aemeasurable⟩

/-- The `LogRadialBound` hypothesis in the `M.S.dist 0 ·` normalisation used by the accepted
Lemma I.4.3 packet, converted to the `M.S.ρ ∘ toVec` normalisation of `BallAverage`. -/
theorem logRadialBound_rho_of_dist {C p : ℝ}
    (hF : LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    LogRadialBound (fun x : M.V => M.S.ρ (toVec x)) (openTriangleNabla M) C p := by
  intro y hy
  rw [openTriangleNabla_eq_openTriangle M y]
  have hy' : 0 < M.S.dist 0 y := by rwa [dist_zero_eq]
  have h := hF y hy'
  simpa only [dist_zero_eq] using h

/-- **`𝓔_{1,r}` is a logarithmically integrable error function at the actual cut law.**

Inputs: the triangle condition `∇_{β_c} < ∞` (which gives the finite constant `∇_0 < ∞`), the
eventual finiteness of the first cutoff moment, the `(HD)` Case 3 pointwise logarithmic bound
`∇_{β_c}(0,y) ⪯ (log (1+‖y‖))^{-p}` with `p > 1`, and measurability of the defect in the radius.
All of them are explicit; none is derived here. -/
theorem isLogErrorFunction_cutE1
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg
      M.betaCrit 0 < ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p)
    (hmeas : Measurable (fun r => cutE1 M r)) :
    Analysis.IsLogErrorFunction (fun r => cutE1 M r) := by
  have hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤ :=
    ne_top_of_le_ne_top hTri.ne (nablaSup_le_openTriangleSelf M)
  exact ⟨logarithmicallyIntegrable_cutE1 M hT h1 hC hp (logRadialBound_rho_of_dist M hF) hmeas,
    cutE1_tendsto_zero_of_triangleCondition_logBound M hTri h1 hC hp hF⟩

/-- **The source's improper logarithmic integral of the defect converges.**  This is the faithful
reading of the paper's `∫^{∞} 𝓔_{1,r} dr / r`: every interval integral `∫_{r₀}^{R} 𝓔_{1,r} dr/r`
exists and converges, as `R → ∞`, to the finite integral over `Ioi r₀`.

`LogTailLocal.tendsto_intervalIntegral_div_id` supplies the identification of the improper
integral with the limit of the interval integrals; the only inputs are measurability and the
global logarithmic-integrability clause proved above. -/
theorem exists_tendsto_intervalIntegral_cutE1_div
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg
      M.betaCrit 0 < ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p)
    (hmeas : Measurable (fun r => cutE1 M r)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      Tendsto (fun R => ∫ r in r₀..R, cutE1 M r / r) atTop
        (𝓝 (∫ r in Ioi r₀, cutE1 M r / r)) := by
  obtain ⟨hm, r₀, hr₀, habs⟩ :=
    isLogErrorFunction_cutE1 M hTri h1 hC hp hF hmeas |>.1
  exact ⟨r₀, hr₀, Analysis.LogTailLocal.tendsto_intervalIntegral_div_id hm hr₀ habs⟩

/-- **The residual gap of the local clause, isolated.**  Local integrability of the defect on the
compacta of `(0, ∞)` follows from measurability together with local boundedness.  Boundedness is
*not* free: at HEAD it is available for the cut-off cluster mass
(`LogTailLocal.boundedOnPositiveCompacts_toReal_of_antitone`, from `cutMassAt_mono`) but not for
the two cluster-dependent statistics `E1Sign.pairMass`, `E1Sign.connMass`. -/
theorem sourceLogErrorFunction_cutE1
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg
      M.betaCrit 0 < ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p)
    (hmeas : Measurable (fun r => cutE1 M r))
    (hbdd : Analysis.LogTailLocal.BoundedOnPositiveCompacts (fun r => cutE1 M r)) :
    Analysis.LogTailLocal.SourceLogErrorFunction (fun r => cutE1 M r) :=
  ⟨isLogErrorFunction_cutE1 M hTri h1 hC hp hF hmeas,
   Analysis.integrableOnPositiveCompacts_of_measurable_bounded hmeas hbdd⟩

/-! ## Case 2 of `(HD)`: polynomial decay of the uncut open triangle

The same assembly with the `(I.4.11)` power majorant.  Nothing here is a consequence of the
logarithmic case: the hypothesis `PowRadialBound` is independent, and the conclusion is the same
log-integrability of the defect.  This is the second branch of the source's dichotomy. -/

/-- **The defect bound in power form.**  From `cutE1_le_pow_rate`, using
`powMajorant C a (√r) = C r^{-a/2}` and `r^{-d/2} ≤ r^{-min (d/2) (a/2)}`,
`r^{-a/2} ≤ r^{-min (d/2) (a/2)}` for `r ≥ 1`. -/
theorem cutE1_le_powScale
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hF : PowRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C a) :
    ∀ᶠ r : ℝ in atTop, cutE1 M r ≤
      ((2 : ℝ) ^ M.d * (2 : ℝ) ^ M.d *
          (((nablaSup M (openTriangleNabla M) 0).toReal) + C)) *
        r ^ (-(min ((M.d : ℝ) / 2) (a / 2))) := by
  filter_upwards [cutE1_le_pow_rate M hT h1 hC ha hF, eventually_ge_atTop (1 : ℝ)]
    with r hle hr1
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hA0 : 0 ≤ (nablaSup M (openTriangleNabla M) 0).toReal := ENNReal.toReal_nonneg
  have hd : (1 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast M.hd
  have hpm : powMajorant C a (Real.sqrt r) = C * r ^ (-a / 2) := by
    rw [powMajorant, Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le]
    ring_nf
  rw [hpm] at hle
  have hexp : 0 < min ((M.d : ℝ) / 2) (a / 2) :=
    lt_min (by linarith) (by linarith)
  have he1 : r ^ (-(M.d : ℝ) / 2) ≤ r ^ (-(min ((M.d : ℝ) / 2) (a / 2))) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith [min_le_left ((M.d : ℝ) / 2) (a / 2)])
  have he2 : r ^ (-a / 2) ≤ r ^ (-(min ((M.d : ℝ) / 2) (a / 2))) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith [min_le_right ((M.d : ℝ) / 2) (a / 2)])
  have hE : 0 ≤ r ^ (-(min ((M.d : ℝ) / 2) (a / 2))) := Real.rpow_nonneg hr0.le _
  have hstep : (nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2)
      + C * r ^ (-a / 2) ≤
      (((nablaSup M (openTriangleNabla M) 0).toReal) + C) *
        r ^ (-(min ((M.d : ℝ) / 2) (a / 2))) := by
    have h1' : (nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2) ≤
        (nablaSup M (openTriangleNabla M) 0).toReal *
          r ^ (-(min ((M.d : ℝ) / 2) (a / 2))) :=
      mul_le_mul_of_nonneg_left he1 hA0
    have h2' : C * r ^ (-a / 2) ≤ C * r ^ (-(min ((M.d : ℝ) / 2) (a / 2))) :=
      mul_le_mul_of_nonneg_left he2 hC
    nlinarith [h1', h2']
  calc cutE1 M r
      ≤ (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
          ((nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2)
            + C * r ^ (-a / 2))) := hle
    _ ≤ (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
          ((((nablaSup M (openTriangleNabla M) 0).toReal) + C) *
            r ^ (-(min ((M.d : ℝ) / 2) (a / 2))))) := by
        have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ M.d := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep h2d) h2d
    _ = ((2 : ℝ) ^ M.d * (2 : ℝ) ^ M.d *
          (((nablaSup M (openTriangleNabla M) 0).toReal) + C)) *
        r ^ (-(min ((M.d : ℝ) / 2) (a / 2))) := by ring

/-- **Case 2 of `(HD)`: polynomial decay gives log-integrability of the defect.** -/
theorem logarithmicallyIntegrable_cutE1_of_powRadialBound
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hF : PowRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C a)
    (hmeas : Measurable (fun r => cutE1 M r)) :
    Analysis.LogarithmicallyIntegrable (fun r => cutE1 M r) := by
  have hd : (1 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast M.hd
  have hexp : 0 < min ((M.d : ℝ) / 2) (a / 2) := lt_min (by linarith) (by linarith)
  exact ⟨hmeas, Analysis.integrableOn_abs_div_of_eventually_le_rpow_neg hmeas hexp
    (cutE1_nonneg_eventually M h1) (cutE1_le_powScale M hT h1 hC ha hF)⟩

/-- **Case 2 of `(HD)`: polynomial decay gives a log-error function.** -/
theorem isLogErrorFunction_cutE1_of_powRadialBound
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hF : PowRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C a)
    (hmeas : Measurable (fun r => cutE1 M r)) :
    Analysis.IsLogErrorFunction (fun r => cutE1 M r) :=
  ⟨logarithmicallyIntegrable_cutE1_of_powRadialBound M hT h1 hC ha hF hmeas,
    cutE1_tendsto_zero_of_powRadialBound M hT h1 hC ha hF⟩

/-! ## Where the measurability input comes from

The theorems above carry `Measurable (fun r => cutE1 M r)` as a hypothesis because at HEAD the two
cluster-dependent statistics `E1Sign.pairMass` and `E1Sign.connMass` are not known to be
measurable functions of the cut-off radius.  The next two lemmas pin down exactly what is missing:
the lattice-ball count is measurable by monotonicity, and the defect is a rational function of
the three statistics, so measurability of the defect is *exactly* measurability of the three
statistics. -/

/-- The lattice-ball count `r ↦ |B_r|` is measurable (it is monotone in the radius). -/
theorem measurable_ball_ncard :
    Measurable fun r : ℝ => ((M.ball r).ncard : ℝ) := by
  have hmono : Monotone fun r : ℝ => ((M.ball r).ncard : ℝ) := by
    intro r r' hrr'
    have hsub : M.ball r ⊆ M.ball r' := fun y hy => le_trans hy hrr'
    have hle : (M.ball r).ncard ≤ (M.ball r').ncard :=
      Set.ncard_le_ncard hsub (ball_finite M r')
    change ((M.ball r).ncard : ℝ) ≤ ((M.ball r').ncard : ℝ)
    exact_mod_cast hle
  exact hmono.measurable

/-- **Measurability of the defect reduces to measurability of its three statistics.**  This is
`cE1 A S T b = (b A² - S + T)/(b A²)` with `A = χ_r`, `S`, `T` the cutoff statistics; no
regularity of the radius dependence is smuggled in beyond the three measurability hypotheses. -/
theorem measurable_cutE1_of_measurable_stats
    (hmass : Measurable fun r : ℝ => (M.cutMassAt r 0).toReal)
    (hpair : Measurable fun r : ℝ =>
      (PercLib.CriticalLRP.E1Sign.pairMass M r).toReal)
    (hconn : Measurable fun r : ℝ =>
      (PercLib.CriticalLRP.E1Sign.connMass M r).toReal) :
    Measurable fun r : ℝ => cutE1 M r := by
  have hcard := measurable_ball_ncard M
  unfold cutE1 PercLib.CriticalLRP.VolumeMoments.cE1
  measurability

/-- **The cut-off mass is a.e. measurable in the radius on any tail where it is finite.**
`r ↦ (M.cutMassAt r 0).toReal` is monotone there (`SourceModelData.cutMassAt_mono`), and a
monotone function is a.e. measurable on its interval of monotonicity
(`aemeasurable_restrict_of_monotoneOn`).  The finiteness hypothesis is not cosmetic:
`ENNReal.toReal` sends `⊤` to `0`, so a jump to `⊤` destroys monotonicity of the real value. -/
theorem aemeasurable_cutMassReal (hfin : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) :
    AEMeasurable (fun r : ℝ => (M.cutMassAt r 0).toReal) (volume.restrict (Ioi 1)) := by
  refine aemeasurable_restrict_of_monotoneOn measurableSet_Ioi ?_
  intro r hr r' hr' hrr'
  exact ENNReal.toReal_mono (hfin r' (le_of_lt hr'))
    (M.cutMassAt_mono (lt_trans one_pos hr) (lt_trans one_pos hr') hrr')

/-- **The residual measurability input for the defect, isolated exactly.**  Given a.e.
measurability in the radius of the two cluster statistics `pairMass` and `connMass` (and
finiteness of the mass on the tail, needed only to make `toReal` monotone), the defect is a.e.
measurable on `(1, ∞)`.  The mass and the ball count are free: the first by monotonicity, the
second because `r ↦ |B_r|` is monotone. -/
theorem aemeasurable_cutE1_of_aemeasurable_stats
    (hfin : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hpair : AEMeasurable (fun r : ℝ =>
      (PercLib.CriticalLRP.E1Sign.pairMass M r).toReal) (volume.restrict (Ioi 1)))
    (hconn : AEMeasurable (fun r : ℝ =>
      (PercLib.CriticalLRP.E1Sign.connMass M r).toReal) (volume.restrict (Ioi 1))) :
    AEMeasurable (fun r : ℝ => cutE1 M r) (volume.restrict (Ioi 1)) := by
  have hmass := aemeasurable_cutMassReal M hfin
  have hcard : AEMeasurable (fun r : ℝ => ((M.ball r).ncard : ℝ))
      (volume.restrict (Ioi 1)) := (measurable_ball_ncard M).aemeasurable
  have hA2 : AEMeasurable (fun r : ℝ => (M.cutMassAt r 0).toReal ^ 2)
      (volume.restrict (Ioi 1)) := by
    have h := hmass.mul hmass
    refine h.congr ?_
    filter_upwards with r
    simp [pow_two]
  have hden : AEMeasurable (fun r : ℝ =>
      ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2)
      (volume.restrict (Ioi 1)) := hcard.mul hA2
  have hnum : AEMeasurable (fun r : ℝ =>
      ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2
        - (PercLib.CriticalLRP.E1Sign.pairMass M r).toReal
        + (PercLib.CriticalLRP.E1Sign.connMass M r).toReal) (volume.restrict (Ioi 1)) :=
    (hden.sub hpair).add hconn
  unfold cutE1 PercLib.CriticalLRP.VolumeMoments.cE1
  have hkey : (fun r : ℝ => (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2
        - (PercLib.CriticalLRP.E1Sign.pairMass M r).toReal
        + (PercLib.CriticalLRP.E1Sign.connMass M r).toReal) /
      (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2))
      = (fun r : ℝ => ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2
          - (PercLib.CriticalLRP.E1Sign.pairMass M r).toReal
          + (PercLib.CriticalLRP.E1Sign.connMass M r).toReal) /
        (fun r : ℝ => ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2) := rfl
  rw [hkey]
  exact hnum.div hden

end PercLib.CriticalLRP.CutoffDefect

/-! ## Axiom audit (campaign protocol: one line per new theorem) -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Analysis.measurable_logMajorant
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_logMajorant
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_const_mul
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_comp_rpow_add_rpow_neg
#print axioms PercLib.CriticalLRP.Analysis.logMajorant_sqrt_eq_comp_rpow
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_logMajorant_sqrt_add
#print axioms PercLib.CriticalLRP.Analysis.integrableOn_abs_div_of_eventually_le_rpowScale
#print axioms PercLib.CriticalLRP.Analysis.integrableOn_abs_div_of_eventually_le_rpow_neg
#print axioms PercLib.CriticalLRP.Analysis.integrableOnPositiveCompacts_of_measurable_bounded
#print axioms PercLib.CriticalLRP.CutoffDefect.arith_absorb
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_le_rpowScale
#print axioms PercLib.CriticalLRP.CutoffDefect.exists_logErrorFunction_majorant_cutE1
#print axioms PercLib.CriticalLRP.CutoffDefect.lintegral_abs_div_cutE1_lt_top
#print axioms PercLib.CriticalLRP.CutoffDefect.integrableOn_cutE1_abs_div
#print axioms PercLib.CriticalLRP.CutoffDefect.logarithmicallyIntegrable_cutE1
#print axioms PercLib.CriticalLRP.CutoffDefect.logRadialBound_rho_of_dist
#print axioms PercLib.CriticalLRP.CutoffDefect.isLogErrorFunction_cutE1
#print axioms PercLib.CriticalLRP.CutoffDefect.exists_tendsto_intervalIntegral_cutE1_div
#print axioms PercLib.CriticalLRP.CutoffDefect.sourceLogErrorFunction_cutE1
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_le_powScale
#print axioms PercLib.CriticalLRP.CutoffDefect.logarithmicallyIntegrable_cutE1_of_powRadialBound
#print axioms PercLib.CriticalLRP.CutoffDefect.isLogErrorFunction_cutE1_of_powRadialBound
#print axioms PercLib.CriticalLRP.CutoffDefect.measurable_ball_ncard
#print axioms PercLib.CriticalLRP.CutoffDefect.measurable_cutE1_of_measurable_stats
#print axioms PercLib.CriticalLRP.CutoffDefect.aemeasurable_cutMassReal
#print axioms PercLib.CriticalLRP.CutoffDefect.aemeasurable_cutE1_of_aemeasurable_stats
