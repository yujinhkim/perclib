/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Campaign `smwttizjk`, member `m5`, direction D7B.

# The cutoff defect `𝓔_{1,r}` vanishes: signed two-sided limit at the truncated law

Paper anchor: Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1),
§I.4.1–I.4.2, Lemmas I.4.7 and I.4.11, and the Case 2 / Case 3 analysis of `(HD)` that
produces `∇_r → 0` ((I.4.11), (I.4.13)).

`TriangleAverage.defect_upper_tendsto_zero_of_tail` proves the *uncut* defect vanishes, and
its docstring says the signed statement `0 ≤ 𝓔_{1,r}` is not available at the uncut law
because the comparison layer has no sign.  At the **truncated** law the sign *is* available:
`E1Sign.cE1_nonneg` (Lemma I.4.7), with the finite second cutoff moment replaced by the
finite first moment via `E1Sign.cutMoment_two_ne_top_of_one`.

What is proved here, all at `M.cutLaw` (Definition I.1.5 of the source):

* `cutE1_le_normalized_ballSum` — `𝓔_{1,r} ≤ 2^d · |B_r|⁻¹ Σ_{x∈B_r} ∇_β_c(0,x)` eventually;
* `cutE1_le_two_scale` — the quantitative rate `𝓔_{1,r} ⪯ ∇_0 r^{-d/2} + ∇_{√r}`
  (the shape Lemma I.4.13 consumes), from `E1Sign.cE1_le_windowOpenTriangle` and
  `TriangleAverage.normalized_ballSum_le_two_scale`;
* `cutE1_mem_Ioo_eventually` — the signed two-sided statement
  `-ε < 𝓔_{1,r} < ε` eventually, from the sign plus the upper bound;
* `cutE1_tendsto_zero_of_tail` — `𝓔_{1,r} → 0` given `∇_r → 0`;
* `cutE1_tendsto_zero_of_logRadialBound` / `_of_powRadialBound` — the same with the tail
  hypothesis replaced by the pointwise decay `∇(0,x) ⪯ (log (1+‖x‖))^{-p}` (`p > 0`) resp.
  `⪯ ‖x‖^{-a}` (`a > 0`) of (I.4.13) / (I.4.11);
* `cutE1_tendsto_zero_of_summable` — the Cesàro (Case 2) route, which needs no decay rate at
  all but needs `Σ_x ∇(0,x) < ∞` (incompatible with `χ(β_c) = ∞`, see
  `TriangleAverage.suscept_le_triMass`; kept as an explicit hypothesis).

Residual premises, unchanged from HEAD: the finite first cutoff moment
`M.cutMoment 1 r ≠ ⊤` for all large `r`, and the finite triangle constant `∇_0 < ∞`.  They
are *not* derived here.  The tail decay `∇_r → 0` *is* derived, from the pointwise `(HD)`
output.
-/
module

public import PercLib.CriticalLRP.Analysis.TriangleAverage
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect.Triangle
public import PercLib.CriticalLRP.Analysis.OpenTriangleLogTail
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffDefect.Defs

/-! # Signed two-sided cutoff-defect vanishing under explicit analytic premises -/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.CutoffDefect

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.Orchestration.SourceModelData
open PercLib.CriticalLRP.BallAverage
open PercLib.CriticalLRP.TriangleAverage
open PercLib.CriticalLRP.Analysis

variable (M : SourceModelData)

/-! ## The windowed uncut triangle sum is finite from `∇_0 < ∞` -/

/-- Finiteness of the lattice-ball sum `Σ_{x∈B_r} ∇_{β_c}(0,x)` under the triangle
condition in sup form.  This discharges the `hN` hypothesis of
`E1Sign.cE1_le_ballSum_openTriangle`. -/
theorem ballSum_openTriangleNabla_ne_top
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤) (r : ℝ) :
    ballSum M (openTriangleNabla M) r ≠ ⊤ := by
  rw [← ballSum_finset M (openTriangleNabla M) r]
  exact sum_nabla_ne_top M hT r

/-- The tail supremum is bounded by the total triangle mass. -/
theorem nablaSup_le_tsum (f : M.V → ℝ≥0∞) (r : ℝ) :
    nablaSup M f r ≤ ∑' x : M.V, f x := by
  refine iSup_le fun x => iSup_le fun _ => ?_
  exact ENNReal.le_tsum (f := f) x

/-! ## The defect bound and its normalized form -/

/-- **The truncated-law defect against the exact lattice-ball ratio** at one radius:
`𝓔_{1,r} ≤ (|B_r|⁻¹ Σ_{x∈B_r} ∇_{β_c}(0,x)) = (Σ/r^d) · (r^d/|B_r|)`.

This is `E1Sign.cE1_le_ballSum_openTriangle` (Lemma I.4.11 at the truncated law under a finite
first cutoff moment, with the finiteness of the windowed triangle sum discharged from
`∇_0 < ∞`) with `TriangleAverage.ballSum_div_ncard_eq` applied.  No use of `r^d/|B_r| ≤ 2^d`
is made, so the statement is honest at every `r > 0`. -/
theorem cutE1_le_ratio (r : ℝ) (hr : 0 < r)
    (h1 : M.cutMoment 1 r ≠ ⊤)
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤) :
    cutE1 M r ≤ ((ballSum M (openTriangleNabla M) r).toReal / r ^ M.d) *
      (r ^ M.d / ((M.ball r).ncard : ℝ)) := by
  have hnc : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    have hne := ballFinset_nonempty M hr.le
    have hc : 0 < (ballFinset M r).card := Finset.card_pos.mpr hne
    rw [ballFinset_card] at hc
    exact_mod_cast hc
  have hb := PercLib.CriticalLRP.E1Sign.cE1_le_ballSum_openTriangle M r hr.le h1
    (ballSum_openTriangleNabla_ne_top M hT r)
  calc cutE1 M r
      ≤ ((M.ball r).ncard : ℝ)⁻¹ * (ballSum M (openTriangleNabla M) r).toReal := hb
    _ = (ballSum M (openTriangleNabla M) r).toReal / ((M.ball r).ncard : ℝ) := by
        rw [div_eq_inv_mul, mul_comm]
    _ = ((ballSum M (openTriangleNabla M) r).toReal / r ^ M.d) *
          (r ^ M.d / ((M.ball r).ncard : ℝ)) := ballSum_div_ncard_eq M _ hr hnc

/-- **The truncated-law defect is at most the normalized ball sum of the uncut open
triangle, up to the lattice-ball ratio `2^d`.**

`𝓔_{1,r} ≤ 2^d · |B_r|⁻¹ Σ_{x∈B_r} ∇_{β_c}(0,x)` eventually, from `cutE1_le_ratio` and
`TriangleAverage.eventually_pow_div_ncard_le`. -/
theorem cutE1_le_normalized_ballSum
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, cutE1 M r ≤
      (2 : ℝ) ^ M.d * ((ballSum M (openTriangleNabla M) r).toReal / r ^ M.d) := by
  filter_upwards [eventually_pow_div_ncard_le M, eventually_gt_atTop (0 : ℝ), h1]
    with r hrat h0 h1r
  have hnonneg : 0 ≤ (ballSum M (openTriangleNabla M) r).toReal / r ^ M.d :=
    div_nonneg ENNReal.toReal_nonneg (pow_nonneg h0.le M.d)
  calc cutE1 M r
      ≤ ((ballSum M (openTriangleNabla M) r).toReal / r ^ M.d) *
          (r ^ M.d / ((M.ball r).ncard : ℝ)) := cutE1_le_ratio M r h0 h1r hT
    _ ≤ ((ballSum M (openTriangleNabla M) r).toReal / r ^ M.d) * (2 : ℝ) ^ M.d :=
        mul_le_mul_of_nonneg_left hrat hnonneg
    _ = (2 : ℝ) ^ M.d * ((ballSum M (openTriangleNabla M) r).toReal / r ^ M.d) := by ring

/-- **The sandwich of Lemma I.4.7/I.4.11 at the truncated law, `hN` discharged.**

`0 ≤ 𝓔_{1,r} ≤ |B_r|⁻¹ Σ_{x∈B_r} ∇_{β_c}(0,x)` at every `r ≥ 0`, with the only inputs a
finite first cutoff moment at `r` and the finite triangle constant `∇_0 < ∞`.  (At HEAD the
same statement carries an extra hypothesis `BallAverage.ballSum M (…) r ≠ ⊤`; here it is
derived.) -/
theorem cutE1_mem_Icc_ballSum (r : ℝ) (hr : 0 ≤ r)
    (h1 : M.cutMoment 1 r ≠ ⊤)
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤) :
    0 ≤ cutE1 M r ∧ cutE1 M r ≤
      ((M.ball r).ncard : ℝ)⁻¹ * (ballSum M (openTriangleNabla M) r).toReal :=
  PercLib.CriticalLRP.E1Sign.cE1_mem_Icc_ballSum_openTriangle M r hr h1
    (ballSum_openTriangleNabla_ne_top M hT r)

/-- **The rate form of the defect bound**: `𝓔_{1,r} ⪯ ∇_0 r^{-d/2} + ∇_{√r}` eventually.

This is the truncated-law analogue of `TriangleAverage.defect_le_two_scale`, and the shape
Lemma I.4.13 consumes for logarithmic integrability of the error: it carries the rate, not
only the limit.  Inputs: `∇_0 < ∞` (triangle condition in sup form) and the first cutoff
moment eventually finite; `∇_{√r}` is the actual tail along the lattice balls. -/
theorem cutE1_le_two_scale
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, cutE1 M r ≤
      (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
        ((nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2) +
          (nablaSup M (openTriangleNabla M) (Real.sqrt r)).toReal)) := by
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ M.d := by positivity
  filter_upwards [cutE1_le_normalized_ballSum M hT h1,
    normalized_ballSum_le_two_scale M (openTriangleNabla M) hT] with r hle h2s
  calc cutE1 M r
      ≤ (2 : ℝ) ^ M.d * ((ballSum M (openTriangleNabla M) r).toReal / r ^ M.d) := hle
    _ ≤ (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
          ((nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2)) +
            (2 : ℝ) ^ M.d * (nablaSup M (openTriangleNabla M) (Real.sqrt r)).toReal) :=
        mul_le_mul_of_nonneg_left h2s h2d
    _ = (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
        ((nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2) +
          (nablaSup M (openTriangleNabla M) (Real.sqrt r)).toReal)) := by ring

/-! ## Nonnegativity (Lemma I.4.7) with a first-moment premise -/

/-- **`𝓔_{1,r} ≥ 0` eventually**, from the first cutoff moment alone.

`E1Sign.cE1_nonneg` (Lemma I.4.7's sign half) needs a finite second cutoff moment; at the
actual truncated law that follows from the first moment by
`E1Sign.cutMoment_two_ne_top_of_one`. -/
theorem cutE1_nonneg_eventually
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, 0 ≤ cutE1 M r :=
  h1.mono fun r hr =>
    PercLib.CriticalLRP.E1Sign.cE1_nonneg M r
      (PercLib.CriticalLRP.E1Sign.cutMoment_two_ne_top_of_one M r hr)

/-! ## The signed two-sided limit -/

/-- **`𝓔_{1,r} → 0`.**  The truncated-law defect vanishes along the lattice balls.

Squeeze between `0` (`cutE1_nonneg_eventually`) and
`2^d |B_r|⁻¹ Σ_{x∈B_r} ∇_{β_c}(0,x)` (`cutE1_le_normalized_ballSum`), the latter tending to
`0` by `TriangleAverage.tendsto_normalized_ballSum_toReal` under `∇_r → 0`.  Note the
conclusion is two-sided: the sign is a theorem here, not an assumption. -/
theorem cutE1_tendsto_zero_of_tail
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    (htail : Tendsto (fun r => nablaSup M (openTriangleNabla M) r) atTop (𝓝 0)) :
    Tendsto (fun r => cutE1 M r) atTop (𝓝 0) := by
  have hball := tendsto_normalized_ballSum_toReal M (openTriangleNabla M) hT htail
  have hup : Tendsto (fun r : ℝ => (2 : ℝ) ^ M.d *
      ((ballSum M (openTriangleNabla M) r).toReal / r ^ M.d)) atTop (𝓝 0) := by
    have hc := hball.const_mul ((2 : ℝ) ^ M.d)
    simpa using hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (cutE1_nonneg_eventually M h1) (cutE1_le_normalized_ballSum M hT h1)

/-- The absolute value of the defect vanishes. -/
theorem cutE1_abs_tendsto_zero_of_tail
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    (htail : Tendsto (fun r => nablaSup M (openTriangleNabla M) r) atTop (𝓝 0)) :
    Tendsto (fun r => |cutE1 M r|) atTop (𝓝 0) := by
  have h := cutE1_tendsto_zero_of_tail M hT h1 htail
  simpa using h.abs

/-- **The signed two-sided interval form**: `-ε < 𝓔_{1,r} < ε` eventually, for every `ε > 0`.
This is the exact hypothesis shape consumed by the error-transfer steps of §I.4.2. -/
theorem cutE1_mem_Ioo_eventually
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    (htail : Tendsto (fun r => nablaSup M (openTriangleNabla M) r) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, cutE1 M r ∈ Set.Ioo (-ε) ε := by
  have h := cutE1_abs_tendsto_zero_of_tail M hT h1 htail
  filter_upwards [(tendsto_order.1 h).2 ε hε] with r hr
  rw [abs_lt] at hr
  exact hr

/-- `1 - 𝓔_{1,r} > 0` eventually: the strict positivity of the factor that (I.4.5)/(I.4.6)
invert, from the signed two-sided limit. -/
theorem one_sub_cutE1_pos_eventually
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    (htail : Tendsto (fun r => nablaSup M (openTriangleNabla M) r) atTop (𝓝 0)) :
    ∀ᶠ r : ℝ in atTop, 0 < 1 - cutE1 M r := by
  filter_upwards [cutE1_mem_Ioo_eventually M hT h1 htail (ε := 1) one_pos] with r hr
  have hlt : cutE1 M r < 1 := hr.2
  linarith

/-- `1 - 𝓔_{1,r} → 1`. -/
theorem one_sub_cutE1_tendsto_one
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    (htail : Tendsto (fun r => nablaSup M (openTriangleNabla M) r) atTop (𝓝 0)) :
    Tendsto (fun r => 1 - cutE1 M r) atTop (𝓝 1) := by
  have h := (cutE1_tendsto_zero_of_tail M hT h1 htail).const_sub 1
  simpa using h

/-! ## The tail hypothesis from the pointwise `(HD)` output -/

/-- **`∇_r → 0` from the pointwise logarithmic bound** (Case 3 of `(HD)`, (I.4.13)).

If the uncut open triangle satisfies `∇_{β_c}(0,x) ≤ C (log (1+‖x‖))^{-p}` at every lattice
point with `p > 0`, then its far-distance supremum `∇_r` tends to `0`.  (The paper's
(I.4.13) has `p = 2`; any positive exponent gives the limit, the sharper `p > 1` is what
`Analysis.LogTailCore` needs for logarithmic *integrability*.) -/
theorem tendsto_nablaSup_zero_of_logRadialBound
    {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x)) (openTriangleNabla M) C p) :
    Tendsto (fun r => nablaSup M (openTriangleNabla M) r) atTop (𝓝 0) := by
  have hof : Tendsto (fun r : ℝ => ENNReal.ofReal (logMajorant C p r)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
      (tendsto_logMajorant_zero (C := C) hp)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof
    (Eventually.of_forall fun r => zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hb := radialTailSup_le_logMajorant hC hp.le hr hF
  simpa only [nablaSup, radialTailSup] using hb

/-- **`∇_r → 0` from the pointwise polynomial bound** (Case 2 of `(HD)`, (I.4.11)). -/
theorem tendsto_nablaSup_zero_of_powRadialBound
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hF : PowRadialBound (fun x : M.V => M.S.ρ (toVec x)) (openTriangleNabla M) C a) :
    Tendsto (fun r => nablaSup M (openTriangleNabla M) r) atTop (𝓝 0) := by
  have hof : Tendsto (fun r : ℝ => ENNReal.ofReal (powMajorant C a r)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
      (tendsto_powMajorant_zero (C := C) ha)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof
    (Eventually.of_forall fun r => zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hb := radialTailSup_le_powMajorant hC ha.le hr hF
  simpa only [nablaSup, radialTailSup] using hb

/-! ## The defect vanishes from the pointwise decay input -/

/-- **`𝓔_{1,r} → 0` from the pointwise logarithmic `(HD)` bound (Case 3).** -/
theorem cutE1_tendsto_zero_of_logRadialBound
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x)) (openTriangleNabla M) C p) :
    Tendsto (fun r => cutE1 M r) atTop (𝓝 0) :=
  cutE1_tendsto_zero_of_tail M hT h1 (tendsto_nablaSup_zero_of_logRadialBound M hC hp hF)

/-- **`𝓔_{1,r} → 0` from the pointwise polynomial `(HD)` bound (Case 2).** -/
theorem cutE1_tendsto_zero_of_powRadialBound
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hF : PowRadialBound (fun x : M.V => M.S.ρ (toVec x)) (openTriangleNabla M) C a) :
    Tendsto (fun r => cutE1 M r) atTop (𝓝 0) :=
  cutE1_tendsto_zero_of_tail M hT h1 (tendsto_nablaSup_zero_of_powRadialBound M hC ha hF)

/-! ## Quantitative rate form: the defect inherits the `(I.4.13)` profile -/

/-- **The defect satisfies the logarithmic rate `𝓔_{1,r} ⪯ ∇_0 r^{-d/2} + (log (1+√r))^{-p}`.**

This is `cutE1_le_two_scale` with the tail `∇_{√r}` evaluated through the pointwise bound
`(I.4.13)`.  It is the quantitative statement the error-transfer of §I.4.2 needs; it *does not*
claim logarithmic integrability in `r` of `r ↦ 𝓔_{1,r}`, which would additionally require
measurability of the cutoff moments as functions of the radius (not available at HEAD). -/
theorem cutE1_le_log_rate
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x)) (openTriangleNabla M) C p) :
    ∀ᶠ r : ℝ in atTop, cutE1 M r ≤
      (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
        ((nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2) +
          logMajorant C p (Real.sqrt r))) := by
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ M.d := by positivity
  filter_upwards [cutE1_le_two_scale M hT h1, eventually_gt_atTop (0 : ℝ)] with r hle hr
  have htail : (nablaSup M (openTriangleNabla M) (Real.sqrt r)).toReal ≤
      logMajorant C p (Real.sqrt r) := by
    have hb := radialTailSup_toReal_le (nrm := fun x : M.V => M.S.ρ (toVec x))
      (F := openTriangleNabla M) hC hp.le (Real.sqrt_pos.mpr hr) hF
    simpa only [nablaSup, radialTailSup] using hb
  refine hle.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ h2d) h2d)
  exact add_le_add le_rfl htail

/-- The polynomial-rate analogue of `cutE1_le_log_rate`, from the pointwise `(I.4.11)` bound. -/
theorem cutE1_le_pow_rate
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hF : PowRadialBound (fun x : M.V => M.S.ρ (toVec x)) (openTriangleNabla M) C a) :
    ∀ᶠ r : ℝ in atTop, cutE1 M r ≤
      (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
        ((nablaSup M (openTriangleNabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2) +
          powMajorant C a (Real.sqrt r))) := by
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ M.d := by positivity
  filter_upwards [cutE1_le_two_scale M hT h1, eventually_gt_atTop (0 : ℝ)] with r hle hr
  have htail : (nablaSup M (openTriangleNabla M) (Real.sqrt r)).toReal ≤
      powMajorant C a (Real.sqrt r) := by
    have hb := radialTailSup_toReal_le_powMajorant (nrm := fun x : M.V => M.S.ρ (toVec x))
      (F := openTriangleNabla M) hC ha.le (Real.sqrt_pos.mpr hr) hF
    simpa only [nablaSup, radialTailSup] using hb
  refine hle.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ h2d) h2d)
  exact add_le_add le_rfl htail

/-! ## Identification with the paper's `∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)` -/

/-- `BallAverage.openTriangleNabla` is literally the threefold convolution of the
`ℝ≥0∞` two-point function, i.e. the `TriTail.openTriangle` of the model.  The only content
is `ENNReal.ofReal (τ.toReal) = τ` for the probability-valued two-point function. -/
theorem openTriangleNabla_eq_openTriangle (x : M.V) :
    openTriangleNabla M x =
      PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 x := by
  have hfac : ∀ a b : M.V,
      ENNReal.ofReal (M.twoPoint M.betaCrit a b) = M.twoPointE M.betaCrit a b := by
    intro a b
    rw [SourceModelData.twoPoint_eq_toReal]
    exact ENNReal.ofReal_toReal (M.twoPointE_ne_top M.betaCrit a b)
  simp only [openTriangleNabla, PercLib.CriticalLRP.TriTail.openTriangle, hfac,
    PercLib.CriticalLRP.twoPointFunction, SourceModelData.twoPointE,
    SourceModelData.law]

/-- **`∇_r` is the paper's tail**: the `BallAverage.nablaSup` of the open triangle is
exactly `SourceModelData.nablaTail`, the model's `sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)`. -/
theorem nablaSup_eq_nablaTail (r : ℝ) :
    nablaSup M (openTriangleNabla M) r = M.nablaTail r := by
  simp only [nablaSup, SourceModelData.nablaTail, openTriangleNabla_eq_openTriangle M,
    SourceModelData.dist_zero_eq]

/-- **`𝓔_{1,r} → 0` stated with the paper's tail `∇_r = M.nablaTail`.** -/
theorem cutE1_tendsto_zero_of_nablaTail
    (hT : M.nablaTail 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    (htail : Tendsto M.nablaTail atTop (𝓝 0)) :
    Tendsto (fun r => cutE1 M r) atTop (𝓝 0) := by
  have hT' : nablaSup M (openTriangleNabla M) 0 ≠ ⊤ := by
    rwa [nablaSup_eq_nablaTail]
  refine cutE1_tendsto_zero_of_tail M hT' h1 ?_
  simpa only [nablaSup_eq_nablaTail] using htail

/-- **`𝓔_{1,r} → 0` straight from the accepted Lemma I.4.3 packet.**

`SourceModelData.tendsto_nablaTail_zero` (HEAD, `Analysis/OpenTriangleLogTail.lean`) turns a
pointwise bound `∇_{β_c}(0,y) ⪯ (log (1+‖y‖))^{-p}`, `p > 1`, on the `TriTail` open triangle
into `∇_r → 0`.  Composing with `cutE1_tendsto_zero_of_nablaTail` gives the vanishing of the
truncated defect with no separate tail hypothesis. -/
theorem cutE1_tendsto_zero_of_triTail_logBound
    (hT : M.nablaTail 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Tendsto (fun r => cutE1 M r) atTop (𝓝 0) :=
  cutE1_tendsto_zero_of_nablaTail M hT h1
    (PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_zero M hC hp hF)

/-! ## The Cesàro (Case 2) route: no decay rate needed -/

/-- Cesàro form of the defect bound: `𝓔_{1,r} ≤ |B_r|^{-1} Σ_{x ∈ B_r} ∇_{β_c}(0,x)`
eventually, with the sum written over the ball finset. -/
theorem cutE1_le_cesaro
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, cutE1 M r ≤
      ((ballFinset M r).card : ℝ)⁻¹ *
        (∑ x ∈ ballFinset M r, openTriangleNabla M x).toReal := by
  filter_upwards [h1, eventually_ge_atTop (0 : ℝ)] with r h1r hr
  have hb := PercLib.CriticalLRP.E1Sign.cE1_le_ballSum_openTriangle M r hr h1r
    (ballSum_openTriangleNabla_ne_top M hT r)
  calc cutE1 M r
      ≤ ((M.ball r).ncard : ℝ)⁻¹ * (ballSum M (openTriangleNabla M) r).toReal := hb
    _ = ((ballFinset M r).card : ℝ)⁻¹ *
          (∑ x ∈ ballFinset M r, openTriangleNabla M x).toReal := by
        rw [← ballSum_finset, ← ballFinset_card]

/-- **`𝓔_{1,r} → 0` from summability of `∇_{β_c}(0,·)` (Cesàro, Case 2 shape).**

No decay *rate* is used: `TriangleAverage.summable_kernel_cesaro_tendsto_zero` only needs a
finite total mass and `|B_r| → ∞`.  The hypothesis `Σ_x ∇(0,x) < ∞` is *not* expected to hold
at `β_c` (`TriangleAverage.suscept_le_triMass` derives `χ(β_c) ≤ Σ_x ∇(0,x)`, and
`χ(β_c) = ∞` is the campaign's expected criticality), so this is a conditional structural
result, kept because it is exactly the Case 2 half of the paper's argument. -/
theorem cutE1_tendsto_zero_of_summable
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    (hsum : (∑' x : M.V, openTriangleNabla M x) ≠ ⊤) :
    Tendsto (fun r => cutE1 M r) atTop (𝓝 0) := by
  have hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤ :=
    ne_top_of_le_ne_top hsum (nablaSup_le_tsum M (openTriangleNabla M) 0)
  have hces := summable_kernel_cesaro_tendsto_zero (f := openTriangleNabla M) hsum
    (B := fun r : ℝ => ballFinset M r)
    (by simpa only [ballFinset_card] using tendsto_ball_ncard M)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hces
    (cutE1_nonneg_eventually M h1) (cutE1_le_cesaro M hT h1)

/-! ## Axiom audit (campaign protocol: one line per new theorem) -/

set_option linter.hashCommand false

/-! ## Paper-shaped input: the triangle condition `∇_{β_c} < ∞` -/

/-- **`∇_0 ≤ ∇_{β_c}`**: the sup form of the triangle constant is bounded by the paper's
triangle diagram `∇_{β_c} = ∇_{β_c}(0,0)`, via the diagonal bound
`TriTail.openTriangle_le_diagonal`.  Consequently the hypothesis
`nablaSup M (openTriangleNabla M) 0 ≠ ⊤` is *exactly* the triangle condition, and can be
supplied from `TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤`. -/
theorem nablaSup_le_openTriangleSelf :
    nablaSup M (openTriangleNabla M) 0 ≤
      PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 := by
  refine iSup_le fun x => iSup_le fun _ => ?_
  rw [openTriangleNabla_eq_openTriangle]
  exact PercLib.CriticalLRP.TriTail.openTriangle_le_diagonal M.kernel_shift M.kernel_nonneg
    M.betaCrit x

/-- **`𝓔_{1,r} → 0` from the triangle condition plus `∇_r → 0`.** -/
theorem cutE1_tendsto_zero_of_triangleCondition
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    (htail : Tendsto (fun r => nablaSup M (openTriangleNabla M) r) atTop (𝓝 0)) :
    Tendsto (fun r => cutE1 M r) atTop (𝓝 0) :=
  cutE1_tendsto_zero_of_tail M
    (ne_top_of_le_ne_top hTri.ne (nablaSup_le_openTriangleSelf M))
    h1 htail

/-- **Assembled source-style vanishing of the truncated defect.**

Triangle condition `∇_{β_c} < ∞`, the finite first cutoff moment at every large radius, and the
pointwise logarithmic bound (I.4.13) on the *uncut* open triangle together give the signed
two-sided limit `𝓔_{1,r} → 0` at the actual truncated critical law.  The middle hypothesis is
the only one not derived in the campaign; the last is the `(HD)` Case 3 input, consumed here
through the accepted `tendsto_nablaTail_zero`. -/
theorem cutE1_tendsto_zero_of_triangleCondition_logBound
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Tendsto (fun r => cutE1 M r) atTop (𝓝 0) :=
  cutE1_tendsto_zero_of_triTail_logBound M (M.nablaTail_ne_top 0 hTri) h1 hC hp hF

/-- **The rate form in the paper's own tail notation** `∇_r = M.nablaTail`:
`𝓔_{1,r} ⪯ 2^d (2^d (∇_0 r^{-d/2} + ∇_{√r}))` eventually. -/
theorem cutE1_le_two_scale_nablaTail
    (hT : M.nablaTail 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, cutE1 M r ≤
      (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
        ((M.nablaTail 0).toReal * r ^ (-(M.d : ℝ) / 2) + (M.nablaTail (Real.sqrt r)).toReal)) := by
  have hT' : nablaSup M (openTriangleNabla M) 0 ≠ ⊤ := by rwa [nablaSup_eq_nablaTail]
  refine (cutE1_le_two_scale M hT' h1).mono fun r hr => ?_
  simpa only [nablaSup_eq_nablaTail] using hr

/-! ## The same, in the `TriangleAverage` vocabulary `triMass` -/

/-- `TriangleAverage.triMass` is the total mass of the open triangle of the model, i.e. the
`tsum` of `BallAverage.openTriangleNabla`. -/
theorem triMass_eq_tsum_openTriangleNabla :
    triMass M = ∑' y : M.V, openTriangleNabla M y := by
  rw [triMass]
  exact tsum_congr fun y => (openTriangleNabla_eq_openTriangle M y).symm

/-- **`𝓔_{1,r} → 0` from `Σ_x ∇(0,x) < ∞` in the landed `triMass` vocabulary.** -/
theorem cutE1_tendsto_zero_of_triMass
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    (hmass : triMass M ≠ ⊤) :
    Tendsto (fun r => cutE1 M r) atTop (𝓝 0) :=
  cutE1_tendsto_zero_of_summable M h1
    (by rwa [triMass_eq_tsum_openTriangleNabla] at hmass)

end CutoffDefect

end CriticalLRP

end PercLib

/-! ## Axiom audit (campaign protocol: one line per new theorem) -/

#print axioms PercLib.CriticalLRP.CutoffDefect.ballSum_openTriangleNabla_ne_top
#print axioms PercLib.CriticalLRP.CutoffDefect.nablaSup_le_tsum
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_le_ratio
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_le_normalized_ballSum
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_mem_Icc_ballSum
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_le_two_scale
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_nonneg_eventually
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_tail
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_abs_tendsto_zero_of_tail
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_mem_Ioo_eventually
#print axioms PercLib.CriticalLRP.CutoffDefect.one_sub_cutE1_pos_eventually
#print axioms PercLib.CriticalLRP.CutoffDefect.one_sub_cutE1_tendsto_one
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_le_log_rate
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_le_pow_rate
#print axioms PercLib.CriticalLRP.CutoffDefect.tendsto_nablaSup_zero_of_logRadialBound
#print axioms PercLib.CriticalLRP.CutoffDefect.tendsto_nablaSup_zero_of_powRadialBound
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_logRadialBound
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_powRadialBound
#print axioms PercLib.CriticalLRP.CutoffDefect.openTriangleNabla_eq_openTriangle
#print axioms PercLib.CriticalLRP.CutoffDefect.nablaSup_eq_nablaTail
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_nablaTail
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_triTail_logBound
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_le_cesaro
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_summable
#print axioms PercLib.CriticalLRP.CutoffDefect.nablaSup_le_openTriangleSelf
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_triangleCondition
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_triangleCondition_logBound
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_le_two_scale_nablaTail
#print axioms PercLib.CriticalLRP.CutoffDefect.triMass_eq_tsum_openTriangleNabla
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_triMass
