/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The Karamata primitive for the signed ODE lemma (paper Lemma I.5.26)

Supporting analysis for T. Hutchcroft, *Critical long-range percolation I*
(arXiv:2508.18807v1), Lemma I.5.26.  The proof of that lemma introduces

`f_λ r = f r + λ ∫_{r₀}^{r} h s / s ds`,

uses `∫_{r₀}^{r} h s / s ds = (1 ± o(1)) (1/b) h r`, chooses `λ` large enough that
`f_λ` is eventually positive, feeds `f_λ` into the *positive* ODE Lemma I.4.21,
and finally removes `λ` again: `f_λ ∼ c h` with `c = (1/(b-a))(A + (b-a)λ/b)`
gives `f/h → c - λ/b = A/(b-a)`.

This file supplies that analysis, independently of any ODE (the ODE input itself
is Lemma I.4.21, which is *not* reproved here):

* `regularlyVaryingAtTop_div_id` -- `s ↦ h s / s` is regularly varying of index
  `b - 1`, so Karamata's integral theorem applies to it;
* `intervalIntegrable_of_locallyIntegrableOn`,
  `intervalIntegrable_div_of_locallyBounded_tail` -- interval integrability of
  the primitive from local integrability, resp. from local boundedness of `h` on
  the tail (the paper's "`r₀` large enough that `h` is locally integrable on
  `[r₀, ∞)`");
* `tendsto_karamataPrimitive_base` -- the engine: after extending `h s / s` by
  zero below a cut `r₁ ≥ 1`, Lemma I.2.10 gives `(∫_{r₁}^{r} h/s)/h → 1/b`;
* `tendsto_karamataPrimitive_tail` / `tendsto_karamataPrimitive` -- **the
  Karamata primitive** `(∫_{r₀}^{r} h s / s ds) / h r → 1/b` for `b > 0`, under
  integrability of `h s / s` on the tail `[r₀, ∞)` only (equivalently under
  local integrability on all of `(0, ∞)`);
* `isLittleO_karamataPrimitive` -- the same as `o(h)`, i.e. the paper's
  `(1 ± o(1)) (1/b) h r`;
* `regularlyVaryingAtTop_karamataPrimitive` -- the primitive is itself regularly
  varying of index `b` (it is `∼ h/b`);
* `eventually_pos_add_const_mul_karamataPrimitive` -- for `|f| = O(h)` and `λ`
  large (`C b < λ`, i.e. `λ/b > C`) the shifted function `f + λ ∫ h/s` is
  eventually positive: the paper's choice of `λ`;
* `tendsto_div_of_add_const_mul_karamata` -- the final algebraic step
  `f_λ/h → c ⟹ f/h → c - λ/b`;
* `karamataShift_bridge` -- the two combined, exactly the passage made at the end
  of the proof of Lemma I.5.26;
* `karamataShift_arithmetic` -- the arithmetic identity
  `(1/(b-a))(A + (b-a)λ/b) - λ/b = A/(b-a)` that makes the choice of `λ`
  irrelevant;
* `hasDerivAt_add_const_mul_karamataPrimitive` -- `f_λ' = f' + λ h/r`, the
  derivative computation used to feed `f_λ` back into the ODE.

Hypotheses are those of the paper: `h` measurable, regularly varying of index
`b > 0`, eventually positive; no monotonicity or continuity of `h` is assumed
except where explicitly stated (the derivative lemma).  Potter's bounds and the
divergence `h → ∞` are derived elsewhere in the project
(`Analysis/UniformConvergence.lean`, `Analysis/GeneralInverse.lean`).
-/
module

public import PercLib.CriticalLRP.Analysis.KaramataTail
public import PercLib.CriticalLRP.Analysis.RVInverseMonotone

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

/-! ### Preparatory lemmas -/

/-- Pointwise congruence for regular variation at top. -/
theorem RegularlyVaryingAtTop.congr_fun {f g : ℝ → ℝ} {α : ℝ}
    (hf : RegularlyVaryingAtTop f α) (hfg : ∀ x, f x = g x) :
    RegularlyVaryingAtTop g α := by
  constructor
  · filter_upwards [hf.1] with x hx
    rwa [← hfg x]
  · intro l hl
    refine (hf.2 l hl).congr' ?_
    filter_upwards with x
    rw [hfg (l * x), hfg x]

/-- **Dividing by the identity lowers the index by one.**  If `h` is regularly
varying of index `b` then `s ↦ h s / s` is regularly varying of index `b - 1`.
This is the reduction that lets Karamata's integral theorem produce the
primitive `∫ h s / s ds` with asymptotic `h r / b`. -/
theorem regularlyVaryingAtTop_div_id {h : ℝ → ℝ} {b : ℝ}
    (hrv : RegularlyVaryingAtTop h b) :
    RegularlyVaryingAtTop (fun s => h s / s) (b - 1) := by
  have hinv : RegularlyVaryingAtTop (fun s : ℝ => s ^ (-1 : ℝ)) (-1) :=
    regularlyVaryingAtTop_rpow (-1)
  have hmul : RegularlyVaryingAtTop (fun s : ℝ => h s * s ^ (-1 : ℝ)) (b + -1) :=
    hrv.mul hinv
  rw [show b + (-1 : ℝ) = b - 1 by ring] at hmul
  refine hmul.congr_fun (fun s => ?_)
  rw [div_eq_mul_inv, Real.rpow_neg_one]

/-- Locally integrable on `(0, ∞)` implies interval integrable on every compact
subinterval of `(0, ∞)`. -/
theorem intervalIntegrable_of_locallyIntegrableOn {g : ℝ → ℝ}
    (hloc : LocallyIntegrableOn g (Ioi 0)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab (by simp)]
  exact (locallyIntegrableOn_iff isLocallyClosed_Ioi).1 hloc (Icc a b)
    (fun z hz => lt_of_lt_of_le ha hz.1) isCompact_Icc

/-- **Interval integrability on the tail from local boundedness.**  This is how the
paper's hypothesis "`r₀` is large enough that `h` is locally integrable on
`[r₀, ∞)`" is discharged for the measurable moment functions that occur in the
application: a measurable function bounded on every compact subinterval of
`[r₀, ∞)` has `s ↦ h s / s` interval integrable there. -/
theorem intervalIntegrable_div_of_locallyBounded_tail {h : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hmeas : Measurable h)
    (hbdd : ∀ R, r₀ ≤ R → ∃ C, ∀ s, r₀ ≤ s → s ≤ R → |h s| ≤ C) :
    ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y := by
  intro x y hx hxy
  obtain ⟨C, hC⟩ := hbdd y (le_trans hx hxy)
  have hxpos : 0 < x := lt_of_lt_of_le hr₀ hx
  refine intervalIntegrable_of_bound (C := |C| / x) ?_ ?_
  · exact (hmeas.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
    rw [uIcc_of_le hxy] at hs
    have hspos : 0 < s := lt_of_lt_of_le hxpos hs.1
    have h1 : |h s| ≤ |C| := le_trans (hC s (le_trans hx hs.1) hs.2) (le_abs_self C)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hspos, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul h1 (by simpa [one_div] using one_div_le_one_div_of_le hxpos hs.1)
      (by positivity) (abs_nonneg C)

/-! ### The Karamata primitive -/

/-- **Karamata's theorem for the primitive `∫ h s / s ds`, cut at `r₁ ≥ 1`.**
The integrand `s ↦ h s / s` is extended by zero below `r₁`, which preserves both
regular variation (of index `b - 1`) and local integrability on `(0, ∞)`; Karamata's
integral theorem (paper Lemma I.2.10) applied to that extension then gives the
claim, since the extension agrees with `h s / s` above `r₁` and vanishes on
`(1, r₁)`. -/
theorem tendsto_karamataPrimitive_base {h : ℝ → ℝ} {b r₁ : ℝ}
    (hb : 0 < b) (hr₁ : 1 ≤ r₁) (hmeas : Measurable h)
    (hrv : RegularlyVaryingAtTop h b) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : ∀ x y : ℝ, r₁ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y) :
    Tendsto (fun r => (∫ s in r₁..r, h s / s) / h r) atTop (𝓝 (1 / b)) := by
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le one_pos hr₁
  set g : ℝ → ℝ := fun s => h s / s with hgdef
  set T : ℝ → ℝ := (Ioi r₁).indicator g with hTdef
  have hgmeas : Measurable g := hmeas.div measurable_id
  have hgrv : RegularlyVaryingAtTop g (b - 1) := regularlyVaryingAtTop_div_id hrv
  have hTm : Measurable T := hgmeas.indicator measurableSet_Ioi
  have hTrv : RegularlyVaryingAtTop T (b - 1) := regularlyVarying_indicator_Ioi hgrv
  have hTloc : LocallyIntegrableOn T (Ioi 0) :=
    locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable hloc
  have hTpos : ∀ᶠ s in atTop, 0 < T s := by
    filter_upwards [hpos, eventually_gt_atTop r₁] with s hs hs₁
    rw [hTdef, Set.indicator_of_mem (Set.mem_Ioi.2 hs₁), hgdef]
    exact div_pos hs (lt_trans hr₁pos hs₁)
  have hbase := lemma_I_2_10_of_regularlyVarying (f := T) (α := b - 1) (by linarith)
    hTm hTloc hTpos hTrv
  rw [show (b - 1) + 1 = b by ring] at hbase
  have hTint : ∀ a c : ℝ, 0 < a → 0 < c → IntervalIntegrable T volume a c := by
    intro a c ha hc
    rcases le_total a c with h | h
    · exact intervalIntegrable_of_locallyIntegrableOn hTloc ha h
    · exact (intervalIntegrable_of_locallyIntegrableOn hTloc hc h).symm
  have hnum : ∀ᶠ r in atTop, (∫ s in 1..r, T s) = ∫ s in r₁..r, g s := by
    filter_upwards [eventually_ge_atTop r₁] with r hr
    have hrpos : 0 < r := lt_of_lt_of_le hr₁pos hr
    have hzero : (∫ s in 1..r₁, T s) = 0 := by
      have hz : EqOn T (fun _ => 0) (uIcc 1 r₁) := by
        intro x hx
        rw [uIcc_of_le hr₁] at hx
        rw [hTdef]
        exact Set.indicator_of_notMem (fun hm => not_lt_of_ge hx.2 (Set.mem_Ioi.1 hm)) g
      calc (∫ s in 1..r₁, T s) = ∫ _s in 1..r₁, (0 : ℝ) :=
            intervalIntegral.integral_congr hz
        _ = 0 := intervalIntegral.integral_zero
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hTint 1 r₁ one_pos hr₁pos) (hTint r₁ r hr₁pos hrpos)
    have hcongr : (∫ s in r₁..r, T s) = ∫ s in r₁..r, g s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      rw [uIoc_of_le hr] at hx
      rw [hTdef, Set.indicator_of_mem (Set.mem_Ioi.2 hx.1)]
    rw [← hadd, hzero, zero_add, hcongr]
  have hden : ∀ᶠ r in atTop, r * T r = h r := by
    filter_upwards [eventually_gt_atTop r₁] with r hr
    have hrne : r ≠ 0 := ne_of_gt (lt_trans hr₁pos hr)
    rw [hTdef, Set.indicator_of_mem (Set.mem_Ioi.2 hr), hgdef]
    field_simp
  refine hbase.congr' ?_
  filter_upwards [hnum, hden] with r hrn hrd
  rw [hrn, hrd, hgdef]

/-- **The Karamata primitive** (the analytic input to paper Lemma I.5.26): if `h` is
measurable, eventually positive and regularly varying of index `b > 0`, and
`s ↦ h s / s` is interval integrable on the tail `[r₀, ∞)`, then

`(∫_{r₀}^{r} h s / s ds) / h r → 1/b`.

No positivity of `r₀` is needed: only the integrability hypothesis on the tail
`[r₀, ∞)` is used.  The proof moves the cut up to `r₁ = max 1 r₀` (where the zero
extension of `tendsto_karamataPrimitive_base` applies) and lets `h → ∞` absorb the
constant `∫_{r₀}^{r₁} h/s`. -/
theorem tendsto_karamataPrimitive_tail {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hmeas : Measurable h)
    (hrv : RegularlyVaryingAtTop h b) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y) :
    Tendsto (fun r => (∫ s in r₀..r, h s / s) / h r) atTop (𝓝 (1 / b)) := by
  set r₁ := max 1 r₀ with hr₁def
  have hr₁ : 1 ≤ r₁ := le_max_left _ _
  have hr₀r₁ : r₀ ≤ r₁ := le_max_right _ _
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le one_pos hr₁
  have hbase := tendsto_karamataPrimitive_base hb hr₁ hmeas hrv hpos
    (fun x y hx hxy => hloc x y (le_trans hr₀r₁ hx) hxy)
  set K : ℝ := ∫ s in r₀..r₁, h s / s with hKdef
  have hshift : ∀ᶠ r in atTop, (∫ s in r₀..r, h s / s) = (∫ s in r₁..r, h s / s) + K := by
    filter_upwards [eventually_ge_atTop r₁] with r hr
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hloc r₀ r₁ le_rfl hr₀r₁) (hloc r₁ r hr₀r₁ hr)
    linarith
  have hK0 : Tendsto (fun r => K / h r) atTop (𝓝 0) := by
    have htop : Tendsto h atTop atTop := (RVPosData.of hb hmeas hrv hpos).tendsto_atTop_self
    have hinv : Tendsto (fun r => (h r)⁻¹) atTop (𝓝 0) := htop.inv_tendsto_atTop
    have hmul : Tendsto (fun r => K * (h r)⁻¹) atTop (𝓝 (K * 0)) := hinv.const_mul K
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards with r
    rw [div_eq_mul_inv, mul_comm]
  have hsum : Tendsto (fun r => ((∫ s in r₁..r, h s / s) + K) / h r) atTop (𝓝 (1 / b)) := by
    have hd := hbase.add hK0
    rw [add_zero] at hd
    refine hd.congr' ?_
    filter_upwards with r
    rw [add_div]
  refine hsum.congr' ?_
  filter_upwards [hshift] with r hr
  rw [hr]

/-- **The Karamata primitive, local-integrability form**: it suffices that
`s ↦ h s / s` be locally integrable on all of `(0, ∞)` (the form needed when the
primitive is fed to a result phrased with the fixed lower limit `1`). -/
theorem tendsto_karamataPrimitive {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h)
    (hrv : RegularlyVaryingAtTop h b) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0)) :
    Tendsto (fun r => (∫ s in r₀..r, h s / s) / h r) atTop (𝓝 (1 / b)) :=
  tendsto_karamataPrimitive_tail hb hmeas hrv hpos
    (fun _x _y hx hxy =>
      intervalIntegrable_of_locallyIntegrableOn hloc (lt_of_lt_of_le hr₀ hx) hxy)

/-- **The Karamata primitive with no integrability side condition**: a measurable
regularly varying `h` of index `b > 0` that is bounded on compact subintervals of
`[r₀, ∞)` satisfies the primitive asymptotics.  This is the form in which the paper
applies the lemma (`r₀` large enough that `h` is locally integrable there). -/
theorem tendsto_karamataPrimitive_of_locallyBounded {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h)
    (hrv : RegularlyVaryingAtTop h b) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hbdd : ∀ R, r₀ ≤ R → ∃ C, ∀ s, r₀ ≤ s → s ≤ R → |h s| ≤ C) :
    Tendsto (fun r => (∫ s in r₀..r, h s / s) / h r) atTop (𝓝 (1 / b)) :=
  tendsto_karamataPrimitive_tail hb hmeas hrv hpos
    (intervalIntegrable_div_of_locallyBounded_tail hr₀ hmeas hbdd)

/-! ### The primitive as a little-`o` perturbation, and its regular variation -/

/-- The Karamata primitive differs from `(1/b) h` by `o(h)`: this is the form
`∫_{r₀}^{r} h s / s ds = (1 ± o(1)) (1/b) h r` used in the proof of paper
Lemma I.5.26. -/
theorem isLittleO_karamataPrimitive_of_tendsto {h : ℝ → ℝ} {b r₀ : ℝ}
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hK : Tendsto (fun r => (∫ s in r₀..r, h s / s) / h r) atTop (𝓝 (1 / b))) :
    (fun r => (∫ s in r₀..r, h s / s) - (1 / b) * h r) =o[atTop] h := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ r in atTop,
      |(∫ s in r₀..r, h s / s) / h r - 1 / b| < c := by
    have hball := hK.eventually (Metric.ball_mem_nhds (1 / b) hc)
    simpa [Real.dist_eq, Metric.mem_ball] using hball
  filter_upwards [hev, hpos] with r hr hhr
  have hkey : (∫ s in r₀..r, h s / s) - (1 / b) * h r
      = h r * ((∫ s in r₀..r, h s / s) / h r - 1 / b) := by
    field_simp
  rw [hkey, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hhr]
  nlinarith [abs_nonneg ((∫ s in r₀..r, h s / s) / h r - 1 / b)]

/-- The Karamata primitive differs from `(1/b) h` by `o(h)` (local-integrability
form). -/
theorem isLittleO_karamataPrimitive {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h)
    (hrv : RegularlyVaryingAtTop h b) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0)) :
    (fun r => (∫ s in r₀..r, h s / s) - (1 / b) * h r) =o[atTop] h :=
  isLittleO_karamataPrimitive_of_tendsto hpos
    (tendsto_karamataPrimitive hb hr₀ hmeas hrv hpos hloc)

/-- **The Karamata primitive is regularly varying of the same index `b`**, because
it is asymptotic to `(1/b) h`.  This is what allows the primitive to be fed back
into the ODE lemmas. -/
theorem regularlyVaryingAtTop_karamataPrimitive {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h)
    (hrv : RegularlyVaryingAtTop h b) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0)) :
    RegularlyVaryingAtTop (fun r => ∫ s in r₀..r, h s / s) b := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hscaled : RegularlyVaryingAtTop (fun r => (1 / b) * h r) b :=
    RegularlyVaryingAtTop.const_mul (by positivity) hrv
  refine hscaled.of_tendsto_div ?_
  have hK := tendsto_karamataPrimitive hb hr₀ hmeas hrv hpos hloc
  have hmul : Tendsto (fun r => b * ((∫ s in r₀..r, h s / s) / h r)) atTop
      (𝓝 (b * (1 / b))) := hK.const_mul b
  have hb1 : b * (1 / b) = 1 := by
    field_simp
  rw [hb1] at hmul
  refine hmul.congr' ?_
  filter_upwards with r
  field_simp

/-! ### The shift `f_λ = f + λ ∫ h s / s ds` -/

/-- **Positivity of the shifted function** (the choice of `λ` in the proof of paper
Lemma I.5.26): if `|f| ≤ C h` eventually and `C b < λ` (equivalently `C < λ/b`),
then `f r + λ ∫_{r₀}^{r} h s / s ds > 0` for all large `r`.

The paper writes this as "take `λ` sufficiently large that `A + (b-a)λ/b > 0` and
`f_λ ≥ 0`"; since the primitive is `(1/b ± o(1)) h`, the only content is
`λ/b > C`, exactly as stated here. -/
theorem eventually_pos_add_const_mul_karamata_of_tendsto {f h : ℝ → ℝ} {b r₀ C lam : ℝ}
    (hb : 0 < b) (hlam : 0 < lam) (hC : C * b < lam)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hK : Tendsto (fun r => (∫ s in r₀..r, h s / s) / h r) atTop (𝓝 (1 / b)))
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * h r) :
    ∀ᶠ r in atTop, 0 < f r + lam * ∫ s in r₀..r, h s / s := by
  have hCb : C / lam < 1 / b := by
    rw [div_lt_div_iff₀ hlam hb]
    linarith
  have hδ : 0 < 1 / b - C / lam := sub_pos.2 hCb
  have hev : ∀ᶠ r in atTop,
      |(∫ s in r₀..r, h s / s) / h r - 1 / b| < 1 / b - C / lam := by
    have hball := hK.eventually (Metric.ball_mem_nhds (1 / b) hδ)
    simpa [Real.dist_eq, Metric.mem_ball] using hball
  filter_upwards [hev, hpos, hf] with r hr hhr hfr
  have hlow : C / lam < (∫ s in r₀..r, h s / s) / h r := by
    have := abs_lt.1 hr
    linarith
  have hmul : C < lam * ((∫ s in r₀..r, h s / s) / h r) := by
    calc C = lam * (C / lam) := by field_simp
      _ < lam * ((∫ s in r₀..r, h s / s) / h r) :=
          mul_lt_mul_of_pos_left hlow hlam
  have hshift : C * h r < lam * (∫ s in r₀..r, h s / s) := by
    have hEq : lam * ((∫ s in r₀..r, h s / s) / h r) * h r
        = lam * (∫ s in r₀..r, h s / s) := by
      field_simp
    nlinarith [hEq]
  have hfge : -(C * h r) ≤ f r := by
    have h1 : -(C * h r) ≤ -|f r| := by linarith [neg_abs_le (f r)]
    linarith [abs_le.1 hfr]
  linarith

/-- **The final algebraic step of paper Lemma I.5.26**: if the shifted function
satisfies `(f + λ ∫_{r₀}^{·} h s / s ds)/h → c`, then `f/h → c - λ/b`. -/
theorem tendsto_div_of_add_const_mul_karamata_of_tendsto {f h : ℝ → ℝ} {b r₀ lam c : ℝ}
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hK : Tendsto (fun r => (∫ s in r₀..r, h s / s) / h r) atTop (𝓝 (1 / b)))
    (hf : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop (𝓝 c)) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (c - lam / b)) := by
  have h2 : Tendsto (fun r => lam * ((∫ s in r₀..r, h s / s) / h r)) atTop
      (𝓝 (lam * (1 / b))) := hK.const_mul lam
  have hl : lam * (1 / b) = lam / b := by
    field_simp
  rw [hl] at h2
  have h3 := hf.sub h2
  refine h3.congr' ?_
  filter_upwards [hpos] with r hr
  have hrne : h r ≠ 0 := ne_of_gt hr
  field_simp
  ring

/-- **Positivity of the shifted function** (local-integrability form). -/
theorem eventually_pos_add_const_mul_karamataPrimitive {f h : ℝ → ℝ} {b r₀ C lam : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hlam : 0 < lam) (hC : C * b < lam)
    (hmeas : Measurable h) (hrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0))
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * h r) :
    ∀ᶠ r in atTop, 0 < f r + lam * ∫ s in r₀..r, h s / s :=
  eventually_pos_add_const_mul_karamata_of_tendsto hb hlam hC hpos
    (tendsto_karamataPrimitive hb hr₀ hmeas hrv hpos hloc) hf

/-- **The final algebraic step of paper Lemma I.5.26** (local-integrability form). -/
theorem tendsto_div_of_add_const_mul_karamata {f h : ℝ → ℝ} {b r₀ lam c : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h)
    (hrv : RegularlyVaryingAtTop h b) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0))
    (hf : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop (𝓝 c)) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (c - lam / b)) :=
  tendsto_div_of_add_const_mul_karamata_of_tendsto hpos
    (tendsto_karamataPrimitive hb hr₀ hmeas hrv hpos hloc) hf

/-- **The Karamata step of paper Lemma I.5.26, packaged**: for `h` regularly varying
of index `b > 0` and `|f| ≤ C h` with `C b < λ`, the shifted function
`f_λ = f + λ ∫ h s / s ds` is eventually positive, and if `f_λ / h → c` (the
output of Lemma I.4.21 applied to `f_λ`) then `f / h → c - λ/b`.

This is exactly the passage from `f_λ ∼ c h` to `f ∼ (c - λ/b) h` made at the end
of the proof of Lemma I.5.26, with the freedom in `λ` eliminated. -/
theorem karamataShift_bridge {f h : ℝ → ℝ} {b r₀ C lam c : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hlam : 0 < lam) (hC : C * b < lam)
    (hmeas : Measurable h) (hrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0))
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * h r)
    (hflam : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop (𝓝 c)) :
    (∀ᶠ r in atTop, 0 < f r + lam * ∫ s in r₀..r, h s / s) ∧
      Tendsto (fun r => f r / h r) atTop (𝓝 (c - lam / b)) :=
  ⟨eventually_pos_add_const_mul_karamataPrimitive hb hr₀ hlam hC hmeas hrv hpos hloc hf,
    tendsto_div_of_add_const_mul_karamata hb hr₀ hmeas hrv hpos hloc hflam⟩

/-- **Positivity of the shifted function** (tail-integrability form). -/
theorem eventually_pos_add_const_mul_karamata_of_tail {f h : ℝ → ℝ} {b r₀ C lam : ℝ}
    (hb : 0 < b) (hlam : 0 < lam) (hC : C * b < lam)
    (hmeas : Measurable h) (hrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y)
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * h r) :
    ∀ᶠ r in atTop, 0 < f r + lam * ∫ s in r₀..r, h s / s :=
  eventually_pos_add_const_mul_karamata_of_tendsto hb hlam hC hpos
    (tendsto_karamataPrimitive_tail hb hmeas hrv hpos hloc) hf

/-- **The final algebraic step of paper Lemma I.5.26** (tail-integrability form). -/
theorem tendsto_div_of_add_const_mul_karamata_of_tail {f h : ℝ → ℝ} {b r₀ lam c : ℝ}
    (hb : 0 < b) (hmeas : Measurable h)
    (hrv : RegularlyVaryingAtTop h b) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y)
    (hf : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop (𝓝 c)) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (c - lam / b)) :=
  tendsto_div_of_add_const_mul_karamata_of_tendsto hpos
    (tendsto_karamataPrimitive_tail hb hmeas hrv hpos hloc) hf

/-- **The Karamata step of paper Lemma I.5.26** (tail-integrability form): the
packaged positivity-plus-algebra passage, with the paper's hypotheses. -/
theorem karamataShift_bridge_of_tail {f h : ℝ → ℝ} {b r₀ C lam c : ℝ}
    (hb : 0 < b) (hlam : 0 < lam) (hC : C * b < lam)
    (hmeas : Measurable h) (hrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y)
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * h r)
    (hflam : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop (𝓝 c)) :
    (∀ᶠ r in atTop, 0 < f r + lam * ∫ s in r₀..r, h s / s) ∧
      Tendsto (fun r => f r / h r) atTop (𝓝 (c - lam / b)) :=
  ⟨eventually_pos_add_const_mul_karamata_of_tail hb hlam hC hmeas hrv hpos hloc hf,
    tendsto_div_of_add_const_mul_karamata_of_tail hb hmeas hrv hpos hloc hflam⟩

/-- **The arithmetic identity behind the choice of `λ`** in paper Lemma I.5.26:
applying Lemma I.4.21 to `f_λ` gives `f_λ/h → (1/(b-a))(A + (b-a)λ/b)`, and
subtracting `λ/b` recovers `A/(b-a)`, independently of `λ`. -/
theorem karamataShift_arithmetic {a b A lam : ℝ} (ha : 0 < a) (hab : a < b) :
    (1 / (b - a)) * (A + (b - a) * lam / b) - lam / b = A / (b - a) := by
  have hb : 0 < b := lt_trans ha hab
  have hbne : b ≠ 0 := ne_of_gt hb
  have hd : b - a ≠ 0 := by linarith
  field_simp
  ring

/-- **The conclusion of paper Lemma I.5.26**, `f r = (A/(b-a) ± o(1)) h r`, reduced
to the output of the *positive* ODE Lemma I.4.21 for the shifted function
`f_λ = f + λ ∫ h s/s ds`.

`hI421` is precisely that ODE output, taken as a named hypothesis (paper
Lemma I.4.21 applied to `f_λ`, whose positivity is supplied by
`eventually_pos_add_const_mul_karamataPrimitive` once `C b < λ`): it says
`f_λ/h → (1/(b-a))(A + (b-a)λ/b)`.  Subtracting `λ/b` with
`karamataShift_arithmetic` gives `f/h → A/(b-a)`, independently of `λ`.

Nothing about `f` being positive, or about the ODE satisfied by `f`, is assumed
here.  The remaining hypotheses of the paper (`|f| ≤ C h` and `λ` large, i.e.
`C b < λ`) enter only through the applicability of Lemma I.4.21 to `f_λ`; the
positivity part is `eventually_pos_add_const_mul_karamataPrimitive`. -/
theorem lemma_I_5_26_asymptotic {f h : ℝ → ℝ} {a b A r₀ lam : ℝ}
    (ha : 0 < a) (hab : a < b) (hr₀ : 0 < r₀)
    (hmeas : Measurable h) (hrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0))
    (hI421 : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop
      (𝓝 ((1 / (b - a)) * (A + (b - a) * lam / b)))) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  have hb : 0 < b := lt_trans ha hab
  have h := tendsto_div_of_add_const_mul_karamata (r₀ := r₀) (lam := lam)
    hb hr₀ hmeas hrv hpos hloc hI421
  rwa [karamataShift_arithmetic ha hab] at h

/-- **The conclusion of paper Lemma I.5.26** (tail-integrability form), with the
ODE input of Lemma I.4.21 as a named hypothesis. -/
theorem lemma_I_5_26_asymptotic_of_tail {f h : ℝ → ℝ} {a b A r₀ lam : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hmeas : Measurable h) (hrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y)
    (hI421 : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop
      (𝓝 ((1 / (b - a)) * (A + (b - a) * lam / b)))) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  have hb : 0 < b := lt_trans ha hab
  have h := tendsto_div_of_add_const_mul_karamata_of_tail (r₀ := r₀) (lam := lam)
    hb hmeas hrv hpos hloc hI421
  rwa [karamataShift_arithmetic ha hab] at h

/-- **The shift `f_λ = f + λ ∫ h s / s ds` is differentiable**, with derivative
`f' + λ h r / r`: the computation `f_λ' = f' + λ h/r` in the proof of paper
Lemma I.5.26 (only continuity of `h` at the evaluation point is needed for the
fundamental theorem of calculus). -/
theorem hasDerivAt_add_const_mul_karamataPrimitive {f f' h : ℝ → ℝ} {r₀ lam r : ℝ}
    (hf : HasDerivAt f (f' r) r)
    (hint : IntervalIntegrable (fun s => h s / s) volume r₀ r)
    (hmeas : Measurable h) (hcont : ContinuousAt h r) (hr : r ≠ 0) :
    HasDerivAt (fun x => f x + lam * ∫ s in r₀..x, h s / s)
      (f' r + lam * (h r / r)) r := by
  have hc : ContinuousAt (fun s : ℝ => h s / s) r :=
    hcont.div continuousAt_id (by simpa using hr)
  have hsm : StronglyMeasurableAtFilter (fun s : ℝ => h s / s) (nhds r) volume :=
    (hmeas.div measurable_id).stronglyMeasurable.stronglyMeasurableAtFilter
  have hP : HasDerivAt (fun x => ∫ s in r₀..x, h s / s) (h r / r) r :=
    intervalIntegral.integral_hasDerivAt_right hint hsm hc
  exact hf.add (hP.const_mul lam)

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.Analysis.RegularlyVaryingAtTop.congr_fun
#print axioms PercLib.CriticalLRP.Analysis.regularlyVaryingAtTop_div_id
#print axioms PercLib.CriticalLRP.Analysis.intervalIntegrable_of_locallyIntegrableOn
#print axioms PercLib.CriticalLRP.Analysis.intervalIntegrable_div_of_locallyBounded_tail
#print axioms PercLib.CriticalLRP.Analysis.tendsto_karamataPrimitive_base
#print axioms PercLib.CriticalLRP.Analysis.tendsto_karamataPrimitive_tail
#print axioms PercLib.CriticalLRP.Analysis.tendsto_karamataPrimitive
#print axioms PercLib.CriticalLRP.Analysis.tendsto_karamataPrimitive_of_locallyBounded
#print axioms PercLib.CriticalLRP.Analysis.isLittleO_karamataPrimitive_of_tendsto
#print axioms PercLib.CriticalLRP.Analysis.isLittleO_karamataPrimitive
#print axioms PercLib.CriticalLRP.Analysis.regularlyVaryingAtTop_karamataPrimitive
#print axioms PercLib.CriticalLRP.Analysis.eventually_pos_add_const_mul_karamata_of_tendsto
#print axioms PercLib.CriticalLRP.Analysis.eventually_pos_add_const_mul_karamataPrimitive
#print axioms PercLib.CriticalLRP.Analysis.tendsto_div_of_add_const_mul_karamata_of_tendsto
#print axioms PercLib.CriticalLRP.Analysis.tendsto_div_of_add_const_mul_karamata
#print axioms PercLib.CriticalLRP.Analysis.karamataShift_bridge
#print axioms PercLib.CriticalLRP.Analysis.eventually_pos_add_const_mul_karamata_of_tail
#print axioms PercLib.CriticalLRP.Analysis.tendsto_div_of_add_const_mul_karamata_of_tail
#print axioms PercLib.CriticalLRP.Analysis.karamataShift_bridge_of_tail
#print axioms PercLib.CriticalLRP.Analysis.karamataShift_arithmetic
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_26_asymptotic
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_26_asymptotic_of_tail
#print axioms PercLib.CriticalLRP.Analysis.hasDerivAt_add_const_mul_karamataPrimitive

end PercLib.CriticalLRP.Analysis
