/-
Integrated and independently rebuilt from accepted Ultramath `smwyue9wx`, member `m2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwyue9wx`, member `m2`, direction d2.

# Proposition I.4.15, Case 3 (triangle condition): the second-moment error

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, Case 3 (p. 47).  The source's chain is

```
  E_{2,r} ⪯ (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^4 / (E_{β_c,r}|K| E_{β_c,r}|K|^2),
  (∇_{r^c} + r^{-c}) → 0,      ∇_{r^c} logarithmically integrable when ∇ is,
  E_{β_c,r}|K|^2 ⪰ (E_{β_c,r}|K|)^3 ⪰ r^{3α}.
```

The numerator inequality is Lemma I.4.17 at `p = 3`, `q = 0`, summed over the window `B_r`,
combined with the polygon estimate of Lemma I.4.18.  The *denominator* improvement
`E|K|^2 ⪰ (E|K|)^3` is the source's `case3_hgm_of_tail`
(`I420Case3.case3_hgm_of_tail`: it uses only the uncut critical volume-tail envelope
`P(|K| ≥ n) ≾ n^{-1/2}`, i.e. `hVolTail`, and the finiteness of the cutoff second moment).

## What this file proves

Nothing here re-derives the moment-gap combinatorics or the polygon estimate: both are used as
they stand on disk.  This file supplies the *Case-3 assembly* and everything downstream of it.

* `SecondMomentCase3.ratio_le_of_moment_gap` — the exact real-algebra step of the display:
  with `M2 ⪰ c3 χ³` the numerator bound `C ≤ K |B_r| drv χ⁴` gives
  `C / (|B_r| χ M2) ≤ (K / c3) drv`.  This is where the source's `(E|K|)^4 / (E|K| E|K|^2)`
  is cancelled by the moment gap: without the gap the display only gives `~ χ · drv`, which
  decays at no rate and is *not* logarithmically integrable from `∇` alone.
* `SecondMomentCase3.sum_perVertex_le` — the summation over the window: the per-vertex
  Lemma I.4.17 terms at `p = 3`, `q = 0` (path length `ℓ = 3` and `ℓ = 4`, `2p+2q+1 = 7`)
  produce exactly `|B_r| · C · drv · χ⁴`, i.e. the `|B_r|` of the window cancels against the
  denominator's `|B_r|`.  The hypotheses `hT3`, `hT4` are the two polygon inputs; `hT4` is
  exactly `exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii` at `ℓ = 4`,
  `hT3` is not: see the note below.
* `p2ExclError_le_case3Driver` / `p2ExclError_tendsto_zero_of_case3` — `E_{2,r} ⪯ drv` and
  `E_{2,r} → 0`.
* `logIntegrable_p2ExclError_of_case3` — logarithmic integrability of `E_{2,r}` from that of the
  driver (Lemma I.4.19 at work), and `logIntegrable_p2Ebar` — that of `Ē_{2,r}`, from
  `E_{2,r}`, `H_r`, `E_{0,r}` and their convergence.
* `regularlyVarying_two_of_case3`, `tendsto_div_two_of_case3` — the Case-3 instances of
  `M.regularlyVarying_two` / `M.tendsto_div_two`, i.e. regular variation of index `3α` and
  `E_{β_c,r}|K|^2 ∼ A r^{3α}`.

## The single remaining numerator dependency, named exactly

The source's Lemma I.4.17 at `p = 3`, `q = 0` is **not** on disk.  The formalized general case
`I417SummedFresh.moment_gap_le_pairPoly` requires `1 ≤ q`, and
`I417Gen.prodSet_not_subset_q_zero` shows that the two-copy covering proof *fails* at `q = 0`
(the `y`-arm is the marked walk's terminal; with no `y`-arm there is no terminal).  So the
numerator input is carried below as the explicitly source-shaped hypothesis `hnum`
(`(M.connCubeMass r).toReal ≤ K |B_r| drv χ⁴`), never as a consequence of boundedness.

Two further points about that dependency, both checkable at this base:

* the `ℓ = 4` term is available:
  `exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii` gives
  `T^4(0,x) ≤ C(∇_{r^c}+r^{-c})χ` uniformly in `x`, hence `C₄ T^4(0,y) χ³ ≤ C₄C drv χ⁴`
  per window vertex;
* the `ℓ = 3` term is *not* available in the printed form: the source's `ℓ = 3` display
  `T³(0,0) ≤ C(∇_{r^c}+r^{-c})` is refuted at this base (`I418C.one_le_polyK_three` together
  with the divergence of the driver), so the `ℓ = 3` term must be handled by the column sum
  `∑_y T³(0,y) = χ³`.  Doing so leaves the honest residual term `C₃ χ³ / |B_r|`, which vanishes
  only when `3α < d` — i.e. exactly Case 1.  `sum_perVertex_le` therefore keeps `hT3` visible
  rather than pretending it follows from `hTri`; supplying `hT3` is part of the same missing
  `p = 3`, `q = 0` moment-gap input.

Follow-up modules prove the stronger fact that this pointwise `hT3`, with a vanishing driver, is
unsatisfiable: the diagonal threefold two-point power is at least one.  Consequently the
`hcase3` hypothesis bundle below is uninhabited under its usual finite-moment hypotheses; the
conditional wrapper below is not a non-vacuous Case-3 proof.  `SummedThree` replaces it by a
derived near/far window sum with a logarithmically integrable driver, and `ConsumerGap`
independently derives the near-count residual and repaired analytic conclusions, and
`WindowedEllThree` constructs a source-shaped all-radius windowed driver and asymptotic wrapper.
Each retains `hgap` and its other explicit model hypotheses.  `MarkedPolygon` and `EllThreeObstruction` record
alternative bounds and their residuals; none supplies the source's exact two-term tree-gap.

`QZeroDiagonal` subsequently proves that even the full all-vertex `hgap` is uninhabited under the
explicit `QZeroDiagInputs` growth package: the root is the third cut-off moment, larger than the
allowed diagonal bound by one power of χ. Its `HasRepairedPerVertexHgap` quantifies only over `y ≠ 0`,
and `windowSum_le_of_repaired` isolates the root term exactly. The conditional second-moment wrappers
below retain their original statements as historical conditional interfaces, not as non-vacuous
source claims. The remaining off-diagonal bound has not been supplied, and the non-vacuity of the
full `QZeroDiagInputs` package has not been established here.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.TailLower
public import PercLib.CriticalLRP.Analysis.Polygon.Assembly
public import PercLib.CriticalLRP.Analysis.Polygon.SmallRadius
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.LogIntegrability

/-! # Case-3 second-moment error and logarithmic asymptotics -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Set
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP
namespace Analysis

/-! ## Logarithmic integrability: the eventual comparison used by the Case-3 error -/

/-- **`LogarithmicallyIntegrable` is a tail property.**  If `h` is logarithmically integrable and
the measurable `g` satisfies `|g| ≤ |h|` eventually, then `g` is logarithmically integrable.  The
definition asks for the integrability of `r ↦ |g r| / r` on `(r₀,∞)` for *some* `r₀`; this lemma
lets `r₀` absorb the range where the pointwise comparison is not yet known. -/
theorem LogarithmicallyIntegrable.of_eventually_abs_le {g h : ℝ → ℝ}
    (hg : Measurable g) (hh : LogarithmicallyIntegrable h)
    (hle : ∀ᶠ r : ℝ in atTop, |g r| ≤ |h r|) :
    LogarithmicallyIntegrable g := by
  obtain ⟨-, r₀, hr₀, hint⟩ := hh
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.1 hle
  refine ⟨hg, max r₀ r₁, lt_max_of_lt_left hr₀, ?_⟩
  refine Integrable.mono (hint.mono_set (Ioi_subset_Ioi (le_max_left _ _)))
    ((hg.abs.div measurable_id).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := lt_trans (lt_max_of_lt_left hr₀) hr
  have hr1 : r₁ ≤ r := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hr)
  have h1 : (0 : ℝ) ≤ |g r| / r := by positivity
  have h2 : (0 : ℝ) ≤ |h r| / r := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2]
  exact div_le_div_of_nonneg_right (hr₁ r hr1) hr0.le

/-- The constant-multiple form of `of_eventually_abs_le`. -/
theorem LogarithmicallyIntegrable.of_eventually_abs_le_const_mul {g h : ℝ → ℝ}
    (hg : Measurable g) (hh : LogarithmicallyIntegrable h) {K : ℝ} (hK : 0 ≤ K)
    (hle : ∀ᶠ r : ℝ in atTop, |g r| ≤ K * |h r|) :
    LogarithmicallyIntegrable g := by
  refine LogarithmicallyIntegrable.of_eventually_abs_le hg
    (VolumeMoments.FirstMoment.logIntegrable_const_mul K hh) ?_
  filter_upwards [hle] with r hr
  rw [abs_mul, abs_of_nonneg hK]
  exact hr

/-- The absolute value of a logarithmically integrable function is logarithmically integrable. -/
theorem LogarithmicallyIntegrable.abs {g : ℝ → ℝ}
    (hg : LogarithmicallyIntegrable g) : LogarithmicallyIntegrable (fun r => |g r|) :=
  LogarithmicallyIntegrable.of_eventually_abs_le hg.1.abs hg
    (Filter.Eventually.of_forall fun r => by rw [abs_abs])

/-- A real-valued version of the eventual smallness of an error: if `h → 0` and `h` is measurable
then `|h| ≤ 1/2` eventually. -/
theorem eventually_abs_le_half {h : ℝ → ℝ} (h0 : Tendsto h atTop (𝓝 0)) :
    ∀ᶠ r : ℝ in atTop, |h r| ≤ 1 / 2 := by
  have hmem : ∀ᶠ r : ℝ in atTop, h r ∈ Metric.ball (0 : ℝ) (1 / 2) :=
    h0 (Metric.ball_mem_nhds 0 (by norm_num))
  filter_upwards [hmem] with r hr
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hr
  exact hr.le

/-- Sums of logarithmically integrable functions are logarithmically integrable. -/
theorem LogarithmicallyIntegrable.sub {g h : ℝ → ℝ}
    (hg : LogarithmicallyIntegrable g) (hh : LogarithmicallyIntegrable h) :
    LogarithmicallyIntegrable (fun r => g r - h r) := by
  have := VolumeMoments.FirstMoment.logIntegrable_add hg
    (VolumeMoments.FirstMoment.logIntegrable_neg hh)
  simpa [sub_eq_add_neg] using this

end Analysis

namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The Case-3 numerator-to-error ratio -/

namespace SecondMomentCase3

/-- **The real algebra of the source's Case-3 display.**

With the paper's notation `b = |B_r|`, `A₁ = E|K|`, `A₂ = E|K|²`, `C = E[|K|³|K ∩ B_r|]` and
`drv = ∇_{r^c} + r^{-c}`, the numerator bound `C ≤ K b (drv) A₁⁴` and the moment gap
`c₃ A₁³ ≤ A₂` give

`C / (b A₁ A₂) ≤ (K / c₃) drv`,

since `b A₁ A₂ ⪰ c₃ b A₁⁴`.  Without the moment gap only `C/(b A₁ A₂) ≤ K drv A₁³/A₂ ≤ K drv`
would fail: `A₁³/A₂` can blow up. -/
theorem ratio_le_of_moment_gap {C b A1 A2 χ drv K c3 : ℝ}
    (hb : 0 < b) (hA1 : 0 < A1) (hA2 : 0 < A2) (hχ : 0 < χ) (hdrv : 0 ≤ drv)
    (hA1χ : A1 = χ) (hK : 0 ≤ K) (hc3 : 0 < c3)
    (hgm : c3 * χ ^ 3 ≤ A2) (hC : C ≤ K * b * drv * χ ^ 4) :
    C / (b * A1 * A2) ≤ (K / c3) * drv := by
  have hden : (0 : ℝ) < b * A1 * A2 := by positivity
  rw [div_le_iff₀ hden]
  have hcoef : (0 : ℝ) ≤ K * drv * b * χ / c3 := by positivity
  have hkey : K * b * drv * χ ^ 4 ≤ (K / c3) * drv * (b * A1 * A2) := by
    rw [hA1χ]
    have e1 : K * b * drv * χ ^ 4 = (K * drv * b * χ / c3) * (c3 * χ ^ 3) := by
      field_simp
    have e2 : (K / c3) * drv * (b * χ * A2) = (K * drv * b * χ / c3) * A2 := by
      field_simp
    calc K * b * drv * χ ^ 4 = (K * drv * b * χ / c3) * (c3 * χ ^ 3) := e1
      _ ≤ (K * drv * b * χ / c3) * A2 := mul_le_mul_of_nonneg_left hgm hcoef
      _ = (K / c3) * drv * (b * χ * A2) := e2.symm
  exact hC.trans hkey

/-- **The window summation of the Case-3 numerator.**

Per window vertex `y`, Lemma I.4.17 at `p = 3`, `q = 0` gives two terms
(`2p + 2q + 1 = 7` kernel factors, the path `0 → y` having `ℓ = 3` or `ℓ = 4` edges):

`F y ≤ C₃ T³(0,y) A₁⁴ + C₄ T⁴(0,y) A₁³`.

Summed over the window `B_r` (written `s`), with the polygon bounds `T³(0,y) ≤ Cp drv` and
`T⁴(0,y) ≤ Cp drv A₁`, this is `|B_r| (C₃+C₄) Cp drv A₁⁴` — the `|B_r|` produced by the sum is
exactly the `|B_r|` of the denominator of (I.4.16). -/
theorem sum_perVertex_le {ι : Type*} (s : Finset ι) (F T3 T4 : ι → ℝ) {χ drv C3 C4 Cp : ℝ}
    (hF : ∀ y ∈ s, F y ≤ C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3)
    (hT3 : ∀ y ∈ s, T3 y ≤ Cp * drv)
    (hT4 : ∀ y ∈ s, T4 y ≤ Cp * drv * χ)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (_hCp : 0 ≤ Cp) (hχ : 0 ≤ χ) (_hdrv : 0 ≤ drv) :
    ∑ y ∈ s, F y ≤ (s.card : ℝ) * ((C3 + C4) * Cp) * drv * χ ^ 4 := by
  have hbound : ∀ y ∈ s,
      F y ≤ ((C3 + C4) * Cp) * drv * χ ^ 4 := by
    intro y hy
    refine (hF y hy).trans ?_
    have h3 : C3 * T3 y * χ ^ 4 ≤ C3 * (Cp * drv) * χ ^ 4 := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hχ 4)
      exact mul_le_mul_of_nonneg_left (hT3 y hy) hC3
    have h4 : C4 * T4 y * χ ^ 3 ≤ C4 * (Cp * drv * χ) * χ ^ 3 := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hχ 3)
      exact mul_le_mul_of_nonneg_left (hT4 y hy) hC4
    have hsum : C3 * (Cp * drv) * χ ^ 4 + C4 * (Cp * drv * χ) * χ ^ 3
        = ((C3 + C4) * Cp) * drv * χ ^ 4 := by
      ring
    linarith [h3, h4, hsum.le, hsum.ge]
  calc ∑ y ∈ s, F y ≤ ∑ _y ∈ s, ((C3 + C4) * Cp) * drv * χ ^ 4 :=
        Finset.sum_le_sum hbound
    _ = (s.card : ℝ) * (((C3 + C4) * Cp) * drv * χ ^ 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ) * ((C3 + C4) * Cp) * drv * χ ^ 4 := by ring

end SecondMomentCase3

/-- **Case 3, the source's numerator estimate implies the error estimate.**

Given the Case-3 numerator bound `E[|K_0|³|K_0 ∩ B_r|] ≤ K |B_r| (∇_{r^c} + r^{-c}) (E|K|)⁴`
and the moment gap `c₃ (E|K|)³ ≤ E|K|²`, the second-moment excluded error of (I.4.16) satisfies
`E_{2,r} ≤ (K/c₃)(∇_{r^c} + r^{-c})` eventually. -/
theorem p2ExclError_le_case3Driver {K c r₀ : ℝ} (hK : 0 ≤ K) {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r ≤ (K / c3) * M.case3Driver c r := by
  filter_upwards [hnum, hgm, eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)]
    with r hn hg hr hr1
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have h2r := h2 r hr
  have h1r : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2r
  have hχeq : (M.cutMoment 1 r).toReal = (M.cutMassAt r 0).toReal := by
    rw [M.cutMassAt_zero_eq_cutMoment r]
  have hχ : (0 : ℝ) < (M.cutMassAt r 0).toReal := by
    have := M.one_le_cutMoment_one_toReal r h1r
    rw [hχeq] at this
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := M.one_le_cutMoment_two_toReal r h2r
    linarith
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr0.le
  have hdrv : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
  refine (M.p2ExclError_le_connCubeMass_div r hr0.le h2r (hc r hr1)).trans ?_
  have hA1 : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    rw [hχeq]
    exact hχ
  refine SecondMomentCase3.ratio_le_of_moment_gap (C := (M.connCubeMass r).toReal)
    (b := ((M.ball r).ncard : ℝ)) (A1 := (M.cutMoment 1 r).toReal)
    (A2 := (M.cutMoment 2 r).toReal) (χ := (M.cutMassAt r 0).toReal)
    (drv := M.case3Driver c r) (K := K) (c3 := c3) hb hA1 hA2 hχ hdrv hχeq hK hc3 hg hn

/-- **Case 3: `E_{2,r} → 0`** from the numerator estimate, the moment gap, and the vanishing of
the driver `(∇_{r^c} + r^{-c}) → 0` supplied by the triangle condition. -/
theorem p2ExclError_tendsto_zero_of_case3 {K c r₀ : ℝ} (hK : 0 ≤ K) {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hle := M.p2ExclError_le_case3Driver hK hc3 h2 hc hnum hgm
  have hratio : Tendsto (fun r : ℝ => (K / c3) * M.case3Driver c r) atTop (𝓝 0) := by
    have h := tendsto_const_nhds.mul hdrv (a := K / c3)
    simpa using h
  refine squeeze_zero' ?_ hle hratio
  filter_upwards [eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  exact M.p2ExclError_nonneg r (le_trans zero_le_one hr1) (h2 r hr)

/-- **Case 3: logarithmic integrability of `E_{2,r}`**, from the logarithmic integrability of the
driver (Lemma I.4.19) and the same numerator estimate plus moment gap.  The comparison is
`0 ≤ E_{2,r} ≤ (K/c₃) drv`; `Measurable M.p2ExclError` is the measurability obligation (the
`hmf`/`hmR` shape of `Normalized.lean`). -/
theorem logIntegrable_p2ExclError_of_case3 {K c r₀ : ℝ} (hK : 0 ≤ K) {c3 : ℝ} (hc3 : 0 < c3)
    (hmeas : Measurable M.p2ExclError)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c)) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  have hle := M.p2ExclError_le_case3Driver hK hc3 h2 hc hnum hgm
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le_const_mul hmeas hlogdrv
    (div_nonneg hK hc3.le) ?_
  filter_upwards [hle, eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)]
    with r hbnd hr hr1
  have h0 : 0 ≤ M.p2ExclError r :=
    M.p2ExclError_nonneg r (le_trans zero_le_one hr1) (h2 r hr)
  have hd : 0 ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
  rw [abs_of_nonneg h0, abs_of_nonneg hd]
  exact hbnd

/-! ## Logarithmic integrability of the normalized error `Ē_{2,r}` -/

/-- **The algebraic decomposition of `Ē_{2,r}`.**  With `Ψ_r = (1 + H_r)(1 − E_{0,r})` the
source's relation `1 − Ē_{2,r} = (1 − E_{2,r}) Ψ_r` reads `Ē_{2,r} = E_{2,r} Ψ_r − (Ψ_r − 1)`.
This is the form in which the logarithmic integrability of `Ē` reduces to that of `E_{2,r}` and of
`H_r`, `E_{0,r}`. -/
theorem p2Ebar_eq_exclError_mul_sub (r : ℝ) :
    M.p2Ebar r
      = M.p2ExclError r * ((1 + M.p2H r) * (1 - PivotFlux.cutE0 M r))
        - ((1 + M.p2H r) * (1 - PivotFlux.cutE0 M r) - 1) := by
  have h := M.one_sub_p2Ebar r
  linarith

/-- `Ψ_r − 1 = H_r − E_{0,r} − H_r E_{0,r}`. -/
theorem one_add_mul_one_sub_sub_one (r : ℝ) :
    (1 + M.p2H r) * (1 - PivotFlux.cutE0 M r) - 1
      = M.p2H r - PivotFlux.cutE0 M r - M.p2H r * PivotFlux.cutE0 M r := by
  ring


/-- **Case 3: logarithmic integrability of `Ē_{2,r}`.**

`Ē_{2,r} = E_{2,r} Ψ_r − (Ψ_r − 1)` with `Ψ_r = (1+H_r)(1−E_{0,r}) → 1`, so on the tail
`|Ē_{2,r}| ≤ 3|E_{2,r}| + |H_r − E_{0,r} − H_r E_{0,r}|`, and the second summand is logarithmically
integrable because `H_r` and `E_{0,r}` are (the product uses the smallness of `H_r`).  The
hypotheses `hH`, `hE0` are the *first*-moment logarithmic integrabilities of Proposition I.4.2;
`hE2` is Case 3's own output (`logIntegrable_p2ExclError_of_case3`); `hmeas` is the measurability
obligation. -/
theorem logIntegrable_p2Ebar (hmeas : Measurable M.p2Ebar)
    (hE2 : Analysis.LogarithmicallyIntegrable M.p2ExclError)
    (hH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    (hH0 : Tendsto M.p2H atTop (𝓝 0)) :
    Analysis.LogarithmicallyIntegrable M.p2Ebar := by
  have hE00 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0) := PivotFlux.tendsto_cutE0 M
  have hHhalf := Analysis.eventually_abs_le_half hH0
  have hE0half := Analysis.eventually_abs_le_half hE00
  -- the product `H · E_0` is logarithmically integrable
  have hprod : Analysis.LogarithmicallyIntegrable
      (fun r => M.p2H r * PivotFlux.cutE0 M r) := by
    refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le (hH.1.mul hE0.1) hE0 ?_
    filter_upwards [hHhalf] with r hr
    rw [abs_mul]
    calc |M.p2H r| * |PivotFlux.cutE0 M r|
        ≤ (1 / 2) * |PivotFlux.cutE0 M r| :=
          mul_le_mul_of_nonneg_right hr (abs_nonneg _)
      _ ≤ 1 * |PivotFlux.cutE0 M r| :=
          mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
      _ = |PivotFlux.cutE0 M r| := one_mul _
  -- the discrepancy `Ψ - 1`
  have hA : Analysis.LogarithmicallyIntegrable
      (fun r => M.p2H r - PivotFlux.cutE0 M r - M.p2H r * PivotFlux.cutE0 M r) :=
    (hH.sub hE0).sub hprod
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le hmeas
    (VolumeMoments.FirstMoment.logIntegrable_add
      (VolumeMoments.FirstMoment.logIntegrable_const_mul 3 hE2.abs) hA.abs) ?_
  filter_upwards [hHhalf, hE0half] with r hh he
  have hPsi : |(1 + M.p2H r) * (1 - PivotFlux.cutE0 M r)| ≤ 3 := by
    rw [abs_mul]
    have h1 : |1 + M.p2H r| ≤ 3 / 2 := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (M.p2H r), le_abs_self (M.p2H r)]
    have h2 : |1 - PivotFlux.cutE0 M r| ≤ 3 / 2 := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (PivotFlux.cutE0 M r),
        le_abs_self (PivotFlux.cutE0 M r)]
    calc |1 + M.p2H r| * |1 - PivotFlux.cutE0 M r|
        ≤ (3 / 2) * (3 / 2) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ ≤ 3 := by norm_num
  rw [M.p2Ebar_eq_exclError_mul_sub r, M.one_add_mul_one_sub_sub_one r]
  have hnn : (0 : ℝ) ≤ 3 * |M.p2ExclError r|
      + |M.p2H r - PivotFlux.cutE0 M r - M.p2H r * PivotFlux.cutE0 M r| := by positivity
  rw [abs_of_nonneg hnn]
  have hsplit : |M.p2ExclError r * ((1 + M.p2H r) * (1 - PivotFlux.cutE0 M r))
      - (M.p2H r - PivotFlux.cutE0 M r - M.p2H r * PivotFlux.cutE0 M r)|
      ≤ |M.p2ExclError r| * |(1 + M.p2H r) * (1 - PivotFlux.cutE0 M r)|
        + |M.p2H r - PivotFlux.cutE0 M r - M.p2H r * PivotFlux.cutE0 M r| := by
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_mul]
  have hmul : |M.p2ExclError r| * |(1 + M.p2H r) * (1 - PivotFlux.cutE0 M r)|
      ≤ |M.p2ExclError r| * 3 :=
    mul_le_mul_of_nonneg_left hPsi (abs_nonneg _)
  linarith [hsplit, hmul]

/-! ## The moment gap from the uncut critical volume tail -/

/-- **Case 3, the source's complementary lower bound `E|K|² ⪰ (E|K|)³`.**  This is
`I420Case3.case3_hgm_of_tail` (the source's optimization of `E|K| ≤ N^{1/2} + N^{-1}E|K|²`
against the `n^{-1/2}` volume-tail envelope) transcribed to the source objects: `M.cutMassAt r 0`
is `E_{β_c,r}|K|` by definition of `M.p2H`.  The only probabilistic input is `hVolTail`, the uncut
critical volume-tail envelope; it is *not* inferred from `hTri`, `hP` or any boundedness. -/
theorem exists_momentGap_of_volumeTail {C : ℝ} (hC : 0 ≤ C)
    (hVolTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        Analysis.Route3.tailEnvelope C n)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal := by
  obtain ⟨c3, hc3, hgm⟩ := I420Case3.case3_hgm_of_tail M hC hVolTail h2
  refine ⟨c3, hc3, ?_⟩
  filter_upwards [hgm] with r hr
  rw [I420Case3.momOf_cutProb_eq_toReal_cutMoment M r 1,
    I420Case3.momOf_cutProb_eq_toReal_cutMoment M r 2,
    ← M.cutMassAt_zero_eq_cutMoment r] at hr
  exact hr

/-! ## The Case-3 conclusions for the second cutoff moment -/

/-- **Proposition I.4.15, Case 3 (triangle condition): regular variation of index `3α`.**

The hypotheses are exactly the ones the source uses, split as in `Normalized.lean`:

* `hac`, `hae`, `hmR` — the corner-safe radial regularity of `r ↦ E_{β_c,r}|K|²`;
* `h1`, `h2` — tail finiteness of the first and second cutoff moments;
* `hP` — the (accepted) first-moment asymptotic, which is `H_r → 0`;
* `hcn`, `hnum`, `hK`, `c` — Case 3's numerator input (see the header): the finiteness of the
  connected third window moment and the source's bound
  `E[|K_0|³|K_0 ∩ B_r|] ≤ K |B_r| (∇_{r^c}+r^{-c})(E|K|)⁴`;
* `c3`, `hc3`, `hgm` — the moment gap `E|K|² ⪰ c₃ (E|K|)³`, e.g. from
  `exists_momentGap_of_volumeTail`;
* `hdrv` — the triangle condition's consequence `∇_{r^c} + r^{-c} → 0`.

`E_{0,r} → 0` is discharged by `PivotFlux.tendsto_cutE0`. -/
theorem regularlyVarying_two_of_case3 (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {K c c3 : ℝ} (hK : 0 ≤ K) (hc3 : 0 < c3)
    (hcn : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  exact M.regularlyVarying_two_of_hP_of_ae_deriv hα hr₀ hβ hac hmR hae h1 h2 hP
    (M.p2ExclError_tendsto_zero_of_case3 (r₀ := r₀) hK hc3 h2 hcn hnum hgm hdrv)

/-- **Proposition I.4.15, Case 3: `E_{β_c,r}|K|² ∼ A r^{3α}`.**

Same hypotheses as `regularlyVarying_two_of_case3`, plus the logarithmic integrabilities that the
source's Proposition I.4.2 supplies for the first-moment defects `H_r`, `E_{0,r}` (here `hlogH`,
`hlogE0`) and the two measurability obligations for `E_{2,r}` and `Ē_{2,r}`.  The Case-3
logarithmic integrability of the *driver* is `hlogdrv`
(`M.isLogErrorFunction_case3Driver` provides it from the open-triangle log tail), which is where
Lemma I.4.19 is used. -/
theorem tendsto_div_two_of_case3 (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {K c c3 : ℝ} (hK : 0 ≤ K) (hc3 : 0 < c3)
    (hcn : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0))
    (hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c))
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M)) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  exact M.tendsto_div_two hα hr₀ hβ hac hae h1 h2
    (M.p2ExclError_tendsto_zero_of_case3 (r₀ := r₀) hK hc3 h2 hcn hnum hgm hdrv)
    (M.p2H_tendsto_zero_of_hP hP) (PivotFlux.tendsto_cutE0 M)
    (M.logIntegrable_p2Ebar hmeasEbar
      (M.logIntegrable_p2ExclError_of_case3 (r₀ := r₀) hK hc3 hmeasE2 h2 hcn hnum hgm hlogdrv)
      hlogH hlogE0 (M.p2H_tendsto_zero_of_hP hP))

/-! ## The `ℓ = 4` polygon input and the window assembly -/

/-- **Lemma I.4.18 at `ℓ = 4`, as the Case-3 assembly consumes it.**  This is
`I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii` instantiated at
`ℓ = 4`, with `χ ^ (4 - 3) = χ` evaluated.  The exponent `c` and the constant `Cp` are the
source's, independent of `r` and of the point. -/
theorem exists_polygonBound_four
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) :
    ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧ ∀ r : ℝ, 0 < r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal := by
  obtain ⟨c, Cp, hc, hCp, hbound⟩ :=
    I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii M hP hTri
  refine ⟨c, Cp, hc, hCp, ?_⟩
  intro r hr x
  have h := (hbound (ell := 4) (by norm_num) r hr x).2
  rw [pow_one] at h
  simpa only [case3Driver] using h

/-- **Case 3, window assembly: the numerator estimate from the per-vertex moment gap.**

`F r y` is the per-vertex connected expectation `E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` and
`hF` records that `E[|K_0|³|K_0 ∩ B_r|]` is its sum over the window: this is
`M.connCubeMass_eq_lintegral` followed by `Finset.mul_sum`, `lintegral_finset_sum` and
`ENNReal.toReal_sum` (the finiteness of the summands following from `M.connCubeMass r ≠ ⊤`; it is
kept as a hypothesis so that no `⊤ ↦ 0` conversion is ever made).

The per-vertex gap `hgap` is the source's Lemma I.4.17 at `p = 3`, `q = 0`, whose two terms
(`ℓ = 3`, `ℓ = 4`, kernel count `2p + 2q + 1 = 7`) are `T³(0,y) χ⁴` and `T⁴(0,y) χ³`.  `hT3` and
`hpoly4` are the polygon inputs; `hpoly4` is `exists_polygonBound_four`.  See the header for why
`hT3` is kept visible: the printed `ℓ = 3` display is false at this base, and the column-sum
substitute contributes a residual `χ³/|B_r|`. -/
theorem connCubeMass_toReal_le_of_perVertex_gap {c Cp C3 C4 : ℝ}
    (hCp : 0 ≤ Cp) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) {F : ℝ → M.V → ℝ}
    (hF : ∀ r : ℝ, 1 ≤ r → (M.connCubeMass r).toReal = ∑ y ∈ E1Sign.ballF M r, F r y)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      F r y ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hT3 : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
      I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      ((C3 + C4) * Cp) * ((M.ball r).ncard : ℝ) * M.case3Driver c r
        * (M.cutMassAt r 0).toReal ^ 4 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hχ : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
  have hdrv : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
  rw [hF r hr]
  have hmain := SecondMomentCase3.sum_perVertex_le (s := E1Sign.ballF M r)
    (F := F r) (T3 := fun y => I418C.polyK (M.cutTwoPoint r) 3 0 y)
    (T4 := fun y => I418C.polyK (M.cutTwoPoint r) 4 0 y)
    (χ := (M.cutMassAt r 0).toReal) (drv := M.case3Driver c r)
    (C3 := C3) (C4 := C4) (Cp := Cp)
    (hgap r hr) (fun y _ => hT3 r hr y) (fun y _ => hpoly4 r hr y) hC3 hC4 hCp hχ hdrv
  calc ∑ y ∈ E1Sign.ballF M r, F r y
      ≤ ((E1Sign.ballF M r).card : ℝ) * ((C3 + C4) * Cp) * M.case3Driver c r
          * (M.cutMassAt r 0).toReal ^ 4 := hmain
    _ = ((C3 + C4) * Cp) * ((M.ball r).ncard : ℝ) * M.case3Driver c r
          * (M.cutMassAt r 0).toReal ^ 4 := by
        rw [E1Sign.card_ballF M r]
        ring

/-! ## The window sum decomposition of the Case-3 numerator -/

/-- **`E[|K_0|³ |K_0 ∩ B_r|]` is the sum of its per-vertex parts.**  This is the identity that
lets the source's per-vertex Lemma I.4.17 terms be summed over the window; the `|B_r|` thereby
produced cancels the `|B_r|` of the denominator of (I.4.16).  Proof: the windowed cluster volume is
the sum of the indicators (`Finset.mul_sum`), the integral of a finite sum is the finite sum of the
integrals (`lintegral_finsetSum`). -/
theorem connCubeMass_eq_sum_vertex (r : ℝ) :
    M.connCubeMass r = ∑ y ∈ E1Sign.ballF M r, M.connCubeVertexMass r y := by
  rw [M.connCubeMass_eq_lintegral r]
  have hmul : ∀ ω : Config M.V,
      clusterVol ω (0 : M.V) ^ 3 * ∑ y ∈ E1Sign.ballF M r,
        (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
      = ∑ y ∈ E1Sign.ballF M r, clusterVol ω (0 : M.V) ^ 3 *
        (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro ω
    rw [Finset.mul_sum]
  rw [lintegral_congr hmul]
  exact lintegral_finsetSum _
    (fun y _ => (measurable_clusterVol (0 : M.V)).pow_const 3 |>.mul
      (measurable_const.indicator (measurableSet_cluster_mem (0 : M.V) y)))

/-- The real-valued form of `connCubeMass_eq_sum_vertex`: no `⊤ ↦ 0` conversion is made, the
finiteness of the individual summands being derived from that of the total. -/
theorem connCubeMass_toReal_eq_sum_vertex (r : ℝ) (hfin : M.connCubeMass r ≠ ⊤) :
    (M.connCubeMass r).toReal
      = ∑ y ∈ E1Sign.ballF M r, (M.connCubeVertexMass r y).toReal := by
  rw [M.connCubeMass_eq_sum_vertex r]
  refine ENNReal.toReal_sum ?_
  intro y hy
  have hne : (∑ y ∈ E1Sign.ballF M r, M.connCubeVertexMass r y) ≠ ⊤ := by
    rw [← M.connCubeMass_eq_sum_vertex r]
    exact hfin
  exact ENNReal.sum_ne_top.mp hne y hy

/-- **Case 3, the numerator estimate from the per-vertex moment gap**, with the window
decomposition discharged (`connCubeMass_toReal_eq_sum_vertex`).  The remaining inputs are the
source's per-vertex Lemma I.4.17 at `p = 3`, `q = 0` (`hgap`), its two polygon majorants (`hT3`,
`hpoly4`), and the finiteness of the connected third window moment. -/
theorem connCubeMass_le_of_windowGap {c Cp C3 C4 : ℝ}
    (hCp : 0 ≤ Cp) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hT3 : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
      I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      ((C3 + C4) * Cp) * ((M.ball r).ncard : ℝ) * M.case3Driver c r
        * (M.cutMassAt r 0).toReal ^ 4 :=
  M.connCubeMass_toReal_le_of_perVertex_gap hCp hC3 hC4
    (fun r hr => M.connCubeMass_toReal_eq_sum_vertex r (hc r hr)) hgap hT3 hpoly4

/-! ## The Case-3 theorem, in one statement -/

/-- **Proposition I.4.15, Case 3 (triangle condition): `E_{β_c,r}|K|^2 ∼ A r^{3α}`.**

This is the Case-3 instance of `M.tendsto_div_two`, with every model-side ingredient named:

* `hac`, `hae`, `h1`, `h2` — the corner-safe radial regularity of `r ↦ E_{β_c,r}|K|²` and the tail
  finiteness of the first two cutoff moments;
* `hP` — the accepted first-moment asymptotic `E_{β_c,r}|K| ∼ (α/β_c) r^α` (i.e. `H_r → 0`);
* `hcase3` — **the Case-3 analytic input, in exactly the source's shape**: there are `c, Cp > 0`
  and, for every `r ≥ 1`,
  * the driver decays and is logarithmically integrable: `∇_{r^c} + r^{-c} → 0` and its log
    integrability (Lemma I.4.19), which `M.isLogErrorFunction_case3Driver` supplies from the
    open-triangle log tail;
  * the `ℓ = 4` polygon estimate `T⁴(0,x) ≤ Cp (∇_{r^c}+r^{-c}) χ` (`exists_polygonBound_four`,
    i.e. Lemma I.4.18);
  * the `ℓ = 3` polygon input `T³(0,y) ≤ Cp (∇_{r^c}+r^{-c})`, which is *not* available at this
    base in the printed form (see the header) and is therefore carried visibly;
* `hc`, `hgap` — finiteness of the connected third window moment and the per-vertex Lemma I.4.17
  at `p = 3`, `q = 0` (`C3`, `C4` the source's combinatorial coefficients, `C3, C4 ≥ 0`);
* `hc3`, `hgm` — the moment gap `E_{β_c,r}|K|² ⪰ c₃ (E_{β_c,r}|K|)³`
  (`exists_momentGap_of_volumeTail` produces it from the uncut critical volume tail);
* `hmeasE2`, `hmeasEbar` — the two measurability obligations;
* `hlogH`, `hlogE0` — the first-moment logarithmic integrabilities of Proposition I.4.2.

Nothing is inferred from boundedness alone, no `hTri` is manufactured, and no uniform polygon
factor is promoted: every polygon statement is an explicit hypothesis with its own constant. -/
theorem secondMoment_asymptotic_case3 (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
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
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨c, Cp, hc0, hCp0, hdrv, hlogdrv, hT3, hpoly4⟩ := hcase3
  have hcn : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤ := hc
  have hnum := M.connCubeMass_le_of_windowGap hCp0.le hC3 hC4 hcn hgap hT3 hpoly4
  refine M.tendsto_div_two_of_case3 hα hr₀ hβ hac hae h1 h2 hP
    (K := (C3 + C4) * Cp) (c := c) (c3 := c3) (by positivity) hc3 hc hnum hgm
    hdrv hlogdrv hmeasE2 hmeasEbar hlogH hlogE0

/-! ## Discharging the driver's two properties from the open-triangle log tail -/

/-- **The Case-3 driver is a logarithmic error function, from the pointwise open-triangle log
bound.**  This is `Analysis.isLogErrorFunction_nablaTail` (Lemma I.4.13's radial bound on the uncut
open triangle, giving the open-triangle log tail) followed by
`isLogErrorFunction_nablaTail_add_rpow_neg` (Lemma I.4.19).  It removes `hTail` from the Case-3
input bundle in favour of the pointwise bound `hF`, leaving only the two polygon statements and the
per-vertex moment gap. -/
theorem case3Driver_isLogErrorFunction {c C p : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.IsLogErrorFunction (M.case3Driver c) :=
  M.isLogErrorFunction_case3Driver (isLogErrorFunction_nablaTail M hC hp hF) hc

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
