/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The weak-convergence / integral layer for Proposition I.3.2

Status: reusable analysis only.  This file supplies the analytic input that
`SizeBiasedMGF.lean` keeps as the hypotheses `hker` and `hexp`, derived from a single
weak-convergence hypothesis `Q_r ⇒ Q_∞` on probability laws carried by `[0, ∞)` with
`Q_∞ {0} = 0`.  It does not claim Proposition I.3.2, I.3.5 or the completed MGF.

## Route (Laplace / layer-cake, *not* continuous extension of the singular kernel)

For a probability law `Q` on `[0,∞)` the Laplace transform is
`L_Q t = ∫ exp (-(t*y)) dQ(y)`, and the layer-cake identity (proved in `ChiSquareA3` as
`integral_one_sub_exp_div_eq_interval`) gives, for `Q {0} = 0`,

  `∫ kern λ y dQ(y) = ∫_0^λ L_Q t dt`.

So the singular kernel `kern λ y = (1 - exp (-(λ*y)))/y` is never extended at `y = 0`:
the junk value `kern λ 0 = 0` is replaced by the *integral* value `λ`, which is what the
layer-cake identity produces, and the two differ exactly on the `Q`-null set `{0}`.

The convergence input is used only through:
* fixed-rate Laplace convergence `L_{Q_r} t → L_Q t` (`t > 0`), proved by comparing with the
  bounded continuous *clipped* exponential `clipExp c M` and the explicit truncation error
  `exp (-(c*M))` — no tightness or atom hypothesis is needed for this step;
* bounded continuous transfer for the exponential test `y ↦ exp (-(c*|y|))`, which is
  bounded and continuous on all of `ℝ`;
* the monotone `1`-Lipschitz bound `|∫_s^t L_Q| ≤ |t - s|` for the layer-cake functional,
  which propagates a moving rate `c_r → λ` without differentiating `kern`;
* `Q_∞ {0} = 0` for the `λ → ∞` limit of `∫ exp (-(λ*|y|)) dQ_∞`.

## Hypotheses, stated explicitly

Every theorem below lists its own hypotheses.  In the paper's cluster setting they are:
`Q_r`, `Q_∞` are probability laws (`IsProbabilityMeasure`), carried by `[0,∞)`
(`Q (Iio 0) = 0`), and `Q_∞ {0} = 0` (source hypothesis 4).  For the size-biased laws
`sizeBiasedLaw μ_r` the last two are *proved* here from `μ_r (Iio 0) = 0` and
`0 < sbMean μ_r` (`sizeBiasedLaw_Iio_zero`, `sizeBiasedLaw_singleton_zero`).
-/
module

public import PercLib.CriticalLRP.Analysis.SizeBiasedMGF
public import PercLib.CriticalLRP.Analysis.ChiSquareA3

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace PercLib.CriticalLRP.Analysis.I32Weak

/-! ## 1. The Laplace transform and the clipped exponential -/

/-- The Laplace transform `L_Q(t) = ∫ exp (-(t * y)) dQ(y)`. -/
noncomputable def laplace (Q : Measure ℝ) (t : ℝ) : ℝ := ∫ y, Real.exp (-(t * y)) ∂Q

theorem laplace_def (Q : Measure ℝ) (t : ℝ) :
    laplace Q t = ∫ y, Real.exp (-(t * y)) ∂Q := rfl

/-- On a law carried by `[0, ∞)` and `t ≥ 0`, the Laplace integrand is at most `1`. -/
theorem ae_exp_neg_mul_le_one {Q : Measure ℝ} (hQpos : Q (Iio 0) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ y ∂Q, Real.exp (-(t * y)) ≤ 1 := by
  filter_upwards [PercLib.CriticalLRP.Analysis.I32.ae_nonneg_of_Iio hQpos] with y hy
  rw [Real.exp_le_one_iff]
  nlinarith [mul_nonneg ht hy]

/-- The Laplace integrand is integrable against a finite law carried by `[0, ∞)`. -/
theorem integrable_exp_neg_mul {Q : Measure ℝ} [IsFiniteMeasure Q] (hQpos : Q (Iio 0) = 0)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun y : ℝ => Real.exp (-(t * y))) Q := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [ae_exp_neg_mul_le_one hQpos ht] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hy

/-- The Laplace transform of a probability law carried by `[0, ∞)` is bounded by `1`. -/
theorem abs_laplace_le_one {Q : Measure ℝ} [IsProbabilityMeasure Q] (hQpos : Q (Iio 0) = 0)
    {t : ℝ} (ht : 0 ≤ t) : |laplace Q t| ≤ 1 := by
  have hint := integrable_exp_neg_mul hQpos ht
  have hmono : ∫ y, ‖Real.exp (-(t * y))‖ ∂Q ≤ ∫ _y, (1 : ℝ) ∂Q := by
    refine integral_mono_ae hint.norm (integrable_const 1) ?_
    filter_upwards [ae_exp_neg_mul_le_one hQpos ht] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hy
  have hone : ∫ _y, (1 : ℝ) ∂Q = 1 := by
    rw [integral_const, Measure.real, measure_univ, smul_eq_mul]
    norm_num
  calc |laplace Q t| = ‖laplace Q t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖Real.exp (-(t * y))‖ ∂Q := norm_integral_le_integral_norm _
    _ ≤ 1 := by rw [hone] at hmono; exact hmono

/-- `clipExp c M y = exp (-(c * y))` on `0 ≤ y ≤ M`, and constant outside: the
bounded continuous truncation of the exponential used to transfer weak convergence. -/
noncomputable def clipExp (c M y : ℝ) : ℝ := Real.exp (-(c * max (min y M) 0))

theorem continuous_clipExp (c M : ℝ) : Continuous (clipExp c M) := by
  unfold clipExp; fun_prop

theorem clipExp_pos (c M y : ℝ) : 0 < clipExp c M y := Real.exp_pos _

theorem clipExp_le_one {c M y : ℝ} (hc : 0 ≤ c) : clipExp c M y ≤ 1 := by
  rw [clipExp, Real.exp_le_one_iff]
  have h : 0 ≤ max (min y M) 0 := le_max_right _ _
  nlinarith

theorem abs_clipExp_le_one {c M y : ℝ} (hc : 0 ≤ c) : |clipExp c M y| ≤ 1 := by
  rw [abs_of_pos (clipExp_pos c M y)]
  exact clipExp_le_one hc

theorem clipExp_eq_exp {c M y : ℝ} (hy0 : 0 ≤ y) (hyM : y ≤ M) :
    clipExp c M y = Real.exp (-(c * y)) := by
  rw [clipExp, min_eq_left hyM, max_eq_left hy0]

/-- Explicit truncation error: the clipped exponential is within `exp (-(c*M))` of the
exponential on `[0, ∞)`. -/
theorem abs_exp_sub_clipExp_le {c M y : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (hy : 0 ≤ y) :
    |Real.exp (-(c * y)) - clipExp c M y| ≤ Real.exp (-(c * M)) := by
  rcases le_or_gt y M with hle | hlt
  · rw [clipExp_eq_exp hy hle, sub_self, abs_zero]
    exact (Real.exp_pos _).le
  · have hmax : max (min y M) 0 = M := by rw [min_eq_right hlt.le, max_eq_left hM]
    rw [clipExp, hmax]
    have hexp : Real.exp (-(c * y)) ≤ Real.exp (-(c * M)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    rw [abs_of_nonpos (by linarith)]
    linarith [Real.exp_pos (-(c * y))]

theorem dist_clipExp_le_one {c M : ℝ} (hc : 0 ≤ c) (x y : ℝ) :
    dist (clipExp c M x) (clipExp c M y) ≤ 1 := by
  have hx0 : 0 ≤ clipExp c M x := (clipExp_pos _ _ _).le
  have hx1 : clipExp c M x ≤ 1 := clipExp_le_one hc
  have hy0 : 0 ≤ clipExp c M y := (clipExp_pos _ _ _).le
  have hy1 : clipExp c M y ≤ 1 := clipExp_le_one hc
  rw [Real.dist_eq]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- The clipped exponential as a bounded continuous function (bound `1`). -/
noncomputable def clipExpBCF (c M : ℝ) (hc : 0 ≤ c) : ℝ →ᵇ ℝ where
  toFun := clipExp c M
  continuous_toFun := continuous_clipExp c M
  map_bounded' := ⟨1, dist_clipExp_le_one hc⟩

/-- Truncation error of the Laplace integral itself. -/
theorem abs_laplace_sub_integral_clipExp_le {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hQpos : Q (Iio 0) = 0) {c M : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) :
    |laplace Q c - ∫ y, clipExp c M y ∂Q| ≤ Real.exp (-(c * M)) := by
  have h1 := integrable_exp_neg_mul (Q := Q) hQpos hc
  have h2 : Integrable (clipExp c M) Q := by
    refine Integrable.of_bound (continuous_clipExp c M).aestronglyMeasurable 1 ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact abs_clipExp_le_one hc
  have hsub : laplace Q c - ∫ y, clipExp c M y ∂Q
      = ∫ y, (Real.exp (-(c * y)) - clipExp c M y) ∂Q := by
    rw [laplace_def, integral_sub h1 h2]
  rw [hsub]
  refine le_trans abs_integral_le_integral_abs ?_
  calc ∫ y, |Real.exp (-(c * y)) - clipExp c M y| ∂Q ≤ ∫ _y, Real.exp (-(c * M)) ∂Q := by
        refine integral_mono_ae (h1.sub h2).abs (integrable_const _) ?_
        filter_upwards [PercLib.CriticalLRP.Analysis.I32.ae_nonneg_of_Iio hQpos] with y hy
        exact abs_exp_sub_clipExp_le hc hM hy
    _ = Real.exp (-(c * M)) := by
        rw [integral_const, Measure.real, measure_univ, smul_eq_mul]
        norm_num

/-! ## 2. Fixed-rate exponential convergence (bounded continuous transfer) -/

/-- The exponential test `y ↦ exp (-(c * |y|))` is bounded continuous on all of `ℝ`, so
weak convergence transfers with no support or atom hypothesis whatsoever. -/
theorem tendsto_integral_exp_abs {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {Qr : ι → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hconv : Tendsto Qr L (𝓝 Q)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i => ∫ y, Real.exp (-(c * |y|)) ∂(Qr i : Measure ℝ)) L
      (𝓝 (∫ y, Real.exp (-(c * |y|)) ∂(Q : Measure ℝ))) := by
  have hbc : ∃ C : ℝ, ∀ x y : ℝ,
      dist (Real.exp (-(c * |x|))) (Real.exp (-(c * |y|))) ≤ C := by
    refine ⟨1, fun x y => ?_⟩
    have hx0 : 0 < Real.exp (-(c * |x|)) := Real.exp_pos _
    have hx1 : Real.exp (-(c * |x|)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg x]
    have hy0 : 0 < Real.exp (-(c * |y|)) := Real.exp_pos _
    have hy1 : Real.exp (-(c * |y|)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg y]
    rw [Real.dist_eq]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  let g : ℝ →ᵇ ℝ :=
    { toFun := fun y => Real.exp (-(c * |y|))
      continuous_toFun := by fun_prop
      map_bounded' := hbc }
  have hg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) g
  simpa [g] using hg

/-- Fixed-rate exponential convergence in the `exp (-(c * y))` form, for laws carried by
`[0, ∞)`; it is the `hexp` hypothesis of `SizeBiasedMGF.lean` in the shape used there. -/
theorem tendsto_integral_exp_mul {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {Qr : ι → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hconv : Tendsto Qr L (𝓝 Q))
    (hQr_pos : ∀ i, (Qr i : Measure ℝ) (Iio 0) = 0) (hQpos : (Q : Measure ℝ) (Iio 0) = 0)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i => ∫ y, Real.exp (-(c * y)) ∂(Qr i : Measure ℝ)) L
      (𝓝 (∫ y, Real.exp (-(c * y)) ∂(Q : Measure ℝ))) := by
  have hbase := tendsto_integral_exp_abs (c := c) hconv hc
  have hEq : ∀ (R : Measure ℝ) [IsProbabilityMeasure R], R (Iio 0) = 0 →
      ∫ y, Real.exp (-(c * y)) ∂R = ∫ y, Real.exp (-(c * |y|)) ∂R := by
    intro R _ hR
    refine integral_congr_ae ?_
    filter_upwards [PercLib.CriticalLRP.Analysis.I32.ae_nonneg_of_Iio hR] with y hy
    rw [abs_of_nonneg hy]
  rw [hEq (Q : Measure ℝ) hQpos]
  refine hbase.congr' (Eventually.of_forall fun i => ?_)
  exact (hEq ((Qr i : Measure ℝ)) (hQr_pos i)).symm

/-! ## 3. Laplace convergence along `Q_r ⇒ Q` by truncation -/

/-- **Fixed-rate Laplace convergence.**  Weak convergence `Q_r ⇒ Q` plus the fact that the
laws live on `[0, ∞)` gives `L_{Q_r} c → L_Q c` for every rate `c > 0`.  The proof is the
explicit truncation bound `|L_R c - ∫ clipExp c M dR| ≤ exp (-(c*M))` together with
bounded continuous transfer for `clipExp c M`. -/
theorem tendsto_laplace {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {Qr : ι → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hconv : Tendsto Qr L (𝓝 Q))
    (hQr_pos : ∀ i, (Qr i : Measure ℝ) (Iio 0) = 0) (hQpos : (Q : Measure ℝ) (Iio 0) = 0)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i => laplace (Qr i : Measure ℝ) c) L (𝓝 (laplace (Q : Measure ℝ) c)) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  -- truncation level, large enough that `exp (-(c*M)) < ε/3`
  have hlimM : Tendsto (fun M : ℝ => Real.exp (-(c * M))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ => c * M) atTop atTop :=
      Tendsto.const_mul_atTop hc tendsto_id
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  obtain ⟨M₀, hM₀⟩ :=
    (hlimM.eventually (eventually_lt_nhds (by linarith : (0:ℝ) < ε / 3))).exists
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMε : Real.exp (-(c * M)) < ε / 3 := by
    have hle : Real.exp (-(c * M)) ≤ Real.exp (-(c * M₀)) := by
      refine Real.exp_le_exp.mpr ?_
      have : M₀ ≤ M := le_max_left _ _
      nlinarith
    linarith
  -- bounded continuous transfer at the truncated test function
  have hg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv)
    (clipExpBCF c M hc.le)
  have hg' : Tendsto (fun i => ∫ y, clipExp c M y ∂(Qr i : Measure ℝ)) L
      (𝓝 (∫ y, clipExp c M y ∂(Q : Measure ℝ))) := by
    simpa [clipExpBCF] using hg
  filter_upwards [hg'.eventually
    (Metric.ball_mem_nhds (∫ y, clipExp c M y ∂(Q : Measure ℝ)) (by linarith : (0:ℝ) < ε / 3))]
    with i hi
  rw [Real.dist_eq] at hi ⊢
  have hb1 := abs_laplace_sub_integral_clipExp_le (Q := (Qr i : Measure ℝ)) (hQr_pos i) hc.le hM0
  have hb2 := abs_laplace_sub_integral_clipExp_le (Q := (Q : Measure ℝ)) hQpos hc.le hM0
  have t1 : |laplace (Qr i : Measure ℝ) c - laplace (Q : Measure ℝ) c|
      ≤ |laplace (Qr i : Measure ℝ) c - ∫ y, clipExp c M y ∂(Qr i : Measure ℝ)|
        + |∫ y, clipExp c M y ∂(Qr i : Measure ℝ) - laplace (Q : Measure ℝ) c| :=
    abs_sub_le _ _ _
  have t2 : |∫ y, clipExp c M y ∂(Qr i : Measure ℝ) - laplace (Q : Measure ℝ) c|
      ≤ |∫ y, clipExp c M y ∂(Qr i : Measure ℝ) - ∫ y, clipExp c M y ∂(Q : Measure ℝ)|
        + |∫ y, clipExp c M y ∂(Q : Measure ℝ) - laplace (Q : Measure ℝ) c| :=
    abs_sub_le _ _ _
  have hb2' : |∫ y, clipExp c M y ∂(Q : Measure ℝ) - laplace (Q : Measure ℝ) c| < ε / 3 := by
    rw [abs_sub_comm]; linarith
  linarith


/-! ## 4. The layer-cake functional and the fixed-rate `kern` limit -/

/-- The layer-cake functional `Φ_Q(λ) = ∫_0^λ L_Q(t) dt`. -/
noncomputable def layerCake (Q : Measure ℝ) (lam : ℝ) : ℝ := ∫ t in (0)..lam, laplace Q t

/-- **Layer-cake identity.**  For a finite law carried by `[0, ∞)` with no atom at `0`, the
`kern` integral is the integral of the Laplace transform over the rates `[0, λ]`.  This is
where the junk value `kern λ 0 = 0` is replaced by the correct value `λ`: the identity is
`PercLib.CriticalLRP.Anchor.integral_one_sub_exp_div_eq_interval`, and it needs `Q {0} = 0`. -/
theorem integral_kern_eq_layerCake {Q : Measure ℝ} [IsFiniteMeasure Q]
    (hQpos : ∀ᵐ x ∂Q, 0 ≤ x) (hQ0 : Q {(0 : ℝ)} = 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂Q = layerCake Q lam := by
  have h := PercLib.CriticalLRP.Anchor.integral_one_sub_exp_div_eq_interval Q hQpos hQ0 lam hlam
  simpa [layerCake, laplace_def, PercLib.CriticalLRP.Analysis.I32.kern] using h

/-- The Laplace transform is continuous on `[0, ∞)` in the rate (dominated convergence with
bound `1`). -/
theorem continuousOn_laplace {Q : Measure ℝ} [IsFiniteMeasure Q] (hQpos : Q (Iio 0) = 0) :
    ContinuousOn (laplace Q) (Ici 0) := by
  intro t₀ ht₀
  refine tendsto_integral_filter_of_dominated_convergence (μ := Q) (l := 𝓝[Ici (0:ℝ)] t₀)
    (F := fun t y => Real.exp (-(t * y))) (f := fun y => Real.exp (-(t₀ * y)))
    (bound := fun _ => 1) ?_ ?_ (integrable_const 1) ?_
  · filter_upwards with t
    exact (by fun_prop : Continuous fun y : ℝ => Real.exp (-(t * y))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [PercLib.CriticalLRP.Analysis.I32.ae_nonneg_of_Iio hQpos] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [mul_nonneg ht hy]
  · filter_upwards [PercLib.CriticalLRP.Analysis.I32.ae_nonneg_of_Iio hQpos] with y hy
    exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(t * y))).tendsto t₀).mono_left
      nhdsWithin_le_nhds

/-- **Monotone error bound for a moving rate.**  The layer-cake functional is `1`-Lipschitz
in the rate, because `L_Q ∈ [0, 1]`; equivalently the `kern` integrals are `1`-Lipschitz in
the rate uniformly in the law.  This is what propagates `c_r → λ` below. -/
theorem abs_layerCake_sub_le {Q : Measure ℝ} [IsFiniteMeasure Q] (hQpos : Q (Iio 0) = 0)
    (hQ0 : Q {(0 : ℝ)} = 0) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |layerCake Q s - layerCake Q t| ≤ |s - t| * (Q Set.univ).toReal := by
  rw [← integral_kern_eq_layerCake (PercLib.CriticalLRP.Analysis.I32.ae_nonneg_of_Iio hQpos)
      hQ0 hs.le,
    ← integral_kern_eq_layerCake (PercLib.CriticalLRP.Analysis.I32.ae_nonneg_of_Iio hQpos)
      hQ0 ht.le]
  exact PercLib.CriticalLRP.Analysis.I32.abs_integral_kern_sub_le hQpos hs ht

/-- **Fixed-rate `kern` limit.**  Weak convergence of probability laws on `[0, ∞)` with no
atom at `0` transfers to the `kern` integrals at every fixed positive rate.

The route avoids any continuous extension of `kern` at `0`: by the layer-cake identity both
sides are `∫_0^λ` of the Laplace transform, and the integrands converge with domination
`|L| ≤ 1`. -/
theorem tendsto_integral_kern {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {Qr : ι → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hconv : Tendsto Qr L (𝓝 Q))
    (hQr_pos : ∀ i, (Qr i : Measure ℝ) (Iio 0) = 0)
    (hQr0 : ∀ i, (Qr i : Measure ℝ) {(0 : ℝ)} = 0)
    (hQpos : (Q : Measure ℝ) (Iio 0) = 0) (hQ0 : (Q : Measure ℝ) {(0 : ℝ)} = 0)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun i => ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂(Qr i : Measure ℝ)) L
      (𝓝 (∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂(Q : Measure ℝ))) := by
  set mu := volume.restrict (Set.Ioc 0 lam) with hmudef
  have hmain : Tendsto (fun i => ∫ t, laplace (Qr i : Measure ℝ) t ∂mu) L
      (𝓝 (∫ t, laplace (Q : Measure ℝ) t ∂mu)) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := mu)
      (F := fun i t => laplace (Qr i : Measure ℝ) t) (f := fun t => laplace (Q : Measure ℝ) t)
      (bound := fun _ => 1) ?_ ?_ (integrable_const 1) ?_
    · filter_upwards with i
      exact ((continuousOn_laplace (hQr_pos i)).mono (fun x hx => hx.1.le)).aestronglyMeasurable
        measurableSet_Ioc
    · filter_upwards with i
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs]
      exact abs_laplace_le_one (hQr_pos i) ht.1.le
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact tendsto_laplace hconv hQr_pos hQpos ht.1
  -- identify the two restricted integrals with the `kern` integrals
  have hEq : ∀ (R : Measure ℝ) [IsProbabilityMeasure R], R (Iio 0) = 0 → R {(0 : ℝ)} = 0 →
      ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂R = ∫ t, laplace R t ∂mu := by
    intro R _ hRpos hR0
    rw [integral_kern_eq_layerCake (PercLib.CriticalLRP.Analysis.I32.ae_nonneg_of_Iio hRpos)
      hR0 hlam.le, layerCake, intervalIntegral.integral_of_le hlam.le, hmudef]
  have hlim : ∫ t, laplace (Q : Measure ℝ) t ∂mu
      = ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂(Q : Measure ℝ) :=
    (hEq (Q : Measure ℝ) hQpos hQ0).symm
  rw [hlim] at hmain
  refine hmain.congr' (Eventually.of_forall fun i => ?_)
  exact (hEq ((Qr i : Measure ℝ)) (hQr_pos i) (hQr0 i)).symm

/-! ## 5. Moving rates -/

/-- **Moving-rate `kern` limit.**  If the rates converge, `c_r → λ > 0`, then the `kern`
integrals at the moving rate converge.  The error splits into a fixed-rate part (previous
theorem) and a rate part bounded by `|c_r - λ|` (monotone error bound). -/
theorem tendsto_integral_kern_of_tendsto_rate {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {Qr : ι → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hconv : Tendsto Qr L (𝓝 Q))
    (hQr_pos : ∀ i, (Qr i : Measure ℝ) (Iio 0) = 0)
    (hQr0 : ∀ i, (Qr i : Measure ℝ) {(0 : ℝ)} = 0)
    (hQpos : (Q : Measure ℝ) (Iio 0) = 0) (hQ0 : (Q : Measure ℝ) {(0 : ℝ)} = 0)
    {c : ι → ℝ} {lam : ℝ} (hc : Tendsto c L (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun i => ∫ y, PercLib.CriticalLRP.Analysis.I32.kern (c i) y ∂(Qr i : Measure ℝ)) L
      (𝓝 (∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂(Q : Measure ℝ))) := by
  have hcpos : ∀ᶠ i in L, 0 < c i := hc.eventually (eventually_gt_nhds hlam)
  have hfix := tendsto_integral_kern hconv hQr_pos hQr0 hQpos hQ0 hlam
  have hbound : ∀ᶠ i in L,
      |(∫ y, PercLib.CriticalLRP.Analysis.I32.kern (c i) y ∂(Qr i : Measure ℝ))
          - ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂(Qr i : Measure ℝ)|
        ≤ |c i - lam| := by
    filter_upwards [hcpos] with i hi
    have h := PercLib.CriticalLRP.Analysis.I32.abs_integral_kern_sub_le (Q := (Qr i : Measure ℝ))
      (hQr_pos i) hi hlam
    simpa using h
  have hrate : Tendsto (fun i => |c i - lam|) L (𝓝 0) := by
    simpa using (hc.sub_const lam).abs
  have hdiff : Tendsto
      (fun i => |(∫ y, PercLib.CriticalLRP.Analysis.I32.kern (c i) y ∂(Qr i : Measure ℝ))
          - ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂(Qr i : Measure ℝ)|) L (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i => abs_nonneg _) hbound hrate
  have hdiff' : Tendsto
      (fun i => (∫ y, PercLib.CriticalLRP.Analysis.I32.kern (c i) y ∂(Qr i : Measure ℝ))
          - ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂(Qr i : Measure ℝ)) L (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using hdiff
  have hsum := hdiff'.add hfix
  simpa using hsum

/-- The same, along an index map `r'(a)` (the `r(λ, h)` of the regular-variation inverse).
Nothing is specialised to constants: the rate is the moving `c a`. -/
theorem tendsto_integral_kern_comp {ι κ : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {L' : Filter κ} [L'.IsCountablyGenerated]
    {Qr : ι → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hconv : Tendsto Qr L (𝓝 Q))
    (hQr_pos : ∀ i, (Qr i : Measure ℝ) (Iio 0) = 0)
    (hQr0 : ∀ i, (Qr i : Measure ℝ) {(0 : ℝ)} = 0)
    (hQpos : (Q : Measure ℝ) (Iio 0) = 0) (hQ0 : (Q : Measure ℝ) {(0 : ℝ)} = 0)
    {r' : κ → ι} (hr' : Tendsto r' L' L) {c : κ → ℝ} {lam : ℝ}
    (hc : Tendsto c L' (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun a => ∫ y, PercLib.CriticalLRP.Analysis.I32.kern (c a) y
        ∂(Qr (r' a) : Measure ℝ)) L'
      (𝓝 (∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂(Q : Measure ℝ))) :=
  tendsto_integral_kern_of_tendsto_rate (hconv.comp hr') (fun a => hQr_pos (r' a))
    (fun a => hQr0 (r' a)) hQpos hQ0 hc hlam

/-! ## 6. The `λ → ∞` limit from `Q {0} = 0` -/

/-- **No-atom limit.**  For a probability law with `Q {0} = 0`, the exponential test
`∫ exp (-(λ*|y|)) dQ` tends to `0` as `λ → ∞`: the pointwise limit is `0` off the
`Q`-null set `{0}`, and the domination is the explicit constant `1`. -/
theorem tendsto_integral_exp_abs_atTop {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hQ0 : Q {(0 : ℝ)} = 0) :
    Tendsto (fun c : ℝ => ∫ y, Real.exp (-(c * |y|)) ∂Q) atTop (𝓝 0) := by
  have hae : ∀ᵐ y ∂Q, y ≠ 0 := by
    rw [ae_iff]
    simpa using hQ0
  have key : Tendsto (fun c : ℝ => ∫ y, Real.exp (-(c * |y|)) ∂Q) atTop
      (𝓝 (∫ _y, (0 : ℝ) ∂Q)) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := Q) (bound := fun _ => 1)
      ?_ ?_ (integrable_const 1) ?_
    · filter_upwards with c
      exact (by fun_prop : Continuous fun y : ℝ => Real.exp (-(c * |y|))).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with c hc
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [abs_nonneg y, mul_nonneg hc (abs_nonneg y)]
    · filter_upwards [hae] with y hy
      have hpos : 0 < |y| := abs_pos.mpr hy
      have h1 : Tendsto (fun c : ℝ => c * |y|) atTop atTop :=
        Tendsto.atTop_mul_const hpos tendsto_id
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  simpa using key


/-! ## 7. The size-biased laws: the exact hypotheses `hker` and `hexp` -/

/-- The size-biased law has no atom at `0`: the change of variables is injective at `0` and the
size-biasing density vanishes there.  (No hypothesis on `μ` beyond `sbMean μ ≠ 0`.) -/
theorem sizeBiasedLaw_singleton_zero {mu : Measure ℝ}
    (hS : PercLib.CriticalLRP.Analysis.I32.sbMean mu ≠ 0) :
    PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw mu {(0 : ℝ)} = 0 := by
  unfold PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have hpre : (fun x : ℝ => x / PercLib.CriticalLRP.Analysis.I32.sbMean mu) ⁻¹' {(0 : ℝ)}
      = {(0 : ℝ)} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, div_eq_zero_iff]
    tauto
  rw [hpre, MeasureTheory.withDensity_apply _ (measurableSet_singleton 0)]
  have hzero : ∀ᵐ x ∂(mu.restrict {(0 : ℝ)}), x = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton 0)] with x hx
    simpa using hx
  rw [show (∫⁻ x in {(0 : ℝ)},
        ENNReal.ofReal (x / PercLib.CriticalLRP.Analysis.I32.mean mu) ∂mu)
      = ∫⁻ _x in {(0 : ℝ)}, (0 : ℝ≥0∞) ∂mu from ?_]
  · simp
  · apply lintegral_congr_ae
    filter_upwards [hzero] with x hx
    simp [hx]

/-- **The `hker` hypothesis of `SizeBiasedMGF.lean`, derived.**  For the size-biased laws
`Q_r = sizeBiasedLaw (μ r)` and a limit law `Q_∞` carried by `[0, ∞)` with `Q_∞ {0} = 0`,
weak convergence `Q_r ⇒ Q_∞` gives the fixed-rate kernel limit at every rate `λ > 0`. -/
theorem tendsto_integral_kern_sizeBiasedLaw
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    [∀ r, IsProbabilityMeasure (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))]
    [IsProbabilityMeasure Qinf]
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hSpos : ∀ r, 0 < PercLib.CriticalLRP.Analysis.I32.sbMean (mu r))
    (hQinfpos : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
        (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun r => ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y
        ∂(PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂Qinf)) := by
  have hmain := tendsto_integral_kern (L := atTop)
    (Qr := fun r => Measure.toProbabilityMeasure
      (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r)))
    (Q := Measure.toProbabilityMeasure Qinf) hconv
    (fun r => by
      simp only [Measure.coe_toProbabilityMeasure]
      exact PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw_Iio_zero (hmu r) (hSpos r))
    (fun r => by
      simp only [Measure.coe_toProbabilityMeasure]
      exact sizeBiasedLaw_singleton_zero (hSpos r).ne')
    (by simp only [Measure.coe_toProbabilityMeasure]; exact hQinfpos)
    (by simp only [Measure.coe_toProbabilityMeasure]; exact hQinf0)
    hlam
  simpa only [Measure.coe_toProbabilityMeasure] using hmain

/-- **The moving-rate form for the size-biased laws**: along any family of rates `c_r → λ > 0`. -/
theorem tendsto_integral_kern_sizeBiasedLaw_of_tendsto_rate
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    [∀ r, IsProbabilityMeasure (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))]
    [IsProbabilityMeasure Qinf]
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hSpos : ∀ r, 0 < PercLib.CriticalLRP.Analysis.I32.sbMean (mu r))
    (hQinfpos : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
        (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {c : ℝ → ℝ} {lam : ℝ}
    (hc : Tendsto c atTop (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun r => ∫ y, PercLib.CriticalLRP.Analysis.I32.kern (c r) y
        ∂(PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂Qinf)) := by
  have hmain := tendsto_integral_kern_of_tendsto_rate (L := atTop)
    (Qr := fun r => Measure.toProbabilityMeasure
      (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r)))
    (Q := Measure.toProbabilityMeasure Qinf) hconv
    (fun r => by
      simp only [Measure.coe_toProbabilityMeasure]
      exact PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw_Iio_zero (hmu r) (hSpos r))
    (fun r => by
      simp only [Measure.coe_toProbabilityMeasure]
      exact sizeBiasedLaw_singleton_zero (hSpos r).ne')
    (by simp only [Measure.coe_toProbabilityMeasure]; exact hQinfpos)
    (by simp only [Measure.coe_toProbabilityMeasure]; exact hQinf0)
    hc hlam
  simpa only [Measure.coe_toProbabilityMeasure] using hmain

/-- **The `hexp` hypothesis of `SizeBiasedMGF.lean`, derived.**  No support, atom or
integrability hypothesis is needed: `y ↦ exp (-(c*|y|))` is bounded continuous on `ℝ`. -/
theorem tendsto_integral_exp_abs_sizeBiasedLaw
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    [∀ r, IsProbabilityMeasure (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))]
    [IsProbabilityMeasure Qinf]
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
        (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r => ∫ y, Real.exp (-(c * |y|))
        ∂(PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (∫ y, Real.exp (-(c * |y|)) ∂Qinf)) := by
  have hmain := tendsto_integral_exp_abs (L := atTop)
    (Qr := fun r => Measure.toProbabilityMeasure
      (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r)))
    (Q := Measure.toProbabilityMeasure Qinf) hconv hc
  simpa only [Measure.coe_toProbabilityMeasure] using hmain

/-! ## 8. The chosen index `r(λ, h)` of the regular-variation inverse -/

/-- An order isomorphism of `ℝ` tends to `atTop` at `atTop`. -/
theorem orderIso_tendsto_atTop (e : ℝ ≃o ℝ) : Tendsto (⇑e) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  obtain ⟨z, hz⟩ := e.surjective M
  filter_upwards [eventually_ge_atTop z] with y hy
  calc M = e z := hz.symm
    _ ≤ e y := e.monotone hy

/-- **The lift to the chosen index `r(λ, h)`.**  With `r(λ,h) = e⁻¹(λ/(A₂ h))` — the scale
selection generated by the regular-variation inverse `e` (`GeneralInverse`) — and with the
*measurable, non-constant* rate `h · Ê_{r(λ,h)}`, the size-biased kernel integrals converge to
the `kern` integral of the limit law.  Both `r` and the rate move with `h`; neither is
replaced by a constant. -/
theorem tendsto_integral_kern_scale_selection
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    [∀ r, IsProbabilityMeasure (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))]
    [IsProbabilityMeasure Qinf]
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hSpos : ∀ r, 0 < PercLib.CriticalLRP.Analysis.I32.sbMean (mu r))
    (hQinfpos : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
        (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {e : ℝ ≃o ℝ} {A2 lam : ℝ} (hA2 : 0 < A2) (hlam : 0 < lam)
    (hS2 : Tendsto (fun r => PercLib.CriticalLRP.Analysis.I32.sbMean (mu r) / (A2 * ⇑e r))
      atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => ∫ y, PercLib.CriticalLRP.Analysis.I32.kern
        (h * PercLib.CriticalLRP.Analysis.I32.sbMean (mu (e.symm (lam / (A2 * h))))) y
        ∂(PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw
          (mu (e.symm (lam / (A2 * h)))))) (𝓝[>] (0:ℝ))
      (𝓝 (∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂Qinf)) := by
  -- the argument `λ/(A₂ h)` runs to `atTop`
  have harg : Tendsto (fun h : ℝ => lam / (A2 * h)) (𝓝[>] (0:ℝ)) atTop := by
    have hinv : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have hc : Tendsto (fun h : ℝ => (lam / A2) * h⁻¹) (𝓝[>] (0:ℝ)) atTop :=
      hinv.const_mul_atTop (by positivity)
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := ne_of_gt hh
    field_simp
  -- hence `r(λ, h) → atTop`
  have hrfun : Tendsto (fun h : ℝ => e.symm (lam / (A2 * h))) (𝓝[>] (0:ℝ)) atTop :=
    (orderIso_tendsto_atTop e.symm).comp harg
  -- the moving rate `h Ê_{r(λ,h)} → λ`
  have hrate : Tendsto (fun h : ℝ =>
      h * PercLib.CriticalLRP.Analysis.I32.sbMean (mu (e.symm (lam / (A2 * h)))))
      (𝓝[>] (0:ℝ)) (𝓝 lam) := by
    have hcomp := hS2.comp hrfun
    have hcomp' : Tendsto (fun h : ℝ =>
        PercLib.CriticalLRP.Analysis.I32.sbMean (mu (e.symm (lam / (A2 * h))))
          / (A2 * (lam / (A2 * h)))) (𝓝[>] (0:ℝ)) (𝓝 1) := by
      refine hcomp.congr' ?_
      filter_upwards with h
      simp only [Function.comp_apply]
      rw [e.apply_symm_apply]
    have hmul : Tendsto (fun h : ℝ =>
        (PercLib.CriticalLRP.Analysis.I32.sbMean (mu (e.symm (lam / (A2 * h))))
          / (A2 * (lam / (A2 * h)))) * lam) (𝓝[>] (0:ℝ)) (𝓝 (1 * lam)) :=
      hcomp'.mul_const lam
    have hmul' : Tendsto (fun h : ℝ =>
        (PercLib.CriticalLRP.Analysis.I32.sbMean (mu (e.symm (lam / (A2 * h))))
          / (A2 * (lam / (A2 * h)))) * lam) (𝓝[>] (0:ℝ)) (𝓝 lam) := by
      simpa using hmul
    have h2 : Tendsto (fun h : ℝ =>
        PercLib.CriticalLRP.Analysis.I32.sbMean (mu (e.symm (lam / (A2 * h)))) * h)
        (𝓝[>] (0:ℝ)) (𝓝 lam) := by
      refine hmul'.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh0 : h ≠ 0 := ne_of_gt hh
      have hA2' : A2 ≠ 0 := hA2.ne'
      have hl' : lam ≠ 0 := hlam.ne'
      field_simp
    refine h2.congr' (Eventually.of_forall fun h => ?_)
    ring
  -- assemble with the composition form of the moving-rate theorem
  have hmain := tendsto_integral_kern_comp (L := atTop) (L' := 𝓝[>] (0:ℝ))
    (Qr := fun r => Measure.toProbabilityMeasure
      (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r)))
    (Q := Measure.toProbabilityMeasure Qinf) hconv
    (fun r => by
      simp only [Measure.coe_toProbabilityMeasure]
      exact PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw_Iio_zero (hmu r) (hSpos r))
    (fun r => by
      simp only [Measure.coe_toProbabilityMeasure]
      exact sizeBiasedLaw_singleton_zero (hSpos r).ne')
    (by simp only [Measure.coe_toProbabilityMeasure]; exact hQinfpos)
    (by simp only [Measure.coe_toProbabilityMeasure]; exact hQinf0)
    hrfun hrate hlam
  simpa only [Measure.coe_toProbabilityMeasure] using hmain

/-! ## 9. Concrete checks: the junk convention at zero, constant sequences, chi-square `Q∞` -/

/-- The junk value at the removable singularity. -/
theorem kern_zero (s : ℝ) : PercLib.CriticalLRP.Analysis.I32.kern s 0 = 0 := by
  simp [PercLib.CriticalLRP.Analysis.I32.kern]

/-- **The no-atom hypothesis cannot be dropped.**  Against `δ₀` the `kern` integral is the
junk value `kern λ 0 = 0`, while the layer-cake integral of the Laplace transform is `λ`.
So `∫ kern λ dQ = ∫_0^λ L_Q` genuinely requires `Q {0} = 0`; the discontinuity of `kern`
at `0` is not harmless in general. -/
theorem integral_kern_dirac_zero_ne_layerCake {lam : ℝ} (hlam : 0 < lam) :
    ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂(Measure.dirac (0:ℝ)) = 0 ∧
      ∫ t in (0)..lam, (∫ y, Real.exp (-(t * y)) ∂(Measure.dirac (0:ℝ))) = lam := by
  have _ := hlam
  constructor
  · rw [integral_dirac]
    exact kern_zero lam
  · have h : ∀ t : ℝ, (∫ y, Real.exp (-(t * y)) ∂(Measure.dirac (0:ℝ))) = 1 := by
      intro t
      rw [integral_dirac]
      simp
    simp only [h]
    simp

/-- **The punctured limit of `kern λ` at `0` is `λ`.**  This is the value that the layer-cake
identity computes (`kern λ y = ∫_0^λ e^{-ty} dt` for `y ≠ 0`, then dominated convergence in
`y`); the Lean value `kern λ 0 = 0` is junk.  So `kern λ` is discontinuous at `0` and cannot
be used as a bounded continuous test function without replacing its value there. -/
theorem tendsto_kern_nhdsNE_zero {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun y => PercLib.CriticalLRP.Analysis.I32.kern lam y) (𝓝[≠] (0:ℝ)) (𝓝 lam) := by
  set mu := volume.restrict (Set.Ioc 0 lam) with hmudef
  have hvol : ∫ _t, (1 : ℝ) ∂mu = lam := by
    rw [hmudef, integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, sub_zero, mul_one]
  have hball : ∀ᶠ y : ℝ in 𝓝[≠] (0:ℝ), |y| ≤ 1 := by
    have h : ∀ᶠ y : ℝ in 𝓝 (0:ℝ), |y| ≤ 1 := by
      filter_upwards [Metric.closedBall_mem_nhds (0:ℝ) zero_lt_one] with y hy
      simpa using hy
    exact h.filter_mono nhdsWithin_le_nhds
  have hmain : Tendsto (fun y : ℝ => ∫ t, Real.exp (-(t * y)) ∂mu)
      (𝓝[≠] (0:ℝ)) (𝓝 (∫ _t, (1 : ℝ) ∂mu)) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := mu) (l := 𝓝[≠] (0:ℝ))
      (F := fun y t => Real.exp (-(t * y))) (f := fun _ => (1 : ℝ))
      (bound := fun _ => Real.exp lam) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with y
      exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t * y))).aestronglyMeasurable
    · filter_upwards [hball] with y hy
      filter_upwards [hmudef ▸ ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr ?_
      have ht1 : 0 < t := ht.1
      have ht2 : t ≤ lam := ht.2
      nlinarith [abs_le.mp hy, ht1.le, ht2]
    · filter_upwards [hmudef ▸ ae_restrict_mem measurableSet_Ioc] with t ht
      have hcont : Tendsto (fun y : ℝ => Real.exp (-(t * y))) (𝓝 (0:ℝ)) (𝓝 1) := by
        have h := (by fun_prop : Continuous fun y : ℝ => Real.exp (-(t * y))).tendsto (0:ℝ)
        simpa using h
      exact hcont.mono_left nhdsWithin_le_nhds
  have hmain' : Tendsto (fun y : ℝ => ∫ t, Real.exp (-(t * y)) ∂mu) (𝓝[≠] (0:ℝ)) (𝓝 lam) := by
    simpa only [hvol] using hmain
  refine hmain'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [hmudef, ← intervalIntegral.integral_of_le hlam.le,
    PercLib.CriticalLRP.Anchor.intervalIntegral_exp_neg_mul lam y hy]
  simp [PercLib.CriticalLRP.Analysis.I32.kern]

/-- **`kern s` is discontinuous at `0` for every positive rate**, so it is *not* a bounded
continuous test function and cannot be fed to Portmanteau directly: the extension at `0` must
be the value `s`. -/
theorem kern_not_continuousAt_zero {s : ℝ} (hs : 0 < s) :
    ¬ ContinuousAt (fun y => PercLib.CriticalLRP.Analysis.I32.kern s y) (0:ℝ) := by
  intro hcont
  have h1 : Tendsto (fun y => PercLib.CriticalLRP.Analysis.I32.kern s y) (𝓝[≠] (0:ℝ)) (𝓝 s) :=
    tendsto_kern_nhdsNE_zero hs
  have h2 : Tendsto (fun y => PercLib.CriticalLRP.Analysis.I32.kern s y) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    simpa [kern_zero s] using hcont.tendsto.mono_left (nhdsWithin_le_nhds)
  exact hs.ne' (tendsto_nhds_unique h1 h2)

/-! ### The chi-square limit law of the paper -/

theorem Qinf_Iio_zero : PercLib.CriticalLRP.Anchor.Qinf (Iio 0) = 0 := by
  rw [← compl_mem_ae_iff]
  filter_upwards [PercLib.CriticalLRP.Anchor.Qinf_ae_nonneg] with x hx
  simpa using hx

/-- The `kern` integral of the chi-square limit law is the closed form `√(1+2λ) - 1` used for
`A₃` in the paper (it is `PercLib.CriticalLRP.Anchor.integral_A3_kernel_Qinf`). -/
theorem kern_Qinf_value {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂PercLib.CriticalLRP.Anchor.Qinf
      = Real.sqrt (1 + 2 * lam) - 1 := by
  simpa [PercLib.CriticalLRP.Analysis.I32.kern] using
    PercLib.CriticalLRP.Anchor.integral_A3_kernel_Qinf lam hlam

/-- The exponential test of the chi-square law: `∫ exp (-(c*|y|)) dQ∞ = (√(1+2c))⁻¹`. -/
theorem exp_abs_Qinf_value {c : ℝ} (hc : 0 ≤ c) :
    ∫ y, Real.exp (-(c * |y|)) ∂PercLib.CriticalLRP.Anchor.Qinf
      = (Real.sqrt (1 + 2 * c))⁻¹ := by
  rw [← PercLib.CriticalLRP.Anchor.laplace_Qinf c hc]
  refine integral_congr_ae ?_
  filter_upwards [PercLib.CriticalLRP.Anchor.Qinf_ae_nonneg] with y hy
  rw [abs_of_nonneg hy]

/-- **Check: constant sequence of laws plus a moving rate.**  The abstract moving-rate theorem
instantiates at `Q_r ≡ Q∞` (chi-square) and `c_n = λ + 1/(n+1) → λ`, giving the limit in the
closed form `√(1+2λ) - 1`. -/
theorem chiSquare_constant_sequence_moving_rate {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => ∫ y, PercLib.CriticalLRP.Analysis.I32.kern
        (lam + 1 / ((n : ℝ) + 1)) y ∂PercLib.CriticalLRP.Anchor.Qinf) atTop
      (𝓝 (Real.sqrt (1 + 2 * lam) - 1)) := by
  have hrate : Tendsto (fun n : ℕ => lam + 1 / ((n : ℝ) + 1)) atTop (𝓝 lam) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds.add h)
  have hsupp : ∀ _i : ℕ,
      (↑(Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf) : Measure ℝ) (Iio 0) = 0 := by
    intro i
    simp only [Measure.coe_toProbabilityMeasure]
    exact Qinf_Iio_zero
  have hatom : ∀ _i : ℕ,
      (↑(Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf) : Measure ℝ)
        {(0 : ℝ)} = 0 := by
    intro i
    simp only [Measure.coe_toProbabilityMeasure]
    exact PercLib.CriticalLRP.Anchor.Qinf_singleton_zero
  have hmain := tendsto_integral_kern_of_tendsto_rate (L := atTop)
    (Qr := fun _ => Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf)
    (Q := Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf)
    tendsto_const_nhds hsupp hatom (hsupp 0) (hatom 0) hrate hlam
  have hfun : Tendsto (fun n : ℕ => ∫ y, PercLib.CriticalLRP.Analysis.I32.kern
      (lam + 1 / ((n : ℝ) + 1)) y ∂PercLib.CriticalLRP.Anchor.Qinf) atTop
      (𝓝 (∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y
        ∂PercLib.CriticalLRP.Anchor.Qinf)) := by
    simpa only [Measure.coe_toProbabilityMeasure] using hmain
  simpa only [kern_Qinf_value hlam.le] using hfun

/-- **Check: the `λ → ∞` no-atom limit at the chi-square law**, in closed form
`(√(1+2λ))⁻¹ → 0`. -/
theorem chiSquare_exp_abs_atTop :
    Tendsto (fun c : ℝ => (Real.sqrt (1 + 2 * c))⁻¹) atTop (𝓝 0) := by
  have hbase := tendsto_integral_exp_abs_atTop
    (Q := PercLib.CriticalLRP.Anchor.Qinf) PercLib.CriticalLRP.Anchor.Qinf_singleton_zero
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with c hc
  exact exp_abs_Qinf_value hc


/-! ## 10. Plug-in interface for the two hypotheses of `SizeBiasedMGF.lean` -/

/-- The exact shape of the `hker` hypothesis of `stage1_mgf_ratio` / `mgf_of_components`,
discharged from weak convergence.  (The caller should have the instance
`∀ r, IsProbabilityMeasure (sizeBiasedLaw (μ r))` in scope, e.g. via `haveI := hprob`; it is
what makes `Measure.toProbabilityMeasure` applicable.) -/
theorem hker_of_weak_convergence
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    [∀ r, IsProbabilityMeasure (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))]
    [IsProbabilityMeasure Qinf]
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hSpos : ∀ r, 0 < PercLib.CriticalLRP.Analysis.I32.sbMean (mu r))
    (hQinfpos : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
        (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf))) :
    ∀ lam > 0, Tendsto (fun r => ∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y
        ∂(PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (∫ y, PercLib.CriticalLRP.Analysis.I32.kern lam y ∂Qinf)) :=
  fun _lam hlam =>
    tendsto_integral_kern_sizeBiasedLaw mu Qinf hmu hSpos hQinfpos hQinf0 hconv hlam

/-- The exact shape of the `hexp` hypothesis of `ghost_control_of_source`, discharged from
weak convergence.  No support or atom hypothesis is needed for this one. -/
theorem hexp_of_weak_convergence
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    [∀ r, IsProbabilityMeasure (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))]
    [IsProbabilityMeasure Qinf]
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
        (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf))) :
    ∀ c > 0, Tendsto (fun r => ∫ y, Real.exp (-(c * |y|))
        ∂(PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (∫ y, Real.exp (-(c * |y|)) ∂Qinf)) :=
  fun _c hc => tendsto_integral_exp_abs_sizeBiasedLaw mu Qinf hconv hc

/-! ## 12. Moving rates for the exponential test (monotone squeeze)

The rate `c ↦ exp (-(c*|y|))` is decreasing, so a moving rate is squeezed between the two
fixed rates `λ ∓ δ`, and the limit functional is continuous in the rate at `λ > 0`.  This
gives the exponential analogue of `tendsto_integral_kern_of_tendsto_rate` without needing
uniform moment bounds. -/

/-- The exponential test is continuous in the rate at every positive rate. -/
theorem continuousOn_exp_abs (Q : Measure ℝ) [IsFiniteMeasure Q] :
    ContinuousOn (fun c : ℝ => ∫ y, Real.exp (-(c * |y|)) ∂Q) (Ioi 0) := by
  intro c₀ hc₀
  refine tendsto_integral_filter_of_dominated_convergence (μ := Q) (l := 𝓝[Ioi (0:ℝ)] c₀)
    (F := fun c y => Real.exp (-(c * |y|))) (f := fun y => Real.exp (-(c₀ * |y|)))
    (bound := fun _ => 1) ?_ ?_ (integrable_const 1) ?_
  · filter_upwards with c
    exact (by fun_prop : Continuous fun y : ℝ => Real.exp (-(c * |y|))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : (0:ℝ) < c := hc
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [abs_nonneg y, hc0.le]
  · filter_upwards with y
    exact ((by fun_prop : Continuous fun c : ℝ => Real.exp (-(c * |y|))).tendsto c₀).mono_left
      nhdsWithin_le_nhds

/-- Monotonicity of the exponential test in the rate. -/
theorem integral_exp_abs_anti {Q : Measure ℝ} [IsFiniteMeasure Q] {c c' : ℝ}
    (hc' : 0 ≤ c') (hle : c' ≤ c) :
    ∫ y, Real.exp (-(c * |y|)) ∂Q ≤ ∫ y, Real.exp (-(c' * |y|)) ∂Q := by
  have hb : ∀ d : ℝ, 0 ≤ d → Integrable (fun y : ℝ => Real.exp (-(d * |y|))) Q := by
    intro d hd
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [abs_nonneg y, hd]
  refine integral_mono_ae (hb c (le_trans hc' hle)) (hb c' hc') ?_
  filter_upwards with y
  refine Real.exp_le_exp.mpr ?_
  nlinarith [abs_nonneg y]

/-- **Moving-rate exponential limit.**  For `c_r → λ > 0` the exponential tests at the moving
rate converge.  No support, atom or moment hypothesis is needed. -/
theorem tendsto_integral_exp_abs_of_tendsto_rate {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {Qr : ι → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hconv : Tendsto Qr L (𝓝 Q))
    {c : ι → ℝ} {lam : ℝ} (hc : Tendsto c L (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun i => ∫ y, Real.exp (-(c i * |y|)) ∂(Qr i : Measure ℝ)) L
      (𝓝 (∫ y, Real.exp (-(lam * |y|)) ∂(Q : Measure ℝ))) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hcont : Tendsto (fun d : ℝ => ∫ y, Real.exp (-(d * |y|)) ∂(Q : Measure ℝ))
      (𝓝[Ioi (0:ℝ)] lam) (𝓝 (∫ y, Real.exp (-(lam * |y|)) ∂(Q : Measure ℝ))) :=
    continuousOn_exp_abs (Q : Measure ℝ) lam hlam
  have hclose : ∀ᶠ d : ℝ in 𝓝[Ioi (0:ℝ)] lam,
      dist (∫ y, Real.exp (-(d * |y|)) ∂(Q : Measure ℝ))
        (∫ y, Real.exp (-(lam * |y|)) ∂(Q : Measure ℝ)) < ε / 3 :=
    hcont.eventually (Metric.ball_mem_nhds _ (by linarith))
  rw [eventually_nhdsWithin_iff] at hclose
  obtain ⟨η, hη0, hη⟩ := Metric.eventually_nhds_iff.mp hclose
  set dlt : ℝ := min η (lam / 2) with hdlt
  have hdlt0 : 0 < dlt := lt_min hη0 (by linarith)
  have hdltη : dlt ≤ η := min_le_left η (lam / 2)
  have hdltlam : dlt ≤ lam / 2 := min_le_right η (lam / 2)
  have hrate_lo : 0 < lam - dlt / 2 := by linarith
  have hrate_hi : 0 < lam + dlt / 2 := by linarith
  have hlo := tendsto_integral_exp_abs (Qr := Qr) (Q := Q) hconv hrate_lo
  have hhi := tendsto_integral_exp_abs (Qr := Qr) (Q := Q) hconv hrate_hi
  have hdistlo : dist (lam - dlt / 2) lam < η := by
    rw [Real.dist_eq, show lam - dlt / 2 - lam = -(dlt / 2) by ring, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < dlt / 2)]
    linarith
  have hdisthi : dist (lam + dlt / 2) lam < η := by
    rw [Real.dist_eq, show lam + dlt / 2 - lam = dlt / 2 by ring,
      abs_of_pos (by linarith : (0:ℝ) < dlt / 2)]
    linarith
  have hcloselo : dist (∫ y, Real.exp (-((lam - dlt / 2) * |y|)) ∂(Q : Measure ℝ))
      (∫ y, Real.exp (-(lam * |y|)) ∂(Q : Measure ℝ)) < ε / 3 :=
    hη hdistlo hrate_lo
  have hclosehi : dist (∫ y, Real.exp (-((lam + dlt / 2) * |y|)) ∂(Q : Measure ℝ))
      (∫ y, Real.exp (-(lam * |y|)) ∂(Q : Measure ℝ)) < ε / 3 :=
    hη hdisthi hrate_hi
  have hband : ∀ᶠ i in L, lam - dlt / 2 ≤ c i ∧ c i ≤ lam + dlt / 2 := by
    have h1 : ∀ᶠ i in L, |c i - lam| < dlt / 2 := by
      have habs : Tendsto (fun i => |c i - lam|) L (𝓝 0) := by
        simpa using (hc.sub_const lam).abs
      exact habs.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [h1] with i hi
    rw [abs_lt] at hi
    exact ⟨by linarith [hi.1, hi.2], by linarith [hi.1, hi.2]⟩
  rw [Real.dist_eq] at hcloselo hclosehi
  filter_upwards [hband,
    hlo.eventually (Metric.ball_mem_nhds _ (by linarith : (0:ℝ) < ε / 3)),
    hhi.eventually (Metric.ball_mem_nhds _ (by linarith : (0:ℝ) < ε / 3))] with i hb hloi hhii
  rw [Real.dist_eq] at hloi hhii
  have hmono_lo : ∫ y, Real.exp (-(c i * |y|)) ∂(Qr i : Measure ℝ)
      ≤ ∫ y, Real.exp (-((lam - dlt / 2) * |y|)) ∂(Qr i : Measure ℝ) :=
    integral_exp_abs_anti (c := c i) (c' := lam - dlt / 2) hrate_lo.le hb.1
  have hmono_hi : ∫ y, Real.exp (-((lam + dlt / 2) * |y|)) ∂(Qr i : Measure ℝ)
      ≤ ∫ y, Real.exp (-(c i * |y|)) ∂(Qr i : Measure ℝ) :=
    integral_exp_abs_anti (c := lam + dlt / 2) (c' := c i) (le_trans hrate_lo.le hb.1) hb.2
  rw [Real.dist_eq, abs_lt]
  constructor
  · have h1 := (abs_lt.mp hhii).1
    have h2 := (abs_lt.mp hclosehi).1
    linarith
  · have h1 := (abs_lt.mp hloi).2
    have h2 := (abs_lt.mp hcloselo).2
    linarith

/-- Moving-rate exponential form for the size-biased laws. -/
theorem tendsto_integral_exp_abs_sizeBiasedLaw_of_tendsto_rate
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    [∀ r, IsProbabilityMeasure (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))]
    [IsProbabilityMeasure Qinf]
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
        (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    {c : ℝ → ℝ} {lam : ℝ} (hc : Tendsto c atTop (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun r => ∫ y, Real.exp (-(c r * |y|))
        ∂(PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r))) atTop
      (𝓝 (∫ y, Real.exp (-(lam * |y|)) ∂Qinf)) := by
  have hmain := tendsto_integral_exp_abs_of_tendsto_rate (L := atTop)
    (Qr := fun r => Measure.toProbabilityMeasure
      (PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw (mu r)))
    (Q := Measure.toProbabilityMeasure Qinf) hconv hc hlam
  simpa only [Measure.coe_toProbabilityMeasure] using hmain

/-- **Check: chi-square, constant sequence, moving exponential rate**, in closed form
`(√(1+2(λ+1/(n+1))))⁻¹ → (√(1+2λ))⁻¹`. -/
theorem chiSquare_constant_sequence_moving_rate_exp {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (Real.sqrt (1 + 2 * (lam + 1 / ((n : ℝ) + 1))))⁻¹) atTop
      (𝓝 ((Real.sqrt (1 + 2 * lam))⁻¹)) := by
  have hrate : Tendsto (fun n : ℕ => lam + 1 / ((n : ℝ) + 1)) atTop (𝓝 lam) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds.add h)
  have hmain := tendsto_integral_exp_abs_of_tendsto_rate (L := atTop)
    (Qr := fun _ => Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf)
    (Q := Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf)
    tendsto_const_nhds hrate hlam
  have hfun : Tendsto (fun n : ℕ => ∫ y, Real.exp (-((lam + 1 / ((n : ℝ) + 1)) * |y|))
      ∂PercLib.CriticalLRP.Anchor.Qinf) atTop
      (𝓝 (∫ y, Real.exp (-(lam * |y|)) ∂PercLib.CriticalLRP.Anchor.Qinf)) := by
    simpa only [Measure.coe_toProbabilityMeasure] using hmain
  have hgoal : Tendsto (fun n : ℕ => (Real.sqrt (1 + 2 * (lam + 1 / ((n : ℝ) + 1))))⁻¹)
      atTop (𝓝 (∫ y, Real.exp (-(lam * |y|)) ∂PercLib.CriticalLRP.Anchor.Qinf)) := by
    refine hfun.congr' ?_
    filter_upwards with n
    exact exp_abs_Qinf_value (by positivity)
  rwa [exp_abs_Qinf_value hlam.le] at hgoal

/-! ## 11. Axiom audit -/

#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_exp_abs
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_exp_mul
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_laplace
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.integral_kern_eq_layerCake
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_kern
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_kern_of_tendsto_rate
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_kern_comp
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_exp_abs_atTop
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.sizeBiasedLaw_singleton_zero
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_kern_sizeBiasedLaw
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_kern_scale_selection
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_exp_abs_sizeBiasedLaw
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.integral_kern_dirac_zero_ne_layerCake
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_kern_nhdsNE_zero
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.kern_not_continuousAt_zero
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.chiSquare_constant_sequence_moving_rate
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.chiSquare_exp_abs_atTop
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.hker_of_weak_convergence
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.continuousOn_exp_abs
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.integral_exp_abs_anti
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_exp_abs_of_tendsto_rate
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.tendsto_integral_exp_abs_sizeBiasedLaw_of_tendsto_rate
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.chiSquare_constant_sequence_moving_rate_exp
#print axioms PercLib.CriticalLRP.Analysis.I32Weak.hexp_of_weak_convergence


end PercLib.CriticalLRP.Analysis.I32Weak
