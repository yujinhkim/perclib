/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Normalized triangle-ball averages

The uncut source-model definitions are in `TriangleAverage/Defs.lean`; this
module is proof-only. It proves two-scale and Cesàro estimates, and conditional
upper/positive-part defect bounds. It does not establish the uncut critical
susceptibility finiteness, model tail decay, or the defect sign required for a
full two-sided defect limit.

Reviewed from Ultramath `smwtqkdul`, member `m2`, `C2.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.TriangleAverage.Defs
public import PercLib.CriticalLRP.Correlation.I411.RealQuotient

/-! # Two-scale bounds and conditional positive-part vanishing of the uncut defect -/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal BigOperators Topology

namespace PercLib.CriticalLRP.TriangleAverage

open PercLib.CriticalLRP.I411
open PercLib.CriticalLRP.VolumeMoments
open PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

/-! ## Lemma I.4.11 with the windowed triangle diagram explicit -/

/-- **Lemma I.4.11 (landed finite-moment form), with the windowed diagram
`Σ_{y∈B} ∇(0,y)` as the bound.**  All three moments are made finite by the three
explicit finiteness hypotheses; nothing else is assumed. -/
theorem cE1_le_windowDiagram_div_card {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (hAfin : (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w) ≠ ∞)
    (hJfin : (∫⁻ ω, Percolation.cardFun (cluster ω 0) *
        ∑ y ∈ B, Percolation.cardFun (cluster ω y)
          ∂(longRangeMeasure J hJ β)) ≠ ∞)
    (hDfin : (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b *
          twoPointFunction J hJ β b y) ≠ ∞) :
    cE1 (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β)).toReal
        (∫⁻ ω, Percolation.cardFun (cluster ω 0) *
          ∑ y ∈ B, Percolation.cardFun (cluster ω y)
            ∂(longRangeMeasure J hJ β)).toReal
        (∫⁻ ω, ((B.filter fun y => y ∈ cluster ω 0).card : ℝ≥0∞) *
          (Percolation.cardFun (cluster ω 0) *
            Percolation.cardFun (cluster ω 0))
            ∂(longRangeMeasure J hJ β)).toReal
        B.card ≤
      (B.card : ℝ)⁻¹ *
        (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b *
            twoPointFunction J hJ β b y).toReal :=
  lemma_I_4_11_of_finite hJinv hJ β B hB hAfin hJfin hDfin

/-! ## The ball sum of `∇`, and the defect bound in the paper's shape -/

/-- The finset sum over the ball is the `ballSum` of the same weight. -/
theorem ballSum_finset (M : SourceModelData) (f : M.V → ℝ≥0∞) (r : ℝ) :
    ∑ x ∈ ballFinset M r, f x = BallAverage.ballSum M f r := by
  have hfin : (M.ball r).Finite := BallAverage.ball_finite M r
  rw [BallAverage.ballSum, tsum_eq_sum]
  · refine Finset.sum_congr rfl fun x hx => ?_
    exact (Set.indicator_of_mem (hfin.mem_toFinset.mp hx) f).symm
  · intro x hx
    exact Set.indicator_of_notMem (fun h => hx (hfin.mem_toFinset.mpr h)) f

/-- Any weight bounded by `∇_0` has a finite sum over a finite window: the
windowed triangle diagram is finite under the triangle condition in sup form. -/
theorem sum_nabla_ne_top (M : SourceModelData) {f : M.V → ℝ≥0∞}
    (hT : BallAverage.nablaSup M f 0 ≠ ⊤) (r : ℝ) :
    (∑ y ∈ ballFinset M r, f y) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (Finset.sum_le_card_nsmul (ballFinset M r) f _
    fun y _ => BallAverage.le_nablaSup_zero M f y)
  rw [nsmul_eq_mul]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hT

/-- **Lemma I.4.11 at the configured model, in the paper's shape.**
`E_{1,r} ≤ |B_r|^{-1} Σ_{y ∈ B_r} ∇(0,y)`, with the triangle condition in sup form
as the only new input. -/
theorem defect_le_normalized_ballSum (M : SourceModelData) (r : ℝ)
    (hT : BallAverage.nablaSup M (nabla M) 0 ≠ ⊤) (hAfin : suscept M ≠ ⊤)
    (hJfin : winMoment M r ≠ ⊤) (hne : (ballFinset M r).Nonempty) :
    defect M r ≤ (BallAverage.ballSum M (nabla M) r).toReal / ((M.ball r).ncard : ℝ) := by
  have hDfin : (∑ y ∈ ballFinset M r, ∑' a : M.V, ∑' b : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 a *
        twoPointFunction M.kernel M.kernel_nonneg M.betaCrit a b *
          twoPointFunction M.kernel M.kernel_nonneg M.betaCrit b y) ≠ ⊤ :=
    sum_nabla_ne_top M hT r
  have hcard : (ballFinset M r).card = (M.ball r).ncard := ballFinset_card M r
  have hmain := cE1_le_windowDiagram_div_card (J := M.kernel) (by
      intro a e
      exact SourceModelData.kernel_shift M a e) M.kernel_nonneg M.betaCrit
    (ballFinset M r) hne hAfin hJfin hDfin
  rw [hcard] at hmain
  rw [← ballSum_finset M (nabla M) r]
  simp only [defect, originMass, winMoment, sameMoment, nabla, SourceModelData.law,
    ballFinset_card]
  refine hmain.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, mul_comm]

/-! ## The lattice balls have diverging cardinality -/

/-- `|B_r| → ∞` along the lattice balls of the configured norm.  This is the
landed lattice-ball sandwich `(r - C)^d ≤ |B_r|` (`BallAverage.ball_ncard_ge`),
used only through its lower half. -/
theorem tendsto_ball_ncard (M : SourceModelData) :
    Tendsto (fun r : ℝ => ((M.ball r).ncard : ℝ)) atTop atTop := by
  obtain ⟨C, hC⟩ := BallAverage.exists_cube_bound M
  have hC0 : 0 ≤ C := BallAverage.cube_bound_nonneg M hC
  refine tendsto_atTop.2 fun b => ?_
  refine eventually_atTop.2 ⟨C + max 1 (b + 1), fun r hr => ?_⟩
  have hrC : C < r := by
    have := le_max_left (1 : ℝ) (b + 1); linarith
  have hm1 : 1 ≤ max 1 (b + 1) := le_max_left _ _
  have hrm : 1 ≤ r - C := by
    have := le_max_right (1 : ℝ) (b + 1); linarith
  have hb : b ≤ r - C := by
    have := le_max_right (1 : ℝ) (b + 1); linarith
  have hge := BallAverage.ball_ncard_ge M hC hC0 hrC
  have h1 : b ≤ (r - C) ^ M.d := by
    calc b ≤ r - C := hb
      _ = (r - C) ^ 1 := (pow_one _).symm
      _ ≤ (r - C) ^ M.d := pow_le_pow_right₀ hrm M.hd
  linarith

/-- `0` lies in every ball of nonnegative radius. -/
theorem ballFinset_nonempty (M : SourceModelData) {r : ℝ} (hr : 0 ≤ r) :
    (ballFinset M r).Nonempty := by
  have h0 : (0 : M.V) ∈ M.ball r := by
    change M.S.ρ (toVec (0 : M.V)) ≤ r
    have hz : toVec (0 : M.V) = 0 := by
      funext i
      simp [toVec]
    rw [hz, M.S.ρ_zero]
    exact hr
  exact ⟨0, (BallAverage.ball_finite M r).mem_toFinset.mpr h0⟩

/-! ## Two elementary real limits -/

/-- `x ^ a → 0` at `+∞` for `a < 0`. -/
theorem tendsto_rpow_neg_atTop_zero {a : ℝ} (ha : a < 0) :
    Tendsto (fun x : ℝ => x ^ a) atTop (𝓝 0) := by
  have hpos : 0 < -a := by linarith
  have h1 : Tendsto (fun x : ℝ => (x ^ (-a))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hpos)
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx a, inv_inv]

/-- `√r → +∞`. -/
theorem tendsto_sqrt_atTop : Tendsto Real.sqrt atTop atTop := by
  rw [tendsto_atTop]
  intro b
  refine eventually_atTop.2 ⟨b ^ 2 + 1, fun r hr => ?_⟩
  rcases le_or_gt 0 b with hb | hb
  · have hr0 : (0 : ℝ) ≤ r := by nlinarith [sq_nonneg b]
    rw [Real.le_sqrt hb hr0]
    nlinarith
  · exact hb.le.trans (Real.sqrt_nonneg r)

/-! ## The quantitative two-scale bound, and vanishing of the normalized ball sum -/

/-- **Quantitative two-scale bound for the normalized ball sum.**
`r^{-d} Σ_{x ∈ B_r} f x ≤ 2^d ( ∇_0 r^{-d/2} + ∇_{√r} )` eventually, where
`∇_0 = sup_x f x` and `∇_r = sup_{‖x‖ ≥ r} f x`.

This is the source's split of `B_r` at `R = √r` (`r ≥ 1`) with the honest lattice-ball
cardinalities of `BallAverage.normalized_ballSum_le`.  It carries the *rate*, not only
the limit, which is what the log-integrability of the error in Proposition I.4.2
consumes: `E_{1,r} ⪯ ∇_0 r^{-d/2} + ∇_{√r}`.  The only hypothesis is the
finiteness `∇_0 < ∞`, needed to take `toReal` of the two-scale bound. -/
theorem normalized_ballSum_le_two_scale (M : SourceModelData) (f : M.V → ℝ≥0∞)
    (hfin : BallAverage.nablaSup M f 0 ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop,
      (BallAverage.ballSum M f r).toReal / r ^ M.d ≤
        (2 : ℝ) ^ M.d * ((BallAverage.nablaSup M f 0).toReal * r ^ (-(M.d : ℝ) / 2)) +
          (2 : ℝ) ^ M.d * (BallAverage.nablaSup M f (Real.sqrt r)).toReal := by
  obtain ⟨C, hC⟩ := BallAverage.exists_cube_bound M
  have hC0 : 0 ≤ C := BallAverage.cube_bound_nonneg M hC
  filter_upwards [eventually_ge_atTop (max 1 (C + 1)),
    eventually_ge_atTop (C ^ 2 + 1)] with r hr1 hr2
  have hr1' : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr1
  have hrC : C < r := by
    have h := le_max_right (1 : ℝ) (C + 1); linarith
  have hrC2 : C < Real.sqrt r := by
    rw [Real.lt_sqrt hC0]
    linarith
  have h0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr1'
  have hs : (0 : ℝ) ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsle : BallAverage.nablaSup M f (Real.sqrt r) ≤ BallAverage.nablaSup M f 0 :=
    BallAverage.nablaSup_anti M f hs
  have hfins : BallAverage.nablaSup M f (Real.sqrt r) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin hsle
  have hleft : ENNReal.ofReal ((2 : ℝ) ^ M.d) *
      ((BallAverage.nablaSup M f 0) *
        ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top)
  have hright : ENNReal.ofReal ((2 : ℝ) ^ M.d) *
      BallAverage.nablaSup M f (Real.sqrt r) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfins
  have hmain := BallAverage.normalized_ballSum_le M f hC hC0 hr1' hrC hrC2
  have hpowr1 : (0 : ℝ) ≤ r ^ (-(M.d : ℝ)) := Real.rpow_nonneg h0.le _
  have hpowr2 : (0 : ℝ) ≤ r ^ (-(M.d : ℝ) / 2) := Real.rpow_nonneg h0.le _
  have htwo : (0 : ℝ) ≤ (2 : ℝ) ^ M.d := pow_nonneg (by norm_num) M.d
  have htoReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hleft, hright⟩) hmain
  rw [ENNReal.toReal_add hleft hright] at htoReal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpowr1,
    ENNReal.toReal_ofReal hpowr2, ENNReal.toReal_ofReal htwo] at htoReal
  have hrw : (BallAverage.ballSum M f r).toReal / r ^ M.d =
      r ^ (-(M.d : ℝ)) * (BallAverage.ballSum M f r).toReal := by
    rw [Real.rpow_neg h0.le, Real.rpow_natCast, div_eq_mul_inv, mul_comm]
  rw [hrw]
  exact htoReal

/-- **`r^{-d} Σ_{x ∈ B_r} f x → 0`** from the triangle condition in sup form
`∇_0 < ∞` and the uniform tail decay `∇_r → 0`.

This is `normalized_ballSum_le_two_scale` followed by the two elementary limits
`r^{-d/2} → 0` and `∇_{√r} → 0`.  No summability of `f` is assumed: this is the
statement that `Analysis/BallAverage` explicitly leaves open. -/
theorem tendsto_normalized_ballSum_toReal (M : SourceModelData) (f : M.V → ℝ≥0∞)
    (hfin : BallAverage.nablaSup M f 0 ≠ ⊤)
    (htail : Tendsto (BallAverage.nablaSup M f) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (BallAverage.ballSum M f r).toReal / r ^ M.d) atTop (𝓝 0) := by
  have hstep := normalized_ballSum_le_two_scale M f hfin
  -- both summands tend to `0`
  have h1 : Tendsto (fun r : ℝ => (2 : ℝ) ^ M.d *
      ((BallAverage.nablaSup M f 0).toReal * r ^ (-(M.d : ℝ) / 2))) atTop (𝓝 0) := by
    have hneg : (-(M.d : ℝ) / 2) < 0 := by
      have hd : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
      linarith
    have hc := (tendsto_rpow_neg_atTop_zero hneg).const_mul
      (BallAverage.nablaSup M f 0).toReal
    simpa using hc.const_mul ((2 : ℝ) ^ M.d)
  have h2 : Tendsto (fun r : ℝ => (2 : ℝ) ^ M.d *
      (BallAverage.nablaSup M f (Real.sqrt r)).toReal) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun r : ℝ => BallAverage.nablaSup M f (Real.sqrt r)) atTop (𝓝 0) :=
      htail.comp tendsto_sqrt_atTop
    have hc := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) ENNReal.zero_ne_top).comp hcomp
    simpa using hc.const_mul ((2 : ℝ) ^ M.d)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hg : Tendsto (fun r : ℝ => (2 : ℝ) ^ M.d *
        ((BallAverage.nablaSup M f 0).toReal * r ^ (-(M.d : ℝ) / 2)) +
      (2 : ℝ) ^ M.d * (BallAverage.nablaSup M f (Real.sqrt r)).toReal) atTop (𝓝 0) := by
    simpa using h1.add h2
  have hsmall : ∀ᶠ r : ℝ in atTop, (2 : ℝ) ^ M.d *
        ((BallAverage.nablaSup M f 0).toReal * r ^ (-(M.d : ℝ) / 2)) +
      (2 : ℝ) ^ M.d * (BallAverage.nablaSup M f (Real.sqrt r)).toReal < ε :=
    (tendsto_order.1 hg).2 ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hsmall.and hstep)
  refine ⟨max R 0, fun r hr => ?_⟩
  have hrR : R ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : (0 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  obtain ⟨h1', h2'⟩ := hR r hrR
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg (pow_nonneg hr0 M.d))]
  linarith

/-! ## The source defect vanishes -/

/-- The lattice-ball ratio `r^d / |B_r|` is eventually at most `2^d`: the lower
half of the landed lattice-ball sandwich. -/
theorem eventually_pow_div_ncard_le (M : SourceModelData) :
    ∀ᶠ r : ℝ in atTop, r ^ M.d / ((M.ball r).ncard : ℝ) ≤ (2 : ℝ) ^ M.d := by
  obtain ⟨C, hC⟩ := BallAverage.exists_cube_bound M
  have hC0 : 0 ≤ C := BallAverage.cube_bound_nonneg M hC
  filter_upwards [eventually_ge_atTop (C + max 1 (2 * C))] with r hr
  have hrC : C < r := by
    have := le_max_left (1 : ℝ) (2 * C); linarith
  have hr2C : 2 * C ≤ r := by
    have := le_max_right (1 : ℝ) (2 * C); linarith
  have hge := BallAverage.ball_ncard_ge M hC hC0 hrC
  have hncpos : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    have hp : (0 : ℝ) < (r - C) ^ M.d := pow_pos (by linarith) M.d
    linarith
  have hle : r ^ M.d ≤ (2 : ℝ) ^ M.d * ((M.ball r).ncard : ℝ) := by
    have h2 : r ≤ 2 * (r - C) := by linarith
    have hp : r ^ M.d ≤ (2 * (r - C)) ^ M.d := pow_le_pow_left₀ (by linarith) h2 M.d
    rw [mul_pow] at hp
    have h2d : (0 : ℝ) < (2 : ℝ) ^ M.d := pow_pos (by norm_num) M.d
    nlinarith [hp, hge, h2d]
  rw [div_le_iff₀ hncpos]
  exact hle

/-- Splitting the ball average through `r^d`:
`B/|B_r| = (B/r^d) · (r^d/|B_r|)`. -/
theorem ballSum_div_ncard_eq (M : SourceModelData) (f : M.V → ℝ≥0∞) {r : ℝ}
    (hr : 0 < r) (hnc : 0 < ((M.ball r).ncard : ℝ)) :
    (BallAverage.ballSum M f r).toReal / ((M.ball r).ncard : ℝ) =
      ((BallAverage.ballSum M f r).toReal / r ^ M.d) *
        (r ^ M.d / ((M.ball r).ncard : ℝ)) := by
  have hpow : r ^ M.d ≠ 0 := (pow_pos hr M.d).ne'
  have hn : ((M.ball r).ncard : ℝ) ≠ 0 := hnc.ne'
  field_simp

/-- **Quantitative bound for the source defect**: `E_{1,r} ⪯ ∇_0 r^{-d/2} + ∇_{√r}`
eventually.  This is `defect_le_normalized_ballSum` composed with the two-scale
bound and with `r^d/|B_r| ≤ 2^d`.  It is the rate form of
`defect_upper_tendsto_zero_of_tail`, and it is what the log-integrability of the
error in Proposition I.4.2 (Lemma I.4.13) consumes. -/
theorem defect_le_two_scale (M : SourceModelData)
    (hT : BallAverage.nablaSup M (nabla M) 0 ≠ ⊤) (hAfin : suscept M ≠ ⊤)
    (hJfin : ∀ r : ℝ, winMoment M r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, defect M r ≤
      (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
        ((BallAverage.nablaSup M (nabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2) +
          (BallAverage.nablaSup M (nabla M) (Real.sqrt r)).toReal)) := by
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ M.d := pow_nonneg (by norm_num) M.d
  filter_upwards [normalized_ballSum_le_two_scale M (nabla M) hT,
    eventually_pow_div_ncard_le M, eventually_gt_atTop (0 : ℝ)] with r h2s hrat h0
  have hde := defect_le_normalized_ballSum M r hT hAfin (hJfin r)
    (ballFinset_nonempty M h0.le)
  have hnc : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    have hne := ballFinset_nonempty M h0.le
    have hc : 0 < (ballFinset M r).card := Finset.card_pos.mpr hne
    rw [ballFinset_card] at hc
    exact_mod_cast hc
  have hnonneg : (0 : ℝ) ≤ (BallAverage.ballSum M (nabla M) r).toReal / r ^ M.d :=
    div_nonneg ENNReal.toReal_nonneg (pow_nonneg h0.le M.d)
  calc defect M r
      ≤ (BallAverage.ballSum M (nabla M) r).toReal / ((M.ball r).ncard : ℝ) := hde
    _ = ((BallAverage.ballSum M (nabla M) r).toReal / r ^ M.d) *
          (r ^ M.d / ((M.ball r).ncard : ℝ)) :=
        ballSum_div_ncard_eq M (nabla M) h0 hnc
    _ ≤ ((BallAverage.ballSum M (nabla M) r).toReal / r ^ M.d) * (2 : ℝ) ^ M.d :=
        mul_le_mul_of_nonneg_left hrat hnonneg
    _ ≤ ((2 : ℝ) ^ M.d * ((BallAverage.nablaSup M (nabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2) +
          (BallAverage.nablaSup M (nabla M) (Real.sqrt r)).toReal)) * (2 : ℝ) ^ M.d := by
        refine mul_le_mul_of_nonneg_right ?_ h2d
        rw [mul_add]
        exact h2s
    _ = (2 : ℝ) ^ M.d * ((2 : ℝ) ^ M.d *
          ((BallAverage.nablaSup M (nabla M) 0).toReal * r ^ (-(M.d : ℝ) / 2) +
            (BallAverage.nablaSup M (nabla M) (Real.sqrt r)).toReal)) := by ring

/-- **The source defect vanishes along the lattice balls.**  Under the triangle
condition in sup form and the uniform tail decay of `∇`, the defect `E_{1,r}` of
Lemma I.4.11 is eventually below every positive `ε`.

The window moment and the susceptibility are the two finiteness hypotheses
inherited from the landed Lemma I.4.11; they are kept explicit and are *not*
derived here. -/
theorem defect_upper_tendsto_zero_of_tail (M : SourceModelData)
    (hT : BallAverage.nablaSup M (nabla M) 0 ≠ ⊤) (hAfin : suscept M ≠ ⊤)
    (hJfin : ∀ r : ℝ, winMoment M r ≠ ⊤)
    (htail : Tendsto (BallAverage.nablaSup M (nabla M)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ r : ℝ in atTop, defect M r ≤ ε := by
  intro ε hε
  have hv := tendsto_normalized_ballSum_toReal M (nabla M) hT htail
  have hg : Tendsto (fun r : ℝ =>
      (2 : ℝ) ^ M.d * ((BallAverage.ballSum M (nabla M) r).toReal / r ^ M.d))
      atTop (𝓝 0) := by
    have hc := hv.const_mul ((2 : ℝ) ^ M.d)
    simpa [mul_comm] using hc
  have hsmall : ∀ᶠ r : ℝ in atTop,
      (2 : ℝ) ^ M.d * ((BallAverage.ballSum M (nabla M) r).toReal / r ^ M.d) < ε :=
    (tendsto_order.1 hg).2 ε hε
  filter_upwards [hsmall, eventually_pow_div_ncard_le M, eventually_gt_atTop (0 : ℝ)]
    with r hlt hrat h0
  have hde := defect_le_normalized_ballSum M r hT hAfin (hJfin r)
    (ballFinset_nonempty M h0.le)
  have hrpos : (0 : ℝ) < r := h0
  have hnc : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    have hne := ballFinset_nonempty M h0.le
    have hc : 0 < (ballFinset M r).card := Finset.card_pos.mpr hne
    rw [ballFinset_card] at hc
    exact_mod_cast hc
  have hpow : (0 : ℝ) < r ^ M.d := pow_pos hrpos M.d
  calc defect M r ≤ (BallAverage.ballSum M (nabla M) r).toReal / ((M.ball r).ncard : ℝ) := hde
    _ = ((BallAverage.ballSum M (nabla M) r).toReal / r ^ M.d) *
          (r ^ M.d / ((M.ball r).ncard : ℝ)) :=
        ballSum_div_ncard_eq M (nabla M) hrpos hnc
    _ ≤ ((BallAverage.ballSum M (nabla M) r).toReal / r ^ M.d) * (2 : ℝ) ^ M.d :=
        mul_le_mul_of_nonneg_left hrat (by positivity)
    _ = (2 : ℝ) ^ M.d * ((BallAverage.ballSum M (nabla M) r).toReal / r ^ M.d) := by ring
    _ ≤ ε := hlt.le

/-- **Two-sided vanishing of the positive part of the source defect.**  The signed
statement `0 ≤ E_{1,r}` is not available at the uncut law from the landed
comparison layer (it is the sign of the coupling identity behind Lemma I.4.12), so
this is the honest two-sided `Tendsto` consequence of the upper bound. -/
theorem defect_posPart_tendsto_zero_of_tail (M : SourceModelData)
    (hT : BallAverage.nablaSup M (nabla M) 0 ≠ ⊤) (hAfin : suscept M ≠ ⊤)
    (hJfin : ∀ r : ℝ, winMoment M r ≠ ⊤)
    (htail : Tendsto (BallAverage.nablaSup M (nabla M)) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => max 0 (defect M r)) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hev : ∀ᶠ r : ℝ in atTop, max 0 (defect M r) ≤ ε / 2 := by
    filter_upwards [defect_upper_tendsto_zero_of_tail M hT hAfin hJfin htail (ε / 2) hε2]
      with r hr
    exact max_le hε2.le hr
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left (0 : ℝ) (defect M n))]
  have := hN n hn
  linarith

/-! ## The unconditional analytic half in summable-kernel form

The source's Case 2 uses only that `∇(0,·)` is summable
(`∇(0,x) ⪯ ‖x‖^{-d+6}`, (I.4.11)); then the normalized ball average of `∇` over
any expanding window vanishes, with no decay rate and no monotonicity. -/

/-- **Cesàro vanishing of a finite-total-mass kernel over an expanding window.**
If `Σ_x f x` is finite and the window cardinalities diverge, then the normalized
average `|B r|^{-1} Σ_{x ∈ B r} f x` tends to `0`.

No translation invariance is needed: the whole content is
`Σ_{x ∈ B r} f x ≤ Σ_x f x` together with `|B r| → ∞`. -/
theorem summable_kernel_cesaro_tendsto_zero {ι : Type*} {f : ι → ℝ≥0∞}
    (hf : (∑' x, f x) ≠ ⊤) {B : ℝ → Finset ι}
    (hB : Tendsto (fun r : ℝ => ((B r).card : ℝ)) atTop atTop) :
    Tendsto (fun r : ℝ => ((B r).card : ℝ)⁻¹ * (∑ x ∈ B r, f x).toReal)
      atTop (𝓝 0) := by
  have hbound : ∀ r : ℝ, ((B r).card : ℝ)⁻¹ * (∑ x ∈ B r, f x).toReal ≤
      ((B r).card : ℝ)⁻¹ * (∑' x, f x).toReal := by
    intro r
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hf (ENNReal.sum_le_tsum (B r))) ?_
    positivity
  have hzero : Tendsto (fun r : ℝ => ((B r).card : ℝ)⁻¹ * (∑' x, f x).toReal)
      atTop (𝓝 0) := by
    refine (Tendsto.div_atTop tendsto_const_nhds hB
      (a := (∑' x, f x).toReal)).congr' ?_
    filter_upwards with r
    rw [div_eq_mul_inv, mul_comm]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun r => ?_) (fun r => hbound r)
  positivity

end PercLib.CriticalLRP.TriangleAverage

/-! ## Axiom audit (campaign protocol: one line per new theorem) -/

#print axioms PercLib.CriticalLRP.TriangleAverage.ballFinset_card
#print axioms PercLib.CriticalLRP.TriangleAverage.cE1_le_windowDiagram_div_card
#print axioms PercLib.CriticalLRP.TriangleAverage.suscept_le_triMass
#print axioms PercLib.CriticalLRP.TriangleAverage.ballSum_finset
#print axioms PercLib.CriticalLRP.TriangleAverage.sum_nabla_ne_top
#print axioms PercLib.CriticalLRP.TriangleAverage.defect_le_normalized_ballSum
#print axioms PercLib.CriticalLRP.TriangleAverage.tendsto_ball_ncard
#print axioms PercLib.CriticalLRP.TriangleAverage.ballFinset_nonempty
#print axioms PercLib.CriticalLRP.TriangleAverage.tendsto_rpow_neg_atTop_zero
#print axioms PercLib.CriticalLRP.TriangleAverage.tendsto_sqrt_atTop
#print axioms PercLib.CriticalLRP.TriangleAverage.normalized_ballSum_le_two_scale
#print axioms PercLib.CriticalLRP.TriangleAverage.tendsto_normalized_ballSum_toReal
#print axioms PercLib.CriticalLRP.TriangleAverage.eventually_pow_div_ncard_le
#print axioms PercLib.CriticalLRP.TriangleAverage.ballSum_div_ncard_eq
#print axioms PercLib.CriticalLRP.TriangleAverage.defect_le_two_scale
#print axioms PercLib.CriticalLRP.TriangleAverage.defect_upper_tendsto_zero_of_tail
#print axioms PercLib.CriticalLRP.TriangleAverage.defect_posPart_tendsto_zero_of_tail
#print axioms PercLib.CriticalLRP.TriangleAverage.summable_kernel_cesaro_tendsto_zero
