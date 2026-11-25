/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The weak-convergence / integral layer for Proposition I.3.2

This file supplies the missing layer that turns weak convergence of the rescaled
size-biased cluster-volume laws `Q_r ⇒ Q_∞` into the kernel-integral limits used in
Proposition I.3.2 of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1.

Everything here is stated for abstract families of probability measures on `ℝ`, so it
applies verbatim to `PercLib.CriticalLRP.Analysis.I32.sizeBiasedLaw mu r`.

## The mathematical content

* `kern s y = (1 - e^{-s y})/y` is the paper's kernel.  In Lean the formula takes the
  junk value `0` at `y = 0`, which is **discontinuous**: the true limit is `s`.
  `kernE s` is the continuous extension (`kernE s 0 = s`), and `kernB s y = kernE s |y|`
  is its bounded-continuous version on `ℝ` (bounded by `s` for `s ≥ 0`).  The raw kernel
  and the bounded-continuous kernel agree off `Iic 0`, hence a.e. for laws carried by
  `(0,∞)`; this is exactly where the source hypotheses "nonnegative cluster volume" and
  "no atom at zero" are used.
* `expK c y = e^{-c|y|}` is bounded continuous for `c ≥ 0`, uniformly in `y`.
* Weak convergence gives, for every `s > 0`,
  `∫ kern s dQ_r → ∫ kern s dQ_∞` and `∫ expK c dQ_r → ∫ expK c dQ_∞`
  (Mathlib's `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`).
* Moving rates: if `c_r → λ > 0` then `∫ kern (c_r) dQ_r → ∫ kern λ dQ_∞`
  (Lipschitz bound in the rate, uniformly in the law), and likewise for `expK`
  (explicit `ε`/`R` truncation bound).  Both are stated for an arbitrary index filter
  and are reparametrisation-stable, so no moving parameter is silently frozen.
* No atom at `0`: `∫ expK λ dQ_∞ → 0` as `λ → ∞`, with the explicit bound
  `∫ expK λ dQ ≤ Q (Ioo (-δ) δ) + e^{-λδ}` for every `δ > 0`.

## Added hypotheses (all explicit)

Every theorem below states them as arguments; none is an instance or a default:

* `Q`, `Q i` are probability measures (`IsProbabilityMeasure` / `ProbabilityMeasure`);
* support: `Q (Iio 0) = 0` (nonnegative cluster volume);
* no atom at zero: `Q {0} = 0`;
* rates are positive (`0 < s`, `0 < λ`) as in the paper.

No moment bounds, no uniform integrability and no `sorry`/custom axioms are used.
-/

module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction

set_option maxHeartbeats 1000000

namespace PercLib.CriticalLRP.Analysis.I32WeakConv

/-! ## 1. The kernels and their continuous extensions -/

/-- The paper's kernel `y ↦ (1 - e^{-s y})/y`.  At `y = 0` the real-valued formula takes
Lean's junk value `0`; see `kern_zero`.  The correct limiting value is the rate `s`. -/
noncomputable def kern (s y : ℝ) : ℝ := (1 - Real.exp (-(s * y))) / y

/-- The continuous extension of `kern s` to `y = 0`, with value the rate `s`. -/
noncomputable def kernE (s y : ℝ) : ℝ := if y = 0 then s else kern s y

/-- The kernel composed with `|·|`: for `s ≥ 0` this is a bounded continuous function on
`ℝ`, agreeing with `kern s` on `(0,∞)`.  This is the test function fed to the
Portmanteau theorem. -/
noncomputable def kernB (s y : ℝ) : ℝ := kernE s |y|

/-- The exponential kernel `y ↦ e^{-c |y|}`. -/
noncomputable def expK (c y : ℝ) : ℝ := Real.exp (-(c * |y|))

@[simp] theorem kern_zero (s : ℝ) : kern s 0 = 0 := by simp [kern]

@[simp] theorem kernE_zero (s : ℝ) : kernE s 0 = s := by simp [kernE]

theorem kernE_of_ne {s y : ℝ} (hy : y ≠ 0) : kernE s y = kern s y := by simp [kernE, hy]

theorem kernB_of_pos {s y : ℝ} (hy : 0 < y) : kernB s y = kern s y := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp [kernB, kernE, abs_of_pos hy, hy0]

/-! ### Elementary bounds for the kernel (after the source's Lemma) -/

theorem kern_nonneg {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) : 0 ≤ kern s y := by
  unfold kern
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp
  · have hle : Real.exp (-(s * y)) ≤ 1 := by
      have : -(s * y) ≤ 0 := by nlinarith
      simpa using Real.exp_le_one_iff.mpr this
    exact div_nonneg (by linarith) h.le

theorem kern_le_rate {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) : kern s y ≤ s := by
  unfold kern
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp [hs.le]
  · rw [div_le_iff₀ h]
    have h1 : 1 - Real.exp (-(s * y)) ≤ s * y := by
      have := Real.add_one_le_exp (-(s * y))
      linarith
    linarith

theorem kern_mono_rate {y s t : ℝ} (hy : 0 ≤ y) (hst : s ≤ t) : kern s y ≤ kern t y := by
  unfold kern
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp
  · apply div_le_div_of_nonneg_right _ h.le
    have : -(t * y) ≤ -(s * y) := by nlinarith
    linarith [Real.exp_le_exp.mpr this]

/-- The two halves of the `1`-Lipschitz bound in the rate, for `0 ≤ a ≤ b`. -/
theorem kern_pair_le {y a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hy : 0 ≤ y) :
    kern a y ≤ kern b y ∧ kern b y - kern a y ≤ b - a := by
  refine ⟨kern_mono_rate hy hab, ?_⟩
  unfold kern
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, div_zero]; linarith
  · rw [div_sub_div_same, div_le_iff₀ h]
    have hexp : Real.exp (-(a * y)) ≤ 1 := by
      have : -(a * y) ≤ 0 := by nlinarith
      simpa using Real.exp_le_one_iff.mpr this
    have hkey : 1 - Real.exp (-((b - a) * y)) ≤ (b - a) * y := by
      have := Real.add_one_le_exp (-((b - a) * y))
      linarith
    have hnn : 0 ≤ 1 - Real.exp (-((b - a) * y)) := by
      have : -((b - a) * y) ≤ 0 := by nlinarith
      linarith [Real.exp_le_one_iff.mpr this]
    have hring : 1 - Real.exp (-(b * y)) - (1 - Real.exp (-(a * y)))
        = Real.exp (-(a * y)) - Real.exp (-(b * y)) := by ring
    have hfac : Real.exp (-(a * y)) - Real.exp (-(b * y))
        = Real.exp (-(a * y)) * (1 - Real.exp (-((b - a) * y))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      ring_nf
    rw [hring, hfac]
    calc Real.exp (-(a * y)) * (1 - Real.exp (-((b - a) * y)))
        ≤ 1 * (1 - Real.exp (-((b - a) * y))) :=
          mul_le_mul_of_nonneg_right hexp hnn
      _ ≤ (b - a) * y := by rw [one_mul]; exact hkey

/-- `kern · y` is `1`-Lipschitz in its rate, on nonnegative arguments. -/
theorem abs_kern_sub_kern_le {s t y : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hy : 0 ≤ y) :
    |kern s y - kern t y| ≤ |s - t| := by
  rcases le_total s t with hst | hts
  · obtain ⟨h1, h2⟩ := kern_pair_le hs hst hy
    have e1 : |kern s y - kern t y| = -(kern s y - kern t y) := abs_of_nonpos (by linarith)
    have e2 : |s - t| = t - s := by
      rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [e1, e2]; linarith
  · obtain ⟨h1, h2⟩ := kern_pair_le ht hts hy
    have e1 : |kern s y - kern t y| = kern s y - kern t y := abs_of_nonneg (by linarith)
    have e2 : |s - t| = s - t := abs_of_nonneg (by linarith)
    rw [e1, e2]; linarith

/-! ### Continuity at zero (the removable singularity) -/

theorem measurable_kern (s : ℝ) : Measurable (kern s) := by
  unfold kern; fun_prop

/-- The elementary Taylor bound behind the removable singularity:
`|(1 - e^{-s y})/y - s| ≤ s ^ 2 * |y|` for `|s y| ≤ 1`.  (From
`|e^x - 1 - x| ≤ x^2`, with `x = -(s y)`.) -/
theorem abs_kern_sub_rate_le {s y : ℝ} (hy : y ≠ 0) (hsmall : |s * y| ≤ 1) :
    |kern s y - s| ≤ s ^ 2 * |y| := by
  have hyabs : (0:ℝ) < |y| := abs_pos.mpr hy
  have hb : |Real.exp (-(s * y)) - 1 - (-(s * y))| ≤ |s * y| ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (x := -(s * y)) (by
      rw [Real.norm_eq_abs, abs_neg]; exact hsmall)
    simpa only [Real.norm_eq_abs, abs_neg] using h
  have hkey : Real.exp (-(s * y)) - 1 - (-(s * y))
      = -(1 - Real.exp (-(s * y)) - s * y) := by ring
  rw [hkey, abs_neg] at hb
  have hEq : kern s y - s = (1 - Real.exp (-(s * y)) - s * y) / y := by
    rw [kern]; field_simp
  rw [hEq, abs_div, div_le_iff₀ hyabs]
  calc |1 - Real.exp (-(s * y)) - s * y| ≤ |s * y| ^ 2 := hb
    _ = s ^ 2 * |y| ^ 2 := by rw [abs_mul, mul_pow, sq_abs]
    _ = s ^ 2 * |y| * |y| := by ring

/-- The punctured limit of the raw kernel at `0` is the rate: this is exactly the value
that the junk convention `kern s 0 = 0` throws away. -/
theorem tendsto_kern_zero {s : ℝ} (hs : 0 < s) : Tendsto (kern s) (𝓝[≠] (0:ℝ)) (𝓝 s) := by
  have hball : ∀ᶠ y in (𝓝[≠] (0:ℝ)), |s * y| < 1 := by
    have hmem : Metric.ball (0:ℝ) (1 / s) ∈ 𝓝[≠] (0:ℝ) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 (by positivity))
    filter_upwards [hmem] with y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    rw [abs_mul, abs_of_pos hs]
    have h := mul_lt_mul_of_pos_left hy hs
    rwa [mul_one_div, div_self hs.ne'] at h
  have hbound : ∀ᶠ y in (𝓝[≠] (0:ℝ)), |kern s y - s| ≤ s ^ 2 * |y| := by
    filter_upwards [hball, self_mem_nhdsWithin] with y hy hyne
    exact abs_kern_sub_rate_le hyne hy.le
  have h0 : Tendsto (fun y : ℝ => s ^ 2 * |y|) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun y : ℝ => s ^ 2 * |y|) (𝓝 (0:ℝ)) (𝓝 (s ^ 2 * |(0:ℝ)|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have habs : Tendsto (fun y : ℝ => |kern s y - s|) (𝓝[≠] (0:ℝ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun y => abs_nonneg _) hbound h0
  have hdiff : Tendsto (fun y : ℝ => kern s y - s) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  have h := hdiff.const_add s
  simpa using h

theorem continuousAt_kern {s y : ℝ} (hy : y ≠ 0) : ContinuousAt (kern s) y := by
  unfold kern
  refine ContinuousAt.div ?_ continuousAt_id (by simpa using hy)
  exact continuousAt_const.sub
    ((Real.continuous_exp.continuousAt).comp (continuousAt_const.mul continuousAt_id).neg)

theorem continuous_kernE {s : ℝ} (hs : 0 < s) : Continuous (kernE s) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · rw [continuousAt_iff_punctured_nhds, kernE_zero]
    refine (tendsto_kern_zero hs).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (kernE_of_ne ht).symm
  · refine (continuousAt_kern (s := s) hy).congr ?_
    filter_upwards [isOpen_ne.mem_nhds hy] with t ht
    exact (kernE_of_ne ht).symm

theorem continuous_kernB {s : ℝ} (hs : 0 < s) : Continuous (kernB s) :=
  (continuous_kernE hs).comp continuous_abs

theorem kernB_nonneg {s : ℝ} (hs : 0 < s) (y : ℝ) : 0 ≤ kernB s y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [kernB, kernE, hs.le]
  · rw [kernB, kernE_of_ne (abs_ne_zero.mpr hy)]
    exact kern_nonneg hs (abs_nonneg y)

theorem kernB_le_rate {s : ℝ} (hs : 0 < s) (y : ℝ) : kernB s y ≤ s := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [kernB, kernE]
  · rw [kernB, kernE_of_ne (abs_ne_zero.mpr hy)]
    exact kern_le_rate hs (abs_nonneg y)

/-- The bounded continuous kernel used for the Portmanteau step. -/
noncomputable def kernBCF (s : ℝ) (hs : 0 < s) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨kernB s, continuous_kernB hs⟩ s fun x y => by
    rw [Real.dist_eq]
    change |kernB s x - kernB s y| ≤ s
    rw [abs_sub_le_iff]
    have hx0 := kernB_nonneg hs x
    have hx1 := kernB_le_rate hs x
    have hy0 := kernB_nonneg hs y
    have hy1 := kernB_le_rate hs y
    constructor <;> linarith

@[simp] theorem kernBCF_apply (s : ℝ) (hs : 0 < s) (y : ℝ) :
    kernBCF s hs y = kernB s y := rfl

/-! ### The exponential kernel -/

theorem continuous_expK (c : ℝ) : Continuous (expK c) := by
  unfold expK; fun_prop

theorem expK_pos (c y : ℝ) : 0 < expK c y := Real.exp_pos _

theorem expK_nonneg (c y : ℝ) : 0 ≤ expK c y := (Real.exp_pos _).le

theorem expK_le_one {c : ℝ} (hc : 0 ≤ c) (y : ℝ) : expK c y ≤ 1 := by
  rw [expK, Real.exp_le_one_iff]
  have := abs_nonneg y
  nlinarith

/-- The exponential kernel as a bounded continuous function. -/
noncomputable def expKBCF (c : ℝ) (hc : 0 ≤ c) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨expK c, continuous_expK c⟩ 1 fun x y => by
    rw [Real.dist_eq]
    change |expK c x - expK c y| ≤ 1
    rw [abs_sub_le_iff]
    have hx0 := expK_nonneg c x
    have hx1 := expK_le_one hc x
    have hy0 := expK_nonneg c y
    have hy1 := expK_le_one hc y
    constructor <;> linarith

@[simp] theorem expKBCF_apply (c : ℝ) (hc : 0 ≤ c) (y : ℝ) :
    expKBCF c hc y = expK c y := rfl

/-! ## 2. Weak convergence transfers the integrals (Portmanteau) -/

/-- **Fixed-rate transfer, bounded-continuous form.**  Weak convergence of probability
laws on `ℝ` gives convergence of the integrals of the bounded continuous kernel
`kernB s` for every rate `s > 0`.  No support or atom hypothesis is needed here. -/
theorem tendsto_integral_kernB {ι : Type*} {l : Filter ι} {Q : ι → ProbabilityMeasure ℝ}
    {Qinf : ProbabilityMeasure ℝ} (hQ : Tendsto Q l (𝓝 Qinf)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun i => ∫ y, kernB s y ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ y, kernB s y ∂(Qinf : Measure ℝ))) := by
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ) (kernBCF s hs)
  simpa using h

/-- **Fixed-rate transfer for the exponential kernel.** -/
theorem tendsto_integral_expK {ι : Type*} {l : Filter ι} {Q : ι → ProbabilityMeasure ℝ}
    {Qinf : ProbabilityMeasure ℝ} (hQ : Tendsto Q l (𝓝 Qinf)) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun i => ∫ y, expK c y ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ y, expK c y ∂(Qinf : Measure ℝ))) := by
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ) (expKBCF c hc)
  simpa using h

/-! ## 3. Passing from the bounded-continuous kernel to the raw kernel -/

theorem ae_pos_of_support {Q : Measure ℝ} (hnonneg : Q (Iio 0) = 0) (h0 : Q {0} = 0) :
    ∀ᵐ y ∂Q, 0 < y := by
  rw [ae_iff]
  have hIic : Iic (0:ℝ) = Iio (0:ℝ) ∪ {0} := by
    ext x
    simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h | h) <;> linarith
  have hnull : Q (Iic (0:ℝ)) = 0 := by
    rw [hIic]
    refine le_antisymm ?_ (by positivity)
    calc Q (Iio (0:ℝ) ∪ {0}) ≤ Q (Iio (0:ℝ)) + Q {0} := measure_union_le _ _
      _ = 0 := by rw [hnonneg, h0, add_zero]
  rw [show {y : ℝ | ¬ 0 < y} = Iic 0 from by ext y; simp]
  exact hnull

/-- On laws carried by `(0,∞)` the raw kernel and its bounded-continuous version have the
same integral.  This is where `Q (Iio 0) = 0` and `Q {0} = 0` enter. -/
theorem integral_kern_eq_integral_kernB {Q : Measure ℝ} (hnonneg : Q (Iio 0) = 0)
    (h0 : Q {0} = 0) (s : ℝ) :
    ∫ y, kern s y ∂Q = ∫ y, kernB s y ∂Q := by
  refine integral_congr_ae ?_
  filter_upwards [ae_pos_of_support hnonneg h0] with y hy
  exact (kernB_of_pos hy).symm

/-- **Fixed-rate transfer for the raw kernel**, under the source hypotheses: the laws are
carried by `[0,∞)` and have no atom at `0`. -/
theorem tendsto_integral_kern {ι : Type*} {l : Filter ι} {Q : ι → ProbabilityMeasure ℝ}
    {Qinf : ProbabilityMeasure ℝ}
    (hsupp : ∀ i, (Q i : Measure ℝ) (Iio 0) = 0) (h0 : ∀ i, (Q i : Measure ℝ) {0} = 0)
    (hsupinf : (Qinf : Measure ℝ) (Iio 0) = 0) (h0inf : (Qinf : Measure ℝ) {0} = 0)
    (hQ : Tendsto Q l (𝓝 Qinf)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun i => ∫ y, kern s y ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ y, kern s y ∂(Qinf : Measure ℝ))) := by
  have hEq : ∀ i, ∫ y, kern s y ∂(Q i : Measure ℝ) = ∫ y, kernB s y ∂(Q i : Measure ℝ) :=
    fun i => integral_kern_eq_integral_kernB (hsupp i) (h0 i) s
  have hEqinf : ∫ y, kern s y ∂(Qinf : Measure ℝ) = ∫ y, kernB s y ∂(Qinf : Measure ℝ) :=
    integral_kern_eq_integral_kernB hsupinf h0inf s
  simpa only [hEq, hEqinf] using tendsto_integral_kernB hQ hs

/-- **Fixed-rate transfer for the raw exponential kernel**; the `|·|` makes the raw and
bounded-continuous versions identical, so only probability laws are needed. -/
theorem tendsto_integral_expK_of_measure {ι : Type*} {l : Filter ι}
    {Q : ι → ProbabilityMeasure ℝ} {Qinf : ProbabilityMeasure ℝ}
    (hQ : Tendsto Q l (𝓝 Qinf)) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun i => ∫ y, Real.exp (-(c * |y|)) ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ y, Real.exp (-(c * |y|)) ∂(Qinf : Measure ℝ))) := by
  simpa only [expK] using tendsto_integral_expK hQ hc

/-! ## 4. Moving rates -/

/-- `|kern s y| ≤ s` on `[0,∞)`, for any nonnegative rate `s` (including `s = 0`). -/
theorem kern_abs_le_rate {s y : ℝ} (hs : 0 ≤ s) (hy : 0 ≤ y) : |kern s y| ≤ s := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h; simp [kern]
  · rw [abs_of_nonneg (kern_nonneg h hy)]
    exact kern_le_rate h hy

theorem ae_nonneg_of_Iio {Q : Measure ℝ} (hQ : Q (Iio 0) = 0) : ∀ᵐ y ∂Q, 0 ≤ y := by
  filter_upwards [compl_mem_ae_iff.mpr hQ] with y hy
  simpa using hy

/-- `∫ kern s dQ` is `1`-Lipschitz in the rate `s`, uniformly in the law. -/
theorem abs_integral_kern_sub_le {Q : Measure ℝ} [IsFiniteMeasure Q] (hQ : Q (Iio 0) = 0)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |(∫ y, kern s y ∂Q) - ∫ y, kern t y ∂Q| ≤ |s - t| * (Q Set.univ).toReal := by
  have hsup := ae_nonneg_of_Iio hQ
  have hi1 : Integrable (fun y => kern s y) Q := by
    refine Integrable.of_bound (measurable_kern s).aestronglyMeasurable s ?_
    filter_upwards [hsup] with y hy
    rw [Real.norm_eq_abs]
    exact kern_abs_le_rate hs hy
  have hi2 : Integrable (fun y => kern t y) Q := by
    refine Integrable.of_bound (measurable_kern t).aestronglyMeasurable t ?_
    filter_upwards [hsup] with y hy
    rw [Real.norm_eq_abs]
    exact kern_abs_le_rate ht hy
  have hb : ∀ᵐ y ∂Q, ‖kern s y - kern t y‖ ≤ |s - t| := by
    filter_upwards [hsup] with y hy
    rw [Real.norm_eq_abs]
    exact abs_kern_sub_kern_le hs ht hy
  rw [← integral_sub hi1 hi2]
  calc |∫ y, kern s y - kern t y ∂Q| ≤ ∫ y, |kern s y - kern t y| ∂Q :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y, |s - t| ∂Q :=
        integral_mono_ae (hi1.sub hi2).norm (integrable_const _) hb
    _ = |s - t| * (Q Set.univ).toReal := by
        rw [integral_const, smul_eq_mul, Measure.real, mul_comm]

/-- **Moving-rate transfer for the kernel.**  If `c r → λ > 0` and the laws converge
weakly, then the kernel integrals at the moving rates converge to the kernel integral at
the limit rate.  The only estimate used is the uniform Lipschitz bound
`|kern s y - kern t y| ≤ |s - t|` on `y ≥ 0`. -/
theorem tendsto_integral_kern_moving {ι : Type*} {l : Filter ι}
    {Q : ι → ProbabilityMeasure ℝ} {Qinf : ProbabilityMeasure ℝ}
    (hsupp : ∀ i, (Q i : Measure ℝ) (Iio 0) = 0) (h0 : ∀ i, (Q i : Measure ℝ) {0} = 0)
    (hsupinf : (Qinf : Measure ℝ) (Iio 0) = 0) (h0inf : (Qinf : Measure ℝ) {0} = 0)
    (hQ : Tendsto Q l (𝓝 Qinf)) {c : ι → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hc : Tendsto c l (𝓝 lam)) (hcpos : ∀ᶠ i in l, 0 ≤ c i) :
    Tendsto (fun i => ∫ y, kern (c i) y ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ y, kern lam y ∂(Qinf : Measure ℝ))) := by
  have hfix := tendsto_integral_kern hsupp h0 hsupinf h0inf hQ hlam
  have hbound : ∀ᶠ i in l,
      |(∫ y, kern (c i) y ∂(Q i : Measure ℝ)) - ∫ y, kern lam y ∂(Q i : Measure ℝ)|
        ≤ |c i - lam| := by
    filter_upwards [hcpos] with i hi
    have h := abs_integral_kern_sub_le (Q := (Q i : Measure ℝ)) (hsupp i) hi hlam.le
    simpa using h
  have hdiff : Tendsto
      (fun i => (∫ y, kern (c i) y ∂(Q i : Measure ℝ)) - ∫ y, kern lam y ∂(Q i : Measure ℝ))
      l (𝓝 0) := by
    have habs : Tendsto (fun i => |c i - lam|) l (𝓝 0) := by
      simpa using (hc.sub_const lam).abs
    have hdiff_abs : Tendsto
        (fun i => |(∫ y, kern (c i) y ∂(Q i : Measure ℝ))
          - ∫ y, kern lam y ∂(Q i : Measure ℝ)|) l (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun i => abs_nonneg _) hbound habs
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hdiff_abs
  have hsum := hdiff.add hfix
  simpa [sub_add_cancel] using hsum

/-- Reparametrised form: the same conclusion holds along any family `ρ → l` of indices.
This is the "lift" that lets a scale `r(λ,h)` generated by `GeneralInverse` replace the
abstract index; no moving parameter is silently frozen. -/
theorem tendsto_integral_kern_moving_comp {ι γ : Type*} {l : Filter ι} {l' : Filter γ}
    {Q : ι → ProbabilityMeasure ℝ} {Qinf : ProbabilityMeasure ℝ}
    (hsupp : ∀ i, (Q i : Measure ℝ) (Iio 0) = 0) (h0 : ∀ i, (Q i : Measure ℝ) {0} = 0)
    (hsupinf : (Qinf : Measure ℝ) (Iio 0) = 0) (h0inf : (Qinf : Measure ℝ) {0} = 0)
    (hQ : Tendsto Q l (𝓝 Qinf)) {c : ι → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hc : Tendsto c l (𝓝 lam)) (hcpos : ∀ᶠ i in l, 0 ≤ c i)
    {ρ : γ → ι} (hρ : Tendsto ρ l' l) :
    Tendsto (fun g => ∫ y, kern (c (ρ g)) y ∂(Q (ρ g) : Measure ℝ)) l'
      (𝓝 (∫ y, kern lam y ∂(Qinf : Measure ℝ))) :=
  (tendsto_integral_kern_moving hsupp h0 hsupinf h0inf hQ hlam hc hcpos).comp hρ

/-! ## 5. Moving rates for the exponential kernel

The kernel `expK c` is not Lipschitz in `c` uniformly in `y` in the naive sense, but the
weighted bound `|y| e^{-m|y|} ≤ 1/(e m)` makes the difference uniform on all of `ℝ` as
soon as the two rates stay at distance `≥ m > 0` from `0`. -/

/-- The one-variable bound `t e^{-m t} ≤ 1/(e m)` for `m > 0`. -/
theorem abs_mul_exp_neg_le {m : ℝ} (hm : 0 < m) (y : ℝ) :
    |y| * Real.exp (-(m * |y|)) ≤ 1 / (Real.exp 1 * m) := by
  have h := Real.mul_exp_neg_le_exp_neg_one (m * |y|)
  have h2 : m * (|y| * Real.exp (-(m * |y|))) = (m * |y|) * Real.exp (-(m * |y|)) := by ring
  rw [h2] at *
  have h3 : |y| * Real.exp (-(m * |y|))
      = (m * (|y| * Real.exp (-(m * |y|)))) / m := by
    field_simp
  have h4 : 1 / (Real.exp 1 * m) = Real.exp (-1) / m := by
    rw [Real.exp_neg, one_div]; field_simp
  rw [h4]
  rw [show |y| * Real.exp (-(m * |y|)) = ((m * |y|) * Real.exp (-(m * |y|))) / m by
    field_simp]
  exact div_le_div_of_nonneg_right h hm.le

/-- Two-term bound: for `m ≤ a ≤ b`, `|e^{-a t} - e^{-b t}| ≤ (b - a) t e^{-m t}`. -/
theorem abs_expK_pair_le {y a b m : ℝ} (hm0 : 0 ≤ m) (ham : m ≤ a) (hab : a ≤ b) :
    |expK a y - expK b y| ≤ (b - a) * (|y| * Real.exp (-(m * |y|))) := by
  unfold expK
  have ht : 0 ≤ |y| := abs_nonneg y
  have hmono : Real.exp (-(b * |y|)) ≤ Real.exp (-(a * |y|)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [abs_of_nonneg (by linarith :
    0 ≤ Real.exp (-(a * |y|)) - Real.exp (-(b * |y|)))]
  have hfac : Real.exp (-(a * |y|)) - Real.exp (-(b * |y|))
      = Real.exp (-(a * |y|)) * (1 - Real.exp (-((b - a) * |y|))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    ring_nf
  rw [hfac]
  have hnn : 0 ≤ 1 - Real.exp (-((b - a) * |y|)) := by
    have hle : -((b - a) * |y|) ≤ 0 := by nlinarith
    linarith [Real.exp_le_one_iff.mpr hle]
  have hkey : 1 - Real.exp (-((b - a) * |y|)) ≤ (b - a) * |y| := by
    have h := Real.add_one_le_exp (-((b - a) * |y|))
    linarith
  have hexp : Real.exp (-(a * |y|)) ≤ Real.exp (-(m * |y|)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc Real.exp (-(a * |y|)) * (1 - Real.exp (-((b - a) * |y|)))
      ≤ Real.exp (-(m * |y|)) * ((b - a) * |y|) :=
        mul_le_mul hexp hkey hnn (Real.exp_pos _).le
    _ = (b - a) * (|y| * Real.exp (-(m * |y|))) := by ring

/-- Two-sided rate bound for the exponential kernel: for `m > 0`, `m ≤ a`, `m ≤ b`,
`|e^{-a|y|} - e^{-b|y|}| ≤ |a - b| |y| e^{-m|y|}`. -/
theorem abs_expK_sub_le {y a b m : ℝ} (hm0 : 0 ≤ m) (ham : m ≤ a) (hbm : m ≤ b) :
    |expK a y - expK b y| ≤ |a - b| * (|y| * Real.exp (-(m * |y|))) := by
  rcases le_total a b with hab | hba
  · have h := abs_expK_pair_le (y := y) hm0 ham hab
    rwa [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub]
  · have h := abs_expK_pair_le (y := y) hm0 hbm hba
    rw [abs_sub_comm (expK a y), abs_of_nonneg (by linarith : 0 ≤ a - b)]
    exact h

/-- **Moving-rate transfer for the exponential kernel**: if `c i → λ > 0` (with `c i`
eventually bounded below by `λ/2`) then the exponential integrals converge.  The bound is
uniform in `y`: `|c i - λ| / (e * λ/2)`. -/
theorem tendsto_integral_expK_moving {ι : Type*} {l : Filter ι}
    {Q : ι → ProbabilityMeasure ℝ} {Qinf : ProbabilityMeasure ℝ}
    (hQ : Tendsto Q l (𝓝 Qinf)) {c : ι → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hc : Tendsto c l (𝓝 lam)) (hcpos : ∀ᶠ i in l, lam / 2 ≤ c i) :
    Tendsto (fun i => ∫ y, expK (c i) y ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ y, expK lam y ∂(Qinf : Measure ℝ))) := by
  have hm0 : (0:ℝ) ≤ lam / 2 := by linarith
  have hmpos : (0:ℝ) < lam / 2 := by linarith
  have hfix := tendsto_integral_expK (Q := Q) (Qinf := Qinf) hQ hlam.le
  have hbound : ∀ᶠ i in l,
      |(∫ y, expK (c i) y ∂(Q i : Measure ℝ)) - ∫ y, expK lam y ∂(Q i : Measure ℝ)|
        ≤ |c i - lam| * (1 / (Real.exp 1 * (lam / 2))) := by
    filter_upwards [hcpos] with i hi
    have hi_int : Integrable (fun y => expK (c i) y) (Q i : Measure ℝ) := by
      refine Integrable.of_bound (continuous_expK _).aestronglyMeasurable 1 ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_pos (expK_pos (c i) y)]
      exact expK_le_one (le_trans hm0 hi) y
    have hlam_int : Integrable (fun y => expK lam y) (Q i : Measure ℝ) := by
      refine Integrable.of_bound (continuous_expK _).aestronglyMeasurable 1 ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_pos (expK_pos lam y)]
      exact expK_le_one hlam.le y
    have hpt : ∀ y : ℝ, |expK (c i) y - expK lam y|
        ≤ |c i - lam| * (1 / (Real.exp 1 * (lam / 2))) := by
      intro y
      refine (abs_expK_sub_le hm0 hi (by linarith : lam / 2 ≤ lam) (y := y)).trans ?_
      exact mul_le_mul_of_nonneg_left (abs_mul_exp_neg_le hmpos y) (abs_nonneg _)
    rw [← integral_sub hi_int hlam_int]
    calc |∫ y, expK (c i) y - expK lam y ∂(Q i : Measure ℝ)|
        ≤ ∫ y, |expK (c i) y - expK lam y| ∂(Q i : Measure ℝ) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _y, |c i - lam| * (1 / (Real.exp 1 * (lam / 2))) ∂(Q i : Measure ℝ) := by
          refine integral_mono_ae ?_ (integrable_const _) (Eventually.of_forall hpt)
          exact (hi_int.sub hlam_int).abs
      _ = |c i - lam| * (1 / (Real.exp 1 * (lam / 2))) := by
          rw [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one,
            one_mul]
  have hdiff : Tendsto
      (fun i => (∫ y, expK (c i) y ∂(Q i : Measure ℝ)) - ∫ y, expK lam y ∂(Q i : Measure ℝ))
      l (𝓝 0) := by
    have habs : Tendsto (fun i => |c i - lam| * (1 / (Real.exp 1 * (lam / 2)))) l (𝓝 0) := by
      have h0 : Tendsto (fun i => |c i - lam|) l (𝓝 0) := by
        simpa using (hc.sub_const lam).abs
      have := h0.mul_const (1 / (Real.exp 1 * (lam / 2)))
      simpa using this
    have hdiff_abs : Tendsto
        (fun i => |(∫ y, expK (c i) y ∂(Q i : Measure ℝ))
          - ∫ y, expK lam y ∂(Q i : Measure ℝ)|) l (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun i => abs_nonneg _) hbound habs
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hdiff_abs
  have hsum := hdiff.add hfix
  simpa [sub_add_cancel] using hsum

/-! ## 6. The no-atom-at-zero limit `∫ e^{-λ|y|} dQ → 0` as `λ → ∞` -/

/-- No atom at `0` gives continuity from above at `0`. -/
theorem tendsto_measure_Ioo_zero_of_noAtom {Q : Measure ℝ} [IsFiniteMeasure Q]
    (hQ : Q {0} = 0) :
    Tendsto (fun δ : ℝ => Q (Ioo (-δ) δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hbi : (⋂ r > (0:ℝ), Ioo (-r) r) = {0} := by
    ext x
    simp only [mem_iInter, mem_Ioo, mem_singleton_iff]
    constructor
    · intro hx
      refine le_antisymm ?_ ?_
      · by_contra hneg
        push Not at hneg
        have := hx (x / 2) (by linarith)
        linarith [this.2]
      · by_contra hneg
        push Not at hneg
        have := hx (-x) (by linarith)
        linarith [this.1]
    · rintro rfl r hr
      exact ⟨by linarith, hr⟩
  have h := tendsto_measure_biInter_gt (μ := Q) (a := (0:ℝ)) (s := fun r => Ioo (-r) r)
    (fun r _ => measurableSet_Ioo.nullMeasurableSet)
    (fun i j hi hij x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    ⟨1, one_pos, measure_ne_top Q _⟩
  rw [hbi, hQ] at h
  exact h

/-- Real-valued form of the no-atom continuity. -/
theorem tendsto_measure_Ioo_zero_toReal_of_noAtom {Q : Measure ℝ} [IsFiniteMeasure Q]
    (hQ : Q {0} = 0) :
    Tendsto (fun δ : ℝ => (Q (Ioo (-δ) δ)).toReal) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  exact (ENNReal.tendsto_toReal_zero_iff (f := fun δ => Q (Ioo (-δ) δ))
    (fun _ => measure_ne_top Q _)).mpr (tendsto_measure_Ioo_zero_of_noAtom hQ)

/-- The explicit error bound behind the `λ → ∞` limit: on a symmetric neighbourhood of `0`
the exponential is at most `1`, and off it at most `e^{-λδ}`. -/
theorem integral_expK_le {Q : Measure ℝ} [IsFiniteMeasure Q] {c δ : ℝ}
    (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∫ y, expK c y ∂Q
      ≤ (Q (Ioo (-δ) δ)).toReal + Real.exp (-(c * δ)) * (Q Set.univ).toReal := by
  have hpt : ∀ y : ℝ, expK c y
      ≤ (Set.indicator (Ioo (-δ) δ) (fun _ => (1:ℝ)) y + Real.exp (-(c * δ))) := by
    intro y
    by_cases hy : y ∈ Ioo (-δ) δ
    · rw [Set.indicator_of_mem hy]
      have h1 : expK c y ≤ 1 := expK_le_one hc y
      linarith [Real.exp_pos (-(c * δ))]
    · rw [Set.indicator_of_notMem hy, zero_add]
      apply Real.exp_le_exp.mpr
      have hy' : |y| ≥ δ := by
        simp only [mem_Ioo, not_and_or, not_lt] at hy
        rcases hy with h | h
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      nlinarith
  have hint1 : Integrable (fun y : ℝ => expK c y) Q := by
    refine Integrable.of_bound (continuous_expK c).aestronglyMeasurable 1 ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_pos (expK_pos c y)]
    exact expK_le_one hc y
  have hint2 : Integrable (fun y : ℝ =>
      (Set.indicator (Ioo (-δ) δ) (fun _ => (1:ℝ)) y + Real.exp (-(c * δ)))) Q := by
    refine Integrable.of_bound
      ((measurable_const.indicator measurableSet_Ioo).add measurable_const).aestronglyMeasurable
      (1 + Real.exp (-(c * δ))) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    by_cases hy : y ∈ Ioo (-δ) δ
    · rw [Set.indicator_of_mem hy,
        abs_of_pos (by positivity : (0:ℝ) < 1 + Real.exp (-(c * δ)))]
    · rw [Set.indicator_of_notMem hy, zero_add, abs_of_pos (Real.exp_pos _)]
      linarith [Real.exp_pos (-(c * δ))]
  calc ∫ y, expK c y ∂Q
      ≤ ∫ y, (Set.indicator (Ioo (-δ) δ) (fun _ => (1:ℝ)) y + Real.exp (-(c * δ))) ∂Q :=
        integral_mono hint1 hint2 hpt
    _ = ∫ y, Set.indicator (Ioo (-δ) δ) (fun _ => (1:ℝ)) y ∂Q
          + ∫ _y, Real.exp (-(c * δ)) ∂Q := by
        rw [integral_add ((integrable_const _).indicator measurableSet_Ioo) (integrable_const _)]
    _ = (Q (Ioo (-δ) δ)).toReal + Real.exp (-(c * δ)) * (Q Set.univ).toReal := by
        rw [integral_indicator measurableSet_Ioo, integral_const, integral_const, Measure.real,
          Measure.real, Measure.restrict_apply_univ, smul_eq_mul, smul_eq_mul, mul_one]
        ring

/-- **The no-atom limit of Proposition I.3.2**: if a probability law on `ℝ` has no atom at
`0`, then `∫ e^{-λ|y|} dQ → 0` as `λ → ∞`.  The proof uses the explicit bound
`∫ e^{-λ|y|} dQ ≤ Q (Ioo (-δ) δ) + e^{-λδ}` and continuity from above at `0`. -/
theorem tendsto_integral_expK_atTop {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (h0 : Q {0} = 0) :
    Tendsto (fun c : ℝ => ∫ y, expK c y ∂Q) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  have hδlim := tendsto_measure_Ioo_zero_toReal_of_noAtom h0
  have hev : ∀ᶠ δ in (𝓝[>] (0:ℝ)), (Q (Ioo (-δ) δ)).toReal < ε / 2 ∧ 0 < δ := by
    filter_upwards [hδlim.eventually (Metric.ball_mem_nhds 0 hε2), self_mem_nhdsWithin]
      with δ hδ hδ0
    refine ⟨?_, hδ0⟩
    rw [Real.dist_eq, sub_zero] at hδ
    linarith [le_abs_self ((Q (Ioo (-δ) δ)).toReal)]
  obtain ⟨δ, hδ, hδ0⟩ := hev.exists
  have htwoε : (2:ℝ) / ε ≠ 0 := by positivity
  refine ⟨max 0 (Real.log (2 / ε) / δ + 1), ?_⟩
  intro c hc
  have hc0 : 0 ≤ c := le_trans (le_max_left _ _) hc
  have hcbig : Real.log (2 / ε) / δ < c := by
    have h1 : Real.log (2 / ε) / δ + 1 ≤ c := le_trans (le_max_right _ _) hc
    linarith
  have hcd : Real.log (2 / ε) < c * δ := by
    have h2 : Real.log (2 / ε) / δ * δ < c * δ := mul_lt_mul_of_pos_right hcbig hδ0
    have h3 : Real.log (2 / ε) / δ * δ = Real.log (2 / ε) := by field_simp
    linarith [h2, h3]
  have hexp : Real.exp (-(c * δ)) < ε / 2 := by
    have h1 : Real.exp (-(c * δ)) < Real.exp (-(Real.log (2 / ε))) :=
      Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp (-(Real.log (2 / ε))) = ε / 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    rwa [h2] at h1
  have hbound := integral_expK_le (Q := Q) hc0 hδ0
  have hQuniv : (Q Set.univ).toReal = 1 := by
    rw [measure_univ, ENNReal.toReal_one]
  have hfin : ∫ y, expK c y ∂Q < ε := by
    rw [hQuniv, mul_one] at hbound
    linarith
  have hnonneg : 0 ≤ ∫ y, expK c y ∂Q :=
    integral_nonneg fun y => expK_nonneg c y
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hfin

/-! ## 7. Measure-level interface: discharging the `hker` / `hexp` hypotheses

The candidate module `Analysis.I32` states its probabilistic inputs as convergence of
integrals against the raw `Measure` `sizeBiasedLaw mu r`, with `IsProbabilityMeasure`
instances.  The following two statements are exactly that shape; they are proved here by
converting to `ProbabilityMeasure`. -/

theorem tendsto_integral_kern_measure {ι : Type*} {l : Filter ι} {ν : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)] {νinf : Measure ℝ} [IsProbabilityMeasure νinf]
    (hsupp : ∀ i, ν i (Iio 0) = 0) (h0 : ∀ i, ν i {0} = 0)
    (hsupinf : νinf (Iio 0) = 0) (h0inf : νinf {0} = 0)
    (hQ : Tendsto (fun i => (ν i).toProbabilityMeasure) l (𝓝 νinf.toProbabilityMeasure))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun i => ∫ y, kern s y ∂(ν i)) l (𝓝 (∫ y, kern s y ∂νinf)) := by
  have h := tendsto_integral_kern (Q := fun i => (ν i).toProbabilityMeasure)
    (Qinf := νinf.toProbabilityMeasure) (fun i => by simpa using hsupp i)
    (fun i => by simpa using h0 i) (by simpa using hsupinf) (by simpa using h0inf) hQ hs
  simpa using h

theorem tendsto_integral_expK_measure {ι : Type*} {l : Filter ι} {ν : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)] {νinf : Measure ℝ} [IsProbabilityMeasure νinf]
    (hQ : Tendsto (fun i => (ν i).toProbabilityMeasure) l (𝓝 νinf.toProbabilityMeasure))
    {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun i => ∫ y, Real.exp (-(c * |y|)) ∂(ν i)) l
      (𝓝 (∫ y, Real.exp (-(c * |y|)) ∂νinf)) := by
  have h := tendsto_integral_expK (Q := fun i => (ν i).toProbabilityMeasure)
    (Qinf := νinf.toProbabilityMeasure) hQ hc
  simpa [expK] using h

/-- **The `hker` hypothesis of `Analysis.I32`**, discharged: for `r → ∞` weak convergence
of the rescaled size-biased laws gives, for *every* fixed rate `λ > 0`, convergence of the
raw kernel integrals. -/
theorem forall_tendsto_integral_kern_measure {ι : Type*} {l : Filter ι} {ν : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)] {νinf : Measure ℝ} [IsProbabilityMeasure νinf]
    (hsupp : ∀ i, ν i (Iio 0) = 0) (h0 : ∀ i, ν i {0} = 0)
    (hsupinf : νinf (Iio 0) = 0) (h0inf : νinf {0} = 0)
    (hQ : Tendsto (fun i => (ν i).toProbabilityMeasure) l (𝓝 νinf.toProbabilityMeasure)) :
    ∀ lam > 0, Tendsto (fun i => ∫ y, kern lam y ∂(ν i)) l (𝓝 (∫ y, kern lam y ∂νinf)) :=
  fun _ hlam => tendsto_integral_kern_measure hsupp h0 hsupinf h0inf hQ hlam

/-- **The `hexp` hypothesis of `Analysis.I32`**, discharged. -/
theorem forall_tendsto_integral_expK_measure {ι : Type*} {l : Filter ι}
    {ν : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (ν i)] {νinf : Measure ℝ}
    [IsProbabilityMeasure νinf]
    (hQ : Tendsto (fun i => (ν i).toProbabilityMeasure) l (𝓝 νinf.toProbabilityMeasure)) :
    ∀ c > 0, Tendsto (fun i => ∫ y, Real.exp (-(c * |y|)) ∂(ν i)) l
      (𝓝 (∫ y, Real.exp (-(c * |y|)) ∂νinf)) :=
  fun _ hc => tendsto_integral_expK_measure hQ hc.le

/-! ### The `GeneralInverse` scale `r(λ,h) = e.symm (λ / (A h))`

The reparametrisation form `tendsto_integral_kern_moving_comp` is the abstract "lift";
these two lemmas supply the concrete scale produced by the inverse of an order
isomorphism (the `RegularlyVaryingAtTop` inverse in `Analysis.GeneralInverse`), and the
corollary below combines them, so the index really moves with `h ↓ 0`. -/

theorem tendsto_orderIso_atTop (e : ℝ ≃o ℝ) : Tendsto (⇑e) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  refine eventually_atTop.2 ⟨e.symm b, fun y hy => ?_⟩
  simpa using (OrderIso.le_iff_le e).mpr hy

theorem tendsto_orderIso_symm_div_nhdsGT_zero (e : ℝ ≃o ℝ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun h : ℝ => e.symm (v / h)) (𝓝[>] (0:ℝ)) atTop := by
  have hmul : Tendsto (fun h : ℝ => v / h) (𝓝[>] (0:ℝ)) atTop := by
    have hinv : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have h := hinv.const_mul_atTop hv
    simpa only [div_eq_mul_inv] using h
  exact (tendsto_orderIso_atTop e.symm).comp hmul

/-- The composite lift with an abstract scale `ρ → ∞`: the law index and the rate both move
with the new parameter `h ↓ 0`. -/
theorem tendsto_integral_kern_along_scale {Q : ℝ → ProbabilityMeasure ℝ}
    {Qinf : ProbabilityMeasure ℝ}
    (hsupp : ∀ r, (Q r : Measure ℝ) (Iio 0) = 0) (h0 : ∀ r, (Q r : Measure ℝ) {0} = 0)
    (hsupinf : (Qinf : Measure ℝ) (Iio 0) = 0) (h0inf : (Qinf : Measure ℝ) {0} = 0)
    (hQ : Tendsto Q atTop (𝓝 Qinf)) {c ρ : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hc : Tendsto c (𝓝[>] (0:ℝ)) (𝓝 lam)) (hcpos : ∀ᶠ h in 𝓝[>] (0:ℝ), 0 ≤ c h)
    (hρ : Tendsto ρ (𝓝[>] (0:ℝ)) atTop) :
    Tendsto (fun h : ℝ => ∫ y, kern (c h) y ∂(Q (ρ h) : Measure ℝ)) (𝓝[>] (0:ℝ))
      (𝓝 (∫ y, kern lam y ∂(Qinf : Measure ℝ))) := by
  have hQ' : Tendsto (fun h : ℝ => Q (ρ h)) (𝓝[>] (0:ℝ)) (𝓝 Qinf) := hQ.comp hρ
  have hsupp' : ∀ h : ℝ, (Q (ρ h) : Measure ℝ) (Iio 0) = 0 := fun h => hsupp (ρ h)
  have h0' : ∀ h : ℝ, (Q (ρ h) : Measure ℝ) {0} = 0 := fun h => h0 (ρ h)
  exact tendsto_integral_kern_moving (l := 𝓝[>] (0:ℝ)) (Q := fun h : ℝ => Q (ρ h))
    (Qinf := Qinf) (c := c) (lam := lam) hsupp' h0' hsupinf h0inf hQ' hlam hc hcpos

/-- The composite lift in the shape produced by `GeneralInverse`: the scale
`r = e.symm (v/h)` tends to `∞` as `h ↓ 0`, the rate `c h` tends to `lam > 0`, and nothing
is frozen. -/
theorem tendsto_integral_kern_along_orderIso {Q : ℝ → ProbabilityMeasure ℝ}
    {Qinf : ProbabilityMeasure ℝ}
    (hsupp : ∀ r, (Q r : Measure ℝ) (Iio 0) = 0) (h0 : ∀ r, (Q r : Measure ℝ) {0} = 0)
    (hsupinf : (Qinf : Measure ℝ) (Iio 0) = 0) (h0inf : (Qinf : Measure ℝ) {0} = 0)
    (hQ : Tendsto Q atTop (𝓝 Qinf)) {c : ℝ → ℝ} {lam v : ℝ} (hlam : 0 < lam) (hv : 0 < v)
    (e : ℝ ≃o ℝ) (hc : Tendsto c (𝓝[>] (0:ℝ)) (𝓝 lam))
    (hcpos : ∀ᶠ h in 𝓝[>] (0:ℝ), 0 ≤ c h) :
    Tendsto (fun h : ℝ => ∫ y, kern (c h) y ∂(Q (⇑(e.symm) (v / h)) : Measure ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ y, kern lam y ∂(Qinf : Measure ℝ))) :=
  tendsto_integral_kern_along_scale (ρ := fun h : ℝ => ⇑(e.symm) (v / h))
    hsupp h0 hsupinf h0inf hQ hlam hc hcpos (tendsto_orderIso_symm_div_nhdsGT_zero e hv)

/-! ## 8. Checks and examples

* the constant sequence (fixed law, fixed rate);
* point masses at `a > 0` (explicit closed forms, both kernels);
* the chi-square / Gamma law `χ²₁ = gammaMeasure (1/2) (1/2)` of the paper's application;
* the concrete failure of the *raw* (discontinuous at zero) convention on `δ₀`, which shows
  that the no-atom hypothesis cannot be dropped. -/

section Checks

/-- Constant sequence: every hypothesis is satisfied and the limit is the integral itself. -/
example {Q : ProbabilityMeasure ℝ} (hsupp : (Q : Measure ℝ) (Iio 0) = 0)
    (h0 : (Q : Measure ℝ) {0} = 0) :
    Tendsto (fun _ : ℕ => ∫ y, kern (1:ℝ) y ∂(Q : Measure ℝ)) atTop
      (𝓝 (∫ y, kern (1:ℝ) y ∂(Q : Measure ℝ))) :=
  tendsto_integral_kern (fun _ => hsupp) (fun _ => h0) hsupp h0 tendsto_const_nhds one_pos

/-- Constant sequence through the *moving-rate* theorem (constant rate `c ≡ λ`). -/
example {Q : ProbabilityMeasure ℝ} (hsupp : (Q : Measure ℝ) (Iio 0) = 0)
    (h0 : (Q : Measure ℝ) {0} = 0) :
    Tendsto (fun _ : ℕ => ∫ y, kern (1:ℝ) y ∂(Q : Measure ℝ)) atTop
      (𝓝 (∫ y, kern (1:ℝ) y ∂(Q : Measure ℝ))) :=
  tendsto_integral_kern_moving (fun _ => hsupp) (fun _ => h0) hsupp h0 tendsto_const_nhds
    one_pos tendsto_const_nhds (Eventually.of_forall fun _ => zero_le_one)

/-- The two conventions really differ at zero, for every positive rate. -/
theorem kern_ne_kernE_zero {s : ℝ} (hs : 0 < s) : kern s 0 = 0 ∧ kernE s 0 = s :=
  ⟨kern_zero s, kernE_zero s⟩

/-- A point mass at `a > 0` is carried by `(0,∞)` and has no atom at `0`. -/
theorem dirac_support {a : ℝ} (ha : 0 < a) :
    Measure.dirac a (Iio 0) = 0 ∧ Measure.dirac a {0} = 0 := by
  have hIio : Measure.dirac a (Iio (0:ℝ)) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iio]
    have h : a ∉ Iio (0:ℝ) := by simpa using ha.le
    rw [Set.indicator_of_notMem h]
  have hsing : Measure.dirac a ({(0:ℝ)}) = 0 := by
    rw [Measure.dirac_apply' _ (measurableSet_singleton 0)]
    have h : a ∉ ({(0:ℝ)} : Set ℝ) := by simpa using ha.ne'
    rw [Set.indicator_of_notMem h]
  exact ⟨hIio, hsing⟩

/-- Explicit value of the kernel integral against a point mass. -/
theorem integral_kern_dirac (s a : ℝ) (ha : a ≠ 0) :
    ∫ y, kern s y ∂(Measure.dirac a) = (1 - Real.exp (-(s * a))) / a := by
  rw [integral_dirac]
  rfl

/-- The no-atom limit at a point mass, by the general theorem. -/
example {a : ℝ} (ha : 0 < a) :
    Tendsto (fun c : ℝ => ∫ y, expK c y ∂(Measure.dirac a)) atTop (𝓝 0) :=
  tendsto_integral_expK_atTop (dirac_support ha).2

/-- The same limit by the closed form, agreeing with the general theorem. -/
example {a : ℝ} (ha : 0 < a) :
    Tendsto (fun c : ℝ => ∫ y, expK c y ∂(Measure.dirac a)) atTop (𝓝 0) := by
  have hfun : ∀ c : ℝ, ∫ y, expK c y ∂(Measure.dirac a) = Real.exp (-(c * a)) := by
    intro c
    rw [integral_dirac]
    simp [expK, abs_of_pos ha]
  simp_rw [hfun]
  have h : Tendsto (fun c : ℝ => c * a) atTop atTop := by
    have h1 := Filter.Tendsto.const_mul_atTop ha tendsto_id
    simpa only [id, mul_comm] using h1
  have h2 : Tendsto (fun c : ℝ => Real.exp (-(c * a))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h
  exact h2

/-! ### The chi-square law of the paper's application -/

theorem gammaMeasure_singleton_zero (a r : ℝ) :
    ProbabilityTheory.gammaMeasure a r {(0:ℝ)} = 0 := by
  rw [ProbabilityTheory.gammaMeasure, MeasureTheory.withDensity_apply _ (measurableSet_singleton 0)]
  simp

theorem gammaMeasure_Iio_zero (a r : ℝ) :
    ProbabilityTheory.gammaMeasure a r (Iio (0:ℝ)) = 0 := by
  rw [ProbabilityTheory.gammaMeasure, MeasureTheory.withDensity_apply _ measurableSet_Iio]
  rw [setLIntegral_congr_fun measurableSet_Iio
    (fun x hx => ProbabilityTheory.gammaPDF_of_neg hx)]
  simp

/-- `χ²₁`, the limit law of the paper's application, is a probability law carried by
`(0,∞)` with no atom at `0`, so the no-atom limit applies to it. -/
theorem tendsto_integral_expK_chiSquare :
    Tendsto (fun c : ℝ => ∫ y, expK c y ∂(ProbabilityTheory.gammaMeasure (1/2) (1/2)))
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure (1/2) (1/2)) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  exact tendsto_integral_expK_atTop (gammaMeasure_singleton_zero _ _)

/-- The same for an arbitrary Gamma law (any shape `a > 0`, any rate `r > 0`). -/
theorem tendsto_integral_expK_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Tendsto (fun c : ℝ => ∫ y, expK c y ∂(ProbabilityTheory.gammaMeasure a r))
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure a r) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure ha hr
  exact tendsto_integral_expK_atTop (gammaMeasure_singleton_zero _ _)

/-! ### The raw convention is *not* weakly continuous at `0` -/

/-- **Sharpness of the no-atom hypothesis.**  For the raw kernel (`kern s 0 = 0`) the
conclusion of `tendsto_integral_kern` fails for the weakly convergent family
`δ_{1/r} ⇒ δ_0`: the integrals converge to the true limiting value `s`, while the raw
integral against `δ_0` is `0`.  So the raw convention is discontinuous at zero and the
hypothesis `Q {0} = 0` cannot be dropped.  (The bounded-continuous version `kernB` has no
such defect: `tendsto_integral_kernB` applies to this family.) -/
theorem raw_kern_not_tendsto_dirac_zero {s : ℝ} (hs : 0 < s) :
    ¬ Tendsto (fun r : ℝ => ∫ y, kern s y ∂(Measure.dirac (1 / r))) atTop
        (𝓝 (∫ y, kern s y ∂(Measure.dirac (0:ℝ)))) := by
  intro h
  have hinv : Tendsto (fun r : ℝ => 1 / r) atTop (𝓝[≠] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa [one_div] using tendsto_inv_atTop_zero
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
      exact (one_div r).symm ▸ inv_ne_zero (ne_of_gt hr)
  have hleft : Tendsto (fun r : ℝ => ∫ y, kern s y ∂(Measure.dirac (1 / r))) atTop (𝓝 s) := by
    have hcomp : Tendsto (fun r : ℝ => kern s (1 / r)) atTop (𝓝 s) :=
      (tendsto_kern_zero hs).comp hinv
    refine hcomp.congr' ?_
    filter_upwards with r
    rw [integral_dirac]
  have hright : (∫ y, kern s y ∂(Measure.dirac (0:ℝ))) = 0 := by
    simp
  rw [hright] at h
  have huniq := tendsto_nhds_unique hleft h
  linarith

end Checks

/-- **The Laplace transform of a Gamma law**, in closed form.  This is the chi-square
check: for `χ²₁ = gammaMeasure (1/2) (1/2)` it gives `(1 + 2c)^{-1/2}`, which tends to `0`
as `c → ∞`, in agreement with `tendsto_integral_expK_chiSquare`. -/
theorem integral_expK_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (hrt : 0 < r + t) :
    ∫ y, expK t y ∂(ProbabilityTheory.gammaMeasure a r) = (r / (r + t)) ^ a := by
  have hΓne : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hden : (0:ℝ) < r + t := hrt
  have hf_meas : Measurable (ProbabilityTheory.gammaPDF a r) :=
    (ProbabilityTheory.measurable_gammaPDFReal a r).ennreal_ofReal
  have hf_lt : ∀ᵐ y ∂volume, ProbabilityTheory.gammaPDF a r y < ∞ := by
    filter_upwards with y
    exact ENNReal.ofReal_lt_top
  rw [ProbabilityTheory.gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul hf_meas hf_lt]
  have htoReal : ∀ y : ℝ, (ProbabilityTheory.gammaPDF a r y).toReal
      = ProbabilityTheory.gammaPDFReal a r y := by
    intro y
    rw [ProbabilityTheory.gammaPDF,
      ENNReal.toReal_ofReal (ProbabilityTheory.gammaPDFReal_nonneg ha hr y)]
  simp only [htoReal, smul_eq_mul]
  -- the density vanishes off `Ioi 0`
  have step1 : ∫ y, ProbabilityTheory.gammaPDFReal a r y * expK t y ∂volume
      = ∫ y in Ioi (0:ℝ), ProbabilityTheory.gammaPDFReal a r y * expK t y := by
    rw [← integral_indicator (s := Ioi (0:ℝ)) measurableSet_Ioi]
    refine integral_congr_ae ?_
    have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by
      filter_upwards [compl_mem_ae_iff.mpr (by simp : (volume ({0} : Set ℝ)) = 0)] with y hy
      simpa using hy
    filter_upwards [hne] with y hyne
    by_cases hy : y ∈ Ioi (0:ℝ)
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyneg : y < 0 := by
        simp only [mem_Ioi, not_lt] at hy
        exact lt_of_le_of_ne hy hyne
      rw [ProbabilityTheory.gammaPDFReal, ite_eq_right (not_le.mpr hyneg), zero_mul]
  rw [step1]
  -- the integrand on `Ioi 0`
  have hpt : ∀ y ∈ Ioi (0:ℝ), ProbabilityTheory.gammaPDFReal a r y * expK t y
      = r ^ a / Real.Gamma a * (y ^ (a - 1) * Real.exp (-((r + t) * y))) := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [ProbabilityTheory.gammaPDFReal, ite_eq_left hy0.le, expK, abs_of_pos hy0]
    have hexp : Real.exp (-(r * y)) * Real.exp (-(t * y)) = Real.exp (-((r + t) * y)) := by
      rw [← Real.exp_add]; ring_nf
    calc r ^ a / Real.Gamma a * y ^ (a - 1) * Real.exp (-(r * y)) * Real.exp (-(t * y))
        = r ^ a / Real.Gamma a * y ^ (a - 1)
            * (Real.exp (-(r * y)) * Real.exp (-(t * y))) := by ring
      _ = r ^ a / Real.Gamma a * (y ^ (a - 1) * Real.exp (-((r + t) * y))) := by
          rw [hexp]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hrt]
  -- algebra
  have hinv : (1 / (r + t)) ^ a = ((r + t) ^ a)⁻¹ := by
    rw [one_div, Real.inv_rpow (le_of_lt hden)]
  have hne : ((r + t) ^ a) ≠ 0 := (Real.rpow_pos_of_pos hden a).ne'
  rw [hinv, Real.div_rpow hr.le (le_of_lt hden)]
  field_simp

/-- **The moving rate attached to the `GeneralInverse` scale.**  This is the rate that
occurs in `stage1_mgf_ratio`/`mgf_of_components`: at the scale `r = e.symm (v/h)` chosen so
that `h · e(r)` is the fixed number `A2 · v = λ`, the product `h · Ê_{r(λ,h)}` tends to `λ`
as soon as the size-biased mean is asymptotic to `A2 · e` at infinity.  It supplies the
`Tendsto c (𝓝[>] 0) (𝓝 lam)` hypothesis of `tendsto_integral_kern_along_orderIso`, so that
the moving rate there is the paper's, not an abstract function. -/
theorem tendsto_rate_of_orderIso_scale {Ê : ℝ → ℝ} {e : ℝ ≃o ℝ} {A2 lam v : ℝ}
    (hA2 : 0 < A2) (hlam : 0 < lam) (hv : v = lam / A2)
    (hS2 : Tendsto (fun r => Ê r / (A2 * ⇑e r)) atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => h * Ê (⇑(e.symm) (v / h))) (𝓝[>] (0:ℝ)) (𝓝 lam) := by
  have hv0 : 0 < v := by rw [hv]; positivity
  have hρ : Tendsto (fun h : ℝ => ⇑(e.symm) (v / h)) (𝓝[>] (0:ℝ)) atTop :=
    tendsto_orderIso_symm_div_nhdsGT_zero e hv0
  have hratio : Tendsto (fun h : ℝ => Ê (⇑(e.symm) (v / h)) / (A2 * ⇑e (⇑(e.symm) (v / h))))
      (𝓝[>] (0:ℝ)) (𝓝 1) := hS2.comp hρ
  have hratio' : Tendsto (fun h : ℝ => Ê (⇑(e.symm) (v / h)) / (A2 * (v / h)))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    refine hratio.congr' ?_
    filter_upwards with h
    rw [OrderIso.apply_symm_apply]
  have hEq : (fun h : ℝ => h * Ê (⇑(e.symm) (v / h))) =ᶠ[𝓝[>] (0:ℝ)]
      fun h => (Ê (⇑(e.symm) (v / h)) / (A2 * (v / h))) * (A2 * v) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := ne_of_gt hh
    have hvne : v ≠ 0 := ne_of_gt hv0
    field_simp
  have hAv : A2 * v = lam := by rw [hv]; field_simp
  have hlim : Tendsto (fun h : ℝ => (Ê (⇑(e.symm) (v / h)) / (A2 * (v / h))) * (A2 * v))
      (𝓝[>] (0:ℝ)) (𝓝 (1 * (A2 * v))) :=
    hratio'.mul_const (A2 * v)
  have hlim' : Tendsto (fun h : ℝ => (Ê (⇑(e.symm) (v / h)) / (A2 * (v / h))) * (A2 * v))
      (𝓝[>] (0:ℝ)) (𝓝 lam) := by
    simpa [hAv] using hlim
  exact hlim'.congr' hEq.symm

end PercLib.CriticalLRP.Analysis.I32WeakConv
/-! ## 9. Axiom audit -/

#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.tendsto_integral_kernB
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.tendsto_integral_kern
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.tendsto_integral_kern_moving
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.tendsto_integral_expK
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.tendsto_integral_expK_moving
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.tendsto_integral_expK_atTop
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.tendsto_integral_kern_measure
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.forall_tendsto_integral_expK_measure
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.tendsto_integral_kern_along_orderIso
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.integral_expK_gammaMeasure
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.tendsto_integral_expK_chiSquare
#print axioms PercLib.CriticalLRP.Analysis.I32WeakConv.raw_kern_not_tendsto_dirac_zero
