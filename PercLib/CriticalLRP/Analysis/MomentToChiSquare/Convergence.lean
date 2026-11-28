/-
Standalone development for swarm smwzuf8hm member m4: the moment-to-weak-convergence step of
Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), Remark I.1.7.

This file is self-contained apart from `PercLib.CriticalLRP.MomentProblem.ChiSquare`, from which it
takes the chi-square moments `(2n-1)!!` and the moment-determinacy theorem.
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import PercLib.CriticalLRP.MomentProblem.ChiSquare

/-!
# Moment convergence to the chi-square law implies weak convergence

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), proof of (I.1.7) (p. 32):
"any subsequential limit ... has `p`th moment `(2p-1)!!` for each integer `p ≥ 1` and hence by
Carleman's criterion ... converges to a chi-squared random variable with one degree of freedom".

The present file carries out that step with the tail and moment estimates actually proved, for
probability laws on `[0,∞)` with finite moments of every order:

* `tail_compl_Icc_le`: Markov's inequality in the form
  `ρ ((Icc (-R) R)ᶜ) ≤ ∫ x, x ^ 2 ∂ρ / R ^ 2`;
* `isTightMeasureSet_range`: bounded second moments give tightness;
* `integral_pow_eq_of_tendsto` (**the core**): a moment of a weak subsequential limit is the limit
  of the moments, obtained by clamping `x ↦ x ^ k` to `[-R, R]` (a bounded continuous test
  function), bounding the clamping error both at the sequence and at the limit by the `2k`-th
  moment, and letting `R → ∞`;
* `tendsto_chiSquare_of_moment_tendsto` (**main**): if all moments of `μ n` tend to `(2n-1)!!` then
  `μ n` converges weakly to `gammaMeasure (1/2) (1/2)`, using Prokhorov compactness, the core
  lemma at every subsequential limit, and moment determinacy.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace SwarmM4

/-! ### Even powers and the chi-square moments -/

/-- `x ^ (2 * k) = (x ^ k) ^ 2`. -/
lemma pow_two_mul_eq_sq (x : ℝ) (k : ℕ) : x ^ (2 * k) = (x ^ k) ^ 2 := by
  rw [show 2 * k = k * 2 by ring, pow_mul]

lemma pow_two_mul_nonneg (x : ℝ) (k : ℕ) : 0 ≤ x ^ (2 * k) := by
  rw [pow_two_mul_eq_sq]; positivity

/-- For an even exponent the absolute power is the power. -/
lemma abs_pow_two_mul (x : ℝ) (k : ℕ) : |x| ^ (2 * k) = x ^ (2 * k) := by
  rw [← abs_pow, abs_of_nonneg (pow_two_mul_nonneg x k)]

/-! ### Clamping a monomial to a bounded continuous test function -/

/-- The monomial `y ↦ y ^ k` clamped to the interval `[-R, R]`. -/
noncomputable def clamp (k : ℕ) (R : ℝ) (y : ℝ) : ℝ := max (-R) (min (y ^ k) R)

lemma continuous_clamp (k : ℕ) (R : ℝ) : Continuous (clamp k R) :=
  continuous_const.max ((continuous_pow k).min continuous_const)

lemma clamp_le (k : ℕ) {R : ℝ} (hR : 0 ≤ R) (y : ℝ) : clamp k R y ≤ R :=
  max_le (by linarith) (min_le_right _ _)

lemma neg_le_clamp (k : ℕ) (R y : ℝ) : -R ≤ clamp k R y :=
  le_max_left _ _

lemma abs_clamp_le (k : ℕ) {R : ℝ} (hR : 0 ≤ R) (y : ℝ) : |clamp k R y| ≤ R :=
  abs_le.mpr ⟨neg_le_clamp k R y, clamp_le k hR y⟩

lemma clamp_eq_of_abs_le (k : ℕ) {R y : ℝ} (h : |y ^ k| ≤ R) : clamp k R y = y ^ k := by
  simp only [clamp, min_eq_left (le_of_abs_le h), max_eq_right (neg_le_of_abs_le h)]

/-- The clamping error is dominated by the `2k`-th power. -/
lemma abs_sub_clamp_le (k : ℕ) {R : ℝ} (hR : 0 < R) (y : ℝ) :
    |y ^ k - clamp k R y| ≤ 2 / R * |y| ^ (2 * k) := by
  by_cases h : |y| ^ k ≤ R
  · have hyk : |y ^ k| ≤ R := by rwa [abs_pow]
    have hclamp : clamp k R y = y ^ k := clamp_eq_of_abs_le k hyk
    rw [hclamp, sub_self, abs_zero]
    positivity
  · push Not at h
    have h2 : |y ^ k - clamp k R y| ≤ |y ^ k| + |clamp k R y| := abs_sub _ _
    have h3 : |clamp k R y| ≤ R := abs_clamp_le k hR.le y
    have h4 : |y ^ k| = |y| ^ k := abs_pow y k
    have h5 : |y ^ k - clamp k R y| ≤ 2 * |y| ^ k := by rw [h4] at h2; linarith
    have ht : 0 < |y| ^ k := by
      rcases eq_or_lt_of_le (pow_nonneg (abs_nonneg y) k) with h0 | h0
      · rw [← h0] at h; linarith
      · exact h0
    have h6 : 2 * |y| ^ k ≤ 2 / R * |y| ^ (2 * k) := by
      rw [pow_two_mul_eq_sq, div_mul_eq_mul_div, le_div_iff₀ hR]
      nlinarith [h, ht]
    linarith

/-! ### Markov's inequality for the second moment and tightness -/

/-- Markov's inequality in the form used for tightness: the mass outside `[-R, R]` times `R ^ 2` is
at most the second moment. -/
theorem mul_measure_compl_Icc_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {R : ℝ} (hR : 0 < R)
    (hint : Integrable (fun x : ℝ => x ^ 2) ρ) :
    ENNReal.ofReal (R ^ 2) * ρ (Set.Icc (-R) R)ᶜ ≤ ENNReal.ofReal (∫ x, x ^ 2 ∂ρ) := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (x ^ 2) :=
    (measurable_id.pow_const 2).ennreal_ofReal
  have key := mul_meas_ge_le_lintegral (μ := ρ) hmeas (ENNReal.ofReal (R ^ 2))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => by positivity)] at key
  have hmono : ρ (Set.Icc (-R) R)ᶜ
      ≤ ρ {a : ℝ | ENNReal.ofReal (R ^ 2) ≤ ENNReal.ofReal (a ^ 2)} := by
    refine measure_mono fun a ha => ?_
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ha
    have ha' : R < |a| := by
      rcases ha with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : |a| ^ 2 = a ^ 2 := sq_abs a
    nlinarith [abs_nonneg a, hR]
  calc ENNReal.ofReal (R ^ 2) * ρ (Set.Icc (-R) R)ᶜ
      ≤ ENNReal.ofReal (R ^ 2) * ρ {a : ℝ | ENNReal.ofReal (R ^ 2) ≤ ENNReal.ofReal (a ^ 2)} := by
        gcongr
    _ ≤ ENNReal.ofReal (∫ x, x ^ 2 ∂ρ) := key

/-- Bounded second moments give a tight family of probability measures on `ℝ`. -/
theorem isTightMeasureSet_range_of_second_moment (u : ℕ → ProbabilityMeasure ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hint : ∀ n, Integrable (fun x : ℝ => x ^ 2) (u n : Measure ℝ))
    (hC : ∀ n, ∫ x, x ^ 2 ∂(u n : Measure ℝ) ≤ C) :
    IsTightMeasureSet {x | ∃ n, ((u n : ProbabilityMeasure ℝ) : Measure ℝ) = x} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with htop | htop
  · exact ⟨∅, isCompact_empty, fun μ _ => by rw [htop]; exact le_top⟩
  set e : ℝ≥0 := ε.toNNReal with he
  have he0 : 0 < e := ENNReal.toNNReal_pos hε.ne' htop
  have hcoe : (e : ℝ≥0∞) = ε := ENNReal.coe_toNNReal htop
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he0
  have hRex : ∃ R : ℝ, 0 < R ∧ C ≤ (e : ℝ) * R ^ 2 := by
    have hnn : 0 ≤ C / (e : ℝ) := div_nonneg hC0 hepos.le
    refine ⟨Real.sqrt (C / e) + 1, by positivity, ?_⟩
    have h1 : C / e ≤ (Real.sqrt (C / e) + 1) ^ 2 := by
      have h3 : C / e ≤ (Real.sqrt (C / e)) ^ 2 := by
        rw [Real.sq_sqrt hnn]
      nlinarith [Real.sqrt_nonneg (C / e)]
    rw [mul_comm]
    exact (div_le_iff₀ hepos).mp h1
  obtain ⟨R, hR, hCR⟩ := hRex
  refine ⟨Set.Icc (-R) R, isCompact_Icc, fun μ hμ => ?_⟩
  obtain ⟨n, rfl⟩ := hμ
  have hmom2 : (∫ x, x ^ 2 ∂(u n : Measure ℝ)) ≤ (e : ℝ) * R ^ 2 := le_trans (hC n) hCR
  have hstep : ENNReal.ofReal (∫ x, x ^ 2 ∂(u n : Measure ℝ))
      ≤ ENNReal.ofReal (R ^ 2) * ε := by
    have h5 : ENNReal.ofReal (R ^ 2) * ε = ENNReal.ofReal ((e : ℝ) * R ^ 2) := by
      rw [ENNReal.ofReal_mul hepos.le, ENNReal.ofReal_coe_nnreal, hcoe, mul_comm]
    rw [h5]
    exact ENNReal.ofReal_le_ofReal hmom2
  have hR2ne : ENNReal.ofReal (R ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hR2top : ENNReal.ofReal (R ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hR2ne hR2top).mp
    (le_trans (mul_measure_compl_Icc_le _ hR (hint n)) hstep)

/-! ### Passing moments to a weak limit -/

section Core

variable {ρ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}

/-- The `j`-th absolute moment of a weak limit is at most the limsup of the `j`-th absolute moments
of the sequence (lower semicontinuity of `ν ↦ ∫⁻ |x|^j ∂ν` under weak convergence). -/
theorem lintegral_abs_pow_le_of_tendsto (hconv : Tendsto ρ atTop (𝓝 ν)) (j : ℕ) {C : ℝ}
    (hint : ∀ n, Integrable (fun x : ℝ => |x| ^ j) (ρ n : Measure ℝ))
    (hbd : ∀ n, ∫ x, |x| ^ j ∂(ρ n : Measure ℝ) ≤ C) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ j) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal C := by
  have hopen : ∀ G : Set ℝ, IsOpen G →
      (ν : Measure ℝ) G ≤ atTop.liminf (fun i => (ρ i : Measure ℝ) G) :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hG
  have key := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (ν : Measure ℝ)) (μs := fun i => (ρ i : Measure ℝ))
    (f := fun x : ℝ => |x| ^ j) (by fun_prop) (fun x => by positivity) hopen
  refine key.trans ?_
  have hterm : ∀ n, ∫⁻ x, ENNReal.ofReal (|x| ^ j) ∂(ρ n : Measure ℝ) ≤ ENNReal.ofReal C := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall fun x => by positivity)]
    exact ENNReal.ofReal_le_ofReal (hbd n)
  refine Filter.liminf_le_of_le ?_ ?_
  · exact isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => bot_le)
  · intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact le_trans hn (hterm n)

end Core

section Core

variable {ρ : ℕ → ProbabilityMeasure ℝ}

/-- The clamping error: replacing `x ↦ x ^ k` by its clamp to `[-R, R]` changes the integral by at
most `(2 / R)` times the `2k`-th absolute moment. -/
theorem abs_integral_pow_sub_clamp_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) {R : ℝ}
    (hR : 0 < R) (hint : Integrable (fun x : ℝ => |x| ^ (2 * k)) μ) :
    |∫ x, x ^ k ∂μ - ∫ x, clamp k R x ∂μ| ≤ 2 / R * ∫ x, |x| ^ (2 * k) ∂μ := by
  have hclamp_int : Integrable (fun x : ℝ => clamp k R x) μ :=
    Integrable.of_bound (continuous_clamp k R).aestronglyMeasurable R
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_clamp_le k hR.le x)
  have hk_int : Integrable (fun x : ℝ => x ^ k) μ := by
    refine Integrable.mono' (hint.add (integrable_const (1 : ℝ)))
      ((continuous_pow k).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    have h2 : |x| ^ k ≤ |x| ^ (2 * k) + 1 := by
      by_cases hle : |x| ^ k ≤ 1
      · linarith [pow_nonneg (abs_nonneg x) (2 * k)]
      · push Not at hle
        have h4 : |x| ^ k ≤ |x| ^ (2 * k) := by
          rw [pow_two_mul_eq_sq]
          nlinarith
        linarith
    exact h2
  rw [← integral_sub hk_int hclamp_int]
  refine (abs_integral_le_integral_abs).trans ?_
  have hsub_int : Integrable (fun x : ℝ => |x ^ k - clamp k R x|) μ :=
    (hk_int.sub hclamp_int).abs
  have hdom_int : Integrable (fun x : ℝ => 2 / R * |x| ^ (2 * k)) μ :=
    hint.const_mul (2 / R)
  refine (integral_mono hsub_int hdom_int (fun x => abs_sub_clamp_le k hR x)).trans ?_
  rw [integral_const_mul]

end Core

/-! ### Bounding a convergent sequence -/

lemma exists_bound_of_tendsto {u : ℕ → ℝ} {a : ℝ} (h : Tendsto u atTop (𝓝 a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, u n ≤ C := by
  have hev : ∀ᶠ n : ℕ in atTop, dist (u n) a < 1 := (Metric.tendsto_nhds.mp h) 1 (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have htail : ∀ n, N ≤ n → u n ≤ max (max 0 (a + 1)) (a + 1) := by
    intro n hn
    have h1 : dist (u n) a < 1 := hN n hn
    rw [Real.dist_eq] at h1
    have h2 : u n - a < 1 := (abs_lt.mp h1).2
    have h3 : a + 1 ≤ max (max 0 (a + 1)) (a + 1) := le_max_right _ _
    linarith
  refine ⟨max (max (max 0 (a + 1)) (a + 1))
    (Finset.sup' (Finset.range (N + 1))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ u),
    le_trans (le_max_left 0 (a + 1)) (le_trans (le_max_left (max 0 (a + 1)) (a + 1))
      (le_max_left _ _)), fun n => ?_⟩
  by_cases hn : n < N + 1
  · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr hn
    exact le_trans (Finset.le_sup' u hmem) (le_max_right _ _)
  · push Not at hn
    exact le_trans (htail n (by omega)) (le_max_left _ _)

/-! ### The moment at a weak limit -/

/-- The chi-square law with one degree of freedom, as a probability measure on `ℝ`. -/
noncomputable def chiSq : ProbabilityMeasure ℝ :=
  ⟨gammaMeasure (1 / 2) (1 / 2), isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)⟩

lemma chiSq_coe : (chiSq : Measure ℝ) = gammaMeasure (1 / 2) (1 / 2) := rfl

/-- The clamping function as a bounded continuous test function. -/
noncomputable def clampBCF (k : ℕ) {R : ℝ} (hR : 0 ≤ R) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (clamp k R) (continuous_clamp k R) R
    (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_clamp_le k hR x)

lemma clampBCF_apply (k : ℕ) {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : clampBCF k hR x = clamp k R x :=
  rfl

/-- If `ρ n → ν` weakly, the `k`-th moments of `ρ n` are finite and tend to `m`, and the `2k`-th
absolute moments are bounded by `C`, then `ν` has a finite `k`-th moment and it equals `m`. -/
theorem integral_pow_eq_of_tendsto {ρ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto ρ atTop (𝓝 ν)) (k : ℕ) {C m : ℝ} (hC0 : 0 ≤ C)
    (hint2 : ∀ n, Integrable (fun x : ℝ => |x| ^ (2 * k)) (ρ n : Measure ℝ))
    (hbound : ∀ n, ∫ x, |x| ^ (2 * k) ∂(ρ n : Measure ℝ) ≤ C)
    (hm : Tendsto (fun n => ∫ x, x ^ k ∂(ρ n : Measure ℝ)) atTop (𝓝 m)) :
    Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) ∧ ∫ x, x ^ k ∂(ν : Measure ℝ) = m := by
  -- the `2k`-th absolute moment of the limit
  have hνlin : ∫⁻ x, ENNReal.ofReal (|x| ^ (2 * k)) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal C :=
    lintegral_abs_pow_le_of_tendsto hconv (2 * k) hint2 hbound
  have hνint2 : Integrable (fun x : ℝ => |x| ^ (2 * k)) (ν : Measure ℝ) := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hcongr : (fun x : ℝ => ENNReal.ofReal ‖|x| ^ (2 * k)‖)
        = fun x : ℝ => ENNReal.ofReal (|x| ^ (2 * k)) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hcongr]
    exact lt_of_le_of_lt hνlin ENNReal.ofReal_lt_top
  have hνbound : ∫ x, |x| ^ (2 * k) ∂(ν : Measure ℝ) ≤ C := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x| ^ (2 * k)) (ν : Measure ℝ))]
    calc (∫⁻ x, ENNReal.ofReal (|x| ^ (2 * k)) ∂(ν : Measure ℝ)).toReal
        ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hνlin
      _ = C := ENNReal.toReal_ofReal hC0
  -- the `k`-th moment of the limit is finite
  have hνint : Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) := by
    refine Integrable.mono' (hνint2.add (integrable_const (1 : ℝ))) (by fun_prop)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    have h2 : |x| ^ k ≤ |x| ^ (2 * k) + 1 := by
      by_cases hle : |x| ^ k ≤ 1
      · linarith [pow_nonneg (abs_nonneg x) (2 * k)]
      · push Not at hle
        have h4 : |x| ^ k ≤ |x| ^ (2 * k) := by
          rw [pow_two_mul_eq_sq]
          nlinarith
        linarith
    simpa using h2
  refine ⟨hνint, ?_⟩
  -- the sandwich
  have hconv_clamp : ∀ R : ℝ, 0 < R → Tendsto (fun n => ∫ x, clamp k R x ∂(ρ n : Measure ℝ))
      atTop (𝓝 (∫ x, clamp k R x ∂(ν : Measure ℝ))) := by
    intro R hR
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) (clampBCF k hR.le)
  have hkey : ∀ R : ℝ, 0 < R → |∫ x, x ^ k ∂(ν : Measure ℝ) - m| ≤ 4 * C / R := by
    intro R hR
    set B : ℝ := 2 / R * C with hB
    have h1 : |∫ x, x ^ k ∂(ν : Measure ℝ) - ∫ x, clamp k R x ∂(ν : Measure ℝ)| ≤ B :=
      (abs_integral_pow_sub_clamp_le (ν : Measure ℝ) k hR hνint2).trans
        (mul_le_mul_of_nonneg_left hνbound (by positivity))
    have h2 : ∀ n, |∫ x, clamp k R x ∂(ρ n : Measure ℝ) - ∫ x, x ^ k ∂(ρ n : Measure ℝ)|
        ≤ B := by
      intro n
      rw [abs_sub_comm]
      exact (abs_integral_pow_sub_clamp_le (ρ n : Measure ℝ) k hR (hint2 n)).trans
        (mul_le_mul_of_nonneg_left (hbound n) (by positivity))
    have hε : ∀ ε : ℝ, 0 < ε → |∫ x, x ^ k ∂(ν : Measure ℝ) - m| ≤ B + B + ε := by
      intro ε hε
      have hε2 : (0 : ℝ) < ε / 2 := by linarith
      have hev1 : ∀ᶠ n : ℕ in atTop,
          |∫ x, clamp k R x ∂(ρ n : Measure ℝ) - ∫ x, clamp k R x ∂(ν : Measure ℝ)| < ε / 2 := by
        have hc := (Metric.tendsto_nhds.mp (hconv_clamp R hR)) (ε / 2) hε2
        filter_upwards [hc] with n hn
        rw [Real.dist_eq] at hn
        simpa only [abs_sub_comm] using hn
      have hev2 : ∀ᶠ n : ℕ in atTop, |∫ x, x ^ k ∂(ρ n : Measure ℝ) - m| < ε / 2 := by
        have hc := (Metric.tendsto_nhds.mp hm) (ε / 2) hε2
        filter_upwards [hc] with n hn
        rwa [Real.dist_eq] at hn
      obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
      have hchain : |∫ x, x ^ k ∂(ν : Measure ℝ) - m|
          ≤ |∫ x, x ^ k ∂(ν : Measure ℝ) - ∫ x, clamp k R x ∂(ν : Measure ℝ)|
            + (|∫ x, clamp k R x ∂(ν : Measure ℝ) - ∫ x, clamp k R x ∂(ρ n : Measure ℝ)|
            + (|∫ x, clamp k R x ∂(ρ n : Measure ℝ) - ∫ x, x ^ k ∂(ρ n : Measure ℝ)|
            + |∫ x, x ^ k ∂(ρ n : Measure ℝ) - m|)) := by
        have hrw : ∫ x, x ^ k ∂(ν : Measure ℝ) - m
            = (∫ x, x ^ k ∂(ν : Measure ℝ) - ∫ x, clamp k R x ∂(ν : Measure ℝ))
              + ((∫ x, clamp k R x ∂(ν : Measure ℝ) - ∫ x, clamp k R x ∂(ρ n : Measure ℝ))
              + ((∫ x, clamp k R x ∂(ρ n : Measure ℝ) - ∫ x, x ^ k ∂(ρ n : Measure ℝ))
              + (∫ x, x ^ k ∂(ρ n : Measure ℝ) - m))) := by ring
        rw [hrw]
        refine (abs_add_le _ _).trans ?_
        have hstep : |(∫ x, clamp k R x ∂(ν : Measure ℝ) - ∫ x, clamp k R x ∂(ρ n : Measure ℝ))
            + ((∫ x, clamp k R x ∂(ρ n : Measure ℝ) - ∫ x, x ^ k ∂(ρ n : Measure ℝ))
            + (∫ x, x ^ k ∂(ρ n : Measure ℝ) - m))|
            ≤ |∫ x, clamp k R x ∂(ν : Measure ℝ) - ∫ x, clamp k R x ∂(ρ n : Measure ℝ)|
            + (|∫ x, clamp k R x ∂(ρ n : Measure ℝ) - ∫ x, x ^ k ∂(ρ n : Measure ℝ)|
            + |∫ x, x ^ k ∂(ρ n : Measure ℝ) - m|) := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
        linarith
      have hb1 := h1
      have hb2 := h2 n
      have hb3 : |∫ x, clamp k R x ∂(ν : Measure ℝ) - ∫ x, clamp k R x ∂(ρ n : Measure ℝ)|
          < ε / 2 := by simpa only [abs_sub_comm] using hn1
      have hb4 : |∫ x, x ^ k ∂(ρ n : Measure ℝ) - m| < ε / 2 := hn2
      linarith
    have hfin : |∫ x, x ^ k ∂(ν : Measure ℝ) - m| ≤ B + B := le_of_forall_pos_le_add hε
    have hBB : B + B = 4 * C / R := by
      rw [hB]; field_simp; ring
    linarith
  have hlim : Tendsto (fun R : ℝ => 4 * C / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hfin : |∫ x, x ^ k ∂(ν : Measure ℝ) - m| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.mono (eventually_gt_atTop (0 : ℝ)) fun R hR => hkey R hR)
  have : ∫ x, x ^ k ∂(ν : Measure ℝ) - m = 0 := abs_eq_zero.mp (le_antisymm hfin (abs_nonneg _))
  linarith

/-! ### Support in `[0,∞)` is preserved in the limit -/

lemma ae_nonneg_of_tendsto (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hconv : Tendsto μ atTop (𝓝 ν)) (hsup : ∀ n, ∀ᵐ x ∂(μ n : Measure ℝ), 0 ≤ x) :
    ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x := by
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv
    (isClosed_Ici (a := (0 : ℝ)))
  have hone : ∀ n, (μ n : Measure ℝ) (Set.Ici (0 : ℝ)) = 1 := by
    intro n
    have h0 : (μ n : Measure ℝ) (Set.Iio (0 : ℝ)) = 0 := by
      have h1 := ae_iff.mp (hsup n)
      rwa [show {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 from by ext x; simp] at h1
    rw [← Set.compl_Iio, measure_compl measurableSet_Iio (measure_ne_top _ _), h0, measure_univ,
      tsub_zero]
  have hν1 : (ν : Measure ℝ) (Set.Ici (0 : ℝ)) = 1 := by
    refine le_antisymm ?_ ?_
    · calc (ν : Measure ℝ) (Set.Ici (0 : ℝ)) ≤ (ν : Measure ℝ) Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    calc (1 : ℝ≥0∞) = atTop.limsup (fun n => (μ n : Measure ℝ) (Set.Ici (0 : ℝ))) := by
          simp [hone]
      _ ≤ (ν : Measure ℝ) (Set.Ici (0 : ℝ)) := hlim
  rw [ae_iff]
  rw [show {x : ℝ | ¬ 0 ≤ x} = (Set.Ici (0 : ℝ))ᶜ from by ext x; simp,
    measure_compl measurableSet_Ici (measure_ne_top _ _), measure_univ, hν1, tsub_self]

/-! ### Identification of every weak subsequential limit -/

open PercLib.CriticalLRP.MomentProblem in
/-- **Every weak subsequential limit is the chi-square law.** Along a subsequence, the moment
hypotheses pass to the limit `ν'` (`integral_pow_eq_of_tendsto`), and moment determinacy
(`eq_gammaMeasure_of_forall_moment_eq`) identifies `ν'`. -/
theorem subseq_limit_eq_chiSq (μ : ℕ → ProbabilityMeasure ℝ)
    (hsup : ∀ n, ∀ᵐ x ∂(μ n : Measure ℝ), 0 ≤ x)
    (hint : ∀ (n k : ℕ), Integrable (fun x : ℝ => x ^ k) (μ n : Measure ℝ))
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ x, x ^ k ∂(μ n : Measure ℝ)) atTop
      (𝓝 ((oddFact k : ℝ))))
    {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop) {ν' : ProbabilityMeasure ℝ}
    (hconv : Tendsto (fun n => μ (σ n)) atTop (𝓝 ν')) : ν' = chiSq := by
  have hmomν : ∀ k : ℕ, ∫ x, x ^ k ∂(ν' : Measure ℝ)
      = ∫ x, x ^ k ∂(gammaMeasure (1 / 2) (1 / 2)) := by
    intro k
    obtain ⟨Ck, hCk0, hCk⟩ := exists_bound_of_tendsto (hmom (2 * k))
    have hint2 : ∀ n, Integrable (fun x : ℝ => |x| ^ (2 * k)) (μ n : Measure ℝ) := by
      intro n
      have h := hint n (2 * k)
      convert h using 1
      funext x
      exact abs_pow_two_mul x k
    have hbound : ∀ n, ∫ x, |x| ^ (2 * k) ∂(μ n : Measure ℝ) ≤ Ck := by
      intro n
      rw [show (fun x : ℝ => |x| ^ (2 * k)) = fun x => x ^ (2 * k) from by
        funext x; exact abs_pow_two_mul x k]
      exact hCk n
    have hmσ : Tendsto (fun n => ∫ x, x ^ k ∂(μ (σ n) : Measure ℝ)) atTop
        (𝓝 ((oddFact k : ℝ))) := by
      simpa only [Function.comp_def] using (hmom k).comp hσ
    have hres := integral_pow_eq_of_tendsto hconv k hCk0 (fun n => hint2 (σ n))
      (fun n => hbound (σ n)) hmσ
    rw [integral_pow_gammaMeasure_one_half k]
    exact hres.2
  have hsupp : ∀ᵐ x ∂(ν' : Measure ℝ), 0 ≤ x :=
    ae_nonneg_of_tendsto (fun n => μ (σ n)) ν' hconv (fun n => hsup (σ n))
  have hI : IsFiniteMeasure (ν' : Measure ℝ) := inferInstance
  have key := eq_gammaMeasure_of_forall_moment_eq hsupp hmomν
  exact Subtype.ext key

/-! ### Tightness and the main theorem -/

open PercLib.CriticalLRP.MomentProblem in
/-- **Moment convergence to the chi-square moments implies weak convergence.**

Let `μ n` be probability laws on `[0, ∞)` with finite moments of every order, and suppose that for
every `k` the `k`-th moment of `μ n` tends to the `k`-th moment `(2k-1)!!` of the chi-square law
with one degree of freedom. Then `μ n` converges weakly to that law.

This is the step that Hutchcroft, *Critical long-range percolation I*, proof of (I.1.7), carries out
"by Carleman's criterion": bounded second moments give tightness (Prokhorov), every weak
subsequential limit is the chi-square law (`subseq_limit_eq_chiSq`), and convergence of all
subsequences forces convergence of the sequence. -/
theorem tendsto_chiSq_of_moment_tendsto (μ : ℕ → ProbabilityMeasure ℝ)
    (hsup : ∀ n, ∀ᵐ x ∂(μ n : Measure ℝ), 0 ≤ x)
    (hint : ∀ (n k : ℕ), Integrable (fun x : ℝ => x ^ k) (μ n : Measure ℝ))
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ x, x ^ k ∂(μ n : Measure ℝ)) atTop
      (𝓝 ((oddFact k : ℝ)))) :
    Tendsto μ atTop (𝓝 chiSq) := by
  -- tightness from the bounded second moments
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_tendsto (hmom 2)
  have htight : IsTightMeasureSet {x | ∃ n, ((μ n : ProbabilityMeasure ℝ) : Measure ℝ) = x} :=
    isTightMeasureSet_range_of_second_moment μ hC0 (fun n => hint n 2) hC
  have hS : IsCompact (closure (Set.range μ)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert htight using 2
    ext x
    simp [eq_comm]
  -- every subsequence has a further subsequence converging to the chi-square law
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hmem : ∀ n, μ (ns n) ∈ closure (Set.range μ) := fun n => subset_closure ⟨ns n, rfl⟩
  obtain ⟨ν', -, φ, hφ, hconv⟩ := hS.tendsto_subseq hmem
  refine ⟨φ, ?_⟩
  have hσ : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hconv' : Tendsto (fun n => μ (ns (φ n))) atTop (𝓝 ν') := hconv
  have hν' : ν' = chiSq := subseq_limit_eq_chiSq μ hsup hint hmom hσ hconv'
  rwa [hν'] at hconv'

open PercLib.CriticalLRP.MomentProblem in
/-- The `L¹` form of the main theorem: every bounded continuous test function has convergent
integrals. -/
theorem tendsto_integral_of_moment_tendsto (μ : ℕ → ProbabilityMeasure ℝ)
    (hsup : ∀ n, ∀ᵐ x ∂(μ n : Measure ℝ), 0 ≤ x)
    (hint : ∀ (n k : ℕ), Integrable (fun x : ℝ => x ^ k) (μ n : Measure ℝ))
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ x, x ^ k ∂(μ n : Measure ℝ)) atTop
      (𝓝 ((oddFact k : ℝ)))) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂(μ n : Measure ℝ)) atTop (𝓝 (∫ x, f x ∂(chiSq : Measure ℝ))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_chiSq_of_moment_tendsto μ hsup hint hmom)) f

/-! ### Support in `[0,∞)` from a vanishing lower half-line -/

lemma ae_nonneg_of_measure_Iio {μ : Measure ℝ} (h : μ (Set.Iio (0 : ℝ)) = 0) :
    ∀ᵐ x ∂μ, 0 ≤ x := by
  rw [ae_iff]
  rwa [show {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 from by ext x; simp]

/-! ### The radius-indexed form -/

open PercLib.CriticalLRP.MomentProblem in
/-- **Radius-indexed form of the main theorem.** The same conclusion for a family indexed by a real
radius `r → ∞`, which is the shape of the source's laws `Q_r` in the proof of (I.1.7) and of the
weak-convergence hypothesis of `PercLib.CriticalLRP.Analysis.ClusterVolumeTail.I17`. -/
theorem tendsto_chiSq_of_moment_tendsto_real (Q : ℝ → ProbabilityMeasure ℝ)
    (hsup : ∀ r, ∀ᵐ x ∂(Q r : Measure ℝ), 0 ≤ x)
    (hint : ∀ (r : ℝ) (k : ℕ), Integrable (fun x : ℝ => x ^ k) (Q r : Measure ℝ))
    (hmom : ∀ k : ℕ, Tendsto (fun r : ℝ => ∫ x, x ^ k ∂(Q r : Measure ℝ)) atTop
      (𝓝 ((oddFact k : ℝ)))) :
    Tendsto Q atTop (𝓝 chiSq) := by
  rw [tendsto_iff_seq_tendsto]
  intro σ hσ
  exact tendsto_chiSq_of_moment_tendsto (fun n => Q (σ n)) (fun n => hsup (σ n))
    (fun n k => hint (σ n) k) (fun k => by
      simpa only [Function.comp_def] using (hmom k).comp hσ)

open PercLib.CriticalLRP.MomentProblem in
/-- The radius-indexed form for a family of raw measures, in the shape of the hypotheses of
`Analysis/ClusterVolumeTail/I17`. -/
theorem tendsto_toProbabilityMeasure_chiSq (mu : ℝ → Measure ℝ)
    [inst : ∀ r, IsProbabilityMeasure (mu r)]
    (hsup : ∀ r, mu r (Set.Iio (0 : ℝ)) = 0)
    (hint : ∀ (r : ℝ) (k : ℕ), Integrable (fun x : ℝ => x ^ k) (mu r))
    (hmom : ∀ k : ℕ, Tendsto (fun r : ℝ => ∫ x, x ^ k ∂(mu r)) atTop
      (𝓝 ((oddFact k : ℝ)))) :
    Tendsto (fun r => Measure.toProbabilityMeasure (mu r)) atTop (𝓝 chiSq) := by
  have hsup' : ∀ r, ∀ᵐ x ∂(Measure.toProbabilityMeasure (mu r) : Measure ℝ), 0 ≤ x := by
    intro r
    have hcoe : (Measure.toProbabilityMeasure (mu r) : Measure ℝ) = mu r := rfl
    rw [hcoe]
    exact ae_nonneg_of_measure_Iio (hsup r)
  have hQ : (fun r => Measure.toProbabilityMeasure (mu r))
      = fun r => (⟨mu r, inst r⟩ : ProbabilityMeasure ℝ) := rfl
  rw [hQ]
  refine tendsto_chiSq_of_moment_tendsto_real _ hsup' ?_ ?_
  · intro r k
    exact hint r k
  · intro k
    refine (hmom k).congr' (Eventually.of_forall fun r => ?_)
    rfl

end SwarmM4

/-! ### Axiom audit -/

set_option linter.hashCommand false

#print axioms SwarmM4.tendsto_chiSq_of_moment_tendsto
#print axioms SwarmM4.tendsto_integral_of_moment_tendsto
#print axioms SwarmM4.subseq_limit_eq_chiSq
#print axioms SwarmM4.integral_pow_eq_of_tendsto
#print axioms SwarmM4.isTightMeasureSet_range_of_second_moment
#print axioms SwarmM4.mul_measure_compl_Icc_le
#print axioms SwarmM4.tendsto_chiSq_of_moment_tendsto_real
#print axioms SwarmM4.tendsto_toProbabilityMeasure_chiSq
