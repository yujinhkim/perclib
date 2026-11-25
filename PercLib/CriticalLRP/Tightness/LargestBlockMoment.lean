/-
# The edian `M_β(W)` is the typical size of the largest cluster: explicit constants

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.2.1 ("the typical size of the largest cluster in the box `B_r`
under the cut-off measure `P_{β_c,r}`"), Theorem I.2.3.

Theorem I.2.3 exhibits the edian `M_β(Λ)` of `|K_max(Λ)|` as the scale of the exponential tail.
This module records the two-sided quantitative meaning of that scale for the *first moment of the
maximum cluster size itself*, with explicit constants:

  `(M_β(W) - 1)/e  ≤  E_β |K_max(W)|  ≤  10 M_β(W)`.

The lower bound is the abstract Markov step of Lemma I.2.6 already available in
`Tightness/RealExponent.lean` (`edian_sub_one_div_exp_le_lintegral`); the upper bound is new and
uses only the maximum-cluster tail (I.2.4) together with the integer-valued discrete layer cake
`∫⁻ X = ∑_n μ{X ≥ n+1}`.  The geometric factor uses `1 - e^{-s} ≥ s/(1+s)`, equivalently
`e^s ≥ 1 + s`, and gives the constant `1 + 9 = 10`.

Neither direction needs subcriticality, a moment-finiteness input, or the pointed tail (I.2.6):
both hold for every non-empty finite window and every probability measure for which the per-scale
display (2.8) holds (which the long-range law satisfies by `display28_longRange`).

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Tightness.Universal
public import PercLib.CriticalLRP.Tightness.RealExponent
public import PercLib.CriticalLRP.Tightness.BlockMaximum

/-!
# Largest-cluster tail scale and first moment

The finite-window maximum-cluster size has lower mean bound `(M−1)/e` and upper
mean bound `10 M`, where `M` is the repository's `edianMaxVol` cutoff tail median.
The proof uses the maximum-cluster tail estimate and an exact integer layer-cake sum.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

namespace Percolation

variable {V : Type*} [Countable V]

/-! ### The lower bound: the edian is at most `e` times the first moment -/

/-- `(M_β(W) - 1)/e ≤ E|K_max(W)|`, the abstract Markov half of Lemma I.2.6 at the maximum
cluster size. -/
theorem edian_sub_one_div_exp_le_lintegral_clusterMaxVol {μ : Measure (Config V)}
    [IsProbabilityMeasure μ] (W : Finset V) :
    ENNReal.ofReal (((edianMaxVol μ W (exists_edianMaxVol W) : ℝ) - 1) / Real.exp 1) ≤
      ∫⁻ ω, clusterMaxVol ω W ∂μ := by
  have hempty : {ω : Config V | clusterMaxVol ω W = ⊤} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    have hle : clusterMaxVol ω W ≤ ((W.card : ℕ) : ℝ≥0∞) := clusterMaxVol_le_card ω W
    rw [hω] at hle
    exact ENNReal.natCast_ne_top W.card (top_le_iff.mp hle)
  have hfin : μ {ω : Config V | clusterMaxVol ω W = ⊤} = 0 := by
    rw [hempty, measure_empty]
  exact edian_sub_one_div_exp_le_lintegral (μ := μ)
    (X := fun ω => clusterMaxVol ω W) (measurable_clusterMaxVol W) hfin
    (hex := exists_edianMaxVol W)

/-! ### The upper bound: the first moment is at most `10` edians -/

/-- `E|K_max(W)| ≤ 10 M_β(W)` from the maximum-cluster tail (I.2.4). -/
theorem lintegral_clusterMaxVol_le_ten_mul_edian {μ : Measure (Config V)}
    [IsProbabilityMeasure μ] (W : Finset V)
    (h28 : Display28 μ (fun ω => clusterMaxVol ω W)) :
    ∫⁻ ω, clusterMaxVol ω W ∂μ ≤
      ENNReal.ofReal 10 * ENNReal.ofReal ((edianMaxVol μ W (exists_edianMaxVol W) : ℝ)) := by
  classical
  set M : ℕ := edianMaxVol μ W (exists_edianMaxVol W) with hMdef
  have hM1 : 1 ≤ M := one_le_edianMaxVol W (exists_edianMaxVol W)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have h24 : TailMaxI24 μ (fun ω => clusterMaxVol ω W) M := by
    simpa only [hMdef] using tailMaxI24_at_edian W h28
  set S : ℕ → ℝ≥0∞ := fun n => μ {ω : Config V | ((n : ℝ≥0∞) + 1) ≤ clusterMaxVol ω W}
    with hSdef
  -- the layer cake
  have hlc : ∫⁻ ω, clusterMaxVol ω W ∂μ = ∑' n : ℕ, S n := by
    exact Tightness.lintegral_eq_tsum_meas_ge (μ := μ)
      (X := fun ω => clusterMaxVol ω W) (measurable_clusterMaxVol W)
      (fun ω => clusterMaxVol_integer ω W)
  -- split the sum at the edian
  have hsplit : (∑' n : ℕ, S n) =
      (∑' n : ℕ, (if n < M then S n else 0)) + (∑' n : ℕ, (if n < M then 0 else S n)) := by
    rw [← ENNReal.tsum_add]
    congr 1
    funext n
    by_cases h : n < M <;> simp [h]
  -- each layer has measure at most one
  have hS_le_one : ∀ n : ℕ, S n ≤ 1 := by
    intro n
    rw [hSdef]
    calc μ {ω : Config V | ((n : ℝ≥0∞) + 1) ≤ clusterMaxVol ω W} ≤ μ Set.univ :=
          measure_mono (subset_univ _)
      _ = 1 := measure_univ
  -- the lower part of the sum
  have hlow : (∑' n : ℕ, (if n < M then S n else 0)) ≤ (M : ℝ≥0∞) := by
    rw [tsum_eq_sum (s := Finset.range M) (fun b hb => by
      rw [Finset.mem_range, not_lt] at hb
      simp [hb])]
    calc ∑ n ∈ Finset.range M, (if n < M then S n else 0) ≤ ∑ _n ∈ Finset.range M, (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [ite_eq_left (Finset.mem_range.mp hn)]
          exact hS_le_one n
      _ = (M : ℝ≥0∞) := by simp
  -- the exponential tail for the layers above the edian
  have hS_tail : ∀ n : ℕ, M ≤ n →
      S n ≤ ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) / (9 * (M : ℝ))))) := by
    intro n hn
    have hn' : (M : ℝ) ≤ (n : ℝ) + 1 := by
      have : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hcast : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
    rw [hSdef]
    change μ {ω : Config V | ((n : ℝ≥0∞) + 1) ≤ clusterMaxVol ω W} ≤
      ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) / (9 * (M : ℝ)))))
    rw [hcast]
    exact h24 ((n : ℝ) + 1) hn'
  -- the geometric majorant
  set q : ℝ := Real.exp (-(1 / (9 * (M : ℝ)))) with hqdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq_lt : q < 1 := by
    rw [hqdef, Real.exp_lt_one_iff]
    have hpos : (0 : ℝ) < 1 / (9 * (M : ℝ)) := by positivity
    linarith
  have hterm : ∀ n : ℕ, (if n < M then 0 else S n) ≤ ENNReal.ofReal (q ^ (n + 1)) := by
    intro n
    by_cases hn : n < M
    · simp [hn]
    · rw [ite_eq_right hn]
      refine le_trans (hS_tail n (by omega)) ?_
      rw [hqdef]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp : Real.exp (-(1 / (9 * (M : ℝ)))) ^ (n + 1) =
          Real.exp (-(((n : ℝ) + 1) / (9 * (M : ℝ)))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        (field_simp [hMpos.ne']; norm_num [Nat.cast_add, Nat.cast_one])
      rw [hexp]
  -- the geometric series value
  have hgeom : (∑' n : ℕ, q ^ (n + 1)) = q * (1 - q)⁻¹ := by
    rw [show (∑' n : ℕ, q ^ (n + 1)) = ∑' n : ℕ, q * q ^ n by
      congr 1
      funext n
      rw [pow_succ]
      ring]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  -- the explicit geometric bound
  have hgeom_le : q * (1 - q)⁻¹ ≤ 9 * (M : ℝ) := by
    have hq_lt' : (0 : ℝ) < 1 - q := by linarith
    have hs : (0 : ℝ) < 1 / (9 * (M : ℝ)) := by positivity
    -- `1 - e^{-s} ≥ s/(1+s)`, equivalently `e^s ≥ 1 + s`
    have hexp : 1 + 1 / (9 * (M : ℝ)) ≤ Real.exp (1 / (9 * (M : ℝ))) := by
      have := Real.add_one_le_exp (1 / (9 * (M : ℝ)))
      linarith
    have hq_le : q ≤ (1 + 1 / (9 * (M : ℝ)))⁻¹ := by
      rw [hqdef, Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) (by linarith)).mpr hexp
    have hkey : 1 / (9 * (M : ℝ) + 1) ≤ 1 - q := by
      have h1 : 1 - (1 + 1 / (9 * (M : ℝ)))⁻¹ = 1 / (9 * (M : ℝ) + 1) := by
        field_simp
        ring
      rw [← h1]
      linarith
    have hinv : (1 - q)⁻¹ ≤ 9 * (M : ℝ) + 1 := by
      have hpos : (0 : ℝ) < 1 / (9 * (M : ℝ) + 1) := by positivity
      have := (inv_le_inv₀ hq_lt' hpos).mpr hkey
      rwa [one_div, inv_inv] at this
    have hq1 : q ≤ 1 := le_of_lt hq_lt
    have hsplit' : q * (1 - q)⁻¹ = (1 - q)⁻¹ - 1 := by
      field_simp
      ring
    rw [hsplit']
    linarith
  -- assemble
  have hhigh : (∑' n : ℕ, (if n < M then 0 else S n)) ≤ ENNReal.ofReal (9 * (M : ℝ)) := by
    refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
    have hqnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
    have hsummable : Summable (fun n : ℕ => q ^ (n + 1)) := by
      have hs := (summable_geometric_of_norm_lt_one hqnorm).mul_left q
      simpa only [pow_succ'] using hs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hq0 (n + 1)) hsummable,
      hgeom]
    exact ENNReal.ofReal_le_ofReal hgeom_le
  rw [hlc, hsplit]
  calc (∑' n : ℕ, (if n < M then S n else 0)) + (∑' n : ℕ, (if n < M then 0 else S n))
      ≤ (M : ℝ≥0∞) + ENNReal.ofReal (9 * (M : ℝ)) := add_le_add hlow hhigh
    _ = ENNReal.ofReal 10 * ENNReal.ofReal ((M : ℝ)) := by
        have h10 : (10 : ℝ) * (M : ℝ) = (M : ℝ) + 9 * (M : ℝ) := by ring
        have h10' := congrArg ENNReal.ofReal h10
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)] at h10'
        rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact h10'.symm

end Percolation

end PercLib.CriticalLRP
