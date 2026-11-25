/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
**Injectivity of the Laplace transform on `L¹`** — the uniqueness step of the Tauberian
converse of Hutchcroft, Theorem I.2.11.

If `D ∈ L¹(0,∞)` and `∫_0^∞ e^{-σu} D u du = 0` for *every* `σ > 0`, then `D = 0` a.e.

The proof is elementary: using the integer rates gives the vanishing of
`∫_0^∞ q (e^{-u}) D u` for every polynomial `q`; Weierstrass' theorem upgrades this to every
continuous `φ` on `[0,1]`; trapezoid functions then give `∫_{(a,b)} D = 0` for all intervals,
and the Lebesgue differentiation theorem finishes.
-/
module

public import PercLib.CriticalLRP.Analysis.TauberianLaplace

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ENNReal Polynomial

namespace PercLib.CriticalLRP.Analysis

/-! ### Step 1: the total integral vanishes -/

theorem integral_eq_zero_of_forall_laplace_eq_zero {D : ℝ → ℝ}
    (hD : IntegrableOn D (Ioi (0:ℝ)))
    (hlaplace : ∀ σ : ℝ, 0 < σ → ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * D u = 0) :
    ∫ u in Ioi (0:ℝ), D u = 0 := by
  classical
  set μ := volume.restrict (Ioi (0:ℝ)) with hμ
  have hDμ : Integrable D μ := hD
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-(((1:ℝ)/((n:ℝ)+1))*u)) * D u) μ := by
    filter_upwards with n
    exact (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).neg)).aestronglyMeasurable.mul hDμ.aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ u ∂μ,
      ‖Real.exp (-(((1:ℝ)/((n:ℝ)+1))*u)) * D u‖ ≤ ‖D u‖ := by
    filter_upwards with n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : (0:ℝ) < u := hu
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    have h1 : |Real.exp (-(((1:ℝ)/((n:ℝ)+1))*u))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have hc : (0:ℝ) ≤ 1/((n:ℝ)+1) := by positivity
      nlinarith
    calc |Real.exp (-(((1:ℝ)/((n:ℝ)+1))*u))| * |D u|
        ≤ 1 * |D u| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |D u| := one_mul _
  have hint : Integrable (fun u : ℝ => ‖D u‖) μ := hDμ.norm
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun n : ℕ => Real.exp (-(((1:ℝ)/((n:ℝ)+1))*u)) * D u)
      atTop (𝓝 (D u)) := by
    filter_upwards with u
    have hc : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => -(((1:ℝ)/((n:ℝ)+1))*u)) atTop (𝓝 0) := by
      simpa using (hc.mul_const u).neg
    have h3 : Tendsto (fun n : ℕ => Real.exp (-(((1:ℝ)/((n:ℝ)+1))*u))) atTop (𝓝 1) := by
      simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp h2
    simpa using h3.mul_const (D u)
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (F := fun n : ℕ => fun u : ℝ => Real.exp (-(((1:ℝ)/((n:ℝ)+1))*u)) * D u)
    (f := D) (bound := fun u => ‖D u‖) hmeas hbound hint hlim
  have hzero : ∀ n : ℕ, ∫ u, Real.exp (-(((1:ℝ)/((n:ℝ)+1))*u)) * D u ∂μ = 0 := by
    intro n
    exact hlaplace _ (by positivity)
  have h2 : Tendsto (fun n : ℕ => ∫ u, Real.exp (-(((1:ℝ)/((n:ℝ)+1))*u)) * D u ∂μ)
      atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hmain h2

/-! ### Step 2: polynomial weights in `e^{-u}` -/

theorem integral_eval_exp_mul_eq_zero {D : ℝ → ℝ}
    (hD : IntegrableOn D (Ioi (0:ℝ)))
    (hlaplace : ∀ σ : ℝ, 0 < σ → ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * D u = 0) :
    ∀ p : ℝ[X], ∫ u in Ioi (0:ℝ), p.eval (Real.exp (-u)) * D u = 0 := by
  classical
  set μ := volume.restrict (Ioi (0:ℝ)) with hμ
  have hDμ : Integrable D μ := hD
  -- the integer rates
  have hpow : ∀ k : ℕ, ∫ u, Real.exp (-((k:ℝ)*u)) * D u ∂μ = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simpa using integral_eq_zero_of_forall_laplace_eq_zero hD hlaplace
    · have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
      exact hlaplace (k:ℝ) hkpos
  -- integrability of a monomial times `D`
  have hint_term : ∀ k : ℕ, Integrable (fun u : ℝ => (Real.exp (-u))^k * D u) μ := by
    intro k
    refine hDμ.norm.mono' ?_ ?_
    · exact (Real.continuous_exp.comp continuous_id.neg).aestronglyMeasurable.pow k |>.mul hDμ.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : (0:ℝ) < u := hu
      have hle : |(Real.exp (-u))^k| ≤ 1 := by
        rw [abs_pow, abs_of_pos (Real.exp_pos _)]
        exact pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
      have hgoal : |(Real.exp (-u))^k * D u| ≤ |D u| := by
        rw [abs_mul]
        calc |(Real.exp (-u))^k| * |D u| ≤ 1 * |D u| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
          _ = |D u| := one_mul _
      simpa [Real.norm_eq_abs] using hgoal
  -- each monomial contributes zero
  have hmono : ∀ k : ℕ, ∫ u, (Real.exp (-u))^k * D u ∂μ = 0 := by
    intro k
    have h1 : (fun u : ℝ => (Real.exp (-u))^k * D u)
        = fun u : ℝ => Real.exp (-((k:ℝ)*u)) * D u := by
      ext u
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    rw [h1]
    exact hpow k
  intro p
  have hsplit : ∀ u : ℝ,
      p.eval (Real.exp (-u)) * D u
        = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * ((Real.exp (-u))^k * D u) := by
    intro u
    rw [Polynomial.eval_eq_sum_range]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  simp only [hsplit]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [integral_const_mul, hmono k, mul_zero]
  · intro k _
    exact (hint_term k).const_mul (p.coeff k)

/-- A bounded measurable factor preserves integrability of `D` against the weight `D`. -/
theorem integrableOn_mul_of_norm_bound {D g : ℝ → ℝ} (hD : IntegrableOn D (Ioi (0:ℝ)))
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi (0:ℝ))))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), ‖g u‖ ≤ C) :
    IntegrableOn (fun u => g u * D u) (Ioi (0:ℝ)) := by
  refine (hD.norm.const_mul C).mono' (hgm.mul hD.aestronglyMeasurable) ?_
  filter_upwards [hC] with u hu
  have hu' : |g u| ≤ C := by rwa [Real.norm_eq_abs] at hu
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hu' (abs_nonneg (D u))

/-! ### Step 3: continuous weights in `e^{-u}` -/

theorem integral_comp_exp_mul_eq_zero {D : ℝ → ℝ}
    (hD : IntegrableOn D (Ioi (0:ℝ)))
    (hlaplace : ∀ σ : ℝ, 0 < σ → ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * D u = 0)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (0:ℝ) 1)) :
    ∫ u in Ioi (0:ℝ), φ (Real.exp (-u)) * D u = 0 := by
  classical
  set μ := volume.restrict (Ioi (0:ℝ)) with hμ
  have hDμ : Integrable D μ := hD
  -- measurability of `u ↦ φ (e^{-u})` on `(0,∞)`
  have hφcont : ContinuousOn (fun u : ℝ => φ (Real.exp (-u))) (Ioi 0) := by
    refine hφ.comp ?_ ?_
    · exact (Real.continuous_exp.comp continuous_id.neg).continuousOn
    · intro u hu
      have hu' : (0:ℝ) < u := hu
      exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have hφmeas : AEStronglyMeasurable (fun u : ℝ => φ (Real.exp (-u))) μ :=
    hφcont.aestronglyMeasurable measurableSet_Ioi
  -- the approximation argument
  have hkey : ∀ ε > 0, ‖∫ u, φ (Real.exp (-u)) * D u ∂μ‖ ≤ ε * ∫ u, ‖D u‖ ∂μ := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 φ hφ ε hε
    have hbump : ∀ u : ℝ, 0 < u → ‖φ (Real.exp (-u)) - p.eval (Real.exp (-u))‖ ≤ ε := by
      intro u hu
      have hmem : Real.exp (-u) ∈ Icc (0:ℝ) 1 :=
        ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
      have h := hp _ hmem
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact le_of_lt h
    have hdiff_meas : AEStronglyMeasurable
        (fun u : ℝ => φ (Real.exp (-u)) - p.eval (Real.exp (-u))) μ :=
      hφmeas.sub (by fun_prop : Measurable fun u : ℝ => p.eval (Real.exp (-u))).aestronglyMeasurable
    have hdiff_int : Integrable
        (fun u : ℝ => (φ (Real.exp (-u)) - p.eval (Real.exp (-u))) * D u) μ := by
      refine integrableOn_mul_of_norm_bound hD hdiff_meas hε.le ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hbump u hu
    have hp_int : Integrable (fun u : ℝ => p.eval (Real.exp (-u)) * D u) μ := by
      refine integrableOn_mul_of_norm_bound (C := ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖)
        hD ?_ (by positivity) ?_
      · exact (by fun_prop : Measurable fun u : ℝ => p.eval (Real.exp (-u))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu' : (0:ℝ) < u := hu
        rw [Polynomial.eval_eq_sum_range]
        calc ‖∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * Real.exp (-u) ^ k‖
            ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k * Real.exp (-u) ^ k‖ :=
              norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ := by
              refine Finset.sum_le_sum (fun k _ => ?_)
              rw [norm_mul, norm_pow]
              have h1 : ‖Real.exp (-u)‖ ≤ 1 := by
                rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                exact Real.exp_le_one_iff.mpr (by linarith)
              calc ‖p.coeff k‖ * ‖Real.exp (-u)‖ ^ k ≤ ‖p.coeff k‖ * 1 := by
                    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                    exact pow_le_one₀ (norm_nonneg _) h1
                _ = ‖p.coeff k‖ := mul_one _
    have hsplit : ∫ u, φ (Real.exp (-u)) * D u ∂μ
        = ∫ u, (φ (Real.exp (-u)) - p.eval (Real.exp (-u))) * D u ∂μ
          + ∫ u, p.eval (Real.exp (-u)) * D u ∂μ := by
      rw [← integral_add hdiff_int hp_int]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      simp only [Pi.add_apply]
      ring
    rw [hsplit, integral_eval_exp_mul_eq_zero hD hlaplace p, add_zero]
    calc ‖∫ u, (φ (Real.exp (-u)) - p.eval (Real.exp (-u))) * D u ∂μ‖
        ≤ ∫ u, ‖(φ (Real.exp (-u)) - p.eval (Real.exp (-u))) * D u‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u, ε * ‖D u‖ ∂μ := by
          refine integral_mono_ae hdiff_int.norm (hDμ.norm.const_mul ε) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          have hb := hbump u hu
          rw [Real.norm_eq_abs] at hb
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = ε * ∫ u, ‖D u‖ ∂μ := integral_const_mul _ _
  -- conclude that the integral vanishes
  have hfin : (0:ℝ) ≤ ∫ u, ‖D u‖ ∂μ := integral_nonneg (fun u => norm_nonneg _)
  have habs : |∫ u, φ (Real.exp (-u)) * D u ∂μ| ≤ 0 := by
    rcases eq_or_lt_of_le hfin with hM | hM
    · have h1 := hkey 1 one_pos
      rw [← hM, mul_zero] at h1
      rwa [← Real.norm_eq_abs]
    · by_contra hcon
      have hpos : 0 < |∫ u, φ (Real.exp (-u)) * D u ∂μ| := not_le.mp hcon
      have h1 := hkey (|∫ u, φ (Real.exp (-u)) * D u ∂μ| / (2 * (∫ u, ‖D u‖ ∂μ))) (by positivity)
      rw [Real.norm_eq_abs] at h1
      have h2 : |∫ u, φ (Real.exp (-u)) * D u ∂μ| / (2 * (∫ u, ‖D u‖ ∂μ))
          * (∫ u, ‖D u‖ ∂μ) = |∫ u, φ (Real.exp (-u)) * D u ∂μ| / 2 := by
        field_simp
      linarith [h1, h2]
  exact abs_nonpos_iff.mp habs

/-! ### Step 4: indicators of intervals -/

/-- The trapezoid weight on `ℝ` that converges to the indicator of `(c,d)` as `n → ∞`. -/
noncomputable def trapezoid (n : ℕ) (c d s : ℝ) : ℝ :=
  max 0 (min 1 ((n:ℝ) * (s - c))) * max 0 (min 1 ((n:ℝ) * (d - s)))

theorem continuous_trapezoid (n : ℕ) (c d : ℝ) : Continuous (trapezoid n c d) := by
  unfold trapezoid
  fun_prop

theorem abs_trapezoid_le_one (n : ℕ) (c d s : ℝ) : |trapezoid n c d s| ≤ 1 := by
  have h1 : (0:ℝ) ≤ max 0 (min 1 ((n:ℝ) * (s - c))) := le_max_left _ _
  have h2 : max 0 (min 1 ((n:ℝ) * (s - c))) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have h3 : (0:ℝ) ≤ max 0 (min 1 ((n:ℝ) * (d - s))) := le_max_left _ _
  have h4 : max 0 (min 1 ((n:ℝ) * (d - s))) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hnn : 0 ≤ trapezoid n c d s := mul_nonneg h1 h3
  rw [abs_of_nonneg hnn]
  calc max 0 (min 1 ((n:ℝ) * (s - c))) * max 0 (min 1 ((n:ℝ) * (d - s)))
      ≤ 1 * 1 := mul_le_mul h2 h4 h3 (by norm_num)
    _ = 1 := by norm_num

theorem trapezoid_eq_zero_of_le {n : ℕ} {c d s : ℝ} (hcd : c < d) (hs : s ≤ c) :
    trapezoid n c d s = 0 := by
  unfold trapezoid
  have h1 : (n:ℝ) * (s - c) ≤ 0 := by
    have hsc : (s - c) ≤ 0 := by linarith
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith
  have h2 : (n:ℝ) * (s - c) ≤ 1 := by linarith
  rw [min_eq_right h2, max_eq_left h1, zero_mul]

theorem trapezoid_eq_zero_of_ge {n : ℕ} {c d s : ℝ} (hcd : c < d) (hs : d ≤ s) :
    trapezoid n c d s = 0 := by
  unfold trapezoid
  have h1 : (n:ℝ) * (d - s) ≤ 0 := by
    have hds : (d - s) ≤ 0 := by linarith
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith
  have h2 : (n:ℝ) * (d - s) ≤ 1 := by linarith
  rw [min_eq_right h2, max_eq_left h1, mul_zero]

theorem tendsto_trapezoid {c d s : ℝ} (hs : s ∈ Ioo c d) :
    Tendsto (fun n : ℕ => trapezoid n c d s) atTop (𝓝 1) := by
  obtain ⟨h1, h2⟩ := hs
  have hpos1 : 0 < s - c := by linarith
  have hpos2 : 0 < d - s := by linarith
  have hA : ∀ᶠ n : ℕ in atTop, 1 ≤ (n:ℝ) * (s - c) :=
    ((tendsto_natCast_atTop_atTop.atTop_mul_const hpos1).eventually
      (eventually_ge_atTop 1))
  have hB : ∀ᶠ n : ℕ in atTop, 1 ≤ (n:ℝ) * (d - s) :=
    ((tendsto_natCast_atTop_atTop.atTop_mul_const hpos2).eventually
      (eventually_ge_atTop 1))
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hA, hB] with n hn1 hn2
  unfold trapezoid
  rw [min_eq_left hn1, max_eq_right (by norm_num : (0:ℝ) ≤ 1),
    min_eq_left hn2, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  norm_num

/-- For `D` integrable on `(0,∞)` with vanishing Laplace transform, all interval integrals
vanish. -/
theorem integral_Ioo_eq_zero {D : ℝ → ℝ} (hD : IntegrableOn D (Ioi (0:ℝ)))
    (hlaplace : ∀ σ : ℝ, 0 < σ → ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * D u = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ u in Ioo a b, D u = 0 := by
  classical
  set μ := volume.restrict (Ioi (0:ℝ)) with hμ
  have hsub : Ioo a b ⊆ Ioi (0:ℝ) := fun u hu => by
    rw [mem_Ioo] at hu
    exact lt_of_le_of_lt ha hu.1
  have hcd : Real.exp (-b) < Real.exp (-a) := Real.exp_lt_exp.mpr (by linarith)
  -- the approximating integrands
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun u : ℝ => trapezoid n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u)) * D u) μ := by
    filter_upwards with n
    exact ((continuous_trapezoid n _ _).comp
      (Real.continuous_exp.comp continuous_id.neg)).aestronglyMeasurable.mul hD.aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ u ∂μ,
      ‖trapezoid n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u)) * D u‖ ≤ ‖D u‖ := by
    filter_upwards with n
    filter_upwards with u
    have h := abs_trapezoid_le_one n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    calc |trapezoid n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u))| * |D u|
        ≤ 1 * |D u| := mul_le_mul_of_nonneg_right h (abs_nonneg _)
      _ = |D u| := one_mul _
  have hlim : ∀ᵐ u ∂μ, Tendsto
      (fun n : ℕ => trapezoid n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u)) * D u)
      atTop (𝓝 ((Ioo a b).indicator D u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : (0:ℝ) < u := hu
    have hexp : Real.exp (-u) ∈ Ioo (Real.exp (-b)) (Real.exp (-a)) ↔ u ∈ Ioo a b := by
      rw [mem_Ioo, mem_Ioo, Real.exp_lt_exp, Real.exp_lt_exp]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    by_cases hin : u ∈ Ioo a b
    · have hs := hexp.mpr hin
      have h1 : Tendsto (fun n : ℕ => trapezoid n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u))
          * D u) atTop (𝓝 (D u)) := by
        have h := (tendsto_trapezoid hs).mul_const (D u)
        simpa using h
      rwa [Set.indicator_of_mem hin]
    · have hcases : u ≤ a ∨ b ≤ u := by
        rcases le_or_gt u a with h | h
        · exact Or.inl h
        · rcases le_or_gt b u with h2 | h2
          · exact Or.inr h2
          · exact absurd ⟨h, h2⟩ hin
      have hz : ∀ n : ℕ, trapezoid n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u)) = 0 := by
        intro n
        rcases hcases with hle | hge
        · exact trapezoid_eq_zero_of_ge hcd (by rw [Real.exp_le_exp]; linarith)
        · exact trapezoid_eq_zero_of_le hcd (by rw [Real.exp_le_exp]; linarith)
      have h1 : Tendsto (fun n : ℕ => trapezoid n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u))
          * D u) atTop (𝓝 0) := by
        simp only [hz, zero_mul]
        exact tendsto_const_nhds
      rwa [Set.indicator_of_notMem hin]
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (F := fun n : ℕ => fun u : ℝ =>
      trapezoid n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u)) * D u)
    (f := (Ioo a b).indicator D) (bound := fun u => ‖D u‖) hmeas hbound hD.norm hlim
  have hzero : ∀ n : ℕ, ∫ u, trapezoid n (Real.exp (-b)) (Real.exp (-a)) (Real.exp (-u))
      * D u ∂μ = 0 := by
    intro n
    exact integral_comp_exp_mul_eq_zero hD hlaplace
      ((continuous_trapezoid n _ _).continuousOn)
  have h2 : Tendsto (fun n : ℕ => ∫ u, trapezoid n (Real.exp (-b)) (Real.exp (-a))
      (Real.exp (-u)) * D u ∂μ) atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  have key : ∫ u, (Ioo a b).indicator D u ∂μ = 0 := tendsto_nhds_unique hDCT h2
  rw [integral_indicator measurableSet_Ioo] at key
  rw [Measure.restrict_restrict_of_subset hsub] at key
  exact key

/-! ### Step 5: from interval integrals to the a.e. statement -/

theorem eq_zero_ae_of_forall_laplace_eq_zero {D : ℝ → ℝ}
    (hD : IntegrableOn D (Ioi (0:ℝ)))
    (hlaplace : ∀ σ : ℝ, 0 < σ → ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * D u = 0) :
    D =ᵐ[volume.restrict (Ioi (0:ℝ))] 0 := by
  classical
  set Dt : ℝ → ℝ := (Ioi (0:ℝ)).indicator D with hDt
  -- the extended function `Dt` has vanishing integrals over all open intervals
  have hIoo : ∀ a b : ℝ, a < b → ∫ u in Ioo a b, Dt u = 0 := by
    intro a b hab
    have hfun : (fun u => (Ioo a b).indicator Dt u) = (fun u => (Ioo (max a 0) b).indicator Dt u) := by
      funext u
      by_cases hu : u ∈ Ioo (max a 0) b
      · have hu' : u ∈ Ioo a b := ⟨by linarith [le_max_left a (0:ℝ), hu.1], hu.2⟩
        rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu']
      · rw [Set.indicator_of_notMem hu]
        by_cases hu' : u ∈ Ioo a b
        · rw [Set.indicator_of_mem hu']
          rw [mem_Ioo] at hu'
          have hle : u ≤ max a 0 := by
            by_contra hcon
            push Not at hcon
            exact hu ⟨hcon, hu'.2⟩
          have ha0 : a ≤ 0 := by
            by_contra hcon
            push Not at hcon
            rw [max_eq_left hcon.le] at hle
            linarith [hu'.1]
          have hmax : max a 0 = 0 := max_eq_right ha0
          rw [hmax] at hle
          exact Set.indicator_of_notMem (by simp only [mem_Ioi]; linarith) D
        · rw [Set.indicator_of_notMem hu']
    rw [← integral_indicator measurableSet_Ioo, hfun, integral_indicator measurableSet_Ioo]
    rcases le_or_gt b 0 with hb | hb
    · have hz : ∀ u ∈ Ioo (max a 0) b, Dt u = 0 := by
        intro u hu
        rw [mem_Ioo] at hu
        exact Set.indicator_of_notMem (by simp only [mem_Ioi]; linarith [hu.2]) D
      -- placeholder
      rw [show (∫ u in Ioo (max a 0) b, Dt u) = ∫ _u in Ioo (max a 0) b, (0:ℝ) from
        setIntegral_congr_fun measurableSet_Ioo hz]
      simp
    · have hlt : max a 0 < b := max_lt hab hb
      rw [show (∫ u in Ioo (max a 0) b, Dt u) = ∫ u in Ioo (max a 0) b, D u from
        setIntegral_congr_fun measurableSet_Ioo (fun u hu => by
          rw [mem_Ioo] at hu
          exact Set.indicator_of_mem (by
            simp only [mem_Ioi]; linarith [hu.1, le_max_right a (0:ℝ)]) D)]
      exact integral_Ioo_eq_zero hD hlaplace (le_max_right a 0) hlt
  have hInt_le : ∀ x y : ℝ, x ≤ y → ∫ t in x..y, Dt t = 0 := by
    intro x y hxy
    rw [intervalIntegral.integral_of_le hxy, integral_Ioc_eq_integral_Ioo]
    rcases eq_or_lt_of_le hxy with h | h
    · rw [← h]; simp
    · exact hIoo x y h
  have hInt : ∀ x y : ℝ, ∫ t in x..y, Dt t = 0 := by
    intro x y
    rcases le_or_gt x y with h | h
    · exact hInt_le x y h
    · rw [intervalIntegral.integral_symm]
      exact neg_eq_zero.mpr (hInt_le y x h.le)
  -- local integrability of `Dt`
  have hloc : LocallyIntegrable Dt volume := by
    intro x
    refine ⟨Ioo (x-1) (x+1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    rw [hDt, integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet]
    exact hD.mono_set Set.inter_subset_left
  -- Lebesgue differentiation
  have hae := LocallyIntegrable.ae_hasDerivAt_integral hloc
  have hfinal : Dt =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    have hconst : (fun y => ∫ t in x..y, Dt t) = fun _ => 0 := funext (hInt x)
    have h0 : HasDerivAt (fun y => ∫ t in x..y, Dt t) 0 x := by
      rw [hconst]
      exact hasDerivAt_const x 0
    have h1 := (hx x).unique h0
    simpa using h1
  have hfinal' : Dt =ᵐ[volume.restrict (Ioi (0:ℝ))] 0 := ae_mono Measure.restrict_le_self hfinal
  filter_upwards [hfinal', ae_restrict_mem measurableSet_Ioi] with u hu huIoi
  have h1 : Dt u = D u := Set.indicator_of_mem huIoi D
  rw [← h1]
  exact hu

end PercLib.CriticalLRP.Analysis
