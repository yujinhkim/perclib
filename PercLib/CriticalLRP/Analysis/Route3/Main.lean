/- Integrated from independently rebuilt Ultramath work.
Production base 37c0efc68ae8ef365d8d155bc931fd784fdfde2b.
Scratch source: ../../.ultramath/smwvnrt0i/m2/Main.lean.
-/

module

public import PercLib.CriticalLRP.Analysis.Route3.Defs
public import PercLib.CriticalLRP.Analysis.Route3.Sums
public import PercLib.CriticalLRP.Tightness.DiscreteLayerCake

/-!
# Proofs: termwise bounds, the split partial sum, and the optimization

The only production object used is `PercLib.CriticalLRP.Tightness.lintegral_eq_tsum_meas_ge`
(the discrete layer cake for integer-valued `ℝ≥0∞`-valued random variables); everything else
is proved here from `Defs`/`Sums`.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Analysis.Route3

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ≥0∞}

/-! ### §1 Termwise bounds -/

/-- `(j+1)^2` as an extended nonnegative real, in the `ofReal` shape used by Markov. -/
theorem ennreal_add_one_sq (j : ℕ) :
    ((j : ℝ≥0∞) + 1) ^ 2 = ENNReal.ofReal (((j : ℝ) + 1) ^ 2) := by
  have h1 : ((j : ℝ≥0∞) + 1) = ENNReal.ofReal ((j : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast]
    norm_num
  rw [h1, ENNReal.ofReal_pow (by positivity)]

/-- The inverse of the same quantity, in the `ofReal` shape used by the telescoping sum. -/
theorem ennreal_add_one_sq_inv (j : ℕ) :
    (((j : ℝ≥0∞) + 1) ^ 2)⁻¹ = ENNReal.ofReal ((((j : ℝ) + 1) ^ 2)⁻¹) := by
  rw [ennreal_add_one_sq, ENNReal.ofReal_inv_of_pos (by positivity)]

/-- **The head bound.**  Where the `n^{-1/2}` envelope applies, the terminal probability at
scale `j+1` is at most `C / √(j+1)`; summing over `j+1 ≤ N` and using
`sum_range_inv_sqrt_le` gives `⪯ 2C √N`. -/
theorem sum_filter_head_le {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hTail : ∀ n : ℕ, 1 ≤ n → μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ tailEnvelope C n) (M : ℕ) :
    ∑ j ∈ (Finset.range M).filter (fun j => j + 1 ≤ N), μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}
      ≤ ENNReal.ofReal (2 * C * Real.sqrt N) := by
  have hterm : ∀ j ∈ (Finset.range M).filter (fun j => j + 1 ≤ N),
      μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} ≤ ENNReal.ofReal (C / Real.sqrt ((j : ℝ) + 1)) := by
    intro j hj
    have h1 : 1 ≤ j + 1 := Nat.le_add_left 1 j
    have := hTail (j + 1) h1
    simpa [tailEnvelope, Nat.cast_add, Nat.cast_one] using this
  have hfil : (Finset.range M).filter (fun j => j + 1 ≤ N) = Finset.range (min N M) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), hfil]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsplit : ∑ j ∈ Finset.range (min N M), C / Real.sqrt ((j : ℝ) + 1)
      = C * ∑ j ∈ Finset.range (min N M), (Real.sqrt ((j : ℝ) + 1))⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
  rw [hsplit]
  have hmono : ∑ j ∈ Finset.range (min N M), (Real.sqrt ((j : ℝ) + 1))⁻¹
      ≤ ∑ j ∈ Finset.range N, (Real.sqrt ((j : ℝ) + 1))⁻¹ :=
    sum_range_inv_sqrt_mono (min_le_left N M)
  have hhead : ∑ j ∈ Finset.range (min N M), (Real.sqrt ((j : ℝ) + 1))⁻¹
      ≤ 2 * Real.sqrt (N : ℝ) := le_trans hmono (sum_range_inv_sqrt_le N)
  calc C * ∑ j ∈ Finset.range (min N M), (Real.sqrt ((j : ℝ) + 1))⁻¹
      ≤ C * (2 * Real.sqrt (N : ℝ)) := mul_le_mul_of_nonneg_left hhead hC
    _ = 2 * C * Real.sqrt (N : ℝ) := by ring

/-- **Markov at scale `j+1`.**  `μ{X ≥ j+1} ≤ m_2/(j+1)^2`, from `X ≥ j+1 ⇒ X^2 ≥ (j+1)^2`. -/
theorem meas_add_one_le_lintegral_sq_div (hX : Measurable X) (j : ℕ) :
    μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}
      ≤ (∫⁻ ω, X ω ^ 2 ∂μ) / ((j : ℝ≥0∞) + 1) ^ 2 := by
  have hsub : {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} ⊆ {ω | ((j : ℝ≥0∞) + 1) ^ 2 ≤ X ω ^ 2} :=
    fun ω hω => show ((j : ℝ≥0∞) + 1) ^ 2 ≤ X ω ^ 2 from pow_le_pow_left' hω 2
  refine le_trans (measure_mono hsub) ?_
  refine meas_ge_le_lintegral_div (f := fun ω => X ω ^ 2) ((hX.pow_const 2).aemeasurable)
    (by simp) (by simp)

/-- **The tail bound.**  Beyond the truncation scale, Markov plus the telescoping bound
`sum_Ico_inv_sq_le` give `∑_{N ≤ j < M} μ{X ≥ j+1} ≤ m_2 / N`. -/
theorem sum_filter_tail_le (hX : Measurable X) {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ j ∈ (Finset.range M).filter (fun j => ¬ (j + 1 ≤ N)), μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}
      ≤ (∫⁻ ω, X ω ^ 2 ∂μ) / (N : ℝ≥0∞) := by
  have hterm : ∀ j ∈ (Finset.range M).filter (fun j => ¬ (j + 1 ≤ N)),
      μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}
        ≤ (∫⁻ ω, X ω ^ 2 ∂μ) / ((j : ℝ≥0∞) + 1) ^ 2 :=
    fun j _ => meas_add_one_le_lintegral_sq_div hX j
  have hIco : (Finset.range M).filter (fun j => ¬ (j + 1 ≤ N)) = Finset.Ico N M := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hsum : ∑ j ∈ (Finset.range M).filter (fun j => ¬ (j + 1 ≤ N)),
        (((j : ℝ≥0∞) + 1) ^ 2)⁻¹ ≤ (N : ℝ≥0∞)⁻¹ := by
    have hcongr : ∑ j ∈ (Finset.range M).filter (fun j => ¬ (j + 1 ≤ N)),
          (((j : ℝ≥0∞) + 1) ^ 2)⁻¹
        = ∑ j ∈ Finset.Ico N M, ENNReal.ofReal ((((j : ℝ) + 1) ^ 2)⁻¹) := by
      rw [hIco]
      exact Finset.sum_congr rfl fun j _ => ennreal_add_one_sq_inv j
    have hNinv : ((N : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((N : ℝ)⁻¹) := by
      rw [← ENNReal.ofReal_natCast N,
        ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < N by exact_mod_cast hN)]
    rw [hcongr, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), hNinv]
    exact ENNReal.ofReal_le_ofReal (sum_Ico_inv_sq_le N M hN)
  calc ∑ j ∈ (Finset.range M).filter (fun j => ¬ (j + 1 ≤ N)),
        μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}
      ≤ ∑ j ∈ (Finset.range M).filter (fun j => ¬ (j + 1 ≤ N)),
          (∫⁻ ω, X ω ^ 2 ∂μ) / ((j : ℝ≥0∞) + 1) ^ 2 := Finset.sum_le_sum hterm
    _ = (∫⁻ ω, X ω ^ 2 ∂μ)
          * ∑ j ∈ (Finset.range M).filter (fun j => ¬ (j + 1 ≤ N)),
              (((j : ℝ≥0∞) + 1) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [ENNReal.div_eq_inv_mul, mul_comm]
    _ ≤ (∫⁻ ω, X ω ^ 2 ∂μ) * (N : ℝ≥0∞)⁻¹ := by gcongr
    _ = (∫⁻ ω, X ω ^ 2 ∂μ) / (N : ℝ≥0∞) := by
        rw [ENNReal.div_eq_inv_mul, mul_comm]

/-! ### §2 The split partial sum -/

/-- **The truncated layer cake.**  For every `M`, the first `M` terms of the layer cake are
at most `2C √N + m_2/N`.  This is the source's displayed estimate, in partial-sum form. -/
theorem partialSum_le {C : ℝ} (hC : 0 ≤ C) (hX : Measurable X) {N : ℕ} (hN : 1 ≤ N)
    (hTail : ∀ n : ℕ, 1 ≤ n → μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ tailEnvelope C n) (M : ℕ) :
    ∑ j ∈ Finset.range M, μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}
      ≤ ENNReal.ofReal (2 * C * Real.sqrt N) + (∫⁻ ω, X ω ^ 2 ∂μ) / (N : ℝ≥0∞) := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range M)
    (p := fun j => j + 1 ≤ N) (f := fun j => μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω})]
  exact add_le_add (sum_filter_head_le hC hTail M) (sum_filter_tail_le hX hN M)

/-! ### §3 The optimization -/

/-- The real-variable core of the optimization: with `t = m^{1/3}` and `N = ⌈t^2⌉`,
`2C √N + m/N ≤ (4C+1) t`. -/
theorem opt_arith {C m t : ℝ} (hC : 0 ≤ C) (hm : 1 ≤ m) (ht : t = m ^ ((1 : ℝ) / 3))
    (hNge : t * t ≤ (cutoffScale m : ℝ)) (hNlt : (cutoffScale m : ℝ) < t * t + 1) :
    2 * C * Real.sqrt (cutoffScale m) + m / (cutoffScale m) ≤ (4 * C + 1) * t := by
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : 1 ≤ t := by rw [ht]; exact Real.one_le_rpow hm (by norm_num)
  have hcube : t ^ 3 = m := by rw [ht]; exact rpow_third_cube (by linarith)
  have hNpos : (0 : ℝ) < (cutoffScale m : ℝ) := lt_of_lt_of_le (by nlinarith) hNge
  -- `√N ≤ t + 1`
  have hsq : (cutoffScale m : ℝ) ≤ (t + 1) ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (cutoffScale m) ≤ t + 1 := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by linarith)] at this
  -- `m/N ≤ t`
  have hdiv : m / (cutoffScale m : ℝ) ≤ t := by
    rw [div_le_iff₀ hNpos]
    nlinarith [hNge, ht0]
  -- assemble
  have h1 : 2 * C * Real.sqrt (cutoffScale m) ≤ 2 * C * (t + 1) := by
    exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have h2 : 2 * C * (t + 1) ≤ 4 * C * t := by nlinarith
  linarith

/-- **Route 3 of Proposition I.4.15: the second moment dominates the cube of the first.**

For any probability measure, any measurable integer-valued `X ≥ 1` and any `n^{-1/2}`
upper tail envelope `C/√n`, the first and second moments satisfy
`(∫⁻ X)^3 ≤ (4C+1)^3 · ∫⁻ X^2`.  Both sides are extended nonnegative reals, so no
finiteness is required: if the second moment is infinite the inequality is trivial. -/
theorem cube_lintegral_le_of_tail [IsProbabilityMeasure μ] (hX : Measurable X)
    (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞)) (hX1 : ∀ ω, 1 ≤ X ω) {C : ℝ}
    (hC : 0 ≤ C)
    (hTail : ∀ n : ℕ, 1 ≤ n → μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ tailEnvelope C n) :
    (∫⁻ ω, X ω ∂μ) ^ 3 ≤ ENNReal.ofReal (ratioConst C) * ∫⁻ ω, X ω ^ 2 ∂μ := by
  classical
  set m2 : ℝ≥0∞ := ∫⁻ ω, X ω ^ 2 ∂μ with hm2def
  rcases eq_or_ne m2 ⊤ with hm2top | hm2ne
  · rw [hm2top, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.2 (ratioConst_pos hC))]
    exact le_top
  -- the second moment is finite; `m = m2.toReal`
  set m : ℝ := m2.toReal with hmdef
  have hm2of : m2 = ENNReal.ofReal m := (ENNReal.ofReal_toReal hm2ne).symm
  have hmge : 1 ≤ m := by
    have h1 : (1 : ℝ≥0∞) ≤ m2 := by
      calc (1 : ℝ≥0∞) = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := by
            rw [lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ ω, X ω ^ 2 ∂μ :=
            lintegral_mono fun ω => by simpa using pow_le_pow_left' (hX1 ω) 2
    have := ENNReal.toReal_mono hm2ne h1
    simpa [hmdef] using this
  -- the truncation scale
  set t : ℝ := m ^ ((1 : ℝ) / 3) with htdef
  set N : ℕ := cutoffScale m with hNdef
  have hN1 : 1 ≤ N := one_le_cutoffScale hmge
  have hNne : (N : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hNtop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  -- the partial-sum bound, then the supremum
  have hbound : ∫⁻ ω, X ω ∂μ
      ≤ ENNReal.ofReal (2 * C * Real.sqrt N) + m2 / (N : ℝ≥0∞) := by
    rw [PercLib.CriticalLRP.Tightness.lintegral_eq_tsum_meas_ge hX hint,
      ENNReal.tsum_eq_iSup_nat]
    exact iSup_le fun M => partialSum_le hC hX hN1 hTail M
  have hfin1 : ENNReal.ofReal (2 * C * Real.sqrt N) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfin2 : m2 / (N : ℝ≥0∞) ≠ ⊤ := by
    rw [hm2of, ENNReal.div_eq_inv_mul]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hNne) ENNReal.ofReal_ne_top
  have hfinT : ENNReal.ofReal (2 * C * Real.sqrt N) + m2 / (N : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩
  have hm1fin : ∫⁻ ω, X ω ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top hfinT hbound
  -- pass to reals
  have hreal : (∫⁻ ω, X ω ∂μ).toReal ≤ 2 * C * Real.sqrt N + m / N := by
    have h := ENNReal.toReal_mono hfinT hbound
    have hsplit : (ENNReal.ofReal (2 * C * Real.sqrt N) + m2 / (N : ℝ≥0∞)).toReal
        = 2 * C * Real.sqrt N + m / N := by
      rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_div, ← hmdef, ENNReal.toReal_natCast]
    linarith [h, hsplit.symm ▸ h]
  -- the arithmetic optimization
  have harith : 2 * C * Real.sqrt N + m / N ≤ (4 * C + 1) * t := by
    exact opt_arith hC hmge htdef (cutoffScale_ge (by linarith)) (cutoffScale_lt (by linarith))
  have hcube : t ^ 3 = m := by rw [htdef]; exact rpow_third_cube (by linarith)
  have hle : (∫⁻ ω, X ω ∂μ).toReal ≤ (4 * C + 1) * t := le_trans hreal harith
  have hpow : ((∫⁻ ω, X ω ∂μ).toReal) ^ 3 ≤ (((4 * C + 1) * t) ^ 3) :=
    pow_le_pow_left₀ (by positivity) hle 3
  have hm1eq : (∫⁻ ω, X ω ∂μ) = ENNReal.ofReal ((∫⁻ ω, X ω ∂μ).toReal) :=
    (ENNReal.ofReal_toReal hm1fin).symm
  calc (∫⁻ ω, X ω ∂μ) ^ 3
      = (ENNReal.ofReal ((∫⁻ ω, X ω ∂μ).toReal)) ^ 3 := by conv_lhs => rw [hm1eq]
    _ = ENNReal.ofReal (((∫⁻ ω, X ω ∂μ).toReal) ^ 3) := by
        rw [← ENNReal.ofReal_pow (by positivity)]
    _ ≤ ENNReal.ofReal (((4 * C + 1) * t) ^ 3) := ENNReal.ofReal_le_ofReal hpow
    _ = ENNReal.ofReal (ratioConst C) * m2 := by
        rw [hm2of, ratioConst, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_pow, hcube]

end PercLib.CriticalLRP.Analysis.Route3
