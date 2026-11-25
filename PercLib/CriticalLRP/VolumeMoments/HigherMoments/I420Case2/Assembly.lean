/- Integrated from independently rebuilt Ultramath work.
Production base e6fb888fa60f4bb3d7fa5ab717b2d149345e3a7f.
Scratch source: repository-root .ultramath/smwwp7q3k/m1/.
-/

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Assembly of the Case 2 decorrelation error of Proposition I.4.20 in the cut-off model
`PercLib.CriticalLRP.Orchestration.SourceModelData`: from the two moment inputs
((I.4.19) at index `2p+2` and universal tightness `E_r[|K ∩ B_r|²] ⪯ M_r E_r|K|`), the first
moment order `A' r^α ≤ E_r|K| ≤ A r^α`, the two-point driver bound `M₂/M₁ ≤ γ M₁²`,
the ball growth
`|B_r| ≥ c r^d` and the `Hydro` hypothesis `M_r = o(r^{(d+α)/2})` at `d = 3α`, the joint moment
`E_r[|K|^{p+1}|K ∩ B_r|]` is `o(|B_r| (M₂/M₁)^{p-1} M₁²)`.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case2.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case2.Scalar

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology Asymptotics

namespace PercLib.CriticalLRP.Analysis.I420Case2

/-- A positive `ε` with `K √ε < η`. -/
theorem exists_eps_sqrt_mul_lt {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ K * Real.sqrt ε < η := by
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  refine ⟨min 1 ((η / (K + 1)) ^ 2), ?_, ?_⟩
  · have h : (0 : ℝ) < (η / (K + 1)) ^ 2 := by positivity
    exact lt_min one_pos h
  · have hle : Real.sqrt (min 1 ((η / (K + 1)) ^ 2)) ≤ η / (K + 1) := by
      refine le_trans (Real.sqrt_le_sqrt (min_le_right _ _)) (le_of_eq ?_)
      rw [Real.sqrt_sq (le_of_lt (by positivity : (0 : ℝ) < η / (K + 1)))]
    have := mul_le_mul_of_nonneg_left hle hK
    have h2 : K * (η / (K + 1)) < η := by
      rw [mul_div_assoc', div_lt_iff₀ hK1]
      nlinarith
    linarith

/-- `Hydro` in the form used in Case 2: `M_r ≤ ε r^{(d+α)/2}` eventually, for every `ε > 0`. -/
theorem Mr_eventually_le (M : Orchestration.SourceModelData) (hH : Orchestration.Hydro M)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, (M.Mr r : ℝ) ≤ ε * r ^ (((M.d : ℝ) + M.α) / 2) := by
  have h : ∀ᶠ r : ℝ in atTop, dist ((M.Mr r : ℝ) / r ^ (((M.d : ℝ) + M.α) / 2)) 0 < ε :=
    (Metric.tendsto_nhds.mp hH) ε hε
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hr
  rw [div_lt_iff₀ (Real.rpow_pos_of_pos hr0 _)] at hr
  exact le_of_lt hr

/-- The ball grows at least like `c r^d`, from `M.ball_count` (Lemma I.4.6). -/
theorem ballCard_eventually_ge (M : Orchestration.SourceModelData) {c : ℝ} (hc1 : c < 1) :
    ∀ᶠ r : ℝ in atTop, c * r ^ M.d ≤ ballCard M r := by
  have hne : ∀ᶠ r : ℝ in atTop, (fun r : ℝ => r ^ M.d) r ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact ne_of_gt (by positivity)
  have ht : Tendsto (fun r : ℝ => ballCard M r / r ^ M.d) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hne).mp M.ball_count
  have hlt : ∀ᶠ r : ℝ in atTop, c < ballCard M r / r ^ M.d := (tendsto_order.mp ht).1 c hc1
  filter_upwards [hlt, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  have hpos : (0 : ℝ) < r ^ M.d := by positivity
  rw [lt_div_iff₀ hpos] at hr
  exact le_of_lt hr

/-- `f = o(g)` for nonnegative functions, in eventual-`η` form. -/
theorem isLittleO_iff_eventually_le {f g : ℝ → ℝ} (hf : ∀ᶠ r : ℝ in atTop, 0 ≤ f r)
    (hg : ∀ᶠ r : ℝ in atTop, 0 ≤ g r) :
    f =o[atTop] g ↔ ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop, f r ≤ η * g r := by
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro h η hη
    filter_upwards [h hη, hf, hg] with r hr hfr hgr
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgr, abs_of_nonneg hfr] at hr
  · intro h η hη
    filter_upwards [h η hη, hf, hg] with r hr hfr hgr
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgr, abs_of_nonneg hfr]

/-- **Decorrelation error of Proposition I.4.20, Case 2 (`d = 3α`).**
The joint moment `E_r[|K|^{p+1}|K ∩ B_r|]`, which dominates the error in (I.4.20), is
`o(|B_r| (M₂/M₁)^{p-1} M₁²)` in the cut-off model, given
* the moment upper bound (I.4.19) at index `2p+2` (hypothesis `hI419`),
* universal tightness `E_r[|K ∩ B_r|²] ≤ M_r E_r|K|` (hypothesis `hTight`),
* the two-point bound `M₂/M₁ ≤ γ M₁²` (hypothesis `hdrive`),
* the first-moment order `A' r^α ≤ M₁ ≤ A r^α` (`hm₁lo`, `hm₁hi`),
* the ball growth `|B_r| ≥ c r^d` (`hball`),
* the hypothesis `Hydro` of Theorem I.1.6, i.e. `M_r = o(r^{(d+α)/2})`. -/
theorem case2_decorrelation_error (M : Orchestration.SourceModelData) (p : ℕ) (hp : 1 ≤ p)
    (m₁ m₂ : ℝ → ℝ) (C γ A A' c : ℝ)
    (_hα : 0 < M.α) (hd : (M.d : ℝ) = 3 * M.α) (hH : Orchestration.Hydro M)
    (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hA : 0 < A) (hA' : 0 < A') (hc : 0 < c)
    (hI419 : ∀ᶠ r : ℝ in atTop, M.cutMoment (2 * p + 2) r
      ≤ ENNReal.ofReal (C * (m₂ r / m₁ r) ^ (2 * p + 1) * m₁ r))
    (hTight : ∀ᶠ r : ℝ in atTop, interSecond M r
      ≤ ENNReal.ofReal ((M.Mr r : ℝ) * m₁ r))
    (hdrive : ∀ᶠ r : ℝ in atTop, m₂ r / m₁ r ≤ γ * m₁ r ^ 2)
    (hdrive0 : ∀ᶠ r : ℝ in atTop, 0 ≤ m₂ r / m₁ r)
    (hm₁hi : ∀ᶠ r : ℝ in atTop, m₁ r ≤ A * r ^ M.α)
    (hm₁lo : ∀ᶠ r : ℝ in atTop, A' * r ^ M.α ≤ m₁ r)
    (hm₁pos : ∀ᶠ r : ℝ in atTop, 0 < m₁ r)
    (hball : ∀ᶠ r : ℝ in atTop, c * r ^ (M.d : ℝ) ≤ ballCard M r) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop,
      jointMoment M p r ≤ ENNReal.ofReal (η * normTarget M p m₁ m₂ r) := by
  intro η hη
  obtain ⟨ε, hε0, hεK⟩ := exists_eps_sqrt_mul_lt
    (K := Real.sqrt (C * γ ^ 3) * A ^ 4 / (c * A' ^ 2)) (η := η) (by positivity) hη
  have hMrle := Mr_eventually_le M hH hε0
  filter_upwards [hI419, hTight, hdrive, hdrive0, hm₁hi, hm₁lo, hm₁pos, hball, hMrle,
    eventually_ge_atTop (1 : ℝ)] with r hI hT hd1 hd0 hhi hlo hpos hb hMr hr1
  have h3 : 3 * M.α ≤ (M.d : ℝ) := by rw [hd]
  have hC' : (0 : ℝ) ≤ C * (m₂ r / m₁ r) ^ (2 * p + 1) * m₁ r :=
    mul_nonneg (mul_nonneg hC (pow_nonneg hd0 (2 * p + 1))) (le_of_lt hpos)
  have hMr' : (0 : ℝ) ≤ (M.Mr r : ℝ) * m₁ r :=
    mul_nonneg (by positivity) (le_of_lt hpos)
  have hstep1 : jointMoment M p r ≤ ENNReal.ofReal (jointUpper M p C m₁ m₂ r) :=
    jointMoment_le_of_bounds M p r C m₁ m₂ hC' hMr' hI hT
  have hstep2 : jointUpper M p C m₁ m₂ r
      ≤ (Real.sqrt (C * γ ^ 3) * A ^ 4 / (c * A' ^ 2)) * Real.sqrt ε
          * normTarget M p m₁ m₂ r := by
    have := sqrt_bound_le (p := p) (α := M.α) (d := (M.d : ℝ)) (C := C) (γ := γ) (A := A)
      (A' := A') (c := c) (ε := ε) (b := ballCard M r) (s := m₂ r / m₁ r) (m := m₁ r)
      (Mr := (M.Mr r : ℝ)) (r := r) hp h3 hr1 hC hγ (le_of_lt hA) hA' hc (le_of_lt hε0)
      hd0 hpos (by positivity) hd1 hhi hlo (by simpa using hMr) (by simpa using hb)
    simpa only [jointUpper, i419Factor, tightFactor, normTarget] using this
  have hstep3 : (Real.sqrt (C * γ ^ 3) * A ^ 4 / (c * A' ^ 2)) * Real.sqrt ε
      * normTarget M p m₁ m₂ r ≤ η * normTarget M p m₁ m₂ r := by
    have hbc : (0 : ℝ) ≤ ballCard M r :=
      le_trans (le_of_lt (mul_pos hc (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < r) _))) hb
    have hN : (0 : ℝ) ≤ normTarget M p m₁ m₂ r := by
      rw [normTarget]
      exact mul_nonneg (mul_nonneg hbc (pow_nonneg hd0 (p - 1))) (by positivity)
    nlinarith [hεK, hN]
  calc jointMoment M p r ≤ ENNReal.ofReal (jointUpper M p C m₁ m₂ r) := hstep1
    _ ≤ ENNReal.ofReal (η * normTarget M p m₁ m₂ r) :=
        ENNReal.ofReal_le_ofReal (le_trans hstep2 hstep3)

end PercLib.CriticalLRP.Analysis.I420Case2
