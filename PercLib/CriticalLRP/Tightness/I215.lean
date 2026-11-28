/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Corollary I.2.15: the median of the largest cluster is `O(r^{(d+α)/2})`.
-/
module

public import PercLib.CriticalLRP.Analysis.Case3Hydro
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Corollary I.2.15: the median of the largest cluster is `O(r^{(d + α)/2})`

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1.
Theorem I.2.13 (p. 27) and Corollary I.2.15 (p. 28).

Theorem I.2.13, proved in [76] and cited by the paper, states the spatially
averaged critical two-point bound

`∑_{x ∈ B_r} P_{β_c}(0 ↔ x) ≼ r ^ α`   for every `r ≥ 1`.

The paper deduces from it (Corollary I.2.15) that the source median `M_r` of the
largest cluster inside the ball `B_r`, under the cut-off law `P_{β_c,r}`, satisfies

`M_r ≼ r ^ ((d + α) / 2)`   for every `r ≥ 1`.

The deduction has three ingredients, each of which is available in the library:

* the windowed median/averaging bound (`M5.mr_sq_le_inter`), i.e. the statement
  `(M_r - 1)^2 ≤ e |B_r| E_{β_c,r} |K ∩ B_{2r}|` obtained from the source's
  Lemma I.2.6 by averaging over the `|B_r|` possible centres of `B_r`;
* the comparison `E_{β_c,r} |K ∩ B_{2r}| ≤ ∑_{x ∈ B_{2r}} P_{β_c}(0 ↔ x)`,
  which is Tonelli plus cut-off domination of the uncut two-point function;
* the lattice count `|B_r| ≼ r ^ d` (Lemma I.4.6).

**Scope.** The cited Theorem I.2.13 is *not* proved here: its conclusion is the
explicit hypothesis `SpatialTwoPointAverage M` of the main theorem.  Nothing in
this file asserts that the hypothesis holds for the canonical model, and no
volume-tail bound or CitedInput is filled in.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

open PercLib.CriticalLRP PercLib.CriticalLRP.Orchestration

namespace M2I215

variable (M : SourceModelData)

/-- The conclusion of the cited Theorem I.2.13, in the paper's form: the critical
two-point function has spatial average `≼ r ^ α` over the ball of radius `r`. -/
def SpatialTwoPointAverage : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
    ∑ x ∈ (M.finite_ball r).toFinset, M.tau x ≤ C * r ^ M.α

/-- The lattice count `|B_r| ≼ r ^ d`, made uniform over all `r ≥ 1`. -/
theorem exists_ball_ncard_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ((M.ball r).ncard : ℝ) ≤ C * r ^ M.d := by
  obtain ⟨r₀, h₀⟩ := eventually_atTop.1 (M5.ball_ncard_eventually_le M)
  refine ⟨2 * max r₀ 1 ^ M.d, by positivity, ?_⟩
  intro r hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hrpow : (0 : ℝ) ≤ r ^ M.d := pow_nonneg hrpos.le _
  rcases le_or_gt (max r₀ 1) r with h | h
  · have h₁ : ((M.ball r).ncard : ℝ) ≤ 2 * r ^ M.d := h₀ r (le_trans (le_max_left _ _) h)
    have h₂ : (1 : ℝ) ≤ max r₀ 1 ^ M.d := one_le_pow₀ (le_max_right _ _)
    nlinarith
  · have hsub : M.ball r ⊆ M.ball (max r₀ 1) := fun y hy => le_trans hy h.le
    have hmono : (M.ball r).ncard ≤ (M.ball (max r₀ 1)).ncard :=
      Set.ncard_le_ncard hsub (M.finite_ball (max r₀ 1))
    have hM : ((M.ball (max r₀ 1)).ncard : ℝ) ≤ 2 * max r₀ 1 ^ M.d :=
      h₀ _ (le_max_left _ _)
    have hmonoR : ((M.ball r).ncard : ℝ) ≤ ((M.ball (max r₀ 1)).ncard : ℝ) := by
      exact_mod_cast hmono
    have hle : ((M.ball r).ncard : ℝ) ≤ 2 * max r₀ 1 ^ M.d := hmonoR.trans hM
    have h₂ : (1 : ℝ) ≤ max r₀ 1 ^ M.d := one_le_pow₀ (le_max_right _ _)
    have hr1 : (1 : ℝ) ≤ r ^ M.d := one_le_pow₀ hr
    nlinarith

/-- The two-point function is a probability, hence at most one. -/
theorem tau_le_one (x : M.V) : M.tau x ≤ 1 := by
  rw [M.tau_eq_twoPoint, SourceModelData.twoPoint, Measure.real_def]
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  simpa using measure_mono (μ := M.law M.betaCrit)
    (Set.subset_univ {ω : Config M.V | Connects ω 0 x})

/-- **Non-vacuity of the spatial-average hypothesis.**  When `α ≥ d` the bound of
Theorem I.2.13 is automatic: every two-point value is at most one and the ball has
`≼ r ^ d ≤ r ^ α` points.  (This is the paper's own remark that Theorem I.2.13
"holds vacuously when `α ≥ d`".) -/
theorem spatialTwoPointAverage_of_le_d (h : (M.d : ℝ) ≤ M.α) :
    SpatialTwoPointAverage M := by
  obtain ⟨Cb, hCb, hball⟩ := exists_ball_ncard_le M
  refine ⟨Cb, hCb, fun r hr => ?_⟩
  have hcard : ∑ x ∈ (M.finite_ball r).toFinset, M.tau x ≤ ((M.ball r).ncard : ℝ) := by
    have h₁ : ∑ _x ∈ (M.finite_ball r).toFinset, (1 : ℝ) = ((M.ball r).ncard : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast (Set.ncard_eq_toFinset_card (M.ball r) (M.finite_ball r)).symm
    rw [← h₁]
    exact Finset.sum_le_sum fun x _ => tau_le_one M x
  calc ∑ x ∈ (M.finite_ball r).toFinset, M.tau x ≤ ((M.ball r).ncard : ℝ) := hcard
    _ ≤ Cb * r ^ M.d := hball r hr
    _ ≤ Cb * r ^ M.α := by
        have hd : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg _
        have hpow : r ^ M.d ≤ r ^ M.α := by
          rw [← Real.rpow_natCast r M.d]
          exact Real.rpow_le_rpow_of_exponent_le hr h
        exact mul_le_mul_of_nonneg_left hpow hCb.le

/-- **From a power gain over Corollary I.2.15 to the hydrodynamic condition.**
If the median bound of Corollary I.2.15 can be improved by any positive power of
`r`, then `(Hydro)` holds.  This is the shape of the paper's passage from its
two-point estimates to `(Hydro)` in Corollary I.4.14; the content proved here is
only the elementary exponent comparison, the two-point input staying explicit. -/
theorem hydro_of_eventually_le_rpow {e C : ℝ}
    (he : e < ((M.d : ℝ) + M.α) / 2)
    (h : ∀ᶠ r : ℝ in atTop, (M.Mr r : ℝ) ≤ C * r ^ e) :
    Hydro M := by
  set E : ℝ := ((M.d : ℝ) + M.α) / 2 with hE
  have hδ : 0 < E - e := by rw [hE]; linarith
  have hratio : ∀ r : ℝ, E - e + e = E := fun r => by ring
  have hpow : Tendsto (fun r : ℝ => r ^ (-(E - e))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hδ
  have hmaj : ∀ᶠ r : ℝ in atTop,
      (M.Mr r : ℝ) / r ^ E ≤ C * r ^ (-(E - e)) := by
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hEr : (0 : ℝ) < r ^ E := Real.rpow_pos_of_pos hr0 _
    rw [div_le_iff₀ hEr]
    calc (M.Mr r : ℝ) ≤ C * r ^ e := hr
      _ = C * r ^ (-(E - e)) * r ^ E := by
          have hsum : -(E - e) + E = e := by ring
          rw [← hsum, Real.rpow_add hr0]
          ring_nf
  have hzero : Tendsto (fun r : ℝ => C * r ^ (-(E - e))) atTop (𝓝 0) := by
    simpa using hpow.const_mul C
  have hnonneg : ∀ᶠ r : ℝ in atTop, (0 : ℝ) ≤ (M.Mr r : ℝ) / r ^ E := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hEr : (0 : ℝ) < r ^ E := Real.rpow_pos_of_pos hr _
    positivity
  have hmain : Tendsto (fun r : ℝ => (M.Mr r : ℝ) / r ^ E) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := fun r : ℝ => (M.Mr r : ℝ) / r ^ E)
      (g := fun _ : ℝ => (0 : ℝ)) tendsto_const_nhds hzero hnonneg hmaj
  simpa [Hydro, hE] using hmain

/-- **Log-tolerant form of the power-gain interface.**  If the median bound of
Corollary I.2.15 can be improved by a power of `r` at the cost of any power of
`log r`, then `(Hydro)` holds.  This is the shape of the paper's Case-1 bound
`M_r ⪯ (E_{β_c,r}|K|)² log r ⪯ r^{2α} log r` when `d > 3α`. -/
theorem hydro_of_eventually_le_rpow_mul_log {e c C : ℝ}
    (he : e < ((M.d : ℝ) + M.α) / 2) (hC : 0 < C)
    (h : ∀ᶠ r : ℝ in atTop, (M.Mr r : ℝ) ≤ C * r ^ e * (Real.log r) ^ c) :
    Hydro M := by
  set E : ℝ := ((M.d : ℝ) + M.α) / 2 with hE
  have hδ : 0 < E - e := by rw [hE]; linarith
  have hhalf : 0 < (E - e) / 2 := by linarith
  have hlittle : (fun r : ℝ => Real.log r ^ c) =o[atTop] (fun r : ℝ => r ^ ((E - e) / 2)) :=
    isLittleO_log_rpow_rpow_atTop c hhalf
  have hlog : ∀ᶠ r : ℝ in atTop, Real.log r ^ c ≤ r ^ ((E - e) / 2) := by
    filter_upwards [hlittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with r hr hr1
    have hlog0 : (0 : ℝ) ≤ Real.log r := Real.log_nonneg hr1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 c),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hr
    exact hr
  have hmaj : ∀ᶠ r : ℝ in atTop,
      (M.Mr r : ℝ) / r ^ E ≤ C * r ^ ((e - E) / 2) := by
    filter_upwards [h, hlog, eventually_ge_atTop (1 : ℝ)] with r hr hrlog hr1
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr1
    have hEr : (0 : ℝ) < r ^ E := Real.rpow_pos_of_pos hr0 _
    rw [div_le_iff₀ hEr]
    calc (M.Mr r : ℝ) ≤ C * r ^ e * Real.log r ^ c := hr
      _ ≤ C * r ^ e * r ^ ((E - e) / 2) := by
          refine mul_le_mul_of_nonneg_left hrlog (by positivity)
      _ = C * r ^ ((e - E) / 2) * r ^ E := by
          have hrw : r ^ e * r ^ ((E - e) / 2) = r ^ ((e - E) / 2) * r ^ E := by
            rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]
            congr 1
            ring
          calc C * r ^ e * r ^ ((E - e) / 2) = C * (r ^ e * r ^ ((E - e) / 2)) := by ring
            _ = C * (r ^ ((e - E) / 2) * r ^ E) := by rw [hrw]
            _ = C * r ^ ((e - E) / 2) * r ^ E := by ring
  have hzero : Tendsto (fun r : ℝ => C * r ^ ((e - E) / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => C * r ^ (-((E - e) / 2))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hhalf).const_mul C
    have heq : -((E - e) / 2) = (e - E) / 2 := by ring
    rwa [heq] at h1
  have hnonneg : ∀ᶠ r : ℝ in atTop, (0 : ℝ) ≤ (M.Mr r : ℝ) / r ^ E := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
    have hEr : (0 : ℝ) < r ^ E := Real.rpow_pos_of_pos hr0 _
    positivity
  have hmain : Tendsto (fun r : ℝ => (M.Mr r : ℝ) / r ^ E) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := fun r : ℝ => (M.Mr r : ℝ) / r ^ E)
      (g := fun _ : ℝ => (0 : ℝ)) tendsto_const_nhds hzero hnonneg hmaj
  simpa [Hydro, hE] using hmain

/-- **Corollary I.2.15.** If the critical two-point function has spatial average
`≼ r ^ α` over `B_r` (the conclusion of the cited Theorem I.2.13), then the source
median `M_r` of `|K_max(B_r)|` under the cut-off law is `O(r ^ ((d + α) / 2))`,
uniformly for every `r ≥ 1`. -/
theorem Mr_le_rpow_of_spatialTwoPointAverage (h : SpatialTwoPointAverage M) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      (M.Mr r : ℝ) ≤ C * r ^ (((M.d : ℝ) + M.α) / 2) := by
  obtain ⟨C, hC, hCbound⟩ := h
  obtain ⟨Cb, hCb, hball⟩ := exists_ball_ncard_le M
  refine ⟨1 + Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)), by positivity, ?_⟩
  intro r hr
  have hr0 : (0 : ℝ) < r := by linarith
  have h2r : (1 : ℝ) ≤ 2 * r := by linarith
  set I : ℝ≥0∞ :=
    ∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.cutLaw r) with hI
  have hIle : I ≤ ENNReal.ofReal (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x) :=
    M5.interVol_le_ofReal_sum_tau M r
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hIle
  have hstep1 : ((M.Mr r : ℝ) - 1) ^ 2 ≤
      Real.exp 1 * ((M.ball r).ncard : ℝ) * I.toReal := by
    have hmain := M5.mr_sq_le_inter M r hr0.le
    have htop : ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) * I ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hItop
    calc ((M.Mr r : ℝ) - 1) ^ 2
        = (ENNReal.ofReal (((M.Mr r : ℝ) - 1) ^ 2)).toReal := by
          rw [ENNReal.toReal_ofReal (sq_nonneg _)]
      _ ≤ (ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) * I).toReal :=
          ENNReal.toReal_mono htop hmain
      _ = Real.exp 1 * ((M.ball r).ncard : ℝ) * I.toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hstep2 : I.toReal ≤ ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x :=
    M5.interVol_toReal_le_sum_tau M r
  have hsum : ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x ≤ C * 2 ^ M.α * r ^ M.α := by
    have h₁ := hCbound (2 * r) h2r
    have h₂ : (2 * r) ^ M.α = 2 ^ M.α * r ^ M.α := Real.mul_rpow (by norm_num) hr0.le
    rw [h₂] at h₁
    calc ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x ≤ C * (2 ^ M.α * r ^ M.α) := h₁
      _ = C * 2 ^ M.α * r ^ M.α := by ring
  have hK : (0 : ℝ) ≤ Real.exp 1 * Cb * (C * 2 ^ M.α) := by positivity
  have hsq : ((M.Mr r : ℝ) - 1) ^ 2 ≤
      (Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
        r ^ (((M.d : ℝ) + M.α) / 2)) ^ 2 := by
    have hfac : (0 : ℝ) ≤ Real.exp 1 * ((M.ball r).ncard : ℝ) := by positivity
    have hsum_nonneg : (0 : ℝ) ≤ ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x :=
      Finset.sum_nonneg fun x _ => M.tau_nonneg x
    calc ((M.Mr r : ℝ) - 1) ^ 2
        ≤ Real.exp 1 * ((M.ball r).ncard : ℝ) * I.toReal := hstep1
      _ ≤ Real.exp 1 * ((M.ball r).ncard : ℝ) *
            (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x) := by
          refine mul_le_mul_of_nonneg_left hstep2 hfac
      _ ≤ Real.exp 1 * (Cb * r ^ M.d) * (C * 2 ^ M.α * r ^ M.α) := by
          have hb := hball r hr
          have hCd : (0 : ℝ) ≤ C * 2 ^ M.α * r ^ M.α := by positivity
          have he : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
          have hn : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := by positivity
          have hb' : ((M.ball r).ncard : ℝ) ≤ Cb * r ^ M.d := hb
          have hs' : (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x) ≤
              C * 2 ^ M.α * r ^ M.α := hsum
          calc Real.exp 1 * ((M.ball r).ncard : ℝ) *
                (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x)
              ≤ Real.exp 1 * (Cb * r ^ M.d) *
                (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x) := by
                refine mul_le_mul_of_nonneg_right ?_ hsum_nonneg
                exact mul_le_mul_of_nonneg_left hb' he
            _ ≤ Real.exp 1 * (Cb * r ^ M.d) * (C * 2 ^ M.α * r ^ M.α) := by
                refine mul_le_mul_of_nonneg_left hs' ?_
                positivity
      _ = Real.exp 1 * Cb * (C * 2 ^ M.α) * (r ^ M.d * r ^ M.α) := by ring
      _ = Real.exp 1 * Cb * (C * 2 ^ M.α) * r ^ ((M.d : ℝ) + M.α) := by
          rw [← Real.rpow_natCast r M.d, ← Real.rpow_add hr0]
      _ = (Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
            r ^ (((M.d : ℝ) + M.α) / 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hK, ← Real.rpow_natCast _ 2,
            ← Real.rpow_mul hr0.le]
          ring_nf
  have hB : (0 : ℝ) ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
      r ^ (((M.d : ℝ) + M.α) / 2) := by positivity
  have habs : |(M.Mr r : ℝ) - 1| ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
      r ^ (((M.d : ℝ) + M.α) / 2) := by
    have h' := (sq_le_sq.mp hsq)
    rwa [abs_of_nonneg hB] at h'
  have hlin : (M.Mr r : ℝ) - 1 ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
      r ^ (((M.d : ℝ) + M.α) / 2) := le_trans (le_abs_self _) habs
  have hαpos : (0 : ℝ) < M.α := M.hα
  have hone : (1 : ℝ) ≤ r ^ (((M.d : ℝ) + M.α) / 2) :=
    Real.one_le_rpow hr (by positivity)
  calc (M.Mr r : ℝ) = ((M.Mr r : ℝ) - 1) + 1 := by ring
    _ ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) * r ^ (((M.d : ℝ) + M.α) / 2) + 1 := by
        linarith
    _ ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) * r ^ (((M.d : ℝ) + M.α) / 2) +
          r ^ (((M.d : ℝ) + M.α) / 2) := by linarith
    _ = (1 + Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α))) *
          r ^ (((M.d : ℝ) + M.α) / 2) := by ring



end M2I215

/-! ## The uncut critical median: the "In fact" clause of Corollary I.2.15 -/

namespace M2I215Uncut

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open PercLib.CriticalLRP PercLib.CriticalLRP.Orchestration PercLib.CriticalLRP.Percolation

variable (M : SourceModelData)

/-- The median of `|K_max(B_r)|` under the uncut critical law, i.e. the source's
`M_{β_c}(B_r)` in the "In fact" clause of Corollary I.2.15. -/
noncomputable def MrCrit (r : ℝ) : ℕ :=
  sInf {n : ℕ |
    (M.criticalLaw).real {ω : Config M.V | (n : ℝ≥0∞) ≤ M.maxClusterInBall r ω}
      ≤ Real.exp (-1)}

instance instCriticalLawIsProbability : IsProbabilityMeasure (M.criticalLaw) :=
  inferInstanceAs (IsProbabilityMeasure
    (longRangeMeasure M.kernel M.kernel_nonneg M.betaCrit))

/-- The uncut critical law is invariant under lattice translations. -/
theorem criticalLaw_map_shiftConfig (a : M.V) :
    (M.criticalLaw).map (shiftConfig a) = M.criticalLaw := by
  rw [SourceModelData.criticalLaw, SourceModelData.law, longRangeMeasure]
  exact edgeMeasure_shift_invariant _
    (fun a e => bernoulliEdgeProb_shift (J := M.kernel) (fun a e => M.kernel_shift a e)
      M.kernel_nonneg M.betaCrit a e) a

/-- `MrCrit` is the paper's median: the least `n` with
`P_{β_c}(|K_max(B_r)| ≥ n) ≤ e^{-1}`. -/
theorem MrCrit_eq_edianMaxVol (r : ℝ) :
    MrCrit M r = Percolation.edianMaxVol (M.criticalLaw) (E1Sign.ballF M r)
      (Percolation.exists_edianMaxVol (E1Sign.ballF M r)) := by
  classical
  have hset : ∀ n : ℕ,
      ((M.criticalLaw).real {ω : Config M.V | (n : ℝ≥0∞) ≤ M.maxClusterInBall r ω}
          ≤ Real.exp (-1))
        ↔ ((M.criticalLaw) {ω : Config M.V | (n : ℝ≥0∞) ≤
            Percolation.clusterMaxVol ω (E1Sign.ballF M r)}
            ≤ ENNReal.ofReal (Real.exp (-1))) := by
    intro n
    have hEq : {ω : Config M.V | (n : ℝ≥0∞) ≤ M.maxClusterInBall r ω}
        = {ω : Config M.V | (n : ℝ≥0∞) ≤
            Percolation.clusterMaxVol ω (E1Sign.ballF M r)} := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
      rw [PercLib.CriticalLRP.CaseTwo.clusterMaxVol_ballF M r ω]
    rw [hEq, Measure.real,
      ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos (-1)).le]
  have hne : ({n : ℕ | (M.criticalLaw).real
      {ω : Config M.V | (n : ℝ≥0∞) ≤ M.maxClusterInBall r ω}
        ≤ Real.exp (-1)}).Nonempty :=
    ⟨_, (hset _).mpr (Nat.find_spec (Percolation.exists_edianMaxVol (E1Sign.ballF M r)))⟩
  refine le_antisymm ?_ ?_
  · rw [MrCrit]
    exact Nat.sInf_le ((hset _).mpr (Nat.find_spec
      (Percolation.exists_edianMaxVol (E1Sign.ballF M r))))
  · rw [MrCrit]
    exact Nat.find_min' (Percolation.exists_edianMaxVol (E1Sign.ballF M r))
      ((hset _).mp (Nat.sInf_mem hne))

/-- Translation invariance of the windowed event under the uncut critical law. -/
theorem measure_clusterVolIn_ballAt_eq_crit (m : ℕ) (r : ℝ) (x : M.V) :
    (M.criticalLaw) {ω : Config M.V |
        (m : ℝ≥0∞) ≤ clusterVolIn ω x (M5.ballAt M x (2 * r))}
      = (M.criticalLaw) {ω : Config M.V |
          (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
  have hmeas0 : MeasurableSet
      {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} :=
    measurableSet_le measurable_const (measurable_clusterVolIn 0 _)
  have hid : ∀ ω : Config M.V,
      clusterVolIn (shiftConfig (-x) ω) (0 : M.V) (M.ball (2 * r))
        = clusterVolIn ω x (M5.ballAt M x (2 * r)) := by
    intro ω
    have h4 := M5.clusterVolIn_shift_image (M := M) (a := -x) (v := x) (ω := ω)
      (W := M5.ballAt M x (2 * r))
    have h3 : x + (-x) = (0 : M.V) := by abel
    rw [h3] at h4
    have himg : (fun y : M.V => y + (-x)) '' M5.ballAt M x (2 * r) = M.ball (2 * r) := by
      rw [← M5.ballAt_add_image M (-x) x (2 * r), h3, M5.ballAt_zero]
    rw [himg] at h4
    exact h4
  have hpre : shiftConfig (-x) ⁻¹'
      {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}
      = {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω x (M5.ballAt M x (2 * r))} := by
    ext ω
    change ((m : ℝ≥0∞) ≤ clusterVolIn (shiftConfig (-x) ω) 0 (M.ball (2 * r)))
      ↔ ((m : ℝ≥0∞) ≤ clusterVolIn ω x (M5.ballAt M x (2 * r)))
    rw [hid ω]
  calc (M.criticalLaw) {ω : Config M.V |
        (m : ℝ≥0∞) ≤ clusterVolIn ω x (M5.ballAt M x (2 * r))}
      = (M.criticalLaw) (shiftConfig (-x) ⁻¹'
          {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}) := by
        rw [hpre]
    _ = (M.criticalLaw).map (shiftConfig (-x))
          {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
        rw [Measure.map_apply (measurable_shiftConfig _) hmeas0]
    _ = (M.criticalLaw) {ω : Config M.V |
          (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
        rw [criticalLaw_map_shiftConfig M (-x)]

/-- The lintegral of the counting function under the uncut critical law. -/
theorem lintegral_winCount_crit (m : ℕ) (r : ℝ) :
    ∫⁻ ω, M5.winCount M m r ω ∂(M.criticalLaw)
      = ((M.ball r).ncard : ℝ≥0∞) *
          (M.criticalLaw) {ω : Config M.V |
            (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
  classical
  simp only [M5.winCount]
  rw [lintegral_finsetSum]
  · rw [Finset.sum_congr rfl (g := fun _ => (M.criticalLaw)
        {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))})]
    · rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [← Set.ncard_eq_toFinset_card (M.ball r) (M.finite_ball r)]
    · intro x _
      have hmeas : MeasurableSet
          {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω x (M5.ballAt M x (2 * r))} :=
        measurableSet_le measurable_const (measurable_clusterVolIn x _)
      have hfun : (fun ω => (if (m : ℝ≥0∞) ≤ clusterVolIn ω x (M5.ballAt M x (2 * r)) then
            (1 : ℝ≥0∞) else 0))
          = {ω : Config M.V |
              (m : ℝ≥0∞) ≤ clusterVolIn ω x (M5.ballAt M x (2 * r))}.indicator
              (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        by_cases h : (m : ℝ≥0∞) ≤ clusterVolIn ω x (M5.ballAt M x (2 * r))
        · simp [h]
        · simp [h]
      rw [hfun]
      exact (lintegral_indicator_one hmeas).trans (measure_clusterVolIn_ballAt_eq_crit M m r x)
  · intro b _
    exact Measurable.ite
      (measurableSet_le measurable_const (measurable_clusterVolIn b _))
      measurable_const measurable_const

/-- The median gives a lower bound for the averaging event, under the uncut law. -/
theorem mrCrit_measure_exists (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (Real.exp (-1)) ≤
      (M.criticalLaw) {ω : Config M.V | ∃ w ∈ M.ball r,
        (((MrCrit M r) - 1 : ℕ) : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)} := by
  classical
  set μ := M.criticalLaw
  set W := E1Sign.ballF M r
  have hW : (W : Set M.V) = M.ball r := PercLib.CriticalLRP.CaseTwo.coe_ballF M r
  have hMr1 : 1 ≤ MrCrit M r := by
    rw [MrCrit_eq_edianMaxVol M r]
    exact Percolation.one_le_edianMaxVol _ _
  have hMr : MrCrit M r = Percolation.edianMaxVol μ W
      (Percolation.exists_edianMaxVol W) :=
    MrCrit_eq_edianMaxVol M r
  rcases Nat.lt_or_ge (MrCrit M r) 2 with hsmall | hbig
  · have h1 : MrCrit M r = 1 := by omega
    have huniv : {ω : Config M.V | ∃ w ∈ M.ball r,
        (((MrCrit M r) - 1 : ℕ) : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)} = univ := by
      ext ω
      refine iff_true_intro ⟨0, PercLib.CriticalLRP.CaseTwo.zero_mem_ball M hr, ?_⟩
      rw [h1]
      simp
    rw [huniv, measure_univ]
    exact le_of_lt (ENNReal.ofReal_lt_one.mpr (by
      rw [Real.exp_lt_one_iff]
      norm_num))
  · have hm : 1 ≤ MrCrit M r - 1 := by omega
    have hlt : MrCrit M r - 1 < Percolation.edianMaxVol μ W
        (Percolation.exists_edianMaxVol W) := by
      rw [← hMr]
      omega
    have hmin := Percolation.edianOf_min (μ := μ)
      (X := fun ω => Percolation.clusterMaxVol ω W)
      (hex := Percolation.exists_edianMaxVol W) hlt
    refine le_trans (le_of_lt hmin) (measure_mono ?_)
    intro ω hω
    obtain ⟨w, hw, hle⟩ := (Percolation.le_clusterMaxVol_iff hm W ω).mp hω
    refine ⟨w, ?_, ?_⟩
    · exact hW ▸ Finset.mem_coe.mpr hw
    · rw [hW] at hle
      exact hle

/-- The averaging step at the uncut law. -/
theorem averaging_bound_ball_crit (m : ℕ) (r : ℝ)
    (hA : ENNReal.ofReal (Real.exp (-1)) ≤
      (M.criticalLaw) {ω : Config M.V | ∃ w ∈ M.ball r,
        (m : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)}) :
    ENNReal.ofReal (Real.exp (-1) * (m : ℝ)) ≤
      ENNReal.ofReal ((M.ball r).ncard : ℝ) *
        (M.criticalLaw) {ω : Config M.V |
          (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
  classical
  set μ := M.criticalLaw
  set A : Set (Config M.V) :=
    {ω | ∃ w ∈ M.ball r, (m : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)} with hAdef
  have hAmeas : MeasurableSet A := by
    have hset : A = ⋃ w ∈ (M.finite_ball r).toFinset,
        {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω w (M.ball r)} := by
      ext ω
      simp only [hAdef, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨w, hw, hle⟩
        exact ⟨w, (M.finite_ball r).mem_toFinset.mpr hw, hle⟩
      · rintro ⟨w, hw, hle⟩
        exact ⟨w, (M.finite_ball r).mem_toFinset.mp hw, hle⟩
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun w _ =>
      measurableSet_le measurable_const (measurable_clusterVolIn w _)
  have hpoint : ∀ ω : Config M.V,
      (m : ℝ≥0∞) * A.indicator (fun _ => (1 : ℝ≥0∞)) ω ≤ M5.winCount M m r ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, mul_one]
      exact M5.le_winCount M hω
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact bot_le
  calc ENNReal.ofReal (Real.exp (-1) * (m : ℝ))
      = (m : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-1)) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos (-1)).le, ENNReal.ofReal_natCast]
        ring
    _ ≤ (m : ℝ≥0∞) * μ A := by
        rw [hAdef]
        gcongr
    _ = ∫⁻ ω, (m : ℝ≥0∞) * A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
        rw [lintegral_const_mul _ (measurable_const.indicator hAmeas)]
        rw [show ∫⁻ a, A.indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ = μ A from
          lintegral_indicator_one hAmeas]
    _ ≤ ∫⁻ ω, M5.winCount M m r ω ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal ((M.ball r).ncard : ℝ) *
          μ {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} := by
        rw [lintegral_winCount_crit M m r, ENNReal.ofReal_natCast]

/-- **The windowed median inequality at the uncut critical law.** -/
theorem mrCrit_sq_le_inter (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (((MrCrit M r : ℝ) - 1) ^ 2) ≤
      ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) *
        ∫⁻ ω, clusterVolIn ω 0 (M.ball (2 * r)) ∂(M.criticalLaw) := by
  classical
  set μ := M.criticalLaw
  set m : ℕ := MrCrit M r - 1 with hm
  set q : ℝ≥0∞ :=
    μ {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} with hq
  set E : ℝ≥0∞ := ∫⁻ ω, clusterVolIn ω 0 (M.ball (2 * r)) ∂μ with hE
  have hMr1 : 1 ≤ MrCrit M r := by
    rw [MrCrit_eq_edianMaxVol M r]
    exact Percolation.one_le_edianMaxVol _ _
  have hmcast : (m : ℝ) + 1 = (MrCrit M r : ℝ) := by
    have h : m + 1 = MrCrit M r := by
      rw [hm]
      exact Nat.sub_add_cancel hMr1
    exact_mod_cast h
  have hmr : (m : ℝ) = (MrCrit M r : ℝ) - 1 := by linarith
  have h1 : ENNReal.ofReal (Real.exp (-1) * (m : ℝ)) ≤
      ENNReal.ofReal ((M.ball r).ncard : ℝ) * q :=
    averaging_bound_ball_crit M m r (mrCrit_measure_exists M r hr)
  have h2 : (m : ℝ≥0∞) * q ≤ E := by
    have hmeas : MeasurableSet
        {ω : Config M.V | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} :=
      measurableSet_le measurable_const (measurable_clusterVolIn 0 _)
    have hpoint : ∀ ω : Config M.V,
        (m : ℝ≥0∞) * {ω : Config M.V |
            (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω ≤ clusterVolIn ω 0 (M.ball (2 * r)) := by
      intro ω
      by_cases hω : ω ∈ {ω : Config M.V |
          (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}
      · rw [Set.indicator_of_mem hω, mul_one]
        exact hω
      · rw [Set.indicator_of_notMem hω, mul_zero]
        exact bot_le
    calc (m : ℝ≥0∞) * q
        = ∫⁻ ω, (m : ℝ≥0∞) *
            {ω : Config M.V |
              (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
          rw [hq, lintegral_const_mul _ (measurable_const.indicator hmeas)]
          rw [show ∫⁻ a, {ω : Config M.V |
              (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))}.indicator
              (fun _ => (1 : ℝ≥0∞)) a ∂μ
              = μ {ω : Config M.V |
                (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (M.ball (2 * r))} from
            lintegral_indicator_one hmeas]
      _ ≤ ∫⁻ ω, clusterVolIn ω 0 (M.ball (2 * r)) ∂μ := lintegral_mono hpoint
      _ = E := rfl
  have h3 : ENNReal.ofReal (Real.exp (-1) * (m : ℝ) ^ 2) ≤
      ENNReal.ofReal ((M.ball r).ncard : ℝ) * E := by
    have hmul : ENNReal.ofReal (Real.exp (-1) * (m : ℝ)) * (m : ℝ≥0∞)
        = ENNReal.ofReal (Real.exp (-1) * (m : ℝ) ^ 2) := by
      rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    rw [← hmul]
    calc ENNReal.ofReal (Real.exp (-1) * (m : ℝ)) * (m : ℝ≥0∞)
        ≤ (ENNReal.ofReal ((M.ball r).ncard : ℝ) * q) * (m : ℝ≥0∞) := by
          gcongr
      _ = ENNReal.ofReal ((M.ball r).ncard : ℝ) * ((m : ℝ≥0∞) * q) := by ring
      _ ≤ ENNReal.ofReal ((M.ball r).ncard : ℝ) * E := by gcongr
  have h4 : ENNReal.ofReal ((m : ℝ) ^ 2) ≤
      ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) * E := by
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hfac : Real.exp 1 * (Real.exp (-1) * (m : ℝ) ^ 2) = (m : ℝ) ^ 2 := by
      rw [← mul_assoc, Real.exp_neg]
      field_simp
    calc ENNReal.ofReal ((m : ℝ) ^ 2)
        = ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-1) * (m : ℝ) ^ 2) := by
          rw [← ENNReal.ofReal_mul he.le, hfac]
      _ ≤ ENNReal.ofReal (Real.exp 1) *
            (ENNReal.ofReal ((M.ball r).ncard : ℝ) * E) := by gcongr
      _ = ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) * E := by
          rw [ENNReal.ofReal_mul he.le]
          ring
  rwa [hmr] at h4

/-- The uncut first moment of the cluster inside `B_{2r}` is the sum of the two-point
function over `B_{2r}` (Tonelli, at the uncut critical law). -/
theorem lintegral_clusterVolIn_ball_eq_sum_crit (r : ℝ) :
    ∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.criticalLaw)
      = ∑ x ∈ (M.finite_ball (2 * r)).toFinset, ENNReal.ofReal (M.tau x) := by
  classical
  set μ := M.criticalLaw
  set F := (M.finite_ball (2 * r)).toFinset with hF
  set W : Set M.V := M.ball (2 * r) with hW
  have hFcoe : (F : Set M.V) = W := by
    rw [hF, hW]
    exact (M.finite_ball (2 * r)).coe_toFinset
  have hind : ∀ ω : Config M.V, clusterVolIn ω (0 : M.V) W
      = ∑ x ∈ F, (cluster ω (0 : M.V) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro ω
    rw [clusterVolIn_eq_tsum]
    refine tsum_eq_sum ?_
    intro x hx
    have hx' : x ∉ W := by
      rw [← hFcoe]
      exact fun hmem => hx (by rwa [hF] at hmem)
    exact Set.indicator_of_notMem (fun hh => hx' hh.2) _
  calc ∫⁻ ω, clusterVolIn ω (0 : M.V) W ∂μ
      = ∫⁻ ω, ∑ x ∈ F, (cluster ω (0 : M.V) ∩ W).indicator
            (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
        exact lintegral_congr hind
    _ = ∑ x ∈ F, ∫⁻ ω, (cluster ω (0 : M.V) ∩ W).indicator
            (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
        rw [lintegral_finsetSum]
        intro b _
        have hmeas : MeasurableSet {ω : Config M.V | (cluster ω (0 : M.V) ∩ W) b} := by
          by_cases hb : b ∈ W
          · have hset : {ω : Config M.V | (cluster ω (0 : M.V) ∩ W) b}
                = {ω : Config M.V | b ∈ cluster ω (0 : M.V)} := by
              ext ω
              exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩
            rw [hset]
            exact measurableSet_cluster_mem 0 b
          · have hset : {ω : Config M.V | (cluster ω (0 : M.V) ∩ W) b}
                = (∅ : Set (Config M.V)) := by
              ext ω
              exact ⟨fun h => absurd h.2 hb, fun h => h.elim⟩
            rw [hset]
            exact MeasurableSet.empty
        exact measurable_const.indicator hmeas
    _ = ∑ x ∈ F, ENNReal.ofReal (M.tau x) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxW : x ∈ W := by
          rw [← hFcoe]
          exact hx
        have hmeas : MeasurableSet {ω : Config M.V | x ∈ cluster ω (0 : M.V)} :=
          measurableSet_cluster_mem 0 x
        have hfun : (fun ω => (cluster ω (0 : M.V) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) x)
            = {ω : Config M.V | x ∈ cluster ω (0 : M.V)}.indicator
                (fun _ => (1 : ℝ≥0∞)) := by
          funext ω
          by_cases h : x ∈ cluster ω (0 : M.V)
          · have hmem : ω ∈ {ω : Config M.V | x ∈ cluster ω (0 : M.V)} := h
            rw [Set.indicator_of_mem (Set.mem_inter h hxW), Set.indicator_of_mem hmem]
          · have hmem : ω ∉ {ω : Config M.V | x ∈ cluster ω (0 : M.V)} := h
            rw [Set.indicator_of_notMem (fun hh => h hh.1), Set.indicator_of_notMem hmem]
        rw [hfun]
        rw [show ∫⁻ a, {ω : Config M.V | x ∈ cluster ω (0 : M.V)}.indicator
              (fun _ => (1 : ℝ≥0∞)) a ∂μ
              = μ {ω : Config M.V | x ∈ cluster ω (0 : M.V)} from
            lintegral_indicator_one hmeas]
        have hEqSet : {ω : Config M.V | x ∈ cluster ω (0 : M.V)}
            = {ω : Config M.V | Connects ω 0 x} := by
          ext ω
          exact mem_cluster_iff
        have htwo : M.tau x = (μ {ω : Config M.V | Connects ω 0 x}).toReal := by
          rw [M.tau_eq_twoPoint]
          rfl
        rw [hEqSet, htwo, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- `E_{β_c}|K ∩ B_{2r}| ≤ ∑_{x ∈ B_{2r}} P_{β_c}(0 ↔ x)`. -/
theorem interVol_toReal_le_sum_tau_crit (r : ℝ) :
    (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.criticalLaw)).toReal
      ≤ ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x := by
  rw [lintegral_clusterVolIn_ball_eq_sum_crit M r, ENNReal.toReal_sum]
  · refine Finset.sum_le_sum fun x _ => ?_
    rw [ENNReal.toReal_ofReal (M.tau_nonneg x)]
  · intro i _
    exact ENNReal.ofReal_ne_top

/-- **The "In fact" clause of Corollary I.2.15.**  If the critical two-point function
has spatial average `≼ r ^ α` over `B_r` (the cited Theorem I.2.13), then the median
`M_{β_c}(B_r)` of `|K_max(B_r)|` under the *uncut* law `P_{β_c}` is `O(r ^ ((d+α)/2))`,
uniformly for every `r ≥ 1`. -/
theorem MrCrit_le_rpow_of_spatialTwoPointAverage (h : M2I215.SpatialTwoPointAverage M) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      (MrCrit M r : ℝ) ≤ C * r ^ (((M.d : ℝ) + M.α) / 2) := by
  obtain ⟨C, hC, hCbound⟩ := h
  obtain ⟨Cb, hCb, hball⟩ := M2I215.exists_ball_ncard_le M
  refine ⟨1 + Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)), by positivity, ?_⟩
  intro r hr
  have hr0 : (0 : ℝ) < r := by linarith
  have h2r : (1 : ℝ) ≤ 2 * r := by linarith
  set I : ℝ≥0∞ :=
    ∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball (2 * r)) ∂(M.criticalLaw) with hI
  have hIle : I ≤ ENNReal.ofReal (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x) := by
    rw [show I = ∑ x ∈ (M.finite_ball (2 * r)).toFinset, ENNReal.ofReal (M.tau x) from
      lintegral_clusterVolIn_ball_eq_sum_crit M r]
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => M.tau_nonneg x)]
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hIle
  have hstep1 : ((MrCrit M r : ℝ) - 1) ^ 2 ≤
      Real.exp 1 * ((M.ball r).ncard : ℝ) * I.toReal := by
    have hmain := mrCrit_sq_le_inter M r hr0.le
    have htop : ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) * I ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hItop
    calc ((MrCrit M r : ℝ) - 1) ^ 2
        = (ENNReal.ofReal (((MrCrit M r : ℝ) - 1) ^ 2)).toReal := by
          rw [ENNReal.toReal_ofReal (sq_nonneg _)]
      _ ≤ (ENNReal.ofReal (Real.exp 1 * ((M.ball r).ncard : ℝ)) * I).toReal :=
          ENNReal.toReal_mono htop hmain
      _ = Real.exp 1 * ((M.ball r).ncard : ℝ) * I.toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hstep2 : I.toReal ≤ ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x :=
    interVol_toReal_le_sum_tau_crit M r
  have hsum : ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x ≤
      C * 2 ^ M.α * r ^ M.α := by
    have h₁ := hCbound (2 * r) h2r
    have h₂ : (2 * r) ^ M.α = 2 ^ M.α * r ^ M.α := Real.mul_rpow (by norm_num) hr0.le
    rw [h₂] at h₁
    calc ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x ≤ C * (2 ^ M.α * r ^ M.α) := h₁
      _ = C * 2 ^ M.α * r ^ M.α := by ring
  have hK : (0 : ℝ) ≤ Real.exp 1 * Cb * (C * 2 ^ M.α) := by positivity
  have hsq : ((MrCrit M r : ℝ) - 1) ^ 2 ≤
      (Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
        r ^ (((M.d : ℝ) + M.α) / 2)) ^ 2 := by
    have hfac : (0 : ℝ) ≤ Real.exp 1 * ((M.ball r).ncard : ℝ) := by positivity
    have hsum_nonneg : (0 : ℝ) ≤ ∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x :=
      Finset.sum_nonneg fun x _ => M.tau_nonneg x
    calc ((MrCrit M r : ℝ) - 1) ^ 2
        ≤ Real.exp 1 * ((M.ball r).ncard : ℝ) * I.toReal := hstep1
      _ ≤ Real.exp 1 * ((M.ball r).ncard : ℝ) *
            (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x) := by
          refine mul_le_mul_of_nonneg_left hstep2 hfac
      _ ≤ Real.exp 1 * (Cb * r ^ M.d) * (C * 2 ^ M.α * r ^ M.α) := by
          have hb := hball r hr
          have he : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
          have hb' : ((M.ball r).ncard : ℝ) ≤ Cb * r ^ M.d := hb
          calc Real.exp 1 * ((M.ball r).ncard : ℝ) *
                (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x)
              ≤ Real.exp 1 * (Cb * r ^ M.d) *
                (∑ x ∈ (M.finite_ball (2 * r)).toFinset, M.tau x) := by
                refine mul_le_mul_of_nonneg_right ?_ hsum_nonneg
                exact mul_le_mul_of_nonneg_left hb' he
            _ ≤ Real.exp 1 * (Cb * r ^ M.d) * (C * 2 ^ M.α * r ^ M.α) := by
                refine mul_le_mul_of_nonneg_left hsum ?_
                positivity
      _ = Real.exp 1 * Cb * (C * 2 ^ M.α) * (r ^ M.d * r ^ M.α) := by ring
      _ = Real.exp 1 * Cb * (C * 2 ^ M.α) * r ^ ((M.d : ℝ) + M.α) := by
          rw [← Real.rpow_natCast r M.d, ← Real.rpow_add hr0]
      _ = (Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
            r ^ (((M.d : ℝ) + M.α) / 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hK, ← Real.rpow_natCast _ 2,
            ← Real.rpow_mul hr0.le]
          ring_nf
  have hB : (0 : ℝ) ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
      r ^ (((M.d : ℝ) + M.α) / 2) := by positivity
  have habs : |(MrCrit M r : ℝ) - 1| ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
      r ^ (((M.d : ℝ) + M.α) / 2) := by
    have h' := (sq_le_sq.mp hsq)
    rwa [abs_of_nonneg hB] at h'
  have hlin : (MrCrit M r : ℝ) - 1 ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
      r ^ (((M.d : ℝ) + M.α) / 2) := le_trans (le_abs_self _) habs
  have hαpos : (0 : ℝ) < M.α := M.hα
  have hone : (1 : ℝ) ≤ r ^ (((M.d : ℝ) + M.α) / 2) :=
    Real.one_le_rpow hr (by positivity)
  calc (MrCrit M r : ℝ) = ((MrCrit M r : ℝ) - 1) + 1 := by ring
    _ ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
        r ^ (((M.d : ℝ) + M.α) / 2) + 1 := by linarith
    _ ≤ Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α)) *
          r ^ (((M.d : ℝ) + M.α) / 2) + r ^ (((M.d : ℝ) + M.α) / 2) := by linarith
    _ = (1 + Real.sqrt (Real.exp 1 * Cb * (C * 2 ^ M.α))) *
          r ^ (((M.d : ℝ) + M.α) / 2) := by ring

end M2I215Uncut

set_option linter.hashCommand false
#print axioms M2I215.exists_ball_ncard_le
#print axioms M2I215.tau_le_one
#print axioms M2I215.spatialTwoPointAverage_of_le_d
#print axioms M2I215.hydro_of_eventually_le_rpow
#print axioms M2I215.hydro_of_eventually_le_rpow_mul_log
#print axioms M2I215.Mr_le_rpow_of_spatialTwoPointAverage
#print axioms M2I215Uncut.criticalLaw_map_shiftConfig
#print axioms M2I215Uncut.MrCrit_eq_edianMaxVol
#print axioms M2I215Uncut.mrCrit_sq_le_inter
#print axioms M2I215Uncut.interVol_toReal_le_sum_tau_crit
#print axioms M2I215Uncut.MrCrit_le_rpow_of_spatialTwoPointAverage
