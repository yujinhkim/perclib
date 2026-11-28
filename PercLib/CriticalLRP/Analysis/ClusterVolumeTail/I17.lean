/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The tail constant of (I.1.7) from Proposition I.3.2

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Theorem I.1.6 / (I.1.7) (p. 10) and the paragraph "Proof of (I.1.7)
and (I.1.17) given (I.1.6) and (I.1.16)" (pp. 32-33) following Proposition I.3.2 (p. 30).

`PercLib.CriticalLRP.Analysis.I32.prop_I_3_2_of_restoration` proves the paper's
Proposition I.3.2 with the constant `A3` existential: it produces
`∃ A3, 0 < A3 ∧ A3cand A1 A2 a Qinf → A3 ∧ <MGF and tail asymptotics with that A3>`.
This file supplies the assembly the paper performs when deducing (I.1.7): the *explicit*
value of `A3` (and of `A4 = A3/Γ(1/a)`) for the chi-square limit law, and the resulting
tail formula at integer `n` with the printed constant.

Main results:

* `tendsto_A3cand_two_Qinf`: for the paper's limit law `Q∞ = law(Z²)` (`Z` standard
  normal) and `a = 2`, `A3cand A1 A2 2 Q∞ → A3chi A1 A2 = √2 A1/√A2`. Hence the
  implicitly defined `A3` of Proposition I.3.2 is the explicit constant.
* `genInv_rpow_eq`: the generalized inverse used by the production I.3.2 assembler of
  `x ↦ x^ρ` is `y ↦ max x₀ y^(1/ρ)`; for `f r = r^(2α)` this makes the (I.3.3) factor
  `(D.genInv n)^α / n` exactly `1/√n` above the threshold.
* `tendsto_tail_I17_of_moments`: (I.1.7) at integer `n` with the printed constant
  `(α/β_c)√(2/(πA))`, from the hypotheses of Proposition I.3.2 at `a = 2`, `f r = r^(2α)`.
  In the application `A1 = α/β_c` and `A2 = A`, exactly the normalisation constraint
  recorded as finding N1 in `docs/CRITICAL_LRP_FIDELITY_AUDIT.md`: the tail constant is
  `A4chi (α/β_c) A = √2 (α/β_c)/(√A √π)`, i.e. (I.1.7) uses the same `A` as (I.1.6)
  with no further rescaling by `α/β_c`.
-/
module

public import PercLib.CriticalLRP.Analysis.ChiSquareA3
public import PercLib.CriticalLRP.Analysis.PercolationI32
public import PercLib.CriticalLRP.Analysis.VolumeTailModel
public import PercLib.CriticalLRP.Orchestration.Defs

/-! The explicit first-order critical volume-tail constant, conditional on the
paper's restoration, weak-convergence, finiteness and moment-asymptotic inputs. -/

set_option linter.hashCommand false

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace PercLib.CriticalLRP.I17

open PercLib.CriticalLRP.Analysis
open PercLib.CriticalLRP.Analysis.I32
open PercLib.CriticalLRP.Anchor
open PercLib.CriticalLRP

/-! ## 1. The constant `A3` of Proposition I.3.2 is explicit for the chi-square limit law -/

/-- The `A3` exponent of Proposition I.3.2 at `a = 2` is `-1/2`. -/
theorem neg_half_eq : -((2 : ℝ) - 1) / 2 = -(1 / 2) := by norm_num

/-- The candidate `A3` of Proposition I.3.2 in the form `(A1/√A2) * L`, where `L` is the
`λ → ∞` limit of `λ^(-(a-1)/a) ∫ (1-e^(-λy))/y dQ∞`, at `a = 2`. -/
theorem A3cand_two_eq (A1 A2 : ℝ) (hA2 : 0 < A2) (Q : Measure ℝ) (lam : ℝ) :
    A3cand A1 A2 2 Q lam
      = A3const A1 A2 2 (lam ^ (-((2 : ℝ) - 1) / 2) * ∫ y, kern lam y ∂Q) := by
  unfold A3cand A3const
  rw [neg_half_eq, Real.rpow_neg hA2.le (1 / 2), div_eq_mul_inv]
  ring

theorem integral_kern_Qinf_apply (lam : ℝ) :
    (∫ y, kern lam y ∂Qinf) = ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Qinf := by
  simp only [kern]

/-- **The `A3` limit of Proposition I.3.2 at the paper's chi-square limit law**:
the candidate constant converges to the explicit `A3chi A1 A2 = √2 A1/√A2`. -/
theorem tendsto_A3cand_two_Qinf (A1 A2 : ℝ) (hA2 : 0 < A2) :
    Tendsto (A3cand A1 A2 2 Qinf) atTop (𝓝 (A3chi A1 A2)) := by
  have hlim := Anchor.tendsto_A3_kernel_Qinf.const_mul (A1 / A2 ^ ((1 : ℝ) / 2))
  refine Tendsto.congr' ?_ hlim
  filter_upwards with lam
  rw [A3cand_two_eq A1 A2 hA2, integral_kern_Qinf_apply]
  simp only [A3const]
  rw [show (-((2 : ℝ) - 1)) / 2 = -(((2 : ℝ) - 1) / 2) by norm_num]

/-! ## 2. The generalized inverse of a monomial -/

/-- **The generalized inverse of `x ↦ x^ρ`**: on `[0,∞)` the level set
`{x ≥ x₀ | y ≤ x^ρ}` is the interval `[max x₀ y^(1/ρ), ∞)`, whose infimum is
`max x₀ y^(1/ρ)`. -/
theorem genInv_rpow_eq {ρ : ℝ} (hρ : 0 < ρ) {x0 y : ℝ} (hx0 : 0 ≤ x0) (hy : 0 ≤ y) :
    genInv (fun x : ℝ => x ^ ρ) x0 y = max x0 (y ^ (1 / ρ)) := by
  have hset : {x : ℝ | x0 ≤ x ∧ y ≤ x ^ ρ} = Ici (max x0 (y ^ (1 / ρ))) := by
    ext x
    rw [mem_ofPred_eq, mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩
      have hxnn : 0 ≤ x := le_trans hx0 h1
      have hstep : y ^ (1 / ρ) ≤ (x ^ ρ) ^ (1 / ρ) :=
        Real.rpow_le_rpow hy h2 (le_of_lt (one_div_pos.mpr hρ))
      rw [one_div, Real.rpow_rpow_inv hxnn hρ.ne'] at hstep
      exact max_le h1 (by simpa only [one_div] using hstep)
    · intro h
      have hx0' : x0 ≤ x := le_trans (le_max_left _ _) h
      have hyx : y ^ (1 / ρ) ≤ x := le_trans (le_max_right _ _) h
      have hstep : (y ^ (1 / ρ)) ^ ρ ≤ x ^ ρ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hy _) hyx hρ.le
      rw [one_div, Real.rpow_inv_rpow hy hρ.ne'] at hstep
      exact ⟨hx0', hstep⟩
  rw [genInv_def, hset, csInf_Ici]

/-- The inverse of the paper's `f r = r^(2α)` inside the production I.3.2 assembler. -/
theorem genInv_rpow_two_mul {α : ℝ} (hα : 0 < α)
    (D : RVPosData (fun r : ℝ => r ^ (2 * α)) (2 * α)) {x : ℝ} (hx : 0 ≤ x) :
    D.genInv x = max D.threshold (x ^ (1 / (2 * α))) := by
  have h2α : 0 < 2 * α := by positivity
  have h := genInv_rpow_eq h2α (le_trans zero_le_one D.one_le_threshold) hx
  simpa only [RVPosData.genInv, Analysis.genInv] using h

/-- **The `(genInv)^α` identity of (I.3.3)**: for `f r = r^(2α)`, above the threshold the
generalized inverse is the genuine inverse, so `(D.genInv x)^α = √x`. -/
theorem genInv_rpow_two_mul_pow {α : ℝ} (hα : 0 < α)
    (D : RVPosData (fun r : ℝ => r ^ (2 * α)) (2 * α)) {x : ℝ} (hx : 0 ≤ x)
    (hxthr : D.threshold ≤ x ^ (1 / (2 * α))) :
    D.genInv x ^ α = x ^ ((1 : ℝ) / 2) := by
  rw [genInv_rpow_two_mul hα D hx, max_eq_right hxthr, ← Real.rpow_mul hx]
  rw [show 1 / (2 * α) * α = (1 : ℝ) / 2 by field_simp]

/-- **The (I.3.3) scale factor is exactly `1/√n`** for `a = 2` and `f r = r^(2α)`, above the
threshold of the regular-variation data. -/
theorem genInv_tail_factor {α : ℝ} (hα : 0 < α)
    (D : RVPosData (fun r : ℝ => r ^ (2 * α)) (2 * α)) {x : ℝ} (hx : 0 < x)
    (hxthr : D.threshold ≤ x ^ (1 / (2 * α))) :
    D.genInv x ^ α / x = (Real.sqrt x)⁻¹ := by
  rw [genInv_rpow_two_mul_pow hα D hx.le hxthr, Real.sqrt_eq_rpow]
  have h1 : x ^ ((1 : ℝ) / 2 - 1) = x ^ ((1 : ℝ) / 2) / x := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  rw [← h1, show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg hx.le]

/-! ## 3. The printed constant `(α/β_c)√(2/(πA))` of (I.1.7) -/

/-- The constant of (I.1.7) written with `A1 = α/β_c` and `A2 = A`. -/
noncomputable def I17const (A1 A2 : ℝ) : ℝ := A1 * Real.sqrt (2 / (Real.pi * A2))

/-- `I17const A1 A2` is the `A4` of Proposition I.3.2 for the chi-square limit law. -/
theorem I17const_eq_A4chi (A1 A2 : ℝ) (hA2 : 0 < A2) :
    I17const A1 A2 = A4chi A1 A2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : Real.sqrt (2 / (Real.pi * A2))
      = Real.sqrt 2 / (Real.sqrt Real.pi * Real.sqrt A2) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul hπ.le]
  rw [I17const, A4chi_eq A1 A2 hA2, h1]
  field_simp

/-! ## 4. The tail (I.1.7) from the hypotheses of Proposition I.3.2 at `a = 2` -/

/-- Hypothesis (4) of Proposition I.3.2 for the paper's limit law `Q∞ = law(Z²)`. -/
theorem Qinf_Iio_zero : Qinf (Iio 0) = 0 := by
  have h := Anchor.Qinf_ae_nonneg
  rw [ae_iff] at h
  exact measure_mono_null (fun x hx => by
    simp only [mem_ofPred_eq]
    exact not_le.mpr (by simpa using hx)) h

/-- The monomial `x ↦ x^ρ` is regularly varying at `∞` of index `ρ`. -/
theorem regularlyVaryingAtTop_rpow (ρ : ℝ) :
    RegularlyVaryingAtTop (fun x : ℝ => x ^ ρ) ρ := by
  constructor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.rpow_pos_of_pos hx ρ).ne'
  · intro l hl
    have heq : (fun x : ℝ => (l * x) ^ ρ / x ^ ρ) =ᶠ[atTop] fun _ => l ^ ρ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.mul_rpow hl.le hx.le, mul_div_assoc,
        div_self (Real.rpow_pos_of_pos hx ρ).ne', mul_one]
    rw [tendsto_congr' heq]
    exact tendsto_const_nhds

/-- **(I.1.7) with the printed constant, from the hypotheses of Proposition I.3.2.**

Given the paper's hypotheses (1)-(4) of Proposition I.3.2 at `a = 2` and `f r = r^(2α)` —
i.e. `E|K| ∼ A1 r^α` and `Ê|K| ∼ A2 r^(2α)` with `Q∞` the chi-square law of one
degree of freedom — together with the restoration estimate (I.3.5), the uncut
cluster-volume tail has the exact asymptotic

  `P(|K| ≥ n) ∼ (A1 √(2/(π A2))) / √n`  as `n → ∞` through the integers,

which is (I.1.7) with `A1 = α/β_c`, `A2 = A`. The constant is the paper's printed one and
`A3`/`A4` are not existential: `A4chi A1 A2` was evaluated by `Anchor.A4chi_eq`.

The hypotheses are exactly the production interface of `prop_I_3_2_of_restoration`; the
content added here is the explicit constant, the generalized inverse of `f r = r^(2α)`,
and the passage to integer `n`. No hypothesis of Proposition I.3.2 is discharged here. -/
theorem tendsto_tail_I17_of_moments
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ)
    {α A1 A2 C : ℝ} (hα : 0 < α) (hA1 : 0 < A1) (hA2 : 0 < A2) (hC : 0 < C)
    (hmuProb : ∀ r, IsProbabilityMeasure (mu r)) [IsProbabilityMeasure muinf]
    (hmu : ∀ r, mu r (Iio 0) = 0) (hmuinf : muinf (Iio 0) = 0)
    (hint1 : ∀ r, Integrable (fun x : ℝ => x) (mu r))
    (hint2 : ∀ r, Integrable (fun x : ℝ => x ^ 2) (mu r))
    (hEpos : ∀ r, 0 < mean (mu r)) (hSpos : ∀ r, 0 < sbMean (mu r))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (mu r)))
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure (sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    (hE1 : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (hψ2 : Tendsto (fun r => sbMean (mu r) / (A2 * r ^ (2 * α))) atTop (𝓝 1))
    (hI35 : ∀ᶠ r in atTop, ∀ h > 0,
      lapDefect (mu r) h ≤ lapDefect muinf h ∧
      lapDefect muinf h ≤ lapDefect (mu r) h +
        C * r ^ (-α) * (∫ x, x * Real.exp (-(h * x)) ∂(mu r)) * lapDefect muinf h) :
    Tendsto (fun n : ℕ => (muinf (Ici (n : ℝ))).toReal /
      (I17const A1 A2 * (1 / Real.sqrt (n : ℝ)))) atTop (𝓝 1) := by
  have hmeas : Measurable (fun r : ℝ => r ^ (2 * α)) := by fun_prop
  have hrv : RegularlyVaryingAtTop (fun r : ℝ => r ^ (2 * α)) (2 * α) :=
    regularlyVaryingAtTop_rpow (2 * α)
  obtain ⟨A3, -, hA3cand, -, htail⟩ :=
    prop_I_3_2_of_restoration (mu := mu) (muinf := muinf) (Qinf := Qinf)
      (f := fun r : ℝ => r ^ (2 * α)) (a := 2) (α := α)
      (A1 := A1) (A2 := A2) (C := C) (by norm_num) hα hA1 hA2 hC hmeas hrv hmuProb
      hmu hmuinf hint1 hint2 hEpos hSpos hprob Qinf_Iio_zero Qinf_singleton_zero hconv
      hE1 hψ2 hI35
  have hA3eq : A3 = A3chi A1 A2 :=
    tendsto_nhds_unique hA3cand (tendsto_A3cand_two_Qinf A1 A2 hA2)
  subst hA3eq
  obtain ⟨D, htail⟩ : ∃ D : RVPosData (fun r : ℝ => r ^ (2 * α)) (2 * α),
      Tendsto (fun x : ℝ => (muinf (Ici x)).toReal /
        ((A3chi A1 A2 / Real.Gamma (1 / 2)) * (D.genInv x ^ α / x))) atTop (𝓝 1) :=
    ⟨_, htail⟩
  have hconst : A3chi A1 A2 / Real.Gamma (1 / 2) = I17const A1 A2 := by
    rw [I17const_eq_A4chi A1 A2 hA2]
    rfl
  have hthr : ∀ᶠ x : ℝ in atTop, D.threshold ≤ x ^ (1 / (2 * α)) :=
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (2 * α))).eventually
      (eventually_ge_atTop D.threshold)
  have hlim : Tendsto (fun x : ℝ => (muinf (Ici x)).toReal /
      (I17const A1 A2 * (1 / Real.sqrt x))) atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ htail
    filter_upwards [hthr, eventually_gt_atTop (0 : ℝ)] with x hxthr hx
    rw [hconst, genInv_tail_factor hα D hx hxthr, one_div]
  exact hlim.comp tendsto_natCast_atTop_atTop

/-! ## 5. The model statement of (I.1.7) for `SourceModelData` -/

/-- The canonical cutoff law `P_{β_c,r}` of the model. -/
noncomputable def cutProb (M : Orchestration.SourceModelData) (r : ℝ) :
    Sym2 M.V → unitInterval :=
  bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit

/-- The canonical law `P_{β_c,∞}` of the model. -/
noncomputable def critProb (M : Orchestration.SourceModelData) : Sym2 M.V → unitInterval :=
  bernoulliEdgeProb M.kernel M.kernel_nonneg M.betaCrit

/-- **The model's tail probability is the tail of its canonical volume law**, provided
clusters are almost surely finite at criticality. Without that hypothesis the two differ
by the (a priori possibly positive) mass of the infinite-cluster event, since `toReal`
sends `⊤` to `0`. -/
theorem tailProb_eq_volumeLaw (M : Orchestration.SourceModelData)
    (hfin : ∀ᵐ ω ∂M.criticalLaw, clusterVol ω (0 : M.V) ≠ ⊤) (n : ℕ) :
    M.tailProb n = (volumeLaw (critProb M) (0 : M.V) (Ici (n : ℝ))).toReal := by
  have hset : {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      =ᵐ[M.criticalLaw] {ω : Config M.V | (n : ℝ) ≤ (clusterVol ω (0 : M.V)).toReal} := by
    filter_upwards [hfin] with ω hω
    have hiff : (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)
        ↔ (n : ℝ) ≤ (clusterVol ω (0 : M.V)).toReal := by
      rw [← ENNReal.ofReal_natCast n]
      exact ENNReal.ofReal_le_iff_le_toReal hω
    exact propext hiff
  have hmain : M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      = volumeLaw (critProb M) (0 : M.V) (Ici (n : ℝ)) := by
    rw [volumeLaw_tail_eq_tailEvent]
    have hcrit : edgeMeasure (critProb M) = M.criticalLaw := rfl
    rw [hcrit]
    simpa only [tailEvent] using measure_congr hset
  simp only [Orchestration.SourceModelData.tailProb, Measure.real, hmain]

/-- **(I.1.7) for the model.** The uncut critical cluster-volume tail of a `SourceModelData`
with `A1 = α/β_c` and `A2 = A` is asymptotically `(α/β_c)√(2/(πA))/√n`, given the
hypotheses (1)-(4) of Proposition I.3.2 (in their canonical volume-law form), the
restoration estimate (I.3.5), and almost sure finiteness of the critical cluster. -/
theorem model_tendsto_tail_I17 (M : Orchestration.SourceModelData) {A C : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hβ : 0 < (M.betaCrit : ℝ))
    (hfin : ∀ᵐ ω ∂M.criticalLaw, clusterVol ω (0 : M.V) ≠ ⊤)
    (hint1 : ∀ r, Integrable (fun x : ℝ => x) (volumeLaw (cutProb M r) (0 : M.V)))
    (hint2 : ∀ r, Integrable (fun x : ℝ => x ^ 2) (volumeLaw (cutProb M r) (0 : M.V)))
    (hEpos : ∀ r, 0 < mean (volumeLaw (cutProb M r) (0 : M.V)))
    (hSpos : ∀ r, 0 < sbMean (volumeLaw (cutProb M r) (0 : M.V)))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (volumeLaw (cutProb M r) (0 : M.V))))
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
        (sizeBiasedLaw (volumeLaw (cutProb M r) (0 : M.V)))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    (hE1 : Tendsto (fun r => mean (volumeLaw (cutProb M r) (0 : M.V))
        / (M.α / (M.betaCrit : ℝ) * r ^ M.α)) atTop (𝓝 1))
    (hψ2 : Tendsto (fun r => sbMean (volumeLaw (cutProb M r) (0 : M.V))
        / (A * r ^ (2 * M.α))) atTop (𝓝 1))
    (hI35 : ∀ᶠ r in atTop, ∀ h > 0,
      lapDefect (volumeLaw (cutProb M r) (0 : M.V)) h
          ≤ lapDefect (volumeLaw (critProb M) (0 : M.V)) h ∧
      lapDefect (volumeLaw (critProb M) (0 : M.V)) h
          ≤ lapDefect (volumeLaw (cutProb M r) (0 : M.V)) h +
            C * r ^ (-M.α) *
              (∫ x, x * Real.exp (-(h * x)) ∂(volumeLaw (cutProb M r) (0 : M.V))) *
              lapDefect (volumeLaw (critProb M) (0 : M.V)) h) :
    Tendsto (fun n : ℕ => M.tailProb n /
      (I17const (M.α / (M.betaCrit : ℝ)) A * (1 / Real.sqrt (n : ℝ)))) atTop (𝓝 1) := by
  have hmuProb : ∀ r, IsProbabilityMeasure (volumeLaw (cutProb M r) (0 : M.V)) :=
    fun r => isProbabilityMeasure_volumeLaw (cutProb M r) (0 : M.V)
  have hmain := tendsto_tail_I17_of_moments
    (mu := fun r => volumeLaw (cutProb M r) (0 : M.V))
    (muinf := volumeLaw (critProb M) (0 : M.V))
    (α := M.α) (A1 := M.α / (M.betaCrit : ℝ)) (A2 := A) (C := C)
    M.hα (div_pos M.hα hβ) hA hC hmuProb
    (fun r => volumeLaw_Iio_zero (cutProb M r) (0 : M.V))
    (volumeLaw_Iio_zero (critProb M) (0 : M.V)) hint1 hint2 hEpos hSpos hprob hconv hE1 hψ2 hI35
  refine Tendsto.congr' ?_ hmain
  filter_upwards with n
  rw [tailProb_eq_volumeLaw M hfin]


/-! ## 6. From the model's cut moments to real volume-law moments -/

/-- The model's first cut moment as an integral of the real cluster volume. -/
theorem mean_volumeLaw_eq {V : Type*} [Countable V] (π : Sym2 V → unitInterval) (o : V)
    (hne : ∫⁻ ω, clusterVol ω o ∂edgeMeasure π ≠ ⊤) :
    mean (volumeLaw π o) = (∫⁻ ω, clusterVol ω o ∂edgeMeasure π).toReal := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have hint : Integrable (fun ω : Config V => (clusterVol ω o).toReal) (edgeMeasure π) :=
    integrable_toReal_of_lintegral_ne_top (measurable_clusterVol o).aemeasurable hne
  have hnn : 0 ≤ᵐ[edgeMeasure π] fun ω : Config V => (clusterVol ω o).toReal :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have h1 : mean (volumeLaw π o) = ∫ ω, (clusterVol ω o).toReal ∂edgeMeasure π := by
    rw [mean, volumeLaw]
    simpa only [Function.comp_apply, id_eq] using integral_map hm.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) (volumeLaw π o))
  have h2 : ENNReal.ofReal (∫ ω, (clusterVol ω o).toReal ∂edgeMeasure π)
      = ∫⁻ ω, clusterVol ω o ∂edgeMeasure π := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top (measurable_clusterVol o) hne] with ω hω
    exact ENNReal.ofReal_toReal (ne_of_lt hω)
  calc mean (volumeLaw π o) = ∫ ω, (clusterVol ω o).toReal ∂edgeMeasure π := h1
    _ = (ENNReal.ofReal (∫ ω, (clusterVol ω o).toReal ∂edgeMeasure π)).toReal := by
        rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)]
    _ = (∫⁻ ω, clusterVol ω o ∂edgeMeasure π).toReal := by rw [h2]

/-- The model's second cut moment as an integral of the squared real cluster volume. -/
theorem secMoment_volumeLaw_eq {V : Type*} [Countable V] (π : Sym2 V → unitInterval) (o : V)
    (hne : ∫⁻ ω, (clusterVol ω o) ^ 2 ∂edgeMeasure π ≠ ⊤) :
    secMoment (volumeLaw π o) = (∫⁻ ω, (clusterVol ω o) ^ 2 ∂edgeMeasure π).toReal := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have hmeas2 : Measurable fun ω : Config V => (clusterVol ω o) ^ 2 :=
    (measurable_clusterVol o).pow_const 2
  have hint : Integrable (fun ω : Config V => (clusterVol ω o).toReal ^ 2) (edgeMeasure π) :=
    (integrable_toReal_of_lintegral_ne_top hmeas2.aemeasurable hne).congr
      (Filter.Eventually.of_forall fun ω => ENNReal.toReal_pow _ 2)
  have hnn : 0 ≤ᵐ[edgeMeasure π] fun ω : Config V => (clusterVol ω o).toReal ^ 2 :=
    Filter.Eventually.of_forall fun _ => by positivity
  have h1 : secMoment (volumeLaw π o)
      = ∫ ω, (clusterVol ω o).toReal ^ 2 ∂edgeMeasure π := by
    rw [secMoment, volumeLaw]
    simpa only [Function.comp_apply] using integral_map hm.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) (volumeLaw π o))
  have h2 : ENNReal.ofReal (∫ ω, (clusterVol ω o).toReal ^ 2 ∂edgeMeasure π)
      = ∫⁻ ω, (clusterVol ω o) ^ 2 ∂edgeMeasure π := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top hmeas2 hne] with ω hω
    have hω' : clusterVol ω o ≠ ⊤ := by
      intro h
      rw [h] at hω
      simp at hω
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    rw [ENNReal.ofReal_toReal hω']
  calc secMoment (volumeLaw π o) = ∫ ω, (clusterVol ω o).toReal ^ 2 ∂edgeMeasure π := h1
    _ = (ENNReal.ofReal (∫ ω, (clusterVol ω o).toReal ^ 2 ∂edgeMeasure π)).toReal := by
        rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)]
    _ = (∫⁻ ω, (clusterVol ω o) ^ 2 ∂edgeMeasure π).toReal := by rw [h2]

/-- Integrability of the identity under a canonical volume law. -/
theorem integrable_id_volumeLaw {V : Type*} [Countable V] (π : Sym2 V → unitInterval) (o : V)
    (hne : ∫⁻ ω, clusterVol ω o ∂edgeMeasure π ≠ ⊤) :
    Integrable (fun x : ℝ => x) (volumeLaw π o) := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have hint : Integrable (fun ω : Config V => (clusterVol ω o).toReal) (edgeMeasure π) :=
    integrable_toReal_of_lintegral_ne_top (measurable_clusterVol o).aemeasurable hne
  rw [volumeLaw]
  exact (integrable_map_measure (g := fun x : ℝ => x) (by fun_prop) hm.aemeasurable).mpr hint

/-- Integrability of the square under a canonical volume law. -/
theorem integrable_sq_volumeLaw {V : Type*} [Countable V] (π : Sym2 V → unitInterval) (o : V)
    (hne : ∫⁻ ω, (clusterVol ω o) ^ 2 ∂edgeMeasure π ≠ ⊤) :
    Integrable (fun x : ℝ => x ^ 2) (volumeLaw π o) := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have hmeas2 : Measurable fun ω : Config V => (clusterVol ω o) ^ 2 :=
    (measurable_clusterVol o).pow_const 2
  have hint : Integrable (fun ω : Config V => (clusterVol ω o).toReal ^ 2) (edgeMeasure π) :=
    (integrable_toReal_of_lintegral_ne_top hmeas2.aemeasurable hne).congr
      (Filter.Eventually.of_forall fun ω => ENNReal.toReal_pow _ 2)
  rw [volumeLaw]
  exact (integrable_map_measure (g := fun x : ℝ => x ^ 2) (by fun_prop) hm.aemeasurable).mpr hint

/-- **The size-biased mean from the first two ordinary moments.** For `A2 = A` and
`A1 = κ`, the hypothesis (2) of Proposition I.3.2 with `f r = r^(2α)` is implied by the
moment asymptotics at `p = 1` and `p = 2`, and the resulting constant is `A2 = A`
itself — no further rescaling by `α/β_c` enters. -/
theorem sbMean_asymptotic_of_moment_asymptotics (mu : ℝ → Measure ℝ) {α A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ)
    (h1 : Tendsto (fun r => mean (mu r) / (κ * r ^ α)) atTop (𝓝 1))
    (h2 : Tendsto (fun r => secMoment (mu r) / (A * κ * r ^ (3 * α))) atTop (𝓝 1)) :
    Tendsto (fun r => sbMean (mu r) / (A * r ^ (2 * α))) atTop (𝓝 1) := by
  have hratio : Tendsto (fun r => (secMoment (mu r) / (A * κ * r ^ (3 * α)))
      / (mean (mu r) / (κ * r ^ α))) atTop (𝓝 ((1 : ℝ) / 1)) :=
    Tendsto.div h2 h1 one_ne_zero
  rw [div_one] at hratio
  refine Tendsto.congr' ?_ hratio
  have hne : ∀ᶠ r in atTop, mean (mu r) ≠ 0 := by
    have h := h1.eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
    filter_upwards [h] with r hr hc
    rw [hc] at hr
    simp at hr
  filter_upwards [hne, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  rw [sbMean]
  have h3 : r ^ (3 * α) = r ^ α * r ^ (2 * α) := by
    rw [show (3 : ℝ) * α = α + 2 * α by ring, Real.rpow_add hr0]
  have hα0 : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hr0 α).ne'
  have h2α0 : r ^ (2 * α) ≠ 0 := (Real.rpow_pos_of_pos hr0 (2 * α)).ne'
  rw [h3]
  field_simp

/-! ## 7. (I.1.7) from the model's moment asymptotics at `p = 1, 2` -/

/-- `I16rhs` at `p = 1` is the first-moment normaliser `(α/β_c) r^α`. -/
theorem I16rhs_one_model (M : Orchestration.SourceModelData) (A r : ℝ) :
    Orchestration.I16rhs M A 1 r = (M.α / (M.betaCrit : ℝ)) * r ^ M.α := by
  simp only [Orchestration.I16rhs]
  rw [show (2 * ((1 : ℕ) : ℝ) - 1) * M.α = M.α by norm_num]
  simp [VolumeMoments.M]

/-- `I16rhs` at `p = 2` is the second-moment normaliser `A (α/β_c) r^(3α)`. -/
theorem I16rhs_two_model (M : Orchestration.SourceModelData) (A r : ℝ) :
    Orchestration.I16rhs M A 2 r = A * (M.α / (M.betaCrit : ℝ)) * r ^ (3 * M.α) := by
  simp only [Orchestration.I16rhs]
  rw [show (2 * ((2 : ℕ) : ℝ) - 1) * M.α = 3 * M.α by norm_num]
  simp [VolumeMoments.M]

/-- **(I.1.7) from (I.1.6)(a) at `p = 1, 2`.** The model's uncut critical cluster-volume
tail is `(α/β_c)√(2/(πA))/√n` given the first- and second-moment asymptotics of the
cut-off cluster volume with the exact normalisations of (I.1.6), the weak convergence of
the normalised size-biased laws to the chi-square law with one degree of freedom, the
restoration estimate (I.3.5), finiteness of the first two cut moments, `β_c > 0`, and
almost sure finiteness of the critical cluster. -/
theorem model_tail_from_cutMoment (M : Orchestration.SourceModelData) {A C : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hβ : 0 < (M.betaCrit : ℝ))
    (hfin : ∀ᵐ ω ∂M.criticalLaw, clusterVol ω (0 : M.V) ≠ ⊤)
    (h1ne : ∀ r, M.cutMoment 1 r ≠ ⊤) (h2ne : ∀ r, M.cutMoment 2 r ≠ ⊤)
    (hEpos : ∀ r, 0 < mean (volumeLaw (cutProb M r) (0 : M.V)))
    (hSpos : ∀ r, 0 < sbMean (volumeLaw (cutProb M r) (0 : M.V)))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (volumeLaw (cutProb M r) (0 : M.V))))
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure
        (sizeBiasedLaw (volumeLaw (cutProb M r) (0 : M.V)))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    (hE1 : Tendsto (fun r => (M.cutMoment 1 r).toReal
        / Orchestration.I16rhs M A 1 r) atTop (𝓝 1))
    (hE2 : Tendsto (fun r => (M.cutMoment 2 r).toReal
        / Orchestration.I16rhs M A 2 r) atTop (𝓝 1))
    (hI35 : ∀ᶠ r in atTop, ∀ h > 0,
      lapDefect (volumeLaw (cutProb M r) (0 : M.V)) h
          ≤ lapDefect (volumeLaw (critProb M) (0 : M.V)) h ∧
      lapDefect (volumeLaw (critProb M) (0 : M.V)) h
          ≤ lapDefect (volumeLaw (cutProb M r) (0 : M.V)) h +
            C * r ^ (-M.α) *
              (∫ x, x * Real.exp (-(h * x)) ∂(volumeLaw (cutProb M r) (0 : M.V))) *
              lapDefect (volumeLaw (critProb M) (0 : M.V)) h) :
    Tendsto (fun n : ℕ => M.tailProb n /
      (I17const (M.α / (M.betaCrit : ℝ)) A * (1 / Real.sqrt (n : ℝ)))) atTop (𝓝 1) := by
  have hκ : 0 < M.α / (M.betaCrit : ℝ) := div_pos M.hα hβ
  have hratio : ∀ r, M.cutMoment 1 r
      = ∫⁻ ω, clusterVol ω (0 : M.V) ∂edgeMeasure (cutProb M r) := by
    intro r
    simp only [Orchestration.SourceModelData.cutMoment, pow_one,
      Orchestration.SourceModelData.cutLaw, longRangeMeasure, cutProb]
  have hratio2 : ∀ r,
      M.cutMoment 2 r = ∫⁻ ω, (clusterVol ω (0 : M.V)) ^ 2 ∂edgeMeasure (cutProb M r) := by
    intro r
    simp only [Orchestration.SourceModelData.cutMoment,
      Orchestration.SourceModelData.cutLaw, longRangeMeasure, cutProb]
  have hE1' : Tendsto (fun r => mean (volumeLaw (cutProb M r) (0 : M.V))
      / (M.α / (M.betaCrit : ℝ) * r ^ M.α)) atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ hE1
    filter_upwards with r
    rw [I16rhs_one_model, hratio r,
      ← mean_volumeLaw_eq (cutProb M r) (0 : M.V) (by rw [← hratio r]; exact h1ne r)]
  have hE2' : Tendsto (fun r => secMoment (volumeLaw (cutProb M r) (0 : M.V))
      / (A * (M.α / (M.betaCrit : ℝ)) * r ^ (3 * M.α))) atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ hE2
    filter_upwards with r
    rw [I16rhs_two_model, hratio2 r,
      ← secMoment_volumeLaw_eq (cutProb M r) (0 : M.V) (by rw [← hratio2 r]; exact h2ne r)]
  have hψ2 := sbMean_asymptotic_of_moment_asymptotics
    (fun r => volumeLaw (cutProb M r) (0 : M.V)) hA hκ hE1' hE2'
  exact model_tendsto_tail_I17 M hA hC hβ hfin
    (fun r => integrable_id_volumeLaw (cutProb M r) (0 : M.V)
      (by rw [← hratio r]; exact h1ne r))
    (fun r => integrable_sq_volumeLaw (cutProb M r) (0 : M.V)
      (by rw [← hratio2 r]; exact h2ne r))
    hEpos hSpos hprob hconv hE1' hψ2 hI35

end I17

end PercLib.CriticalLRP

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.I17.tendsto_A3cand_two_Qinf
#print axioms PercLib.CriticalLRP.I17.genInv_rpow_eq
#print axioms PercLib.CriticalLRP.I17.genInv_tail_factor
#print axioms PercLib.CriticalLRP.I17.I17const_eq_A4chi
#print axioms PercLib.CriticalLRP.I17.Qinf_Iio_zero
#print axioms PercLib.CriticalLRP.I17.regularlyVaryingAtTop_rpow
#print axioms PercLib.CriticalLRP.I17.tendsto_tail_I17_of_moments
#print axioms PercLib.CriticalLRP.I17.tailProb_eq_volumeLaw
#print axioms PercLib.CriticalLRP.I17.model_tendsto_tail_I17
#print axioms PercLib.CriticalLRP.I17.mean_volumeLaw_eq
#print axioms PercLib.CriticalLRP.I17.secMoment_volumeLaw_eq
#print axioms PercLib.CriticalLRP.I17.integrable_id_volumeLaw
#print axioms PercLib.CriticalLRP.I17.integrable_sq_volumeLaw
#print axioms PercLib.CriticalLRP.I17.sbMean_asymptotic_of_moment_asymptotics
#print axioms PercLib.CriticalLRP.I17.I16rhs_one_model
#print axioms PercLib.CriticalLRP.I17.I16rhs_two_model
#print axioms PercLib.CriticalLRP.I17.model_tail_from_cutMoment
#print PercLib.CriticalLRP.I17.model_tail_from_cutMoment

#print PercLib.CriticalLRP.I17.model_tendsto_tail_I17
