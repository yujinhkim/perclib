/-
# The `hconv` input of the (I.1.7) chain from the all-order moment asymptotics (I.1.6)

Integrated after independent review from `.ultramath/smwzvo8ss/m1/AllOrderMomentsHconv.lean`.
Production integration follows `c6051892f9793d851027bc4575a9a57f285f6c24`; the theorem
statements and proof bodies are unchanged.

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1).

Theorem I.1.6 supplies, for every integer `p ≥ 1`, the first-order asymptotic

  `E_{β_c,r} |K|^p ∼ (2p-3)!! A^{p-1} (α/β_c) r^{(2p-1)α}`   as `r → ∞`     (I.1.6)

and Remark I.1.7 explains that the factor `(2p-3)!!` "encodes the fact that the size-biased
distribution of `|K|` under `P_{β_c,r}`, normalized to have mean `1`, converges to a chi-squared
distribution with one degree of freedom". The production interface
`PercLib.CriticalLRP.Analysis.ClusterVolumeTail.I17` takes that convergence as the hypothesis
`hconv`; the present file derives it from (I.1.6).

The two steps are exactly the ones the task distinguishes.

* **Size-biased numerators and the index shift.** The `k`-th moment of the normalized size-biased
  law `sizeBiasedLaw (mu r)` of a cluster-volume law `mu r` is
  `E|K|^{k+1} / (E|K| · (E|K|²/E|K|)^k)`
  (`integral_pow_sizeBiasedLaw`): the numerator is the `(k+1)`-st ordinary moment, i.e. the index
  shift `p = k+1` of (I.1.6), and the denominator carries the size-biased mean
  `Ehat|K| = E|K|²/E|K|` to the power `k`.
* **Cancellation of the `r`-powers.** Substituting (I.1.6) at `p = k+1`, `p = 1` and `p = 2` gives
  `r^{(2k+1)α} / (r^α · (r^{2α})^k) = 1` and `A^k (α/β_c) / ((α/β_c) A^k) = 1`, so the `k`-th
  size-biased moment tends to `(2k-1)!! = oddFact k`, the `k`-th moment of the chi-square law with
  one degree of freedom.
* The moment method of `PercLib.CriticalLRP.Analysis.MomentToChiSquare` (verified, not wrapped:
  the hypotheses on support, probability, positivity and finite integrability are discharged here
  from the cluster-volume data) then yields `hconv`.

Nothing in the paper's per-radius hypotheses is assumed opaquely: the single moment schema
`I16` is (I.1.6), and `mean ∼ (α/β_c) r^α`, `Ehat|K| ∼ A r^{2α}` (the `hE1`, `hψ2` of the I.1.7
interface) are *derived* from it. What remains explicit is only what the model must supply: that
the truncated cluster-volume laws are probability laws carried by `[0,∞)` with finite moments of
every order and positive first moment.
-/
module

public import PercLib.CriticalLRP.Analysis.ClusterVolumeTail.I17
public import PercLib.CriticalLRP.Analysis.MomentToChiSquare.QinfAdapter
public import PercLib.CriticalLRP.Analysis.SizeBiasedMGF

/-! The main results are `tendsto_mean_of_I16`, `tendsto_sbMean_of_I16`,
`tendsto_integral_pow_sizeBiasedLaw_of_I16` and `tendsto_sizeBiasedLaw_Qinf_of_I16`; the last is
the `hconv` hypothesis of `Analysis/ClusterVolumeTail/I17`. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

open PercLib.CriticalLRP.Analysis.I32
open PercLib.CriticalLRP.MomentProblem (oddFact)

namespace SwarmM1

/-! ## 1. The moments of the normalized size-biased law -/

/-- **The `k`-th moment of the normalized size-biased law** is the `(k+1)`-st ordinary moment
divided by `E|K| · (Ehat|K|)^k`. This is the index shift `p = k+1` of (I.1.6) in the numerator
and the size-biased mean `Ehat|K| = E|K|²/E|K|` in the denominator. -/
theorem integral_pow_sizeBiasedLaw {mu : Measure ℝ} (k : ℕ) (hmu : mu (Iio 0) = 0)
    (hM : 0 < mean mu) (hS : 0 < sbMean mu) :
    ∫ y, y ^ k ∂(sizeBiasedLaw mu)
      = (∫ x, x ^ (k + 1) ∂mu) / (mean mu * sbMean mu ^ k) := by
  have htr := integral_sizeBiasedLaw hmu hM (fun y : ℝ => y ^ k) (by fun_prop)
  have hpw : ∀ x : ℝ, x * (x / sbMean mu) ^ k = x ^ (k + 1) / sbMean mu ^ k := by
    intro x
    rw [div_pow, pow_succ]
    field_simp
  simp only [hpw] at htr
  rw [htr, integral_div]
  have hsp : sbMean mu ^ k ≠ 0 := pow_ne_zero k hS.ne'
  field_simp

/-- The `k`-th power is integrable under the normalized size-biased law as soon as the
`(k+1)`-st ordinary moment is finite. -/
theorem integrable_pow_sizeBiasedLaw {mu : Measure ℝ} (k : ℕ) (hmu : mu (Iio 0) = 0)
    (hM : 0 < mean mu) (hS : 0 < sbMean mu)
    (hint : Integrable (fun x : ℝ => x ^ (k + 1)) mu) :
    Integrable (fun y : ℝ => y ^ k) (sizeBiasedLaw mu) := by
  have hφ : AEMeasurable (fun x : ℝ => x / sbMean mu)
      (mu.withDensity fun x => ENNReal.ofReal (x / mean mu)) :=
    (by fun_prop : Measurable fun x : ℝ => x / sbMean mu).aemeasurable
  have hmap : Integrable (fun y : ℝ => y ^ k)
      ((mu.withDensity fun x => ENNReal.ofReal (x / mean mu)).map fun x => x / sbMean mu) ↔
      Integrable ((fun y : ℝ => y ^ k) ∘ fun x : ℝ => x / sbMean mu)
        (mu.withDensity fun x => ENNReal.ofReal (x / mean mu)) :=
    integrable_map_measure (by fun_prop) hφ
  rw [sizeBiasedLaw, hmap, integrable_withDensity_iff (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hbd : Integrable (fun x : ℝ => (1 / (sbMean mu ^ k * mean mu)) * x ^ (k + 1)) mu :=
    hint.const_mul _
  refine hbd.mono' (by fun_prop) ?_
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hmu] with x hx
  simp only [mem_compl_iff, mem_Iio, not_lt] at hx
  rw [Function.comp_apply, ENNReal.toReal_ofReal (div_nonneg hx hM.le)]
  have hsp : sbMean mu ^ k * mean mu ≠ 0 :=
    mul_ne_zero (pow_ne_zero k hS.ne') hM.ne'
  have hid : (x / sbMean mu) ^ k * (x / mean mu)
      = x ^ (k + 1) / (sbMean mu ^ k * mean mu)
      ∧ (1 / (sbMean mu ^ k * mean mu)) * x ^ (k + 1)
        = x ^ (k + 1) / (sbMean mu ^ k * mean mu) := by
    constructor
    · rw [div_pow]
      field_simp
      ring
    · field_simp
  rw [hid.1, hid.2]
  exact le_of_eq (abs_of_nonneg (by positivity))

/-- The normalized size-biased law as a **probability measure**, with the probability obligation
discharged from the cluster-volume data rather than assumed. -/
noncomputable def sbProb (mu : Measure ℝ) [IsProbabilityMeasure mu] (hmu : mu (Iio 0) = 0)
    (hint : Integrable (fun x : ℝ => x) mu) (hpos : 0 < mean mu) : ProbabilityMeasure ℝ :=
  ⟨sizeBiasedLaw mu, isProbabilityMeasure_sizeBiasedLaw mu hmu hint hpos⟩

/-- `sbProb` is the raw measure `sizeBiasedLaw mu`; in particular it agrees with
`Measure.toProbabilityMeasure (sizeBiasedLaw mu)` whenever that is well formed. -/
theorem sbProb_coe {mu : Measure ℝ} [IsProbabilityMeasure mu] (hmu : mu (Iio 0) = 0)
    (hint : Integrable (fun x : ℝ => x) mu) (hpos : 0 < mean mu) :
    (sbProb mu hmu hint hpos : Measure ℝ) = sizeBiasedLaw mu := rfl

/-! ## 2. The `r`-powers in (I.1.6) -/

/-- `r^{(2k+1)α} = r^α · (r^{2α})^k` for `r > 0`. -/
theorem rpow_two_mul_add_one_mul {r α : ℝ} (hr : 0 < r) (k : ℕ) :
    r ^ (((2 * k + 1 : ℕ) : ℝ) * α) = r ^ α * (r ^ (2 * α)) ^ k := by
  have h1 : (((2 * k + 1 : ℕ) : ℝ) * α) = α + (k : ℝ) * (2 * α) := by
    push_cast
    ring
  rw [h1, Real.rpow_add hr]
  congr 1
  rw [show (k : ℝ) * (2 * α) = (2 * α) * (k : ℝ) by ring, Real.rpow_mul hr.le,
    Real.rpow_natCast]

/-! ## 3. The moment schema (I.1.6) -/

/-- **The all-order moment asymptotics (I.1.6)**, indexed by `k = p - 1` so that both the power
`p = k + 1` and the exponent `(2p-1)α = (2k+1)α` are visible:

`E|K|^{k+1} ∼ (2k-1)!! A^k (α/β_c) r^{(2k+1)α}` as `r → ∞`, for every `k`.

Here `c` is the paper's `α/β_c` and `A` the non-universal constant of Theorem I.1.6. -/
def I16 (mu : ℝ → Measure ℝ) (A c α : ℝ) : Prop :=
  ∀ k : ℕ, Tendsto (fun r : ℝ => (∫ x, x ^ (k + 1) ∂(mu r)) /
      ((oddFact k : ℝ) * A ^ k * c * r ^ (((2 * k + 1 : ℕ) : ℝ) * α))) atTop (𝓝 1)

/-- `oddFact k > 0` for every `k`, so its image in `ℝ` is nonzero. -/
theorem oddFact_pos (k : ℕ) : 0 < oddFact k := by
  unfold oddFact
  exact Finset.prod_pos fun i _ => by omega

theorem oddFact_cast_ne_zero (k : ℕ) : (oddFact k : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (oddFact_pos k).ne'

/-- The `p = 1` case of (I.1.6): `E|K| ∼ (α/β_c) r^α`. -/
theorem tendsto_mean_of_I16 {mu : ℝ → Measure ℝ} {A c α : ℝ} (h : I16 mu A c α) :
    Tendsto (fun r : ℝ => mean (mu r) / (c * r ^ α)) atTop (𝓝 1) := by
  have h0 := h 0
  simpa [mean] using h0

/-- The `p = 2` case of (I.1.6): `E|K|² ∼ A (α/β_c) r^{3α}`. -/
theorem tendsto_secMoment_of_I16 {mu : ℝ → Measure ℝ} {A c α : ℝ} (h : I16 mu A c α) :
    Tendsto (fun r : ℝ => secMoment (mu r) / (A * c * r ^ (3 * α))) atTop (𝓝 1) := by
  have h1 := h 1
  have ho1 : oddFact 1 = 1 := by simp [oddFact]
  simp only [ho1, Nat.cast_one, one_mul, pow_one] at h1
  exact h1

/-- **The size-biased mean** `Ehat|K| = E|K|²/E|K| ∼ A r^{2α}`: the quotient of (I.1.6) at `p = 2`
by (I.1.6) at `p = 1`. This is the hypothesis `hψ2` of `Analysis/ClusterVolumeTail/I17`, here
*derived* from (I.1.6) given the strict positivity of the first moment. -/
theorem tendsto_sbMean_of_I16 {mu : ℝ → Measure ℝ} {A c α : ℝ} (h : I16 mu A c α)
    (hA : 0 < A) (hc : 0 < c) (hMpos : ∀ r, 0 < mean (mu r)) :
    Tendsto (fun r : ℝ => sbMean (mu r) / (A * r ^ (2 * α))) atTop (𝓝 1) := by
  have hM := tendsto_mean_of_I16 h
  have hsec := tendsto_secMoment_of_I16 (A := A) (c := c) (α := α) h
  have hratio : Tendsto
      (fun r : ℝ => (secMoment (mu r) / (A * c * r ^ (3 * α))) / (mean (mu r) / (c * r ^ α)))
      atTop (𝓝 (1 / 1)) := hsec.div hM one_ne_zero
  have hone : (1 : ℝ) / 1 = 1 := by norm_num
  rw [hone] at hratio
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hrα : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hr α).ne'
  have hr3α : r ^ (3 * α) ≠ 0 := (Real.rpow_pos_of_pos hr (3 * α)).ne'
  have hr2α : r ^ (2 * α) ≠ 0 := (Real.rpow_pos_of_pos hr (2 * α)).ne'
  have hM0 : mean (mu r) ≠ 0 := (hMpos r).ne'
  have hA0 : A ≠ 0 := hA.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have hrpow : r ^ α * r ^ (α * 2) = r ^ (3 * α) := by
    rw [← Real.rpow_add hr, show α + α * 2 = 3 * α by ring]
  simp only [sbMean]
  field_simp
  calc secMoment (mu r) * r ^ α * r ^ (α * 2)
      = secMoment (mu r) * (r ^ α * r ^ (α * 2)) := by ring
    _ = secMoment (mu r) * r ^ (3 * α) := by rw [hrpow]

/-! ## 4. The size-biased moments tend to `(2k-1)!!` -/

/-- The algebraic identity behind the cancellation of the `r`-powers: the `(k+1)`-st ordinary
moment over `E|K| · (Ehat|K|)^k` is the product of the three (I.1.6) ratios and the factor
`(2k-1)!!`. The identity `r^{(2k+1)α} = r^α (r^{2α})^k` of section 2 is what makes the `r`-powers
cancel. -/
theorem sbMoment_eq (k : ℕ) {A c α N M S r : ℝ} (hA : A ≠ 0) (hc : c ≠ 0) (hr : 0 < r)
    (hM : M ≠ 0) (hS : S ≠ 0) :
    N / (M * S ^ k)
      = (N / ((oddFact k : ℝ) * A ^ k * c * r ^ (((2 * k + 1 : ℕ) : ℝ) * α)))
        * (c * r ^ α / M) * (A * r ^ (2 * α) / S) ^ k * (oddFact k : ℝ) := by
  have hof : (oddFact k : ℝ) ≠ 0 := oddFact_cast_ne_zero k
  have hrα : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hr α).ne'
  have hr2α : r ^ (2 * α) ≠ 0 := (Real.rpow_pos_of_pos hr (2 * α)).ne'
  rw [rpow_two_mul_add_one_mul hr k, div_pow, mul_pow]
  field_simp

/-- **The `k`-th moment of the normalized size-biased law tends to `(2k-1)!!`.** Substituting
(I.1.6) at `p = k+1`, `p = 1` and `p = 2`, the `r`-powers cancel and the `(α/β_c)` and `A`
constants cancel, leaving `(2k-1)!! = oddFact k`, the `k`-th moment of the chi-square law with one
degree of freedom. -/
theorem tendsto_integral_pow_sizeBiasedLaw_of_I16 {mu : ℝ → Measure ℝ} {A c α : ℝ}
    (h : I16 mu A c α) (hA : 0 < A) (hc : 0 < c)
    (hmu : ∀ r, (mu r) (Iio 0) = 0) (hMpos : ∀ r, 0 < mean (mu r))
    (hSpos : ∀ r, 0 < sbMean (mu r)) (k : ℕ) :
    Tendsto (fun r : ℝ => ∫ y, y ^ k ∂(sizeBiasedLaw (mu r))) atTop
      (𝓝 ((oddFact k : ℝ))) := by
  have hu : Tendsto (fun r : ℝ => (∫ x, x ^ (k + 1) ∂(mu r)) /
      ((oddFact k : ℝ) * A ^ k * c * r ^ (((2 * k + 1 : ℕ) : ℝ) * α))) atTop (𝓝 1) := h k
  have hv : Tendsto (fun r : ℝ => c * r ^ α / mean (mu r)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun r : ℝ => (mean (mu r) / (c * r ^ α))⁻¹) atTop (𝓝 (1 : ℝ)) := by
      have h' := (tendsto_mean_of_I16 h).inv₀ (one_ne_zero)
      simpa using h'
    refine Tendsto.congr' ?_ hinv
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hrα : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hr α).ne'
    have hM0 : mean (mu r) ≠ 0 := (hMpos r).ne'
    have hc0 : c ≠ 0 := hc.ne'
    field_simp
  have hw : Tendsto (fun r : ℝ => A * r ^ (2 * α) / sbMean (mu r)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun r : ℝ => (sbMean (mu r) / (A * r ^ (2 * α)))⁻¹) atTop (𝓝 (1 : ℝ)) := by
      have h' := (tendsto_sbMean_of_I16 h hA hc hMpos).inv₀ (one_ne_zero)
      simpa using h'
    refine Tendsto.congr' ?_ hinv
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hr2α : r ^ (2 * α) ≠ 0 := (Real.rpow_pos_of_pos hr (2 * α)).ne'
    have hA0 : A ≠ 0 := hA.ne'
    have hS0 : sbMean (mu r) ≠ 0 := (hSpos r).ne'
    field_simp
  have hprod : Tendsto (fun r : ℝ =>
      ((∫ x, x ^ (k + 1) ∂(mu r)) /
          ((oddFact k : ℝ) * A ^ k * c * r ^ (((2 * k + 1 : ℕ) : ℝ) * α)))
        * (c * r ^ α / mean (mu r)) * (A * r ^ (2 * α) / sbMean (mu r)) ^ k * (oddFact k : ℝ))
      atTop (𝓝 ((oddFact k : ℝ))) := by
    have h1 : Tendsto (fun r : ℝ =>
        ((∫ x, x ^ (k + 1) ∂(mu r)) /
            ((oddFact k : ℝ) * A ^ k * c * r ^ (((2 * k + 1 : ℕ) : ℝ) * α)))
          * (c * r ^ α / mean (mu r)) * (A * r ^ (2 * α) / sbMean (mu r)) ^ k * (oddFact k : ℝ))
        atTop (𝓝 (1 * 1 * 1 ^ k * (oddFact k : ℝ))) :=
      ((hu.mul hv).mul (hw.pow k)).mul tendsto_const_nhds
    simpa using h1
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [integral_pow_sizeBiasedLaw k (hmu r) (hMpos r) (hSpos r)]
  exact (sbMoment_eq k hA.ne' hc.ne' hr (hMpos r).ne' (hSpos r).ne').symm

/-! ## 5. The `hconv` hypothesis of the (I.1.7) chain -/

/-- **(I.1.6) implies the weak convergence `hconv` of `Analysis/ClusterVolumeTail/I17`.**

Let `mu r` be the cut-off cluster-volume law `P_{β_c,r}(|K| ∈ ·)`, a probability law carried by
`[0,∞)` with finite moments of every order and positive first moment. If the moments satisfy
(I.1.6) in the form `I16 mu A c α`, then the normalized size-biased laws converge weakly to `Q∞`,
the law of `Z²` for a standard normal `Z` — exactly the hypothesis `hconv` taken as input by
`tendsto_tail_I17_of_moments` and `model_tendsto_tail_I17`.

Every other hypothesis of the moment-to-weak-convergence step is discharged from the data:
the size-biased law is a probability measure (`isProbabilityMeasure_sizeBiasedLaw`), it is carried
by `[0,∞)` (`sizeBiasedLaw_Iio_zero`), and all its moments are finite
(`integrable_pow_sizeBiasedLaw`). -/
theorem tendsto_sizeBiasedLaw_Qinf_of_I16 {mu : ℝ → Measure ℝ}
    [inst : ∀ r, IsProbabilityMeasure (mu r)] {A c α : ℝ}
    (h : I16 mu A c α) (hA : 0 < A) (hc : 0 < c)
    (hmu : ∀ r, (mu r) (Iio 0) = 0)
    (hint : ∀ (r : ℝ) (k : ℕ), Integrable (fun x : ℝ => x ^ k) (mu r))
    (hMpos : ∀ r, 0 < mean (mu r)) (hSpos : ∀ r, 0 < sbMean (mu r)) :
    Tendsto (fun r : ℝ => sbProb (mu r) (hmu r) (by simpa only [pow_one] using hint r 1)
        (hMpos r)) atTop
      (𝓝 (Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf)) := by
  exact @SwarmM4.tendsto_toProbabilityMeasure_Qinf (fun r : ℝ => sizeBiasedLaw (mu r))
    (fun r => (sbProb (mu r) (hmu r) (by simpa only [pow_one] using hint r 1) (hMpos r)).2)
    (fun r => sizeBiasedLaw_Iio_zero (hmu r) (hSpos r))
    (fun r k => integrable_pow_sizeBiasedLaw k (hmu r) (hMpos r) (hSpos r) (hint r (k + 1)))
    (fun k => tendsto_integral_pow_sizeBiasedLaw_of_I16 h hA hc hmu hMpos hSpos k)

end SwarmM1

/-! ## 6. The model: canonical cut-off volume laws

Here the cluster-volume data of Section 5 is instantiated at the level of a
`SourceModelData`: the laws `mu r` are the canonical cut-off volume laws
`volumeLaw (cutProb M r) 0`, and the hypotheses of Section 5 are discharged from the cluster
variable `clusterVol ω 0`.
-/

namespace SwarmM1

section Model

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I17

variable {V : Type*} [Countable V]

/-- **All powers of the cluster volume are integrable under the volume law**, from finiteness of
the `p`-th `lintegral` of `clusterVol`. This generalises the production `integrable_id_volumeLaw`
and `integrable_sq_volumeLaw` to every exponent, which is what the moment method needs. -/
theorem integrable_pow_volumeLaw (π : Sym2 V → unitInterval) (o : V) (p : ℕ)
    (hne : ∫⁻ ω, (clusterVol ω o) ^ p ∂(edgeMeasure π) ≠ ⊤) :
    Integrable (fun x : ℝ => x ^ p) (volumeLaw π o) := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have hmeas : Measurable fun ω : Config V => (clusterVol ω o) ^ p :=
    (measurable_clusterVol o).pow_const p
  have hint : Integrable (fun ω : Config V => (clusterVol ω o).toReal ^ p) (edgeMeasure π) :=
    (integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hne).congr
      (Filter.Eventually.of_forall fun ω => ENNReal.toReal_pow _ p)
  rw [volumeLaw]
  exact (integrable_map_measure (by fun_prop) hm.aemeasurable).mpr hint

/-- **The first volume moment is at least one**: the cluster always contains the root, so
`|K| ≥ 1`, and `∫⁻ |K| ≥ 1`. (This is the formal content of `E|K| ≥ 1 > 0`.) -/
theorem one_le_mean_volumeLaw (π : Sym2 V → unitInterval) (o : V)
    (hne : ∫⁻ ω, clusterVol ω o ∂(edgeMeasure π) ≠ ⊤) :
    1 ≤ mean (volumeLaw π o) := by
  rw [PercLib.CriticalLRP.I17.mean_volumeLaw_eq π o hne]
  have h1 : (1 : ℝ≥0∞) ≤ ∫⁻ ω, clusterVol ω o ∂(edgeMeasure π) := by
    calc (1 : ℝ≥0∞) = ∫⁻ _ω, (1 : ℝ≥0∞) ∂(edgeMeasure π) := by simp
      _ ≤ ∫⁻ ω, clusterVol ω o ∂(edgeMeasure π) := by
        refine lintegral_mono fun ω => ?_
        change (1 : ℝ≥0∞) ≤ clusterVol ω o
        rw [clusterVol_eq_encard]
        have h1 : (1 : ℕ∞) ≤ (cluster ω o).encard :=
          Set.one_le_encard_iff_nonempty.mpr ⟨o, cluster_mem_self ω o⟩
        exact_mod_cast h1
  calc (1 : ℝ) = (1 : ℝ≥0∞).toReal := by simp
    _ ≤ (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)).toReal := ENNReal.toReal_mono hne h1

/-- **The second volume moment exceeds the first**, from the pointwise inequality
`x² ≥ x - 1/4`. This replaces any support or finiteness input: it is the variance identity
`E[X²] - E[X]² ≥ 0` in the form needed to keep the second moment strictly positive. -/
theorem sub_quarter_le_secMoment_volumeLaw (π : Sym2 V → unitInterval) (o : V)
    (hint1 : Integrable (fun x : ℝ => x) (volumeLaw π o))
    (hint2 : Integrable (fun x : ℝ => x ^ 2) (volumeLaw π o)) :
    mean (volumeLaw π o) - 1 / 4 ≤ secMoment (volumeLaw π o) := by
  have hsq : 0 ≤ ∫ x, (x - 1 / 2) ^ 2 ∂(volumeLaw π o) :=
    integral_nonneg fun x => by positivity
  have hsub : (fun x : ℝ => (x - 1 / 2) ^ 2) = fun x => x ^ 2 - x + 1 / 4 := by
    funext x; ring
  rw [hsub] at hsq
  have h1 : ∫ x, (x ^ 2 - x + 1 / 4) ∂(volumeLaw π o)
      = ∫ x, (x ^ 2 - x) ∂(volumeLaw π o) + ∫ x, (1 / 4 : ℝ) ∂(volumeLaw π o) :=
    integral_add (hint2.sub hint1) (integrable_const (1 / 4))
  have h2 : ∫ x, (x ^ 2 - x) ∂(volumeLaw π o)
      = ∫ x, x ^ 2 ∂(volumeLaw π o) - ∫ x, x ∂(volumeLaw π o) := integral_sub hint2 hint1
  have h3 : ∫ x, (1 / 4 : ℝ) ∂(volumeLaw π o) = 1 / 4 := by
    rw [integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have hsplit : ∫ x, (x ^ 2 - x + 1 / 4) ∂(volumeLaw π o)
      = secMoment (volumeLaw π o) - mean (volumeLaw π o) + 1 / 4 := by
    rw [h1, h2, h3]
    simp only [mean, secMoment]
  rw [hsplit] at hsq
  linarith

/-- **The size-biased mean is strictly positive** for a cluster-volume law: `Ehat|K| ≥ 3/(4 E|K|)`.
Hence the normalisation in `sizeBiasedLaw` is genuine. -/
theorem sbMean_pos_volumeLaw (π : Sym2 V → unitInterval) (o : V)
    (hint1 : Integrable (fun x : ℝ => x) (volumeLaw π o))
    (hint2 : Integrable (fun x : ℝ => x ^ 2) (volumeLaw π o))
    (h1 : 1 ≤ mean (volumeLaw π o)) : 0 < sbMean (volumeLaw π o) := by
  have hq := sub_quarter_le_secMoment_volumeLaw π o hint1 hint2
  have hpos : 0 < secMoment (volumeLaw π o) := by linarith
  have hmean : 0 < mean (volumeLaw π o) := by linarith
  rw [sbMean]
  exact div_pos hpos hmean

end Model

end SwarmM1

namespace SwarmM1

section ModelInstantiation

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I17
open scoped Topology ENNReal NNReal

variable (M : PercLib.CriticalLRP.Orchestration.SourceModelData)

/-- Finiteness of all cluster moments under the cut-off law, in the `lintegral` form used by the
cluster-volume integrability lemmas. This is the model's content of "(I.1.6) is a finite number". -/
abbrev MomentFinite : Prop :=
  ∀ (r : ℝ) (p : ℕ), ∫⁻ ω, (clusterVol ω (0 : M.V)) ^ p ∂(edgeMeasure (cutProb M r)) ≠ ⊤

/-- **The normalized size-biased cut-off volume law as a probability measure.** This is the paper's
`Q_r` of the proof of (I.1.7): `sizeBiasedLaw (mu r)` with the probability obligation discharged. -/
noncomputable def modelSB (hnePow : MomentFinite M) (r : ℝ) : ProbabilityMeasure ℝ :=
  sbProb (volumeLaw (cutProb M r) (0 : M.V)) (volumeLaw_Iio_zero _ _)
    (by
      simpa only [pow_one] using
        integrable_pow_volumeLaw (cutProb M r) (0 : M.V) 1 (hnePow r 1))
    (by
      have h1 : 1 ≤ mean (volumeLaw (cutProb M r) (0 : M.V)) :=
        one_le_mean_volumeLaw (cutProb M r) (0 : M.V) (by
          simpa only [pow_one] using hnePow r 1)
      linarith)

theorem modelSB_coe (hnePow : MomentFinite M) (r : ℝ) :
    (modelSB M hnePow r : Measure ℝ) = sizeBiasedLaw (volumeLaw (cutProb M r) (0 : M.V)) := rfl

/-- The probability obligation for the cut-off size-biased laws. -/
theorem modelSB_isProbabilityMeasure (hnePow : MomentFinite M) (r : ℝ) :
    IsProbabilityMeasure (sizeBiasedLaw (volumeLaw (cutProb M r) (0 : M.V))) :=
  (modelSB M hnePow r).2

/-- `hconv` of the (I.1.7) chain at the model level: **(I.1.6) implies that the normalized
size-biased cut-off volume laws converge weakly to `Q∞`**, the law of `Z²` for standard normal
`Z`. -/
theorem model_tendsto_Qinf_of_I16 {A : ℝ} (hA : 0 < A) (hβ : 0 < (M.betaCrit : ℝ))
    (hnePow : MomentFinite M)
    (h : I16 (fun r : ℝ => volumeLaw (cutProb M r) (0 : M.V)) A
      (M.α / (M.betaCrit : ℝ)) M.α) :
    Tendsto (modelSB M hnePow) atTop
      (𝓝 (Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf)) := by
  have hc : 0 < M.α / (M.betaCrit : ℝ) := div_pos M.hα hβ
  have hEpos : ∀ r : ℝ, 0 < mean (volumeLaw (cutProb M r) (0 : M.V)) := fun r => by
    have h1 := one_le_mean_volumeLaw (cutProb M r) (0 : M.V) (by
      simpa only [pow_one] using hnePow r 1)
    linarith
  have hSpos : ∀ r : ℝ, 0 < sbMean (volumeLaw (cutProb M r) (0 : M.V)) := fun r =>
    sbMean_pos_volumeLaw (cutProb M r) (0 : M.V)
      (by simpa only [pow_one] using
        integrable_pow_volumeLaw (cutProb M r) (0 : M.V) 1 (hnePow r 1))
      (integrable_pow_volumeLaw (cutProb M r) (0 : M.V) 2 (hnePow r 2))
      (one_le_mean_volumeLaw (cutProb M r) (0 : M.V) (by
        simpa only [pow_one] using hnePow r 1))
  have hint : ∀ (r : ℝ) (k : ℕ),
      Integrable (fun x : ℝ => x ^ k) (volumeLaw (cutProb M r) (0 : M.V)) := fun r k =>
    integrable_pow_volumeLaw (cutProb M r) (0 : M.V) k (hnePow r k)
  exact tendsto_sizeBiasedLaw_Qinf_of_I16
    (inst := fun r => isProbabilityMeasure_volumeLaw (cutProb M r) (0 : M.V))
    h hA hc (fun r => volumeLaw_Iio_zero _ _) hint hEpos hSpos

/-- **(I.1.7) from (I.1.6)** with the printed constant `(α/β_c)√(2/(πA))`, for a
`SourceModelData`. Compared with the production assembly `I17.model_tendsto_tail_I17`, the
hypotheses `hconv`, `hE1`, `hψ2`, `hEpos`, `hSpos` and `hprob` are *derived*: what remains is the
all-order moment asymptotics (I.1.6), the finiteness of the cluster moments, the almost sure
finiteness of the critical cluster, and the restoration estimate (I.3.5). -/
theorem model_tendsto_tail_I17_of_I16 {A C : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hβ : 0 < (M.betaCrit : ℝ))
    (hfin : ∀ᵐ ω ∂M.criticalLaw, clusterVol ω (0 : M.V) ≠ ⊤)
    (hnePow : MomentFinite M)
    (h : I16 (fun r : ℝ => volumeLaw (cutProb M r) (0 : M.V)) A
      (M.α / (M.betaCrit : ℝ)) M.α)
    (hI35 : ∀ᶠ r in atTop, ∀ h' > 0,
      lapDefect (volumeLaw (cutProb M r) (0 : M.V)) h'
          ≤ lapDefect (volumeLaw (critProb M) (0 : M.V)) h' ∧
      lapDefect (volumeLaw (critProb M) (0 : M.V)) h'
          ≤ lapDefect (volumeLaw (cutProb M r) (0 : M.V)) h' +
            C * r ^ (-M.α) *
              (∫ x, x * Real.exp (-(h' * x)) ∂(volumeLaw (cutProb M r) (0 : M.V))) *
              lapDefect (volumeLaw (critProb M) (0 : M.V)) h') :
    Tendsto (fun n : ℕ => M.tailProb n /
      (I17const (M.α / (M.betaCrit : ℝ)) A * (1 / Real.sqrt (n : ℝ)))) atTop (𝓝 1) := by
  have hc : 0 < M.α / (M.betaCrit : ℝ) := div_pos M.hα hβ
  have hint1 : ∀ r : ℝ, Integrable (fun x : ℝ => x) (volumeLaw (cutProb M r) (0 : M.V)) :=
    fun r => by
      simpa only [pow_one] using
        integrable_pow_volumeLaw (cutProb M r) (0 : M.V) 1 (hnePow r 1)
  have hint2 : ∀ r : ℝ, Integrable (fun x : ℝ => x ^ 2) (volumeLaw (cutProb M r) (0 : M.V)) :=
    fun r => integrable_pow_volumeLaw (cutProb M r) (0 : M.V) 2 (hnePow r 2)
  have hEpos : ∀ r : ℝ, 0 < mean (volumeLaw (cutProb M r) (0 : M.V)) := fun r => by
    have h1 := one_le_mean_volumeLaw (cutProb M r) (0 : M.V) (by
      simpa only [pow_one] using hnePow r 1)
    linarith
  have hSpos : ∀ r : ℝ, 0 < sbMean (volumeLaw (cutProb M r) (0 : M.V)) := fun r =>
    sbMean_pos_volumeLaw (cutProb M r) (0 : M.V) (hint1 r) (hint2 r)
      (one_le_mean_volumeLaw (cutProb M r) (0 : M.V) (by
        simpa only [pow_one] using hnePow r 1))
  have hprob : ∀ r : ℝ,
      IsProbabilityMeasure (sizeBiasedLaw (volumeLaw (cutProb M r) (0 : M.V))) := fun r =>
    isProbabilityMeasure_sizeBiasedLaw _ (volumeLaw_Iio_zero _ _) (hint1 r) (hEpos r)
  have hconv : Tendsto (fun r : ℝ => Measure.toProbabilityMeasure
      (sizeBiasedLaw (volumeLaw (cutProb M r) (0 : M.V)))) atTop
      (𝓝 (Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf)) :=
    model_tendsto_Qinf_of_I16 M hA hβ hnePow h
  exact PercLib.CriticalLRP.I17.model_tendsto_tail_I17 M hA hC hβ hfin hint1 hint2 hEpos hSpos
    hprob hconv (tendsto_mean_of_I16 h) (tendsto_sbMean_of_I16 h hA hc hEpos) hI35

end ModelInstantiation

end SwarmM1

/-! ## 8. Axiom audit -/

set_option linter.hashCommand false

#print axioms SwarmM1.integral_pow_sizeBiasedLaw
#print axioms SwarmM1.integrable_pow_sizeBiasedLaw
#print axioms SwarmM1.sbProb
#print axioms SwarmM1.rpow_two_mul_add_one_mul
#print axioms SwarmM1.tendsto_mean_of_I16
#print axioms SwarmM1.tendsto_secMoment_of_I16
#print axioms SwarmM1.tendsto_sbMean_of_I16
#print axioms SwarmM1.sbMoment_eq
#print axioms SwarmM1.tendsto_integral_pow_sizeBiasedLaw_of_I16
#print axioms SwarmM1.tendsto_sizeBiasedLaw_Qinf_of_I16
#print axioms SwarmM1.integrable_pow_volumeLaw
#print axioms SwarmM1.one_le_mean_volumeLaw
#print axioms SwarmM1.sub_quarter_le_secMoment_volumeLaw
#print axioms SwarmM1.sbMean_pos_volumeLaw
#print axioms SwarmM1.modelSB
#print axioms SwarmM1.modelSB_isProbabilityMeasure
#print axioms SwarmM1.model_tendsto_Qinf_of_I16
#print axioms SwarmM1.model_tendsto_tail_I17_of_I16

/-! ## 9. The `I16rhs` notation of `Orchestration.Defs`

The production development already encodes the right-hand side of (I.1.6) as
`Orchestration.I16rhs M A p r`. The schema `I16` above is that same asymptotic, re-indexed by
`p = k + 1`; the next two results record this so that a hypothesis stated in the paper's own
`p ≥ 1` indexing can be consumed directly. -/

namespace SwarmM1

section PaperNotation

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I17

variable (M : PercLib.CriticalLRP.Orchestration.SourceModelData)

/-- **(I.1.6) in the production notation**, at every order `p ≥ 1`. -/
def I16Model (A : ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → Tendsto (fun r : ℝ =>
    (∫ x, x ^ p ∂(volumeLaw (cutProb M r) (0 : M.V))) / I16rhs M A p r) atTop (𝓝 1)

/-- `I16Model` is the schema `I16` re-indexed by `p = k + 1`: `(2p-3)!! = oddFact (p-1)`,
`A^{p-1}` and `r^{(2p-1)α}` are the `oddFact k`, `A^k` and `r^{(2k+1)α}` of `I16`. -/
theorem I16_of_I16Model {A : ℝ} (h : I16Model M A) :
    I16 (fun r : ℝ => volumeLaw (cutProb M r) (0 : M.V)) A (M.α / (M.betaCrit : ℝ)) M.α := by
  intro k
  have hk := h (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  have hexp : (2 * ((k + 1 : ℕ) : ℝ) - 1) * M.α = (((2 * k + 1 : ℕ)) : ℝ) * M.α := by
    push_cast
    ring
  have hMk : PercLib.CriticalLRP.VolumeMoments.M (k + 1 - 1) = oddFact k := rfl
  have hMk2 : PercLib.CriticalLRP.VolumeMoments.M k = oddFact k := rfl
  simpa only [I16rhs, hMk, hMk2, hexp, Nat.add_sub_cancel] using hk

/-- `hconv` of the (I.1.7) chain from (I.1.6) in the paper's `p ≥ 1` indexing. -/
theorem model_tendsto_Qinf_of_I16Model {A : ℝ} (hA : 0 < A) (hβ : 0 < (M.betaCrit : ℝ))
    (hnePow : MomentFinite M) (h : I16Model M A) :
    Tendsto (modelSB M hnePow) atTop
      (𝓝 (Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf)) :=
  model_tendsto_Qinf_of_I16 M hA hβ hnePow (I16_of_I16Model M h)

end PaperNotation

end SwarmM1

/-! ### Axiom audit (paper notation) -/

set_option linter.hashCommand false

#print axioms SwarmM1.I16_of_I16Model
#print axioms SwarmM1.model_tendsto_Qinf_of_I16Model
