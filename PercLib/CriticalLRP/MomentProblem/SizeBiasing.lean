/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Size biasing on `[0,∞)` and the chi-square moment identity

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), proof of (I.1.7), p. 32:

  "the moments of `Q_r` satisfy
     `∫ x^p dQ_r = Ê|K|^p / (Ê|K|)^p = E|K|^{p+1} / ((E|K|^2/E|K|)^p E|K|) ∼ (2p-1)!!`",

where `Q_r` is the law of `|K| / Ê_{β_c,r}|K|` under the size-biased measure. This file formalizes
the underlying size-biasing identities:

* `sizeBias μ = μ.withDensity (ofReal id)`: the (unnormalized) size-biased measure;
* `integral_pow_sizeBias` : `∫ x^n d(sizeBias μ) = ∫ x^{n+1} dμ` (the moment shift);
* `integral_pow_normSizeBias` : the same for the normalized size-biased measure
  `μ̂ = (m_1)⁻¹ • sizeBias μ`: `∫ x^n dμ̂ = m_{n+1}/m_1`;
* `moments_law_sizeBiased` : the law of `x / Ê x` under `μ̂` has moments `m_{p+1} m_1^{p-1} / m_2^p`;
* `chiSquare_moment_ratio` : if the moments have the form `m_p = (2p-3)!! A^{p-1} u^{2p-1}` (the
  shape of Theorem I.1.6), then these moments are *exactly* `(2p-1)!!` for every `p ≥ 1`, i.e. the
  chi-square moments with one degree of freedom. No limit is needed.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.MomentProblem.ChiSquare

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option maxHeartbeats 800000

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.MomentProblem

/-! ### The size-biased measure -/

/-- The size-biased (unnormalized) version of a measure on `[0,∞)`: density `x` with respect to the
original measure. Its total mass is the first moment `∫ x dμ`. -/
noncomputable def sizeBias (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity fun x => ENNReal.ofReal x

lemma measurable_sizeBias_density : Measurable (fun x : ℝ => ENNReal.ofReal x) :=
  ENNReal.measurable_ofReal

/-- **Moment shift under size biasing.** -/
theorem integral_pow_sizeBias {μ : Measure ℝ} (hμ0 : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (n : ℕ) :
    ∫ x, x ^ n ∂(sizeBias μ) = ∫ x, x ^ (n + 1) ∂μ := by
  rw [sizeBias, integral_withDensity_eq_integral_toReal_smul measurable_sizeBias_density
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (fun x => x ^ n)]
  have hpt : ∀ᵐ x : ℝ ∂μ, (ENNReal.ofReal x).toReal • x ^ n = x ^ (n + 1) := by
    filter_upwards [hμ0] with x hx
    rw [smul_eq_mul, ENNReal.toReal_ofReal hx, pow_succ]
    ring
  exact integral_congr_ae hpt

end PercLib.CriticalLRP.MomentProblem

namespace PercLib.CriticalLRP.MomentProblem

/-! ### The normalized size-biased measure and the law of the normalized point -/

/-- **Moments of the normalized size-biased measure**: `∫ x^p dμ̂ = m_{p+1}/m_1`. -/
theorem integral_pow_normSizeBias {μ : Measure ℝ} (hμ0 : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) {m1 : ℝ}
    (hm1 : 0 < m1) (hm1eq : m1 = ∫ x, x ∂μ) (p : ℕ) :
    ∫ x, x ^ p ∂((ENNReal.ofReal m1)⁻¹ • sizeBias μ) = m1⁻¹ * ∫ x, x ^ (p + 1) ∂μ := by
  rw [integral_smul_measure, integral_pow_sizeBias hμ0 p, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hm1.le, smul_eq_mul, hm1eq]

/-- **The moments of the law of `x / Ê x` under the normalized size-biased measure**, in the form
`(m_1/m_2)^p m_1^{-1} m_{p+1}` (valid for all `p`, including `p = 0`). -/
theorem integral_pow_law_sizeBiased {μ : Measure ℝ} (hμ0 : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) {m1 m2 : ℝ}
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm1eq : m1 = ∫ x, x ∂μ) (hm2eq : m2 = ∫ x, x ^ 2 ∂μ)
    (p : ℕ) :
    ∫ y, y ^ p ∂(((ENNReal.ofReal m1)⁻¹ • sizeBias μ).map (fun x => x * m1 / m2))
      = (m1 / m2) ^ p * (m1⁻¹ * ∫ x, x ^ (p + 1) ∂μ) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, (x * m1 / m2) ^ p = (m1 / m2) ^ p * x ^ p := by
    intro x
    rw [div_pow, div_pow, mul_pow]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_pow_normSizeBias hμ0 hm1 hm1eq p]

/-- The same moment identity in the form used in the proof of (I.1.7) of the paper:
`m_{p+1} m_1^{p-1} / m_2^p` for `p ≥ 1`. -/
theorem integral_pow_law_sizeBiased' {μ : Measure ℝ} (hμ0 : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) {m1 m2 : ℝ}
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm1eq : m1 = ∫ x, x ∂μ) (hm2eq : m2 = ∫ x, x ^ 2 ∂μ)
    {p : ℕ} (hp : 1 ≤ p) :
    ∫ y, y ^ p ∂(((ENNReal.ofReal m1)⁻¹ • sizeBias μ).map (fun x => x * m1 / m2))
      = m1 ^ (p - 1) * (∫ x, x ^ (p + 1) ∂μ) / m2 ^ p := by
  rw [integral_pow_law_sizeBiased hμ0 hm1 hm2 hm1eq hm2eq p, div_pow]
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp
  have hpow : m1 * m1 ^ (p - 1) = m1 ^ p := by
    rw [← pow_succ', hp1]
  field_simp
  calc m1 ^ p * ∫ x, x ^ (p + 1) ∂μ
      = (m1 * m1 ^ (p - 1)) * ∫ x, x ^ (p + 1) ∂μ := by rw [hpow]
    _ = (m1 * ∫ x, x ^ (p + 1) ∂μ) * m1 ^ (p - 1) := by ring

/-- **The chi-square moment identity of Theorem I.1.6.**  If the moments have the form
`m_p = (2p-3)!! A^{p-1} u^{2p-1}` (the shape of (I.1.6), with `u = (α/β_c)^α r^α` and `A` the
non-universal constant), then the `p`-th moment of the normalized size-biased law of the volume is
*exactly* the chi-square moment `(2p-1)!!`, with no limit taken. -/
theorem chiSquare_moment_of_moment_formula {A u : ℝ} (hA : A ≠ 0) (hu : u ≠ 0) {p : ℕ}
    (hp : 1 ≤ p) :
    (oddFact p : ℝ) * A ^ p * u ^ (2 * p + 1) * u ^ (p - 1) / (A * u ^ 3) ^ p
      = (oddFact p : ℝ) := by
  have hexp : 2 * p + 1 + (p - 1) = 3 * p := by omega
  have hAu : (A * u ^ 3) ^ p = A ^ p * u ^ (3 * p) := by
    rw [mul_pow, ← pow_mul]
  have hnum : (oddFact p : ℝ) * A ^ p * u ^ (2 * p + 1) * u ^ (p - 1)
      = (oddFact p : ℝ) * A ^ p * u ^ (3 * p) := by
    rw [mul_assoc ((oddFact p : ℝ) * A ^ p), ← pow_add, hexp]
  rw [hAu, hnum]
  have hA3 : A ^ p ≠ 0 := pow_ne_zero _ hA
  have hu3 : u ^ (3 * p) ≠ 0 := pow_ne_zero _ hu
  field_simp

end PercLib.CriticalLRP.MomentProblem

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.MomentProblem.integral_pow_sizeBias
#print axioms PercLib.CriticalLRP.MomentProblem.integral_pow_normSizeBias
#print axioms PercLib.CriticalLRP.MomentProblem.integral_pow_law_sizeBiased
#print axioms PercLib.CriticalLRP.MomentProblem.integral_pow_law_sizeBiased'
#print axioms PercLib.CriticalLRP.MomentProblem.chiSquare_moment_of_moment_formula
