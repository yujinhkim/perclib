/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Auxiliary inequalities for the universal-tightness moment ratio

Elementary power and measure inequalities feeding into the proof of Corollary I.2.5 of
Hutchcroft, arXiv:2508.18807v1 (the moment-ratio consequence of the universal tightness
theorem I.2.3).
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

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Tightness

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Mean-value bounds for powers -/

lemma pow_succ_sub_pow_le_real (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (x + 1) ^ k - x ^ k ≤ (k : ℝ) * (x + 1) ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hkey : (x + 1) ^ (k + 1) - x ^ (k + 1) = ((x + 1) ^ k - x ^ k) * (x + 1) + x ^ k := by
      ring
    rw [hkey]
    have hx1 : (0 : ℝ) ≤ x + 1 := by linarith
    have h1 : ((x + 1) ^ k - x ^ k) * (x + 1) ≤ ((k : ℝ) * (x + 1) ^ (k - 1)) * (x + 1) :=
      mul_le_mul_of_nonneg_right ih hx1
    have h2 : ((k : ℝ) * (x + 1) ^ (k - 1)) * (x + 1) = (k : ℝ) * (x + 1) ^ k := by
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega
    have h3 : x ^ k ≤ (x + 1) ^ k := pow_le_pow_left₀ hx (by linarith) k
    have h4 : ((k : ℝ) + 1) * (x + 1) ^ k = (k : ℝ) * (x + 1) ^ k + (x + 1) ^ k := by ring
    push_cast
    nlinarith [h1, h2, h3, h4]

/-- Mean-value bound in `ℝ≥0∞`: `(n+1)^k - n^k ≤ k (n+1)^{k-1}`. -/
lemma pow_succ_sub_pow_le (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    ((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k ≤ (k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1) := by
  have hcast1 : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast]
    norm_num
  have hcast2 : ((n : ℝ≥0∞)) = ENNReal.ofReal ((n : ℝ)) := (ENNReal.ofReal_natCast n).symm
  have hreal := pow_succ_sub_pow_le_real ((n : ℝ)) (by positivity) k hk
  have hL : ((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k
      = ENNReal.ofReal (((n : ℝ) + 1) ^ k - (n : ℝ) ^ k) := by
    rw [hcast1, hcast2, ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (n:ℝ) + 1),
      ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (n:ℝ)),
      ← ENNReal.ofReal_sub _ (pow_nonneg (by positivity) k)]
  rw [hL]
  calc ENNReal.ofReal (((n : ℝ) + 1) ^ k - (n : ℝ) ^ k)
      ≤ ENNReal.ofReal ((k : ℝ) * ((n : ℝ) + 1) ^ (k - 1)) := ENNReal.ofReal_le_ofReal hreal
    _ = (k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (n:ℝ) + 1), hcast1.symm]

/-- `(n+1)^{p-1} ≤ (n+1)^p - n^p` for `p ≥ 1`. -/
lemma pow_sub_pow_ge (p : ℕ) (hp : 1 ≤ p) (n : ℕ) :
    ((n : ℝ≥0∞) + 1) ^ (p - 1) ≤ ((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p := by
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 1 := ⟨p - 1, by omega⟩
  have hnat : (n + 1) ^ j + n ^ (j + 1) ≤ (n + 1) ^ (j + 1) := by
    have h1 : n ^ (j + 1) ≤ (n + 1) ^ j * n := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ n) j)
    have h2 : (n + 1) ^ (j + 1) = (n + 1) ^ j * n + (n + 1) ^ j := by
      rw [pow_succ, show n + 1 = Nat.succ n from rfl, Nat.mul_succ]
    rw [h2]
    omega
  have hcast1 : ((n : ℝ≥0∞) + 1) = ((n + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
  have hadd : ((n : ℝ≥0∞) + 1) ^ j + (n : ℝ≥0∞) ^ (j + 1) ≤ ((n : ℝ≥0∞) + 1) ^ (j + 1) := by
    rw [hcast1, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add, Nat.cast_le]
    exact hnat
  exact ENNReal.le_sub_of_add_le_right (by simp) hadd

/-! ### Measure bounds -/

/-- For a nonnegative real `a`, `a * μ {a ≤ X} ≤ ∫⁻ X`. -/
lemma ofReal_mul_meas_le_lintegral {μ : Measure Ω} {X : Ω → ℝ≥0∞} (hX : Measurable X) {a : ℝ}
    (ha : 0 ≤ a) :
    ENNReal.ofReal a * μ {ω | ENNReal.ofReal a ≤ X ω} ≤ ∫⁻ ω, X ω ∂μ := by
  have hmeas : MeasurableSet {ω : Ω | ENNReal.ofReal a ≤ X ω} :=
    measurableSet_le measurable_const hX
  calc ENNReal.ofReal a * μ {ω | ENNReal.ofReal a ≤ X ω}
      = ∫⁻ _ in {ω | ENNReal.ofReal a ≤ X ω}, ENNReal.ofReal a ∂μ := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ x in {ω | ENNReal.ofReal a ≤ X ω}, X x ∂μ := by
        refine setLIntegral_mono' (f := fun _ => ENNReal.ofReal a) (g := X) hmeas ?_
        intro ω hω
        exact hω
    _ ≤ ∫⁻ ω, X ω ∂μ := setLIntegral_le_lintegral _ X

/-- Power form: `M^p * μ {M ≤ X} ≤ ∫⁻ X^p` for `M ≥ 0`. -/
lemma ofReal_pow_mul_meas_le_lintegral {μ : Measure Ω} {X : Ω → ℝ≥0∞} (hX : Measurable X)
    {M : ℝ} (hM : 0 ≤ M) (p : ℕ) :
    ENNReal.ofReal M ^ p * μ {ω | ENNReal.ofReal M ≤ X ω} ≤ ∫⁻ ω, X ω ^ p ∂μ := by
  have hmeas : MeasurableSet {ω : Ω | ENNReal.ofReal M ≤ X ω} :=
    measurableSet_le measurable_const hX
  calc ENNReal.ofReal M ^ p * μ {ω | ENNReal.ofReal M ≤ X ω}
      = ∫⁻ _ in {ω | ENNReal.ofReal M ≤ X ω}, ENNReal.ofReal (M ^ p) ∂μ := by
        rw [setLIntegral_const, ENNReal.ofReal_pow hM]
    _ ≤ ∫⁻ x in {ω | ENNReal.ofReal M ≤ X ω}, X x ^ p ∂μ := by
        refine setLIntegral_mono' (f := fun _ => ENNReal.ofReal (M ^ p)) (g := fun ω => X ω ^ p)
          hmeas ?_
        intro ω hω
        have hω' : ENNReal.ofReal M ≤ X ω := hω
        rw [ENNReal.ofReal_pow hM]
        exact pow_le_pow_left' hω' p
    _ ≤ ∫⁻ ω, X ω ^ p ∂μ := setLIntegral_le_lintegral _ (fun ω => X ω ^ p)

end PercLib.CriticalLRP.Tightness

/-- `(n : ℝ≥0∞) * ofReal x = ofReal (n * x)` for `x ≥ 0`. -/
lemma natCast_mul_ofReal (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (n : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal ((n : ℝ) * x) := by
  nth_rewrite 1 [← ENNReal.ofReal_natCast n]
  rw [← ENNReal.ofReal_mul (by positivity)]
