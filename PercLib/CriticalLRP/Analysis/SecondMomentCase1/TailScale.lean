module
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Case 1 of Corollary I.4.14: the tree-graph scale calculation

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of Corollary I.4.14.
The tree-graph (Aizenman–Newman) bound (I.2.3) is `E|K|^q ≤ (2q-3)!! (E|K|)^{2q-1}` for `q ≥ 1`.
Integrated from the reviewed bounded submission `.ultramath/smwzvo8ss/m3/CaseOneTail`.
This file supplies partial analytic ingredients toward the displayed tail
`P(|K| ≥ n) ≤ sqrt(2 m/n) exp(-n/(4 m²))`, `m = E|K|`, at the natural scale `u = n/m²`.
It does not identify `oddDFact` with `Nat.doubleFactorial` or prove the whole tail.

* `oddDFact q = (2q-3)!! = 1·3···(2q-3)` and `oddDFact_le_two_pow_mul_factorial`;
* `factorial_le_exp_mul_sqrt_mul : q! ≤ e √q (q/e)^q` (Mathlib's monotone Stirling sequence);
* `log_six_ge : log 6 ≥ 1.7`, `log_105_le : log 105 ≤ 5`;
* `scale_two : 1 ≤ u² √(2/u) exp(-u/4)` for `1 ≤ u ≤ 6` (order `q = 2`, `(2q-3)!! = 1`);
* `scale_five : 105 ≤ u⁵ √(2/u) exp(-u/4)` for `6 ≤ u ≤ 16` (order `q = 5`, `(2q-3)!! = 105`).

At `n = u m²` the Markov bound `P(|K| ≥ n) ≤ (2q-3)!! m^{2q-1} n^{-q}` reads
`(2q-3)!! u^{-q}/m`, so the two scale lemmas are exactly what is needed to reach
`√(2/(u m)) exp(-u/4) = √(2m/n) exp(-n/(4m²))`.
-/

@[expose] public section

noncomputable section

open Finset
open scoped BigOperators

namespace CaseOneTail


def oddDFact (q : ℕ) : ℕ := ∏ i ∈ Finset.range (q - 1), (2 * i + 1)

lemma eq_even (q : ℕ) :
    (∏ i ∈ Finset.range (q - 1), (2 * i + 2)) = 2 ^ (q - 1) * Nat.factorial (q - 1) := by
  have step : (∏ i ∈ Finset.range (q - 1), (2 * i + 2)) =
      ∏ i ∈ Finset.range (q - 1), (2 * (i + 1)) := by
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [step, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_range_add_one_eq_factorial]

@[simp] lemma oddDFact_five : oddDFact 5 = 105 := by decide

/-- `(2q-3)!! ≤ 2^{q-1} q!`, the only combinatorial input of the scale calculation. -/
lemma oddDFact_le_two_pow_mul_factorial (q : ℕ) :
    oddDFact q ≤ 2 ^ (q - 1) * Nat.factorial q := by
  rw [oddDFact]
  refine le_trans (Finset.prod_le_prod (f := fun i => 2 * i + 1) (g := fun i => 2 * i + 2)
    (fun i _ => by omega)) ?_
  rw [eq_even q]
  exact Nat.mul_le_mul_left _ (Nat.factorial_le (by omega))



theorem factorial_le_exp_mul_sqrt_mul {q : ℕ} (hq : 1 ≤ q) :
    (Nat.factorial q : ℝ) ≤ Real.exp 1 * Real.sqrt q * (q / Real.exp 1) ^ q := by
  have hmono : Stirling.stirlingSeq q ≤ Stirling.stirlingSeq 1 := by
    have h := Stirling.stirlingSeq'_antitone (show 0 ≤ q - 1 by omega)
    simpa only [Function.comp_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hq,
      Nat.zero_add] using h
  rw [Stirling.stirlingSeq, Stirling.stirlingSeq_one, div_le_iff₀] at hmono
  · have hsqrt : Real.sqrt (2 * (q : ℝ)) = Real.sqrt 2 * Real.sqrt q := by
      rw [Real.sqrt_mul (by norm_num)]
    have h2 : (Real.exp 1 / Real.sqrt 2) *
        (Real.sqrt (2 * (q : ℝ)) * (q / Real.exp 1) ^ q)
        = Real.exp 1 * Real.sqrt q * (q / Real.exp 1) ^ q := by
      rw [hsqrt]
      have hne : Real.sqrt 2 ≠ 0 := by positivity
      field_simp
    rw [← h2]
    exact hmono
  · have : (0:ℝ) < q := by exact_mod_cast hq
    positivity



/-- `log 6 ≥ 1.7`, from `log 2 ≥ 0.6931` and `log x ≥ 1 - 1/x`. -/
lemma log_six_ge : (1.7 : ℝ) ≤ Real.log 6 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h32 : (1 : ℝ) - (3 / 2 : ℝ)⁻¹ ≤ Real.log (3 / 2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have e1 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have e2 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e1, e2] at *
  linarith

/-- `log 105 ≤ 5`, since `105 ≤ e^5`. -/
lemma log_105_le : Real.log 105 ≤ 5 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h5 : Real.exp 5 = (Real.exp 1) ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpow : (2.7182818283 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) he.le 5
  have hnum : (105 : ℝ) < (2.7182818283 : ℝ) ^ 5 := by norm_num
  have hlt : (105 : ℝ) < Real.exp 5 := by rw [h5]; linarith
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr hlt.le

/-- Order `q = 2`: `1 ≤ u² √(2/u) exp(-u/4)` for `1 ≤ u ≤ 6`. -/
lemma scale_two {u : ℝ} (h1 : 1 ≤ u) (h6 : u ≤ 6) :
    1 ≤ u ^ 2 * (Real.sqrt (2 / u) * Real.exp (-(u / 4))) := by
  have hu : 0 < u := by linarith
  have hbase : 0 < u ^ 2 * Real.sqrt (2 / u) := by
    have : (0:ℝ) < 2 / u := by positivity
    positivity
  have hlog : u / 4 ≤ Real.log (u ^ 2 * Real.sqrt (2 / u)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_sqrt (by positivity),
      Real.log_div (by norm_num) hu.ne']
    push_cast
    have hlow : 1 - u⁻¹ ≤ Real.log u := Real.one_sub_inv_le_log_of_pos hu
    have hprod : (u - 1) * (u - 6) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hle : u ^ 2 ≤ 7 * u - 6 := by nlinarith [hprod]
    have hkey : u / 4 + (3 / 2) * u⁻¹ ≤ 7 / 4 := by
      have hrw : u / 4 + (3 / 2) * u⁻¹ = (u ^ 2 + 6) / (4 * u) := by
        field_simp
        ring
      rw [hrw, div_le_iff₀ (by positivity)]
      linarith [hle]
    have h2 := Real.log_two_gt_d9
    linarith [hkey, hlow, h2]
  have hexp : Real.exp (u / 4) ≤ u ^ 2 * Real.sqrt (2 / u) :=
    (Real.le_log_iff_exp_le hbase).mp hlog
  calc (1 : ℝ) = Real.exp (u / 4) * Real.exp (-(u / 4)) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    _ ≤ (u ^ 2 * Real.sqrt (2 / u)) * Real.exp (-(u / 4)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = u ^ 2 * (Real.sqrt (2 / u) * Real.exp (-(u / 4))) := by ring

/-- Order `q = 5`: `105 ≤ u⁵ √(2/u) exp(-u/4)` for `6 ≤ u ≤ 16`. -/
lemma scale_five {u : ℝ} (h6 : 6 ≤ u) (h16 : u ≤ 16) :
    105 ≤ u ^ 5 * (Real.sqrt (2 / u) * Real.exp (-(u / 4))) := by
  have hu : 0 < u := by linarith
  have hbase : 0 < u ^ 5 * Real.sqrt (2 / u) := by
    have : (0:ℝ) < 2 / u := by positivity
    positivity
  have hlog : Real.log 105 + u / 4 ≤ Real.log (u ^ 5 * Real.sqrt (2 / u)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_sqrt (by positivity),
      Real.log_div (by norm_num) hu.ne']
    push_cast
    have h6' : (1.7 : ℝ) ≤ Real.log 6 := log_six_ge
    have hlow : Real.log 6 + (1 - 6 * u⁻¹) ≤ Real.log u := by
      have h0 : 1 - (u / 6)⁻¹ ≤ Real.log (u / 6) :=
        Real.one_sub_inv_le_log_of_pos (by positivity)
      have hinv : (u / 6)⁻¹ = 6 * u⁻¹ := by field_simp
      have hsplit : Real.log u = Real.log 6 + Real.log (u / 6) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
      rw [hinv] at h0
      linarith [h0, hsplit]
    have h105 : Real.log 105 ≤ 5 := log_105_le
    have hprod : (u - 6) * (u - 16) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hquad : u / 4 + 27 * u⁻¹ ≤ 7 := by
      have hrw : u / 4 + 27 * u⁻¹ = (u ^ 2 + 108) / (4 * u) := by
        field_simp
        ring
      rw [hrw, div_le_iff₀ (by positivity)]
      nlinarith [hprod, hu]
    have h2 := Real.log_two_gt_d9
    linarith [hlow, h105, hquad, hu, h2]
  have hexp : 105 * Real.exp (u / 4) ≤ u ^ 5 * Real.sqrt (2 / u) := by
    rw [← Real.log_le_log_iff (by positivity) hbase] at *
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    linarith [hlog]
  calc (105 : ℝ) = (105 * Real.exp (u / 4)) * Real.exp (-(u / 4)) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ (u ^ 5 * Real.sqrt (2 / u)) * Real.exp (-(u / 4)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = u ^ 5 * (Real.sqrt (2 / u) * Real.exp (-(u / 4))) := by ring


end CaseOneTail

set_option linter.hashCommand false
#print axioms CaseOneTail.eq_even
#print axioms CaseOneTail.oddDFact_five
#print axioms CaseOneTail.oddDFact_le_two_pow_mul_factorial
#print axioms CaseOneTail.factorial_le_exp_mul_sqrt_mul
#print axioms CaseOneTail.log_six_ge
#print axioms CaseOneTail.log_105_le
#print axioms CaseOneTail.scale_two
#print axioms CaseOneTail.scale_five
