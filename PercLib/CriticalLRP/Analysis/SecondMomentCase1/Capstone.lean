/-
Integrated after independent review from `.ultramath/smwzx5lly/m4/CaseOneTail/Capstone.lean`.
The preceding partial `TailScale` module is now a compatibility re-export.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import PercLib.CriticalLRP.Analysis.SecondMomentCase1.Hydro
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffAllMoments
public import PercLib.CriticalLRP.Analysis.MomentRegularVariation

/-!
# Case 1 of Corollary I.4.14: the tree-graph scale calculation, all regimes

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Corollary I.4.14 (p. 42).  The tree-graph
(Aizenman--Newman) input (I.2.3) is `E|K|^q ≤ (2q-3)!! (E|K|)^{2q-1}` for every `q ≥ 1`,
which by Markov's inequality gives, writing `m = E|K|`, `u = n/m²` and `D q = (2q-3)!!`,

    P(|K| ≥ n) ≤ D q · m^{2q-1} / n^q = (1/m) · D q · u^{-q}.

The paper's displayed conclusion is `P(|K| ≥ n) ≤ sqrt(2m/n) exp(-n/(4m²))`
`= m^{-1/2} sqrt(2/u) exp(-u/4)`.  So the analytic content is

    D q / u^q ≤ sqrt(m) · (sqrt(2/u) · exp(-u/4)),

and `sqrt m ≥ 1` gives all the slack needed.  This file proves, for `m ≥ 1` and `n ≥ 1`,
that such an order `q ≥ 1` always exists:

* `u m < 1`: the target already exceeds `1`, so `P ≤ 1` suffices;
* `u ≤ 1`, `u m ≥ 1`: order `q = 1`, using `sqrt m ≥ 1/sqrt u`;
* `1 ≤ u ≤ 6`: order `q = 2`, `scale_two`;
* `6 ≤ u ≤ 16`: order `q = 5`, `scale_five`;
* `16 ≤ u`: order `q = ⌊u/2⌋`, from `(2q-3)!! ≤ 2^{q-1} q!` and the Stirling bound
  `q! ≤ e sqrt q (q/e)^q`, which at `2q ≤ u` and `q ≥ u/2 - 1` gives
  `D q u^{-q} ≤ (e²/2) sqrt(u/2) exp(-u/2)`, compared with `sqrt(2/u) exp(-u/4)`
  by `e² u ≤ 4 exp(u/4)`.

The odd double factorial `D q = (2q-3)!! = 1·3···(2q-3)` is bridged to Mathlib's
`Nat.doubleFactorial (2*q-3)`; the bridge to the production normalisation
`VolumeMoments.M (q-1)` lives in `CaseOneTail.Main`.
-/

@[expose] public section

noncomputable section

open Finset
open scoped BigOperators

namespace CaseOneTail

/-! ## The odd double factorial -/

/-- `oddDFact q = (2q-3)!! = 1·3···(2q-3)`, the empty product `(-1)!! = 1` at `q = 1` and
`q = 2`. -/
def oddDFact (q : ℕ) : ℕ := ∏ i ∈ Finset.range (q - 1), (2 * i + 1)

@[simp] theorem oddDFact_one : oddDFact 1 = 1 := by simp [oddDFact]

@[simp] theorem oddDFact_two : oddDFact 2 = 1 := by simp [oddDFact]

@[simp] theorem oddDFact_five : oddDFact 5 = 105 := by decide

/-- The bridge to Mathlib's `Nat.doubleFactorial`: `(2q-3)!! = Nat.doubleFactorial (2q-3)`
for `q ≥ 1` (the truncated subtraction is correct because `Nat.doubleFactorial 0 = 1`). -/
theorem oddDFact_eq_doubleFactorial {q : ℕ} (hq : 1 ≤ q) :
    oddDFact q = Nat.doubleFactorial (2 * q - 3) := by
  rcases Nat.eq_or_lt_of_le hq with h | h
  · subst h
    simp [oddDFact]
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
    rw [show 2 * (k + 2) - 3 = 2 * k + 1 by omega, Nat.doubleFactorial_eq_prod_odd]
    simp only [oddDFact]
    rw [show k + 2 - 1 = k + 1 by omega, Finset.prod_range_succ']
    simp

/-- `(2q-3)!! ≤ 2^{q-1} q!`, termwise `2i+1 ≤ 2i+2`. -/
theorem oddDFact_le_two_pow_mul_factorial (q : ℕ) :
    oddDFact q ≤ 2 ^ (q - 1) * Nat.factorial q := by
  have step : (∏ i ∈ Finset.range (q - 1), (2 * i + 2)) =
      2 ^ (q - 1) * Nat.factorial (q - 1) := by
    have hstep : (∏ i ∈ Finset.range (q - 1), (2 * i + 2)) =
        ∏ i ∈ Finset.range (q - 1), (2 * (i + 1)) :=
      Finset.prod_congr rfl fun i _ => by ring
    rw [hstep, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_range_add_one_eq_factorial]
  rw [oddDFact]
  refine le_trans (Finset.prod_le_prod (f := fun i => 2 * i + 1) (g := fun i => 2 * i + 2)
    (fun i _ => by omega)) ?_
  rw [step]
  exact Nat.mul_le_mul_left _ (Nat.factorial_le (by omega))

/-- The upper Stirling bound `q! ≤ e sqrt q (q/e)^q`, from antitonicity of Mathlib's
`Stirling.stirlingSeq` (Mathlib has the lower bound only). -/
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
  · have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity

/-! ## Elementary numerical bounds -/

/-- `log 6 ≥ 1.7`. -/
theorem log_six_ge : (1.7 : ℝ) ≤ Real.log 6 := by
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
theorem log_105_le : Real.log 105 ≤ 5 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h5 : Real.exp 5 = (Real.exp 1) ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpow : (2.7182818283 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) he.le 5
  have hnum : (105 : ℝ) < (2.7182818283 : ℝ) ^ 5 := by norm_num
  have hlt : (105 : ℝ) < Real.exp 5 := by rw [h5]; linarith
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr hlt.le

/-- `1 ≤ sqrt 2 · exp(-1/4)`, the numerical input of the `u ≤ 1` regime. -/
theorem one_le_sqrt_two_mul_exp_neg_quarter :
    (1 : ℝ) ≤ Real.sqrt 2 * Real.exp (-(1 / 4)) := by
  have hlog : Real.log (Real.sqrt 2) = Real.log 2 / 2 := Real.log_sqrt (by norm_num)
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlt : (1 / 4 : ℝ) < Real.log (Real.sqrt 2) := by rw [hlog]; linarith
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hexp : Real.exp (1 / 4) ≤ Real.sqrt 2 := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr hlt.le
  calc (1 : ℝ) = Real.exp (1 / 4) * Real.exp (-(1 / 4)) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    _ ≤ Real.sqrt 2 * Real.exp (-(1 / 4)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le

/-- `e² u ≤ 4 exp(u/4)` for `u ≥ 16`: this is the whole slack of the large-`u` regime. -/
theorem exp_sq_mul_le {u : ℝ} (hu : 16 ≤ u) :
    Real.exp 2 * u ≤ 4 * Real.exp (u / 4) := by
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith
  have he4 : 4 * Real.exp 2 ≤ Real.exp 4 := by
    have h : Real.exp 4 = Real.exp 2 * Real.exp 2 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have ht : (0 : ℝ) ≤ u - 16 := by linarith
  have hsplit : Real.exp (u / 4) = Real.exp 4 * Real.exp ((u - 16) / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp : 1 + (u - 16) / 4 ≤ Real.exp ((u - 16) / 4) :=
    by linarith [Real.add_one_le_exp ((u - 16) / 4)]
  have hkey : Real.exp 4 * (1 + (u - 16) / 4) ≤ Real.exp (u / 4) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hexp (Real.exp_pos 4).le
  have hmono : Real.exp 2 ≤ Real.exp 4 := by nlinarith
  have hprod : Real.exp 2 * (u - 16) ≤ Real.exp 4 * (u - 16) :=
    mul_le_mul_of_nonneg_right hmono ht
  nlinarith [hkey, hprod, he2, he4, ht]

/-! ## The scale inequalities in the three regimes -/

/-- Order `q = 2`: `1 ≤ u² sqrt(2/u) exp(-u/4)` for `1 ≤ u ≤ 6`. -/
theorem scale_two {u : ℝ} (h1 : 1 ≤ u) (h6 : u ≤ 6) :
    1 ≤ u ^ 2 * (Real.sqrt (2 / u) * Real.exp (-(u / 4))) := by
  have hu : 0 < u := by linarith
  have hbase : 0 < u ^ 2 * Real.sqrt (2 / u) := by
    have : (0 : ℝ) < 2 / u := by positivity
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

/-- Order `q = 5`: `105 ≤ u⁵ sqrt(2/u) exp(-u/4)` for `6 ≤ u ≤ 16`. -/
theorem scale_five {u : ℝ} (h6 : 6 ≤ u) (h16 : u ≤ 16) :
    105 ≤ u ^ 5 * (Real.sqrt (2 / u) * Real.exp (-(u / 4))) := by
  have hu : 0 < u := by linarith
  have hbase : 0 < u ^ 5 * Real.sqrt (2 / u) := by
    have : (0 : ℝ) < 2 / u := by positivity
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

/-- The algebraic identity of the large-`u` regime:
`2^{q-1} q! u^{-q}`-type terms combine into `(e/2) sqrt q (2q/(e u))^q`. -/
theorem pow_identity {q : ℕ} (hq : 1 ≤ q) {u : ℝ} (hu : 0 < u) :
    (2 : ℝ) ^ (q - 1) * (Real.exp 1 * Real.sqrt q * ((q : ℝ) / Real.exp 1) ^ q) / u ^ q
      = Real.exp 1 / 2 * Real.sqrt q * (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q := by
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2q : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := by
    rw [eq_div_iff (by norm_num)]
    rw [← pow_succ, Nat.sub_one_add_one (by omega)]
  have hqE : ((q : ℝ) / Real.exp 1) ^ q = (q : ℝ) ^ q / (Real.exp 1) ^ q := by
    rw [div_pow]
  have h2qu : (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q =
      (2 * (q : ℝ)) ^ q / (Real.exp 1 * u) ^ q := by
    rw [div_pow]
  have h2qmul : (2 * (q : ℝ)) ^ q = 2 ^ q * (q : ℝ) ^ q := by rw [mul_pow]
  have hEumul : (Real.exp 1 * u) ^ q = (Real.exp 1) ^ q * u ^ q := by rw [mul_pow]
  rw [hqE, h2qu, h2qmul, hEumul, h2q]
  have hEq : (Real.exp 1) ^ q ≠ 0 := pow_ne_zero _ hE.ne'
  have huq : u ^ q ≠ 0 := pow_ne_zero _ hu.ne'
  field_simp

/-- Large-`u` regime, order `q = ⌊u/2⌋`: `(2q-3)!! u^{-q} ≤ sqrt(2/u) exp(-u/4)` for
`u ≥ 16`. -/
theorem scale_floor {u : ℝ} (hu : 16 ≤ u) :
    (oddDFact ⌊u / 2⌋₊ : ℝ) / u ^ ⌊u / 2⌋₊ ≤
      Real.sqrt (2 / u) * Real.exp (-(u / 4)) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  set q : ℕ := ⌊u / 2⌋₊ with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    exact Nat.floor_pos.mpr (by linarith)
  have hqle : (q : ℝ) ≤ u / 2 := by
    rw [hqdef]
    exact Nat.floor_le (by linarith)
  have hqge : u / 2 - 1 < (q : ℝ) := by
    have h : u / 2 - 1 < ((⌊u / 2⌋₊ : ℕ) : ℝ) := by
      have h' := Nat.lt_floor_add_one (u / 2)
      linarith
    simpa [hqdef] using h
  -- Step 1: the factorial bound for `oddDFact q`.
  have hstep : (oddDFact q : ℝ) / u ^ q ≤
      Real.exp 1 / 2 * Real.sqrt q * (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q := by
    have hD : (oddDFact q : ℝ) ≤ (2 : ℝ) ^ (q - 1) * (Nat.factorial q : ℝ) := by
      have := oddDFact_le_two_pow_mul_factorial q
      exact_mod_cast this
    have hF : (Nat.factorial q : ℝ) ≤ Real.exp 1 * Real.sqrt q * ((q : ℝ) / Real.exp 1) ^ q :=
      factorial_le_exp_mul_sqrt_mul hq1
    have hupos : (0 : ℝ) < u ^ q := pow_pos hu0 q
    rw [show (Real.exp 1 / 2 * Real.sqrt q * (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q) =
      (2 : ℝ) ^ (q - 1) *
        (Real.exp 1 * Real.sqrt q * ((q : ℝ) / Real.exp 1) ^ q) / u ^ q from
      (pow_identity hq1 hu0).symm]
    rw [div_le_div_iff_of_pos_right hupos]
    exact le_trans hD (mul_le_mul_of_nonneg_left hF (by positivity))
  -- Step 2: decay of the geometric factor at `2q ≤ u`.
  have hbase : 2 * (q : ℝ) / (Real.exp 1 * u) ≤ 1 / Real.exp 1 := by
    rw [div_le_div_iff₀ (by positivity) hE]
    nlinarith [hqle, hE]
  have hpow : (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q ≤ (1 / Real.exp 1) ^ q :=
    pow_le_pow_left₀ (by positivity) hbase q
  have hexpq : (1 / Real.exp 1) ^ q = Real.exp (-(q : ℝ)) := by
    rw [div_pow, one_pow, one_div, ← Real.exp_nat_mul, mul_one, ← Real.exp_neg]
  have hsqrt : Real.sqrt q ≤ Real.sqrt (u / 2) := Real.sqrt_le_sqrt hqle
  have hdecay : Real.exp (-(q : ℝ)) ≤ Real.exp (1 - u / 2) := by
    rw [Real.exp_le_exp]
    linarith
  -- Step 3: chain the decay into the target.
  have hb1 : Real.exp 1 / 2 * Real.sqrt q * (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q
      ≤ Real.exp 1 / 2 * Real.sqrt (u / 2) * Real.exp (1 - u / 2) := by
    have h1 : Real.exp 1 / 2 * Real.sqrt q * (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q
        ≤ Real.exp 1 / 2 * Real.sqrt q * Real.exp (-(q : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_trans hpow hexpq.le) (by positivity)
    have h2 : Real.exp 1 / 2 * Real.sqrt q * Real.exp (-(q : ℝ))
        ≤ Real.exp 1 / 2 * Real.sqrt (u / 2) * Real.exp (1 - u / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hdecay
        (Real.exp_pos _).le (by positivity)
    linarith [h1, h2]
  have hval : Real.exp 1 / 2 * Real.sqrt (u / 2) * Real.exp (1 - u / 2) =
      Real.exp 2 / 2 * Real.sqrt (u / 2) * Real.exp (-(u / 2)) := by
    have h1 : Real.exp (1 - u / 2) = Real.exp 1 * Real.exp (-(u / 2)) := by
      rw [sub_eq_add_neg, ← Real.exp_add]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [h1, h2]
    ring
  -- Step 4: compare squares, reducing to `e² u ≤ 4 exp(u/4)`.
  have hleft : (Real.exp 2 / 2 * Real.sqrt (u / 2) * Real.exp (-(u / 2))) ^ 2
      = Real.exp 4 / 4 * (u / 2) * Real.exp (-u) := by
    have h1 : (Real.exp 2 / 2) ^ 2 = Real.exp 4 / 4 := by
      rw [div_pow, show Real.exp 2 ^ 2 = Real.exp 4 by rw [← Real.exp_nat_mul]; norm_num]
      norm_num
    have h2 : (Real.sqrt (u / 2)) ^ 2 = u / 2 := Real.sq_sqrt (by positivity)
    have h3 : (Real.exp (-(u / 2))) ^ 2 = Real.exp (-u) := by
      rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(u / 2)) = -u by ring]
    calc (Real.exp 2 / 2 * Real.sqrt (u / 2) * Real.exp (-(u / 2))) ^ 2
        = (Real.exp 2 / 2) ^ 2 * (Real.sqrt (u / 2)) ^ 2 *
            (Real.exp (-(u / 2))) ^ 2 := by rw [mul_pow, mul_pow]
      _ = Real.exp 4 / 4 * (u / 2) * Real.exp (-u) := by rw [h1, h2, h3]
  have hright : (Real.sqrt (2 / u) * Real.exp (-(u / 4))) ^ 2
      = 2 / u * Real.exp (-(u / 2)) := by
    have h1 : (Real.sqrt (2 / u)) ^ 2 = 2 / u := Real.sq_sqrt (by positivity)
    have h2 : (Real.exp (-(u / 4))) ^ 2 = Real.exp (-(u / 2)) := by
      rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(u / 4)) = -(u / 2) by ring]
    rw [mul_pow, h1, h2]
  have hfin : (Real.exp 2 / 2 * Real.sqrt (u / 2) * Real.exp (-(u / 2))) ^ 2 ≤
      (Real.sqrt (2 / u) * Real.exp (-(u / 4))) ^ 2 := by
    rw [hleft, hright]
    have hkey : Real.exp 2 * u ≤ 4 * Real.exp (u / 4) := exp_sq_mul_le hu
    have hkey2 : Real.exp 4 * u ^ 2 ≤ 16 * Real.exp (u / 2) := by
      calc Real.exp 4 * u ^ 2 = (Real.exp 2 * u) ^ 2 := by
            rw [mul_pow,
              show Real.exp 2 ^ 2 = Real.exp 4 by rw [← Real.exp_nat_mul]; norm_num]
        _ ≤ (4 * Real.exp (u / 4)) ^ 2 := pow_le_pow_left₀ (by positivity) hkey 2
        _ = 16 * Real.exp (u / 2) := by
            rw [mul_pow,
              show Real.exp (u / 4) ^ 2 = Real.exp (u / 2) by
                rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (u / 4) = u / 2 by ring]]
            norm_num
    have hstep1 : Real.exp 4 * u / 8 ≤ 2 * Real.exp (u / 2) / u := by
      rw [div_le_div_iff₀ (by norm_num) hu0]
      nlinarith [hkey2]
    have hmul := mul_le_mul_of_nonneg_right hstep1 (Real.exp_pos (-u)).le
    have hrew : 2 * Real.exp (u / 2) / u * Real.exp (-u) = 2 / u * Real.exp (-(u / 2)) := by
      have h1 : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-(u / 2)) := by
        rw [← Real.exp_add, show u / 2 + -u = -(u / 2) by ring]
      calc 2 * Real.exp (u / 2) / u * Real.exp (-u)
          = 2 * Real.exp (u / 2) * Real.exp (-u) / u := by rw [div_mul_eq_mul_div]
        _ = 2 * (Real.exp (u / 2) * Real.exp (-u)) / u := by rw [mul_assoc]
        _ = 2 * Real.exp (-(u / 2)) / u := by rw [h1]
        _ = 2 / u * Real.exp (-(u / 2)) := by ring
    rw [hrew] at hmul
    calc Real.exp 4 / 4 * (u / 2) * Real.exp (-u)
        = Real.exp 4 * u / 8 * Real.exp (-u) := by ring
      _ ≤ 2 / u * Real.exp (-(u / 2)) := hmul
  have hsq : (Real.exp 1 / 2 * Real.sqrt q * (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q) ^ 2 ≤
      (Real.sqrt (2 / u) * Real.exp (-(u / 4))) ^ 2 := by
    calc (Real.exp 1 / 2 * Real.sqrt q * (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q) ^ 2
        ≤ (Real.exp 1 / 2 * Real.sqrt (u / 2) * Real.exp (1 - u / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hb1 2
      _ = (Real.exp 2 / 2 * Real.sqrt (u / 2) * Real.exp (-(u / 2))) ^ 2 := by rw [hval]
      _ ≤ (Real.sqrt (2 / u) * Real.exp (-(u / 4))) ^ 2 := hfin
  have hnonneg1 : (0 : ℝ) ≤
      Real.exp 1 / 2 * Real.sqrt q * (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (by positivity)
  have hnonneg2 : (0 : ℝ) ≤ Real.sqrt (2 / u) * Real.exp (-(u / 4)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  calc (oddDFact q : ℝ) / u ^ q
      ≤ Real.exp 1 / 2 * Real.sqrt q * (2 * (q : ℝ) / (Real.exp 1 * u)) ^ q := hstep
    _ ≤ Real.sqrt (2 / u) * Real.exp (-(u / 4)) :=
        (pow_le_pow_iff_left₀ hnonneg1 hnonneg2 (by norm_num : (2 : ℕ) ≠ 0)).mp hsq

/-! ## Transferring the scale inequality to the Markov bound -/

/-- `sqrt m · x / m = x / sqrt m` for `m > 0`. -/
theorem sqrt_mul_div_self {m : ℝ} (hm : 0 < m) (x : ℝ) :
    Real.sqrt m * x / m = x / Real.sqrt m := by
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  have hne : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  rw [div_eq_div_iff hm.ne' hne]
  calc Real.sqrt m * x * Real.sqrt m = x * (Real.sqrt m * Real.sqrt m) := by ring
    _ = x * m := by rw [hs]

/-- The right-hand side of the displayed tail in terms of the scale `u = n/m²`:
`sqrt(2m/n) exp(-n/(4m²)) = (1/m) sqrt m sqrt(2/u) exp(-u/4)`. -/
theorem tail_rhs_eq {m n u : ℝ} (hm : 0 < m) (hn : 0 < n) (hu : u = n / m ^ 2) :
    Real.sqrt (2 * m / n) * Real.exp (-(n / (4 * m ^ 2))) =
      Real.sqrt m * (Real.sqrt (2 / u) * Real.exp (-(u / 4))) / m := by
  have hu0 : 0 < u := by rw [hu]; positivity
  have h1 : 2 * m / n = 2 / (u * m) := by
    rw [hu]; field_simp
  have h2 : n / (4 * m ^ 2) = u / 4 := by
    rw [hu]; field_simp
  rw [h1, h2]
  have hs : Real.sqrt (2 / (u * m)) = Real.sqrt (2 / u) / Real.sqrt m := by
    rw [show 2 / (u * m) = (2 / u) / m by field_simp]
    exact Real.sqrt_div (by positivity) m
  rw [hs, sqrt_mul_div_self hm (Real.sqrt (2 / u) * Real.exp (-(u / 4)))]
  ring

/-- **The Markov bound at order `q` is below the displayed tail**, given the scale inequality
`(2q-3)!! / u^q ≤ sqrt m (sqrt(2/u) exp(-u/4))` at `u = n/m²`. -/
theorem markov_quantity_le {m n u : ℝ} (hm : 1 ≤ m) (hn : 0 < n) (hu : u = n / m ^ 2)
    {q : ℕ} (hq : 1 ≤ q)
    (hscale : (oddDFact q : ℝ) / u ^ q ≤
      Real.sqrt m * (Real.sqrt (2 / u) * Real.exp (-(u / 4)))) :
    (oddDFact q : ℝ) * m ^ (2 * q - 1) / n ^ q ≤
      Real.sqrt (2 * m / n) * Real.exp (-(n / (4 * m ^ 2))) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hu0 : 0 < u := by rw [hu]; positivity
  have hL : (oddDFact q : ℝ) * m ^ (2 * q - 1) / n ^ q
      = (oddDFact q : ℝ) / u ^ q / m := by
    have hmq : (m : ℝ) ^ (2 * q) = m ^ (2 * q - 1) * m := by
      conv_lhs => rw [show 2 * q = 2 * q - 1 + 1 by omega]
      rw [pow_succ]
    have hnm : n = u * m ^ 2 := by rw [hu]; field_simp
    rw [hnm, mul_pow, show (m ^ 2) ^ q = m ^ (2 * q) by rw [← pow_mul], hmq]
    have hp : (0 : ℝ) < m ^ (2 * q - 1) := pow_pos hmpos _
    have huq : (0 : ℝ) < u ^ q := pow_pos hu0 q
    field_simp
  rw [hL, tail_rhs_eq hmpos hn hu]
  exact div_le_div_of_nonneg_right hscale hmpos.le

/-! ## Existence of an order satisfying the scale inequality -/

/-- The numerical core of the `u ≤ 1`, `u m ≥ 1` regime, by squaring:
`1/u ≤ sqrt m · sqrt(2/u) exp(-u/4)` when `1 ≤ u m` and `u ≤ 1`. -/
theorem scale_one {u m : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hum : 1 ≤ u * m) :
    (1 : ℝ) / u ≤ Real.sqrt m * (Real.sqrt (2 / u) * Real.exp (-(u / 4))) := by
  have hmpos : 0 < m := by nlinarith [hu0, hum]
  have hX : (Real.sqrt m * (Real.sqrt (2 / u) * Real.exp (-(u / 4)))) ^ 2
      = m * (2 / u) * Real.exp (-(u / 2)) := by
    have h1 : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt hmpos.le
    have h2 : (Real.sqrt (2 / u)) ^ 2 = 2 / u := Real.sq_sqrt (by positivity)
    have h3 : (Real.exp (-(u / 4))) ^ 2 = Real.exp (-(u / 2)) := by
      rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(u / 4)) = -(u / 2) by ring]
    rw [show Real.sqrt m * (Real.sqrt (2 / u) * Real.exp (-(u / 4)))
        = Real.sqrt m * Real.sqrt (2 / u) * Real.exp (-(u / 4)) by ring,
      mul_pow, mul_pow, h1, h2, h3]
  have hexp2 : Real.exp (u / 2) ≤ 2 := by
    have hle : Real.exp (u / 2) ≤ Real.exp (1 / 2) := by
      rw [Real.exp_le_exp]; linarith
    have h2 : Real.exp (1 / 2) ≤ 2 :=
      (Real.le_log_iff_exp_le (y := 2) (by norm_num : (0 : ℝ) < 2)).mp (by
        have := Real.log_two_gt_d9
        linarith)
    linarith
  have hkey : (1 : ℝ) ≤ 2 * u * m * Real.exp (-(u / 2)) := by
    have he : (0 : ℝ) < Real.exp (-(u / 2)) := Real.exp_pos _
    have h1 : Real.exp (u / 2) * Real.exp (-(u / 2)) ≤ 2 * u * m * Real.exp (-(u / 2)) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hexp2, hum]) he.le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h1
  have hstep : 1 / u ^ 2 ≤ m * (2 / u) * Real.exp (-(u / 2)) := by
    have hupos : (0 : ℝ) < u ^ 2 := by positivity
    calc 1 / u ^ 2 = 1 * (1 / u ^ 2) := (one_mul _).symm
      _ ≤ (2 * u * m * Real.exp (-(u / 2))) * (1 / u ^ 2) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = m * (2 / u) * Real.exp (-(u / 2)) := by
          field_simp
  have hgoal : (1 / u) ^ 2 ≤ (Real.sqrt m * (Real.sqrt (2 / u) * Real.exp (-(u / 4)))) ^ 2 := by
    rw [hX, div_pow, one_pow]
    exact hstep
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (2 : ℕ) ≠ 0)).mp hgoal

/-- **Existence of an order `q ≥ 1` with the scale inequality**, for every `m ≥ 1`
and `n ≥ 1`, either because the displayed tail already exceeds `1` or at one of the four
regimes. -/
theorem exists_scale {m n : ℝ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (1 ≤ Real.sqrt (2 * m / n) * Real.exp (-(n / (4 * m ^ 2)))) ∨
      ∃ q : ℕ, 1 ≤ q ∧ (oddDFact q : ℝ) / (n / m ^ 2) ^ q ≤
        Real.sqrt m * (Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4))) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hsm : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm
  by_cases hA : n / m < 1
  · left
    have hnm : n < m := by
      rw [div_lt_one hmpos] at hA
      exact hA
    have h1 : 2 < 2 * m / n := by
      rw [lt_div_iff₀ hnpos]
      nlinarith
    have h2 : n / (4 * m ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h3 : Real.exp (-(1 / 4)) ≤ Real.exp (-(n / (4 * m ^ 2))) := by
      rw [Real.exp_le_exp]; linarith
    calc (1 : ℝ) ≤ Real.sqrt 2 * Real.exp (-(1 / 4)) := one_le_sqrt_two_mul_exp_neg_quarter
      _ ≤ Real.sqrt (2 * m / n) * Real.exp (-(n / (4 * m ^ 2))) :=
          mul_le_mul (Real.sqrt_le_sqrt h1.le) h3 (Real.exp_pos _).le (Real.sqrt_nonneg _)
  · have hA1 : 1 ≤ n / m := not_lt.mp hA
    have hum : 1 ≤ (n / m ^ 2) * m := by
      rw [show (n / m ^ 2) * m = n / m by field_simp]
      exact hA1
    have hu0 : (0 : ℝ) < n / m ^ 2 := by positivity
    by_cases hu1 : n / m ^ 2 ≤ 1
    · refine Or.inr ⟨1, le_rfl, ?_⟩
      rw [pow_one, oddDFact_one, Nat.cast_one]
      calc (1 : ℝ) / (n / m ^ 2) ≤ Real.sqrt m * (Real.sqrt (2 / (n / m ^ 2)) *
            Real.exp (-((n / m ^ 2) / 4))) := scale_one hu0 hu1 hum
        _ = Real.sqrt m * (Real.sqrt (2 / (n / m ^ 2)) *
            Real.exp (-((n / m ^ 2) / 4))) := rfl
    · have hu1' : 1 < n / m ^ 2 := not_le.mp hu1
      by_cases hu6 : n / m ^ 2 ≤ 6
      · refine Or.inr ⟨2, by norm_num, ?_⟩
        rw [oddDFact_two, Nat.cast_one]
        have h2 := scale_two hu1'.le hu6
        have hu2 : (0 : ℝ) < (n / m ^ 2) ^ 2 := by positivity
        have hs2 : (1 : ℝ) / (n / m ^ 2) ^ 2 ≤
            Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4)) := by
          rw [div_le_iff₀ hu2]
          calc (1 : ℝ) ≤ (n / m ^ 2) ^ 2 *
                (Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4))) := h2
            _ = Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4)) *
                (n / m ^ 2) ^ 2 := by ring
        calc (1 : ℝ) / (n / m ^ 2) ^ 2
            ≤ Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4)) := hs2
          _ = 1 * (Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4))) :=
              (one_mul _).symm
          _ ≤ Real.sqrt m * (Real.sqrt (2 / (n / m ^ 2)) *
                Real.exp (-((n / m ^ 2) / 4))) :=
              mul_le_mul_of_nonneg_right hsm (by positivity)
      · have hu6' : 6 < n / m ^ 2 := not_le.mp hu6
        by_cases hu16 : n / m ^ 2 ≤ 16
        · refine Or.inr ⟨5, by norm_num, ?_⟩
          rw [oddDFact_five]
          have h5 := scale_five hu6'.le hu16
          have hu5 : (0 : ℝ) < (n / m ^ 2) ^ 5 := by positivity
          have hs5 : (105 : ℝ) / (n / m ^ 2) ^ 5 ≤
              Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4)) := by
            rw [div_le_iff₀ hu5]
            calc (105 : ℝ) ≤ (n / m ^ 2) ^ 5 *
                  (Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4))) := h5
              _ = Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4)) *
                  (n / m ^ 2) ^ 5 := by ring
          calc (105 : ℝ) / (n / m ^ 2) ^ 5
              ≤ Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4)) := hs5
            _ = 1 * (Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4))) :=
                (one_mul _).symm
            _ ≤ Real.sqrt m * (Real.sqrt (2 / (n / m ^ 2)) *
                  Real.exp (-((n / m ^ 2) / 4))) :=
                mul_le_mul_of_nonneg_right hsm (by positivity)
        · have hu16' : 16 < n / m ^ 2 := not_le.mp hu16
          refine Or.inr ⟨⌊n / m ^ 2 / 2⌋₊, Nat.floor_pos.mpr (by linarith), ?_⟩
          rw [show n / m ^ 2 / 2 = (n / m ^ 2) / 2 by ring]
          refine le_trans (scale_floor hu16'.le) ?_
          calc Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4))
              = 1 * (Real.sqrt (2 / (n / m ^ 2)) * Real.exp (-((n / m ^ 2) / 4))) :=
                (one_mul _).symm
            _ ≤ Real.sqrt m * (Real.sqrt (2 / (n / m ^ 2)) *
                  Real.exp (-((n / m ^ 2) / 4))) :=
                mul_le_mul_of_nonneg_right hsm (by positivity)

/-! ## Assembly at the actual truncated law -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open PercLib.CriticalLRP
open PercLib.CriticalLRP.Orchestration

/-- The bridge to the paper's normalisation: `oddDFact q = (2q-3)!! =
VolumeMoments.M (q-1)`, the product of the odd integers below `2q-2`. -/
theorem oddDFact_eq_VolumeMoments_M (q : ℕ) :
    oddDFact q = PercLib.CriticalLRP.VolumeMoments.M (q - 1) := rfl

/-- **Markov at order `q` at the actual truncated law**, in the real form the tail needs:
with `m = (E_{β_c,r}|K|).toReal`,
`P_{β_c,r}(|K| ≥ n) ≤ (2q-3)!! m^{2q-1} / n^q`. -/
theorem cutLaw_tail_le_markov (M : SourceModelData) (r : ℝ)
    (h1 : M.cutMoment 1 r ≠ ⊤) {q : ℕ} (hq : 1 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    (M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
      ENNReal.ofReal ((oddDFact q : ℝ) * (M.cutMoment 1 r).toReal ^ (2 * q - 1) /
        (n : ℝ) ^ q) := by
  set m0 : ℝ := (M.cutMoment 1 r).toReal with hm0def
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hcut1 : M.cutMoment 1 r = ENNReal.ofReal m0 := (ENNReal.ofReal_toReal h1).symm
  have hmeas : Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) ^ q :=
    (measurable_clusterVol (0 : M.V)).pow measurable_const
  have hsubset : {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ⊆
      {ω : Config M.V | (n : ℝ≥0∞) ^ q ≤ clusterVol ω (0 : M.V) ^ q} := by
    intro ω hω
    exact pow_le_pow_left₀ (zero_le : (0 : ℝ≥0∞) ≤ (n : ℝ≥0∞)) hω q
  have hmark := mul_meas_ge_le_lintegral (μ := M.cutLaw r) hmeas ((n : ℝ≥0∞) ^ q)
  have hne0 : (n : ℝ≥0∞) ^ q ≠ 0 := pow_ne_zero _ hnne
  have hnetop : (n : ℝ≥0∞) ^ q ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hstep1 : (M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ ((n : ℝ≥0∞) ^ q)⁻¹ * M.cutMoment q r := by
    refine le_trans (measure_mono hsubset) ?_
    calc (M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ^ q ≤ clusterVol ω (0 : M.V) ^ q}
        = ((n : ℝ≥0∞) ^ q)⁻¹ * ((n : ℝ≥0∞) ^ q *
            (M.cutLaw r) {ω : Config M.V |
              (n : ℝ≥0∞) ^ q ≤ clusterVol ω (0 : M.V) ^ q}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
      _ ≤ ((n : ℝ≥0∞) ^ q)⁻¹ * ∫⁻ ω, clusterVol ω (0 : M.V) ^ q ∂(M.cutLaw r) :=
          mul_le_mul_right hmark _
      _ = ((n : ℝ≥0∞) ^ q)⁻¹ * M.cutMoment q r := rfl
  have hstep2 : M.cutMoment q r ≤ ENNReal.ofReal ((oddDFact q : ℝ) * m0 ^ (2 * q - 1)) := by
    refine le_trans (cutMoment_le_dfactorial M r hq) ?_
    have hbridge : (PercLib.CriticalLRP.VolumeMoments.M (q - 1) : ℝ≥0∞) =
        ENNReal.ofReal (oddDFact q : ℝ) := by
      rw [oddDFact_eq_VolumeMoments_M]
      simp
    rw [hbridge, hcut1, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity)]
  have hstep3 : ((n : ℝ≥0∞) ^ q)⁻¹ *
        ENNReal.ofReal ((oddDFact q : ℝ) * m0 ^ (2 * q - 1)) =
      ENNReal.ofReal ((oddDFact q : ℝ) * m0 ^ (2 * q - 1) / (n : ℝ) ^ q) := by
    have hj : (n : ℝ≥0∞) ^ q = ENNReal.ofReal ((n : ℝ) ^ q) := by
      rw [← ENNReal.ofReal_natCast n, ENNReal.ofReal_pow (by positivity)]
    have hi : ((n : ℝ≥0∞) ^ q)⁻¹ = ENNReal.ofReal (((n : ℝ) ^ q)⁻¹) := by
      rw [hj, ENNReal.ofReal_inv_of_pos (by positivity)]
    rw [hi, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  calc (M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ ((n : ℝ≥0∞) ^ q)⁻¹ * M.cutMoment q r := hstep1
    _ ≤ ((n : ℝ≥0∞) ^ q)⁻¹ * ENNReal.ofReal ((oddDFact q : ℝ) * m0 ^ (2 * q - 1)) :=
        mul_le_mul_right hstep2 _
    _ = ENNReal.ofReal ((oddDFact q : ℝ) * m0 ^ (2 * q - 1) / (n : ℝ) ^ q) := hstep3

/-- **The displayed single-cluster tail of Corollary I.4.14, discharged.**

Hutchcroft, arXiv:2508.18807v1, p. 42: for every `n ≥ 1`,
`P_{β_c,r}(|K| ≥ n) ≤ sqrt(2m/n) exp(-n/(4m²))` with
`m = E_{β_c,r}|K| = (M.cutMoment 1 r).toReal`.

The only hypothesis is that this mean is finite (`M.cutMoment 1 r ≠ ⊤`), which is the
first-moment input `E_{β_c,r}|K| ⪯ r^α` of Proposition I.4.2 in the paper's Case 1 setting.
The proof is the tree-graph moment bound `cutMoment_le_dfactorial` followed by Markov
(`cutLaw_tail_le_markov`) at an order `q` chosen by `exists_scale`. -/
theorem singleClusterTail_cutMoment_one (M : SourceModelData) (r : ℝ)
    (h1 : M.cutMoment 1 r ≠ ⊤) :
    PercLib.CriticalLRP.CaseOne.SingleClusterTail M r (M.cutMoment 1 r).toReal := by
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm1 : (1 : ℝ) ≤ (M.cutMoment 1 r).toReal := by
    have hle : (1 : ℝ≥0∞) ≤ M.cutMoment 1 r := M.one_le_cutMoment 1 r
    have h := ENNReal.toReal_mono h1 hle
    simpa using h
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rcases exists_scale hm1 hn1 with htriv | ⟨q, hq1, hscale⟩
  · have hmeas_univ :
        (M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤ 1 := by
      calc (M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
          ≤ (M.cutLaw r) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    refine le_trans hmeas_univ ?_
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal htriv
  · refine le_trans (cutLaw_tail_le_markov M r h1 hq1 hn) (ENNReal.ofReal_le_ofReal ?_)
    exact markov_quantity_le hm1 hnpos rfl hq1 hscale


/-! ## Case 1 of Corollary I.4.14 with the tail discharged -/

/-- **`M_r ⪯ (E_{β_c,r}|K|)² log r` with no tail hypothesis**: the displayed single-cluster
tail is now a theorem, so the only remaining hypothesis is finiteness of the first cutoff
moment at every radius. -/
theorem mr_le_cutMoment_one_finite (M : SourceModelData) (Bc : ℝ) (hBc : 0 < Bc)
    (hball : ∀ r : ℝ, 2 ≤ r → ((M.ball r).ncard : ℝ) ≤ Bc * r ^ (M.d : ℝ))
    (h1 : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 2 ≤ r →
      (M.Mr r : ℝ) ≤ C * ((M.cutMoment 1 r).toReal) ^ 2 * Real.log r := by
  refine PercLib.CriticalLRP.CaseOne.mr_le_cutMoment_one M Bc hBc hball ?_ ?_
  · intro r _
    have h := ENNReal.toReal_mono (h1 r) (M.one_le_cutMoment 1 r)
    simpa using h
  · intro r _
    exact singleClusterTail_cutMoment_one M r (h1 r)

/-- **Case 1 of Corollary I.4.14, capstone with the tail discharged**: `3α < d`, finiteness of
`E_{β_c,r}|K|` at every radius and `E_{β_c,r}|K| ≤ C₁ r^α` give `Hydro M`. -/
theorem hydro_of_cutMoment_one_finite (M : SourceModelData) (_hα : 0 < M.α)
    (hd : 3 * M.α < (M.d : ℝ)) (h1 : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤)
    (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hm : ∀ᶠ r : ℝ in atTop, (M.cutMoment 1 r).toReal ≤ C₁ * r ^ M.α) :
    Hydro M := by
  refine PercLib.CriticalLRP.CaseOne.hydro_of_cutMoment_one' M _hα hd ?_ ?_ C₁ hC₁ hm
  · intro r _
    have h := ENNReal.toReal_mono (h1 r) (M.one_le_cutMoment 1 r)
    simpa using h
  · intro r _
    exact singleClusterTail_cutMoment_one M r (h1 r)

/-- **Case 1 of Corollary I.4.14 from the paper's first-moment input alone.**

`3α < d` and the first-moment asymptotic `E_{β_c,r}|K| ~ c r^α` (with `c > 0`, which is the
`E_{β_c,r}|K| ⪯ r^α` input of Proposition I.4.2, in its sharp form) imply `Hydro M`.

This removes the two remaining hypotheses `hm1` (`1 ≤ m`) and `htail` (`SingleClusterTail`) of
production's `CaseOne.hydro_of_cutMoment_one'`: `hm1` follows from `|K| ≥ 1` plus finiteness,
finiteness follows from the asymptotic, and the tail is `singleClusterTail_cutMoment_one`. -/
theorem hydro_of_firstMoment_asymptotic (M : SourceModelData) (_hα : 0 < M.α)
    (hd : 3 * M.α < (M.d : ℝ)) {c : ℝ} (hc : 0 < c)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal / (c * r ^ M.α)) atTop (𝓝 1)) :
    Hydro M := by
  have hfin : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤ :=
    SourceModelData.cutMoment_one_ne_top_of_asymptotic M hP
  have hm : ∀ᶠ r : ℝ in atTop, (M.cutMoment 1 r).toReal ≤ (2 * c) * r ^ M.α := by
    have h := hP.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hrpow : (0 : ℝ) < r ^ M.α := Real.rpow_pos_of_pos hr0 _
    have hpos : (0 : ℝ) < c * r ^ M.α := by positivity
    rw [div_lt_iff₀ hpos] at hr
    calc (M.cutMoment 1 r).toReal = (M.cutMassAt r 0).toReal := by
          rw [M.cutMassAt_zero_eq_cutMoment]
      _ ≤ 2 * (c * r ^ M.α) := le_of_lt hr
      _ = 2 * c * r ^ M.α := by ring
  exact hydro_of_cutMoment_one_finite M _hα hd hfin (2 * c) (by positivity) hm

end CaseOneTail

#print axioms CaseOneTail.hydro_of_firstMoment_asymptotic

#print axioms CaseOneTail.mr_le_cutMoment_one_finite
#print axioms CaseOneTail.hydro_of_cutMoment_one_finite

#print axioms CaseOneTail.oddDFact_eq_doubleFactorial
#print axioms CaseOneTail.scale_two
#print axioms CaseOneTail.scale_five
#print axioms CaseOneTail.scale_floor
#print axioms CaseOneTail.scale_one
#print axioms CaseOneTail.exists_scale
#print axioms CaseOneTail.markov_quantity_le
#print axioms CaseOneTail.cutLaw_tail_le_markov
#print axioms CaseOneTail.singleClusterTail_cutMoment_one
