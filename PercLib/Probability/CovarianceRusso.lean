/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-76: the covariance form of the finite Russo formula. The covariance of an observable
with a coordinate indicator is `qₑ(1-qₑ)` times the expected forced increment, and in
intensity coordinates the Russo derivative is a sum of covariances with the coefficients
`J/(1 - e^{-βJ})`. Uses the finite-profile vocabulary of Russo.lean; no new definition.
-/
module

public import PercLib.Probability.RussoIntegral

@[expose] public section
noncomputable section

namespace PercLib.Probability.FiniteProfile
open Finset
open scoped Classical
variable {E : Type*} [Fintype E]

private lemma sum_weight_eq_one (q : E → ℝ) : ∑ ω, weight q ω = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun e (b : Bool) => if b then q e else 1 - q e)]
  simp

omit [Fintype E] in
private lemma expectation_force_flip (e : E) (b : Bool) (f : (E → Bool) → ℝ) (ω : E → Bool) :
    f (force e b (flip e ω)) = f (force e b ω) := by
  rw [force_flip]

/-- Splitting the expectation along one coordinate. -/
theorem expectation_split (q : E → ℝ) (e : E) (f : (E → Bool) → ℝ) :
    expectation q f = q e * expectation q (fun ω => f (force e true ω)) +
      (1 - q e) * expectation q (fun ω => f (force e false ω)) := by
  have h1 := expectation_open_coordinate q e (fun ω => f (force e true ω))
    (expectation_force_flip e true f)
  have h0 := expectation_open_coordinate q e (fun ω => f (force e false ω))
    (expectation_force_flip e false f)
  have hf : ∀ ω, f ω = (if ω e then f (force e true ω) else 0) +
      (f (force e false ω) - if ω e then f (force e false ω) else 0) := by
    intro ω
    cases h : ω e
    · have : force e false ω = ω := by
        simp only [force, ← h, Function.update_eq_self]
      simp [this]
    · have : force e true ω = ω := by
        simp only [force, ← h, Function.update_eq_self]
      simp [this]
  have hsum : expectation q f =
      expectation q (fun ω => if ω e then f (force e true ω) else 0) +
        (expectation q (fun ω => f (force e false ω)) -
          expectation q (fun ω => if ω e then f (force e false ω) else 0)) := by
    unfold expectation
    rw [← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by rw [hf ω]; ring
  rw [hsum, h1, h0]
  ring

/-- The expectation of a coordinate indicator is the coordinate's parameter. -/
theorem expectation_coordinate (q : E → ℝ) (e : E) :
    expectation q (fun ω => if ω e then 1 else 0) = q e := by
  have h := expectation_open_coordinate q e (fun _ => 1) (fun _ => rfl)
  rw [h]
  simp [expectation, sum_weight_eq_one]

/-- **VVDC.** `Cov_q(f, Xₑ) = qₑ(1-qₑ) E_q[Δₑ f]`, for every real profile (in particular
every profile in `[0,1]^E`, endpoints included). -/
theorem covariance_coordinate (q : E → ℝ) (e : E) (f : (E → Bool) → ℝ) :
    expectation q (fun ω => f ω * if ω e then 1 else 0) -
        expectation q f * expectation q (fun ω => if ω e then 1 else 0) =
      q e * (1 - q e) * expectation q (difference e f) := by
  have hprod : expectation q (fun ω => f ω * if ω e then 1 else 0) =
      q e * expectation q (fun ω => f (force e true ω)) := by
    rw [← expectation_open_coordinate q e (fun ω => f (force e true ω))
      (expectation_force_flip e true f)]
    congr 1
    funext ω
    cases h : ω e
    · simp
    · have : force e true ω = ω := by
        simp only [force, ← h, Function.update_eq_self]
      simp [this]
  have hdiff : expectation q (difference e f) =
      expectation q (fun ω => f (force e true ω)) -
        expectation q (fun ω => f (force e false ω)) := by
    simp only [expectation, difference, sub_mul, sum_sub_distrib]
  rw [hprod, expectation_coordinate, expectation_split q e f, hdiff]
  ring

omit [Fintype E] in
lemma force_false_le_force_true (e : E) (ω : E → Bool) :
    force e false ω ≤ force e true ω := by
  intro j
  by_cases h : j = e
  · subst h; simp [force]
  · simp [force, Function.update_of_ne h]

/-- For an increasing observable and a profile in `[0,1]^E` the covariance with each
coordinate indicator is nonnegative. -/
theorem covariance_coordinate_nonneg {q : E → ℝ} (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    (e : E) {f : (E → Bool) → ℝ} (hf : Monotone f) :
    0 ≤ expectation q (fun ω => f ω * if ω e then 1 else 0) -
        expectation q f * expectation q (fun ω => if ω e then 1 else 0) := by
  rw [covariance_coordinate]
  have hqe := hq e
  apply mul_nonneg (mul_nonneg hqe.1 (by linarith [hqe.2]))
  apply sum_nonneg
  intro ω _
  apply mul_nonneg
  · exact sub_nonneg.mpr (hf (force_false_le_force_true e ω))
  · exact prod_nonneg fun j _ => by
      have := hq j
      split_ifs
      · exact this.1
      · linarith [this.2]

/-- **DUYN**, derivative. For `q_β(e) = 1 - e^{-βJₑ}` with `Jₑ ≥ 0` and `β > 0`, the
derivative in `β` of `E_β[f]` is `∑_{e ∈ E₊} c_β(e) Cov_β(f, Xₑ)`, where
`E₊ = {e | Jₑ > 0}` and `c_β(e) = Jₑ/(1 - e^{-βJₑ})`. -/
theorem expectation_intensity_hasDerivAt_covariance (J : E → ℝ) (hJ : ∀ e, 0 ≤ J e)
    {β : ℝ} (hβ : 0 < β) (f : (E → Bool) → ℝ) :
    HasDerivAt (fun b => expectation (fun e => 1 - Real.exp (-b * J e)) f)
      (∑ e ∈ univ.filter (fun e => 0 < J e), J e / (1 - Real.exp (-β * J e)) *
        (expectation (fun j => 1 - Real.exp (-β * J j)) (fun ω => f ω * if ω e then 1 else 0) -
          expectation (fun j => 1 - Real.exp (-β * J j)) f *
            expectation (fun j => 1 - Real.exp (-β * J j)) (fun ω => if ω e then 1 else 0)))
      β := by
  convert expectation_intensity_hasDerivAt J β f using 1
  rw [sum_filter]
  apply sum_congr rfl
  intro e _
  rw [covariance_coordinate]
  split_ifs with he
  · have hpos : 0 < 1 - Real.exp (-β * J e) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      nlinarith
    generalize Real.exp (-β * J e) = X at hpos ⊢
    have hne : 1 - X ≠ 0 := hpos.ne'
    field_simp
    ring
  · have : J e = 0 := le_antisymm (not_lt.mp he) (hJ e)
    simp [this]

/-- **DUYN**, coefficient bounds. For `Jₑ > 0` and `β > 0`: `c_β(e) ≥ 1/β`, and
`0 < Jₑ/(e^{βJₑ} - 1) = e^{-βJₑ} c_β(e) ≤ c_β(e)`. -/
theorem intensity_coefficient_bounds {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    1 / β ≤ J / (1 - Real.exp (-β * J)) ∧
    0 < J / (Real.exp (β * J) - 1) ∧
    J / (Real.exp (β * J) - 1) = Real.exp (-β * J) * (J / (1 - Real.exp (-β * J))) ∧
    J / (Real.exp (β * J) - 1) ≤ J / (1 - Real.exp (-β * J)) := by
  have hx : 0 < β * J := mul_pos hβ hJ
  have hd : 0 < 1 - Real.exp (-β * J) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith
  have hd' : 0 < Real.exp (β * J) - 1 := by
    rw [sub_pos]
    exact Real.one_lt_exp_iff.mpr hx
  have hexp : Real.exp (-β * J) * Real.exp (β * J) = 1 := by
    rw [← Real.exp_add]; simp
  have heq : J / (Real.exp (β * J) - 1) = Real.exp (-β * J) * (J / (1 - Real.exp (-β * J))) := by
    rw [mul_div_assoc', div_eq_div_iff hd'.ne' hd.ne']
    linear_combination (-J) * hexp
  refine ⟨?_, div_pos hJ hd', heq, ?_⟩
  · rw [div_le_div_iff₀ hβ hd]
    have := Real.add_one_le_exp (-β * J)
    nlinarith
  · rw [heq]
    have hle : Real.exp (-β * J) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact mul_le_of_le_one_left (div_pos hJ hd).le hle

/-! ### Non-vacuity witnesses (D-5) -/

/-- One coordinate and `f = Xₑ`: VVDC reads `Var = q(1-q)`. -/
example (q : ℝ) :
    expectation (fun _ : Unit => q) (fun ω => (if ω () then (1 : ℝ) else 0) *
        if ω () then 1 else 0) -
      expectation (fun _ : Unit => q) (fun ω => if ω () then (1 : ℝ) else 0) ^ 2 =
      q * (1 - q) := by
  have h := covariance_coordinate (fun _ : Unit => q) () (fun ω => if ω () then 1 else 0)
  have hd : difference () (fun ω : Unit → Bool => if ω () then (1 : ℝ) else 0) = fun _ => 1 := by
    funext ω
    simp [difference, force]
  rw [hd, expectation_coordinate] at h
  have h1 : expectation (fun _ : Unit => q) (fun _ => (1 : ℝ)) = 1 := by
    simp [expectation, sum_weight_eq_one]
  rw [h1, mul_one] at h
  rw [sq, expectation_coordinate, h]

/-- The coefficient bounds apply, e.g. at `J = β = 1`. -/
example : 1 ≤ 1 / (1 - Real.exp (-1)) := by
  simpa using (intensity_coefficient_bounds (J := 1) (β := 1) one_pos one_pos).1

end PercLib.Probability.FiniteProfile
