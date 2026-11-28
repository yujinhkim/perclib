/-
Standalone development for swarm smwzuf8hm member m4: even moments of the standard Gaussian law
and the identification of the paper's `Q∞` (the law of `Z ^ 2`) with the chi-square law.
-/
module

public import PercLib.CriticalLRP.MomentProblem.ChiSquare
public import PercLib.CriticalLRP.Analysis.ChiSquareA3

/-!
# Even moments of the standard normal law, and `Q∞ = gammaMeasure (1/2) (1/2)`

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), proof of (I.1.7): the limit
law `Q∞` is introduced in Proposition I.3.2 as the law of `Z ^ 2` for a standard normal `Z`
(`PercLib.CriticalLRP.Anchor.Qinf`), while the moment-determinacy theorem
`PercLib.CriticalLRP.MomentProblem.eq_gammaMeasure_of_forall_moment_eq` is stated for
`gammaMeasure (1 / 2) (1 / 2)`. This file supplies the missing identification.

* `iteratedDeriv_gaussM_rec`: the moment recursion `m (n+2) = (n+1) * m n` for
  `M t = exp (t^2/2)`, obtained by differentiating `M' = t * M` and applying Leibniz;
* `iteratedDeriv_gaussM_even`: `M^{(2k)}(0) = (2k-1)!!`;
* `integral_pow_gaussianReal`: `∫ z, z ^ (2k) ∂(gaussianReal 0 1) = (2k-1)!!`, via
  `ProbabilityTheory.iteratedDeriv_mgf_zero`;
* `Qinf_eq_gammaMeasure`: `Measure.map (fun z => z ^ 2) (gaussianReal 0 1)` is
  `gammaMeasure (1/2) (1/2)`, by moment determinacy in the form
  `eq_gammaMeasure_of_forall_moment_eq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace SwarmM4

open PercLib.CriticalLRP.MomentProblem in
/-- `M t = exp (t ^ 2 / 2)`, the moment generating function of the standard normal law. -/
noncomputable def gaussM (t : ℝ) : ℝ := Real.exp (t ^ 2 / 2)

lemma contDiff_gaussM : ContDiff ℝ ⊤ gaussM := by
  unfold gaussM
  fun_prop

lemma deriv_gaussM : deriv gaussM = fun t => t * gaussM t := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 := h.div_const 2
    convert h2 using 1
    ring
  have h3 : HasDerivAt gaussM (Real.exp (t ^ 2 / 2) * t) t :=
    (Real.hasDerivAt_exp (t ^ 2 / 2)).comp t h1
  rw [h3.deriv]
  simp only [gaussM, mul_comm]

/-- The `i`-th derivative of the identity vanishes at `0` unless `i = 1`. -/
lemma iteratedDeriv_id_apply_zero {i : ℕ} (hi : i ≠ 1) :
    iteratedDeriv i (fun t : ℝ => t) 0 = 0 := by
  rcases i with _ | _ | i'
  · simp
  · exact absurd rfl hi
  · have h2 : iteratedDeriv (i' + 1 + 1) (fun t : ℝ => t)
        = iteratedDeriv i' (fun _ => (0 : ℝ)) := by
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      rw [show deriv (fun t : ℝ => t) = fun _ => (1 : ℝ) from by funext x; simp]
      simp
    rw [h2, iteratedDeriv_const]
    split_ifs with h
    · rfl
    · rfl

lemma iteratedDeriv_id_apply_one : iteratedDeriv 1 (fun t : ℝ => t) 0 = 1 := by
  simp

/-- The moment recursion `M^{(n+2)}(0) = (n+1) M^{(n)}(0)`. -/
lemma iteratedDeriv_gaussM_rec (n : ℕ) :
    iteratedDeriv (n + 2) gaussM 0 = (n + 1) * iteratedDeriv n gaussM 0 := by
  have hstep : iteratedDeriv (n + 2) gaussM = iteratedDeriv (n + 1) (deriv gaussM) := by
    have h := iteratedDeriv_succ' (n := n + 1) (f := gaussM)
    simpa [Nat.add_assoc] using h
  rw [hstep, deriv_gaussM]
  have hmul : (fun t : ℝ => t * gaussM t) = (fun t : ℝ => t) * gaussM := rfl
  rw [hmul]
  have hf : ContDiffAt ℝ (((n + 1 : ℕ)) : ℕ∞) (fun t : ℝ => t) 0 := contDiff_id.contDiffAt
  have hg : ContDiffAt ℝ (((n + 1 : ℕ)) : ℕ∞) gaussM 0 := contDiff_gaussM.contDiffAt.of_le le_top
  rw [iteratedDeriv_mul hf hg]
  rw [Finset.sum_eq_single 1]
  · rw [iteratedDeriv_id_apply_one]
    rw [show n + 1 - 1 = n from by omega, Nat.choose_one_right]
    push_cast
    ring
  · intro i _ hne
    rw [iteratedDeriv_id_apply_zero hne]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- `M^{(2k)}(0) = (2k-1)!!`. -/
lemma iteratedDeriv_gaussM_even (k : ℕ) :
    iteratedDeriv (2 * k) gaussM 0 = (PercLib.CriticalLRP.MomentProblem.oddFact k : ℝ) := by
  induction k with
  | zero => simp [gaussM]
  | succ k ih =>
    have h := iteratedDeriv_gaussM_rec (2 * k)
    have harg : 2 * k + 2 = 2 * (k + 1) := by ring
    rw [harg] at h
    rw [h, ih, PercLib.CriticalLRP.MomentProblem.oddFact_succ]
    push_cast
    ring

/-- **The `2k`-th moment of the standard normal law is `(2k-1)!!`.** -/
theorem integral_pow_gaussianReal (k : ℕ) :
    ∫ z, z ^ (2 * k) ∂(gaussianReal 0 1) = (PercLib.CriticalLRP.MomentProblem.oddFact k : ℝ) := by
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
    have huniv : integrableExpSet id (gaussianReal 0 1) = Set.univ := by
      ext t
      simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t
    rw [huniv, interior_univ]
    exact Set.mem_univ 0
  have hmgf : mgf id (gaussianReal 0 1) = gaussM := by
    funext t
    have hlaw : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) := HasLaw.id
    rw [mgf_gaussianReal hlaw t]
    simp [gaussM]
  have h := iteratedDeriv_mgf_zero hmem (2 * k)
  rw [hmgf, iteratedDeriv_gaussM_even] at h
  simpa using h.symm

/-- **The law of `Z ^ 2` for standard normal `Z` is the chi-square law with one degree of
freedom**, i.e. `gammaMeasure (1/2) (1/2)`, the limit law `Q∞` of Proposition I.3.2 in the
application of (I.1.7). The proof is moment determinacy
(`eq_gammaMeasure_of_forall_moment_eq`) applied to the even moments of the normal law. -/
theorem Qinf_eq_gammaMeasure :
    PercLib.CriticalLRP.Anchor.Qinf = gammaMeasure (1 / 2) (1 / 2) := by
  have hsupp : ∀ᵐ x ∂(PercLib.CriticalLRP.Anchor.Qinf), 0 ≤ x := by
    rw [ae_iff]
    rw [show {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 from by ext x; simp]
    rw [PercLib.CriticalLRP.Anchor.Qinf]
    rw [Measure.map_apply (f := fun z : ℝ => z ^ 2) (by fun_prop) measurableSet_Iio]
    have hempty : (fun z : ℝ => z ^ 2) ⁻¹' Set.Iio 0 = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      positivity
    rw [hempty, measure_empty]
  refine PercLib.CriticalLRP.MomentProblem.eq_gammaMeasure_of_forall_moment_eq hsupp ?_
  intro n
  rw [PercLib.CriticalLRP.MomentProblem.integral_pow_gammaMeasure_one_half n]
  rw [PercLib.CriticalLRP.Anchor.Qinf]
  rw [integral_map (φ := fun z : ℝ => z ^ 2) (by fun_prop)
    (by fun_prop : AEStronglyMeasurable
      (fun y : ℝ => y ^ n) (Measure.map (fun z : ℝ => z ^ 2) (gaussianReal 0 1)))]
  have hcongr : ∀ z : ℝ, (z ^ 2) ^ n = z ^ (2 * n) := by
    intro z
    rw [← pow_mul, mul_comm]
  simp only [hcongr]
  exact integral_pow_gaussianReal n

end SwarmM4

/-! ### Axiom audit -/

set_option linter.hashCommand false

#print axioms SwarmM4.Qinf_eq_gammaMeasure
#print axioms SwarmM4.integral_pow_gaussianReal
#print axioms SwarmM4.iteratedDeriv_gaussM_even
#print axioms SwarmM4.iteratedDeriv_gaussM_rec
