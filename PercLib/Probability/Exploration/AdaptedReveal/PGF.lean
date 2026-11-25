/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwpalb9h`, member m1, direction 1: the Bernoulli pgf consequence of
`lintegral_adapted_prod`.  This turns the adapted-revelation factorization into the exact
one-step estimate consumed by the generation induction of `PROOF.md` (accepted run
`smwp9xgrt`), with the *true* product-law weight (`prodBernoulli`), not an abstract weight.
-/
module

public import PercLib.Probability.Exploration.AdaptedReveal.Reveal

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open PercLib.Probability

namespace PercLib.Probability.AdaptedReveal

variable {ι St : Type*}

theorem powOpenFun_true (t : ℝ≥0∞) : powOpenFun t True = t := by simp [powOpenFun]

theorem powOpenFun_false (t : ℝ≥0∞) : powOpenFun t False = 1 := by simp [powOpenFun]

/-- `∏_{e ∈ S}` of the one-coordinate pgf factors is the pgf `t ^ #open`. -/
theorem prod_powOpen_eq_pow_openCount (S : Finset ι) (t : ℝ≥0∞) (ω : Set ι) :
    ∏ e ∈ S, powOpen t ω e = t ^ openCount S ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 : openCount (∅ : Finset ι) ω = 0 := rfl
    simp [h0]
  | insert a S ha ih =>
    have hcount : openCount (insert a S) ω
        = ((insert a S).filter (fun e => e ∈ ω)).card := rfl
    rw [hcount, Finset.filter_insert, Finset.prod_insert ha, ih]
    by_cases h : a ∈ ω
    · simp only [powOpen, h, powOpenFun_true, ite_true]
      rw [Finset.card_insert_of_notMem (by simp [ha]), pow_succ']
      rfl
    · simp only [powOpen, h, powOpenFun_false, ite_false, one_mul]
      rfl

/-- **One-coordinate pgf.** The expectation of `t` on an open coordinate and `1` on a
closed one is `t p_e + (1 - p_e)`, the Bernoulli pgf in `ℝ≥0∞` form. -/
theorem lintegral_powOpen (p : ι → unitInterval) (t : ℝ≥0∞) (e : ι) :
    ∫⁻ ω : Set ι, powOpen t ω e ∂(prodBernoulli p)
      = t * (unitInterval.toNNReal (p e) : ℝ≥0∞)
        + (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞)) := by
  classical
  have hs_meas : MeasurableSet {ω : Set ι | e ∈ ω} := measurableSet_mem e
  have hpoint : (fun ω : Set ι => powOpen t ω e)
      = fun ω => t * ({ω : Set ι | e ∈ ω}.indicator (1 : Set ι → ℝ≥0∞)) ω
          + ({ω : Set ι | e ∈ ω}ᶜ.indicator (1 : Set ι → ℝ≥0∞)) ω := by
    funext ω
    by_cases h : e ∈ ω
    · simp [powOpen, powOpenFun_true, h]
    · simp [powOpen, powOpenFun_false, h]
  rw [hpoint, lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop)]
  rw [lintegral_indicator_one hs_meas, lintegral_indicator_one hs_meas.compl,
    prob_compl_eq_one_sub hs_meas, prodBernoulli_setOf_mem]

/-- **Adapted-revelation pgf factorization.** The exact one-step input for the generation
induction: the history factor and the fresh Bernoulli pgf separate, for an arbitrary
(possibly infinite) revealed set. -/
theorem lintegral_adapted_pgf [Countable St] (p : ι → unitInterval) (D : RevealData ι St)
    (G : Set ι → ℝ≥0∞) (H : (σ : St) → Set (D.reveal σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (D.state ω) (blockRestrict (D.reveal (D.state ω)) ω))
    (S : St → Finset ι) (hS : ∀ σ, Disjoint ((S σ : Finset ι) : Set ι) (D.reveal σ))
    (t : ℝ≥0∞) :
    ∫⁻ ω, G ω * t ^ openCount (S (D.state ω)) ω ∂(prodBernoulli p)
      = ∑' σ : St, (∫⁻ ω in {ω | D.state ω = σ}, G ω ∂(prodBernoulli p))
          * ∏ e ∈ S σ, (t * (unitInterval.toNNReal (p e) : ℝ≥0∞)
              + (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞))) := by
  classical
  have hfun : ∀ ω : Set ι, t ^ openCount (S (D.state ω)) ω
      = ∏ e ∈ S (D.state ω), powOpen t ω e :=
    fun ω => (prod_powOpen_eq_pow_openCount (S (D.state ω)) t ω).symm
  have hswap : ∀ (ω : Set ι) (e : ι), powOpen t ω e = powOpenFun t (e ∈ ω) := fun _ _ => rfl
  simp only [hfun, hswap]
  rw [lintegral_adapted_prod p D G H hH hG S hS (fun _ => powOpenFun t)]
  refine tsum_congr fun σ => ?_
  have hswap' : ∀ (ω : Set ι) (e : ι), powOpenFun t (e ∈ ω) = powOpen t ω e := fun _ _ => rfl
  simp only [hswap', lintegral_powOpen]

end PercLib.Probability.AdaptedReveal

namespace PercLib.Probability.AdaptedReveal

variable {ι : Type*} {St : Type*} [Countable St]

/-- **Adapted-revelation pgf bound.** If each state's fresh Bernoulli pgf is dominated by a
deterministic `B σ`, then so is the conditional expectation of the fresh pgf. This is the
form in which the generation induction consumes the estimate: `B σ` is
`exp((t-1) · (row-sum budget of the frontier in state σ))`. -/
theorem lintegral_adapted_pgf_le (p : ι → unitInterval) (D : RevealData ι St)
    (G : Set ι → ℝ≥0∞) (H : (σ : St) → Set (D.reveal σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (D.state ω) (blockRestrict (D.reveal (D.state ω)) ω))
    (S : St → Finset ι) (hS : ∀ σ, Disjoint ((S σ : Finset ι) : Set ι) (D.reveal σ))
    (t : ℝ≥0∞) (B : St → ℝ≥0∞)
    (hB : ∀ σ : St, (∏ e ∈ S σ, (t * (unitInterval.toNNReal (p e) : ℝ≥0∞)
        + (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞)))) ≤ B σ) :
    ∫⁻ ω, G ω * t ^ openCount (S (D.state ω)) ω ∂(prodBernoulli p)
      ≤ ∑' σ : St, (∫⁻ ω in {ω | D.state ω = σ}, G ω ∂(prodBernoulli p)) * B σ := by
  rw [lintegral_adapted_pgf p D G H hH hG S hS t]
  exact ENNReal.tsum_le_tsum fun σ => mul_le_mul' le_rfl (hB σ)

end PercLib.Probability.AdaptedReveal
