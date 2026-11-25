module

public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling

/-!
# The scalar standardised-weight estimate at the source cutoff law

Direction (activity 4) of swarm `smwtzmkep`, member `m5`.

The standardised weight `c_r(e)/q_e(r)` of `Resampling/Defs` divides by the open-edge probability.
This file identifies `q_e(r) = 1 - exp(-(β_c J_r(e)))` and proves the scalar bound

  `stdEdgeWeight r e ≤ (-deriv K r) / J_r(e)`   on `{J_r(e) > 0}`,

from `cutProb_coe_eq`, `cutKernel_mk`, `cutEdgeDeriv_mk` and the elementary inequality
`x · exp(-x) ≤ 1 - exp(-x)` (`x ≥ 0`).  The sign hypothesis `0 ≤ -deriv K r` (the cut-off kernel
decreasing) is kept visible.
-/

set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

/-! ## 1. The elementary exponential inequality -/

/-- **`x e^{-x} ≤ 1 - e^{-x}` for `x ≥ 0`**, i.e. `1 - e^{-x} = e^{-x}(e^{x} - 1) ≥ x e^{-x}`. -/
theorem mul_exp_neg_le_one_sub_exp_neg (x : ℝ) :
    x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : 0 < Real.exp (-x) := Real.exp_pos _
  have h3 : (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt h2)
  have h4 : Real.exp x * Real.exp (-x) = 1 := by
    rw [Real.exp_neg, mul_inv_cancel₀ (ne_of_gt (Real.exp_pos x))]
  rw [h4] at h3
  nlinarith [h3]

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 2. The open-edge probability of the source cutoff law -/

/-- The open-edge probability of a single edge under the cut-off law is the cut-off edge
probability `q_e(r) = 1 - e^{-β_c J_r(e)}`. -/
theorem openProb_eq {r : ℝ} (e : Sym2 M.V) :
    M.openProb r e = 1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) := by
  have hmeasure : (M.cutLaw r) {ω : Config M.V | e ∈ ω}
      = (↑(unitInterval.toNNReal (M.cutProb r e)) : ℝ≥0∞) := by
    rw [M.cutLaw_eq_edgeMeasure]
    exact PercLib.Probability.prodBernoulli_setOf_mem (M.cutProb r) e
  have hreal : (M.cutLaw r).real {ω : Config M.V | e ∈ ω}
      = ((M.cutProb r e : unitInterval) : ℝ) := by
    rw [measureReal_def, hmeasure]
    simp
  rw [SourceModelData.openProb, hreal, M.cutProb_coe_eq]

/-- The cut-off derivative weight in closed form, for a non-loop edge inside the range. -/
theorem cutEdgeDeriv_mk_of_le {r : ℝ} {x y : M.V} (hxy : x ≠ y) (hxy' : M.S.dist x y ≤ r) :
    M.cutEdgeDeriv r s(x, y) = (M.betaCrit : ℝ) * (-(deriv M.K r))
      * Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r s(x, y))) := by
  rw [cutEdgeDeriv_mk, ite_eq_right hxy, ite_eq_left hxy', cutKernel_mk, ite_eq_right hxy]

/-! ## 3. The scalar bound for the standardised weight -/

/-- **The standardised edge weight is at most `(-deriv K r)/J_r(e)` where the kernel is positive.** -/
theorem stdEdgeWeight_le_div_cutKernel {r : ℝ} (e : Sym2 M.V)
    (hJ : 0 < M.cutKernel r e) (hK' : 0 ≤ -(deriv M.K r)) :
    M.stdEdgeWeight r e ≤ (-(deriv M.K r)) / M.cutKernel r e := by
  classical
  have hb0 : (0 : ℝ) ≤ (M.betaCrit : ℝ) := by positivity
  rcases eq_or_lt_of_le hb0 with hbzero | hbpos
  · -- degenerate case `β_c = 0`: both the probability and the derivative weight vanish
    have hq0 : M.openProb r e = 0 := by
      rw [openProb_eq, ← hbzero]
      simp
    have hc0 : M.cutEdgeDeriv r e = 0 := by
      induction e using Sym2.ind with
      | h x y =>
        rw [cutEdgeDeriv_mk]
        by_cases hxy : x = y
        · rw [ite_eq_left hxy]
        · rw [ite_eq_right hxy, ← hbzero]
          split <;> ring
    rw [SourceModelData.stdEdgeWeight, hq0, hc0, zero_div]
    exact div_nonneg hK' (le_of_lt hJ)
  · induction e using Sym2.ind with
    | h x y =>
      by_cases hxy : x = y
      · subst hxy
        rw [cutKernel_mk, ite_eq_left rfl] at hJ
        exact absurd hJ (lt_irrefl 0)
      · by_cases hsr : M.S.dist x y ≤ r
        · -- in range: the exponential inequality applies
          have hJpos : 0 < M.cutKernel r s(x, y) := hJ
          have hx0 : 0 ≤ (M.betaCrit : ℝ) * M.cutKernel r s(x, y) := by positivity
          have hexp := mul_exp_neg_le_one_sub_exp_neg
            ((M.betaCrit : ℝ) * M.cutKernel r s(x, y))
          have hq : M.openProb r s(x, y)
              = 1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r s(x, y))) :=
            openProb_eq M s(x, y)
          have hc : M.cutEdgeDeriv r s(x, y) = (M.betaCrit : ℝ) * (-(deriv M.K r))
              * Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r s(x, y))) :=
            M.cutEdgeDeriv_mk_of_le hxy hsr
          rw [SourceModelData.stdEdgeWeight, hq, hc]
          set b : ℝ := (M.betaCrit : ℝ) with hbdef
          set J : ℝ := M.cutKernel r s(x, y) with hJdef
          set d : ℝ := -(deriv M.K r) with hddef
          have hbpos' : 0 < b := hbdef ▸ hbpos
          have hJpos' : 0 < J := hJdef ▸ hJpos
          have hd0 : 0 ≤ d := hddef ▸ hK'
          have hxpos : 0 < b * J := mul_pos hbpos' hJpos'
          have hlt : Real.exp (-(b * J)) < 1 := by
            rw [Real.exp_lt_one_iff]
            linarith
          have hqpos : 0 < 1 - Real.exp (-(b * J)) := by linarith
          have hden : b * J * Real.exp (-(b * J)) ≤ 1 - Real.exp (-(b * J)) := hexp
          have hdenpos : 0 < b * J * Real.exp (-(b * J)) :=
            mul_pos hxpos (Real.exp_pos _)
          have hnum : 0 ≤ b * d * Real.exp (-(b * J)) := by positivity
          calc b * d * Real.exp (-(b * J)) / (1 - Real.exp (-(b * J)))
              ≤ b * d * Real.exp (-(b * J)) / (b * J * Real.exp (-(b * J))) :=
                div_le_div_of_nonneg_left hnum hdenpos hden
            _ = d / J := by
                field_simp
        · -- out of range: the kernel vanishes, contradicting positivity
          have hk : M.cutKernel r s(x, y) = 0 := by
            rw [cutKernel_mk, ite_eq_right hxy, PercLib.CriticalLRP.FiniteVolume.cutoffProfile,
              ite_eq_right hsr]
          rw [hk] at hJ
          exact absurd hJ (lt_irrefl 0)

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

/-! ## 4. Axiom audit -/

#print axioms PercLib.CriticalLRP.mul_exp_neg_le_one_sub_exp_neg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openProb_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mk_of_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.stdEdgeWeight_le_div_cutKernel
