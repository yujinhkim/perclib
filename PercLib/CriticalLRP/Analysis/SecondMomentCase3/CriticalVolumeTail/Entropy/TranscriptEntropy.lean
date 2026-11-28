module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Entropy.TranscriptKL
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Entropy.PerEdgeKL

/-!
# Composition check: direction d4's transcript bound with direction d1's Lemma 3.3

`LRP.kl_le_of_lemma33` (from `TranscriptKL.lean`) reduces the two-intensity transcript entropy
bound to the one-dimensional estimate
`bkl (1 - e^{-a}) (1 - e^{-b}) ≤ (b - a)^2 / (2 min {a,b})`.
`LRP.bkl_one_sub_exp_le` (`PerEdgeKL.lean`, direction d1) proves exactly that.  This file
records that the two fit, giving the bound with no remaining premise.  It is a verification
artifact only: the two source files remain independent of each other.
-/

@[expose] public section

namespace LRP

variable {E : Type*} [Fintype E] [DecidableEq E] {σ : QueryPlan E}

/-- **The two-intensity transcript entropy bound, with no remaining premise.** -/
theorem kl_le_unconditional {J : E → ℝ} {β₁ β₂ : ℝ} (hJ : ∀ e, 0 < J e) (hβ₁ : 0 < β₁)
    (hβ : β₁ ≤ β₂) (n : ℕ) :
    klPath J β₁ β₂ σ n ≤ ((β₂ - β₁) ^ 2 / (2 * β₁)) * ∑ e, J e * rev J β₁ σ n e :=
  kl_le_of_lemma33 (fun a b ha hb => bkl_one_sub_exp_le (a := a) (b := b) ha hb) hJ hβ₁ hβ n

end LRP

namespace LRP

set_option linter.hashCommand false in
#print axioms LRP.kl_le_unconditional

end LRP
