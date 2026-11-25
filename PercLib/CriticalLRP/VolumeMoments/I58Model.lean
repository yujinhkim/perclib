/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Bridge between the abstract finite model of `I58Remainder` and the project's
finite-volume Bernoulli model (`CriticalPercLib.CriticalLRP.FiniteBernoulli`).

The assembly `lemma_I_5_8_assembly` is stated for an arbitrary finite weight
`w : Ω → ℝ` with `w >= 0` and `sum w = 1`.  The project's finite-volume law
`configurationLaw p` on `Configuration E = Finset E` is such a weight and its
expectation is the project's `expectation p`, so the assembly — *including its
four displayed remainder hypotheses* — can be read in the project's model.

Scope warning: identifying the expectations validates nothing about the four
displayed remainder estimates.  Those are the probabilistic content of the
paper (BK inequality, restoration, mass transport) and are hypotheses here.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.FiniteBernoulli
public import PercLib.CriticalLRP.VolumeMoments.I58Remainder

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.I58

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The project's finite Bernoulli expectation is the finitely supported
expectation of the assembly (definitionally). -/
theorem ex_configurationLaw_eq_expectation (p : E → ℝ) (X : Configuration E → ℝ) :
    ex (configurationLaw p) X = expectation p X := rfl

/-- The weight is normalized, so `ex` is an expectation. -/
theorem ex_configurationLaw_one (p : E → ℝ) :
    ex (configurationLaw p) (fun _ => (1 : ℝ)) = 1 := by
  rw [ex_configurationLaw_eq_expectation]
  simp only [expectation, mul_one, configurationLaw_sum]

/-- The weight is nonnegative on every configuration. -/
theorem ex_configurationLaw_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (s : Configuration E) : 0 ≤ configurationLaw p s :=
  configurationLaw_nonneg p hp hp1 s

/-- The assembly of Lemma I.5.8 instantiated at the project's finite-volume
Bernoulli law.  The four displayed remainder estimates stay hypotheses. -/
theorem lemma_I_5_8_assembly_configurationLaw
    {d : ℕ} (p : E → ℝ) (u : Fin d → ℝ)
    (K : Configuration E → Finset (Site d))
    (Ky : Site d → Configuration E → Finset (Site d))
    (B : Finset (Site d)) {r : ℝ}
    (hR0 : |(∑ y ∈ B, ex (configurationLaw p) (T0 u K Ky y)) -
        (ex (configurationLaw p) (kcard K)) ^ 2 * (∑ y ∈ B, q u y)|
      ≤ uNormSq u * r ^ 2 * ex (configurationLaw p) (fun ω => (kcard K ω) ^ 2 * kap K B ω))
    (hR2 : |(∑ y ∈ B, ex (configurationLaw p) (T2 u K Ky y)) -
        (B.card : ℝ) * (ex (configurationLaw p) (kcard K)) * (ex (configurationLaw p) (kS u K))|
      ≤ ex (configurationLaw p) (fun ω => kcard K ω * kap K B ω * kS u K ω))
    (hR3 : |∑ y ∈ B, ex (configurationLaw p) (T3 u K Ky y)|
      ≤ (1 / 2) * ex (configurationLaw p) (fun ω => kcard K ω * kap K B ω * kS u K ω))
    (hR4 : |∑ y ∈ B, ex (configurationLaw p) (T4 u K Ky y)|
      ≤ (1 / 2) * ex (configurationLaw p) (fun ω => kcard K ω * kap K B ω * kS u K ω)
        + (1 / 2) * ex (configurationLaw p)
            (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)))
    (hGq : ex (configurationLaw p) (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B))
      ≤ uNormSq u * r ^ 2 * ex (configurationLaw p) (fun ω => (kcard K ω) ^ 2 * kap K B ω)) :
    |derivTerm (configurationLaw p) u K Ky B - mainTerm (configurationLaw p) u K B|
      ≤ 3 * (uNormSq u * r ^ 2
          * ex (configurationLaw p) (fun ω => (kcard K ω) ^ 2 * kap K B ω))
        + 5 * ex (configurationLaw p) (fun ω => kcard K ω * kap K B ω * kS u K ω) :=
  lemma_I_5_8_assembly u K Ky B hR0 hR2 hR3 hR4 hGq

end PercLib.CriticalLRP.I58

#print axioms PercLib.CriticalLRP.I58.ex_configurationLaw_eq_expectation
#print axioms PercLib.CriticalLRP.I58.ex_configurationLaw_one
#print axioms PercLib.CriticalLRP.I58.lemma_I_5_8_assembly_configurationLaw
