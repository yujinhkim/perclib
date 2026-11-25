/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Reflection invariance of the project's canonical finite independent law.

`PRefl` (see `I58Reflect.lean`) asks for a configuration-space involution that
preserves the weight and exchanges the two clusters.  This file discharges the
*weight* half for the project's own finite Bernoulli law
`PercLib.CriticalLRP.configurationLaw p` (`FiniteBernoulli.lean`): any
permutation `σ` of the edge set with `p (σ e) = p e` preserves
`configurationLaw p` and hence the expectation `ex (configurationLaw p)`.

Specialising `σ` to the edge permutation induced by the lattice reflection
`x ↦ y - x` (which preserves `|a - b|` and hence any radial `p`) gives the
weight invariance required by `PRefl`.  The remaining input of `PRefl` for a
canonical model is the *cluster equivariance* `K (R ω) = ρ_y '' K_y ω`, which is
the statement that a reflection of the edge set reflects connected components;
that is not formalised here and stays an explicit hypothesis.

No `sorry`, no `admit`, no custom axioms, no `native_decide`.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.I58ReflectWitness
public import PercLib.CriticalLRP.FiniteBernoulli

set_option autoImplicit true

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP.I58

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The permutation of configurations induced by a permutation of the edge set. -/
def cfgPerm (σ : Equiv.Perm E) : Equiv.Perm (Configuration E) where
  toFun s := s.image σ
  invFun s := s.image σ.symm
  left_inv s := by
    show (s.image σ).image σ.symm = s
    rw [Finset.image_image]
    ext e
    simp
  right_inv s := by
    show (s.image σ.symm).image σ = s
    rw [Finset.image_image]
    ext e
    simp

@[simp] theorem cfgPerm_apply (σ : Equiv.Perm E) (s : Configuration E) :
    cfgPerm σ s = s.image σ := rfl

/-- **The canonical independent law is invariant under any edge permutation that
preserves `p`.** -/
theorem configurationLaw_image_perm (σ : Equiv.Perm E) (p : E → ℝ)
    (hp : ∀ e, p (σ e) = p e) (s : Configuration E) :
    configurationLaw p (s.image σ) = configurationLaw p s := by
  simp only [configurationLaw]
  rw [← Equiv.prod_comp σ (fun e => if e ∈ s.image σ then p e else 1 - p e)]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hmem : (σ e ∈ s.image σ) ↔ (e ∈ s) := by
    constructor
    · intro h
      obtain ⟨e', he', heq⟩ := Finset.mem_image.mp h
      have : e' = e := σ.injective heq
      simpa [this] using he'
    · intro h
      exact Finset.mem_image.mpr ⟨e, h, rfl⟩
  by_cases h : e ∈ s
  · rw [ite_eq_left (hmem.mpr h), ite_eq_left h, hp e]
  · rw [ite_eq_right (fun hc => h (hmem.mp hc)), ite_eq_right h, hp e]

/-- **The canonical expectation is invariant under any edge permutation that
preserves `p`.** -/
theorem ex_configurationLaw_comp_image (σ : Equiv.Perm E) (p : E → ℝ)
    (hp : ∀ e, p (σ e) = p e) (X : Configuration E → ℝ) :
    ex (configurationLaw p) (fun s => X (s.image σ)) = ex (configurationLaw p) X := by
  simp only [ex]
  have hfun : ∀ s : Configuration E,
      configurationLaw p s * X (s.image σ)
        = configurationLaw p (cfgPerm σ s) * X (cfgPerm σ s) := by
    intro s
    rw [cfgPerm_apply, configurationLaw_image_perm σ p hp s]
  rw [Finset.sum_congr rfl fun s _ => hfun s]
  exact Equiv.sum_comp (cfgPerm σ) (fun t => configurationLaw p t * X t)

end PercLib.CriticalLRP.I58

#print axioms PercLib.CriticalLRP.I58.cfgPerm
#print axioms PercLib.CriticalLRP.I58.configurationLaw_image_perm
#print axioms PercLib.CriticalLRP.I58.ex_configurationLaw_comp_image
