/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Russo's formula on the genuine countable independent-edge product model.

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Lemma I.4.1.  The finite-volume Russo identity is proved in
`CriticalPercLib.CriticalLRP/RussoFinite.lean`.  This file puts that identity on
the *true* countable product law `edgeMeasure π` of
`CriticalPercLib.CriticalLRP/CountableProduct/Base.lean`: for an observable that
depends only on the states of finitely many edges `S ⊆ Sym2 V`, the `r`-derivative
of its expectation is the finite pivotal sum over `e ∈ S`, with the exact
finite-volume integrand.  The proof goes through the cylinder formula for the
infinite product (`Measure.infinitePi_map_restrict`) and the explicit finite-product
integral formula `∫ g d(Measure.pi (bernoulli …)) = expectation …`.

Nothing here needs a summability or sharpness hypothesis: the sum over edges is
finite.  The passage to the unbounded observable `|K|^p` (infinitely many edges,
needs sharpness / finite pivotal flux) is *not* claimed here; the mass-transport
and binomial consequences that do not need it are in `MassTransportI41.lean`.
-/
module

public import PercLib.CriticalLRP.CountableProduct.Base
public import PercLib.CriticalLRP.RussoFinite
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Distributions.Bernoulli

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PercLib.CriticalLRP

/-! ## The finite-product integral formula -/

/-- The canonical equivalence between finite subsets and `Prop`-valued functions
on a finite type. -/
noncomputable def finsetEquivProp (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Finset ι ≃ (ι → Prop) where
  toFun s := fun i => i ∈ s
  invFun y := by classical exact Finset.univ.filter y
  left_inv s := by ext i; simp
  right_inv y := by funext i; simp [Finset.mem_filter]

theorem bernoulliMeasure_real_true (p : unitInterval) :
    (bernoulliMeasure True False p).real {True} = (p : ℝ) := by
  classical
  rw [bernoulliMeasure_real_apply p (measurableSet_singleton True)]
  simp

theorem bernoulliMeasure_real_false (p : unitInterval) :
    (bernoulliMeasure True False p).real {False} = 1 - (p : ℝ) := by
  classical
  rw [bernoulliMeasure_real_apply p (measurableSet_singleton False)]
  simp

/-- **Finite-product integral formula.**  The integral of an arbitrary function of
finitely many independent Bernoulli coordinates is the finite sum against the
product law `configurationLaw`. -/
theorem integral_pi_bernoulli {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : (ι → Prop) → ℝ) :
    ∫ y, g y ∂(Measure.pi (fun i =>
      bernoulliMeasure True False (⟨p i, Set.mem_Icc.mpr ⟨hp0 i, hp1 i⟩⟩ : unitInterval)))
      = expectation p (fun c => g (fun i => i ∈ c)) := by
  classical
  rw [integral_fintype (Integrable.of_finite)]
  simp only [smul_eq_mul]
  rw [expectation]
  rw [← Equiv.sum_comp (finsetEquivProp ι)
    (fun y : ι → Prop =>
      (Measure.pi (fun i => bernoulliMeasure True False
        (⟨p i, Set.mem_Icc.mpr ⟨hp0 i, hp1 i⟩⟩ : unitInterval))).real {y} * g y)]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hpi : (Measure.pi (fun i => bernoulliMeasure True False
        (⟨p i, Set.mem_Icc.mpr ⟨hp0 i, hp1 i⟩⟩ : unitInterval))).real
      {(finsetEquivProp ι) c}
      = ∏ i, (bernoulliMeasure True False
          (⟨p i, Set.mem_Icc.mpr ⟨hp0 i, hp1 i⟩⟩ : unitInterval)).real
          {((finsetEquivProp ι) c) i} := by
    simp only [measureReal_def]
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
  rw [hpi]
  have hfac : ∀ i, (bernoulliMeasure True False
      (⟨p i, Set.mem_Icc.mpr ⟨hp0 i, hp1 i⟩⟩ : unitInterval)).real
      {((finsetEquivProp ι) c) i} = if i ∈ c then p i else 1 - p i := by
    intro i
    by_cases hi : i ∈ c
    · simp only [finsetEquivProp, Equiv.coe_fn_mk, hi, ite_true]
      exact bernoulliMeasure_real_true _
    · simp only [finsetEquivProp, Equiv.coe_fn_mk, hi, ite_false]
      exact bernoulliMeasure_real_false _
  simp only [hfac]
  rw [configurationLaw]
  rfl

/-! ## Cylinder integrals on the countable product law -/

section Cylinder

variable {V : Type*} [Countable V] [DecidableEq V]

/-- The law of the restriction of `edgeMeasure π` to a finite edge set is the
corresponding finite product of Bernoulli measures. -/
theorem map_restrict_edgeMeasure (π : Sym2 V → unitInterval) (S : Finset (Sym2 V)) :
    (edgeMeasure π).map S.restrict
      = Measure.pi (fun e : S => bernoulliMeasure True False (π e)) := by
  rw [edgeMeasure_eq_infinitePi π]
  exact Measure.infinitePi_map_restrict (μ := fun e : Sym2 V =>
    bernoulliMeasure True False (π e)) (I := S)

/-- The cylinder integral as an integral over the finite product of Bernoulli
measures on `S`. -/
theorem integral_edgeMeasure_restrict (π : Sym2 V → unitInterval) (S : Finset (Sym2 V))
    (g : (S → Prop) → ℝ) :
    ∫ ω : Config V, g (S.restrict ω) ∂(edgeMeasure π)
      = ∫ y : (S → Prop), g y ∂(Measure.pi (fun e : S =>
          bernoulliMeasure True False (π e))) := by
  classical
  have hmap : (edgeMeasure π).map S.restrict
      = Measure.pi (fun e : S => bernoulliMeasure True False (π e)) :=
    map_restrict_edgeMeasure π S
  rw [← hmap]
  exact (integral_map (μ := edgeMeasure π) (φ := S.restrict) (f := g)
    (Finset.measurable_restrict S).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable).symm

/-- **Cylinder integral formula on the countable model.**  An observable depending
only on the finitely many edges in `S` has expectation given by the finite product
law on `S`. -/
theorem integral_edgeMeasure_cylinder (π : Sym2 V → unitInterval) (S : Finset (Sym2 V))
    (g : (S → Prop) → ℝ) :
    ∫ ω : Config V, g (S.restrict ω) ∂(edgeMeasure π)
      = expectation (fun e : S => (π e : ℝ)) (fun c => g (fun e => e ∈ c)) := by
  classical
  rw [integral_edgeMeasure_restrict]
  exact integral_pi_bernoulli (fun e : S => (π e : ℝ)) (fun e => (π e).2.1)
    (fun e => (π e).2.2) g

/-- **Russo's formula for cylinder observables on the countable model.**  For any
family of independent edge probabilities `πt` differentiable in `t` with derivative
`π'`, the derivative of the expectation of a cylinder observable is the finite
pivotal sum over the edges it depends on. -/
theorem hasDerivAt_integral_edgeMeasure_cylinder
    (πt : ℝ → Sym2 V → unitInterval) (π' : Sym2 V → ℝ)
    (S : Finset (Sym2 V)) (g : (S → Prop) → ℝ) {t : ℝ}
    (hderiv : ∀ e : Sym2 V,
      HasDerivAt (fun t' => ((πt t' e : unitInterval) : ℝ)) (π' e) t) :
    HasDerivAt (fun t' => ∫ ω : Config V, g (S.restrict ω) ∂(edgeMeasure (πt t')))
      (∑ e : S, π' e.1 *
        FiniteVolume.pivotalMass (fun e : S => ((πt t e : unitInterval) : ℝ)) e
          (fun c => g (fun i => i ∈ c))) t := by
  classical
  have hcyl : ∀ t' : ℝ, (∫ ω : Config V, g (S.restrict ω) ∂(edgeMeasure (πt t')))
      = expectation (fun e : S => ((πt t' e : unitInterval) : ℝ))
          (fun c => g (fun i => i ∈ c)) :=
    fun t' => integral_edgeMeasure_cylinder (πt t') S g
  simp only [hcyl]
  exact FiniteVolume.hasDerivAt_expectation
    (E := S) (P := fun e t' => ((πt t' e.1 : unitInterval) : ℝ))
    (P' := fun e => π' e.1) (t := t) (fun e => hderiv e.1)
    (X := fun c => g (fun i => i ∈ c))

end Cylinder

end PercLib.CriticalLRP
