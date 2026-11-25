/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New continuity consequences of PercLib.Probability.ProductExpectation, whose
finite-profile formula is adapted from near-critical-diffusivity under R-3.
This file copies no upstream proof. It uses finite sums/products and the product
topology from mathlib at 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
module

public import PercLib.Probability.ProductExpectation
public import PercLib.Percolation.Bond.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace PercLib.Probability

variable {ι : Type*}

/-- Finite event probabilities are sums of multiaffine configuration weights. -/
theorem prodBernoulli_finite_apply [Fintype ι] (p : ι → unitInterval) (A : Set (Set ι)) :
    prodBernoulli p A = ∑ ω ∈ A.toFinset, ∏ i : ι,
      if i ∈ ω then (unitInterval.toNNReal (p i) : ℝ≥0∞)
      else (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) := by
  simpa only [prodBernoulli_singleton, Set.coe_toFinset] using
    (sum_measure_singleton (μ := prodBernoulli p) (s := A.toFinset)).symm

/-- Any event on finitely many coordinates has continuous probability, including endpoints. -/
theorem continuous_prodBernoulli_finite_apply [Finite ι] (A : Set (Set ι)) :
    Continuous (fun p : ι → unitInterval => prodBernoulli p A) := by
  let : Fintype ι := Fintype.ofFinite ι
  have h : Continuous (fun p : ι → unitInterval =>
      ∑ ω ∈ A.toFinset, ∏ i : ι, if i ∈ ω then unitInterval.toNNReal (p i)
        else unitInterval.toNNReal (unitInterval.symm (p i))) := by
    apply continuous_finsetSum
    intro ω _
    apply continuous_finsetProd
    intro i _
    split_ifs <;> fun_prop
  convert ENNReal.continuous_coe.comp h using 1
  funext p
  simp only [Function.comp_apply, prodBernoulli_finite_apply, ENNReal.ofNNReal_finsetSum,
    ENNReal.ofNNReal_finsetProd, apply_ite]

/-- Cylinder probabilities reduce to the law on their finite coordinate block. -/
theorem prodBernoulli_cylinder_apply (p : ι → unitInterval) (F : Finset ι)
    (A : Set (Set F)) :
    prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A} =
      prodBernoulli (fun i : F => p i) A := by
  have hm : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set F)) := by
    apply Measurable.of_mem
    intro i
    exact (measurableSet_mem i.val).mem
  rw [← prodBernoulli_map_restrict p F, Measure.map_apply hm (Set.toFinite A).measurableSet]
  rfl

/-- Explicit finite multiaffine formula on an arbitrary ambient coordinate type. -/
theorem prodBernoulli_cylinder_sum (p : ι → unitInterval) (F : Finset ι)
    (A : Set (Set F)) :
    prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A} =
      ∑ η ∈ A.toFinset, ∏ i : F,
        if i ∈ η then (unitInterval.toNNReal (p i) : ℝ≥0∞)
        else (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) := by
  rw [prodBernoulli_cylinder_apply, prodBernoulli_finite_apply]

/-- Continuity in the ambient product topology needs no countability assumption. -/
theorem continuous_prodBernoulli_cylinder (F : Finset ι) (A : Set (Set F)) :
    Continuous (fun p : ι → unitInterval =>
      prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A}) := by
  simp_rw [prodBernoulli_cylinder_apply]
  exact (continuous_prodBernoulli_finite_apply A).comp (by fun_prop)

/-- Pointwise convergence of parameters implies convergence of finite-cylinder probabilities. -/
theorem tendsto_prodBernoulli_cylinder {α : Type*} {l : Filter α}
    (p : α → ι → unitInterval) (q : ι → unitInterval)
    (hp : ∀ i, Filter.Tendsto (fun a => p a i) l (nhds (q i)))
    (F : Finset ι) (A : Set (Set F)) :
    Filter.Tendsto (fun a => prodBernoulli (p a) {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A}) l
      (nhds (prodBernoulli q {ω | (Subtype.val ⁻¹' ω : Set F) ∈ A})) :=
  (continuous_prodBernoulli_cylinder F A).tendsto q |>.comp (tendsto_pi_nhds.mpr hp)

end PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Connection probabilities on a finite vertex type are continuous in the whole profile. -/
theorem continuous_tau_finite [Finite V] (x y : V) :
    Continuous (fun p : Sym2 V → unitInterval => tau p x y) :=
  PercLib.Probability.continuous_prodBernoulli_finite_apply (conn x y)

/-- A finite domain uses the restricted pair profile on its own vertex subtype. -/
theorem continuous_tau_finite_domain (Λ : Set V) [Finite Λ] (x y : Λ) :
    Continuous (fun p : Sym2 V → unitInterval =>
      tau (fun e : Sym2 Λ => p (Sym2.map Subtype.val e)) x y) :=
  (continuous_tau_finite x y).comp (by fun_prop)

/-- Pointwise limits preserve finite-domain connection probabilities, at all endpoints. -/
theorem tendsto_tau_finite_domain {α : Type*} {l : Filter α}
    (p : α → Sym2 V → unitInterval) (q : Sym2 V → unitInterval)
    (hp : ∀ e, Filter.Tendsto (fun a => p a e) l (nhds (q e)))
    (Λ : Set V) [Finite Λ] (x y : Λ) :
    Filter.Tendsto (fun a => tau (fun e : Sym2 Λ => p a (Sym2.map Subtype.val e)) x y) l
      (nhds (tau (fun e : Sym2 Λ => q (Sym2.map Subtype.val e)) x y)) :=
  (continuous_tau_finite_domain Λ x y).tendsto q |>.comp (tendsto_pi_nhds.mpr hp)

-- Both boundary parameters are covered for a nontrivial connection event.
example : ContinuousAt (fun p : Sym2 Bool → unitInterval => tau p false true) (fun _ => 0) :=
  (continuous_tau_finite false true).continuousAt

example : ContinuousAt (fun p : Sym2 Bool → unitInterval => tau p false true) (fun _ => 1) :=
  (continuous_tau_finite false true).continuousAt

-- An empty coordinate block is allowed even with uncountably many ambient coordinates.
example (A : Set (Set (∅ : Finset ℝ))) : Continuous (fun p : ℝ → unitInterval =>
    PercLib.Probability.prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set (∅ : Finset ℝ)) ∈ A}) :=
  PercLib.Probability.continuous_prodBernoulli_cylinder _ A

end PercLib.Percolation.Bond
