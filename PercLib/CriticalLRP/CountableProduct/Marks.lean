/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The monotone coupling in the intensity parameter `β`, and the paper's law `P_β`.

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.

* §I.1.2, p. 6: edges are open independently with probability `1 - exp(-β J(x,y))`, and
  `β_c := inf{β ≥ 0 : an infinite cluster exists P_β-a.s.}`.
* p. 7: "for every `r < ∞` there exists `ε = ε(r) > 0` such that `J_r(x,y) ≤ (1-ε)J(x,y)`
  for every `x ≠ y`, so that `P_{β_c,r}` is *stochastically dominated* by the subcritical
  measure `P_{(1-ε)β_c}`".  The paper uses the stochastic order in `β`; this file provides
  it.

## Method

Rather than coupling two product spaces, we represent *every* `P_β` on one probability
space: independent marks `U_e` uniform on `[0,1]`, one for each edge, and
`ω_β(U) = {e : U_e < 1 - exp(-β J e)}`.  Since the coordinate maps are independent and
`P(U_e < p) = p`, `P_β` is the law of `ω_β(U)` (`markMeasure_map_atParameter`), and since
`β ↦ 1 - exp(-β J e)` is nondecreasing, an *increasing* event `A` satisfies
`ω_β(U) ∈ A → ω_{β'}(U) ∈ A` for `β ≤ β'` pointwise in `U`; monotonicity of the measure
then gives `P_β(A) ≤ P_{β'}(A)`.

This is unconditional: no `sorry`, no custom axioms.  It gives that
`{β : P_β(an infinite cluster exists) = 1}` is an up-set, i.e. that `β_c` is a genuine
threshold; see `Critical.lean`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.CountableProduct.Base

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

/-! ## A uniform mark for every edge -/

/-- Uniform measure on `[0,1]`. -/
noncomputable def unif : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure unif := by
  constructor
  simp [unif, Real.volume_Icc]

theorem unif_Iio (c : ℝ) (_h0 : 0 ≤ c) (h1 : c ≤ 1) :
    unif (Set.Iio c) = ENNReal.ofReal c := by
  rw [unif, Measure.restrict_apply measurableSet_Iio]
  have he : Set.Iio c ∩ Set.Icc 0 1 = Set.Ico 0 c := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨h, h2, -⟩; exact ⟨h2, h⟩
    · rintro ⟨h2, h⟩; exact ⟨h, h2, le_trans h.le h1⟩
  rw [he, Real.volume_Ico, sub_zero]

theorem unif_Ici (c : ℝ) (h0 : 0 ≤ c) (_h1 : c ≤ 1) :
    unif (Set.Ici c) = ENNReal.ofReal (1 - c) := by
  rw [unif, Measure.restrict_apply measurableSet_Ici]
  have he : Set.Ici c ∩ Set.Icc 0 1 = Set.Icc c 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨h, -, h2⟩; exact ⟨h, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨h, le_trans h0 h, h2⟩
  rw [he, Real.volume_Icc]

/-- Every subset of `Prop` is one of four. -/
theorem prop_set_cases {s : Set Prop} : s = ∅ ∨ s = {True} ∨ s = {False} ∨ s = Set.univ := by
  classical
  by_cases h1 : True ∈ s <;> by_cases h2 : False ∈ s
  · exact Or.inr (Or.inr (Or.inr (by ext x; by_cases hx : x <;> simp_all)))
  · exact Or.inr (Or.inl (by ext x; by_cases hx : x <;> simp_all))
  · exact Or.inr (Or.inr (Or.inl (by ext x; by_cases hx : x <;> simp_all)))
  · exact Or.inl (by ext x; by_cases hx : x <;> simp_all)

/-- Two probability measures on `Prop` agreeing on `{True}` are equal. -/
theorem measure_prop_ext {ν₁ ν₂ : Measure Prop} [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] (h : ν₁ {True} = ν₂ {True}) : ν₁ = ν₂ := by
  classical
  have hF : ∀ (ν : Measure Prop) [IsProbabilityMeasure ν], ν {False} = 1 - ν {True} := by
    intro ν _
    have hc : (({True} : Set Prop))ᶜ = {False} := by
      ext x; by_cases hx : x <;> simp [hx]
    have h' := measure_compl (μ := ν) (s := ({True} : Set Prop)) (measurableSet_singleton True)
      (measure_ne_top _ _)
    rw [hc, MeasureTheory.measure_univ] at h'
    exact h'
  ext s _
  rcases prop_set_cases (s := s) with h' | h' | h' | h'
  · rw [h']; simp
  · rw [h']; exact h
  · rw [h', hF ν₁, hF ν₂, h]
  · rw [h']; simp

section Mark

variable {V : Type*} [Countable V]

/-- Independent uniform marks, one for each edge. -/
noncomputable def markMeasure (V : Type*) [Countable V] : Measure (Sym2 V → ℝ) :=
  Measure.infinitePi (fun _ : Sym2 V => unif)

instance (V : Type*) [Countable V] : IsProbabilityMeasure (markMeasure V) :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi (fun _ : Sym2 V => (unif : Measure ℝ))))

/-- The configuration of edges whose mark is below the edge's open probability. -/
def atParameter (q : Sym2 V → unitInterval) (u : Sym2 V → ℝ) : Config V :=
  fun e => u e < (q e : ℝ)

theorem measurable_atParameter (q : Sym2 V → unitInterval) : Measurable (atParameter q) :=
  Measurable.of_eval fun e => (measurable_pi_apply e).lt measurable_const

/-- For a single edge, thresholding a uniform mark at `p` gives the Bernoulli law `Ber(p)`. -/
theorem unif_map_lt (p : unitInterval) :
    unif.map (fun t : ℝ => t < (p : ℝ)) =
      bernoulliMeasure (True : Prop) (False : Prop) p := by
  classical
  have hm : Measurable (fun t : ℝ => t < (p : ℝ)) := measurable_id.lt measurable_const
  have ht : (unif.map (fun t : ℝ => t < (p : ℝ))) {True} = toNNReal p := by
    rw [Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun t : ℝ => t < (p : ℝ)) ⁻¹' {True} = Set.Iio (p : ℝ) := by
      ext t; simp
    rw [he, unif_Iio (p : ℝ) p.2.1 p.2.2, ENNReal.coe_nnreal_eq]
    rfl
  have hf : (unif.map (fun t : ℝ => t < (p : ℝ))) {False} = toNNReal (σ p) := by
    rw [Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun t : ℝ => t < (p : ℝ)) ⁻¹' {False} = Set.Ici (p : ℝ) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ici]
      exact ⟨fun h => not_lt.1 (by simpa using h), fun h => by simp [not_lt.2 h]⟩
    rw [he, unif_Ici (p : ℝ) p.2.1 p.2.2, ENNReal.coe_nnreal_eq]
    simp [unitInterval.coe_symm_eq]
  refine measure_prop_ext ?_
  rw [ht, bernoulliMeasure_apply _ (measurableSet_singleton _)]
  simp

/-- **The law of long-range percolation is the law of the thresholded uniform marks**
(stated with the product-type carrier so that `Measure.infinitePi_map_pi` applies). -/
theorem markMeasure_map_atParameter_pi (q : Sym2 V → unitInterval) :
    (markMeasure V).map ((fun u : Sym2 V → ℝ => fun e => u e < (q e : ℝ)) : _ → Sym2 V → Prop) =
      Measure.infinitePi (fun e => bernoulliMeasure (True : Prop) (False : Prop) (q e)) := by
  have hmap := Measure.infinitePi_map_pi (μ := fun _ : Sym2 V => (unif : Measure ℝ))
    (f := fun e (t : ℝ) => t < (q e : ℝ)) (fun e => measurable_id.lt measurable_const)
  have hgoal : (markMeasure V).map ((fun u : Sym2 V → ℝ => fun e => u e < (q e : ℝ)) : _ → Sym2 V → Prop) =
      (Measure.infinitePi (fun _ : Sym2 V => unif)).map
        (fun x i => (fun e (t : ℝ) => t < (q e : ℝ)) i (x i)) := rfl
  rw [hgoal, hmap]
  simp only [unif_map_lt]

/-- **The law of long-range percolation is the law of the thresholded uniform marks.** -/
theorem markMeasure_map_atParameter (q : Sym2 V → unitInterval) :
    (markMeasure V).map (atParameter q) = edgeMeasure q := by
  rw [edgeMeasure_eq_infinitePi q]
  exact markMeasure_map_atParameter_pi q

/-! ## Monotonicity of the law in the edge probabilities -/

/-- **Stochastic monotonicity.**  If the edge-open probabilities are increased pointwise,
the probability of every increasing measurable event increases. -/
theorem edgeMeasure_mono_of_le {p q : Sym2 V → unitInterval} (hpq : ∀ e, p e ≤ q e)
    {A : Set (Config V)} (hA : MeasurableSet A) (hinc : IsIncreasing A) :
    edgeMeasure p A ≤ edgeMeasure q A := by
  classical
  have key : ∀ r : Sym2 V → unitInterval,
      edgeMeasure r A = (markMeasure V) ((atParameter r) ⁻¹' A) := by
    intro r
    have hstep := Measure.map_apply (μ := markMeasure V) (f := atParameter r)
      (measurable_atParameter r) (s := A) hA
    calc edgeMeasure r A = (markMeasure V).map (atParameter r) A := by
          rw [markMeasure_map_atParameter r]
      _ = (markMeasure V) ((atParameter r) ⁻¹' A) := hstep
  rw [key p, key q]
  refine measure_mono fun u hu => ?_
  have hsub : atParameter p u ⊆ atParameter q u := by
    intro e he
    have h1 : u e < (p e : ℝ) := he
    have h2 : (p e : ℝ) ≤ (q e : ℝ) := hpq e
    exact lt_of_lt_of_le h1 h2
  exact hinc hsub hu

end Mark

/-! ## The paper's law `P_β` and its monotonicity in `β`

The kernel is an arbitrary nonnegative symmetric function `J : Sym2 V → ℝ` (a function of
the unordered pair, hence symmetric), i.e. `J(x,y) = J(y,x)`.  For the paper's kernel one
takes `J (s(x,y)) = ‖x - y‖^{-d-α}` (`J(x,y) = 1(x ≠ y)J(‖x-y‖)`, Definition I.1.3). -/

section LongRange

variable {V : Type*} [Countable V]

/-- The edge-open probability `1 - exp(-β J e)` of §I.1.2, as an element of the unit
interval. -/
noncomputable def bernoulliEdgeProb (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) :
    Sym2 V → unitInterval :=
  fun e => ⟨1 - Real.exp (-((β : ℝ) * J e)), by
    have hx : 0 ≤ (β : ℝ) * J e := mul_nonneg β.2 (hJ e)
    have h1 : Real.exp (-((β : ℝ) * J e)) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.2 (by linarith)
    have h2 : 0 < Real.exp (-((β : ℝ) * J e)) := Real.exp_pos _
    constructor <;> linarith⟩

theorem bernoulliEdgeProb_coe (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (e : Sym2 V) :
    ((bernoulliEdgeProb J hJ β e : unitInterval) : ℝ) = 1 - Real.exp (-((β : ℝ) * J e)) :=
  rfl

/-- `β ↦ 1 - exp(-β J e)` is nondecreasing. -/
theorem bernoulliEdgeProb_mono (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) {β β' : NNReal}
    (h : β ≤ β') (e : Sym2 V) : bernoulliEdgeProb J hJ β e ≤ bernoulliEdgeProb J hJ β' e := by
  rw [← Subtype.coe_le_coe, bernoulliEdgeProb_coe, bernoulliEdgeProb_coe]
  have hJ' : (0 : ℝ) ≤ J e := hJ e
  have hβ : (β : ℝ) ≤ (β' : ℝ) := by exact_mod_cast h
  have hexp : Real.exp (-((β' : ℝ) * J e)) ≤ Real.exp (-((β : ℝ) * J e)) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  linarith

/-- **The long-range percolation law `P_β`** of §I.1.2. -/
noncomputable def longRangeMeasure (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) :
    Measure (Config V) :=
  edgeMeasure (bernoulliEdgeProb J hJ β)

instance (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) :
    IsProbabilityMeasure (longRangeMeasure J hJ β) := by
  rw [longRangeMeasure]; infer_instance

/-- At `β = 0` no edge is open: the law is the point mass at the empty configuration. -/
theorem longRangeMeasure_zero (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) :
    longRangeMeasure J hJ 0 = dirac (∅ : Config V) := by
  rw [longRangeMeasure]
  have h : bernoulliEdgeProb J hJ 0 = fun _ => (0 : unitInterval) := by
    funext e
    apply Subtype.ext
    simp [bernoulliEdgeProb]
  rw [h, edgeMeasure, PercLib.Percolation.Bond.law]
  simpa using
    PercLib.Probability.prodBernoulli_deterministic (∅ : Set (Sym2 V))

/-- **`P_β` is stochastically monotone in `β`** (the stochastic domination used throughout
the paper). -/
theorem longRangeMeasure_mono_apply {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) {β β' : NNReal}
    (h : β ≤ β') {A : Set (Config V)} (hA : MeasurableSet A) (hinc : IsIncreasing A) :
    longRangeMeasure J hJ β A ≤ longRangeMeasure J hJ β' A :=
  edgeMeasure_mono_of_le (fun e => bernoulliEdgeProb_mono J hJ h e) hA hinc

/-- The **percolation probability** `θ_β(v) = P_β(|K_v| = ∞)`. -/
noncomputable def percolationFunction (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (v : V) : ℝ≥0∞ :=
  longRangeMeasure J hJ β {ω : Config V | InInfiniteCluster ω v}

/-- **Probability that an infinite cluster exists** under `P_β`, the quantity in the
paper's definition of `β_c`. -/
noncomputable def infiniteClusterProb (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) :
    ℝ≥0∞ :=
  longRangeMeasure J hJ β (existsInfiniteClusterEvent V)

theorem infiniteClusterProb_mono {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) {β β' : NNReal}
    (h : β ≤ β') : infiniteClusterProb J hJ β ≤ infiniteClusterProb J hJ β' :=
  longRangeMeasure_mono_apply hJ h measurableSet_existsInfiniteCluster
    isIncreasing_existsInfiniteCluster

theorem percolationFunction_mono {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) {β β' : NNReal}
    (h : β ≤ β') (v : V) : percolationFunction J hJ β v ≤ percolationFunction J hJ β' v :=
  longRangeMeasure_mono_apply hJ h (measurableSet_inInfiniteCluster v)
    (isIncreasing_inInfiniteCluster v)

theorem infiniteClusterProb_le_one (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) :
    infiniteClusterProb J hJ β ≤ 1 := by
  rw [infiniteClusterProb, ← measure_univ (μ := longRangeMeasure J hJ β)]
  exact measure_mono (Set.subset_univ _)

/-- At `β = 0` there is no infinite cluster: `P_0` is a point mass at the empty
configuration, whose clusters are singletons. -/
theorem infiniteClusterProb_zero (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) :
    infiniteClusterProb J hJ 0 = 0 := by
  rw [infiniteClusterProb, longRangeMeasure_zero]
  have h : (∅ : Config V) ∉ existsInfiniteClusterEvent V := by
    rintro ⟨v, hv⟩
    exact not_inInfiniteCluster_empty v hv
  simpa using h

end LongRange

end PercLib.CriticalLRP
