/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Measure.lean ; module path rewritten only.
-/

/-
# Lemma I.4.17 at `p = 2`, `q = 1`: the two-copy probability inequality

This file turns the deterministic covering `I417B/Cover.prodSet_subset` into a probability
inequality on the two-copy space.  Writing `μ = edgeMeasure π`, the chain is

  `(∫⁻|Kx|²) (∫⁻|Ky|) = ∑_{x₁x₂y₁} (μ⊗μ)(prodSet x₁x₂y₁)`
  `  ≤ ∑_{x₁x₂y₁} [ (μ⊗μ)(diagSet x₁x₂y₁) + (μ⊗μ)(yInSet x₁x₂y₁) + ∑_w (μ⊗μ)(markSet x₁x₂y₁w) ]`,

i.e. exactly the additive (subtraction-free) form of the printed

  `E|K|² E|K| − E[|Kx|² |Ky| 1(x ↮ y)] ≤ (marked diagram terms)`,

with the excluded moment `E[|Kx|²|Ky|1(x↮y)]` represented by `∑_{x₁x₂y₁}(μ⊗μ)(diagSet …)`; the
identification with the native `exclMomentSq` is `tsum_diagSet` in `I417B/Diag.lean`.

Everything is `ℝ≥0∞`-valued: no moment finiteness and no subcriticality hypothesis is used, and no
`∞ − ∞` occurs.

No `sorry`, no custom axioms; no definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Cover

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The product measure of the two-copy event -/

theorem measure_prodSet (π : Sym2 V → unitInterval) (x y x₁ x₂ y₁ : V) :
    ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y x₁ x₂ y₁) =
      (edgeMeasure π) (connSet y y₁) *
        (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂) := by
  rw [prodSet]
  exact Measure.prod_prod _ _

/-- **The per-triple probability inequality.**  For fixed `x₁, x₂, y₁` the two-copy product event
is covered by the diagonal event, the `y ∈ Kx` event and the marked crossings, hence
`(μ⊗μ)(prodSet) ≤ (μ⊗μ)(diagSet) + (μ⊗μ)(yInSet) + ∑_w (μ⊗μ)(markSet w)`. -/
theorem measure_prodSet_le (π : Sym2 V → unitInterval) (x y x₁ x₂ y₁ : V) :
    ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y x₁ x₂ y₁) ≤
      ((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y x₁ x₂ y₁) +
        ((edgeMeasure π).prod (edgeMeasure π)) (yInSet x y x₁ x₂ y₁) +
        ∑' w : V, ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w) := by
  refine le_trans (measure_mono (prodSet_subset x y x₁ x₂ y₁)) ?_
  refine le_trans (measure_union_le (μ := (edgeMeasure π).prod (edgeMeasure π)) _ _)
    (add_le_add ?_ (measure_iUnion_le _))
  exact measure_union_le _ _

/-! ## The `τ`-sums that turn the two-copy events into moments -/

/-- The cluster indicator at the vertex `x`, pointwise in the configuration. -/
theorem cluster_indicator_apply (v x : V) (ω : Config V) :
    (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) x =
      (connSet v x).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases h : x ∈ cluster ω v
  · rw [Set.indicator_of_mem h,
      Set.indicator_of_mem (show ω ∈ connSet v x from mem_cluster_iff.mp h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show ω ∉ connSet v x from fun hh => h (mem_cluster_iff.mpr hh))]

/-- The cluster indicator at the vertex `x`, as a function of the configuration. -/
theorem cluster_indicator_eq (v x : V) :
    (fun ω : Config V => (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) x) =
      (connSet v x).indicator (fun _ => (1 : ℝ≥0∞)) :=
  funext fun ω => cluster_indicator_apply v x ω

/-- Pointwise: the product of two indicator functions is the indicator of the intersection. -/
theorem indicator_mul_indicator_apply {α : Type*} (A B : Set α) (a : α) :
    A.indicator (fun _ => (1 : ℝ≥0∞)) a * B.indicator (fun _ => (1 : ℝ≥0∞)) a =
      (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) a := by
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp [hA, hB]

/-- `∑_w P(v ↔ w) = E|Kv|`: the τ-sum is the expected cluster volume, in `ℝ≥0∞` (Tonelli on
`clusterVol_eq_tsum`). -/
theorem tsum_connSet_eq_lintegral (π : Sym2 V → unitInterval) (v : V) :
    (∑' w : V, (edgeMeasure π) (connSet v w)) =
      ∫⁻ ω, clusterVol ω v ∂(edgeMeasure π) := by
  have hfun : (fun ω : Config V => clusterVol ω v) =
      fun ω => ∑' w : V, (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) w := by
    funext ω
    exact clusterVol_eq_tsum ω v
  rw [hfun, lintegral_tsum]
  · refine tsum_congr fun w => ?_
    rw [cluster_indicator_eq v w]
    exact (lintegral_indicator_one (measurableSet_connSet v w)).symm
  · intro w
    exact (Measurable.indicator measurable_const (measurableSet_cluster_mem v w)).aemeasurable

/-- `∑_{x₁x₂} P(x₁,x₂ ∈ Kv) = E|Kv|²`: the second-moment expansion, in `ℝ≥0∞`. -/
theorem tsum_tsum_inter_connSet_eq_lintegral (π : Sym2 V → unitInterval) (v : V) :
    (∑' x₁ : V, ∑' x₂ : V, (edgeMeasure π) (connSet v x₁ ∩ connSet v x₂)) =
      ∫⁻ ω, clusterVol ω v ^ 2 ∂(edgeMeasure π) := by
  have hpt : ∀ ω : Config V, clusterVol ω v ^ 2 =
      ∑' x₁ : V, ∑' x₂ : V,
        ((cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) x₁ *
          (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) x₂) := by
    intro ω
    rw [pow_two, clusterVol_eq_tsum ω v, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun x => by rw [← ENNReal.tsum_mul_left]
  have hfun : (fun ω : Config V => clusterVol ω v ^ 2) =
      fun ω => ∑' x₁ : V, ∑' x₂ : V,
        ((cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) x₁ *
          (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) x₂) := by
    funext ω
    exact hpt ω
  rw [hfun, lintegral_tsum]
  swap
  · intro x₁
    exact (Measurable.tsum fun x₂ =>
      (measurable_const.indicator (measurableSet_cluster_mem v x₁)).mul
        (measurable_const.indicator (measurableSet_cluster_mem v x₂))).aemeasurable
  refine tsum_congr fun x₁ => ?_
  rw [lintegral_tsum]
  swap
  · intro x₂
    exact ((measurable_const.indicator (measurableSet_cluster_mem v x₁)).mul
      (measurable_const.indicator (measurableSet_cluster_mem v x₂))).aemeasurable
  refine tsum_congr fun x₂ => ?_
  have hind : (fun ω : Config V =>
        ((cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) x₁ *
          (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) x₂)) =
      (connSet v x₁ ∩ connSet v x₂).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    simp only [cluster_indicator_apply v x₁ ω, cluster_indicator_apply v x₂ ω,
      indicator_mul_indicator_apply]
  rw [hind]
  exact (lintegral_indicator_one ((measurableSet_connSet v x₁).inter
    (measurableSet_connSet v x₂))).symm

/-- **The three-fold free-variable sum of the product event** equals the product of moments
`E|Kx|² · E|Ky|`. -/
theorem tsum_prodSet_eq (π : Sym2 V → unitInterval) (x y : V) :
    (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
        ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y x₁ x₂ y₁)) =
      volSq π x * ∫⁻ ω, clusterVol ω y ∂(edgeMeasure π) := by
  have hterm : ∀ x₁ x₂ y₁ : V,
      ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y x₁ x₂ y₁) =
        (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂) * (edgeMeasure π) (connSet y y₁) := by
    intro x₁ x₂ y₁
    rw [measure_prodSet, mul_comm]
  simp only [hterm]
  -- factor the `y₁`-sum out, twice
  have h₁ : ∀ x₁ x₂ : V,
      (∑' y₁ : V, (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂) *
          (edgeMeasure π) (connSet y y₁)) =
        (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂) *
          (∑' y₁ : V, (edgeMeasure π) (connSet y y₁)) :=
    fun x₁ x₂ => ENNReal.tsum_mul_left
  simp only [h₁]
  have h₂ : ∀ x₁ : V,
      (∑' x₂ : V, (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂) *
          (∑' y₁ : V, (edgeMeasure π) (connSet y y₁))) =
        (∑' x₂ : V, (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂)) *
          (∑' y₁ : V, (edgeMeasure π) (connSet y y₁)) :=
    fun x₁ => ENNReal.tsum_mul_right
  simp only [h₂]
  rw [ENNReal.tsum_mul_right, tsum_connSet_eq_lintegral, tsum_tsum_inter_connSet_eq_lintegral]
  rfl

/-! ## The summed two-copy inequality -/

/-- **The two-copy probability inequality for `p = 2`, `q = 1`.**  The product of moments
`E|Kx|² · E|Ky|` is bounded by the excluded-moment term plus the `y ∈ Kx` and marked-crossing
two-copy terms, all in `ℝ≥0∞` and with no hypothesis. -/
theorem twoCopy_moment_le (π : Sym2 V → unitInterval) (x y : V) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) ≤
      (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y x₁ x₂ y₁)) +
        (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (yInSet x y x₁ x₂ y₁)) +
        (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V, ∑' w : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w)) := by
  rw [← tsum_prodSet_eq]
  calc (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
        ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y x₁ x₂ y₁))
      ≤ ∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
          (((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y x₁ x₂ y₁) +
            ((edgeMeasure π).prod (edgeMeasure π)) (yInSet x y x₁ x₂ y₁) +
            ∑' w : V, ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w)) :=
        ENNReal.tsum_le_tsum fun x₁ => ENNReal.tsum_le_tsum fun x₂ =>
          ENNReal.tsum_le_tsum fun y₁ => measure_prodSet_le π x y x₁ x₂ y₁
    _ = _ := by
        simp only [ENNReal.tsum_add]

end PercLib.CriticalLRP.I417
