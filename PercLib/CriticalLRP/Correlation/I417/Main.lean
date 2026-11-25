/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Main.lean ; module path rewritten only.
-/

/-
# Lemma I.4.17 at `p = 2`, `q = 1`: assembly and the independent-data factors

This file assembles the two-copy inequality with the identification of the diagonal term, and then
reduces the two excess families to the *genuinely independent* data:

* the `y ∈ Kx` family `yInSet`, whose total is `E[|Kx|² 1(y ∈ Kx)] · ∑_w P(y↔w)`;
* the marked-crossing family `markSet w`, whose total is at most
  `∑_w E[|Kx|² 1(w ∈ Kx)] · P(y↔w) · ∑_{y₁} P(w↔y₁)`, by BK on the fresh disjoint occurrence
  `{y↔w} ∘ {w↔y₁}`.

Each factor is a one-copy quantity: the base factor `E[|Kx|² 1(w ∈ Kx)]` involves only `ω₁`, the
fresh factor only `ω₂`.  This is where a diagram/tree-graph analysis (direction C) can take over;
nothing here uses such an analysis.

The final BK-reduced statement needs `π e < 1` for every edge, exactly the hypothesis under which
`bk_connSet_ennreal` is available in this repository; it holds for the paper's law
`π e = 1 − exp(−β J e)` whenever `J e < ∞`.  The unreduced statement needs no hypothesis.

No `sorry`, no custom axioms; no definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Diag

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The assembled two-copy inequality with the native excluded moment -/

/-- **The two-copy inequality at `p = 2`, `q = 1`, with the excluded moment.**  Unconditional in
`ℝ≥0∞`:

  `E|Kx|² · E|Ky| ≤ E[|Kx|² |Ky| 1(x ↮ y)] + Y + W`.
-/
theorem I417_p21_le (π : Sym2 V → unitInterval) (x y : V) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) ≤
      exclMomentSq π x y +
        (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (yInSet x y x₁ x₂ y₁)) +
        (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V, ∑' w : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w)) := by
  have h := twoCopy_moment_le π x y
  rw [tsum_diagSet] at h
  exact h

/-! ## Elementwise reductions -/

theorem measure_yInSet (π : Sym2 V → unitInterval) (x y x₁ x₂ y₁ : V) :
    ((edgeMeasure π).prod (edgeMeasure π)) (yInSet x y x₁ x₂ y₁) =
      (edgeMeasure π) (connSet y y₁) *
        (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x y) := by
  rw [yInSet]
  exact Measure.prod_prod _ _

/-- The marked crossing event: the product of the base three-point event and the fresh disjoint
occurrence, bounded by BK in the fresh copy. -/
theorem measure_markSet_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y x₁ x₂ y₁ w : V) :
    ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w) ≤
      ((edgeMeasure π) (connSet y w) * (edgeMeasure π) (connSet w y₁)) *
        (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x w) := by
  have hmark : ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w) =
      (edgeMeasure π) (Percolation.DisjointOccurrence (connSet y w) (connSet w y₁)) *
        (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x w) := by
    rw [markSet]
    exact Measure.prod_prod _ _
  rw [hmark]
  refine mul_le_mul' ?_ le_rfl
  exact bk_connSet_ennreal π hπ y w w y₁

/-! ## The three-fold sums: joint moments -/

/-- A double factorised sum: `∑ᵢ∑ⱼ aᵢ bⱼ k = (∑a)(∑b)k`. -/
theorem tsum_tsum_mul_const {ι : Type*} [Countable ι] (a b : ι → ℝ≥0∞) (k : ℝ≥0∞) :
    (∑' i, ∑' j, a i * b j * k) = (∑' i, a i) * (∑' j, b j) * k := by
  have h1 : ∀ i : ι, (∑' j : ι, a i * b j * k) = a i * (∑' j, b j) * k := by
    intro i
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
  simp only [h1]
  simp only [ENNReal.tsum_mul_right]

/-- A four-fold sum split over the shared index: `∑ᵢⱼₗₘ f(l,m) g(i,j,m) = ∑ₘ (∑ₗf)(∑ᵢⱼ g)`. -/
theorem tsum_tsum_tsum_tsum_mul_split {ι : Type*} [Countable ι]
    (f : ι → ι → ℝ≥0∞) (g : ι → ι → ι → ℝ≥0∞) :
    (∑' i, ∑' j, ∑' l, ∑' m : ι, f l m * g i j m) =
      ∑' m, (∑' l, f l m) * (∑' i, ∑' j, g i j m) := by
  have h1 : ∀ i j : ι, (∑' l, ∑' m : ι, f l m * g i j m) =
      ∑' m, ∑' l, f l m * g i j m := fun i j => ENNReal.tsum_comm
  simp only [h1]
  have h2 : ∀ i j m : ι, (∑' l, f l m * g i j m) = (∑' l, f l m) * g i j m :=
    fun i j m => ENNReal.tsum_mul_right
  simp only [h2]
  have h3 : ∀ i : ι, (∑' j, ∑' m : ι, (∑' l, f l m) * g i j m) =
      ∑' m, ∑' j, (∑' l, f l m) * g i j m := fun i => ENNReal.tsum_comm
  simp only [h3]
  have h4 : ∀ i m : ι, (∑' j, (∑' l, f l m) * g i j m) = (∑' l, f l m) * (∑' j, g i j m) :=
    fun i m => ENNReal.tsum_mul_left
  simp only [h4]
  have h5 : (∑' i, ∑' m : ι, (∑' l, f l m) * (∑' j, g i j m)) =
      ∑' m, ∑' i, (∑' l, f l m) * (∑' j, g i j m) := ENNReal.tsum_comm
  simp only [h5]
  exact tsum_congr fun m => ENNReal.tsum_mul_left

/-- Pointwise: a product of three indicators is the indicator of the triple intersection. -/
theorem indicator_mul_mul_apply {α : Type*} (A B C : Set α) (a : α) :
    A.indicator (fun _ => (1 : ℝ≥0∞)) a * B.indicator (fun _ => (1 : ℝ≥0∞)) a *
        C.indicator (fun _ => (1 : ℝ≥0∞)) a =
      (A ∩ B ∩ C).indicator (fun _ => (1 : ℝ≥0∞)) a := by
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> by_cases hC : a ∈ C <;> simp [hA, hB, hC]

/-- **The second moment through a marked vertex**: `∑_{x₁x₂} P(x₁,x₂,w ∈ Kx) = E[|Kx|² 1(w ∈ Kx)]`. -/
theorem tsum_tsum_inter_mark_eq (π : Sym2 V → unitInterval) (x w : V) :
    (∑' x₁ : V, ∑' x₂ : V,
        (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x w)) = jointSq π x w := by
  have hpt : ∀ ω : Config V, clusterVol ω x ^ 2 * (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w =
      ∑' x₁ : V, ∑' x₂ : V,
        ((cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) x₁ *
          (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) x₂ *
          (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w) := by
    intro ω
    have key := tsum_tsum_mul_const
      (fun x₁ : V => (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) x₁)
      (fun x₂ : V => (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) x₂)
      ((cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w)
    rw [pow_two, clusterVol_eq_tsum ω x, ← key]
  have hfun : (fun ω : Config V =>
      clusterVol ω x ^ 2 * (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w) =
      fun ω => ∑' x₁ : V, ∑' x₂ : V,
        ((cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) x₁ *
          (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) x₂ *
          (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w) := by
    funext ω
    exact hpt ω
  rw [jointSq, hfun, lintegral_tsum]
  swap
  · intro x₁
    exact (Measurable.tsum fun x₂ =>
      ((measurable_const.indicator (measurableSet_cluster_mem x x₁)).mul
        (measurable_const.indicator (measurableSet_cluster_mem x x₂))).mul
        (measurable_const.indicator (measurableSet_cluster_mem x w))).aemeasurable
  refine tsum_congr fun x₁ => ?_
  rw [lintegral_tsum]
  swap
  · intro x₂
    exact (((measurable_const.indicator (measurableSet_cluster_mem x x₁)).mul
      (measurable_const.indicator (measurableSet_cluster_mem x x₂))).mul
        (measurable_const.indicator (measurableSet_cluster_mem x w))).aemeasurable
  refine tsum_congr fun x₂ => ?_
  have hind : (fun ω : Config V =>
        ((cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) x₁ *
          (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) x₂ *
          (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w)) =
      (connSet x x₁ ∩ connSet x x₂ ∩ connSet x w).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    simp only [cluster_indicator_apply x x₁ ω, cluster_indicator_apply x x₂ ω,
      cluster_indicator_apply x w ω, indicator_mul_mul_apply]
  rw [hind]
  exact (lintegral_indicator_one (((measurableSet_connSet x x₁).inter
    (measurableSet_connSet x x₂)).inter (measurableSet_connSet x w))).symm

/-! ## The two excess families in independent-data form -/

/-- A triple sum with the outermost index only in the second factor. -/
theorem tsum_tsum_tsum_mul {ι : Type*} [Countable ι] (f : ι → ι → ℝ≥0∞) (c : ι → ℝ≥0∞) :
    (∑' i, ∑' j, ∑' l, c l * f i j) = (∑' i, ∑' j, f i j) * (∑' l, c l) := by
  have h1 : ∀ i j : ι, (∑' l, c l * f i j) = (∑' l, c l) * f i j :=
    fun i j => ENNReal.tsum_mul_right
  simp only [h1]
  have h2 : ∀ i : ι, (∑' j, (∑' l, c l) * f i j) = (∑' l, c l) * (∑' j, f i j) :=
    fun i => ENNReal.tsum_mul_left
  simp only [h2]
  rw [ENNReal.tsum_mul_left, mul_comm]

/-- **The `y ∈ Kx` family, summed.** -/
theorem tsum_yInSet (π : Sym2 V → unitInterval) (x y : V) :
    (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
        ((edgeMeasure π).prod (edgeMeasure π)) (yInSet x y x₁ x₂ y₁)) =
      jointSq π x y * (∑' y₁ : V, (edgeMeasure π) (connSet y y₁)) := by
  have hterm : ∀ x₁ x₂ y₁ : V,
      ((edgeMeasure π).prod (edgeMeasure π)) (yInSet x y x₁ x₂ y₁) =
        (edgeMeasure π) (connSet y y₁) *
          (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x y) :=
    fun x₁ x₂ y₁ => measure_yInSet π x y x₁ x₂ y₁
  simp only [hterm]
  rw [tsum_tsum_tsum_mul (f := fun x₁ x₂ =>
      (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x y))
    (c := fun y₁ => (edgeMeasure π) (connSet y y₁))]
  rw [tsum_tsum_inter_mark_eq]

/-- **The marked-crossing family, summed and BK-reduced.** -/
theorem tsum_markSet_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V) :
    (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V, ∑' w : V,
        ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w)) ≤
      ∑' w : V, jointSq π x w *
        ((edgeMeasure π) (connSet y w) * (∑' y₁ : V, (edgeMeasure π) (connSet w y₁))) := by
  have hterm : ∀ x₁ x₂ y₁ w : V,
      ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w) ≤
        ((edgeMeasure π) (connSet y w) * (edgeMeasure π) (connSet w y₁)) *
          (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x w) :=
    fun x₁ x₂ y₁ w => measure_markSet_le π hπ x y x₁ x₂ y₁ w
  refine le_trans (ENNReal.tsum_le_tsum fun x₁ => ENNReal.tsum_le_tsum fun x₂ =>
    ENNReal.tsum_le_tsum fun y₁ => ENNReal.tsum_le_tsum fun w => hterm x₁ x₂ y₁ w) ?_
  have hsplit : ∀ x₁ x₂ y₁ w : V,
      ((edgeMeasure π) (connSet y w) * (edgeMeasure π) (connSet w y₁)) *
          (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x w) =
        (fun l m => (edgeMeasure π) (connSet y m) * (edgeMeasure π) (connSet m l)) y₁ w *
          (fun i j m => (edgeMeasure π) (connSet x i ∩ connSet x j ∩ connSet x m))
            x₁ x₂ w := fun x₁ x₂ y₁ w => rfl
  simp only [hsplit, tsum_tsum_tsum_tsum_mul_split]
  refine ENNReal.tsum_le_tsum fun w => ?_
  rw [tsum_tsum_inter_mark_eq]
  rw [show (∑' l : V, (edgeMeasure π) (connSet y w) * (edgeMeasure π) (connSet w l)) =
      (edgeMeasure π) (connSet y w) * (∑' y₁ : V, (edgeMeasure π) (connSet w y₁)) from
    ENNReal.tsum_mul_left]
  exact le_of_eq (mul_comm _ _)

end PercLib.CriticalLRP.I417
