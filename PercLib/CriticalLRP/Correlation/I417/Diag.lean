/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Diag.lean ; module path rewritten only.
-/

/-
# The diagonal term *is* the excluded moment

The three-fold free-variable sum of the two-copy diagonal event `diagSet` is exactly the native
excluded moment `E[|Kx|² |Ky| 1(x ↮ y)]` of Lemma I.4.17:

  `∑_{x₁x₂y₁} (μ⊗μ)(diagSet x₁x₂y₁) = ∫⁻ ω, |Kx|² 1(y ∉ Kx) |Ky|`.

The two ingredients are

* `lintegral`/`tsum` interchange (Tonelli) plus `clusterVol_eq_tsum`, which turns the three free
  sums over `x₁, x₂, y₁` into the product of cluster volumes
  `|Kx(p.2)|² · 1(y ∉ Kx(p.2)) · |Ky(restoreMap x p)|`;
* the law preservation `map_restoreMap` together with the exact identity
  `cluster_forceOn_compl_touchSet` (`Kx(ω̃) = Kx(ω₁)`), which identifies the pushed-forward
  integral with the one-copy moment.  This is where the restored cluster `K̃y` replaces the
  base cluster `Ky` — the step the printed proof takes for granted and which is *false* for the
  base cluster.

No `sorry`, no custom axioms; no definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Measure

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Elementary `ℝ≥0∞` reshufflings -/

/-- Indicator of an intersection is the product of the indicators. -/
theorem indicator_inter_one {α : Type*} (A B : Set α) (a : α) :
    (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) a =
      A.indicator (fun _ => (1 : ℝ≥0∞)) a * B.indicator (fun _ => (1 : ℝ≥0∞)) a := by
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp [hA, hB]

/-- A triple factorised sum: `∑ᵢ∑ⱼ∑ₗ aᵢ bⱼ k cₗ = (∑a)(∑b)k(∑c)`. -/
theorem tsum_tsum_tsum_mul_const {ι : Type*} [Countable ι] (a b c : ι → ℝ≥0∞) (k : ℝ≥0∞) :
    (∑' i, ∑' j, ∑' l : ι, a i * b j * k * c l) =
      (∑' i, a i) * (∑' j, b j) * k * (∑' l, c l) := by
  have h1 : ∀ i j : ι, (∑' l : ι, a i * b j * k * c l) = (a i * b j * k) * (∑' l, c l) :=
    fun i j => ENNReal.tsum_mul_left
  simp only [h1]
  have h2 : ∀ i : ι, (∑' j : ι, (a i * b j * k) * (∑' l, c l)) =
      (∑' j : ι, a i * b j * k) * (∑' l, c l) := fun i => ENNReal.tsum_mul_right
  simp only [h2]
  rw [ENNReal.tsum_mul_right]
  congr 1
  have h4 : ∀ i : ι, (∑' j : ι, a i * b j * k) = (a i * ∑' j, b j) * k := by
    intro i
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
  simp only [h4]
  simp only [ENNReal.tsum_mul_right]

/-- Collapsing the three nested free-variable sums into one sum over the product type. -/
theorem tsum_tsum_tsum_eq_tsum_prod (F : V → V → V → ℝ≥0∞) :
    (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V, F x₁ x₂ y₁) =
      ∑' t : V × V × V, F t.1 t.2.1 t.2.2 := by
  have h : (∑' t : V × V × V, F t.1 t.2.1 t.2.2) =
      ∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V, F x₁ x₂ y₁ := by
    rw [ENNReal.tsum_prod (f := fun (a : V) (b : V × V) => F a b.1 b.2)]
    exact tsum_congr fun x₁ =>
      ENNReal.tsum_prod (f := fun (x₂ : V) (y₁ : V) => F x₁ x₂ y₁)
  exact h.symm

/-- The `diagSet` as an intersection of four one-condition sets. -/
theorem diagSet_eq_inter (x y x₁ x₂ y₁ : V) :
    diagSet x y x₁ x₂ y₁ =
      {p : TwoCopy V | p.2 ∈ connSet x x₁} ∩ {p : TwoCopy V | p.2 ∈ connSet x x₂} ∩
        {p : TwoCopy V | p.2 ∉ connSet x y} ∩
        {p : TwoCopy V | restoreMap x p ∈ connSet y y₁} := by
  ext p
  simp only [diagSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- Measurability of the integrand of the excluded moment. -/
theorem measurable_clusterVol_moment (x y : V) :
    Measurable fun ω : Config V => clusterVol ω x ^ 2 *
      (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y :=
  (((measurable_clusterVol x).pow_const 2).mul
    (measurable_const.indicator (measurableSet_cluster_mem x y).compl)).mul
    (measurable_clusterVol y)

/-! ## The pointwise identity -/

/-- **The three free sums of the diagonal indicator.**  For a fixed pair `p = (ω₂, ω₁)`,
summing the indicator of `diagSet x y x₁ x₂ y₁` over `x₁, x₂, y₁` gives the product of the base
cluster volume squared, the indicator of `y ∉ Kx(ω₁)` and the restored cluster volume at `y`. -/
theorem diagSet_indicator_tsum (x y : V) (p : TwoCopy V) :
    (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
        (diagSet x y x₁ x₂ y₁).indicator (fun _ => (1 : ℝ≥0∞)) p) =
      clusterVol p.2 x ^ 2 * (cluster p.2 x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        clusterVol (restoreMap x p) y := by
  have hmem : ∀ x₁ x₂ y₁ : V, (p ∈ diagSet x y x₁ x₂ y₁ ↔
      (x₁ ∈ cluster p.2 x ∧ x₂ ∈ cluster p.2 x ∧ y ∉ cluster p.2 x ∧
        y₁ ∈ cluster (restoreMap x p) y)) := by
    intro x₁ x₂ y₁
    simp only [diagSet, Set.mem_ofPred_eq, Set.mem_inter_iff, mem_cluster_iff, connSet]
    tauto
  have hif : ∀ x₁ x₂ y₁ : V,
      (diagSet x y x₁ x₂ y₁).indicator (fun _ => (1 : ℝ≥0∞)) p =
        (if x₁ ∈ cluster p.2 x then 1 else 0) * (if x₂ ∈ cluster p.2 x then 1 else 0) *
          (if y ∉ cluster p.2 x then 1 else 0) *
          (if y₁ ∈ cluster (restoreMap x p) y then 1 else 0) := by
    intro x₁ x₂ y₁
    rw [Set.indicator_apply, hmem x₁ x₂ y₁]
    by_cases h1 : x₁ ∈ cluster p.2 x <;> by_cases h2 : x₂ ∈ cluster p.2 x <;>
      by_cases h3 : y ∈ cluster p.2 x <;> by_cases h4 : y₁ ∈ cluster (restoreMap x p) y <;>
      simp [h1, h2, h3, h4]
  simp only [hif, tsum_tsum_tsum_mul_const, clusterVol_eq_tsum p.2 x,
    clusterVol_eq_tsum (restoreMap x p) y, sq]
  simp only [Set.indicator_apply, Set.mem_compl_iff]

/-- The collapsed (`V × V × V`-indexed) form of `diagSet_indicator_tsum`. -/
theorem diagSet_indicator_tsum_prod (x y : V) (p : TwoCopy V) :
    (∑' t : V × V × V, (diagSet x y t.1 t.2.1 t.2.2).indicator (fun _ => (1 : ℝ≥0∞)) p) =
      clusterVol p.2 x ^ 2 * (cluster p.2 x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        clusterVol (restoreMap x p) y := by
  rw [← tsum_tsum_tsum_eq_tsum_prod (F := fun x₁ x₂ y₁ =>
    (diagSet x y x₁ x₂ y₁).indicator (fun _ => (1 : ℝ≥0∞)) p)]
  exact diagSet_indicator_tsum x y p

/-! ## The sum over the three free variables -/

/-- **The diagonal term is the excluded moment.** -/
theorem tsum_diagSet (π : Sym2 V → unitInterval) (x y : V) :
    (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
        ((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y x₁ x₂ y₁)) =
      exclMomentSq π x y := by
  classical
  set μ := edgeMeasure π
  have hmeasure : ∀ x₁ x₂ y₁ : V, (μ.prod μ) (diagSet x y x₁ x₂ y₁) =
      ∫⁻ p : TwoCopy V, (diagSet x y x₁ x₂ y₁).indicator (fun _ => (1 : ℝ≥0∞)) p
        ∂(μ.prod μ) :=
    fun x₁ x₂ y₁ => (lintegral_indicator_one (measurableSet_diagSet x y x₁ x₂ y₁)).symm
  simp only [hmeasure]
  rw [tsum_tsum_tsum_eq_tsum_prod]
  rw [← lintegral_tsum]
  swap
  · intro t
    exact (Measurable.indicator measurable_const
      (measurableSet_diagSet x y t.1 t.2.1 t.2.2)).aemeasurable
  trans ∫⁻ p : TwoCopy V,
      (fun ω : Config V => clusterVol ω x ^ 2 *
        (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y) (restoreMap x p)
      ∂(μ.prod μ)
  · refine lintegral_congr fun p => ?_
    rw [diagSet_indicator_tsum_prod x y p]
    simp only [restoreMap, clusterVol, cluster_forceOn_compl_touchSet]
  · rw [(lintegral_map (measurable_clusterVol_moment x y) (measurable_restoreMap x)).symm]
    rw [show (μ.prod μ).map (restoreMap x) = μ from map_restoreMap π x]
    rfl

end PercLib.CriticalLRP.I417
