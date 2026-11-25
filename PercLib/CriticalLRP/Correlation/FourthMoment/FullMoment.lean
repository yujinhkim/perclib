/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The fourth cluster-moment reduction from the exact fifteen-shape realization.
The realization is an explicit input to every exported moment theorem here.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Moment

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- Four connection indicators multiply to the indicator of the corresponding intersection. -/
theorem indicator_mul_four {α : Type*} (s t u v : Set α) :
    ((s.indicator (fun _ => (1 : ℝ≥0∞))) * (t.indicator (fun _ => (1 : ℝ≥0∞)))
      * (u.indicator (fun _ => (1 : ℝ≥0∞))) * (v.indicator (fun _ => (1 : ℝ≥0∞))) =
      ((s ∩ t ∩ u ∩ v).indicator (fun _ : α => (1 : ℝ≥0∞)))) := by
  funext a
  simp only [Pi.mul_apply]
  by_cases h1 : a ∈ s <;> by_cases h2 : a ∈ t <;> by_cases h3 : a ∈ u <;>
    by_cases h4 : a ∈ v <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2, h3, h4]

/-- The fourth cluster power as the fourfold sum of joint connection probabilities.
All values remain in `ℝ≥0∞`; neither finiteness nor local finiteness is assumed. -/
theorem lintegral_cardFun_four_eq [Countable V] (π : Sym2 V → unitInterval) (x : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ 4 ∂(law π) =
      ∑' y, ∑' z, ∑' w, ∑' q,
        law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : V → Config V → ℝ≥0∞,
      ∀ (y : V) (ω : Config V),
        f y ω = (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    ⟨fun y ω => (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω, fun _ _ => rfl⟩
  have hfm : ∀ y, Measurable (f y) := by
    intro y
    rw [show f y = fun ω => (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω from funext (hf y)]
    exact measurable_const.indicator (measurableSet_conn x y)
  have hcard : ∀ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω x) = ∑' y, f y ω := by
    intro ω
    rw [PercLib.CriticalLRP.Percolation.cardFun_eq_encard, encard_cluster_eq_tsum]
    exact tsum_congr fun y => (hf y ω).symm
  have hfour : ∀ ω, (∑' y, f y ω) ^ 4 =
      ∑' y, ∑' z, ∑' w, ∑' q, f y ω * f z ω * f w ω * f q ω := by
    intro ω
    simpa [pow_succ] using
      (tsum_four_mul_with (f := fun y => f y ω) (g := fun z => f z ω)
        (h := fun w => f w ω) (k := fun q => f q ω) (1 : ℝ≥0∞)).symm
  have hjoint : ∀ y z w q : V,
      ∫⁻ ω, f y ω * f z ω * f w ω * f q ω ∂(law π) =
        law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q) := by
    intro y z w q
    have hfun : (fun ω => f y ω * f z ω * f w ω * f q ω) =
        (((conn x y).indicator (fun _ => (1 : ℝ≥0∞)) *
          (conn x z).indicator (fun _ => (1 : ℝ≥0∞))) *
        (conn x w).indicator (fun _ => (1 : ℝ≥0∞)) *
        (conn x q).indicator (fun _ => (1 : ℝ≥0∞))) := by
      funext ω
      simp only [Pi.mul_apply]
      rw [hf y ω, hf z ω, hf w ω, hf q ω]
    rw [hfun, indicator_mul_four]
    exact lintegral_indicator_one
      ((((measurableSet_conn x y).inter (measurableSet_conn x z)).inter
        (measurableSet_conn x w)).inter (measurableSet_conn x q))
  calc
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ 4 ∂(law π)
        = ∫⁻ ω, ∑' y, ∑' z, ∑' w, ∑' q, f y ω * f z ω * f w ω * f q ω ∂(law π) := by
          refine lintegral_congr fun ω => ?_
          rw [hcard ω, hfour ω]
    _ = ∑' y, ∫⁻ ω, ∑' z, ∑' w, ∑' q, f y ω * f z ω * f w ω * f q ω ∂(law π) := by
          refine lintegral_tsum fun y => ?_
          exact (Measurable.tsum fun z => Measurable.tsum fun w =>
            Measurable.tsum fun q => ((hfm y).mul (hfm z)).mul (hfm w) |>.mul (hfm q)).aemeasurable
    _ = ∑' y, ∑' z, ∫⁻ ω, ∑' w, ∑' q, f y ω * f z ω * f w ω * f q ω ∂(law π) := by
          refine tsum_congr fun y => lintegral_tsum fun z => ?_
          exact (Measurable.tsum fun w => Measurable.tsum fun q =>
            ((hfm y).mul (hfm z)).mul (hfm w) |>.mul (hfm q)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∫⁻ ω, ∑' q,
        f y ω * f z ω * f w ω * f q ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => lintegral_tsum fun w => ?_
          exact (Measurable.tsum fun q => ((hfm y).mul (hfm z)).mul (hfm w) |>.mul (hfm q)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∫⁻ ω, f y ω * f z ω * f w ω * f q ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => lintegral_tsum fun q => ?_
          exact ((hfm y).mul (hfm z)).mul (hfm w) |>.mul (hfm q) |>.aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q) := by
          exact tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => tsum_congr fun q =>
            hjoint y z w q

/-- The ordinary `p = 4`, `k = 0` tree-graph moment bound, conditionally on the
precise fifteen-shape realization. No finiteness assumption is hidden in the conclusion. -/
theorem fourth_moment_le_of_harm [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a))
    (harm : ∀ (y z w q : V) (ω : Config V),
      PercLib.CriticalLRP.Connects ω 0 y → PercLib.CriticalLRP.Connects ω 0 z →
      PercLib.CriticalLRP.Connects ω 0 w → PercLib.CriticalLRP.Connects ω 0 q →
      Harm5 (PercLib.CriticalLRP.openGraph ω) 0 y z w q) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0)) ^ 4 ∂(law π) ≤
      15 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0) ∂(law π)) ^ 7 := by
  have hsymm : ∀ a b : V, tau π a b = tau π b a := fun a b => tau_comm π a b
  have hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x :=
    fun a => tsum_row_eq (tau π) 0 hinv a
  have hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x :=
    fun b => tsum_col_eq (tau π) 0 hsymm hinv b
  have hmean : (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0) ∂(law π)) =
      ∑' x, tau π 0 x := by
    rw [show (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0) ∂(law π)) =
        ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ∂(law π) from by
      refine lintegral_congr fun ω => ?_
      exact PercLib.CriticalLRP.Percolation.cardFun_eq_encard _]
    exact chi_eq_tsum_tau π 0
  rw [lintegral_cardFun_four_eq π 0, hmean]
  calc
    ∑' y, ∑' z, ∑' w, ∑' q, law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q)
        ≤ ∑' y, ∑' z, ∑' w, ∑' q, fivePointDiagram π 0 y z w q :=
      ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
        ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
          five_point_le_of_harm π 0 y z w q (harm y z w q)
    _ = _ := tsum_fivePointDiagram π hrow hcol 0

#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.lintegral_cardFun_four_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.fourth_moment_le_of_harm

end PercLib.CriticalLRP.TreeExpansion.FivePoint
