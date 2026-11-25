/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The fifth cluster moment as an exact fivefold sum of joint connection probabilities.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Mixed

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- Five connection indicators multiply to the indicator of the corresponding intersection. -/
theorem indicator_mul_five {α : Type*} (s t u v w : Set α) :
    s.indicator (fun _ => (1 : ℝ≥0∞)) * (t.indicator (fun _ => (1 : ℝ≥0∞)))
      * (u.indicator (fun _ => (1 : ℝ≥0∞))) * (v.indicator (fun _ => (1 : ℝ≥0∞)))
      * (w.indicator (fun _ => (1 : ℝ≥0∞))) =
      ((s ∩ t ∩ u ∩ v ∩ w).indicator (fun _ : α => (1 : ℝ≥0∞))) := by
  funext a
  simp only [Pi.mul_apply]
  by_cases h1 : a ∈ s <;> by_cases h2 : a ∈ t <;> by_cases h3 : a ∈ u <;>
    by_cases h4 : a ∈ v <;> by_cases h5 : a ∈ w <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2, h3, h4, h5]

/-- A product of five extended sums, with an extra constant factor. -/
theorem tsum_five_mul_with [Countable V] [AddCommGroup V] {f g h k l : V → ℝ≥0∞} (C : ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, f a * g b * h c * k d * l e * C) =
      (∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d) * (∑' e, l e) * C := by
  rw [FivePoint.tsum_move_last_five]
  have hinner : ∀ e : V, (∑' a, ∑' b, ∑' c, ∑' d, f a * g b * h c * k d * l e * C) =
      ((∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d)) * (l e * C) := by
    intro e
    simpa only [← mul_assoc] using
      FivePoint.tsum_four_mul_with (f := f) (g := g) (h := h) (k := k) (l e * C)
  calc
    (∑' e, ∑' a, ∑' b, ∑' c, ∑' d, f a * g b * h c * k d * l e * C) =
        ∑' e, ((∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d)) * (l e * C) :=
      tsum_congr hinner
    _ = ∑' e, (((∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d)) * C) * l e :=
      tsum_congr fun e => by ring
    _ = (∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d) * C * ∑' e, l e :=
      ENNReal.tsum_mul_left
    _ = _ := by ring

/-- The fifth cluster power as the fivefold sum of joint connection probabilities.
All values remain in `ℝ≥0∞`; neither finiteness nor local finiteness is assumed. -/
theorem lintegral_cardFun_five_eq [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval) (x : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ 5 ∂(law π) =
      ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q ∩ conn x r) := by
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
  have hfive : ∀ ω, (∑' y, f y ω) ^ 5 =
      ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, f y ω * f z ω * f w ω * f q ω * f r ω := by
    intro ω
    simpa [pow_succ] using
      (tsum_five_mul_with (f := fun y => f y ω) (g := fun z => f z ω)
        (h := fun w => f w ω) (k := fun q => f q ω) (l := fun r => f r ω) (1 : ℝ≥0∞)).symm
  have hjoint : ∀ y z w q r : V,
      ∫⁻ ω, f y ω * f z ω * f w ω * f q ω * f r ω ∂(law π) =
        law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q ∩ conn x r) := by
    intro y z w q r
    have hfun : (fun ω => f y ω * f z ω * f w ω * f q ω * f r ω) =
        (((conn x y).indicator (fun _ => (1 : ℝ≥0∞)) *
          (conn x z).indicator (fun _ => (1 : ℝ≥0∞))) *
        (conn x w).indicator (fun _ => (1 : ℝ≥0∞)) *
        (conn x q).indicator (fun _ => (1 : ℝ≥0∞)) *
        (conn x r).indicator (fun _ => (1 : ℝ≥0∞))) := by
      funext ω
      simp only [Pi.mul_apply]
      rw [hf y ω, hf z ω, hf w ω, hf q ω, hf r ω]
    rw [hfun, indicator_mul_five]
    exact lintegral_indicator_one
      (((((measurableSet_conn x y).inter (measurableSet_conn x z)).inter
        (measurableSet_conn x w)).inter (measurableSet_conn x q)).inter (measurableSet_conn x r))
  calc
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ 5 ∂(law π)
        = ∫⁻ ω, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
            f y ω * f z ω * f w ω * f q ω * f r ω ∂(law π) := by
          refine lintegral_congr fun ω => ?_
          rw [hcard ω, hfive ω]
    _ = ∑' y, ∫⁻ ω, ∑' z, ∑' w, ∑' q, ∑' r,
        f y ω * f z ω * f w ω * f q ω * f r ω ∂(law π) := by
          refine lintegral_tsum fun y => ?_
          exact (Measurable.tsum fun z => Measurable.tsum fun w =>
            Measurable.tsum fun q => Measurable.tsum fun r =>
              ((((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q)).mul (hfm r)).aemeasurable
    _ = ∑' y, ∑' z, ∫⁻ ω, ∑' w, ∑' q, ∑' r,
        f y ω * f z ω * f w ω * f q ω * f r ω ∂(law π) := by
          refine tsum_congr fun y => lintegral_tsum fun z => ?_
          exact (Measurable.tsum fun w => Measurable.tsum fun q => Measurable.tsum fun r =>
            (((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q) |>.mul (hfm r)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∫⁻ ω, ∑' q, ∑' r,
        f y ω * f z ω * f w ω * f q ω * f r ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => lintegral_tsum fun w => ?_
          exact (Measurable.tsum fun q => Measurable.tsum fun r =>
            (((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q) |>.mul (hfm r)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∫⁻ ω, ∑' r,
        f y ω * f z ω * f w ω * f q ω * f r ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => lintegral_tsum fun q => ?_
          exact (Measurable.tsum fun r =>
            (((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q) |>.mul (hfm r)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∫⁻ ω,
        f y ω * f z ω * f w ω * f q ω * f r ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => tsum_congr fun w =>
            tsum_congr fun q => lintegral_tsum fun r => ?_
          exact ((((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q)).mul (hfm r) |>.aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q ∩ conn x r) := by
          exact tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => tsum_congr fun q =>
            tsum_congr fun r => hjoint y z w q r

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.indicator_mul_five
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.tsum_five_mul_with
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.lintegral_cardFun_five_eq

end PercLib.CriticalLRP.TreeExpansion.SixPoint
