/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m1.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m1/SixFold.lean`.
-/

/-
Ultramath `smwzqts7r`, member `m1`, direction `d2`.

# The sixth cluster moment as an exact sixfold sum

The `p = 6` companion of production's `lintegral_cardFun_five_eq`
(`PercLib/CriticalLRP/Correlation/SixPoint/FullMoment.lean`):

  `∫⁻ ω, |K_0(ω)|^6 ∂law π = ∑' y z w q r s, law π (⋂_{x ∈ {y,z,w,q,r,s}} conn 0 x)`.

No finiteness of any moment is assumed: everything stays in `ℝ≥0∞` and the interchange is
Tonelli.  This is the identity the `p = 6`, `k = 2` assembly consumes.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Eval
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Assembly
public import PercLib.CriticalLRP.Correlation.SixPoint.Fork.Assembly

/-! The exact Tonelli representation of the sixth cluster-volume moment. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

namespace PercLib.CriticalLRP.TreeExpansion.SixFold

variable {V : Type*}

/-! ## Products of indicators -/

/-- The product of two indicator functions of sets is the indicator of the intersection. -/
theorem indicator_mul_two {α : Type*} (s t : Set α) :
    s.indicator (fun _ => (1 : ℝ≥0∞)) * t.indicator (fun _ => (1 : ℝ≥0∞)) =
      (s ∩ t).indicator (fun _ : α => (1 : ℝ≥0∞)) := by
  funext a
  simp only [Pi.mul_apply]
  by_cases h1 : a ∈ s <;> by_cases h2 : a ∈ t <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]

/-- Six connection indicators multiply to the indicator of the intersection. -/
theorem indicator_mul_six {α : Type*} (s t u v w x : Set α) :
    s.indicator (fun _ => (1 : ℝ≥0∞)) * (t.indicator (fun _ => (1 : ℝ≥0∞)))
      * (u.indicator (fun _ => (1 : ℝ≥0∞))) * (v.indicator (fun _ => (1 : ℝ≥0∞)))
      * (w.indicator (fun _ => (1 : ℝ≥0∞))) * (x.indicator (fun _ => (1 : ℝ≥0∞))) =
      ((s ∩ t ∩ u ∩ v ∩ w ∩ x).indicator (fun _ : α => (1 : ℝ≥0∞))) := by
  rw [PercLib.CriticalLRP.TreeExpansion.FivePoint.indicator_mul_five s t u v w,
    indicator_mul_two]

/-! ## A sixfold product of sums -/

/-- A product of six extended sums, with one extra constant factor. -/
theorem tsum_six_mul_with [Countable V] [AddCommGroup V] {f g h k l m : V → ℝ≥0∞}
    (C : ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' x, f a * g b * h c * k d * l e * m x * C) =
      (∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d) * (∑' e, l e)
        * (∑' x, m x) * C := by
  have hinner : ∀ a b c d e : V,
      (∑' x, f a * g b * h c * k d * l e * m x * C) =
        f a * g b * h c * k d * l e * ((∑' x, m x) * C) := by
    intro a b c d e
    rw [show (∑' x, f a * g b * h c * k d * l e * m x * C) =
        ∑' x, (f a * g b * h c * k d * l e) * (m x * C) from
      tsum_congr fun x => by ring]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' x, f a * g b * h c * k d * l e * m x * C)
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' e,
          f a * g b * h c * k d * l e * ((∑' x, m x) * C) :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          tsum_congr fun e => hinner a b c d e
    _ = (∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d) * (∑' e, l e)
          * ((∑' x, m x) * C) :=
        PercLib.CriticalLRP.TreeExpansion.FivePoint.tsum_five_mul_with
          (f := f) (g := g) (h := h) (k := k) (l := l) ((∑' x, m x) * C)
    _ = _ := by ring

/-- The sixth power of an extended sum as a sixfold sum of products. -/
theorem tsum_pow_six [Countable V] [AddCommGroup V] (f : V → ℝ≥0∞) :
    (∑' y, f y) ^ 6 = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
      f y * f z * f w * f q * f r * f s := by
  have h := tsum_six_mul_with (f := f) (g := f) (h := f) (k := f) (l := f) (m := f)
    (C := (1 : ℝ≥0∞))
  simp only [mul_one] at h
  calc (∑' y, f y) ^ 6 = (∑' y, f y) * (∑' y, f y) * (∑' y, f y) * (∑' y, f y)
        * (∑' y, f y) * (∑' y, f y) := by ring
    _ = _ := h.symm

/-! ## The sixth cluster moment as a sixfold sum (Tonelli) -/

/-- **The sixth cluster moment as an exact sixfold sum.** -/
theorem lintegral_cardFun_six_eq [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (x : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ 6 ∂(law π) =
      ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
        law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q ∩ conn x r ∩ conn x s) := by
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
  have hsix : ∀ ω, (∑' y, f y ω) ^ 6 =
      ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
        f y ω * f z ω * f w ω * f q ω * f r ω * f s ω := by
    intro ω
    exact tsum_pow_six (fun y => f y ω)
  have hjoint : ∀ y z w q r s : V,
      ∫⁻ ω, f y ω * f z ω * f w ω * f q ω * f r ω * f s ω ∂(law π) =
        law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q ∩ conn x r ∩ conn x s) := by
    intro y z w q r s
    have hfun : (fun ω => f y ω * f z ω * f w ω * f q ω * f r ω * f s ω) =
        ((((conn x y).indicator (fun _ => (1 : ℝ≥0∞)) *
          (conn x z).indicator (fun _ => (1 : ℝ≥0∞))) *
        (conn x w).indicator (fun _ => (1 : ℝ≥0∞)) *
        (conn x q).indicator (fun _ => (1 : ℝ≥0∞)) *
        (conn x r).indicator (fun _ => (1 : ℝ≥0∞))) *
        (conn x s).indicator (fun _ => (1 : ℝ≥0∞))) := by
      funext ω
      simp only [Pi.mul_apply]
      rw [hf y ω, hf z ω, hf w ω, hf q ω, hf r ω, hf s ω]
    rw [hfun, indicator_mul_six]
    exact lintegral_indicator_one
      ((((((measurableSet_conn x y).inter (measurableSet_conn x z)).inter
        (measurableSet_conn x w)).inter (measurableSet_conn x q)).inter
        (measurableSet_conn x r)).inter (measurableSet_conn x s))
  calc
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ 6 ∂(law π)
        = ∫⁻ ω, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
            f y ω * f z ω * f w ω * f q ω * f r ω * f s ω ∂(law π) := by
          refine lintegral_congr fun ω => ?_
          rw [hcard ω, hsix ω]
    _ = ∑' y, ∫⁻ ω, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
        f y ω * f z ω * f w ω * f q ω * f r ω * f s ω ∂(law π) := by
          refine lintegral_tsum fun y => ?_
          exact (Measurable.tsum fun z => Measurable.tsum fun w =>
            Measurable.tsum fun q => Measurable.tsum fun r =>
              Measurable.tsum fun s =>
                (((((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q)).mul (hfm r)).mul
                  (hfm s)).aemeasurable
    _ = ∑' y, ∑' z, ∫⁻ ω, ∑' w, ∑' q, ∑' r, ∑' s,
        f y ω * f z ω * f w ω * f q ω * f r ω * f s ω ∂(law π) := by
          refine tsum_congr fun y => lintegral_tsum fun z => ?_
          exact (Measurable.tsum fun w => Measurable.tsum fun q =>
            Measurable.tsum fun r => Measurable.tsum fun s =>
              (((((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q)).mul (hfm r)).mul
                (hfm s)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∫⁻ ω, ∑' q, ∑' r, ∑' s,
        f y ω * f z ω * f w ω * f q ω * f r ω * f s ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => lintegral_tsum fun w => ?_
          exact (Measurable.tsum fun q => Measurable.tsum fun r => Measurable.tsum fun s =>
            (((((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q)).mul (hfm r)).mul
              (hfm s)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∫⁻ ω, ∑' r, ∑' s,
        f y ω * f z ω * f w ω * f q ω * f r ω * f s ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => tsum_congr fun w =>
            lintegral_tsum fun q => ?_
          exact (Measurable.tsum fun r => Measurable.tsum fun s =>
            (((((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q)).mul (hfm r)).mul
              (hfm s)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∫⁻ ω, ∑' s,
        f y ω * f z ω * f w ω * f q ω * f r ω * f s ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => tsum_congr fun w =>
            tsum_congr fun q => lintegral_tsum fun r => ?_
          exact (Measurable.tsum fun s =>
            (((((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q)).mul (hfm r)).mul
              (hfm s)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s, ∫⁻ ω,
        f y ω * f z ω * f w ω * f q ω * f r ω * f s ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => tsum_congr fun w =>
            tsum_congr fun q => tsum_congr fun r => lintegral_tsum fun s => ?_
          exact (((((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q)).mul (hfm r)).mul
            (hfm s) |>.aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
        law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q ∩ conn x r ∩ conn x s) := by
          exact tsum_congr fun y => tsum_congr fun z => tsum_congr fun w =>
            tsum_congr fun q => tsum_congr fun r => tsum_congr fun s => hjoint y z w q r s

end PercLib.CriticalLRP.TreeExpansion.SixFold
