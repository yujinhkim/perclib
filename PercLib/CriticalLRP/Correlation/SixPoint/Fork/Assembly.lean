/-
Swarm `smwprafq1`, member `m2` (direction B: event/BK side of `p = 5`, `k = 1`).

# Assembly interface: 105 shapes ⟹ the `p = 5`, `k = 1` tree-graph bound

The fifth cluster moment is the exact fivefold sum of five-point connection probabilities
(Tonelli, no finiteness), and each of `105 = 15 * 7` six-terminal shapes contributes at most
`E|K_0|^2 * (E|K|)^6` (`fork_shape_bound` for the fork shape; every shape has the same
counting).  The deterministic cover — every connected six-terminal configuration realizes one
of the `105` nine-arm shapes — is a separate input `hcover`; it is *not* proved here.

The last theorem is therefore an interface: it consumes the cover as an explicit hypothesis
and must not be read as a proof of Lemma I.4.16.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Fork.Main

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ### The fifth cluster moment as a fivefold sum (Tonelli) -/

/-- Five connection indicators multiply to the indicator of the intersection. -/
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

/-- A product of five extended sums, with one extra constant factor. -/
theorem tsum_five_mul_with [Countable V] [AddCommGroup V] {f g h k l : V → ℝ≥0∞}
    (C : ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, f a * g b * h c * k d * l e * C) =
      (∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d) * (∑' e, l e) * C := by
  rw [tsum_move_last_five]
  have hinner : ∀ e : V, (∑' a, ∑' b, ∑' c, ∑' d, f a * g b * h c * k d * l e * C) =
      ((∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d)) * (l e * C) := by
    intro e
    simpa only [← mul_assoc] using
      tsum_four_mul_with (f := f) (g := g) (h := h) (k := k) (C := l e * C)
  calc (∑' e, ∑' a, ∑' b, ∑' c, ∑' d, f a * g b * h c * k d * l e * C)
      = ∑' e, ((∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d)) * (l e * C) :=
        tsum_congr hinner
    _ = ∑' e, (((∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d)) * C) * l e :=
        tsum_congr fun e => by ring
    _ = (∑' a, f a) * (∑' b, g b) * (∑' c, h c) * (∑' d, k d) * C * ∑' e, l e :=
        ENNReal.tsum_mul_left
    _ = _ := by ring

/-- **The fifth cluster moment as an exact fivefold sum.**  No finiteness of any moment is
assumed; everything stays in `ℝ≥0∞`. -/
theorem lintegral_cardFun_five_eq [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (x : V) :
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
        (h := fun w => f w ω) (k := fun q => f q ω) (l := fun r => f r ω)
        (C := (1 : ℝ≥0∞))).symm
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
        (measurableSet_conn x w)).inter (measurableSet_conn x q)).inter
        (measurableSet_conn x r))
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
          refine tsum_congr fun y => tsum_congr fun z => tsum_congr fun w =>
            lintegral_tsum fun q => ?_
          exact (Measurable.tsum fun r =>
            (((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q) |>.mul (hfm r)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∫⁻ ω,
        f y ω * f z ω * f w ω * f q ω * f r ω ∂(law π) := by
          refine tsum_congr fun y => tsum_congr fun z => tsum_congr fun w =>
            tsum_congr fun q => lintegral_tsum fun r => ?_
          exact ((((hfm y).mul (hfm z)).mul (hfm w)).mul (hfm q)).mul (hfm r) |>.aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q ∩ conn x r) := by
          exact tsum_congr fun y => tsum_congr fun z => tsum_congr fun w =>
            tsum_congr fun q => tsum_congr fun r => hjoint y z w q r

/-! ### The five-shape sum with the shape index outermost -/

theorem tsum_five_fin_swap [Countable V] (F : V → V → V → V → V → Fin 105 → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' k : Fin 105, F a b c d e k)
      = ∑' k : Fin 105, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e k := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' k : Fin 105, F a b c d e k)
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' k : Fin 105, ∑' e, F a b c d e k :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' k : Fin 105, ∑' d, ∑' e, F a b c d e k :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' k : Fin 105, ∑' c, ∑' d, ∑' e, F a b c d e k :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' k : Fin 105, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e k :=
        tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' k : Fin 105, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e k :=
        ENNReal.tsum_comm

theorem tsum_fin105_const (c : ℝ≥0∞) : (∑' _ : Fin 105, c) = 105 * c := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- **Assembly interface for `p = 5`, `k = 1`.**  If every connected six-terminal
configuration is covered by one of `105` shape events `E k`, and each shape's fivefold
free-leaf sum is at most `E|K_0|^2 * (E|K|)^6`, then the fifth cluster moment is at most
`105 * E|K_0|^2 * (E|K|)^6`.

The cover `hcover` is an explicit hypothesis: it is the deterministic input of the argument
and is not established here. -/
theorem fifth_moment_of_cover [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (_hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    {E : Fin 105 → (Fin 5 → V) → Set (Config V)}
    (hcover : ∀ x1 x2 x3 x4 x5 : V,
      conn 0 x1 ∩ conn 0 x2 ∩ conn 0 x3 ∩ conn 0 x4 ∩ conn 0 x5 ⊆
        ⋃ k : Fin 105, E k ![x1, x2, x3, x4, x5])
    (hbound : ∀ k : Fin 105, (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5,
        law π (E k ![x1, x2, x3, x4, x5]))
      ≤ secondMoment π 0 * (∑' x, tau π 0 x) ^ 6) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0)) ^ 5 ∂(law π) ≤
      105 * (secondMoment π 0 * (∑' x, tau π 0 x) ^ 6) := by
  rw [lintegral_cardFun_five_eq π 0]
  calc ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5,
        law π (conn 0 x1 ∩ conn 0 x2 ∩ conn 0 x3 ∩ conn 0 x4 ∩ conn 0 x5)
      ≤ ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5,
          law π (⋃ k : Fin 105, E k ![x1, x2, x3, x4, x5]) :=
        ENNReal.tsum_le_tsum fun x1 => ENNReal.tsum_le_tsum fun x2 =>
          ENNReal.tsum_le_tsum fun x3 => ENNReal.tsum_le_tsum fun x4 =>
            ENNReal.tsum_le_tsum fun x5 =>
              measure_mono (hcover x1 x2 x3 x4 x5)
    _ ≤ ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' k : Fin 105,
          law π (E k ![x1, x2, x3, x4, x5]) :=
        ENNReal.tsum_le_tsum fun x1 => ENNReal.tsum_le_tsum fun x2 =>
          ENNReal.tsum_le_tsum fun x3 => ENNReal.tsum_le_tsum fun x4 =>
            ENNReal.tsum_le_tsum fun x5 => measure_iUnion_le _
    _ = ∑' k : Fin 105, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5,
          law π (E k ![x1, x2, x3, x4, x5]) :=
        tsum_five_fin_swap (fun x1 x2 x3 x4 x5 k => law π (E k ![x1, x2, x3, x4, x5]))
    _ ≤ ∑' _k : Fin 105, secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 :=
        ENNReal.tsum_le_tsum hbound
    _ = 105 * (secondMoment π 0 * (∑' x, tau π 0 x) ^ 6) := tsum_fin105_const _

/-- **The fork-shape bound in the notation of the target statement**: the joint pair is the
native second cluster moment and the six arms are six susceptibility factors. -/
theorem fork_shape_bound_lintegral [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, law π (ForkEvent b0 x1 x2 x3 x4 x5))
      ≤ (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
            (PercLib.CriticalLRP.cluster ω 0)) ^ 2 ∂(law π)) *
          (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
            (PercLib.CriticalLRP.cluster ω 0) ∂(law π)) ^ 6 := by
  have h := fork_shape_bound π hq b0
  have h2 : secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 =
      (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0)) ^ 2 ∂(law π)) *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0) ∂(law π)) ^ 6 := by
    rw [show secondMoment π 0 = ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 2 ∂(law π) from rfl]
    rw [show (∑' x, tau π 0 x) = ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0) ∂(law π) from by
      rw [← firstMoment_eq π 0]
      rfl]
  rw [h2] at h
  exact h

end PercLib.CriticalLRP.TreeExpansion.FivePoint
