/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 117 (Q-1), written on 2026-11-14 by PROVER-E. No upstream proof is
copied: everything is derived from the canonical Harris inequality
`PercLib.Probability.prodBernoulli_harris` and mathlib's Tonelli theorem.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PercLib.Probability.Harris

/-!
# Harris for decreasing events and for monotone functions

The canonical Harris inequality `prodBernoulli_harris` is stated for increasing events.
This file adds no definition. It proves:

* complement duality, `prodBernoulli_map_compl`: the complement of a configuration with
  open probabilities `p` has open probabilities `1 - p`;
* Harris for decreasing events, `prodBernoulli_harris_of_isLowerSet`, and the reverse
  inequality for an increasing and a decreasing event,
  `prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet`;
* the function forms: `prodBernoulli_lintegral_mul_le` for monotone `ℝ≥0∞`-valued
  functions, with no integrability hypothesis, and `prodBernoulli_integral_mul_le` and its
  variants for bounded real functions.

The function forms come from the event forms through a layer-cake representation
(`lintegral_mul_eq_lintegral_prod_measure_inter`), which holds for every s-finite measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {ι : Type*}

/-! ### Complement duality -/

/-- Swapping the two outcomes of a Bernoulli law replaces `p` by `1 - p`. -/
theorem bernoulliMeasure_swap {X : Type*} [MeasurableSpace X] (x y : X) (p : unitInterval) :
    bernoulliMeasure y x p = bernoulliMeasure x y (unitInterval.symm p) := by
  rw [bernoulliMeasure_def, bernoulliMeasure_def, unitInterval.symm_symm, add_comm]

/-- **Complement duality.** The complement of a configuration with open probabilities `p`
is a configuration with open probabilities `1 - p`. -/
theorem prodBernoulli_map_compl (p : ι → unitInterval) :
    (prodBernoulli p).map compl = prodBernoulli (fun i => unitInterval.symm (p i)) := by
  have hset : Measurable (fun P : ι → Prop => {i | P i}) :=
    MeasurableEquiv.setOfPred.measurable
  have hnot : Measurable (fun P : ι → Prop => fun i => ¬ P i) :=
    measurable_pi_iff.2 fun i => (measurable_from_top (f := Not)).comp (measurable_pi_apply i)
  rw [prodBernoulli_eq_map, prodBernoulli_eq_map, Measure.map_map measurable_compl hset]
  have hcomp : (compl ∘ fun P : ι → Prop => {i | P i}) =
      (fun P : ι → Prop => {i | P i}) ∘ (fun P : ι → Prop => fun i => ¬ P i) := by
    funext P; ext i; simp
  rw [hcomp, ← Measure.map_map hset hnot,
    Measure.infinitePi_map_pi _ (fun _ => measurable_from_top (f := Not))]
  congr 2
  funext i
  rw [map_bernoulliMeasure, not_true_eq_false, not_false_eq_true, bernoulliMeasure_swap]

/-- The law at `p` is the image of the law at `1 - p` under complementation. -/
theorem prodBernoulli_eq_map_compl (p : ι → unitInterval) :
    prodBernoulli p = (prodBernoulli (fun i => unitInterval.symm (p i))).map compl := by
  rw [prodBernoulli_map_compl]
  simp only [unitInterval.symm_symm]

/-- Complement duality for one event. -/
theorem prodBernoulli_preimage_compl (p : ι → unitInterval) {A : Set (Set ι)}
    (hA : MeasurableSet A) :
    prodBernoulli p {ω | ωᶜ ∈ A} = prodBernoulli (fun i => unitInterval.symm (p i)) A := by
  rw [← prodBernoulli_map_compl, Measure.map_apply measurable_compl hA]
  rfl

/-- The configurations whose complement lies in a decreasing event form an increasing
event. -/
theorem isUpperSet_preimage_compl {A : Set (Set ι)} (hA : IsLowerSet A) :
    IsUpperSet {ω : Set ι | ωᶜ ∈ A} :=
  fun _ _ h ha => hA (compl_le_compl h) ha

/-! ### Decreasing and mixed events -/

/-- **Harris for decreasing events.** -/
theorem prodBernoulli_harris_of_isLowerSet (q : ι → unitInterval) {A B : Set (Set ι)}
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    prodBernoulli q A * prodBernoulli q B ≤ prodBernoulli q (A ∩ B) := by
  rw [prodBernoulli_eq_map_compl q, Measure.map_apply measurable_compl hAm,
    Measure.map_apply measurable_compl hBm,
    Measure.map_apply measurable_compl (hAm.inter hBm), preimage_inter]
  exact prodBernoulli_harris _ (isUpperSet_preimage_compl hA) (isUpperSet_preimage_compl hB)
    (measurable_compl hAm) (measurable_compl hBm)

/-- Real form of Harris for decreasing events. -/
theorem prodBernoulli_harris_real_of_isLowerSet (q : ι → unitInterval) {A B : Set (Set ι)}
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (prodBernoulli q).real A * (prodBernoulli q).real B ≤ (prodBernoulli q).real (A ∩ B) := by
  simp only [Measure.real, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (prodBernoulli_harris_of_isLowerSet q hA hB hAm hBm)

/-- **An increasing and a decreasing event are negatively correlated.** -/
theorem prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet (q : ι → unitInterval)
    {A B : Set (Set ι)} (hA : IsUpperSet A) (hB : IsLowerSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    prodBernoulli q (A ∩ B) ≤ prodBernoulli q A * prodBernoulli q B := by
  set μ := prodBernoulli q
  have hdiff : μ (A ∩ B) + μ (A \ B) = μ A := measure_inter_add_sdiff A hBm
  have hharris : μ A * μ Bᶜ ≤ μ (A \ B) := by
    rw [sdiff_eq]
    exact prodBernoulli_harris q hA hB.compl hAm hBm.compl
  rw [prob_compl_eq_one_sub hBm] at hharris
  have hsplit : μ A * μ B + μ A * (1 - μ B) = μ A := by
    rw [← mul_add, add_tsub_cancel_of_le prob_le_one, mul_one]
  have hfin : μ A * (1 - μ B) ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.sub_ne_top ENNReal.one_ne_top)
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  calc μ (A ∩ B) + μ A * (1 - μ B) ≤ μ (A ∩ B) + μ (A \ B) := by gcongr
    _ = μ A * μ B + μ A * (1 - μ B) := by rw [hdiff, hsplit]

/-- Real form of the negative correlation of an increasing and a decreasing event. -/
theorem prodBernoulli_real_inter_le_of_isUpperSet_of_isLowerSet (q : ι → unitInterval)
    {A B : Set (Set ι)} (hA : IsUpperSet A) (hB : IsLowerSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (prodBernoulli q).real (A ∩ B) ≤ (prodBernoulli q).real A * (prodBernoulli q).real B := by
  simp only [Measure.real, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet q hA hB hAm hBm)

end PercLib.Probability

/-! ### Layer cake for products, for any s-finite measure -/

namespace PercLib.Probability

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every value of `ℝ≥0∞` is the length of the positive reals below it. -/
theorem volume_Ioi_setOf_ofReal_lt (a : ℝ≥0∞) :
    (volume.restrict (Ioi (0 : ℝ))) {t : ℝ | ENNReal.ofReal t < a} = a := by
  rw [Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  · have : {t : ℝ | ENNReal.ofReal t < a} ∩ Ioi 0 = Ioo 0 a.toReal := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h, ht⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).1 h⟩
      · rintro ⟨ht, h⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).2 h, ht⟩
    rw [this, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal ha]

/-- **Layer cake.** The integral of `f` is the integral over `t > 0` of `μ (t < f)`. -/
theorem lintegral_eq_setLIntegral_measure_ofReal_lt (μ : Measure Ω) [SFinite μ]
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f ω ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ {ω | ENNReal.ofReal t < f ω} := by
  have hE : MeasurableSet {x : Ω × ℝ | ENNReal.ofReal x.2 < f x.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hf.comp measurable_fst)
  have h1 := Measure.prod_apply (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ))) hE
  have h2 := Measure.prod_apply_symm (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ))) hE
  refine Eq.trans ?_ (h1.symm.trans h2)
  exact lintegral_congr fun ω => (volume_Ioi_setOf_ofReal_lt (f ω)).symm

/-- The layer function `t ↦ μ (t < f)` is antitone, hence measurable. -/
theorem measurable_measure_ofReal_lt (μ : Measure Ω) (f : Ω → ℝ≥0∞) :
    Measurable fun t : ℝ => μ {ω | ENNReal.ofReal t < f ω} := by
  refine Antitone.measurable fun s t hst => measure_mono fun ω hω => ?_
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hω

/-- **Layer cake for a product.** -/
theorem lintegral_mul_eq_lintegral_measure_inter (μ : Measure Ω) [SFinite μ]
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ ω, f ω * g ω ∂μ =
      ∫⁻ z, μ ({ω | ENNReal.ofReal z.1 < f ω} ∩ {ω | ENNReal.ofReal z.2 < g ω})
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  set ν := volume.restrict (Ioi (0 : ℝ))
  have hE : MeasurableSet {x : Ω × (ℝ × ℝ) |
      ENNReal.ofReal x.2.1 < f x.1 ∧ ENNReal.ofReal x.2.2 < g x.1} :=
    (measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))
      (hf.comp measurable_fst)).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_snd.comp measurable_snd))
        (hg.comp measurable_fst))
  have h1 := Measure.prod_apply (μ := μ) (ν := ν.prod ν) hE
  have h2 := Measure.prod_apply_symm (μ := μ) (ν := ν.prod ν) hE
  refine Eq.trans ?_ (h1.symm.trans h2)
  refine lintegral_congr fun ω => ?_
  have : Prod.mk ω ⁻¹' {x : Ω × (ℝ × ℝ) |
      ENNReal.ofReal x.2.1 < f x.1 ∧ ENNReal.ofReal x.2.2 < g x.1} =
      {t : ℝ | ENNReal.ofReal t < f ω} ×ˢ {t : ℝ | ENNReal.ofReal t < g ω} := rfl
  rw [this, Measure.prod_prod, volume_Ioi_setOf_ofReal_lt, volume_Ioi_setOf_ofReal_lt]

/-- **Layer cake for a product of integrals.** -/
theorem lintegral_mul_lintegral_eq_lintegral_measure_mul (μ : Measure Ω) [SFinite μ]
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, f ω ∂μ) * (∫⁻ ω, g ω ∂μ) =
      ∫⁻ z, μ {ω | ENNReal.ofReal z.1 < f ω} * μ {ω | ENNReal.ofReal z.2 < g ω}
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [lintegral_eq_setLIntegral_measure_ofReal_lt μ hf,
    lintegral_eq_setLIntegral_measure_ofReal_lt μ hg,
    lintegral_prod_mul (measurable_measure_ofReal_lt μ f).aemeasurable
      (measurable_measure_ofReal_lt μ g).aemeasurable]

/-- Association of the superlevel sets of `f` and `g` gives association of `f` and `g`. -/
theorem lintegral_mul_le_of_measure_superlevel (μ : Measure Ω) [SFinite μ]
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ a b : ℝ≥0∞, μ {ω | a < f ω} * μ {ω | b < g ω} ≤
      μ ({ω | a < f ω} ∩ {ω | b < g ω})) :
    (∫⁻ ω, f ω ∂μ) * (∫⁻ ω, g ω ∂μ) ≤ ∫⁻ ω, f ω * g ω ∂μ := by
  rw [lintegral_mul_lintegral_eq_lintegral_measure_mul μ hf hg,
    lintegral_mul_eq_lintegral_measure_inter μ hf hg]
  exact lintegral_mono fun z => h _ _

/-- Negative association of the superlevel sets of `f` and `g` gives negative association
of `f` and `g`. -/
theorem lintegral_mul_le_of_measure_superlevel' (μ : Measure Ω) [SFinite μ]
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ a b : ℝ≥0∞, μ ({ω | a < f ω} ∩ {ω | b < g ω}) ≤
      μ {ω | a < f ω} * μ {ω | b < g ω}) :
    ∫⁻ ω, f ω * g ω ∂μ ≤ (∫⁻ ω, f ω ∂μ) * (∫⁻ ω, g ω ∂μ) := by
  rw [lintegral_mul_lintegral_eq_lintegral_measure_mul μ hf hg,
    lintegral_mul_eq_lintegral_measure_inter μ hf hg]
  exact lintegral_mono fun z => h _ _

end PercLib.Probability

/-! ### Function forms on the configuration law -/

namespace PercLib.Probability

open MeasureTheory Set
open scoped ENNReal

variable {ι : Type*}

theorem isUpperSet_setOf_lt_of_monotone {β : Type*} [Preorder β] {f : Set ι → β}
    (hf : Monotone f) (a : β) : IsUpperSet {ω | a < f ω} :=
  fun _ _ h ha => lt_of_lt_of_le ha (hf h)

theorem isLowerSet_setOf_lt_of_antitone {β : Type*} [Preorder β] {f : Set ι → β}
    (hf : Antitone f) (a : β) : IsLowerSet {ω | a < f ω} :=
  fun _ _ h ha => lt_of_lt_of_le ha (hf h)

/-- **Harris for monotone functions.** No integrability hypothesis is needed. -/
theorem prodBernoulli_lintegral_mul_le (q : ι → unitInterval) {f g : Set ι → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) (hfm : Measurable f) (hgm : Measurable g) :
    (∫⁻ ω, f ω ∂prodBernoulli q) * (∫⁻ ω, g ω ∂prodBernoulli q) ≤
      ∫⁻ ω, f ω * g ω ∂prodBernoulli q :=
  lintegral_mul_le_of_measure_superlevel _ hfm hgm fun a b =>
    prodBernoulli_harris q (isUpperSet_setOf_lt_of_monotone hf a)
      (isUpperSet_setOf_lt_of_monotone hg b) (measurableSet_lt measurable_const hfm)
      (measurableSet_lt measurable_const hgm)

/-- **Harris for antitone functions.** -/
theorem prodBernoulli_lintegral_mul_le_of_antitone (q : ι → unitInterval)
    {f g : Set ι → ℝ≥0∞} (hf : Antitone f) (hg : Antitone g) (hfm : Measurable f)
    (hgm : Measurable g) :
    (∫⁻ ω, f ω ∂prodBernoulli q) * (∫⁻ ω, g ω ∂prodBernoulli q) ≤
      ∫⁻ ω, f ω * g ω ∂prodBernoulli q :=
  lintegral_mul_le_of_measure_superlevel _ hfm hgm fun a b =>
    prodBernoulli_harris_of_isLowerSet q (isLowerSet_setOf_lt_of_antitone hf a)
      (isLowerSet_setOf_lt_of_antitone hg b) (measurableSet_lt measurable_const hfm)
      (measurableSet_lt measurable_const hgm)

/-- **A monotone and an antitone function are negatively correlated.** -/
theorem prodBernoulli_lintegral_mul_le_of_monotone_of_antitone (q : ι → unitInterval)
    {f g : Set ι → ℝ≥0∞} (hf : Monotone f) (hg : Antitone g) (hfm : Measurable f)
    (hgm : Measurable g) :
    ∫⁻ ω, f ω * g ω ∂prodBernoulli q ≤
      (∫⁻ ω, f ω ∂prodBernoulli q) * (∫⁻ ω, g ω ∂prodBernoulli q) :=
  lintegral_mul_le_of_measure_superlevel' _ hfm hgm fun a b =>
    prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet q
      (isUpperSet_setOf_lt_of_monotone hf a) (isLowerSet_setOf_lt_of_antitone hg b)
      (measurableSet_lt measurable_const hfm) (measurableSet_lt measurable_const hgm)

/-- **Harris for bounded monotone real functions.** -/
theorem prodBernoulli_integral_mul_le (q : ι → unitInterval) {f g : Set ι → ℝ} {C : ℝ}
    (hf : Monotone f) (hg : Monotone g) (hfm : Measurable f) (hgm : Measurable g)
    (hfC : ∀ ω, |f ω| ≤ C) (hgC : ∀ ω, |g ω| ≤ C) :
    (∫ ω, f ω ∂prodBernoulli q) * (∫ ω, g ω ∂prodBernoulli q) ≤
      ∫ ω, f ω * g ω ∂prodBernoulli q := by
  set μ := prodBernoulli q
  have hfi : Integrable f μ :=
    Integrable.of_bound hfm.aestronglyMeasurable C (.of_forall fun ω => (hfC ω))
  have hgi : Integrable g μ :=
    Integrable.of_bound hgm.aestronglyMeasurable C (.of_forall fun ω => (hgC ω))
  have hfgi : Integrable (fun ω => f ω * g ω) μ :=
    Integrable.of_bound (hfm.mul hgm).aestronglyMeasurable (C * C)
      (.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hfC ω) (hgC ω) (abs_nonneg _) ((abs_nonneg _).trans (hfC ω)))
  have hF0 : ∀ ω, 0 ≤ f ω + C := fun ω => by linarith [neg_abs_le (f ω), hfC ω]
  have hG0 : ∀ ω, 0 ≤ g ω + C := fun ω => by linarith [neg_abs_le (g ω), hgC ω]
  have hFi : Integrable (fun ω => f ω + C) μ := hfi.add (integrable_const C)
  have hGi : Integrable (fun ω => g ω + C) μ := hgi.add (integrable_const C)
  have hFGi : Integrable (fun ω => (f ω + C) * (g ω + C)) μ := by
    have : (fun ω => (f ω + C) * (g ω + C)) =
        fun ω => f ω * g ω + (C * f ω + (C * g ω + C * C)) := by
      funext ω; ring
    rw [this]
    exact hfgi.add ((hfi.const_mul C).add ((hgi.const_mul C).add (integrable_const _)))
  have key := prodBernoulli_lintegral_mul_le q
    (f := fun ω => ENNReal.ofReal (f ω + C)) (g := fun ω => ENNReal.ofReal (g ω + C))
    (fun _ _ h => ENNReal.ofReal_le_ofReal (by linarith [hf h]))
    (fun _ _ h => ENNReal.ofReal_le_ofReal (by linarith [hg h]))
    (ENNReal.measurable_ofReal.comp (hfm.add measurable_const))
    (ENNReal.measurable_ofReal.comp (hgm.add measurable_const))
  simp only [← ENNReal.ofReal_mul (hF0 _)] at key
  rw [← ofReal_integral_eq_lintegral_ofReal hFi (.of_forall hF0),
    ← ofReal_integral_eq_lintegral_ofReal hGi (.of_forall hG0),
    ← ofReal_integral_eq_lintegral_ofReal hFGi
      (.of_forall fun ω => mul_nonneg (hF0 ω) (hG0 ω)),
    ← ENNReal.ofReal_mul (integral_nonneg hF0),
    ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun ω => mul_nonneg (hF0 ω) (hG0 ω))]
    at key
  have hFint : ∫ ω, f ω + C ∂μ = (∫ ω, f ω ∂μ) + C := by
    rw [integral_add hfi (integrable_const C)]; simp
  have hGint : ∫ ω, g ω + C ∂μ = (∫ ω, g ω ∂μ) + C := by
    rw [integral_add hgi (integrable_const C)]; simp
  have hFGint : ∫ ω, (f ω + C) * (g ω + C) ∂μ =
      (∫ ω, f ω * g ω ∂μ) + (C * ∫ ω, f ω ∂μ + (C * ∫ ω, g ω ∂μ + C * C)) := by
    have : (fun ω => (f ω + C) * (g ω + C)) =
        fun ω => f ω * g ω + (C * f ω + (C * g ω + C * C)) := by
      funext ω; ring
    have e1 : ∫ ω, f ω * g ω + (C * f ω + (C * g ω + C * C)) ∂μ =
        (∫ ω, f ω * g ω ∂μ) + ∫ ω, C * f ω + (C * g ω + C * C) ∂μ :=
      integral_add hfgi ((hfi.const_mul C).add ((hgi.const_mul C).add (integrable_const _)))
    have e2 : ∫ ω, C * f ω + (C * g ω + C * C) ∂μ =
        (∫ ω, C * f ω ∂μ) + ∫ ω, C * g ω + C * C ∂μ :=
      integral_add (hfi.const_mul C) ((hgi.const_mul C).add (integrable_const _))
    have e3 : ∫ ω, C * g ω + C * C ∂μ = (∫ ω, C * g ω ∂μ) + ∫ _ω, C * C ∂μ :=
      integral_add (hgi.const_mul C) (integrable_const _)
    rw [this, e1, e2, e3, integral_const_mul, integral_const_mul]
    simp
  rw [hFint, hGint, hFGint] at key
  nlinarith [key]

/-- **A bounded monotone and a bounded antitone real function are negatively
correlated.** -/
theorem prodBernoulli_integral_mul_le_of_monotone_of_antitone (q : ι → unitInterval)
    {f g : Set ι → ℝ} {C : ℝ} (hf : Monotone f) (hg : Antitone g) (hfm : Measurable f)
    (hgm : Measurable g) (hfC : ∀ ω, |f ω| ≤ C) (hgC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, f ω * g ω ∂prodBernoulli q ≤
      (∫ ω, f ω ∂prodBernoulli q) * (∫ ω, g ω ∂prodBernoulli q) := by
  have h := prodBernoulli_integral_mul_le q (g := fun ω => -g ω) hf
    (fun _ _ h => neg_le_neg (hg h)) hfm hgm.neg hfC (fun ω => by rw [abs_neg]; exact hgC ω)
  simp only [mul_neg, integral_neg] at h
  linarith

/-- **Harris for bounded antitone real functions.** -/
theorem prodBernoulli_integral_mul_le_of_antitone (q : ι → unitInterval)
    {f g : Set ι → ℝ} {C : ℝ} (hf : Antitone f) (hg : Antitone g) (hfm : Measurable f)
    (hgm : Measurable g) (hfC : ∀ ω, |f ω| ≤ C) (hgC : ∀ ω, |g ω| ≤ C) :
    (∫ ω, f ω ∂prodBernoulli q) * (∫ ω, g ω ∂prodBernoulli q) ≤
      ∫ ω, f ω * g ω ∂prodBernoulli q := by
  have h := prodBernoulli_integral_mul_le q (f := fun ω => -f ω) (g := fun ω => -g ω)
    (fun _ _ h => neg_le_neg (hf h)) (fun _ _ h => neg_le_neg (hg h)) hfm.neg hgm.neg
    (fun ω => by rw [abs_neg]; exact hfC ω) (fun ω => by rw [abs_neg]; exact hgC ω)
  simpa only [neg_mul_neg, integral_neg] using h

end PercLib.Probability

/-! Non-vacuity: endpoint profiles taking the values `0` and `1`, a genuinely mixed pair at
`q = 1/2`, and monotone functions that are not indicators. -/
section Witnesses

open MeasureTheory Set PercLib.Probability

/-- Decreasing Harris with a profile taking the values `0` and `1`. -/
example :
    let q : Bool → unitInterval := fun b => if b then 1 else 0
    prodBernoulli q {ω | false ∉ ω} * prodBernoulli q {ω | true ∉ ω} ≤
      prodBernoulli q ({ω | false ∉ ω} ∩ {ω | true ∉ ω}) :=
  prodBernoulli_harris_of_isLowerSet _ (fun _ _ h hx hf => hx (h hf))
    (fun _ _ h hx hf => hx (h hf)) (measurableSet_mem false).compl
    (measurableSet_mem true).compl

/-- A genuinely mixed pair on `Fin 2` at `q = 1/2`: "0 is open" against "0 is closed or
1 is closed". -/
example :
    let q : Fin 2 → unitInterval := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
    prodBernoulli q ({ω | 0 ∈ ω} ∩ {ω | 0 ∉ ω ∨ 1 ∉ ω}) ≤
      prodBernoulli q {ω | 0 ∈ ω} * prodBernoulli q {ω | 0 ∉ ω ∨ 1 ∉ ω} :=
  prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet _ (fun _ _ h hx => h hx)
    (fun _ _ h hx => hx.imp (fun h0 h0' => h0 (h h0')) (fun h1 h1' => h1 (h h1')))
    (measurableSet_mem 0) ((measurableSet_mem 0).compl.union (measurableSet_mem 1).compl)

open Classical in
/-- The function form for a monotone function taking the value `∞`, with no integrability
hypothesis. -/
example (q : ℕ → unitInterval) :
    let f : Set ℕ → ℝ≥0∞ := fun ω => if 0 ∈ ω then ∞ else 1
    (∫⁻ ω, f ω ∂prodBernoulli q) * (∫⁻ ω, f ω ∂prodBernoulli q) ≤
      ∫⁻ ω, f ω * f ω ∂prodBernoulli q := by
  intro f
  have hf : Monotone f := fun a b h => by
    by_cases ha : 0 ∈ a
    · simp [f, ha, h ha]
    · simp only [f, ha, ite_false]
      split_ifs <;> simp
  exact prodBernoulli_lintegral_mul_le q hf hf
    (Measurable.ite (measurableSet_mem 0) measurable_const measurable_const)
    (Measurable.ite (measurableSet_mem 0) measurable_const measurable_const)

open Classical in
/-- The real function form at the boundary profile `q = 1` on `Bool`. -/
example :
    let q : Bool → unitInterval := fun _ => 1
    let f : Set Bool → ℝ := fun ω => if true ∈ ω then 1 else 0
    (∫ ω, f ω ∂prodBernoulli q) * (∫ ω, f ω ∂prodBernoulli q) ≤
      ∫ ω, f ω * f ω ∂prodBernoulli q := by
  intro q f
  have hf : Monotone f := fun a b h => by
    by_cases ha : true ∈ a
    · simp [f, ha, h ha]
    · simp only [f, ha, ite_false]
      split_ifs <;> norm_num
  have hfm : Measurable f := Measurable.ite (measurableSet_mem true) measurable_const
    measurable_const
  have hfC : ∀ ω, |f ω| ≤ 1 := fun ω => by
    simp only [f]
    split_ifs <;> norm_num
  exact prodBernoulli_integral_mul_le q hf hf hfm hfm hfC hfC

end Witnesses
