/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Layer-cake engines for Harris--FKG and the two-cluster BK inequality

This file contains the purely measure-theoretic core of Lemma I.2.1 of Hutchcroft,
arXiv:2508.18807v1 (p. 21), for *general* increasing non-negative functions `F`, `G` rather than
indicator functions: the passage from indicator inequalities to functionals is done by
two-dimensional layer cake (Cavalieri) plus Tonelli, with no monotone-class or finiteness
hypotheses.

The two inputs are stated as hypotheses on level sets:

* `LevelFKG` : `μ {f > s} * μ {g > t} ≤ μ ({f > s} ∩ {g > t})` (Harris--FKG in indicator form),
* `LevelTwoCluster` : `μ (C ∩ {f > s} ∩ {g > t}) ≤ μ {f > s} * μ {g > t}` (BK in indicator form,
  with `C` the event that two clusters are disjoint).

Nothing here is percolation-specific: `C` is an arbitrary measurable set and no order structure on
the probability space is used.  The order only enters in the discharge of the level-set hypotheses
for increasing functionals, which is done in `LemmaI21.lean`.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Percolation.LayerCake

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Layer cake at a point -/

/-- The integral over `t ∈ (0,∞)` of `1_{t < c}` is `c`; this is Cavalieri's principle for the
constant function with value `c` on the line. -/
lemma lintegral_Ioi_indicator_lt (c : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), (Iio c).indicator (fun _ => (1 : ℝ≥0∞)) t = ENNReal.ofReal c := by
  rw [setLIntegral_indicator measurableSet_Iio, setLIntegral_const, one_mul]
  have h : Iio c ∩ Ioi (0 : ℝ) = Ioo 0 c := by
    ext t; simp [Set.Ioo, Set.Ioi, Set.Iio, and_comm]
  rw [h, Real.volume_Ioo, sub_zero]

/-- The one-dimensional layer cake formula with an indicator factor (Cavalieri's principle),
for real-valued non-negative functions. -/
theorem lintegral_mul_indicator_eq {μ : Measure Ω} {h : Ω → ℝ} (hh0 : ∀ ω, 0 ≤ h ω)
    (hh : Measurable h) {B : Set Ω} (hB : MeasurableSet B) :
    ∫⁻ ω, (B.indicator (fun _ => (1 : ℝ≥0∞))) ω * ENNReal.ofReal (h ω) ∂μ
      = ∫⁻ s in Ioi (0 : ℝ), μ (B ∩ {ω | s < h ω}) := by
  have hcongr : ∫⁻ ω, (B.indicator (fun _ => (1 : ℝ≥0∞))) ω * ENNReal.ofReal (h ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal ((B.indicator (fun _ => (1 : ℝ))) ω * h ω) ∂μ := by
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_mul (indicator_nonneg (fun _ _ => zero_le_one) ω)]
    by_cases hω : ω ∈ B <;> simp [hω]
  rw [hcongr]
  have key := lintegral_eq_lintegral_meas_lt (μ := μ)
    (f := fun ω => (B.indicator (fun _ => (1 : ℝ))) ω * h ω)
    (by
      refine Filter.Eventually.of_forall fun ω => ?_
      by_cases hω : ω ∈ B <;> simp [hω, hh0 ω])
    ((measurable_const.indicator hB).mul hh).aemeasurable
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  congr 1
  ext ω
  by_cases hω : ω ∈ B
  · simp [hω]
  · have hge : ¬ (s < 0) := not_lt.mpr (le_of_lt hs)
    simp [hω, hge]

/-! ### The two-dimensional layer cake identity -/

/-- **Two-dimensional layer cake (Cavalieri) identity.**  For non-negative measurable real-valued
`f g` on a measure space and any measurable set `C`,

`∫⁻ ω, 1_C(ω) · (f ω · g ω) = ∫⁻ (s,t), μ (C ∩ {f > s} ∩ {g > t})`,

where `(s,t)` runs over `(0,∞) × (0,∞)`.  This is the engine behind the passage from
indicator inequalities (Harris--FKG, BK) to inequalities for general increasing functionals. -/
theorem lintegral_mul_indicator_eq_double {μ : Measure Ω} [SFinite μ] {f g : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hf : Measurable f) (hg : Measurable g)
    {C : Set Ω} (hC : MeasurableSet C) :
    ∫⁻ ω, (C.indicator (fun _ => (1 : ℝ≥0∞))) ω * ENNReal.ofReal (f ω * g ω) ∂μ
      = ∫⁻ p : ℝ × ℝ,
          μ (C ∩ {ω | p.1 < f ω} ∩ {ω | p.2 < g ω})
            ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  classical
  set H : (ℝ × ℝ) × Ω → ℝ≥0∞ := fun q =>
    (C.indicator (fun _ => (1 : ℝ≥0∞))) q.2 *
      ((Iio (f q.2)).indicator (fun _ => (1 : ℝ≥0∞)) q.1.1 *
        (Iio (g q.2)).indicator (fun _ => (1 : ℝ≥0∞)) q.1.2) with hHdef
  have hA : Measurable fun q : (ℝ × ℝ) × Ω =>
      (Iio (f q.2)).indicator (fun _ => (1 : ℝ≥0∞)) q.1.1 := by
    have heq : (fun q : (ℝ × ℝ) × Ω =>
        (Iio (f q.2)).indicator (fun _ => (1 : ℝ≥0∞)) q.1.1)
        = ({q : (ℝ × ℝ) × Ω | q.1.1 < f q.2}).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext q; simp [Set.indicator_apply, Set.mem_Iio]
    rw [heq]
    exact measurable_const.indicator (measurableSet_lt measurable_fst.fst (hf.comp measurable_snd))
  have hB : Measurable fun q : (ℝ × ℝ) × Ω =>
      (Iio (g q.2)).indicator (fun _ => (1 : ℝ≥0∞)) q.1.2 := by
    have heq : (fun q : (ℝ × ℝ) × Ω =>
        (Iio (g q.2)).indicator (fun _ => (1 : ℝ≥0∞)) q.1.2)
        = ({q : (ℝ × ℝ) × Ω | q.1.2 < g q.2}).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext q; simp [Set.indicator_apply, Set.mem_Iio]
    rw [heq]
    exact measurable_const.indicator (measurableSet_lt measurable_fst.snd (hg.comp measurable_snd))
  have hC' : Measurable fun q : (ℝ × ℝ) × Ω =>
      (C.indicator (fun _ => (1 : ℝ≥0∞))) q.2 :=
    (measurable_const.indicator hC).comp measurable_snd
  have hHm : Measurable H := hC'.mul (hA.mul hB)
  have hpt : ∀ ω : Ω, ∫⁻ p : ℝ × ℝ, H (p, ω)
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))
      = (C.indicator (fun _ => (1 : ℝ≥0∞))) ω *
          (ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω)) := by
    intro ω
    have hm1 : Measurable fun s : ℝ => (Iio (f ω)).indicator (fun _ => (1 : ℝ≥0∞)) s :=
      measurable_const.indicator measurableSet_Iio
    have hm2 : Measurable fun t : ℝ => (Iio (g ω)).indicator (fun _ => (1 : ℝ≥0∞)) t :=
      measurable_const.indicator measurableSet_Iio
    have hval : ∀ p : ℝ × ℝ, H (p, ω) =
        (C.indicator (fun _ => (1 : ℝ≥0∞))) ω *
          ((Iio (f ω)).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
            (Iio (g ω)).indicator (fun _ => (1 : ℝ≥0∞)) p.2) := fun p => rfl
    simp only [hval]
    have hm12 : Measurable fun p : ℝ × ℝ =>
        (Iio (f ω)).indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
          (Iio (g ω)).indicator (fun _ => (1 : ℝ≥0∞)) p.2 :=
      (hm1.comp measurable_fst).mul (hm2.comp measurable_snd)
    rw [lintegral_const_mul _ hm12,
      lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable,
      lintegral_Ioi_indicator_lt (f ω), lintegral_Ioi_indicator_lt (g ω)]
  have hset : ∀ p : ℝ × ℝ, MeasurableSet (C ∩ {ω | p.1 < f ω} ∩ {ω | p.2 < g ω}) := fun p =>
    (hC.inter (measurableSet_lt measurable_const hf)).inter
      (measurableSet_lt measurable_const hg)
  have hpt' : ∀ p : ℝ × ℝ, ∫⁻ ω, H (p, ω) ∂μ
      = μ (C ∩ {ω | p.1 < f ω} ∩ {ω | p.2 < g ω}) := by
    intro p
    have hval : ∀ ω : Ω, H (p, ω) =
        (C ∩ {ω | p.1 < f ω} ∩ {ω | p.2 < g ω}).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
      intro ω
      simp only [hHdef, Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio]
      by_cases h1 : ω ∈ C <;> by_cases h2 : p.1 < f ω <;> by_cases h3 : p.2 < g ω <;>
        simp [h1, h2, h3]
    simp only [hval]
    exact lintegral_indicator_one (hset p)
  have hswap : ∫⁻ ω, ∫⁻ p : ℝ × ℝ, H (p, ω)
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∂μ
      = ∫⁻ p : ℝ × ℝ, ∫⁻ ω, H (p, ω) ∂μ
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    lintegral_lintegral_swap (f := fun ω p => H (p, ω))
      (hHm.comp measurable_swap).aemeasurable
  calc ∫⁻ ω, (C.indicator (fun _ => (1 : ℝ≥0∞))) ω * ENNReal.ofReal (f ω * g ω) ∂μ
      = ∫⁻ ω, (C.indicator (fun _ => (1 : ℝ≥0∞))) ω *
          (ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω)) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_mul (hf0 ω)]
    _ = ∫⁻ ω, ∫⁻ p : ℝ × ℝ, H (p, ω)
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∂μ := by
        simp only [hpt]
    _ = ∫⁻ p : ℝ × ℝ, ∫⁻ ω, H (p, ω) ∂μ
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := hswap
    _ = ∫⁻ p : ℝ × ℝ, μ (C ∩ {ω | p.1 < f ω} ∩ {ω | p.2 < g ω})
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
        simp only [hpt']

/-! ### Level-set measure functions -/

/-- `levelMeas μ f s = μ {ω | s < f ω}`: the tail measure of `f` at level `s`. -/
noncomputable def levelMeas (μ : Measure Ω) (f : Ω → ℝ) (s : ℝ) : ℝ≥0∞ := μ {ω | s < f ω}

lemma antitone_levelMeas (μ : Measure Ω) (f : Ω → ℝ) : Antitone (levelMeas μ f) :=
  fun _ _ hst => measure_mono fun _ hω => lt_of_le_of_lt hst hω

lemma measurable_levelMeas (μ : Measure Ω) (f : Ω → ℝ) : Measurable (levelMeas μ f) :=
  (antitone_levelMeas μ f).measurable

/-- One-dimensional layer cake in terms of `levelMeas`. -/
lemma lintegral_levelMeas {μ : Measure Ω} {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hf : Measurable f) :
    ∫⁻ s in Ioi (0 : ℝ), levelMeas μ f s = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
  have h := lintegral_mul_indicator_eq (μ := μ) hf0 hf (B := univ) MeasurableSet.univ
  simpa [levelMeas] using h.symm

/-! ### Lemma I.2.1 for general increasing functionals -/

/-- **Two-cluster inequality for general functionals** (Lemma I.2.1(i) of
Hutchcroft, arXiv:2508.18807v1, p. 21, for arbitrary non-negative `f`, `g` rather than
indicators).

If the level sets of `f` and `g` satisfy the two-cluster BK inequality on `C`,
`μ (C ∩ {f > s} ∩ {g > t}) ≤ μ {f > s} · μ {g > t}`, then
`∫_C f g ≤ (∫ f)(∫ g)`. -/
theorem lintegral_mul_indicator_le_of_meas_lt {μ : Measure Ω} [SFinite μ] {f g : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hf : Measurable f) (hg : Measurable g)
    {C : Set Ω} (hC : MeasurableSet C)
    (h : ∀ s t : ℝ, 0 < s → 0 < t →
      μ (C ∩ {ω | s < f ω} ∩ {ω | t < g ω}) ≤ μ {ω | s < f ω} * μ {ω | t < g ω}) :
    ∫⁻ ω, (C.indicator (fun _ => (1 : ℝ≥0∞))) ω * ENNReal.ofReal (f ω * g ω) ∂μ
      ≤ (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) * (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) := by
  rw [lintegral_mul_indicator_eq_double hf0 hg0 hf hg hC]
  set κ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hκ
  have hmem : ∀ᵐ s ∂κ, 0 < s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hs
  have hae : ∀ᵐ p ∂(κ.prod κ), 0 < p.1 ∧ 0 < p.2 := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem (s := {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2}) ?_).2 ?_
    · exact (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_const measurable_snd)
    · filter_upwards [hmem] with s hs
      filter_upwards [hmem] with t ht
      exact ⟨hs, ht⟩
  have hle : ∀ᵐ p ∂(κ.prod κ),
      μ (C ∩ {ω | p.1 < f ω} ∩ {ω | p.2 < g ω}) ≤ levelMeas μ f p.1 * levelMeas μ g p.2 := by
    filter_upwards [hae] with p hp using h p.1 p.2 hp.1 hp.2
  refine le_trans (lintegral_mono_ae hle) (le_of_eq ?_)
  have hfl : ∫⁻ s, levelMeas μ f s ∂κ = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
    simpa [hκ] using lintegral_levelMeas (μ := μ) hf0 hf
  have hgl : ∫⁻ s, levelMeas μ g s ∂κ = ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := by
    simpa [hκ] using lintegral_levelMeas (μ := μ) hg0 hg
  have hprod : ∫⁻ p : ℝ × ℝ, levelMeas μ f p.1 * levelMeas μ g p.2 ∂(κ.prod κ)
      = (∫⁻ s, levelMeas μ f s ∂κ) * (∫⁻ t, levelMeas μ g t ∂κ) :=
    lintegral_prod_mul (measurable_levelMeas μ f).aemeasurable
      (measurable_levelMeas μ g).aemeasurable
  rw [hprod, hfl, hgl]

/-- **Harris--FKG for general increasing functionals.**  If the level sets of `f` and `g`
satisfy the indicator FKG inequality `μ{f>s}·μ{g>t} ≤ μ({f>s}∩{g>t})`, then
`(∫ f)(∫ g) ≤ ∫ f g`.  This is the passage from the indicator Harris--FKG inequality to general
increasing observables (the first display of Section I.2.1 of Hutchcroft, arXiv:2508.18807v1). -/
theorem lintegral_mul_ge_of_meas_lt {μ : Measure Ω} [SFinite μ] {f g : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ s t : ℝ, 0 < s → 0 < t →
      μ {ω | s < f ω} * μ {ω | t < g ω} ≤ μ ({ω | s < f ω} ∩ {ω | t < g ω})) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) * (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ)
      ≤ ∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂μ := by
  have h0 := lintegral_mul_indicator_eq_double (μ := μ) hf0 hg0 hf hg (C := univ) MeasurableSet.univ
  simp only [Set.univ_inter, Set.indicator_univ, one_mul] at h0
  rw [h0]
  set κ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hκ
  have hmem : ∀ᵐ s ∂κ, 0 < s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hs
  have hae : ∀ᵐ p ∂(κ.prod κ), 0 < p.1 ∧ 0 < p.2 := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem (s := {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2}) ?_).2 ?_
    · exact (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_const measurable_snd)
    · filter_upwards [hmem] with s hs
      filter_upwards [hmem] with t ht
      exact ⟨hs, ht⟩
  have hle : ∀ᵐ p ∂(κ.prod κ),
      levelMeas μ f p.1 * levelMeas μ g p.2 ≤ μ ({ω | p.1 < f ω} ∩ {ω | p.2 < g ω}) := by
    filter_upwards [hae] with p hp using h p.1 p.2 hp.1 hp.2
  have hfl : ∫⁻ s, levelMeas μ f s ∂κ = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
    simpa [hκ] using lintegral_levelMeas (μ := μ) hf0 hf
  have hgl : ∫⁻ s, levelMeas μ g s ∂κ = ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := by
    simpa [hκ] using lintegral_levelMeas (μ := μ) hg0 hg
  have hprod : ∫⁻ p : ℝ × ℝ, levelMeas μ f p.1 * levelMeas μ g p.2 ∂(κ.prod κ)
      = (∫⁻ s, levelMeas μ f s ∂κ) * (∫⁻ t, levelMeas μ g t ∂κ) :=
    lintegral_prod_mul (measurable_levelMeas μ f).aemeasurable
      (measurable_levelMeas μ g).aemeasurable
  calc (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) * (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ)
      = ∫⁻ p : ℝ × ℝ, levelMeas μ f p.1 * levelMeas μ g p.2 ∂(κ.prod κ) := by
        rw [hprod, hfl, hgl]
    _ ≤ ∫⁻ p : ℝ × ℝ, μ ({ω | p.1 < f ω} ∩ {ω | p.2 < g ω}) ∂(κ.prod κ) :=
        lintegral_mono_ae hle

end PercLib.CriticalLRP.Percolation.LayerCake
