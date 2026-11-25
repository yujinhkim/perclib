/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Weighted Karamata integration on a positive tail

Supporting material for the inhomogeneous ODE lemmas of Hutchcroft,
*Critical long-range percolation I*.  A zero extension below the starting
cut preserves regular variation and is locally integrable on the positive axis.
Positive-index measurable regular variation supplies interval integrability
on its positive tail.  The final theorem integrates with a signed multiplier
`1 - δ`, where `δ → 0`, and keeps the lower normalization explicit:
`∫_{r₀}^r (1-δ)g / (r g(r)) → 1/(c+1)` when `g` has index `c > -1`.

These are analytic inputs to Lemma I.4.21, not the ODE theorem itself.
-/
module

public import PercLib.CriticalLRP.Analysis.GeneralInverse

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

/-- A zero extension of a function integrable on all intervals to the right of a cut. -/
theorem intervalIntegrable_indicator_Ioi_of_intervalIntegrable {g : ℝ → ℝ} {r₀ : ℝ}
    (h : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntegrableOn g (Ioc x y) volume)
    (a b : ℝ) : IntervalIntegrable ((Ioi r₀).indicator g) volume a b := by
  have fragment : ∀ a b : ℝ,
      IntegrableOn ((Ioi r₀).indicator g) (Ioc a b) volume := by
    intro a b
    have hset : Ioc a b ∩ Ioi r₀ = Ioc (max a r₀) b := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨hax, hxb⟩, hr₀x⟩
        exact ⟨max_lt hax hr₀x, hxb⟩
      · rintro ⟨hx, hxb⟩
        exact ⟨⟨(le_max_left _ _).trans_lt hx, hxb⟩,
          (le_max_right _ _).trans_lt hx⟩
    have hg : IntegrableOn ((Ioi r₀).indicator g) (Ioc a b ∩ Ioi r₀) volume := by
      rw [hset]
      by_cases hb : max a r₀ ≤ b
      · have hi := h (max a r₀) b (le_max_right _ _) hb
        exact (integrableOn_congr_fun (fun x hx => Set.indicator_of_mem
          (Set.mem_Ioi.2 ((le_max_right _ _).trans_lt hx.1)) g) measurableSet_Ioc).mpr hi
      · have hempty : Ioc (max a r₀) b = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact hb (le_trans hx.1.le hx.2)
        rw [hempty]
        exact integrableOn_empty
    have hzero : IntegrableOn ((Ioi r₀).indicator g) (Ioc a b ∩ (Ioi r₀)ᶜ) volume := by
      apply (integrableOn_congr_fun (f := fun _ : ℝ => (0 : ℝ)) ?_
        (measurableSet_Ioc.inter measurableSet_Ioi.compl)).mp integrableOn_zero
      intro x hx
      simp only [Set.indicator_of_notMem
        (fun hmem => hx.2 (Set.mem_Ioi.1 hmem)) g]
    rw [show Ioc a b = (Ioc a b ∩ Ioi r₀) ∪ (Ioc a b ∩ (Ioi r₀)ᶜ) by
      exact (inter_union_compl _ _).symm]
    exact hg.union hzero
  exact ⟨fragment a b, fragment b a⟩

/-- The zero extension is locally integrable on the positive axis. -/
theorem locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable {g : ℝ → ℝ} {r₀ : ℝ}
    (h : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y) :
    LocallyIntegrableOn ((Ioi r₀).indicator g) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isLocallyClosed_Ioi]
  intro K hK hKc
  rcases K.eq_empty_or_nonempty with rfl | hKn
  · exact integrableOn_empty
  obtain ⟨m, hm⟩ := hKc.bddBelow
  obtain ⟨M, hM⟩ := hKc.bddAbove
  obtain ⟨x, hx⟩ := hKn
  have hmM : m ≤ M := le_trans (hm hx) (hM hx)
  have hsub : K ⊆ Icc m M := fun y hy => ⟨hm hy, hM hy⟩
  have hInt : IntegrableOn ((Ioi r₀).indicator g) (Icc m M) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hmM (by simp)).1
      (intervalIntegrable_indicator_Ioi_of_intervalIntegrable
        (fun x y hx hxy => (h x y hx hxy).1) m M)
  exact hInt.mono_set hsub

/-- Regular variation is unchanged by zero-extension below a fixed cut. -/
theorem regularlyVarying_indicator_Ioi {g : ℝ → ℝ} {r₀ ρ : ℝ}
    (hrv : RegularlyVaryingAtTop g ρ) :
    RegularlyVaryingAtTop ((Ioi r₀).indicator g) ρ := by
  constructor
  · filter_upwards [hrv.1, eventually_gt_atTop r₀] with x hx hx₀
    rw [Set.indicator_of_mem (Set.mem_Ioi.2 hx₀) g]
    exact hx
  · intro l hl
    have hscale : Tendsto (fun x : ℝ => l * x) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hl).mpr tendsto_id
    apply (hrv.2 l hl).congr'
    filter_upwards [eventually_gt_atTop r₀, hscale.eventually (eventually_gt_atTop r₀)]
      with x hx hlx
    rw [Set.indicator_of_mem (Set.mem_Ioi.2 hlx) g, Set.indicator_of_mem (Set.mem_Ioi.2 hx) g]

/-- Locally integrable positive tails for measurable regularly varying functions. -/
theorem exists_intervalIntegrable_tail_of_regularlyVarying {g : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hgm : Measurable g) (hrv : RegularlyVaryingAtTop g ρ)
    (hpos : ∀ᶠ x in atTop, 0 < g x) :
    ∃ R : ℝ, 0 < R ∧ ∀ x y : ℝ, R ≤ x → x ≤ y →
      IntervalIntegrable g volume x y := by
  let D := RVPosData.of hρ hgm hrv hpos
  refine ⟨D.threshold, lt_of_lt_of_le one_pos D.one_le_threshold, ?_⟩
  intro x y hx hxy
  obtain ⟨C, hC⟩ := D.bddAbove_Icc y
  refine intervalIntegrable_of_bound (C := C) hgm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
  rw [uIcc_of_le hxy] at hs
  rw [Real.norm_eq_abs, abs_of_pos (D.pos_above s (le_trans hx hs.1))]
  exact hC s (le_trans hx hs.1) hs.2

/-- Karamata integration on a positive tail, with a multiplier converging to one. -/
theorem tendsto_mul_one_sub_karamata_integral_tail {g δ : ℝ → ℝ} {r₀ c : ℝ}
    (hc : -1 < c) (hr₀ : 0 < r₀) (hr₀1 : 1 ≤ r₀) (hgm : Measurable g)
    (hrv : RegularlyVaryingAtTop g c) (hpos : ∀ᶠ x in atTop, 0 < g x)
    (hlocal : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y)
    (hδm : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) :
    Tendsto (fun r => (∫ s in r₀..r, (1 - δ s) * g s) / (r * g r))
      atTop (𝓝 (1 / (c + 1))) := by
  let T : ℝ → ℝ := (Ioi r₀).indicator g
  let F : ℝ → ℝ := fun s => (1 - δ s) * T s
  have hTm : Measurable T := hgm.indicator measurableSet_Ioi
  have hTpos : ∀ᶠ x in atTop, 0 < T x := by
    filter_upwards [hpos, eventually_gt_atTop r₀] with x hx hx₀
    simp only [T, Set.indicator_of_mem (Set.mem_Ioi.2 hx₀) g]
    exact hx
  have hTrv : RegularlyVaryingAtTop T c := regularlyVarying_indicator_Ioi hrv
  have hTlocal : LocallyIntegrableOn T (Ioi 0) :=
    locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable hlocal
  have hFm : Measurable F := (measurable_const.sub hδm).mul hTm
  have hbase : LocallyIntegrableOn (fun x => 2 * ‖T x‖) (Ioi 0) := by
    intro x hx
    rcases hTlocal.norm x hx with ⟨U, hU, hi⟩
    exact ⟨U, hU, hi.const_mul 2⟩
  have hFbound : ∀ x, ‖F x‖ ≤ ‖2 * ‖T x‖‖ := by
    intro x
    by_cases hx : r₀ < x
    · have hδ := hδ1 x hx.le
      have hfac : |1 - δ x| ≤ 2 := by
        calc |1 - δ x| ≤ |1| + |δ x| := abs_sub _ _
          _ ≤ 2 := by rw [abs_one]; linarith
      calc ‖F x‖ = |1 - δ x| * |T x| := by rw [Real.norm_eq_abs, abs_mul]
        _ ≤ 2 * |T x| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
        _ = ‖2 * ‖T x‖‖ := by
          simp only [Real.norm_eq_abs, abs_mul,
            abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_nonneg (abs_nonneg _)]
    · have hTx : T x = 0 := by
        simp [T, Set.indicator_of_notMem (fun hm => hx (Set.mem_Ioi.1 hm)) g]
      simp [F, hTx]
  have hFlocal : LocallyIntegrableOn F (Ioi 0) :=
    hbase.mono hFm.aestronglyMeasurable (Eventually.of_forall hFbound)
  have hfac : Tendsto (fun x => 1 - δ x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hδ0
  have hfacpos : ∀ᶠ x in atTop, 0 < 1 - δ x :=
    hfac.eventually (eventually_gt_nhds zero_lt_one)
  have hFT : Tendsto (fun x => F x / T x) atTop (𝓝 1) := by
    apply hfac.congr'
    filter_upwards [hTpos] with x hx
    symm
    exact div_eq_iff hx.ne' |>.mpr rfl
  have hFrv : RegularlyVaryingAtTop F c :=
    RegularlyVaryingAtTop.of_tendsto_div hTrv hFT
  have hFpos : ∀ᶠ x in atTop, 0 < F x := by
    filter_upwards [hfacpos, hTpos] with x hx hxT
    exact mul_pos hx hxT
  have hFint : ∀ x y : ℝ, 0 < x → x ≤ y → IntervalIntegrable F volume x y := by
    intro x y hx hxy
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    exact (locallyIntegrableOn_iff isLocallyClosed_Ioi).1 hFlocal (Icc x y)
      (fun z hz => lt_of_lt_of_le hx hz.1) isCompact_Icc
  have hK : Tendsto (fun r => (∫ s in 1..r, F s) / (r * F r))
      atTop (𝓝 (1 / (c + 1))) :=
    lemma_I_2_10_of_regularlyVarying (by linarith) hFm hFlocal hFpos hFrv
  have hFTg : Tendsto (fun r => F r / g r) atTop (𝓝 1) := by
    apply hFT.congr'
    filter_upwards [hpos, eventually_gt_atTop r₀] with r hr hr₀r
    rw [show T r = g r by simp [T, Set.indicator_of_mem (Set.mem_Ioi.2 hr₀r) g]]
  have hden : Tendsto (fun r => (r * F r) / (r * g r)) atTop (𝓝 1) := by
    apply hFTg.congr'
    filter_upwards [hpos, eventually_gt_atTop (0 : ℝ), hFpos] with r hr hr0 hrF
    field_simp
  have hnormalized : Tendsto (fun r => (∫ s in 1..r, F s) / (r * g r))
      atTop (𝓝 (1 / (c + 1))) := by
    have hm := hK.mul hden
    rw [mul_one] at hm
    apply hm.congr'
    filter_upwards [hFpos, hpos] with r hrF hr
    field_simp
  apply hnormalized.congr'
  filter_upwards [eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  have hzero : (∫ s in 1..r₀, F s) = 0 := by
    have hz : EqOn F (fun _ => 0) (uIcc 1 r₀) := by
      intro x hx
      rw [uIcc_of_le hr₀1] at hx
      by_cases hxr : r₀ < x
      · exact (not_le.2 hxr hx.2).elim
      · simp [F, T, Set.indicator_of_notMem (fun hm => hxr (Set.mem_Ioi.1 hm)) g]
    calc (∫ s in 1..r₀, F s) = ∫ _s in 1..r₀, (0 : ℝ) :=
      intervalIntegral.integral_congr hz
    _ = 0 := intervalIntegral.integral_zero
  have hFint' : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable F volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · exact hFint x y hx hxy
    · exact (hFint y x hy hyx).symm
  have hsplit : (∫ s in 1..r, F s) = ∫ s in r₀..r, F s := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hFint' 1 r₀ one_pos hr₀) (hFint' r₀ r hr₀ (lt_of_lt_of_le zero_lt_one hr1))
    rw [hzero, zero_add] at hadd
    exact hadd.symm
  rw [hsplit]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  rw [uIoc_of_le hr] at hx
  simp [F, T, Set.indicator_of_mem (Set.mem_Ioi.2 hx.1) g]

end PercLib.CriticalLRP.Analysis
