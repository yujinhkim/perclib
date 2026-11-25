/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
**The Tauberian converse of Theorem I.2.11, completed** (Hutchcroft, arXiv:2508.18807v1, p. 26;
after Feller XIII.5.2).

Main results of this file (all sorry-free, on the standard axioms only):

* `exists_limitProfile_eq_rpow_ae_and_tendsto_one`: for the *exact* hypotheses of the problem
  (`0 ≤ α < 1`; `F` measurable, nonnegative, antitone; `f` measurable and regularly varying of
  index `-α`; the kernel-form Laplace hypothesis; any positive `hseq → 0`) there are rational
  limit values `L` and a renumbering `ns` with
  `limitProfile L =ᵐ[volume.restrict (Ioi 0)] (fun u => u ^ (-α))` **and**
  `Tendsto (fun n => Phi α F f (hseq (ns n)) 1) atTop (𝓝 1)`.
* `limitProfile_eq_rpow_ae`: the first conclusion for arbitrary `L, hseq` satisfying the
  hypotheses of `exists_rational_limit`.
* `tendsto_Phi_one`: the full-strength limit `Phi α F f h 1 → 1` as `h ↓ 0` (so *every*
  subsequence works: `tendsto_Phi_subseq_one`).
* `tendsto_tail_of_laplace`: the tail asymptotic `F x ~ f x / Γ(1-α)`.
* `laplace_asymptotic_iff_tail_ge`, `laplace_asymptotic_iff_tail_ge_rpow`: Theorem I.2.11 itself.

Proof architecture (each step is a declaration below):

1. near-zero mass `near_mass_Phi_eventually_le` and far-field domination
   `eventually_Phi_le_profileBound_of_le`;
2. dominated convergence of the Laplace transforms over `(δ,∞)`
   `tendsto_integral_exp_mul_Phi_Ioi`, the exact decomposition over `(0,δ) ∪ (δ,∞)`, and the
   truncation limit `tendsto_setIntegral_Ioi_zero`, giving the Laplace identity
   `integral_exp_mul_limitProfile : ∫ e^{-σu} ψ = Γ(1-α) σ^{α-1}` for every `σ > 0`;
3. weighted Laplace uniqueness `eq_zero_ae_of_forall_laplace_weighted` (the repo's unweighted
   injectivity applied to `u ↦ e^{-u} D u`, since the profile is not `L¹`) and
   `ae_eq_rpow_of_laplace`;
4. the squeeze at `u = 1` between good points `a < 1 < b` (`tendsto_one_of_antitone_squeeze`),
   subsequential compactness (`exists_rational_limit`) and the passage from subsequences to the
   full limit (`tendsto_Phi_one`).

Provenance: sections 1–4 are the previously verified development
`.ultramath/smwgebly0/m1/TauberianStrict.lean`, recompiled unchanged against the current tree;
the last section ("The completed converse: exact required conclusions") is new here and states
the two required conclusions in the problem's own terms, deriving the eventual positivity of the
normalising factor rather than assuming it.
-/
module

public import PercLib.CriticalLRP.Analysis.LaplaceUnique
public import PercLib.CriticalLRP.Analysis.TauberianConverse
public import PercLib.CriticalLRP.Analysis.TauberianEndpoints

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.Analysis

/-! ### Integrability of the comparison functions -/

/-- `u ↦ e^{-σu} u^{-α}` is integrable on `(0,∞)` when `α < 1` and `σ > 0`. -/
theorem integrableOn_exp_mul_rpow_neg {α σ : ℝ} (hα : α < 1) (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * u ^ (-α)) (Ioi (0:ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -α) (b := σ)
    (by linarith : (-1:ℝ) < -α) one_pos hσ
  simpa [mul_comm] using h

/-- `u ↦ e^{-σu} profileBound α u` is integrable on `(0,∞)` when `α < 1` and `σ > 0`. -/
theorem integrableOn_exp_mul_profileBound {α σ : ℝ} (hα : α < 1) (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * profileBound α u) (Ioi (0:ℝ)) := by
  have h := (integrableOn_exp_mul_rpow_neg (α := α) hα hσ).const_mul
    (Real.Gamma (1 - α) * ((3/2) * Real.exp 1))
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [profileBound]
  ring

/-! ### The normalised profile: monotonicity, positivity, near mass, domination -/

/-- `Phi α F f h` is antitone when the normalising factor `f (1/h)` is positive. -/
theorem Phi_antitone {F f : ℝ → ℝ} {α h : ℝ} (hα1 : α < 1) (hanti : Antitone F)
    (hh : 0 < h) (hf : 0 < f (1/h)) :
    Antitone fun u : ℝ => Phi α F f h u := by
  intro u v huv
  have hF : F (v/h) ≤ F (u/h) := hanti (by
    rw [div_le_div_iff_of_pos_right hh]
    exact huv)
  have hΓ : (0:ℝ) ≤ Real.Gamma (1 - α) := (Real.Gamma_pos_of_pos (by linarith)).le
  simp only [Phi]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF hΓ) hf.le

/-- `Phi α F f h` is nonnegative when `F ≥ 0` and `f (1/h) > 0`. -/
theorem Phi_nonneg {F f : ℝ → ℝ} {α h : ℝ} (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x)
    (hf : 0 < f (1/h)) :
    ∀ u : ℝ, 0 ≤ Phi α F f h u := by
  intro u
  have hΓ : (0:ℝ) ≤ Real.Gamma (1 - α) := (Real.Gamma_pos_of_pos (by linarith)).le
  simp only [Phi]
  exact div_nonneg (mul_nonneg hΓ (hF0 _)) hf.le

/-- **Near-zero mass of the normalised profile.**  For every `δ > 0`, eventually
`∫_0^δ Phi α F f h u du ≤ Γ(1-α)·2e·δ^{1-α}`. -/
theorem near_mass_Phi_eventually_le
    {F f : ℝ → ℝ} {α : ℝ}
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    (hα1 : α < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
      ∫ u in Ioo (0:ℝ) δ, Phi α F f h u
        ≤ Real.Gamma (1 - α) * (2 * Real.exp 1 * δ^(1-α)) := by
  have hbase := near_mass_eventually_le hFmeas hF0 hanti hfmeas hrv hmain hδ
  have hΓ : (0:ℝ) ≤ Real.Gamma (1 - α) := (Real.Gamma_pos_of_pos (by linarith)).le
  filter_upwards [hbase] with h hb
  have h1 : ∫ u in Ioo (0:ℝ) δ, Phi α F f h u
      = Real.Gamma (1 - α) * ∫ u in Ioo (0:ℝ) δ, F (u/h) / f (1/h) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo (fun u _ => ?_)
    simp only [Phi]
    ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left hb hΓ

/-- **Far-field domination.**  For every `δ > 0`, eventually in `h`,
`Phi α F f h u ≤ profileBound α δ` for all `u ≥ δ`. -/
theorem eventually_Phi_le_profileBound_of_le
    {F f : ℝ → ℝ} {α : ℝ}
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    (hα1 : α < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), ∀ u : ℝ, δ ≤ u → Phi α F f h u ≤ profileBound α δ := by
  have hb := eventually_profile_bound hFmeas hF0 hanti hfmeas hrv hmain hα1 hδ
  have hfpos := eventually_pos_f_inv hF0 hmain
  have hΓ : (0:ℝ) < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  filter_upwards [hb, hfpos, self_mem_nhdsWithin] with h hb' hf' hh
  intro u hu
  have h1 : F (u/h) ≤ F (δ/h) := hanti (by
    rw [div_le_div_iff_of_pos_right hh]
    exact hu)
  have h2 : Phi α F f h u ≤ Phi α F f h δ := by
    simp only [Phi]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hΓ.le) hf'.le
  exact le_trans h2 hb'.2

/-! ### Truncating an integral at `δ ↓ 0` -/

/-- For `g ≥ 0` integrable on `(0,∞)`, the integrals over `(δ,∞)` tend to the integral over
`(0,∞)` as `δ ↓ 0`. -/
theorem tendsto_setIntegral_Ioi_zero {g : ℝ → ℝ}
    (hgmeas : AEStronglyMeasurable g (volume.restrict (Ioi (0:ℝ))))
    (hgnn : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), 0 ≤ g u)
    (hgint : IntegrableOn g (Ioi (0:ℝ))) :
    Tendsto (fun δ : ℝ => ∫ u in Ioi δ, g u) (𝓝[>] (0:ℝ)) (𝓝 (∫ u in Ioi (0:ℝ), g u)) := by
  set μ := volume.restrict (Ioi (0:ℝ)) with hμ
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ u ∂μ, ‖(Ioi δ).indicator g u‖ ≤ g u := by
    filter_upwards with δ
    filter_upwards [hgnn, ae_restrict_mem measurableSet_Ioi] with u hgn hu
    rw [Set.indicator_apply]
    split_ifs with hmem
    · rw [Real.norm_eq_abs, abs_of_nonneg hgn]
    · rw [norm_zero]
      exact hgn
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun δ : ℝ => (Ioi δ).indicator g u)
      (𝓝[>] (0:ℝ)) (𝓝 (g u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hev : ∀ᶠ δ : ℝ in 𝓝[>] (0:ℝ), u ∈ Ioi δ := by
      have h1 : ∀ᶠ δ : ℝ in 𝓝 (0:ℝ), δ < u := eventually_lt_nhds hu
      exact h1.filter_mono nhdsWithin_le_nhds
    refine Tendsto.congr' (hev.mono (fun δ hδ => ?_)) tendsto_const_nhds
    simp only [Set.indicator_of_mem hδ]
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝[>] (0:ℝ)) (ι := ℝ)
    (F := fun δ : ℝ => (Ioi δ).indicator g) (f := g) (bound := g)
    (Filter.Eventually.of_forall (fun δ => (hgmeas.indicator measurableSet_Ioi))) hbound hgint hlim
  have hrewrite : (fun δ : ℝ => ∫ u, (Ioi δ).indicator g u ∂μ)
      =ᶠ[𝓝[>] (0:ℝ)] fun δ : ℝ => ∫ u in Ioi δ, g u := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hset : Ioi δ ∩ Ioi (0:ℝ) = Ioi δ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, lt_trans hδ h⟩
    rw [hμ, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hset]
  exact hmain.congr' hrewrite

/-! ### Good points are dense -/

/-- A property that holds almost everywhere on `(0,∞)` holds somewhere in every open interval
`(a,b) ⊆ (0,∞)`. -/
theorem exists_mem_of_ae_restrict {P : ℝ → Prop}
    (hP : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), P u)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) : ∃ u : ℝ, a < u ∧ u < b ∧ P u := by
  by_contra hcon
  push Not at hcon
  have hnull : volume.restrict (Ioi (0:ℝ)) {u : ℝ | ¬ P u} = 0 := ae_iff.mp hP
  have hsub : Ioo a b ⊆ {u : ℝ | ¬ P u} := fun u hu => hcon u hu.1 hu.2
  have hle : volume (Ioo a b) ≤ volume.restrict (Ioi (0:ℝ)) {u : ℝ | ¬ P u} := by
    have hset : Ioo a b ∩ Ioi (0:ℝ) = Ioo a b := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, lt_trans ha h.1⟩
    have h1 : volume.restrict (Ioi (0:ℝ)) (Ioo a b) = volume (Ioo a b) := by
      rw [Measure.restrict_apply measurableSet_Ioo, hset]
    rw [← h1]
    exact measure_mono hsub
  rw [hnull] at hle
  have hpos : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  exact hpos (nonpos_iff_eq_zero.mp hle)

/-- **Dense good points below `1`.** -/
theorem exists_good_below {α : ℝ} {P : ℝ → Prop}
    (hP : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), P u) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ P a ∧ a ^ (-α) < 1 + ε := by
  have hcont : Tendsto (fun u : ℝ => u ^ (-α)) (𝓝 (1:ℝ)) (𝓝 ((1:ℝ) ^ (-α))) :=
    Real.continuousAt_rpow_const 1 (-α) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hcont
  have hball : ∀ᶠ u : ℝ in 𝓝 (1:ℝ), dist (u ^ (-α)) 1 < ε :=
    Metric.tendsto_nhds.mp hcont ε hε
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.mp hball
  set c := min (1/2) η with hc
  have hcpos : 0 < c := lt_min (by norm_num) hη
  have hcη : c ≤ η := min_le_right _ _
  have hc1 : c ≤ 1/2 := min_le_left _ _
  obtain ⟨u, hu1, hu2, huP⟩ := exists_mem_of_ae_restrict hP (a := 1 - c) (b := 1)
    (by linarith) (by linarith)
  refine ⟨u, by linarith, hu2, huP, ?_⟩
  have hdist : dist u (1:ℝ) < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hd : dist (u ^ (-α)) 1 < ε := hηb hdist
  rw [Real.dist_eq] at hd
  linarith [(abs_lt.mp hd).2]

/-- **Dense good points above `1`.** -/
theorem exists_good_above {α : ℝ} {P : ℝ → Prop}
    (hP : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), P u) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, 1 < b ∧ b < 2 ∧ P b ∧ 1 - ε < b ^ (-α) := by
  have hcont : Tendsto (fun u : ℝ => u ^ (-α)) (𝓝 (1:ℝ)) (𝓝 ((1:ℝ) ^ (-α))) :=
    Real.continuousAt_rpow_const 1 (-α) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hcont
  have hball : ∀ᶠ u : ℝ in 𝓝 (1:ℝ), dist (u ^ (-α)) 1 < ε :=
    Metric.tendsto_nhds.mp hcont ε hε
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.mp hball
  set c := min 1 η with hc
  have hcpos : 0 < c := lt_min one_pos hη
  have hcη : c ≤ η := min_le_right _ _
  have hc1 : c ≤ 1 := min_le_left _ _
  obtain ⟨u, hu1, hu2, huP⟩ := exists_mem_of_ae_restrict hP (a := 1) (b := 1 + c)
    (by norm_num) (by linarith)
  refine ⟨u, hu1, by linarith, huP, ?_⟩
  have hdist : dist u (1:ℝ) < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hd : dist (u ^ (-α)) 1 < ε := hηb hdist
  rw [Real.dist_eq] at hd
  linarith [(abs_lt.mp hd).1]

/-! ### The Laplace transform of the normalised profile -/

/-- The Laplace transform of `Phi` written as `Γ(1-α)` times the Laplace transform of the
unnormalised profile, divided by the normalising constant. -/
theorem integral_exp_mul_Phi_eq {F f : ℝ → ℝ} {α σ h : ℝ} :
    ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * Phi α F f h u
      = Real.Gamma (1 - α) *
          ((∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h)) / f (1/h)) := by
  have h1 : ∀ u : ℝ, Real.exp (-(σ*u)) * Phi α F f h u
      = Real.Gamma (1 - α) * (Real.exp (-(σ*u)) * F (u/h)) / f (1/h) := by
    intro u
    simp only [Phi]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => h1 u)]
  rw [integral_div, integral_const_mul]
  ring

/-- **The Laplace family at every rate.** -/
theorem tendsto_integral_exp_mul_Phi
    {F f : ℝ → ℝ} {α : ℝ}
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun h : ℝ => ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * Phi α F f h u)
      (𝓝[>] (0:ℝ)) (𝓝 (Real.Gamma (1 - α) * σ^(α-1))) := by
  have hfam := tendsto_laplace_family hFmeas hF0 hanti hfmeas hrv hmain hσ
  have h1 := hfam.const_mul (Real.Gamma (1 - α))
  refine h1.congr' ?_
  filter_upwards with h
  exact (integral_exp_mul_Phi_eq (F := F) (f := f) (α := α) (σ := σ) (h := h)).symm

/-! ### Dominated convergence on `(δ,∞)` -/

/-- **Far-field convergence.**  For every `δ > 0`, the Laplace transforms over `(δ,∞)` of the
profile converge to the Laplace transform of the limit profile. -/
theorem tendsto_integral_exp_mul_Phi_Ioi
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    (hantiPhi : ∀ k, Antitone fun u : ℝ => Phi α F f (hseq k) u)
    (hnnPhi : ∀ k u, 0 ≤ Phi α F f (hseq k) u)
    (hseq_mem : Tendsto hseq atTop (𝓝[>] (0:ℝ)))
    (hLb : ∀ q : {q : ℚ // 0 < q}, L q ≤ profileBound α (q:ℝ))
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Phi α F f (hseq k) (q:ℝ)) atTop (𝓝 (L q)))
    {σ : ℝ} (hσ : 0 < σ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => ∫ u in Ioi δ, Real.exp (-(σ*u)) * Phi α F f (hseq k) u) atTop
      (𝓝 (∫ u in Ioi δ, Real.exp (-(σ*u)) * limitProfile L u)) := by
  set μ := volume.restrict (Ioi δ) with hμ
  have hexpint : Integrable (fun u : ℝ => Real.exp (-(σ*u))) μ := by
    have h := integrableOn_exp_mul_Ioi (a := -σ) (by linarith) δ
    have h2 : (fun x : ℝ => Real.exp (-σ * x)) = fun x => Real.exp (-(σ*x)) := by
      ext x; rw [neg_mul]
    rw [h2] at h
    exact h
  have hbound_int : Integrable (fun u : ℝ => Real.exp (-(σ*u)) * profileBound α δ) μ :=
    hexpint.mul_const _
  have hbdd : ∀ᶠ k in atTop, ∀ᵐ u ∂μ, ‖Real.exp (-(σ*u)) * Phi α F f (hseq k) u‖
      ≤ Real.exp (-(σ*u)) * profileBound α δ := by
    have hev := hseq_mem.eventually
      (eventually_Phi_le_profileBound_of_le hFmeas hF0 hanti hfmeas hrv hmain hα1 hδ)
    filter_upwards [hev] with k hk
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have h1 : 0 ≤ Phi α F f (hseq k) u := hnnPhi k u
    have h2 : Phi α F f (hseq k) u ≤ profileBound α δ := hk u (le_of_lt hu)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h1)]
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun k => Real.exp (-(σ*u)) * Phi α F f (hseq k) u) atTop
      (𝓝 (Real.exp (-(σ*u)) * limitProfile L u)) := by
    have hae := ae_tendsto_limitProfile_ge hα0 hα1 hantiPhi hLb hconv hδ
    filter_upwards [hae] with u hu
    exact hu.const_mul (Real.exp (-(σ*u)))
  have hmeas : ∀ᶠ k in atTop,
      AEStronglyMeasurable (fun u : ℝ => Real.exp (-(σ*u)) * Phi α F f (hseq k) u) μ := by
    filter_upwards with k
    have hm : Measurable fun u : ℝ => Real.exp (-(σ*u)) * Phi α F f (hseq k) u := by
      refine Measurable.mul ?_ ?_
      · exact Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)
      · show Measurable fun u : ℝ =>
          Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k)
        exact (measurable_const.mul
          (hFmeas.comp (measurable_id.div_const (hseq k)))).div_const _
    exact hm.aestronglyMeasurable
  exact tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop) (ι := ℕ)
    (F := fun k => fun u : ℝ => Real.exp (-(σ*u)) * Phi α F f (hseq k) u)
    (f := fun u => Real.exp (-(σ*u)) * limitProfile L u)
    (bound := fun u => Real.exp (-(σ*u)) * profileBound α δ)
    hmeas hbdd hbound_int hlim

/-! ### The Laplace identity for the limit profile -/

/-- **The Laplace transform of the limit profile.**  For every `σ > 0`,
`∫₀^∞ e^{-σu} ψ(u) du = Γ(1-α) σ^{α-1}`, where `ψ = limitProfile L` is the antitone limit
profile attached to the subsequential rational limits `L`. -/
theorem integral_exp_mul_limitProfile
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hfpos : ∀ k, 0 < f (1/hseq k))
    (hLb : ∀ q : {q : ℚ // 0 < q}, L q ≤ profileBound α (q:ℝ))
    (hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q)
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Phi α F f (hseq k) (q:ℝ)) atTop (𝓝 (L q)))
    {σ : ℝ} (hσ : 0 < σ) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * limitProfile L u
      = Real.Gamma (1 - α) * σ^(α-1) := by
  classical
  have hantiPhi : ∀ k, Antitone fun u : ℝ => Phi α F f (hseq k) u :=
    fun k => Phi_antitone hα1 hanti (hpos k) (hfpos k)
  have hnnPhi : ∀ k u, 0 ≤ Phi α F f (hseq k) u :=
    fun k => Phi_nonneg hα1 hF0 (hfpos k)
  have hseq_mem : Tendsto hseq atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htend, Filter.Eventually.of_forall hpos⟩
  have hΓpos : (0:ℝ) < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hfull := tendsto_integral_exp_mul_Phi hFmeas hF0 hanti hfmeas hrv hmain hσ
  have hfull_seq := hfull.comp hseq_mem
  -- integrability of the full integral, for each `k`
  have hint_full : ∀ k, IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * Phi α F f (hseq k) u)
      (Ioi (0:ℝ)) := by
    intro k
    set B : ℝ := Real.Gamma (1 - α) * F 0 / f (1/hseq k) with hB
    have hBnn : 0 ≤ B := div_nonneg (mul_nonneg hΓpos.le (hF0 0)) (hfpos k).le
    have hmaj : Integrable (fun u : ℝ => Real.exp (-(σ*u)) * B)
        (volume.restrict (Ioi (0:ℝ))) := by
      have h := integrableOn_exp_mul_Ioi (a := -σ) (by linarith) (0:ℝ)
      have h2 : (fun x : ℝ => Real.exp (-σ * x)) = fun x => Real.exp (-(σ*x)) := by
        ext x; rw [neg_mul]
      rw [h2] at h
      exact h.mul_const B
    refine Integrable.mono' hmaj ?_ ?_
    · have hm : Measurable fun u : ℝ => Real.exp (-(σ*u)) * Phi α F f (hseq k) u := by
        refine Measurable.mul ?_ ?_
        · exact Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)
        · show Measurable fun u : ℝ => Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k)
          exact (measurable_const.mul
            (hFmeas.comp (measurable_id.div_const (hseq k)))).div_const _
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h1 : Phi α F f (hseq k) u ≤ B := by
        have hFu : F (u/hseq k) ≤ F 0 := hanti (div_nonneg (le_of_lt hu) (hpos k).le)
        simp only [Phi, hB]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hFu hΓpos.le) (hfpos k).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hnnPhi k u))]
      exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  -- the two-sided bound for every radius `δ`
  have key : ∀ δ : ℝ, 0 < δ →
      (∫ u in Ioi δ, Real.exp (-(σ*u)) * limitProfile L u) ≤ Real.Gamma (1 - α) * σ^(α-1) ∧
      Real.Gamma (1 - α) * σ^(α-1) - Real.Gamma (1 - α) * (2 * Real.exp 1 * δ^(1-α))
        ≤ ∫ u in Ioi δ, Real.exp (-(σ*u)) * limitProfile L u := by
    intro δ hδ
    -- the near-mass bound
    have hnear : ∀ᶠ k in atTop, ∫ u in Ioc (0:ℝ) δ, Real.exp (-(σ*u)) * Phi α F f (hseq k) u
        ≤ Real.Gamma (1 - α) * (2 * Real.exp 1 * δ^(1-α)) := by
      have hev := hseq_mem.eventually
        (near_mass_Phi_eventually_le hFmeas hF0 hanti hfmeas hrv hmain hα1 hδ)
      filter_upwards [hev] with k hk
      rw [integral_Ioc_eq_integral_Ioo]
      refine le_trans ?_ hk
      have hInt1 : IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * Phi α F f (hseq k) u)
          (Ioo (0:ℝ) δ) := (hint_full k).mono_set (fun u hu => hu.1)
      have hInt2 : IntegrableOn (fun u : ℝ => Phi α F f (hseq k) u) (Ioo (0:ℝ) δ) := by
        set B : ℝ := Real.Gamma (1 - α) * F 0 / f (1/hseq k) with hB
        have hBnn : 0 ≤ B := div_nonneg (mul_nonneg hΓpos.le (hF0 0)) (hfpos k).le
        have hc : IntegrableOn (fun _ : ℝ => B) (Ioo (0:ℝ) δ) :=
          integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        refine hc.mono' ?_ ?_
        · have hm : Measurable fun u : ℝ => Phi α F f (hseq k) u := by
            show Measurable fun u : ℝ => Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k)
            exact (measurable_const.mul
              (hFmeas.comp (measurable_id.div_const (hseq k)))).div_const _
          exact hm.aestronglyMeasurable
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          have h1 : Phi α F f (hseq k) u ≤ B := by
            have hFu : F (u/hseq k) ≤ F 0 := hanti (div_nonneg hu.1.le (hpos k).le)
            simp only [Phi, hB]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hFu hΓpos.le) (hfpos k).le
          rw [Real.norm_eq_abs, abs_of_nonneg (hnnPhi k u)]
          exact h1
      refine setIntegral_mono_on hInt1 hInt2 measurableSet_Ioo (fun u hu => ?_)
      have hexp : Real.exp (-(σ*u)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith [hu.1, hσ])
      exact mul_le_of_le_one_left (hnnPhi k u) hexp
    -- the decomposition of the full integral at `δ`
    have hsplit : ∀ k, ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * Phi α F f (hseq k) u
        = (∫ u in Ioi δ, Real.exp (-(σ*u)) * Phi α F f (hseq k) u)
          + ∫ u in Ioc (0:ℝ) δ, Real.exp (-(σ*u)) * Phi α F f (hseq k) u := by
      intro k
      have hunion : Ioi δ ∪ Ioc (0:ℝ) δ = Ioi (0:ℝ) := by
        ext x
        simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Ioc]
        constructor
        · rintro (h | ⟨h1, h2⟩) <;> linarith
        · intro h
          by_cases hx : x ≤ δ
          · exact Or.inr ⟨h, hx⟩
          · exact Or.inl (lt_of_not_ge hx)
      rw [← hunion]
      exact setIntegral_union (by
          rw [Set.disjoint_left]
          intro x hx1 hx2
          exact absurd hx1 (not_lt.mpr hx2.2)) measurableSet_Ioc
        ((hint_full k).mono_set (fun u hu => lt_trans hδ hu))
        ((hint_full k).mono_set (fun u hu => hu.1))
    -- the far integral converges
    have hfar := tendsto_integral_exp_mul_Phi_Ioi hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
      hantiPhi hnnPhi hseq_mem hLb hconv hσ hδ
    constructor
    · have hle : ∀ᶠ k in atTop, (∫ u in Ioi δ, Real.exp (-(σ*u)) * Phi α F f (hseq k) u)
          ≤ ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * Phi α F f (hseq k) u := by
        filter_upwards with k
        rw [hsplit k]
        have h1 : 0 ≤ ∫ u in Ioc (0:ℝ) δ, Real.exp (-(σ*u)) * Phi α F f (hseq k) u :=
          setIntegral_nonneg measurableSet_Ioc (fun u _ =>
            mul_nonneg (Real.exp_pos _).le (hnnPhi k u))
        linarith
      exact le_of_tendsto_of_tendsto hfar hfull_seq hle
    · have hdiff : Tendsto (fun k => (∫ u in Ioi (0:ℝ),
            Real.exp (-(σ*u)) * Phi α F f (hseq k) u)
          - ∫ u in Ioi δ, Real.exp (-(σ*u)) * Phi α F f (hseq k) u) atTop
          (𝓝 (Real.Gamma (1 - α) * σ^(α-1)
            - ∫ u in Ioi δ, Real.exp (-(σ*u)) * limitProfile L u)) :=
        hfull_seq.sub hfar
      have hle : ∀ᶠ k in atTop, (∫ u in Ioi (0:ℝ),
            Real.exp (-(σ*u)) * Phi α F f (hseq k) u)
          - ∫ u in Ioi δ, Real.exp (-(σ*u)) * Phi α F f (hseq k) u
          ≤ Real.Gamma (1 - α) * (2 * Real.exp 1 * δ^(1-α)) := by
        filter_upwards [hnear] with k hk
        rw [hsplit k]
        linarith
      have := le_of_tendsto hdiff hle
      linarith
  -- measurability and integrability of the limit profile against the exponential weight
  have hψmeas : AEStronglyMeasurable (limitProfile L) (volume.restrict (Ioi (0:ℝ))) := by
    have hae := ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv
    refine aestronglyMeasurable_of_tendsto_ae atTop ?_ hae
    intro k
    have hm : Measurable fun u : ℝ => Phi α F f (hseq k) u := by
      show Measurable fun u : ℝ => Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k)
      exact (measurable_const.mul
        (hFmeas.comp (measurable_id.div_const (hseq k)))).div_const _
    exact hm.aestronglyMeasurable
  have hψexpmeas : AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-(σ*u)) * limitProfile L u) (volume.restrict (Ioi (0:ℝ))) :=
    ((Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable).mul
      hψmeas
  have hψint : IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * limitProfile L u)
      (Ioi (0:ℝ)) := by
    refine (integrableOn_exp_mul_profileBound hα1 hσ).mono' hψexpmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have h1 : 0 ≤ Real.exp (-(σ*u)) * limitProfile L u :=
      mul_nonneg (Real.exp_pos _).le (limitProfile_nonneg hα0 hα1 hLb hLnn hu)
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact mul_le_mul_of_nonneg_left (limitProfile_le_bound hα0 hα1 hLb hu) (Real.exp_pos _).le
  have hψnn : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))),
      0 ≤ Real.exp (-(σ*u)) * limitProfile L u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.exp_pos _).le (limitProfile_nonneg hα0 hα1 hLb hLnn hu)
  -- pass to `δ ↓ 0`
  have hlimδ := tendsto_setIntegral_Ioi_zero hψexpmeas hψnn hψint
  have hleft : (∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * limitProfile L u)
      ≤ Real.Gamma (1 - α) * σ^(α-1) := by
    refine le_of_tendsto hlimδ ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ'
    exact (key δ hδ').1
  have hright : Real.Gamma (1 - α) * σ^(α-1)
      ≤ ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * limitProfile L u := by
    have hpow : Tendsto (fun δ : ℝ => δ ^ (1 - α)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hr : Tendsto (fun δ : ℝ => δ ^ (-(1 - α))) (𝓝[>] (0:ℝ)) atTop :=
        tendsto_rpow_neg_nhdsGT_zero (by linarith)
      have hr2 : Tendsto (fun δ : ℝ => (δ ^ (-(1 - α)))⁻¹) (𝓝[>] (0:ℝ)) (𝓝 0) :=
        hr.inv_tendsto_atTop
      refine hr2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ'
      rw [Real.rpow_neg hδ'.le, inv_inv]
    have hT : Tendsto (fun δ : ℝ => Real.Gamma (1 - α) * σ^(α-1)
        - Real.Gamma (1 - α) * (2 * Real.exp 1 * δ^(1-α))) (𝓝[>] (0:ℝ))
        (𝓝 (Real.Gamma (1 - α) * σ^(α-1))) := by
      have h2 : Tendsto (fun δ : ℝ => Real.Gamma (1 - α) * (2 * Real.exp 1 * δ^(1-α)))
          (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have h3 := hpow.const_mul (2 * Real.exp 1)
        rw [mul_zero] at h3
        have h4 := h3.const_mul (Real.Gamma (1 - α))
        rw [mul_zero] at h4
        refine h4.congr' ?_
        filter_upwards with δ
        ring
      simpa using (tendsto_const_nhds.sub h2 :
        Tendsto (fun δ : ℝ => Real.Gamma (1 - α) * σ^(α-1)
          - Real.Gamma (1 - α) * (2 * Real.exp 1 * δ^(1-α))) (𝓝[>] (0:ℝ))
          (𝓝 (Real.Gamma (1 - α) * σ^(α-1) - 0)))
    refine le_of_tendsto_of_tendsto hT hlimδ ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ'
    exact (key δ hδ').2
  linarith

/-! ### Weighted Laplace uniqueness -/

/-- **Weighted Laplace uniqueness.**  If `∫₀^∞ e^{-σu}|D u| du < ∞` for every `σ > 0` (stated as
integrability of the weighted difference) and every Laplace transform of `D` vanishes, then
`D = 0` a.e.  This is `Analysis/LaplaceUnique.lean`'s unweighted injectivity applied to
`u ↦ e^{-u} D u`; the hypothesis is what the limit profile actually satisfies, since it only
decays like `u^{-α}` and is therefore not `L¹(0,∞)`. -/
theorem eq_zero_ae_of_forall_laplace_weighted {D : ℝ → ℝ}
    (_hDmeas : AEStronglyMeasurable D (volume.restrict (Ioi (0:ℝ))))
    (hint : ∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * D u) (Ioi (0:ℝ)))
    (hlaplace : ∀ σ : ℝ, 0 < σ →
      ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * D u = 0) :
    D =ᵐ[volume.restrict (Ioi (0:ℝ))] 0 := by
  have hGint : IntegrableOn (fun u : ℝ => Real.exp (-u) * D u) (Ioi (0:ℝ)) := by
    have h := hint 1 one_pos
    refine h.congr ?_
    filter_upwards with u
    rw [one_mul]
  have hGlap : ∀ σ : ℝ, 0 < σ →
      ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * (Real.exp (-u) * D u) = 0 := by
    intro σ hσ
    have h := hlaplace (σ + 1) (by linarith)
    have hcongr : (fun u : ℝ => Real.exp (-(σ*u)) * (Real.exp (-u) * D u))
        = fun u : ℝ => Real.exp (-((σ+1)*u)) * D u := by
      funext u
      rw [← mul_assoc, ← Real.exp_add, show -(σ*u) + -u = -((σ+1)*u) from by ring]
    rw [hcongr, h]
  have hzero := eq_zero_ae_of_forall_laplace_eq_zero
    (D := fun u : ℝ => Real.exp (-u) * D u) hGint hGlap
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioi] with u h1 h2
  have hpos : Real.exp (-u) ≠ 0 := (Real.exp_pos _).ne'
  rw [Pi.zero_apply] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h hpos
  · exact h

/-! ### Identifying the limit profile with `u^{-α}` -/

/-- **Laplace uniqueness identifies the limit profile.**  A nonnegative function bounded by
`profileBound α` whose Laplace transforms are `Γ(1-α)σ^{α-1}` at every rate coincides a.e. with
`u ↦ u^{-α}`. -/
theorem ae_eq_rpow_of_laplace
    {ψ : ℝ → ℝ} {α : ℝ} (_hα0 : 0 ≤ α) (hα1 : α < 1)
    (hψmeas : AEStronglyMeasurable ψ (volume.restrict (Ioi (0:ℝ))))
    (hψnn : ∀ u, 0 < u → 0 ≤ ψ u)
    (hψle : ∀ u, 0 < u → ψ u ≤ profileBound α u)
    (hlaplace : ∀ σ : ℝ, 0 < σ →
      ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * ψ u = Real.Gamma (1 - α) * σ^(α-1)) :
    ψ =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u => u ^ (-α) := by
  set D : ℝ → ℝ := fun u => ψ u - u ^ (-α) with hD
  have hDmeas : AEStronglyMeasurable D (volume.restrict (Ioi (0:ℝ))) :=
    hψmeas.sub (by fun_prop : Measurable fun u : ℝ => u ^ (-α)).aestronglyMeasurable
  have hψint : ∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * ψ u) (Ioi (0:ℝ)) := by
    intro σ hσ
    have hmeas' : AEStronglyMeasurable (fun u : ℝ => Real.exp (-(σ*u)) * ψ u)
        (volume.restrict (Ioi (0:ℝ))) :=
      ((Real.measurable_exp.comp
        ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable).mul hψmeas
    refine (integrableOn_exp_mul_profileBound (α := α) hα1 hσ).mono' hmeas' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hψnn u hu))]
    exact mul_le_mul_of_nonneg_left (hψle u hu) (Real.exp_pos _).le
  have hDint : ∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * D u) (Ioi (0:ℝ)) := by
    intro σ hσ
    have h3 := (hψint σ hσ).sub (integrableOn_exp_mul_rpow_neg (α := α) hα1 hσ)
    refine h3.congr ?_
    filter_upwards with u
    simp only [hD, Pi.sub_apply]
    ring
  have hDlap : ∀ σ : ℝ, 0 < σ →
      ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * D u = 0 := by
    intro σ hσ
    have h1 := hψint σ hσ
    have h2 := integrableOn_exp_mul_rpow_neg (α := α) hα1 hσ
    have heq : (fun u : ℝ => Real.exp (-(σ*u)) * D u)
        = fun u : ℝ => Real.exp (-(σ*u)) * ψ u - Real.exp (-(σ*u)) * u ^ (-α) := by
      ext u
      simp only [hD]
      ring
    rw [heq, integral_sub h1 h2, hlaplace σ hσ, integral_exp_mul_rpow_neg_eq hα1 hσ]
    ring
  have hzero := eq_zero_ae_of_forall_laplace_weighted hDmeas hDint hDlap
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioi] with u h1 h2
  have h2' : D u = 0 := h1
  simp only [hD] at h2'
  linarith

/-! ### The squeeze at `u = 1` -/

/-- **Squeezing a monotone family at `1`.**  If `Φ k` is antitone and converges a.e. on `(0,∞)` to a
function equal a.e. to `u^{-α}`, then `Φ k 1 → 1`.  The proof traps `Φ k 1` between `Φ k a` and
`Φ k b` for good points `a < 1 < b` arbitrarily close to `1`. -/
theorem tendsto_one_of_antitone_squeeze {Φ : ℕ → ℝ → ℝ} {ψ : ℝ → ℝ} {α : ℝ}
    (hanti : ∀ k, Antitone (Φ k))
    (hae : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), Tendsto (fun k => Φ k u) atTop (𝓝 (ψ u)))
    (hident : ψ =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u => u ^ (-α)) :
    Tendsto (fun k => Φ k 1) atTop (𝓝 1) := by
  have hP : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))),
      Tendsto (fun k => Φ k u) atTop (𝓝 (ψ u)) ∧ ψ u = u ^ (-α) := hae.and hident
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨a, ha0, ha1, haP', hae_a⟩ := exists_good_below (α := α) hP (show 0 < ε/2 by linarith)
  obtain ⟨b, hb1, hb2, hbP', hbe_b⟩ := exists_good_above (α := α) hP (show 0 < ε/2 by linarith)
  have hlow : ∀ᶠ k in atTop, 1 - ε < Φ k 1 := by
    have h1 : Tendsto (fun k => Φ k b) atTop (𝓝 (b ^ (-α))) := by
      have := hbP'.1
      rw [hbP'.2] at this
      exact this
    have h2 : ∀ᶠ k in atTop, 1 - ε/2 < Φ k b :=
      h1.eventually (eventually_gt_nhds hbe_b)
    filter_upwards [h2] with k hk
    have h3 : Φ k b ≤ Φ k 1 := hanti k (le_of_lt hb1)
    linarith
  have hhi : ∀ᶠ k in atTop, Φ k 1 < 1 + ε := by
    have h1 : Tendsto (fun k => Φ k a) atTop (𝓝 (a ^ (-α))) := by
      have := haP'.1
      rw [haP'.2] at this
      exact this
    have h2 : ∀ᶠ k in atTop, Φ k a < 1 + ε/2 :=
      h1.eventually (eventually_lt_nhds hae_a)
    filter_upwards [h2] with k hk
    have h3 : Φ k 1 ≤ Φ k a := hanti k (le_of_lt ha1)
    linarith
  refine eventually_atTop.1 ?_
  filter_upwards [hlow, hhi] with k h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### Subsequential compactness gives the limit -/

/-- **Every sequence has a subsequence along which the profile converges at `1`.** -/
theorem exists_subseq_tendsto_Phi_one
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    {hseq : ℕ → ℝ} (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hfpos : ∀ n, 0 < f (1/hseq n)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto (fun k => Phi α F f (hseq (ns k)) 1) atTop (𝓝 1) := by
  classical
  obtain ⟨L, ns, hns, hL, hconv⟩ :=
    exists_rational_limit hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain hpos htend
  have hpos' : ∀ k, 0 < hseq (ns k) := fun k => hpos (ns k)
  have htend' : Tendsto (fun k => hseq (ns k)) atTop (𝓝 0) := htend.comp hns.tendsto_atTop
  have hfpos' : ∀ k, 0 < f (1/(hseq (ns k))) := fun k => hfpos (ns k)
  have hLb : ∀ q : {q : ℚ // 0 < q}, L q ≤ profileBound α (q:ℝ) := fun q => (hL q).2
  have hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q := fun q => (hL q).1
  have hantiPhi : ∀ k, Antitone fun u : ℝ => Phi α F f (hseq (ns k)) u :=
    fun k => Phi_antitone hα1 hanti (hpos' k) (hfpos' k)
  -- the Laplace identity along the subsequence
  have hlaplace : ∀ σ : ℝ, 0 < σ →
      ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * limitProfile L u
        = Real.Gamma (1 - α) * σ^(α-1) := fun σ hσ =>
    integral_exp_mul_limitProfile hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
      hpos' htend' hfpos' hLb hLnn hconv hσ
  -- measurability of the limit profile
  have hψmeas : AEStronglyMeasurable (limitProfile L) (volume.restrict (Ioi (0:ℝ))) := by
    have hae := ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv
    refine aestronglyMeasurable_of_tendsto_ae atTop ?_ hae
    intro k
    have hm : Measurable fun u : ℝ => Phi α F f (hseq (ns k)) u := by
      show Measurable fun u : ℝ => Real.Gamma (1 - α) * F (u / hseq (ns k)) / f (1 / hseq (ns k))
      exact (measurable_const.mul
        (hFmeas.comp (measurable_id.div_const (hseq (ns k))))).div_const _
    exact hm.aestronglyMeasurable
  have hident : limitProfile L =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u => u ^ (-α) :=
    ae_eq_rpow_of_laplace hα0 hα1 hψmeas
      (fun u hu => limitProfile_nonneg hα0 hα1 hLb hLnn hu)
      (fun u hu => limitProfile_le_bound hα0 hα1 hLb hu) hlaplace
  have hae := ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv
  exact ⟨ns, hns, tendsto_one_of_antitone_squeeze hantiPhi hae hident⟩

/-- **The strict Tauberian converse, main normalised form.**  Under the Laplace hypothesis,
`Γ(1-α) F(1/h)/f(1/h) → 1` as `h ↓ 0`. -/
theorem tendsto_Phi_one
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1)) :
    Tendsto (fun h : ℝ => Phi α F f h 1) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ h in 𝓝[>] (0:ℝ), ¬ (dist (Phi α F f h 1) 1 < ε) := by
    by_contra h2
    exact hcon ((not_frequently.mp h2).mono (fun x hx => not_not.mp hx))
  obtain ⟨y, hy, hybad⟩ := exists_seq_forall_of_frequently hfreq
  -- positivity of the sequence and of the normalising factor, eventually
  have h1 : Tendsto (fun h : ℝ => 1/h) (𝓝[>] (0:ℝ)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  have hev1 : ∀ᶠ k : ℕ in atTop, 0 < y k := hy.eventually self_mem_nhdsWithin
  have hinv_atTop : Tendsto (fun x : ℝ => 1/x) atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa [one_div] using tendsto_inv_atTop_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Set.mem_Ioi, one_div]
    positivity
  have hfpos_atTop : ∀ᶠ x : ℝ in atTop, 0 < f x :=
    (hinv_atTop.eventually (eventually_pos_f_inv hF0 hmain)).mono (fun x hx => by
      simpa [one_div] using hx)
  have hev2 : ∀ᶠ k : ℕ in atTop, 0 < f (1/(y k)) := (h1.comp hy).eventually hfpos_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hev1.and hev2)
  set z : ℕ → ℝ := fun k => y (k + K) with hz
  have hzmem : Tendsto z atTop (𝓝[>] (0:ℝ)) := hy.comp (tendsto_add_atTop_nat K)
  have hztend : Tendsto z atTop (𝓝 0) := hzmem.mono_right nhdsWithin_le_nhds
  have hzpos : ∀ k, 0 < z k := fun k => (hK (k + K) (le_add_self)).1
  have hzfpos : ∀ k, 0 < f (1/(z k)) := fun k => (hK (k + K) (le_add_self)).2
  obtain ⟨ns, hns, hns_tend⟩ :=
    exists_subseq_tendsto_Phi_one hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain hzpos hztend hzfpos
  have hbad : ∀ k, ε ≤ dist (Phi α F f (z (ns k)) 1) 1 :=
    fun k => not_lt.mp (hybad (ns k + K))
  have hgood : ∀ᶠ k in atTop, dist (Phi α F f (z (ns k)) 1) 1 < ε := by
    have hb : Metric.ball (1:ℝ) ε ∈ 𝓝 (1:ℝ) := Metric.ball_mem_nhds 1 hε
    filter_upwards [hns_tend.eventually hb] with k hk
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hk
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgood
  have hbadN : ε ≤ dist (Phi α F f (z (ns N)) 1) 1 := hbad N
  exact absurd hbadN (not_le.mpr (hN N le_rfl))

/-! ### The tail asymptotic -/

/-- **The strict Tail form of the converse.**  Under the Laplace hypothesis,
`F(x)/(f(x)/Γ(1-α)) → 1` as `x → ∞`. -/
theorem tendsto_tail_of_laplace
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1)) :
    Tendsto (fun x : ℝ => F x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) := by
  have hΓpos : (0:ℝ) < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hΓne : Real.Gamma (1 - α) ≠ 0 := ne_of_gt hΓpos
  have h1 := tendsto_Phi_one hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
  have hinv : Tendsto (fun x : ℝ => 1/x) atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa [one_div] using tendsto_inv_atTop_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Set.mem_Ioi, one_div]
    positivity
  have h2 : Tendsto (fun x : ℝ => Phi α F f (1/x) 1) atTop (𝓝 1) := h1.comp hinv
  have h3 : Tendsto (fun x : ℝ => Real.Gamma (1 - α) * F x / f x) atTop (𝓝 1) := by
    refine h2.congr' ?_
    filter_upwards with x
    simp only [Phi, one_div, inv_inv]
  have h4 : Tendsto (fun x : ℝ => F x / f x) atTop (𝓝 ((Real.Gamma (1 - α))⁻¹)) := by
    have h := h3.const_mul ((Real.Gamma (1 - α))⁻¹)
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards with x
    field_simp
  have h5 : Tendsto (fun x : ℝ => Real.Gamma (1 - α) * (F x / f x)) atTop (𝓝 1) := by
    have h := h4.const_mul (Real.Gamma (1 - α))
    rw [mul_inv_cancel₀ hΓne] at h
    exact h
  refine h5.congr' ?_
  filter_upwards with x
  by_cases hf : f x = 0
  · simp [hf]
  · field_simp

/-! ### Theorem I.2.11 in the paper's form -/

/-- **Theorem I.2.11** (Feller XIII.5.2; Hutchcroft, arXiv:2508.18807v1, p. 26).

For a probability measure `μ` on `ℝ` carried by `[0,∞)` and `f` regularly varying of index `-α`
with `0 ≤ α < 1`,

`E_μ[1 - e^{-hX}] ~ f(1/h)` as `h ↓ 0` **iff** `μ([x,∞)) ~ f(x)/Γ(1-α)` as `x → ∞`.

The forward direction is `laplace_tail_asymptotic_of_tail_ge`
(`Analysis/TauberianEndpoints.lean`); the converse is `tendsto_tail_of_laplace` above, applied
through the assembly `tail_ge_asymptotic_of_antitone_kernel_converse`. -/
theorem laplace_asymptotic_iff_tail_ge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) {f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hfmeas : Measurable f)
    (hrv : RegularlyVaryingAtTop f (-α)) :
    (Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
      Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)))
        atTop (𝓝 1)) := by
  constructor
  · intro hL
    exact tail_ge_asymptotic_of_antitone_kernel_converse μ hμ hα0 hα1 hrv
      (fun F hFm hanti hF0 _ hk => tendsto_tail_of_laplace hα0 hα1 hFm hF0 hanti hfmeas hrv hk) hL
  · intro htail
    exact laplace_tail_asymptotic_of_tail_ge μ hμ hα0 hα1 hfmeas hrv htail

/-- **Theorem I.2.11 for the exact power law** `f x = x^{-α}`.  This discharges the regular
variation hypothesis with the concrete function `x ↦ x^{-α}`, so the statement has no abstract
regular-variation input left. -/
theorem laplace_asymptotic_iff_tail_ge_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / ((1 / h) ^ (-α)))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
      Tendsto (fun x => (μ (Set.Ici x)).toReal / (x ^ (-α) / Real.Gamma (1 - α)))
        atTop (𝓝 1)) :=
  laplace_asymptotic_iff_tail_ge μ hμ hα0 hα1 (by fun_prop)
    (regularlyVaryingAtTop_rpow (-α))

/-! ### The completed converse: exact required conclusions

The two statements required of this direction are
`limitProfile L =ᵐ u^{-α}` on `(0,∞)` and `Phi α F f (hseq (ns n)) 1 → 1`, where `L, ns` are
the rational limit values and renumbering produced by `exists_rational_limit`.  Both are proved
here for the *exact* hypotheses of the problem statement; the full-strength limit
`Phi α F f h 1 → 1` as `h ↓ 0` is `tendsto_Phi_one` below. -/

/-- **The limit profile is the power law.**  For any sequence `hseq ↓ 0` and any family `L` of
rational limit values of the normalised profile (i.e. any output of `exists_rational_limit`), the
antitone limit profile coincides almost everywhere on `(0,∞)` with `u ↦ u^{-α}`. -/
theorem limitProfile_eq_rpow_ae
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hfpos : ∀ k, 0 < f (1/hseq k))
    (hLb : ∀ q : {q : ℚ // 0 < q}, L q ≤ profileBound α (q:ℝ))
    (hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q)
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Phi α F f (hseq k) (q:ℝ)) atTop (𝓝 (L q))) :
    limitProfile L =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u : ℝ => u ^ (-α) := by
  have hantiPhi : ∀ k, Antitone fun u : ℝ => Phi α F f (hseq k) u :=
    fun k => Phi_antitone hα1 hanti (hpos k) (hfpos k)
  -- the Laplace transform of the limit profile at every rate
  have hlaplace : ∀ σ : ℝ, 0 < σ →
      ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * limitProfile L u
        = Real.Gamma (1 - α) * σ^(α-1) := fun σ hσ =>
    integral_exp_mul_limitProfile hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
      hpos htend hfpos hLb hLnn hconv hσ
  -- the limit profile is measurable: it is the a.e. limit of measurable profiles
  have hψmeas : AEStronglyMeasurable (limitProfile L) (volume.restrict (Ioi (0:ℝ))) := by
    have hae := ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv
    refine aestronglyMeasurable_of_tendsto_ae atTop ?_ hae
    intro k
    have hm : Measurable fun u : ℝ => Phi α F f (hseq k) u := by
      show Measurable fun u : ℝ =>
        Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k)
      exact (measurable_const.mul
        (hFmeas.comp (measurable_id.div_const (hseq k)))).div_const _
    exact hm.aestronglyMeasurable
  exact ae_eq_rpow_of_laplace hα0 hα1 hψmeas
    (fun u hu => limitProfile_nonneg hα0 hα1 hLb hLnn hu)
    (fun u hu => limitProfile_le_bound hα0 hα1 hLb hu) hlaplace

/-- **The squeeze at `u = 1` along a sequence of rational limit values.**  For any `hseq ↓ 0` and
any family `L` of rational limit values of the normalised profile, `Phi α F f (hseq k) 1 → 1`. -/
theorem tendsto_Phi_one_of_rational_limit
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hfpos : ∀ k, 0 < f (1/hseq k))
    (hLb : ∀ q : {q : ℚ // 0 < q}, L q ≤ profileBound α (q:ℝ))
    (hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q)
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Phi α F f (hseq k) (q:ℝ)) atTop (𝓝 (L q))) :
    Tendsto (fun k => Phi α F f (hseq k) 1) atTop (𝓝 1) := by
  have hantiPhi : ∀ k, Antitone fun u : ℝ => Phi α F f (hseq k) u :=
    fun k => Phi_antitone hα1 hanti (hpos k) (hfpos k)
  have hident : limitProfile L =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u : ℝ => u ^ (-α) :=
    limitProfile_eq_rpow_ae hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
      hpos htend hfpos hLb hLnn hconv
  exact tendsto_one_of_antitone_squeeze hantiPhi
    (ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv) hident

/-- **The Tauberian converse with both required conclusions, for every input sequence.**

Given the paper's exact hypotheses (`0 ≤ α < 1`, `F` measurable, nonnegative and antitone, `f`
measurable regularly varying of index `-α`, the kernel-form Laplace hypothesis, and any positive
`hseq → 0`), there are subsequential rational limits `L` (bounded by `profileBound`) and a
renumbering `ns` such that

* the limit profile is `u ↦ u^{-α}` almost everywhere on `(0,∞)`, and
* `Γ(1-α) F(1/hseq (ns n))/f(1/hseq (ns n)) → 1`.

No positivity of `f` and no positivity of `F` at any specific point is assumed: the eventual
positivity of the normalising factor `f (1/h)` is *derived*, and the sequence is shifted to the
tail where it holds, the shift being absorbed into `ns`. -/
theorem exists_limitProfile_eq_rpow_ae_and_tendsto_one
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    {hseq : ℕ → ℝ} (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0)) :
    ∃ (L : {q : ℚ // 0 < q} → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ q : {q : ℚ // 0 < q}, 0 ≤ L q ∧ L q ≤ profileBound α (q:ℝ)) ∧
      (∀ q : {q : ℚ // 0 < q},
        Tendsto (fun k => Phi α F f (hseq (ns k)) (q:ℝ)) atTop (𝓝 (L q))) ∧
      (limitProfile L =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u : ℝ => u ^ (-α)) ∧
      Tendsto (fun n => Phi α F f (hseq (ns n)) 1) atTop (𝓝 1) := by
  classical
  -- the sequence lies eventually in the positive half-line
  have hseq_mem : Tendsto hseq atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htend, Filter.Eventually.of_forall hpos⟩
  -- `f x > 0` eventually on the scale `x = 1/h`
  have hinv_atTop : Tendsto (fun x : ℝ => 1/x) atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa [one_div] using tendsto_inv_atTop_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Set.mem_Ioi, one_div]
    positivity
  have hfpos_atTop : ∀ᶠ x : ℝ in atTop, 0 < f x :=
    (hinv_atTop.eventually (eventually_pos_f_inv hF0 hmain)).mono (fun x hx => by
      simpa [one_div] using hx)
  have hinvseq : Tendsto (fun n : ℕ => 1/(hseq n)) atTop atTop :=
    (by simpa [one_div] using tendsto_inv_nhdsGT_zero :
      Tendsto (fun h : ℝ => 1/h) (𝓝[>] (0:ℝ)) atTop).comp hseq_mem
  -- shift the sequence to where the normalising factor is positive
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hinvseq.eventually hfpos_atTop)
  set hseq' : ℕ → ℝ := fun n => hseq (n + K) with hseq'_def
  have hpos' : ∀ n, 0 < hseq' n := fun n => hpos (n + K)
  have htend' : Tendsto hseq' atTop (𝓝 0) := htend.comp (tendsto_add_atTop_nat K)
  have hfpos' : ∀ k, 0 < f (1/hseq' k) := fun k => hK (k + K) le_add_self
  -- compactness along the shifted sequence
  obtain ⟨L, ns, hns, hL, hconv⟩ :=
    exists_rational_limit hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain hpos' htend'
  have hLb : ∀ q : {q : ℚ // 0 < q}, L q ≤ profileBound α (q:ℝ) := fun q => (hL q).2
  have hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q := fun q => (hL q).1
  -- the sequence `k ↦ hseq' (ns k)`, along which the rational limits are attained
  have hpos'' : ∀ n, 0 < hseq' (ns n) := fun n => hpos' (ns n)
  have htend'' : Tendsto (fun n => hseq' (ns n)) atTop (𝓝 0) :=
    htend'.comp hns.tendsto_atTop
  have hfpos'' : ∀ k, 0 < f (1/(hseq' (ns k))) := fun k => hfpos' (ns k)
  have hident : limitProfile L =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u : ℝ => u ^ (-α) :=
    limitProfile_eq_rpow_ae hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
      hpos'' htend'' hfpos'' hLb hLnn hconv
  have hsub : Tendsto (fun k => Phi α F f (hseq' (ns k)) 1) atTop (𝓝 1) :=
    tendsto_Phi_one_of_rational_limit hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain
      hpos'' htend'' hfpos'' hLb hLnn hconv
  -- renumber: absorb the shift `K` into the subsequence indices
  exact ⟨L, fun n => ns n + K, fun a b hab => Nat.add_lt_add_right (hns hab) K,
    hL, hconv, hident, hsub⟩

/-- **The subsequential conclusion in the exact form required**, for *any* strictly monotone
renumbering `ns` (in particular the one produced by `exists_rational_limit`).  This is a direct
consequence of the full-strength limit `tendsto_Phi_one` and needs no rational-limit data. -/
theorem tendsto_Phi_subseq_one
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1))
    {hseq : ℕ → ℝ} (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    {ns : ℕ → ℕ} (hns : StrictMono ns) :
    Tendsto (fun n => Phi α F f (hseq (ns n)) 1) atTop (𝓝 1) := by
  have hseq_mem : Tendsto hseq atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htend, Filter.Eventually.of_forall hpos⟩
  exact (tendsto_Phi_one hα0 hα1 hFmeas hF0 hanti hfmeas hrv hmain).comp
    (hseq_mem.comp hns.tendsto_atTop)


/-! ### Non-vacuity of the hypothesis set

A cheap but genuine consistency check: the constant profile `α = 0`, `F ≡ 1`, `f ≡ 1` satisfies
every hypothesis of `exists_limitProfile_eq_rpow_ae_and_tendsto_one`, so that theorem is not
vacuous.  Here `Φ 0 F f h u = Γ 1 · 1 / 1 = 1`, and the required a.e. limit is `u ^ (-0) = 1`,
which is exactly the limit profile of the constant data. -/

/-- The converse's hypothesis set is satisfiable (`α = 0`, `F ≡ 1`, `f ≡ 1`,
`hseq n = 1/(n+1)`), and both conclusions hold for its output. -/
theorem nonvacuous_constant_profile :
    ∃ (L : {q : ℚ // 0 < q} → ℝ) (ns : ℕ → ℕ),
      (limitProfile L =ᵐ[volume.restrict (Ioi (0:ℝ))] fun u : ℝ => u ^ (-(0:ℝ))) ∧
      Tendsto (fun n => Phi 0 (fun _ : ℝ => 1) (fun _ : ℝ => 1) (1/((ns n : ℝ)+1)) 1)
        atTop (𝓝 1) := by
  -- `f ≡ 1` is regularly varying of index `-0 = 0`
  have hrv : RegularlyVaryingAtTop (fun _ : ℝ => (1:ℝ)) (-(0:ℝ)) := by
    constructor
    · filter_upwards with x
      simp
    · intro l hl
      have h0 : (-(0:ℝ)) = 0 := by norm_num
      rw [h0, Real.rpow_zero]
      simp
  -- the kernel hypothesis is `∫ e^{-u} du = 1`
  have hint : (∫ u in Ioi (0:ℝ), Real.exp (-u) * (1:ℝ)) = 1 := by
    simpa using integral_exp_neg_Ioi_zero
  have hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * (fun _ : ℝ => (1:ℝ)) (u/h))
        / (fun _ : ℝ => (1:ℝ)) (1/h)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with h
    show (1:ℝ) = (∫ u in Ioi (0:ℝ), Real.exp (-u) * (1:ℝ)) / 1
    rw [div_one, hint]
  obtain ⟨L, ns, -, -, -, hident, hlim⟩ :=
    exists_limitProfile_eq_rpow_ae_and_tendsto_one (F := fun _ : ℝ => 1) (f := fun _ : ℝ => 1)
      (α := 0) le_rfl zero_lt_one measurable_const (fun _ => zero_le_one) antitone_const
      measurable_const hrv hmain (hseq := fun n : ℕ => 1/((n:ℝ)+1))
      (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨L, ns, hident, hlim⟩


end PercLib.CriticalLRP.Analysis
