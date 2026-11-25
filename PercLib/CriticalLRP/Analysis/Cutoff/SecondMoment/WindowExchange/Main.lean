/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The off-corner `p = 2` derivative as a local-uniform pivotal-series exchange

Swarm `smwvdggcc`, member `m2`, direction (A).

Integration donor: `.ultramath/smwvdggcc/m2`; independently checked at `70d28dd23e81d39713b39719197c5a492f8bca8c`.

Target of the swarm:

`HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0`  at an off-sphere `r0 > 0`.

This file proves the reduction to the two genuinely analytic inputs, with the source model and the
accepted right-hand side `M.rhsScalarTwo` appearing literally:

* `integral_volSq_cutLaw` — the real Bochner integral of the unbounded functional
  `ω ↦ (|K_0(ω)|).toReal²` against `M.cutLaw r` **is** `M.cutMomentReal 2 r`, with no cap and no
  `⊤ ↦ 0` conversion (`ENNReal.toReal_pow` plus `MeasureTheory.integral_toReal`);
* `hasDerivAt_windowIntegral_cutLaw` — the finite-window Russo identity for that functional at the
  source model, with the *actual* edge weights `M.cutEdgeDeriv r e`, away from `M.cornerRadii`;
* `tendstoLocallyUniformlyOn_of_split` — the local-uniform window-flux convergence decomposes into
  (T1) local uniform convergence of the infinite pivotal series and (T2) local uniform vanishing of
  the insertion errors `Σ_{e∈S} |c_r(e)| |P_S(e) − P(e)|`;
* `hasDerivAt_integral_clusterVol_sq_cutLaw` — the reduction itself: (T1) and (T2) for the model
  give `HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0`.

## What is *not* claimed

Neither (T1) nor (T2) is proved here, and no substitute for them is assumed.  In particular this
file contains no finite-box proxy, no capped/truncated functional, no monotonicity argument standing
in for the fundamental theorem of calculus, and no treatment of `cutLaw r` as locally constant.
Section 4 states exactly what remains.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.WindowExchange.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FTC

/-!
# Local-uniform pivotal-series exchange at `p = 2`
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open PercLib.CriticalLRP.Orchestration
open scoped ENNReal NNReal Topology Uniformity

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.SecondMomentExchange

variable {V : Type*} [Countable V]

/-! ## 1. The real `p = 2` functional and the `ℝ≥0∞`-to-real bridge -/

/-- `volSq o ω = (clusterVol ω o ^ 2).toReal`: the `ℝ≥0∞`-valued square converts to the real
square *unconditionally* (`ENNReal.toReal_pow`), including at `⊤`. -/
theorem volSq_apply (o : V) (ω : Config V) :
    volSq o ω = (clusterVol ω o ^ 2).toReal := by
  simp only [volSq, ENNReal.toReal_pow]

/-- The Bochner integral of `|K_o|²` against a probability measure is the `.toReal` of its
`ℝ≥0∞`-valued second moment, as soon as that moment is finite.  No cap, no bounded truncation. -/
theorem integral_volSq_eq_toReal_lintegral (μ : Measure (Config V)) (o : V)
    (hfin : ∫⁻ ω, clusterVol ω o ^ 2 ∂μ ≠ ⊤) :
    ∫ ω, volSq o ω ∂μ = (∫⁻ ω, clusterVol ω o ^ 2 ∂μ).toReal := by
  have hf := Measurable.pow_const (measurable_clusterVol (V := V) o) 2
  rw [show (fun ω => volSq o ω) = fun ω : Config V => (clusterVol ω o ^ (2 : ℕ)).toReal from
    funext fun ω => volSq_apply o ω]
  exact integral_toReal hf.aemeasurable (ae_lt_top hf hfin)

/-- At the source model: the real integral of `|K_0|²` against `M.cutLaw r` is exactly the source's
second cut-off moment `M.cutMomentReal 2 r`, under finiteness of the moment. -/
theorem integral_volSq_cutLaw (M : SourceModelData) {r : ℝ} (hfin : M.cutMoment 2 r ≠ ⊤) :
    ∫ ω, volSq (0 : M.V) ω ∂(M.cutLaw r) = M.cutMomentReal 2 r :=
  integral_volSq_eq_toReal_lintegral (V := M.V) (M.cutLaw r) 0 hfin

/-! ## 2. The insertion-error decomposition of the window flux -/

/-- The window flux minus the windowed *limit* flux is the windowed inner product of `c_r` with
the per-edge pivot differences. -/
theorem windowFlux_sub_eq (g : Config V → ℝ) (c : ℝ → Sym2 V → ℝ)
    (μ : ℝ → Measure (Config V)) (S : Finset (Sym2 V)) (r : ℝ) :
    windowFlux g c μ S r - ∑ e ∈ S, c r e * pivotalFlux (μ r) g e
      = ∑ e ∈ S, c r e * (pivotalFlux (μ r) (cutFun S g) e - pivotalFlux (μ r) g e) := by
  simp only [windowFlux, Finset.sum_sub_distrib, mul_sub]

/-- The insertion error `insertionFlux` is nonnegative. -/
theorem insertionFlux_nonneg (g : Config V → ℝ) (c : ℝ → Sym2 V → ℝ)
    (μ : ℝ → Measure (Config V)) (S : Finset (Sym2 V)) (r : ℝ) :
    0 ≤ insertionFlux g c μ S r :=
  Finset.sum_nonneg fun e _ => by positivity

/-- The window flux differs from the windowed limit flux by at most the insertion error. -/
theorem abs_windowFlux_sub_le (g : Config V → ℝ) (c : ℝ → Sym2 V → ℝ)
    (μ : ℝ → Measure (Config V)) (S : Finset (Sym2 V)) (r : ℝ) :
    |windowFlux g c μ S r - ∑ e ∈ S, c r e * pivotalFlux (μ r) g e|
      ≤ insertionFlux g c μ S r := by
  rw [windowFlux_sub_eq g c μ S r, insertionFlux]
  refine (Finset.abs_sum_le_sum_abs (fun e =>
    c r e * (pivotalFlux (μ r) (cutFun S g) e - pivotalFlux (μ r) g e)) S).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun e _ => abs_mul _ _

/-! ## 3. (T1) plus (T2) give the local-uniform window-flux convergence -/

/-- **The exchange bookkeeping.**  If the infinite pivotal series is the locally uniform limit of
its windows (T1) and the insertion errors vanish locally uniformly (T2), then the finite-window
pivotal flux sums converge locally uniformly to the same limit. -/
theorem tendstoLocallyUniformlyOn_of_split {g : Config V → ℝ} {c : ℝ → Sym2 V → ℝ}
    {μ : ℝ → Measure (Config V)} {S : ℕ → Finset (Sym2 V)} {Φ : ℝ → ℝ} {I : Set ℝ}
    (h1 : LocallyUniformLimitFlux g c μ S Φ I) (h2 : UniformInsertionFlux g c μ S I) :
    TendstoLocallyUniformlyOn (fun k r => windowFlux g c μ (S k) r) Φ atTop I := by
  simp only [LocallyUniformLimitFlux, UniformInsertionFlux, TendstoLocallyUniformlyOn] at h1 h2 ⊢
  intro u hu x hx
  obtain ⟨ε, hε, huε⟩ := Metric.mem_uniformity_dist.mp hu
  have hu2 : {p : ℝ × ℝ | dist p.1 p.2 < ε / 2} ∈ 𝓤 ℝ :=
    Metric.mem_uniformity_dist.mpr ⟨ε / 2, by linarith, fun a b hab => hab⟩
  obtain ⟨t1, ht1, hF1⟩ := h1 _ hu2 x hx
  obtain ⟨t2, ht2, hF2⟩ := h2 _ hu2 x hx
  refine ⟨t1 ∩ t2, Filter.inter_mem ht1 ht2, ?_⟩
  filter_upwards [hF1, hF2] with k hk1 hk2
  intro y hy
  have h1' : dist (Φ y) (∑ e ∈ S k, c y e * pivotalFlux (μ y) g e) < ε / 2 := hk1 y hy.1
  have h2' : dist (0 : ℝ) (insertionFlux g c μ (S k) y) < ε / 2 := hk2 y hy.2
  have h3 : dist (∑ e ∈ S k, c y e * pivotalFlux (μ y) g e) (windowFlux g c μ (S k) y)
      ≤ insertionFlux g c μ (S k) y := by
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_windowFlux_sub_le g c μ (S k) y
  have h4 : insertionFlux g c μ (S k) y < ε / 2 := by
    have h5 : |insertionFlux g c μ (S k) y| < ε / 2 := by
      simpa only [Real.dist_eq, zero_sub, abs_neg] using h2'
    rwa [abs_of_nonneg (insertionFlux_nonneg g c μ (S k) y)] at h5
  refine huε ?_
  calc dist (Φ y) (windowFlux g c μ (S k) y)
      ≤ dist (Φ y) (∑ e ∈ S k, c y e * pivotalFlux (μ y) g e)
        + dist (∑ e ∈ S k, c y e * pivotalFlux (μ y) g e) (windowFlux g c μ (S k) y) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! ## 4. The finite-window Russo identity at the source model -/

/-- **The finite-window Russo derivative at `M.cutLaw`.**  For a window `S`, any real functional
`g`, and an off-`cornerRadii` positive radius, the `r`-derivative of the window expectation against
`M.cutLaw` is the finite pivotal-flux sum with the source's edge weights `M.cutEdgeDeriv`. -/
theorem hasDerivAt_windowIntegral_cutLaw (M : SourceModelData) (S : Finset (Sym2 M.V))
    (g : Config M.V → ℝ) {r : ℝ} (hr : 0 < r) (hoff : r ∉ M.cornerRadii) :
    HasDerivAt (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r'))
      (∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (cutFun S g) e) r := by
  have h := hasDerivAt_integral_cutFun (V := M.V) M.cutProb (M.cutEdgeDeriv r) S g
    (fun e => M.hasDerivAt_cutProb_off_of_pos hr hoff e)
  refine h.congr_deriv ?_
  rw [← Finset.sum_coe_sort S (fun e => M.cutEdgeDeriv r e *
    pivotalFlux (M.cutLaw r) (cutFun S g) e)]
  refine Finset.sum_congr rfl fun e _ => ?_
  show M.cutEdgeDeriv r ↑e * pivotalFlux (edgeMeasure (M.cutProb r)) (cutFun S g) ↑e
      = M.cutEdgeDeriv r ↑e * pivotalFlux (M.cutLaw r) (cutFun S g) ↑e
  rw [M.cutLaw_eq_edgeMeasure r]

/-! ## 5. The reduction -/

/-- **The off-corner `p = 2` derivative, reduced to (T1) and (T2).**

For the source model, an edge-exhausting window family, and an open radius window `I` of positive
off-`cornerRadii` radii on which the second cut-off moment is finite:

* `hconv` — the window moments converge to the infinite-volume moment `M.cutMomentReal 2 r`
  (Section 6 of this file discharges it from monotone convergence, with no cap);
* `hunif` — the finite-window pivotal flux sums converge to `M.rhsScalarTwo` **locally uniformly on
  `I`**; by `tendstoLocallyUniformlyOn_of_split` it suffices to provide (T1) and (T2);

then `r ↦ M.cutMomentReal 2 r` has derivative `M.rhsScalarTwo r0` at `r0`.

The derivative value is not a free parameter: the fixed-radius FLUX identity pins the infinite
pivotal series to `M.rhsScalarTwo` at each fixed radius (see the discussion in Section 4 of the
report; this file does not use it, since `hunif` already carries the limit). -/
theorem hasDerivAt_integral_clusterVol_sq_cutLaw (M : SourceModelData)
    (S : ℕ → Finset (Sym2 M.V)) {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hpos : ∀ r ∈ I, 0 < r) (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hfin : ∀ r ∈ I, M.cutMoment 2 r ≠ ⊤)
    (hconv : ∀ r ∈ I, Tendsto
      (fun k => ∫ ω, cutFun (S k) (volSq (0 : M.V)) ω ∂(M.cutLaw r)) atTop
      (𝓝 (M.cutMomentReal 2 r)))
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (cutFun (S k) (volSq (0 : M.V))) e)
      (fun r => M.rhsScalarTwo r) atTop I) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have hderiv : ∀ k : ℕ, ∀ r ∈ I,
      HasDerivAt (fun r' => ∫ ω, cutFun (S k) (volSq (0 : M.V)) ω ∂(M.cutLaw r'))
        (∑ e ∈ S k, M.cutEdgeDeriv r e *
          pivotalFlux (M.cutLaw r) (cutFun (S k) (volSq (0 : M.V))) e) r :=
    fun k r hr => hasDerivAt_windowIntegral_cutLaw M (S k) _ (hpos r hr) (hoff r hr)
  have hconv' : ∀ r ∈ I, Tendsto
      (fun k => ∫ ω, cutFun (S k) (volSq (0 : M.V)) ω ∂(M.cutLaw r)) atTop
      (𝓝 (∫ ω, volSq (0 : M.V) ω ∂(M.cutLaw r))) := by
    intro r hr
    rw [integral_volSq_cutLaw M (hfin r hr)]
    exact hconv r hr
  have hmain : HasDerivAt (fun r => ∫ ω, volSq (0 : M.V) ω ∂(M.cutLaw r))
      (M.rhsScalarTwo r0) r0 :=
    hasDerivAt_integral_of_windowFlux (V := M.V) S (fun r => M.cutLaw r)
      (fun r e => M.cutEdgeDeriv r e) hI hderiv hconv' hunif hr0
  have hEq : (fun r => ∫ ω, volSq (0 : M.V) ω ∂(M.cutLaw r))
      =ᶠ[𝓝 r0] (fun r => M.cutMomentReal 2 r) := by
    filter_upwards [hI.mem_nhds hr0] with r hr
    exact integral_volSq_cutLaw M (hfin r hr)
  exact hEq.hasDerivAt_iff.mp hmain


/-! ## 6. Discharging the window-moment convergence without a cap -/

/-- The Bochner integral of the real part of an `ℝ≥0∞`-valued function is the `.toReal` of its
`ℝ≥0∞`-integral, whenever the latter is finite. -/
theorem integral_toReal_of_lintegral_ne_top (μ : Measure (Config V)) {f : Config V → ℝ≥0∞}
    (hfm : AEMeasurable f μ) (hfin : ∫⁻ ω, f ω ∂μ ≠ ⊤) :
    ∫ ω, (f ω).toReal ∂μ = (∫⁻ ω, f ω ∂μ).toReal :=
  integral_toReal hfm (ae_lt_top' hfm hfin)

/-- **Window moments converge to the second cut-off moment, without any cap.**

Along an edge-exhausting increasing window family, the *unbounded* window functional
`cutFun S k (volSq 0)` increases pointwise to `volSq 0`, and monotone convergence gives
`∫ ω, cutFun (S k) (volSq 0) ω ∂(M.cutLaw r) → M.cutMomentReal 2 r`.  The only hypothesis is
finiteness of the second cut-off moment; no truncation is introduced and none is removed. -/
theorem tendsto_integral_cutFun_volSq (M : SourceModelData) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k) {r : ℝ}
    (hfin : M.cutMoment 2 r ≠ ⊤) :
    Tendsto (fun k => ∫ ω, cutFun (S k) (volSq (0 : M.V)) ω ∂(M.cutLaw r)) atTop
      (𝓝 (M.cutMomentReal 2 r)) := by
  classical
  have hmeas : ∀ k, Measurable fun ω : Config M.V =>
      clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2 := by
    intro k
    have hm0 := (measurable_clusterVol (V := M.V) (0 : M.V)).comp (measurable_cutConfig (S k))
    exact Measurable.pow_const hm0 2
  have hmonoP : Monotone fun k (ω : Config M.V) =>
      clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2 := by
    intro m n hmn ω
    refine pow_le_pow_left₀ (by positivity : (0 : ℝ≥0∞) ≤ _) (clusterVol_mono ?_ (0 : M.V)) 2
    exact fun e he => ⟨he.1, hSmono hmn he.2⟩
  have hint : ∀ k, ∫ ω, cutFun (S k) (volSq (0 : M.V)) ω ∂(M.cutLaw r)
      = (∫⁻ ω, clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2 ∂(M.cutLaw r)).toReal := by
    intro k
    have hm0 := (measurable_clusterVol (V := M.V) (0 : M.V)).comp (measurable_cutConfig (S k))
    have hfm : AEMeasurable (fun ω : Config M.V =>
        clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2) (M.cutLaw r) :=
      (Measurable.pow_const hm0 2).aemeasurable
    have hle : ∫⁻ ω, clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2 ∂(M.cutLaw r) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (lintegral_mono fun ω =>
        pow_le_pow_left₀ (by positivity : (0 : ℝ≥0∞) ≤ _)
          (clusterVol_mono (cutConfig_subset (S k) ω) (0 : M.V)) 2)
    rw [show (fun ω => cutFun (S k) (volSq (0 : M.V)) ω)
        = fun ω => (clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2).toReal from by
      funext ω
      rw [cutFun_apply, restrConfig_restrict, volSq_apply]]
    exact integral_toReal hfm (ae_lt_top' hfm hle)
  have hsup : (fun ω : Config M.V => ⨆ k, clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2)
      = fun ω => clusterVol ω (0 : M.V) ^ 2 := by
    funext ω
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · exact pow_le_pow_left₀ (by positivity : (0 : ℝ≥0∞) ≤ _)
        (clusterVol_mono (cutConfig_subset (S k) ω) (0 : M.V)) 2
    · have hcomp : Tendsto (fun k => clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2) atTop
          (𝓝 (clusterVol ω (0 : M.V) ^ 2)) :=
        ((ENNReal.continuous_pow 2).tendsto _).comp
          (clusterVol_cutConfig_tendsto S hSmono hS ω 0)
      have htup := tendsto_atTop_iSup (fun m n hmn => hmonoP hmn ω)
      exact le_of_eq (tendsto_nhds_unique hcomp htup)
  have hstep : Tendsto
      (fun k => ∫⁻ ω, clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2 ∂(M.cutLaw r)) atTop
      (𝓝 (∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 ∂(M.cutLaw r))) := by
    have hval : (⨆ k, ∫⁻ ω, clusterVol (cutConfig (S k) ω) (0 : M.V) ^ 2 ∂(M.cutLaw r))
        = ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 ∂(M.cutLaw r) := by
      rw [← lintegral_iSup hmeas hmonoP, hsup]
    rw [← hval]
    exact tendsto_atTop_iSup fun m n hmn => lintegral_mono fun ω => hmonoP hmn ω
  have hto := (ENNReal.tendsto_toReal hfin).comp hstep
  simpa only [hint, Function.comp_def, SourceModelData.cutMomentReal,
    SourceModelData.cutMoment] using hto

/-! ## 7. The same reduction with the window-moment input also discharged -/

/-- **The off-corner `p = 2` derivative, reduced to local-uniform flux convergence only.**

Identical to `hasDerivAt_integral_clusterVol_sq_cutLaw`, but the window-moment convergence is now
*derived* from monotone convergence (`tendsto_integral_cutFun_volSq`), so the single remaining
analytic input is `hunif`: local uniform convergence of the finite-window pivotal flux sums to
`M.rhsScalarTwo` on `I`. -/
theorem hasDerivAt_integral_clusterVol_sq_cutLaw' (M : SourceModelData)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hpos : ∀ r ∈ I, 0 < r) (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hfin : ∀ r ∈ I, M.cutMoment 2 r ≠ ⊤)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (cutFun (S k) (volSq (0 : M.V))) e)
      (fun r => M.rhsScalarTwo r) atTop I) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  hasDerivAt_integral_clusterVol_sq_cutLaw M S hI hr0 hpos hoff hfin
    (fun r hr => tendsto_integral_cutFun_volSq M S hSmono hS (hfin r hr)) hunif


/-! ## 8. (T1) from an explicit summable domination (Weierstrass `M`-test) -/

/-- The window family `S` is cofinal in the finite-subset filter as soon as it is monotone and
exhausts the edge set. -/
theorem tendsto_finsetFamily_atTop {ι : Type*} (S : ℕ → Finset ι) (hSmono : Monotone S)
    (hS : ∀ e : ι, ∃ k, e ∈ S k) : Tendsto S atTop atTop := by
  classical
  have hex : ∀ s : Finset ι, ∃ k, s ⊆ S k := by
    intro s
    choose k hk using fun e : ι => hS e
    exact ⟨s.sup k, fun e he => hSmono (Finset.le_sup (f := k) he) (hk e)⟩
  rw [tendsto_atTop_atTop]
  intro s
  obtain ⟨k, hk⟩ := hex s
  exact ⟨k, fun k' hk' e he => hSmono hk' (hk he)⟩

/-- **Weierstrass `M`-test along a cofinal window family.**  A series of functions on a parameter
set `I` whose terms are dominated by a summable sequence has locally uniform partial sums along any
monotone edge-exhausting window family. -/
theorem tendstoLocallyUniformlyOn_finsetSum_of_dominated {ι : Type*}
    (S : ℕ → Finset ι) (hSmono : Monotone S) (hS : ∀ e : ι, ∃ k, e ∈ S k)
    {f : ι → ℝ → ℝ} {u : ι → ℝ} (hu : Summable u) {I : Set ℝ}
    (hfu : ∀ e r, r ∈ I → ‖f e r‖ ≤ u e) :
    TendstoLocallyUniformlyOn (fun k r => ∑ e ∈ S k, f e r) (fun r => ∑' e, f e r) atTop I := by
  have hStend := tendsto_finsetFamily_atTop S hSmono hS
  classical
  have hunif : TendstoUniformlyOn
      (fun t : Finset ι => fun r => ∑ e ∈ t, f e r) (fun r => ∑' e, f e r) atTop I :=
    tendstoUniformlyOn_tsum hu fun e r hr => hfu e r hr
  have hcomp : TendstoUniformlyOn (fun k r => ∑ e ∈ S k, f e r)
      (fun r => ∑' e, f e r) atTop I := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
    exact fun ε hε => hStend.eventually (hunif ε hε)
  exact hcomp.tendstoLocallyUniformlyOn

/-- **(T1) from a summable domination.**  If the per-edge infinite pivotal fluxes are dominated by
a summable sequence `u` uniformly over the radius set `I`, then the infinite pivotal series is the
locally uniform limit of its windows.  This is the precise sense in which (T1) is *not* an extra
analytic input beyond a summability bound: it is a Weierstrass `M`-test. -/
theorem locallyUniformLimitFlux_of_dominated {g : Config V → ℝ} {c : ℝ → Sym2 V → ℝ}
    {μ : ℝ → Measure (Config V)} (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 V, ∃ k, e ∈ S k) {I : Set ℝ} {Φ : ℝ → ℝ} {u : Sym2 V → ℝ}
    (hu : Summable u)
    (hbd : ∀ e r, r ∈ I → ‖c r e * pivotalFlux (μ r) g e‖ ≤ u e)
    (hval : ∀ r ∈ I, Φ r = ∑' e, c r e * pivotalFlux (μ r) g e) :
    LocallyUniformLimitFlux g c μ S Φ I := by
  have h := tendstoLocallyUniformlyOn_finsetSum_of_dominated S hSmono hS hu
    (f := fun e r => c r e * pivotalFlux (μ r) g e) (fun e r hr => hbd e r hr)
  exact h.congr_inseparable_right fun r hr => Inseparable.of_eq (hval r hr).symm

/-! ## 9. The remaining input, stated for the source model -/

/-- **(T1) at the source model.**  A summable per-edge domination of the infinite pivotal flux
`e ↦ M.cutEdgeDeriv r e · pivotalFlux (M.cutLaw r) |K_0|² e`, uniform in `r ∈ I`, together with the
fixed-radius value identity `M.rhsScalarTwo r = Σ'_e M.cutEdgeDeriv r e · pivotalFlux (M.cutLaw r)
|K_0|² e` (the landed FLUX identity, at each fixed `r`), gives (T1) for `Φ = M.rhsScalarTwo`. -/
theorem locallyUniformLimitFlux_cutLaw_of_dominated (M : SourceModelData)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    {I : Set ℝ} {u : Sym2 M.V → ℝ} (hu : Summable u)
    (hbd : ∀ e r, r ∈ I → ‖M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e‖ ≤ u e)
    (hval : ∀ r ∈ I, M.rhsScalarTwo r = ∑' e, M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e) :
    LocallyUniformLimitFlux (volSq (0 : M.V)) (fun r e => M.cutEdgeDeriv r e)
      (fun r => M.cutLaw r) S (fun r => M.rhsScalarTwo r) I :=
  locallyUniformLimitFlux_of_dominated S hSmono hS hu hbd hval

/-- **The capstone of direction (A).**

At an off-`cornerRadii` positive radius `r0`, inside an open radius window `I` on which the second
cut-off moment is finite and the edge exhaustion `S` is available, the source's second cut-off
moment has derivative `M.rhsScalarTwo r0` — provided

* `hu`/`hbd`: an explicit **summable domination** of the infinite pivotal fluxes, uniform in `r ∈ I`
  (this yields (T1) by the Weierstrass `M`-test, `locallyUniformLimitFlux_cutLaw_of_dominated`);
* `hval`: the landed fixed-radius FLUX value identity `M.rhsScalarTwo r = Σ'_e M.cutEdgeDeriv r e ·
  pivotalFlux (M.cutLaw r) |K_0|² e` for `r ∈ I`;
* `hins`: the **uniform insertion tolerance** (T2) `Σ_{e ∈ S k} |M.cutEdgeDeriv r e| ·
  |pivotalFlux (M.cutLaw r) (cutFun (S k) |K_0|²) e − pivotalFlux (M.cutLaw r) |K_0|² e| → 0`
  locally uniformly on `I`.

`hins` is the paper's insertion-tolerance input (Lemma I.4.12 and the use of sharpness in the proof
of Lemma I.4.1); it is the one genuinely non-elementary ingredient, and it is stated here as a
predicate, not assumed away. -/
theorem hasDerivAt_integral_clusterVol_sq_cutLaw_of_dominated (M : SourceModelData)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hpos : ∀ r ∈ I, 0 < r) (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hfin : ∀ r ∈ I, M.cutMoment 2 r ≠ ⊤)
    {u : Sym2 M.V → ℝ} (hu : Summable u)
    (hbd : ∀ e r, r ∈ I → ‖M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e‖ ≤ u e)
    (hval : ∀ r ∈ I, M.rhsScalarTwo r = ∑' e, M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e)
    (hins : UniformInsertionFlux (volSq (0 : M.V)) (fun r e => M.cutEdgeDeriv r e)
      (fun r => M.cutLaw r) S I) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  refine hasDerivAt_integral_clusterVol_sq_cutLaw' M S hSmono hS hI hr0 hpos hoff hfin ?_
  refine tendstoLocallyUniformlyOn_of_split ?_ hins
  exact locallyUniformLimitFlux_cutLaw_of_dominated M S hSmono hS hu hbd hval


/-! ## 10. The quantitative form of the remaining input -/

/-- **The uniform insertion tolerance from an explicit tail bound.**  If the insertion errors are
bounded on `I` by a nonnegative sequence `v k → 0`, then (T2) holds.  Conversely (T2) forces such a
bound at every point of `I`, so this is an exact reformulation of the remaining input rather than a
strengthening: the content is entirely in producing `v`. -/
theorem uniformInsertionFlux_of_le {g : Config V → ℝ} {c : ℝ → Sym2 V → ℝ}
    {μ : ℝ → Measure (Config V)} {S : ℕ → Finset (Sym2 V)} {I : Set ℝ} {v : ℕ → ℝ}
    (hv0 : ∀ k, 0 ≤ v k) (hv : Tendsto v atTop (𝓝 0))
    (hle : ∀ k r, r ∈ I → insertionFlux g c μ (S k) r ≤ v k) :
    UniformInsertionFlux g c μ S I := by
  simp only [UniformInsertionFlux, TendstoLocallyUniformlyOn]
  intro u hu x _
  obtain ⟨ε, hε, huε⟩ := Metric.mem_uniformity_dist.mp hu
  have hev : ∀ᶠ k in atTop, v k < ε := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hv) ε hε
    filter_upwards [eventually_ge_atTop N] with k hk
    have h := hN k hk
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hv0 k)] at h
  refine ⟨I, self_mem_nhdsWithin, ?_⟩
  filter_upwards [hev] with k hk y hy
  have h1 : insertionFlux g c μ (S k) y ≤ v k := hle k y hy
  have h2 : (0 : ℝ) ≤ insertionFlux g c μ (S k) y := insertionFlux_nonneg g c μ (S k) y
  exact huε (by rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg h2]; exact lt_of_le_of_lt h1 hk)

/-- **The complete conditional theorem in checkable form.**

This is `hasDerivAt_integral_clusterVol_sq_cutLaw_of_dominated` with (T2) replaced by the explicit
quantitative bound `Σ_{e ∈ S k} |M.cutEdgeDeriv r e| · |pivotalFlux (M.cutLaw r) (cutFun (S k)
|K_0|²) e − pivotalFlux (M.cutLaw r) |K_0|² e| ≤ v k` for all `r ∈ I`, with `v k ≥ 0`, `v → 0`.

Together with the summable domination `u` of the *infinite* pivotal fluxes, these are exactly the
two quantitative bounds that the interchange needs: `u` is the (locally uniform) flux mass and `v`
the (locally uniform) insertion loss.  Nothing else is assumed. -/
theorem hasDerivAt_integral_clusterVol_sq_cutLaw_of_bounds (M : SourceModelData)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hpos : ∀ r ∈ I, 0 < r) (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hfin : ∀ r ∈ I, M.cutMoment 2 r ≠ ⊤)
    {u : Sym2 M.V → ℝ} (hu : Summable u)
    (hbd : ∀ e r, r ∈ I → ‖M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e‖ ≤ u e)
    (hval : ∀ r ∈ I, M.rhsScalarTwo r = ∑' e, M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e)
    {v : ℕ → ℝ} (hv0 : ∀ k, 0 ≤ v k) (hv : Tendsto v atTop (𝓝 0))
    (hins : ∀ k r, r ∈ I → insertionFlux (volSq (0 : M.V)) (fun r e => M.cutEdgeDeriv r e)
      (fun r => M.cutLaw r) (S k) r ≤ v k) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  hasDerivAt_integral_clusterVol_sq_cutLaw_of_dominated M S hSmono hS hI hr0 hpos hoff hfin hu hbd
    hval (uniformInsertionFlux_of_le hv0 hv hins)


/-- **Consistency check on the interface.**  The domination `hbd` and the value identity `hval`
together force the quantitative consequence `|M.rhsScalarTwo r| ≤ Σ'_e u e` for `r ∈ I`: the total
flux mass is an explicit bound on the derivative.  In particular the interface of
`hasDerivAt_integral_clusterVol_sq_cutLaw_of_bounds` is not satisfiable with a `u` whose total mass
is smaller than the right-hand side. -/
theorem abs_rhsScalarTwo_le_tsum (M : SourceModelData) {I : Set ℝ} {u : Sym2 M.V → ℝ}
    (hu : Summable u)
    (hbd : ∀ e r, r ∈ I → ‖M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e‖ ≤ u e)
    (hval : ∀ r ∈ I, M.rhsScalarTwo r = ∑' e, M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e)
    {r : ℝ} (hr : r ∈ I) :
    |M.rhsScalarTwo r| ≤ ∑' e, u e := by
  have hsum : Summable fun e => M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e :=
    hu.of_norm_bounded (fun e => hbd e r hr)
  rw [hval r hr, ← Real.norm_eq_abs]
  calc ‖∑' e, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e‖
      ≤ ∑' e, ‖M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (volSq (0 : M.V)) e‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' e, u e := hsum.norm.tsum_le_tsum (fun e => hbd e r hr) hu

end PercLib.CriticalLRP.SecondMomentExchange

end

end

#print axioms PercLib.CriticalLRP.SecondMomentExchange.volSq_apply
#print axioms PercLib.CriticalLRP.SecondMomentExchange.integral_volSq_eq_toReal_lintegral
#print axioms PercLib.CriticalLRP.SecondMomentExchange.integral_volSq_cutLaw
#print axioms PercLib.CriticalLRP.SecondMomentExchange.windowFlux_sub_eq
#print axioms PercLib.CriticalLRP.SecondMomentExchange.insertionFlux_nonneg
#print axioms PercLib.CriticalLRP.SecondMomentExchange.abs_windowFlux_sub_le
#print axioms PercLib.CriticalLRP.SecondMomentExchange.tendstoLocallyUniformlyOn_of_split
#print axioms PercLib.CriticalLRP.SecondMomentExchange.hasDerivAt_windowIntegral_cutLaw
#print axioms PercLib.CriticalLRP.SecondMomentExchange.hasDerivAt_integral_clusterVol_sq_cutLaw
#print axioms PercLib.CriticalLRP.SecondMomentExchange.integral_toReal_of_lintegral_ne_top
#print axioms PercLib.CriticalLRP.SecondMomentExchange.tendsto_integral_cutFun_volSq
#print axioms PercLib.CriticalLRP.SecondMomentExchange.hasDerivAt_integral_clusterVol_sq_cutLaw'
#print axioms PercLib.CriticalLRP.SecondMomentExchange.tendsto_finsetFamily_atTop
#print axioms PercLib.CriticalLRP.SecondMomentExchange.tendstoLocallyUniformlyOn_finsetSum_of_dominated
#print axioms PercLib.CriticalLRP.SecondMomentExchange.locallyUniformLimitFlux_of_dominated
#print axioms PercLib.CriticalLRP.SecondMomentExchange.locallyUniformLimitFlux_cutLaw_of_dominated
#print axioms PercLib.CriticalLRP.SecondMomentExchange.hasDerivAt_integral_clusterVol_sq_cutLaw_of_dominated
#print axioms PercLib.CriticalLRP.SecondMomentExchange.uniformInsertionFlux_of_le
#print axioms PercLib.CriticalLRP.SecondMomentExchange.hasDerivAt_integral_clusterVol_sq_cutLaw_of_bounds
#print axioms PercLib.CriticalLRP.SecondMomentExchange.abs_rhsScalarTwo_le_tsum
