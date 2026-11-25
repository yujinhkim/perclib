/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvfwkks`, member `m1`, direction `d2`.

# From pointwise ghost agreement to the vanishing of the insertion error

`Pointwise.lean` proves that, almost surely and for every edge, the flip difference of the
windowed square `cutFun S |K₀|²` equals the flip difference of `|K₀|²` once the window is large
enough.  That is a statement about *one configuration at a time*.  To pass to the pivotal
fluxes (which are means over the cutoff law) one needs an exchange of limit and mean, i.e. a
domination.  This file isolates exactly that exchange and executes the rest of the chain
mechanically:

* `tendsto_sum_finset_zero_of_dominated` — a general dominated-convergence statement for sums
  over a monotone exhausting family of finite sets: if `|F n i| ≤ G i` with `∑ G < ∞` and
  `F n i → 0` for every `i`, then `∑_{i ∈ S n} F n i → 0`.  This is the summation-theoretic
  part of the insertion estimate, and it is unconditional.
* `tendsto_pivotalFlux_cutFun_of_dominated` — the per-edge exchange: a single integrable
  envelope `Env e` dominating *both* the windowed and the untruncated flip difference gives
  `pivotalFlux (cutFun S |K₀|²) e → pivotalFlux |K₀|² e`, by dominated convergence applied to
  the almost-sure eventual agreement of `Pointwise.lean`.
* `tendsto_insertionError_of_envelope` and `tendsto_windowFlux_of_envelope` — the assembly:
  an envelope whose `|cutEdgeDeriv r e|`-weighted *mean* is summable turns the per-edge
  convergence into `M.insertionError (S n) r → 0`, and hence (through the landed
  `tendsto_windowFlux_of_insertionError`) into the actual fixed-radius convergence
  `M.windowFlux (S n) r → M.rhsScalarTwo r`.

The one hypothesis that is *not* discharged here is the existence of such an envelope: a
domination of the windowed closed ghosts that is uniform along the exhausting family.  It is a
genuine second-moment estimate on the model, not a restatement of the convergence — the
pointwise agreement it has to be combined with is proved, and the summation theory it has to be
fed into is proved.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Pointwise

/-!
# Dominated convergence for the insertion error
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PercLib.CriticalLRP

/-! ## 1. Dominated convergence for sums over an exhausting family -/

/-- **Dominated convergence for sums over a monotone exhausting family of finite sets.**

If every entry of the `n`-th family `F n` is dominated in absolute value by a summable `G`, and
if each entry tends to `0`, then the sums over the (arbitrary) finite sets `S n` tend to `0`.
No monotonicity of `S` is needed; the point is that the tail of `G` outside a fixed finite set
can be made small, while on that finite set the entries are eventually small term by term. -/
theorem tendsto_sum_finset_zero_of_dominated {ι : Type*} [Countable ι]
    (S : ℕ → Finset ι) (F : ℕ → ι → ℝ) (G : ι → ℝ)
    (hGnn : ∀ i, 0 ≤ G i) (hG : Summable G)
    (hbound : ∀ n i, |F n i| ≤ G i)
    (hpt : ∀ i, Tendsto (fun n => F n i) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i ∈ S n, F n i) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpartial : Tendsto (fun t : Finset ι => ∑ i ∈ t, G i) atTop (𝓝 (∑' i, G i)) :=
    hG.hasSum
  obtain ⟨t, ht⟩ : ∃ t : Finset ι, (∑' i, G i) - ε / 2 < ∑ i ∈ t, G i :=
    ((tendsto_order.1 hpartial).1 _ (by linarith)).exists
  set T : ι → ℝ := fun i => if i ∉ t then G i else 0 with hTdef
  have hTnn : ∀ i : ι, 0 ≤ T i := by
    intro i
    simp only [hTdef]
    by_cases h : i ∉ t
    · rw [ite_eq_left h]; exact hGnn i
    · rw [ite_eq_right h]
  have hTle : ∀ i : ι, T i ≤ G i := by
    intro i
    simp only [hTdef]
    by_cases h : i ∉ t
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; exact hGnn i
  have hT : Summable T := Summable.of_nonneg_of_le hTnn hTle hG
  have htail : (∑' i : ι, T i) < ε / 2 := by
    have hcomp : ∑ i ∈ t, G i + ∑' (i : ↑(↑t : Set ι)ᶜ), G ↑i = ∑' i, G i :=
      Summable.sum_add_tsum_compl (s := t) hG
    have hEq : (∑' (i : ↑(↑t : Set ι)ᶜ), G ↑i) = ∑' i : ι, T i := by
      rw [tsum_subtype]
      refine tsum_congr fun i => ?_
      rw [Set.indicator_apply]
      change (if i ∈ (↑t : Set ι)ᶜ then G i else 0) = (if i ∉ t then G i else 0)
      by_cases h : i ∈ (↑t : Set ι)ᶜ
      · rw [ite_eq_left h, ite_eq_left (by simpa using h)]
      · rw [ite_eq_right h, ite_eq_right (by simpa using h)]
    linarith
  have hfin : ∀ᶠ n in atTop, ∑ i ∈ t, |F n i| < ε / 2 := by
    have hcont : Tendsto (fun n => ∑ i ∈ t, |F n i|) atTop (𝓝 (∑ i ∈ t, (0 : ℝ))) :=
      tendsto_finsetSum t fun i _ => by simpa using (hpt i).abs
    rw [Finset.sum_const_zero] at hcont
    exact (tendsto_order.1 hcont).2 _ (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfin
  refine ⟨N, fun n hn => ?_⟩
  have hnε : ∑ i ∈ t, |F n i| < ε / 2 := hN n hn
  rw [dist_zero_right]
  calc |∑ i ∈ S n, F n i| ≤ ∑ i ∈ S n, |F n i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ S n ∩ t, |F n i| + ∑ i ∈ S n \ t, |F n i| := by
        rw [← Finset.sum_inter_add_sum_sdiff]
    _ ≤ ∑ i ∈ t, |F n i| + ∑' i : ι, T i := by
        refine add_le_add ?_ ?_
        · refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right) ?_
          intro i _ _; exact abs_nonneg _
        · calc ∑ i ∈ S n \ t, |F n i| ≤ ∑ i ∈ S n \ t, T i :=
                Finset.sum_le_sum fun i hi => by
                  have hTi : T i = G i := by
                    rw [hTdef]
                    exact ite_eq_left (Finset.mem_sdiff.mp hi).2
                  rw [hTi]
                  exact hbound n i
            _ ≤ ∑' i : ι, T i := Summable.sum_le_tsum (S n \ t) (fun i _ => hTnn i) hT
    _ < ε / 2 + ε / 2 := add_lt_add hnε htail
    _ = ε := by ring


/-! ## 2. Measurability of the flip difference -/

variable {V : Type*} [Countable V]

/-- The flip difference of a measurable functional is measurable: changing the state of a
single edge is a measurable operation on configurations. -/
theorem measurable_flipDiff {g : Config V → ℝ} (hg : Measurable g) (e : Sym2 V) :
    Measurable fun ω => flipDiff g e ω := by
  unfold flipDiff
  exact (hg.comp (measurable_forceOn ({e} : Set (Sym2 V)) ({e} : Config V))).sub
    (hg.comp (measurable_forceOn ({e} : Set (Sym2 V)) (∅ : Config V)))

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The squared cluster volume of the origin is a measurable functional of the configuration. -/
theorem measurable_clusterVolSqReal : Measurable M.clusterVolSqReal := by
  have h : Measurable fun ω : Config M.V => (clusterVol ω (0 : M.V)).toReal ^ 2 :=
    (ENNReal.measurable_toReal.comp (measurable_clusterVol (0 : M.V))).pow_const 2
  simpa only [funext M.clusterVolSqReal_apply] using h

/-- **Per-edge exchange of limit and mean.** If a single integrable envelope dominates the
windowed flip differences in absolute value, then the pivotal flux of the windowed square
converges to the pivotal flux of the untruncated square, by dominated convergence applied to the
almost-sure eventual agreement of `Pointwise.lean`. -/
theorem tendsto_pivotalFlux_cutFun_of_dominated (r : ℝ) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (e : Sym2 M.V) (Env : Config M.V → ℝ)
    (hEnvInt : Integrable Env (M.cutLaw r))
    (hbound : ∀ n, ∀ᵐ ω ∂(M.cutLaw r),
      |flipDiff (cutFun (S n) M.clusterVolSqReal) e ω| ≤ Env ω) :
    Tendsto (fun n => pivotalFlux (M.cutLaw r) (cutFun (S n) M.clusterVolSqReal) e) atTop
      (𝓝 (pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)) := by
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun ω => flipDiff (cutFun (S n) M.clusterVolSqReal) e ω) (M.cutLaw r) := fun n =>
    ((measurable_flipDiff (measurable_cutFun M.measurable_clusterVolSqReal) e)).aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂(M.cutLaw r),
      Tendsto (fun n => flipDiff (cutFun (S n) M.clusterVolSqReal) e ω) atTop
        (𝓝 (flipDiff M.clusterVolSqReal e ω)) := by
    filter_upwards [M.ae_eventually_flipDiff_cutFun_eq r h1 S hSmono hSexh] with ω hω
    have hev : (fun n => flipDiff (cutFun (S n) M.clusterVolSqReal) e ω)
        =ᶠ[atTop] (fun _ => flipDiff M.clusterVolSqReal e ω) := hω e
    exact Tendsto.congr' hev.symm tendsto_const_nhds
  simp only [pivotalFlux]
  exact tendsto_integral_of_dominated_convergence Env hmeas hEnvInt hbound hlim

/-- **The insertion error vanishes under a summable envelope.**

Let `Env e` be an integrable function on configurations, nonnegative, dominating in absolute
value *both* the windowed closed flip differences `flipDiff (cutFun (S n) |K₀|²) e` for every
`n` and the untruncated one.  If the `|cutEdgeDeriv r e|`-weighted *means* of `Env` are summable
over the edges, then the insertion error of the window `S n` tends to zero along the exhausting
family.

The proof has no slack: the per-edge difference of pivotal fluxes is bounded by twice the mean
of `Env` (through `abs_integral_le_integral_abs` and `integral_mono_ae`), the per-edge difference
tends to zero by the dominated exchange `tendsto_pivotalFlux_cutFun_of_dominated`, and the
summation is then pure dominated convergence along the exhausting family
(`tendsto_sum_finset_zero_of_dominated`).  The only input not proved here is the envelope. -/
theorem tendsto_insertionError_of_envelope (r : ℝ) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤)
    (Env : Sym2 M.V → Config M.V → ℝ)
    (hEnvInt : ∀ e, Integrable (Env e) (M.cutLaw r))
    (hEnv0 : ∀ e, ∀ᵐ ω ∂(M.cutLaw r), 0 ≤ Env e ω)
    (hEnvSumm : Summable fun e =>
      2 * (|M.cutEdgeDeriv r e| * ∫ ω, Env e ω ∂(M.cutLaw r)))
    (hbound : ∀ n e, ∀ᵐ ω ∂(M.cutLaw r),
      |flipDiff (cutFun (S n) M.clusterVolSqReal) e ω| ≤ Env e ω)
    (hboundLim : ∀ e, ∀ᵐ ω ∂(M.cutLaw r),
      |flipDiff M.clusterVolSqReal e ω| ≤ Env e ω) :
    Tendsto (fun n => M.insertionError (S n) r) atTop (𝓝 0) := by
  classical
  have hconv : ∀ e, Tendsto (fun n => pivotalFlux (M.cutLaw r)
      (cutFun (S n) M.clusterVolSqReal) e) atTop
        (𝓝 (pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)) := fun e =>
    M.tendsto_pivotalFlux_cutFun_of_dominated r S hSmono hSexh h1 e (Env e) (hEnvInt e)
      fun n => hbound n e
  have hEnvnn : ∀ e, 0 ≤ ∫ ω, Env e ω ∂(M.cutLaw r) := fun e =>
    integral_nonneg_of_ae (hEnv0 e)
  have hdiff : ∀ n e, |pivotalFlux (M.cutLaw r) (cutFun (S n) M.clusterVolSqReal) e
      - pivotalFlux (M.cutLaw r) M.clusterVolSqReal e|
      ≤ 2 * ∫ ω, Env e ω ∂(M.cutLaw r) := by
    intro n e
    have hm1 : AEStronglyMeasurable
        (fun ω => |flipDiff (cutFun (S n) M.clusterVolSqReal) e ω|) (M.cutLaw r) :=
      ((measurable_flipDiff (measurable_cutFun M.measurable_clusterVolSqReal) e)).abs
        |>.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable
        (fun ω => |flipDiff M.clusterVolSqReal e ω|) (M.cutLaw r) :=
      ((measurable_flipDiff M.measurable_clusterVolSqReal e)).abs.aestronglyMeasurable
    have hI1 : Integrable (fun ω => |flipDiff (cutFun (S n) M.clusterVolSqReal) e ω|)
        (M.cutLaw r) :=
      Integrable.mono' (hEnvInt e) hm1 (by simpa only [Real.norm_eq_abs, abs_abs] using hbound n e)
    have hI2 : Integrable (fun ω => |flipDiff M.clusterVolSqReal e ω|) (M.cutLaw r) :=
      Integrable.mono' (hEnvInt e) hm2
        (by simpa only [Real.norm_eq_abs, abs_abs] using hboundLim e)
    have hle1 : ∫ ω, |flipDiff (cutFun (S n) M.clusterVolSqReal) e ω| ∂(M.cutLaw r)
        ≤ ∫ ω, Env e ω ∂(M.cutLaw r) := integral_mono_ae hI1 (hEnvInt e) (hbound n e)
    have hle2 : ∫ ω, |flipDiff M.clusterVolSqReal e ω| ∂(M.cutLaw r)
        ≤ ∫ ω, Env e ω ∂(M.cutLaw r) := integral_mono_ae hI2 (hEnvInt e) (hboundLim e)
    simp only [pivotalFlux]
    calc |∫ ω, flipDiff (cutFun (S n) M.clusterVolSqReal) e ω ∂(M.cutLaw r)
          - ∫ ω, flipDiff M.clusterVolSqReal e ω ∂(M.cutLaw r)|
        ≤ |∫ ω, flipDiff (cutFun (S n) M.clusterVolSqReal) e ω ∂(M.cutLaw r)|
            + |∫ ω, flipDiff M.clusterVolSqReal e ω ∂(M.cutLaw r)| := abs_sub _ _
      _ ≤ ∫ ω, Env e ω ∂(M.cutLaw r) + ∫ ω, Env e ω ∂(M.cutLaw r) :=
          add_le_add (le_trans abs_integral_le_integral_abs hle1)
            (le_trans abs_integral_le_integral_abs hle2)
      _ = 2 * ∫ ω, Env e ω ∂(M.cutLaw r) := by ring
  have hpt : ∀ e, Tendsto (fun n => |M.cutEdgeDeriv r e| * |pivotalFlux (M.cutLaw r)
      (cutFun (S n) M.clusterVolSqReal) e - pivotalFlux (M.cutLaw r) M.clusterVolSqReal e|)
      atTop (𝓝 0) := by
    intro e
    have h1' := (hconv e).sub_const (pivotalFlux (M.cutLaw r) M.clusterVolSqReal e)
    have h2 : Tendsto (fun n => |pivotalFlux (M.cutLaw r) (cutFun (S n) M.clusterVolSqReal) e
        - pivotalFlux (M.cutLaw r) M.clusterVolSqReal e|) atTop (𝓝 0) := by
      simpa using h1'.abs
    simpa using h2.const_mul (|M.cutEdgeDeriv r e|)
  have hbF : ∀ n e, |(|M.cutEdgeDeriv r e| * |pivotalFlux (M.cutLaw r)
      (cutFun (S n) M.clusterVolSqReal) e - pivotalFlux (M.cutLaw r) M.clusterVolSqReal e|)|
      ≤ 2 * (|M.cutEdgeDeriv r e| * ∫ ω, Env e ω ∂(M.cutLaw r)) := by
    intro n e
    have hc : 0 ≤ |M.cutEdgeDeriv r e| := abs_nonneg _
    rw [abs_of_nonneg (mul_nonneg hc (abs_nonneg _))]
    calc |M.cutEdgeDeriv r e| * |pivotalFlux (M.cutLaw r) (cutFun (S n) M.clusterVolSqReal) e
          - pivotalFlux (M.cutLaw r) M.clusterVolSqReal e|
        ≤ |M.cutEdgeDeriv r e| * (2 * ∫ ω, Env e ω ∂(M.cutLaw r)) :=
          mul_le_mul_of_nonneg_left (hdiff n e) hc
      _ = 2 * (|M.cutEdgeDeriv r e| * ∫ ω, Env e ω ∂(M.cutLaw r)) := by ring
  have hGnn : ∀ e, 0 ≤ 2 * (|M.cutEdgeDeriv r e| * ∫ ω, Env e ω ∂(M.cutLaw r)) := fun e =>
    mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) (hEnvnn e))
  have hmain := tendsto_sum_finset_zero_of_dominated S
    (fun n e => |M.cutEdgeDeriv r e| * |pivotalFlux (M.cutLaw r)
      (cutFun (S n) M.clusterVolSqReal) e - pivotalFlux (M.cutLaw r) M.clusterVolSqReal e|)
    (fun e => 2 * (|M.cutEdgeDeriv r e| * ∫ ω, Env e ω ∂(M.cutLaw r)))
    hGnn hEnvSumm hbF hpt
  simpa only [SourceModelData.insertionError] using hmain

/-- **The fixed-radius window flux converges under a summable envelope.**

This is `hfluxConv` — the actual
`Tendsto (fun n => M.windowFlux (S n) r) atTop (𝓝 (M.rhsScalarTwo r))` consumed by the landed
orchestration `hasDerivAt_cutMomentReal_two_integrated` — obtained from
`tendsto_insertionError_of_envelope` and the landed
`tendsto_windowFlux_of_insertionError`.  What is *not* assumed is any form of the conclusion:
the hypotheses are (i) a pointwise-in-`ω`, absolute-value domination of the windowed and
untruncated closed flip differences by a common envelope `Env e`, and (ii) summability over `e`
of the `|cutEdgeDeriv r e|`-weighted *means* of `Env`.  The pointwise agreement that turns (i)
into per-edge convergence is proved in `Pointwise.lean` and does not use (i) or (ii). -/
theorem tendsto_windowFlux_of_envelope (r : ℝ) (hr : 0 < r) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hSexh : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤)
    (Env : Sym2 M.V → Config M.V → ℝ)
    (hEnvInt : ∀ e, Integrable (Env e) (M.cutLaw r))
    (hEnv0 : ∀ e, ∀ᵐ ω ∂(M.cutLaw r), 0 ≤ Env e ω)
    (hEnvSumm : Summable fun e =>
      2 * (|M.cutEdgeDeriv r e| * ∫ ω, Env e ω ∂(M.cutLaw r)))
    (hbound : ∀ n e, ∀ᵐ ω ∂(M.cutLaw r),
      |flipDiff (cutFun (S n) M.clusterVolSqReal) e ω| ≤ Env e ω)
    (hboundLim : ∀ e, ∀ᵐ ω ∂(M.cutLaw r),
      |flipDiff M.clusterVolSqReal e ω| ≤ Env e ω) :
    Tendsto (fun n => M.windowFlux (S n) r) atTop (𝓝 (M.rhsScalarTwo r)) :=
  M.tendsto_windowFlux_of_insertionError r hr S hSmono hSexh h1 hp2
    (M.tendsto_insertionError_of_envelope r S hSmono hSexh h1 Env hEnvInt hEnv0 hEnvSumm
      hbound hboundLim)

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP

#print axioms tendsto_sum_finset_zero_of_dominated
#print axioms measurable_flipDiff

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms measurable_clusterVolSqReal
#print axioms tendsto_pivotalFlux_cutFun_of_dominated
#print axioms tendsto_insertionError_of_envelope
#print axioms tendsto_windowFlux_of_envelope

end PercLib.CriticalLRP.Orchestration.SourceModelData
