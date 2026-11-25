/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvi25ua`, member `m1`, direction (A).

# The uniform-in-radius majorant of the `p = 2` window fluxes

This file proves the two halves of the majorant estimate for the candidate
`G = M.windowMajorant C b = 2 * (M.rhsScalarTwo · + 3 C (M.cutMoment 4 b).toReal)` of
`WindowMajorant/Defs.lean`:

* `windowFlux_le_windowMajorant` — the pointwise bound `M.windowFlux (S n) t ≤ G t` for **every**
  window index `n` and every `t ∈ Ioc a b`, i.e. `IsWindowMajorantOn … (Ioc a b)`;
* `intervalIntegrable_windowMajorant` — `IntervalIntegrable G volume a b`.

Neither proof uses monotonicity of the window fluxes in the window index, nor monotonicity of the
closed ghost `quadEdgeWeight (cutRange r)`, nor of the pivotal flip. The chain for the pointwise
bound is, at a fixed radius `t ∈ Ioc a b`:

1. `pivotalFlux (cutLaw t) (cutFun (S n) |K₀|²) e = ∫ flipDiff (cutFun (S n) |K₀|²) e ∂cutLaw t`
   and `flipDiff (cutFun (S n) |K₀|²) e ≤ envelope t e` almost surely
   (`ae_abs_flipDiff_cutFun_le_envelope`), so the pivotal flux is at most `∫ envelope t e`;
2. `M.cutEdgeDeriv t e ≥ 0`, so summing `cutEdgeDeriv t e * pivotalFlux …` over `e ∈ S n` gives at
   most `∑_{e ∈ S n} |cutEdgeDeriv t e| ∫ envelope t e`, and this is at most the `tsum` because all
   terms are nonnegative and the family is summable
   (`summable_two_deriv_mul_integral_envelope`);
3. the per-edge coefficient inequality `two_deriv_mul_integral_envelope_le` turns the `tsum` into
   `coeffRHS t * ∑' e, E[unexclEdgeWeight (· \ {e}) 0 e]`, and the total unexcluded ghost mass is at
   most `p2RHS t + 3 cutMoment 4 t` (`tsum_lintegral_unexclEdgeWeight_sdiff_le`), converted to
   `ℝ` with `ENNReal.tsum_toReal_eq`;
4. `coeffRHS t ≥ 0`, `coeffRHS t ≤ C` and `cutMoment 4 t ≤ cutMoment 4 b` bound the result by
   `rhsScalarTwo t + 3 C (cutMoment 4 b).toReal`, and the outer factor `2` of `G` absorbs it.

The interval integrability is the landed `intervalIntegrable_rhsScalarTwo_of_coeffBound`, which
needs the explicit pointwise coefficient bound and a *measurable* `rhsScalarTwo`; the measurability
is kept as an explicit hypothesis here because it is not implied by finiteness of the fourth
moment. No `sorry`, no auxiliary axiom.

`hasDerivAt_cutMomentReal_two_of_majorant` at the end is only the interface check: it feeds the two
components into the landed monotone-free FTC
`hasDerivAt_cutMomentReal_two_of_window_majorant`. It keeps the fixed-radius convergence
`hfluxConv`, the window-moment convergence `hmoment` and the off-sphere continuity `hrhsCont` as
explicit hypotheses, and it is *not* a proof of a radius derivative from fixed-radius convergence
alone.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.WindowMajorant.Defs

/-!
# The two halves of the majorant estimate
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The first cutoff moment from the fourth -/

/-- Finiteness of the fourth cutoff moment implies finiteness of the first, because
`1 ≤ |K_0|`.  This is the `cutMassAt r 0 ≠ ⊤` input of the almost-sure ghost domination. -/
theorem cutMassAt_zero_ne_top_of_cutMoment_four {t : ℝ} (h4 : M.cutMoment 4 t ≠ ⊤) :
    M.cutMassAt t (0 : M.V) ≠ ⊤ := by
  have hmom : M.cutMoment 1 t ≤ M.cutMoment 4 t :=
    lintegral_mono fun ω =>
      pow_le_pow_right₀ (E1Sign.one_le_clusterVol M ω (0 : M.V)) (by norm_num)
  have h1c : M.cutMoment 1 t ≠ ⊤ := ne_top_of_le_ne_top h4 hmom
  simpa only [cutMassAt, cutMoment, pow_one] using h1c

/-! ## 2. The per-edge pivotal flux against the envelope mean -/

/-- **The pivotal flux of the finite-window square is at most the mean of the ghost envelope.**
This is the only place the `p = 2` estimate enters the majorant: the closed ghost
`flipDiff (cutFun (S n) |K₀|²) e` is dominated almost surely by `envelope t e`
(`ae_abs_flipDiff_cutFun_le_envelope`), both sides are integrable (the windowed flip difference
unconditionally, the envelope by the finite fourth moment), and `pivotalFlux` is their mean.

No monotonicity of `envelope` or of the closed ghost in the configuration is used: the domination
is already `ℝ≥0∞`-valued and junk-free, and the passage to `ℝ` is a plain integral inequality. -/
theorem pivotalFlux_cutFun_le_integral_envelope {t : ℝ}
    (h4 : M.cutMoment 4 t ≠ ⊤) (S : ℕ → Finset (Sym2 M.V)) (n : ℕ) (e : Sym2 M.V) :
    pivotalFlux (M.cutLaw t) (cutFun (S n) M.clusterVolSqReal) e
      ≤ ∫ ω, M.envelope t e ω ∂(M.cutLaw t) := by
  have h1 : M.cutMassAt t (0 : M.V) ≠ ⊤ := M.cutMassAt_zero_ne_top_of_cutMoment_four h4
  have hae : ∀ᵐ ω ∂(M.cutLaw t),
      flipDiff (cutFun (S n) M.clusterVolSqReal) e ω ≤ M.envelope t e ω :=
    (M.ae_abs_flipDiff_cutFun_le_envelope t h1 S n e).mono fun ω hω =>
      le_trans (le_abs_self _) hω
  simp only [pivotalFlux]
  exact integral_mono_ae (M.integrable_flipDiff_cutFun_clusterVolSqReal (S n) t e)
    (M.integrable_envelope t h4 e) hae

/-! ## 3. Summability and the summed coefficient bound -/

/-- The coefficient-weighted envelope means are nonnegative. -/
theorem abs_cutEdgeDeriv_mul_integral_envelope_nonneg (t : ℝ) (e : Sym2 M.V) :
    0 ≤ |M.cutEdgeDeriv t e| * ∫ ω, M.envelope t e ω ∂(M.cutLaw t) :=
  mul_nonneg (abs_nonneg _) (integral_nonneg fun ω => M.envelope_nonneg t e ω)

/-- Summability of the coefficient-weighted envelope means, without the factor `2` of the landed
`summable_two_deriv_mul_integral_envelope`. -/
theorem summable_abs_cutEdgeDeriv_mul_integral_envelope {t : ℝ} (ht : 0 < t)
    (h4 : M.cutMoment 4 t ≠ ⊤) :
    Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv t e| * ∫ ω, M.envelope t e ω ∂(M.cutLaw t) := by
  have hnn := M.abs_cutEdgeDeriv_mul_integral_envelope_nonneg t
  refine Summable.of_nonneg_of_le hnn (fun e => ?_)
    (M.summable_two_deriv_mul_integral_envelope t ht h4)
  linarith [hnn e]

/-- **The summed coefficient bound.**  The total of the coefficient-weighted envelope means over
*all* edges is at most `coeffRHS t · (p2RHS t + 3 cutMoment 4 t)`, in real value.

The proof writes the `ℝ≥0∞` total unexcluded ghost mass `∑' e, E[unexclEdgeWeight (· \ {e}) 0 e]`
as a `tsum` of finite lintegrals (`ENNReal.tsum_toReal_eq`, whose finiteness is
`lintegral_unexclEdgeWeight_sdiff_ne_top`), bounds it by `p2RHS t + 3 cutMoment 4 t`
(`tsum_lintegral_unexclEdgeWeight_sdiff_le`), converts with `ENNReal.toReal_add`/`toReal_mul` and
pulls out the nonnegative coefficient with `mul_le_mul_of_nonneg_left`.  No term is dropped: the
per-edge inequality is the landed `two_deriv_mul_integral_envelope_le` divided by two. -/
theorem tsum_abs_cutEdgeDeriv_mul_integral_envelope_le {t : ℝ} (ht : 0 < t)
    (h4 : M.cutMoment 4 t ≠ ⊤) :
    (∑' e : Sym2 M.V, |M.cutEdgeDeriv t e| * ∫ ω, M.envelope t e ω ∂(M.cutLaw t))
      ≤ M.coeffRHS t * (M.p2RHS t + 3 * M.cutMoment 4 t).toReal := by
  have hI : Summable fun e : Sym2 M.V =>
      (∫⁻ ω, M.unexclEdgeWeight t (ω \ {e}) (0 : M.V) e ∂(M.cutLaw t)).toReal :=
    ENNReal.summable_toReal
      (ne_top_of_le_ne_top (M.p2RHS_add_three_cutMoment_four_ne_top t h4)
        (M.tsum_lintegral_unexclEdgeWeight_sdiff_le t))
  have hY : Summable fun e : Sym2 M.V =>
      M.coeffRHS t *
        (∫⁻ ω, M.unexclEdgeWeight t (ω \ {e}) (0 : M.V) e ∂(M.cutLaw t)).toReal :=
    hI.mul_left _
  have hX := M.summable_abs_cutEdgeDeriv_mul_integral_envelope ht h4
  have hpt : ∀ e : Sym2 M.V,
      |M.cutEdgeDeriv t e| * ∫ ω, M.envelope t e ω ∂(M.cutLaw t)
        ≤ M.coeffRHS t *
          (∫⁻ ω, M.unexclEdgeWeight t (ω \ {e}) (0 : M.V) e ∂(M.cutLaw t)).toReal := by
    intro e
    have h2 := M.two_deriv_mul_integral_envelope_le t ht h4 e
    linarith
  refine le_trans (hX.tsum_le_tsum hpt hY) ?_
  have htoReal :
      (∑' e : Sym2 M.V,
        (∫⁻ ω, M.unexclEdgeWeight t (ω \ {e}) (0 : M.V) e ∂(M.cutLaw t)).toReal)
      = (∑' e : Sym2 M.V,
        ∫⁻ ω, M.unexclEdgeWeight t (ω \ {e}) (0 : M.V) e ∂(M.cutLaw t)).toReal :=
    (ENNReal.tsum_toReal_eq fun e => M.lintegral_unexclEdgeWeight_sdiff_ne_top t h4 e).symm
  rw [tsum_mul_left, htoReal]
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono (M.p2RHS_add_three_cutMoment_four_ne_top t h4)
      (M.tsum_lintegral_unexclEdgeWeight_sdiff_le t))
    (M.coeffRHS_nonneg ht)

/-! ## 4. The pointwise domination (first half of the majorant) -/

/-- **The sharp pointwise bound**: the window flux is at most the accepted `p = 2` right-hand side
plus the explicit constant `3 C (cutMoment 4 b).toReal`.  No factor `2` is needed: the landed
per-edge inequality already carries its own factor `2`, which cancels.  The factor-two form
`windowFlux_le_windowMajorant` is kept because the landed interval-integrability lemma
`intervalIntegrable_candidateMajorant` is stated for `2 * (rhsScalarTwo + 3 C (cutMoment 4 b).toReal)`.

Hypotheses: `0 < a ≤ b`; finiteness of the fourth cutoff moment at every radius of `Icc a b`; an
explicit constant `C ≥ 0` bounding `|M.coeffRHS|` on `Icc a b`.  The window family `S` is
arbitrary — in particular not assumed monotone, nested or exhausting. -/
theorem windowFlux_le_rhsScalarTwo_add_const {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h4 : ∀ t ∈ Set.Icc a b, M.cutMoment 4 t ≠ ⊤)
    (hC0 : 0 ≤ C) (hC : ∀ t ∈ Set.Icc a b, |M.coeffRHS t| ≤ C)
    (S : ℕ → Finset (Sym2 M.V)) :
    ∀ n, ∀ t ∈ Set.Ioc a b,
      M.windowFlux (S n) t ≤ M.rhsScalarTwo t + M.windowMajorantConst C b := by
  intro n t ht
  obtain ⟨hat, htb⟩ := ht
  have ht0 : 0 < t := lt_trans ha hat
  have htI : t ∈ Set.Icc a b := ⟨le_of_lt hat, htb⟩
  have h4t : M.cutMoment 4 t ≠ ⊤ := h4 t htI
  have h4b : M.cutMoment 4 b ≠ ⊤ := h4 b ⟨hab, le_rfl⟩
  -- the per-edge comparison with the envelope mean
  have hper : ∀ e : Sym2 M.V,
      M.cutEdgeDeriv t e * pivotalFlux (M.cutLaw t) (cutFun (S n) M.clusterVolSqReal) e
        ≤ |M.cutEdgeDeriv t e| * ∫ ω, M.envelope t e ω ∂(M.cutLaw t) := by
    intro e
    have hcd : 0 ≤ M.cutEdgeDeriv t e := M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg ht0) e
    calc M.cutEdgeDeriv t e * pivotalFlux (M.cutLaw t) (cutFun (S n) M.clusterVolSqReal) e
        = |M.cutEdgeDeriv t e| * pivotalFlux (M.cutLaw t) (cutFun (S n) M.clusterVolSqReal) e := by
          rw [abs_of_nonneg hcd]
      _ ≤ |M.cutEdgeDeriv t e| * ∫ ω, M.envelope t e ω ∂(M.cutLaw t) :=
          mul_le_mul_of_nonneg_left
            (M.pivotalFlux_cutFun_le_integral_envelope h4t S n e) (abs_nonneg _)
  -- summation over the window, then over all edges
  have hstep1 : M.windowFlux (S n) t
      ≤ ∑' e : Sym2 M.V, |M.cutEdgeDeriv t e| * ∫ ω, M.envelope t e ω ∂(M.cutLaw t) := by
    rw [SourceModelData.windowFlux]
    refine le_trans (Finset.sum_le_sum fun e _ => hper e) ?_
    exact (M.summable_abs_cutEdgeDeriv_mul_integral_envelope ht0 h4t).sum_le_tsum (S n)
      fun e _ => M.abs_cutEdgeDeriv_mul_integral_envelope_nonneg t e
  -- the coefficient bound, with the fourth moment frozen at `b`
  have hstep3 : M.coeffRHS t * (M.p2RHS t + 3 * M.cutMoment 4 t).toReal
      ≤ M.rhsScalarTwo t + M.windowMajorantConst C b := by
    have htoReal : (M.p2RHS t + 3 * M.cutMoment 4 t).toReal
        = (M.p2RHS t).toReal + 3 * (M.cutMoment 4 t).toReal := by
      rw [ENNReal.toReal_add (M.p2RHS_ne_top_of_fourth h4t)
        (ENNReal.mul_ne_top (by norm_num) h4t), ENNReal.toReal_mul]
      norm_num
    have hcoef : M.coeffRHS t ≤ C := le_trans (le_abs_self _) (hC t htI)
    have hcm : (M.cutMoment 4 t).toReal ≤ (M.cutMoment 4 b).toReal :=
      ENNReal.toReal_mono h4b (M.cutMoment_monotone 4 htb)
    have hmul : M.coeffRHS t * (M.cutMoment 4 t).toReal ≤ C * (M.cutMoment 4 b).toReal :=
      mul_le_mul hcoef hcm ENNReal.toReal_nonneg hC0
    calc M.coeffRHS t * (M.p2RHS t + 3 * M.cutMoment 4 t).toReal
        = M.coeffRHS t * (M.p2RHS t).toReal
            + 3 * (M.coeffRHS t * (M.cutMoment 4 t).toReal) := by
          rw [htoReal]; ring
      _ ≤ M.coeffRHS t * (M.p2RHS t).toReal
            + 3 * (C * (M.cutMoment 4 b).toReal) := by linarith
      _ = M.rhsScalarTwo t + M.windowMajorantConst C b := by
          rw [SourceModelData.rhsScalarTwo, SourceModelData.windowMajorantConst]
          ring
  have hstep2 := M.tsum_abs_cutEdgeDeriv_mul_integral_envelope_le ht0 h4t
  calc M.windowFlux (S n) t
      ≤ ∑' e : Sym2 M.V, |M.cutEdgeDeriv t e| * ∫ ω, M.envelope t e ω ∂(M.cutLaw t) := hstep1
    _ ≤ M.coeffRHS t * (M.p2RHS t + 3 * M.cutMoment 4 t).toReal := hstep2
    _ ≤ M.rhsScalarTwo t + M.windowMajorantConst C b := hstep3

theorem windowFlux_le_windowMajorant {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h4 : ∀ t ∈ Set.Icc a b, M.cutMoment 4 t ≠ ⊤)
    (hC0 : 0 ≤ C) (hC : ∀ t ∈ Set.Icc a b, |M.coeffRHS t| ≤ C)
    (S : ℕ → Finset (Sym2 M.V)) :
    IsWindowMajorantOn (fun n t => M.windowFlux (S n) t) (M.windowMajorant C b)
      (Set.Ioc a b) := by
  intro n t ht
  obtain ⟨hat, htb⟩ := ht
  have ht0 : 0 < t := lt_trans ha hat
  have h0 : 0 ≤ M.rhsScalarTwo t + M.windowMajorantConst C b :=
    add_nonneg (M.rhsScalarTwo_nonneg ht0) (M.windowMajorantConst_nonneg hC0)
  refine le_trans (M.windowFlux_le_rhsScalarTwo_add_const ha hab h4 hC0 hC S n t ⟨hat, htb⟩) ?_
  calc M.rhsScalarTwo t + M.windowMajorantConst C b
      ≤ 2 * (M.rhsScalarTwo t + M.windowMajorantConst C b) := by linarith
    _ = M.windowMajorant C b t := (windowMajorant_apply M C b t).symm

/-- **The same pointwise domination with the fourth cutoff moment assumed finite only at the right
endpoint.**  Finiteness at `b` propagates to every `t ≤ b` by monotonicity of the cutoff moments, so
this is the form in which the majorant is fed to the landed FTC (whose own hypotheses are stated at
`b`). -/
theorem windowFlux_le_windowMajorant_of_cutMoment_four_le {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h4b : M.cutMoment 4 b ≠ ⊤)
    (hC0 : 0 ≤ C) (hC : ∀ t ∈ Set.Icc a b, |M.coeffRHS t| ≤ C)
    (S : ℕ → Finset (Sym2 M.V)) :
    IsWindowMajorantOn (fun n t => M.windowFlux (S n) t) (M.windowMajorant C b)
      (Set.Ioc a b) :=
  M.windowFlux_le_windowMajorant ha hab
    (fun _ ht => ne_top_of_le_ne_top h4b (M.cutMoment_monotone 4 ht.2)) hC0 hC S

/-! ## 5. Interval integrability of the majorant (second half) -/

/-- **`IntervalIntegrable (M.windowMajorant C b) volume a b`.**

The majorant is the affine function `t ↦ 2 * M.rhsScalarTwo t + 2 * M.windowMajorantConst C b`, so
it suffices that `M.rhsScalarTwo` be interval integrable on `a..b`.  That is the landed
`intervalIntegrable_rhsScalarTwo_of_coeffBound`, whose inputs are exactly the explicit coefficient
bound `|M.coeffRHS t| ≤ C`, `0 ≤ C`, finiteness of the fourth cutoff moment at the right endpoint
`b`, and measurability of `M.rhsScalarTwo` as a function of the radius.  The last is kept as an
explicit hypothesis: it is *not* derivable from tail integrability of `K'`, and in the applications
it is produced from the fixed-radius window-flux convergence as a `liminf`. -/
theorem intervalIntegrable_windowMajorant {a b C : ℝ} (hab : a ≤ b)
    (hmeas : Measurable fun t => M.rhsScalarTwo t)
    (hC0 : 0 ≤ C) (hC : ∀ t ∈ Set.Icc a b, |M.coeffRHS t| ≤ C)
    (h4b : M.cutMoment 4 b ≠ ⊤) :
    IntervalIntegrable (M.windowMajorant C b) volume a b := by
  have hbase : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound hab hmeas hC0 hC h4b
  rw [M.windowMajorant_eq_affine C b]
  exact (hbase.const_mul 2).add
    (intervalIntegrable_const (c := 2 * M.windowMajorantConst C b))

/-! ## 6. The packaged majorant -/

/-- **The uniform-in-radius majorant exists** under the explicit hypotheses
`0 < a ≤ b`, `∀ t ∈ Icc a b, cutMoment 4 t ≠ ⊤`, `0 ≤ C` and `∀ t ∈ Icc a b, |coeffRHS t| ≤ C`:
the window fluxes on `Ioc a b` are dominated by the single radius function
`M.windowMajorant C b`, and that function is interval integrable on `a..b`.

The measurability of `M.rhsScalarTwo` is the only further input, and it is needed only for the
interval integrability half. -/
theorem isWindowFluxMajorant {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmeas : Measurable fun t => M.rhsScalarTwo t)
    (h4 : ∀ t ∈ Set.Icc a b, M.cutMoment 4 t ≠ ⊤)
    (hC0 : 0 ≤ C) (hC : ∀ t ∈ Set.Icc a b, |M.coeffRHS t| ≤ C)
    (S : ℕ → Finset (Sym2 M.V)) :
    M.IsWindowFluxMajorant a b C S :=
  ⟨M.windowFlux_le_windowMajorant ha hab h4 hC0 hC S,
    M.intervalIntegrable_windowMajorant hab hmeas hC0 hC (h4 b ⟨hab, le_rfl⟩)⟩

/-- **The packaged majorant with the fourth cutoff moment assumed finite only at `b`.** -/
theorem isWindowFluxMajorant_of_cutMoment_four_le {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmeas : Measurable fun t => M.rhsScalarTwo t)
    (h4b : M.cutMoment 4 b ≠ ⊤)
    (hC0 : 0 ≤ C) (hC : ∀ t ∈ Set.Icc a b, |M.coeffRHS t| ≤ C)
    (S : ℕ → Finset (Sym2 M.V)) :
    M.IsWindowFluxMajorant a b C S :=
  ⟨M.windowFlux_le_windowMajorant_of_cutMoment_four_le ha hab h4b hC0 hC S,
    M.intervalIntegrable_windowMajorant hab hmeas hC0 hC h4b⟩

/-! ## 7. Interface check: the majorant feeds the landed monotone-free FTC -/

/-- **The monotone-free radius derivative with the majorant hypotheses discharged.**

This is the landed `hasDerivAt_cutMomentReal_two_of_window_majorant` with `G` specialised to
`M.windowMajorant C b`, `hfluxMaj` supplied by `windowFlux_le_windowMajorant` and `hG` by
`intervalIntegrable_windowMajorant`.

What remains an explicit hypothesis is what the majorant does **not** provide:

* `hfluxConv` — the fixed-radius window-flux convergence, here stated at *every* real radius
  because that is the form of the landed FTC (at positive radii it is
  `tendsto_windowFlux_of_cutMoment_four`, under `∀ t > 0, cutMoment 4 t ≠ ⊤`);
* `hmoment` — convergence of the window-moment increments (landed:
  `tendsto_windowMoment_sub`, from finiteness of the second cutoff moment on the window);
* `hrhsCont` — continuity of `rhsScalarTwo` at `r0` (landed off-sphere:
  `continuousAt_rhsScalarTwo_of_no_sphere`).

Note that `hrhsInt` of the landed statement is *not* a hypothesis here: it is
`M.rhsScalarTwo`'s interval integrability on `a..b`, obtained from the same coefficient bound
(`intervalIntegrable_rhsScalarTwo_of_coeffBound`).  This theorem is an interface check for the
majorant; it is not a derivation of the derivative from fixed-radius convergence alone, and the
global-in-radius form of `hfluxConv` here is exactly the part that a local-in-radius assembly
still has to localise. -/
theorem hasDerivAt_cutMomentReal_two_of_majorant {a b r0 C : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    (har : a < r0) (hrb : r0 < b)
    (hmeas : Measurable fun t => M.rhsScalarTwo t)
    (h4 : ∀ t ∈ Set.Icc a b, M.cutMoment 4 t ≠ ⊤)
    (hC0 : 0 ≤ C) (hC : ∀ t ∈ Set.Icc a b, |M.coeffRHS t| ≤ C)
    (hfluxConv : ∀ t : ℝ, Tendsto (fun n => M.windowFlux (S n) t) atTop
      (𝓝 (M.rhsScalarTwo t)))
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have hab : a ≤ b := hwin.2.1
  have ha : 0 < a := hwin.1
  have hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ M.windowMajorant C b t :=
    M.windowFlux_le_windowMajorant ha hab h4 hC0 hC S
  have hG : IntervalIntegrable (M.windowMajorant C b) volume a b :=
    M.intervalIntegrable_windowMajorant hab hmeas hC0 hC (h4 b ⟨hab, le_rfl⟩)
  have hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound hab hmeas hC0 hC (h4 b ⟨hab, le_rfl⟩)
  exact M.hasDerivAt_cutMomentReal_two_of_window_majorant hwin S har hrb hfluxMaj hG
    hfluxConv hmoment hrhsCont hrhsInt

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms cutMassAt_zero_ne_top_of_cutMoment_four
#print axioms pivotalFlux_cutFun_le_integral_envelope
#print axioms abs_cutEdgeDeriv_mul_integral_envelope_nonneg
#print axioms summable_abs_cutEdgeDeriv_mul_integral_envelope
#print axioms tsum_abs_cutEdgeDeriv_mul_integral_envelope_le
#print axioms windowFlux_le_rhsScalarTwo_add_const
#print axioms windowFlux_le_windowMajorant
#print axioms windowFlux_le_windowMajorant_of_cutMoment_four_le
#print axioms intervalIntegrable_windowMajorant
#print axioms isWindowFluxMajorant
#print axioms isWindowFluxMajorant_of_cutMoment_four_le
#print axioms hasDerivAt_cutMomentReal_two_of_majorant

end PercLib.CriticalLRP.Orchestration.SourceModelData
