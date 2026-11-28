/-
Integrated from the independently rebuilt and accepted
`.ultramath/smwyop3kc/m5/LowerTwoPointProvenance.lean` at production base
`c19b8d12524ba2ccffd2551a56478dd83c449aae`.

Provenance of the Case-3 lower two-point input.

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1: Proposition I.4.2 (p. 34), its proof (p. 35-36), Theorem I.2.14 (p. 27),
and (HD) (p. 9).

## The finding

The Case-3 first-moment chain in `PercLib.CriticalLRP.I42C` and in the Case-3 scope wrappers
consumes the pointwise lower bound

  `hlow : ∀ x ≠ 0, c * ‖x‖^{-d+α} ≤ P_{β_c}(0 ↔ x)`

(`VolumeMoments/FirstMoment/Divergence.lean`, `I42C.first_moment_asymptotic_of_rpow_lower`;
`VolumeMoments/HigherMoments/I420Case3/Scope/Main.lean`, three wrappers).  A search of the whole
library finds no provider of that bound: it occurs in `PercLib` only as a hypothesis.  Its
recorded source is the lower half of Theorem I.2.14 (`paper.txt` line 1426), which is *conditional
on `α < 1`*.  Under Case 3 of (HD) (`paper.txt` lines 445-447: `d = 6`, `α = 2`, and only the
*upper* bound `P_{β_c}(x ↔ y) ⪯ (log‖x-y‖)^{-1}‖x-y‖^{-d+2}`) the hypothesis `α < 1` fails, so
`hlow` is not available, and being a two-sided power-law statement it is not implied by (HD)(3):
that hypothesis is compatible with arbitrarily fast decay.  `hlow` is therefore a *missing model
premise* of the Case-3 assembly, not a consequence of the source's Case-3 hypotheses.

What the source actually uses at that point is the weaker statement of divergence of the critical
mean cluster size.  `paper.txt` line 1924 reads "Since `E_{β_c}|K| = ∞`, it follows from Lemma
I.4.5 and (I.4.6) that the identity (I.4.7) holds", i.e. the single input is

  `E_{β_c}|K_0| = ⊤`

which in this library is `∫⁻ ω, clusterVol ω 0 ∂(M.law M.betaCrit) = ⊤`.  That statement is a
classical consequence of criticality for this class of models (asserted, not proved, in the
paper), and it is *weaker* than `hlow`: `hlow` forces it
(`I42C.uncutFirstMoment_eq_top_of_rpow_lower`), but not conversely, since divergence of the mean
cluster size only constrains the sum of `P_{β_c}(0 ↔ x)` and not the decay of a single term.

## What is proved here

1. `criticalDivergence_of_ballLower`: it suffices that the *spatially averaged* two-point
   function has the critical growth along the ball average,
   `c r^α ≤ ∑_{x ∈ B_r} P_{β_c}(0 ↔ x)` eventually, for some `c > 0`.  This is a genuine
   weakening of `hlow` (which implies it by summing the pointwise bound over `B_r`), and it is
   the shape in which a lower bound on the two-point function is actually available in the
   literature: `paper.txt` (p. 27) records that "a matching lower bound on the *spatially
   averaged* two-point function was proven by [20]".  `ballLower_of_pointwise_lower` proves the
   implication `hlow ⇒` averaged bound, so the weakening loses nothing.
2. `first_moment_asymptotic_of_critical_divergence`: the exact conclusion of
   `I42C.first_moment_asymptotic_of_rpow_lower` -- Proposition I.4.2 / (I.4.7) at the cutoff mass
   -- from `E_{β_c}|K_0| = ⊤` instead of `hlow`; and
   `first_moment_asymptotic_of_critical_divergence_of_subcritical`, where the eventual cutoff
   finiteness `hfin` is replaced by finiteness of the subcritical means; and
   `first_moment_asymptotic_of_ballLower`, the composition of items 1 and 2.
3. `case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence`: the full Case-3 Proposition I.4.20
   assembly (`case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux` in the production tree) with
   `hlow` replaced by `E_{β_c}|K_0| = ⊤`.  Compared with the production wrapper the premise
   `hlow` disappears and every other premise is unchanged: the cutoff ODE handoff (`hderiv` and
   `hflux`), the root moment range (`hMa`), the lower comparison `hgm`, the triangle condition
   `hTri` and the two facts about the composite defect (`hmeas`, `h0`) remain explicit.
4. `case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_of_subcritical_second`: the same with
   the second cutoff moment `h2` also *derived*, from finiteness of the subcritical second moment
   (`subcriticalFiniteMean_of_subcritical_second` and
   `SourceModelData.cutMoment_ne_top_of_subcritical`).  The remaining premise is then sharpness of
   the phase transition at order 2, which is where the paper appeals to sharpness
   (`paper.txt` line 2034).

No `sorry`, no `admit`, no custom axioms.  Axiom audit at the end of the file.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Main
public import PercLib.CriticalLRP.MomentMonotonicity.ReducedMomentTransfer
public import PercLib.CriticalLRP.MomentMonotonicity.ReducedCoefficients.Defs

/-! # Critical-mean divergence and the Case-3 lower-bound interface -/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.LowerTwoPoint

open PercLib.CriticalLRP PercLib.CriticalLRP.Orchestration

/-! ## The averaged sufficient condition for `E_{β_c}|K_0| = ⊤` -/

/-- **Divergence of the critical mean cluster size from a spatially averaged lower bound.**

If the ball average `∑_{x ∈ B_r} P_{β_c}(0 ↔ x)` grows like `r^α` along radii tending to infinity,
then the critical first moment `E_{β_c}|K_0| = ∑_x P_{β_c}(0 ↔ x)` is infinite.  No pointwise
lower bound on `P_{β_c}(0 ↔ x)` is used, so this is strictly weaker than the `hlow` hypothesis of
`I42C.first_moment_asymptotic_of_rpow_lower`, and strictly weaker than the paper's Theorem I.2.14
lower half (which additionally needs `α < 1`). -/
theorem criticalDivergence_of_ballLower (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hball : ∀ᶠ r : ℝ in atTop,
      c * r ^ M.α ≤ ∑ x ∈ (BallAverage.ball_finite M r).toFinset, M.twoPoint M.betaCrit 0 x) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit)) = ⊤ := by
  classical
  rw [I42C.lintegral_uncut_clusterVol_eq_tsum]
  have hstep : ∀ r : ℝ, c * r ^ M.α ≤
      ∑ x ∈ (BallAverage.ball_finite M r).toFinset, M.twoPoint M.betaCrit 0 x →
      ENNReal.ofReal (c * r ^ M.α) ≤ ∑' y : M.V, M.twoPointE M.betaCrit 0 y := by
    intro r hr
    have hnn : ∀ x ∈ (BallAverage.ball_finite M r).toFinset,
        0 ≤ M.twoPoint M.betaCrit 0 x := fun x _ => M.twoPoint_nonneg _ _ _
    have h1 : ENNReal.ofReal (c * r ^ M.α)
        ≤ ENNReal.ofReal (∑ x ∈ (BallAverage.ball_finite M r).toFinset,
            M.twoPoint M.betaCrit 0 x) :=
      ENNReal.ofReal_le_ofReal hr
    have h2 : ENNReal.ofReal (∑ x ∈ (BallAverage.ball_finite M r).toFinset,
          M.twoPoint M.betaCrit 0 x)
        = ∑ x ∈ (BallAverage.ball_finite M r).toFinset,
            ENNReal.ofReal (M.twoPoint M.betaCrit 0 x) :=
      ENNReal.ofReal_sum_of_nonneg hnn
    rw [h2] at h1
    refine h1.trans (le_trans (ENNReal.sum_le_tsum _) (ENNReal.tsum_le_tsum fun y => ?_))
    have hE : M.twoPointE M.betaCrit 0 y
        = (M.law M.betaCrit) {ω : Config M.V | Connects ω 0 y} := rfl
    rw [hE, show M.twoPoint M.betaCrit 0 y
        = ((M.law M.betaCrit) {ω : Config M.V | Connects ω 0 y}).toReal from rfl]
    exact ENNReal.ofReal_toReal_le
  have hn : ∀ n : ℕ, (n : ℝ≥0∞) ≤ ∑' y : M.V, M.twoPointE M.betaCrit 0 y := by
    intro n
    have htend : Tendsto (fun r : ℝ => c * r ^ M.α) atTop atTop :=
      Tendsto.const_mul_atTop hc (tendsto_rpow_atTop M.hα)
    have hev1 : ∀ᶠ r : ℝ in atTop, (n : ℝ) ≤ c * r ^ M.α :=
      htend.eventually (eventually_ge_atTop (n : ℝ))
    obtain ⟨r, hr1, hr2⟩ := (hev1.and hball).exists
    calc (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by simp
      _ ≤ ENNReal.ofReal (c * r ^ M.α) := ENNReal.ofReal_le_ofReal hr1
      _ ≤ ∑' y : M.V, M.twoPointE M.betaCrit 0 y := hstep r hr2
  rw [eq_top_iff, ← ENNReal.iSup_natCast]
  exact iSup_le hn

/-! ## (I.4.7) from divergence of the critical mean cluster size -/

/-- **Proposition I.4.2 / display (I.4.7) at the cutoff mass, from `E_{β_c}|K_0| = ⊤`.**

Same conclusion as `I42C.first_moment_asymptotic_of_rpow_lower`, but with the pointwise lower
two-point bound `hlow` replaced by the paper's own input at `paper.txt` line 1924,
`E_{β_c}|K| = ∞`.  The analytic ODE package (`hderiv`, `hpos`, `hode`, `hmeas`, `hC`, `h0`),
the positivity of `β_c` and the eventual finiteness `hfin` are unchanged.  `hlow` is *not*
recovered: it is strictly stronger, and unavailable in Case 3 of (HD) where `α = 2 > 1`. -/
theorem first_moment_asymptotic_of_critical_divergence (M : SourceModelData)
    {f' h : ℝ → ℝ} {C r₀ : ℝ}
    (htop : M.uncutMean M.betaCrit = ⊤)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t : ℝ, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t : ℝ, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t : ℝ, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1) :=
  VolumeMoments.FirstMoment.first_moment_asymptotic hβ M.hα hr₀ hderiv hpos
    (I42C.tendsto_cutMassAt_toReal_atTop M (I42C.tendsto_cutMassAt_atTop_nhds_top M htop) hfin)
    hode hmeas hC h0

/-- **`(I.4.7)` from the spatially averaged lower bound alone.**

Composition of `criticalDivergence_of_ballLower` with
`first_moment_asymptotic_of_critical_divergence`: the pointwise two-point lower bound `hlow`
is replaced by the averaged growth of `∑_{x ∈ B_r} P_{β_c}(0 ↔ x)`. -/
theorem first_moment_asymptotic_of_ballLower (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hball : ∀ᶠ r : ℝ in atTop,
      c * r ^ M.α ≤ ∑ x ∈ (BallAverage.ball_finite M r).toFinset, M.twoPoint M.betaCrit 0 x)
    {f' h : ℝ → ℝ} {C r₀ : ℝ}
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t : ℝ, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t : ℝ, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t : ℝ, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1) :=
  first_moment_asymptotic_of_critical_divergence M
    (criticalDivergence_of_ballLower M hc hball) hfin hβ hr₀ hderiv hpos hode hmeas hC h0

/-- **The same, with the eventual cutoff finiteness `hfin` derived from finiteness of the
subcritical means.**  This is the shape recorded in
`MomentMonotonicity/ReducedMomentTransfer.lean`: `hfin` is not an extra source premise but a
consequence of `χ(β) < ∞` for `β < β_c`, together with the subcritical domination of the
range-truncated law. -/
theorem first_moment_asymptotic_of_critical_divergence_of_subcritical (M : SourceModelData)
    {f' h : ℝ → ℝ} {C r₀ : ℝ}
    (htop : M.uncutMean M.betaCrit = ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hsub : M.SubcriticalFiniteMean)
    (hr₀ : 0 < r₀)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t : ℝ, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t : ℝ, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t : ℝ, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1) :=
  VolumeMoments.FirstMoment.first_moment_asymptotic hβ M.hα hr₀ hderiv hpos
    (Orchestration.tendsto_cutMassAt_toReal_atTop_of_subcritical M hβ hsub htop)
    hode hmeas hC h0

/-! ## The Case-3 assembly with `hlow` replaced by `E_{β_c}|K_0| = ⊤` -/

/-- **Case 3 of Proposition I.4.20 at the actual source balls, with the lower two-point bound
`hlow` replaced by the paper's own divergence input.**

This is `case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux` of
`VolumeMoments/HigherMoments/I420Case3/Scope/Main.lean` with the pointwise lower bound
`hlow` removed.  What remains is exactly the flux form of the Case-3 hypotheses:

* `hHD3` — Case 3 of (HD) (`paper.txt` p. 9), used only for the triangle tail
  (`Lemma I.4.3`) and to record the regime;
* `htop` — `E_{β_c}|K_0| = ⊤` (`paper.txt` line 1924), replacing `hlow`;
* `hTri` — the triangle condition `∇_{β_c} < ⊤`. The newer `TriangleFromHD`
  package derives it from `hHD3`; it remains explicit in this older wrapper's signature.
* `h2` — finiteness of the second cutoff moment, whence the cutoff mass is finite and positive;
* `hderiv`/`hflux` — the differentiation of the cutoff mass and the identification of its
  derivative with the model's defect (the `(I.4.6)` handoff);
* `hmeas`/`h0` — measurability and vanishing of the composite defect `cutError`;
* `𝓔, h𝓔mono, h𝓔, p, hp, θ` — the tangent/net and order data of `(I.4.19)`;
* `hMa` — root moment finiteness up to order `p+1`;
* `hgm` — the lower comparison `E|K|^2 ⪰ (E|K|)^3` of Proposition I.4.15;
* `hβ`, `hr₀` — the model constants.

In particular no hypothesis on the pointwise decay of `P_{β_c}(0 ↔ x)` survives. -/
theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {F' : ℝ → ℝ} {r₀ : ℝ}
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (F' t) t)
    (hflux : ∀ t : ℝ, r₀ ≤ t →
      F' t = (M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal)
    (hmeas : Measurable (I420Case3.cutError M))
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  -- the uniform bound on the multiplicative error, after shifting the base point
  have hbdd : ∀ᶠ t : ℝ in atTop, |I420Case3.cutError M t| ≤ 1 := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h0) 1 zero_lt_one
    filter_upwards [eventually_ge_atTop N] with t ht
    have h := hN t ht
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt h
  obtain ⟨R, hR⟩ := eventually_atTop.1 hbdd
  have hr₀' : 0 < max r₀ R := lt_of_lt_of_le hr₀ (le_max_left _ _)
  -- the cutoff mass is positive and finite on the tail, from the second moment
  have h2' : ∀ t : ℝ, max r₀ R ≤ t → M.cutMoment 2 t ≠ ⊤ := fun t ht =>
    h2 t (le_trans (le_max_left _ _) ht)
  have hfinA : ∀ t : ℝ, max r₀ R ≤ t → M.cutMassAt t 0 ≠ ⊤ := fun t ht =>
    ne_top_of_le_ne_top (h2 t (le_trans (le_max_left _ _) ht))
      (E1Sign.cutMassAt_le_cutMoment_two M t)
  have hpos : ∀ t : ℝ, max r₀ R ≤ t → 0 < (M.cutMassAt t 0).toReal := by
    intro t ht
    have h1 : (1 : ℝ) ≤ (M.cutMassAt t 0).toReal := by
      have h := ENNReal.toReal_mono (hfinA t ht) (E1Sign.one_le_cutMassAt M t)
      simpa using h
    linarith
  -- the ODE `(I.4.6)` written with the composite defect
  have hode : ∀ t : ℝ, max r₀ R ≤ t →
      F' t = (M.betaCrit : ℝ) * (1 - I420Case3.cutError M t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2 := by
    intro t ht
    have h := PivotFlux.cutMass_ODE_of_flux M hr₀' h2'
      (fun s hs => hflux s (le_trans (le_max_left _ _) hs)) t ht
    rw [h, I420Case3.cutError]
    ring
  refine I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite M ?_ hTri 𝓔 h𝓔mono h𝓔 p hp
    hθ0 hθ1 (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2 hMa hc3 hgm
  refine first_moment_asymptotic_of_critical_divergence M htop ?_ hβ hr₀'
    (fun t ht => hderiv t (le_trans (le_max_left _ _) ht)) hpos hode hmeas
    (fun t ht => hR t (le_trans (le_max_right _ _) ht)) h0
  exact Filter.eventually_atTop.2 ⟨max r₀ R, hfinA⟩

/-! ## The abstract-ODE form of the Case-3 assembly -/

/-- **Case 3 of Proposition I.4.20 from the paper's divergence input, with the ODE package kept
abstract.**  This is `case3_hAend_hAmid_cutPoly_source_of_HD_case3` with `hlow` (and the two
constants `c`, `hαd`) replaced by `E_{β_c}|K_0| = ⊤`.  The data `hderiv`, `hpos`, `hode`,
`hmeas`, `hhedge`, `h0` are the abstract `(I.4.6)` handoff; `hfin` is the eventual cutoff
finiteness (derivable from the second cutoff moment, as in the flux wrapper below). -/
theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_of_critical_divergence
    (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {f' h : ℝ → ℝ} {C r₀ : ℝ}
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t : ℝ, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t : ℝ, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t : ℝ, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) :=
  I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite M
    (first_moment_asymptotic_of_critical_divergence M htop hfin hβ hr₀ hderiv hpos hode
      hmeas hhedge h0)
    hTri 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2 hMa hc3 hgm

/-! ## The normalized `(I.4.21)` consumer -/

/-- **The normalized `(I.4.21)` form of Case 3 at the actual source balls, from
`E_{β_c}|K_0| = ⊤`.**  This is `case3_i421_cutPoly_source_of_HD_case3` of the production tree
with `hlow` (and `c`, `hαd`) replaced by the paper's divergence input.  The root moment range
`hmom` is unchanged. -/
theorem case3_i421_cutPoly_source_of_HD_case3_of_critical_divergence
    (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {f' h : ℝ → ℝ} {C r₀ : ℝ}
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t : ℝ, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t : ℝ, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t : ℝ, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p) (hℓ : ℓ + 1 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hmom : ∀ r : ℝ, 1 ≤ r → ∀ m : ℕ, 1 ≤ m → m ≤ p + 1 →
      I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      Tendsto (fun r => I420Case3.discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        I420Case3.biasTarget (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) := by
  have hMa : ∀ r : ℝ, 1 ≤ r →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤ :=
    fun r hr => hmom r hr (ℓ + 1) (by omega) (by omega)
  have hMb : ∀ (r : ℝ), 1 ≤ r → ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
      I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤ := by
    intro r hr y _
    rw [I420Case3.powMomentAt_cutProb_apply_eq_zero M r (p - ℓ) y]
    have hidx : p - ℓ - 1 + 1 = p - ℓ := by omega
    rw [← hidx]
    exact hmom r hr (p - ℓ - 1 + 1) (by omega) (by omega)
  exact I420Case3.exists_case3_i421_cutPoly_source M
    (first_moment_asymptotic_of_critical_divergence M htop hfin hβ hr₀ hderiv hpos hode
      hmeas hhedge h0)
    hTri 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2
    hMa hMb hc3 hgm

/-! ## The flux form with the second cutoff moment derived from sharpness -/

/-- **Finiteness of the subcritical second moment gives the subcritical first-moment
finiteness `SubcriticalFiniteMean`** (`|K_0| ≥ 1`, so `|K_0| ≤ |K_0|²`). -/
theorem subcriticalFiniteMean_of_subcritical_second (M : SourceModelData)
    (hsub2 : ∀ β : ℝ≥0, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 ∂(M.law β)) ≠ ⊤) :
    M.SubcriticalFiniteMean := by
  intro β hβ
  refine ne_top_of_le_ne_top (hsub2 β hβ) ?_
  refine lintegral_mono (g := fun ω => clusterVol ω (0 : M.V) ^ 2) (fun ω => ?_)
  exact le_self_pow (SourceModelData.one_le_clusterVol ω (0 : M.V)) (by norm_num : 2 ≠ 0)

/-- **The flux form of the Case-3 assembly with the *second cutoff moment* `h2` also derived.**

Compared with `case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence` the hypothesis `h2`
(second cutoff moment finite for all large radii) is replaced by finiteness of the *subcritical*
second moment, i.e. sharpness of the phase transition at second order
(`paper.txt:2034`).  Production derives `E_{β_c,r}|K_0| < ∞` and `E_{β_c,r}|K_0|² < ∞` from a
strictly subcritical intensity through Definition I.1.5
(`SourceModelData.cutMoment_ne_top_of_subcritical`); that is used here. -/
theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_of_subcritical_second
    (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (hsub2 : ∀ β : ℝ≥0, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 ∂(M.law β)) ≠ ⊤)
    {F' : ℝ → ℝ} {r₀ : ℝ}
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (F' t) t)
    (hflux : ∀ t : ℝ, r₀ ≤ t →
      F' t = (M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal)
    (hmeas : Measurable (I420Case3.cutError M))
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  have hβ0 : (0 : ℝ≥0) < M.betaCrit := by exact_mod_cast hβ
  have hsub1 : M.SubcriticalFiniteMean :=
    subcriticalFiniteMean_of_subcritical_second M hsub2
  -- the second cutoff moment is finite at every positive radius
  have h2all : ∀ t : ℝ, 0 < t → M.cutMoment 2 t ≠ ⊤ := fun t ht =>
    M.cutMoment_ne_top_of_subcritical 2 hβ0 hsub2 ht
  have hbdd : ∀ᶠ t : ℝ in atTop, |I420Case3.cutError M t| ≤ 1 := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h0) 1 zero_lt_one
    filter_upwards [eventually_ge_atTop N] with t ht
    have h := hN t ht
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt h
  obtain ⟨R, hR⟩ := eventually_atTop.1 hbdd
  have hr₀' : 0 < max r₀ R := lt_of_lt_of_le hr₀ (le_max_left _ _)
  have hfinA : ∀ t : ℝ, max r₀ R ≤ t → M.cutMassAt t 0 ≠ ⊤ := fun t ht =>
    ne_top_of_le_ne_top (h2all t (lt_of_lt_of_le hr₀' ht))
      (E1Sign.cutMassAt_le_cutMoment_two M t)
  have hpos : ∀ t : ℝ, max r₀ R ≤ t → 0 < (M.cutMassAt t 0).toReal := by
    intro t ht
    have h1 : (1 : ℝ) ≤ (M.cutMassAt t 0).toReal := by
      have h := ENNReal.toReal_mono (hfinA t ht) (E1Sign.one_le_cutMassAt M t)
      simpa using h
    linarith
  have hode : ∀ t : ℝ, max r₀ R ≤ t →
      F' t = (M.betaCrit : ℝ) * (1 - I420Case3.cutError M t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2 := by
    intro t ht
    have h := PivotFlux.cutMass_ODE_of_flux M hr₀'
      (fun s hs => h2all s (lt_of_lt_of_le hr₀' hs))
      (fun s hs => hflux s (le_trans (le_max_left _ _) hs)) t ht
    rw [h, I420Case3.cutError]
    ring
  refine I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite M ?_ hTri 𝓔 h𝓔mono h𝓔 p hp
    hθ0 hθ1 (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2 hMa hc3 hgm
  exact first_moment_asymptotic_of_critical_divergence_of_subcritical M htop hβ hsub1 hr₀'
    (fun t ht => hderiv t (le_trans (le_max_left _ _) ht)) hpos hode hmeas
    (fun t ht => hR t (le_trans (le_max_right _ _) ht)) h0

/-! ## The averaged hypothesis is implied by the pointwise one -/

/-- **`hlow` implies the ball-averaged lower bound** used in `criticalDivergence_of_ballLower`,
with the constant `c / 2^{d+1}`.

Summing the pointwise bound `c ‖x‖^{-d+α} ≤ P_{β_c}(0 ↔ x)` over the ball `B_r` and using
`|B_r| ⪰ r^d` (Lemma I.4.6) gives `c 2^{-(d+1)} r^α ≤ ∑_{x ∈ B_r} P_{β_c}(0 ↔ x)`.  This shows
that the hypothesis of `criticalDivergence_of_ballLower` is implied by the hypothesis `hlow` of
`I42C.first_moment_asymptotic_of_rpow_lower`, so nothing is lost in passing to the averaged
form; the converse fails in general, since a ball sum constrains only the aggregate. -/
theorem ballLower_of_pointwise_lower (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x) :
    ∀ᶠ r : ℝ in atTop, c / 2 ^ (M.d + 1) * r ^ M.α ≤
      ∑ x ∈ (BallAverage.ball_finite M r).toFinset, M.twoPoint M.betaCrit 0 x := by
  classical
  obtain ⟨C, hC⟩ := BallAverage.exists_cube_bound M
  have hC0 : 0 ≤ C := BallAverage.cube_bound_nonneg M hC
  have hexp : (-(M.d : ℝ) + M.α) ≤ 0 := by
    have : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
    linarith
  filter_upwards [eventually_ge_atTop (max (2 * C) 4)] with r hr
  have hr4 : 4 ≤ r := le_trans (le_max_right _ _) hr
  have hr2C : 2 * C ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : 0 < r := by linarith
  have hBfin : (M.ball r).Finite := BallAverage.ball_finite M r
  set s : Finset M.V := hBfin.toFinset.erase 0 with hs
  have h0mem : (0 : M.V) ∈ hBfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    change M.S.ρ (toVec (0 : M.V)) ≤ r
    have hz : toVec (0 : M.V) = 0 := by funext i; simp [Orchestration.toVec]
    rw [hz, M.S.ρ_zero]
    exact hr0.le
  have hcardeq : (s.card : ℝ) = ((M.ball r).ncard : ℝ) - 1 := by
    have h1 : s.card = hBfin.toFinset.card - 1 := Finset.card_erase_of_mem h0mem
    have h2 : (hBfin.toFinset.card : ℝ) = ((M.ball r).ncard : ℝ) := by
      rw [← Set.ncard_eq_toFinset_card (M.ball r) hBfin]
    have h3 : (1 : ℕ) ≤ hBfin.toFinset.card := Finset.card_pos.mpr ⟨0, h0mem⟩
    rw [h1, Nat.cast_sub h3, h2]
    norm_num
  have hcard : (r / 2) ^ M.d / 2 ≤ (s.card : ℝ) := by
    have hge := BallAverage.ball_ncard_ge M hC hC0 (r := r) (by linarith : C < r)
    have h1 : r / 2 ≤ r - C := by linarith
    have h2 : (r / 2) ^ M.d ≤ (r - C) ^ M.d :=
      pow_le_pow_left₀ (by linarith) h1 M.d
    have h3 : (2 : ℝ) ≤ (r / 2) ^ M.d := by
      have h2le : (2 : ℝ) ≤ r / 2 := by linarith
      calc (2 : ℝ) ≤ r / 2 := h2le
        _ = (r / 2) ^ 1 := (pow_one _).symm
        _ ≤ (r / 2) ^ M.d := pow_le_pow_right₀ (by linarith) M.hd
    rw [hcardeq]
    linarith
  have hterm : ∀ x ∈ s, c * r ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x := by
    intro x hx
    have hxmem : x ∈ M.ball r := by
      rw [← Set.Finite.mem_toFinset hBfin]
      exact Finset.mem_of_mem_erase hx
    have hxne : x ≠ 0 := Finset.ne_of_mem_erase hx
    have hdist : M.S.dist 0 x = M.S.ρ (toVec x) := by
      rw [Orchestration.SourceNormData.dist]
      have hsub : toVec ((0 : M.V) - x) = -(toVec x) := by
        rw [Orchestration.toVec_sub]
        have : toVec (0 : M.V) = 0 := by funext i; simp [Orchestration.toVec]
        rw [this, zero_sub]
      rw [hsub, M.S.ρ_neg]
    have hle : M.S.dist 0 x ≤ r := by
      rw [hdist]
      exact hxmem
    have hpos : 0 < M.S.dist 0 x :=
      Orchestration.SourceNormData.dist_pos M.S (x := (0 : M.V)) (y := x) (Ne.symm hxne)
    have hrpow : r ^ (-(M.d : ℝ) + M.α) ≤ (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) :=
      Real.rpow_le_rpow_of_nonpos hpos hle hexp
    exact le_trans (mul_le_mul_of_nonneg_left hrpow hc.le) (hlow x hxne)
  -- collect the sum bounds
  have hfac : 0 ≤ c * r ^ (-(M.d : ℝ) + M.α) :=
    mul_nonneg hc.le (Real.rpow_nonneg hr0.le _)
  have hsum1 : (s.card : ℝ) * (c * r ^ (-(M.d : ℝ) + M.α))
      ≤ ∑ x ∈ s, M.twoPoint M.betaCrit 0 x := by
    have h := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hcard' : c * r ^ (-(M.d : ℝ) + M.α) * (r / 2) ^ M.d / 2
      ≤ ∑ x ∈ s, M.twoPoint M.betaCrit 0 x := by
    have hmul := mul_le_mul_of_nonneg_left hcard hfac
    -- `hmul : (c * r ^ …) * ((r/2)^d / 2) ≤ (c * r ^ …) * (s.card : ℝ)`
    calc c * r ^ (-(M.d : ℝ) + M.α) * (r / 2) ^ M.d / 2
        = (c * r ^ (-(M.d : ℝ) + M.α)) * ((r / 2) ^ M.d / 2) := by ring
      _ ≤ (c * r ^ (-(M.d : ℝ) + M.α)) * (s.card : ℝ) := hmul
      _ = (s.card : ℝ) * (c * r ^ (-(M.d : ℝ) + M.α)) := by ring
      _ ≤ ∑ x ∈ s, M.twoPoint M.betaCrit 0 x := hsum1
  have harith : c / 2 ^ (M.d + 1) * r ^ M.α
      = c * r ^ (-(M.d : ℝ) + M.α) * (r / 2) ^ M.d / 2 := by
    have h1 : (r / 2) ^ M.d = r ^ M.d / 2 ^ M.d := div_pow r 2 M.d
    have h2 : r ^ (-(M.d : ℝ) + M.α) * r ^ M.d = r ^ M.α := by
      rw [← Real.rpow_natCast (x := r) (n := M.d), ← Real.rpow_add hr0]
      congr 1
      ring
    have h3 : (2 : ℝ) ^ (M.d + 1) = 2 ^ M.d * 2 := by
      rw [pow_succ]
    have hpos2 : (0 : ℝ) < 2 ^ M.d := by positivity
    rw [h1, h3]
    field_simp
    nlinarith [h2]
  rw [harith]
  refine le_trans hcard' ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun x _ _ => M.twoPoint_nonneg _ _ _)

/-! ## Axiom audit -/

#print axioms criticalDivergence_of_ballLower
#print axioms ballLower_of_pointwise_lower
#print axioms first_moment_asymptotic_of_critical_divergence
#print axioms first_moment_asymptotic_of_ballLower
#print axioms first_moment_asymptotic_of_critical_divergence_of_subcritical
#print axioms case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence
#print axioms subcriticalFiniteMean_of_subcritical_second
#print axioms case3_hAend_hAmid_cutPoly_source_of_HD_case3_divergence_of_subcritical_second
#print axioms case3_hAend_hAmid_cutPoly_source_of_HD_case3_of_critical_divergence
#print axioms case3_i421_cutPoly_source_of_HD_case3_of_critical_divergence

end PercLib.CriticalLRP.LowerTwoPoint
