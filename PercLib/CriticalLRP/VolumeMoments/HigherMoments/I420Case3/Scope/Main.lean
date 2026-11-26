/- Integrated from independently verified `.ultramath/smwxyesaw/m2/Scope.lean`
at production base `6eb8b0b660d7d9049a9fc25c7424bf10dbd723f6`. -/
module

/-
Scope audit for Case 3 of Proposition I.4.20: the two *source* premises `hP`
(first-moment asymptotic) and `hTail` (vanishing triangle tail) of
`case3_hAend_hAmid_cutPoly_source_of_finite` are discharged by existing
declarations of the read-only worktree,

* `PercLib.CriticalLRP.I42C.first_moment_asymptotic_of_rpow_lower` (Prop I.4.2,
  Case 3, with the divergence of Theorem I.2.14 already discharged), and
* `SourceModelData.isLogErrorFunction_nablaTail_of_HD_case2_or_case3`
  (Lemma I.4.3, third disjunct), whose second component is literally `hTail`.

Three levels are recorded:

* `case3_hAend_hAmid_cutPoly_source_of_HD_case3` — `hP` via the shipped Case-3
  first-moment theorem verbatim.
* `case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux` — the same, but the
  multiplier of `(I.4.6)` is *identified* with the model's own defect
  `1 - (1 - E₀)(1 - E₁)` through `PivotFlux.cutMass_ODE_of_flux`, and the
  positivity / finiteness / uniform-bound hypotheses of the shipped theorem are
  derived rather than assumed.  What is left is the analytic handoff
  `HasDerivAt` + flux identity, the second cutoff moment, the lower two-point
  bound, and the two facts about the composite defect (measurability, vanishing).
* `case3_i421_cutPoly_source_of_HD_case3` — the normalized `(I.4.21)` form, with
  the window moment finiteness discharged by translation invariance
  (`powMomentAt_cutProb_apply_eq_zero`), as in `SplitPolygon.MomentHom`.
-/
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.MomentHom
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.Divergence
public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case23
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.CornerSafe
public import PercLib.CriticalLRP.Analysis.TriTailSqrt
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Defs

/-! # Case-3 first-moment and HD-tail scope wrappers -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- **Case 3 of Proposition I.4.20 on actual source balls, with the first moment and
the triangle tail supplied by the shipped Case-3 theorems.**

`hP` is `I42C.first_moment_asymptotic_of_rpow_lower` and `hTail` is the second
component of `isLogErrorFunction_nablaTail_of_HD_case2_or_case3` under `(HD)(3)`.

The remaining hypotheses are exactly: `(HD)(3)`; finiteness of the open triangle;
the Case-3 first-moment ODE package at the cutoff mass; the tangent `𝓔`, the scale
`θ` and the order `p`; the root moment finiteness `hMa` up to order `p+1`; and the
`E|K|² ⪰ (E|K|)³` lower comparison `hgm` of Proposition I.4.15. -/
theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3 (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) :=
  case3_hAend_hAmid_cutPoly_source_of_finite M
    (I42C.first_moment_asymptotic_of_rpow_lower M hc hαd hlow hfin hβ hr₀ hderiv
      hpos hode hmeas hhedge h0)
    hTri 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2
    hMa hc3 hgm

#print axioms case3_hAend_hAmid_cutPoly_source_of_HD_case3

/-- **The triangle condition at the model from Kozma's `ℓ²` square root.**

The only way the worktree produces `∇_{β_c} = ∇_{β_c}(0,0) < ∞` is
`TriTail.openTriangleSelf_lt_top_of_sqrtKernel`: from a vector `ξ` whose autocorrelation
is the open triangle.  This is the exact minimal shipped obligation behind `hTri`; it is
*not* implied by `(HD)(3)` in the shipped library. -/
theorem openTriangleSelf_lt_top_of_source_sqrt (M : SourceModelData) {ξ : M.V → ℝ}
    (hfac : ∀ x : M.V, TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 x
      = ENNReal.ofReal (∑' y : M.V, ξ y * ξ (y - x))) :
    TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ :=
  TriTail.openTriangleSelf_lt_top_of_sqrtKernel (J := M.kernel) (hJ := M.kernel_nonneg)
    (β := M.betaCrit) hfac

#print axioms openTriangleSelf_lt_top_of_source_sqrt

/-- **The same Case-3 conclusion with `(I.4.6)` written in the model's own defect.**

Compared with `case3_hAend_hAmid_cutPoly_source_of_HD_case3`, the multiplier of the
first-moment ODE is no longer an abstract error function: it is `1 - cutError`, the
defect produced by `PivotFlux.cutMass_ODE_of_flux` from the flux identity.  The
positivity of the cutoff mass, its finiteness and the uniform bound on the error are
*derived* here (finiteness and positivity from the second cutoff moment, the bound by
shifting `r₀` past the point where `|cutError| ≤ 1`).  What remains is the analytic
handoff `hderiv` + `hflux` (the differentiation of the cutoff mass and its
derivative-to-flux identity), the second cutoff moment `h2`, the lower two-point
bound `hlow`, and the two facts about `cutError`: measurability and vanishing. -/
theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {F' : ℝ → ℝ} {c r₀ : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (F' t) t)
    (hflux : ∀ t : ℝ, r₀ ≤ t →
      F' t = (M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal)
    (hmeas : Measurable (cutError M))
    (h0 : Tendsto (cutError M) atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  -- the uniform bound on the multiplicative error, after shifting the base point
  have hbdd : ∀ᶠ t : ℝ in atTop, |cutError M t| ≤ 1 := by
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
  refine case3_hAend_hAmid_cutPoly_source_of_HD_case3 M hHD3 hTri hc hαd hlow ?_ hβ hr₀'
    (fun t ht => hderiv t (le_trans (le_max_left _ _) ht)) hpos ?_
    hmeas (fun t ht => hR t (le_trans (le_max_right _ _) ht)) h0 𝓔 h𝓔mono h𝓔 p hp
    hθ0 hθ1 hMa hc3 hgm
  · filter_upwards [eventually_ge_atTop (max r₀ R)] with t ht using hfinA t ht
  · intro t ht
    have hode := PivotFlux.cutMass_ODE_of_flux M hr₀' h2'
      (fun s hs => hflux s (le_trans (le_max_left _ _) hs)) t ht
    have h1 : (1 : ℝ) - (1 - (1 - PivotFlux.cutE0 M t) * (1 - PivotFlux.cutE1 M t))
        = (1 - PivotFlux.cutE0 M t) * (1 - PivotFlux.cutE1 M t) := by ring
    rw [cutError]
    rw [hode, h1]
    ring

/-- **The normalized `(I.4.21)` form of Case 3 at the actual source balls.**

Both source premises are discharged as in
`case3_hAend_hAmid_cutPoly_source_of_HD_case3`, and the windowed moment finiteness
`hMb` of `exists_case3_i421_cutPoly_source` is discharged by translation invariance
of the cutoff cluster moments (`powMomentAt_cutProb_apply_eq_zero`), so a single
uniform range of exponents `m = 1, …, p+1` of root moments is the only moment input. -/
theorem case3_i421_cutPoly_source_of_HD_case3 (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p) (hℓ : ℓ + 1 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hmom : ∀ r : ℝ, 1 ≤ r → ∀ m : ℕ, 1 ≤ m → m ≤ p + 1 →
      I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) := by
  have hMa : ∀ r : ℝ, 1 ≤ r →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤ :=
    fun r hr => hmom r hr (ℓ + 1) (by omega) (by omega)
  have hMb : ∀ (r : ℝ), 1 ≤ r → ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
      I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤ := by
    intro r hr y _
    rw [powMomentAt_cutProb_apply_eq_zero M r (p - ℓ) y]
    have hidx : p - ℓ - 1 + 1 = p - ℓ := by omega
    rw [← hidx]
    exact hmom r hr (p - ℓ - 1 + 1) (by omega) (by omega)
  exact exists_case3_i421_cutPoly_source M
    (I42C.first_moment_asymptotic_of_rpow_lower M hc hαd hlow hfin hβ hr₀ hderiv
      hpos hode hmeas hhedge h0)
    hTri 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2
    hMa hMb hc3 hgm

/-- **The vanishing of the multiplicative error of `(I.4.6)` at the actual model**,
from the shipped vanishing of the standardization error (`PivotFlux.tendsto_cutE0`) and
the vanishing of the truncated-law defect.  Every consumer of
`first_moment_asymptotic_of_rpow_lower` at the model can take its `h0` from here; the
only remaining route to `cutE1 → 0` shipped in the worktree is
`CutoffDefect.cutE1_tendsto_zero_of_triangleCondition` (triangle condition plus the
sup-form tail limit). -/
theorem tendsto_cutError_of_tendsto_cutE1 (M : SourceModelData)
    (hE1 : Tendsto (fun r => PivotFlux.cutE1 M r) atTop (𝓝 0)) :
    Tendsto (cutError M) atTop (𝓝 0) :=
  CornerSafe.tendsto_one_sub_mul (PivotFlux.tendsto_cutE0 M) hE1

#print axioms tendsto_cutError_of_tendsto_cutE1

#print axioms case3_i421_cutPoly_source_of_HD_case3

#print axioms case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux

end I420Case3

end PercLib.CriticalLRP
