module
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SecondMomentFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.ScalarFactor.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusPivotalWeight
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusTailDeriv

/-!
# Summed singleton flux: closed form, and `hGcont` from scalar continuity

The endpoint derivative theorems of `OffCorner/RadiusMeasurability/Main` and
`OffCorner/RadiusPivotalWeight` carry the summed-flux continuity

`hGcont : ∀ r ∈ Ioo α β, ContinuousAt (fun r' => ∑' y, sMomentInfFlux 0 {y} 1 … r') r`

as a premise alongside the per-vertex continuity `hcontinf`.  The point of this file is that
`hGcont` is *not* an independent analytic input: the total vertex sum has a **closed form**.

`tsum_sMomentInfFlux_eq_rhsScalar` reads the landed identity
`tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass_of_cutMoment_two` (`SecondMomentFlux`) as

`∑'_y sMomentInfFlux 0 {y} 1 r = M.rhsScalar r`,
`M.rhsScalar r = β_c (-K'(r)) (exclMass r).toReal`,

at every off-corner radius `r > 0` with a finite second cutoff moment.  The identity is local in
the radius: non-attained radii have a corner-free neighbourhood
(`exists_nhds_notMem_attainedRadii`)
and `cutMoment 2` is finite below `β` once it is finite at `β` (`cutMoment_ne_top_of_le`).
Consequently `hGcont` is exactly the scalar continuity of `M.rhsScalar`, hence — through
`continuousAt_rhsScalar_iff` — exactly the continuity of `r ↦ (exclMass r).toReal` at points with
`K'(r) ≠ 0`:

* `continuousAt_tsum_sMomentInfFlux_of_continuousAt_rhsScalar` — the usable direction;
* `continuousAt_tsum_sMomentInfFlux_iff_continuousAt_exclScalar` — sharpness: on the window the
  two statements are equivalent, so summed-flux continuity is neither weaker nor stronger than
  excluded-mass continuity;
* `hGcont_of_rhsScalar`, `hGcont_of_scalar_continuity` — the premise `hGcont` in its exact
  consumed shape, derived;
* `hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_scalar` and
  `…_of_measurability_of_scalar` — the two landed endpoint theorems with `hGcont` **deleted** and
  replaced by continuity of `deriv M.K` and of `exclScalar` on the window;
* `abs_tsum_sMomentInfFlux_le_of_window` — the whole infinite vertex sum is bounded on a radius
  window by the endpoint second moment and a bound on `|K'|`.

## 5. Where the remaining scalar input actually sits

The excluded mass carries the moving window `B_r` in its integrand; the landed
`CutoffMomentContinuity` header names that moving window as the obstruction.  Off the corner it
is not: `ballF_eq_of_offCorner_window` shows `B_r = B_{r₀}` for every `r` in a corner-free
neighbourhood of `r₀`, and `continuousAt_exclScalar_iff_frozenWindow` consequently identifies
`(exclMass r).toReal` with a **fixed** integrand against the varying law,

`r ↦ (∫⁻ ω, |K_0| ∑_{y ∈ B_{r₀}} 1(y ∉ K_0) |K_y| ∂(cutLaw r)).toReal`.

So the missing analytic input is the continuity of one frozen-window moment in the cutoff law —
not an annulus estimate.  `hGcont_of_frozenWindow` and
`hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_frozenWindow` consume exactly this
datum; `hcontinf` remains an input in every statement.

What is *not* claimed: no joint-uniform estimate `∑'_y sup_{r∈window} |flux_y r| < ∞` is proved,
used, or needed — the total sum never has to be differentiated termwise.  No continuity of the
excluded mass, of `deriv M.K`, or of the frozen-window moment is proved here; the per-vertex
continuity `hcontinf` also stays an input.  These are genuine hypotheses, and the equivalence
above shows `hGcont` cannot be obtained without a scalar-regularity input of the same strength.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The total vertex sum in closed form -/

/-- **The summed singleton flux is the scalar factor `β_c (-K'(r)) (exclMass r).toReal`.**
The landed `SecondMomentFlux` identity, read in the vocabulary `rhsScalar = coeffRHS ·
exclScalar` of `OffCorner/ScalarFactor/Defs`.  No per-vertex continuity and no uniform
convergence is involved. -/
theorem tsum_sMomentInfFlux_eq_rhsScalar {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) = M.rhsScalar r := by
  rw [M.tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass_of_cutMoment_two hr hoff h2, rhsScalar,
    coeffRHS, exclScalar]

/-- The closed form on an off-corner radius window, from the second cutoff moment at the outer
endpoint only.  This is the equality behind every continuity statement below. -/
theorem tsum_sMomentInfFlux_eq_rhsScalar_on_window {α β : ℝ} (hα0 : 0 < α)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii) (h2β : M.cutMoment 2 β ≠ ⊤) :
    ∀ r ∈ Set.Ioo α β,
      (∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) = M.rhsScalar r := by
  intro r hr
  have hoff' : r ∉ M.attainedRadii := by
    rw [M.attainedRadii_eq_cornerRadii]
    exact hoff r hr
  exact M.tsum_sMomentInfFlux_eq_rhsScalar (hα0.trans hr.1) hoff'
    (M.cutMoment_ne_top_of_le (le_of_lt hr.2) 2 h2β)

/-- **The closed form is local in the radius.**  At an off-corner point of the window the total
vertex sum agrees, on a whole neighbourhood, with the scalar factor: the corner set is locally
avoidable and `cutMoment 2` stays finite below `β`. -/
theorem eventually_tsum_sMomentInfFlux_eq_rhsScalar {α β r₀ : ℝ} (hα0 : 0 < α)
    (hαr₀ : α < r₀) (hr₀β : r₀ < β) (hoff : r₀ ∉ M.cornerRadii)
    (h2β : M.cutMoment 2 β ≠ ⊤) :
    (fun r => ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) =ᶠ[𝓝 r₀] M.rhsScalar := by
  have hoff' : r₀ ∉ M.attainedRadii := by
    rw [M.attainedRadii_eq_cornerRadii]
    exact hoff
  obtain ⟨ε, hε, hεr⟩ := M.exists_nhds_notMem_attainedRadii hoff'
  filter_upwards [isOpen_Ioo.mem_nhds (show r₀ ∈ Set.Ioo α β from ⟨hαr₀, hr₀β⟩),
    Metric.ball_mem_nhds r₀ hε] with r hr hball
  exact M.tsum_sMomentInfFlux_eq_rhsScalar (hα0.trans hr.1)
    (hεr r (by rw [Metric.mem_ball, Real.dist_eq] at hball; exact hball))
    (M.cutMoment_ne_top_of_le (le_of_lt hr.2) 2 h2β)

/-! ## 2. `hGcont` from continuity of the scalar factor, and a window bound on the sum -/

/-- **Summed-flux continuity from continuity of the scalar factor.**  This is the premise
`hGcont` at a point: no vertexwise continuity, no summability of sup-majorants and no uniform
convergence is used — only the local closed form. -/
theorem continuousAt_tsum_sMomentInfFlux_of_continuousAt_rhsScalar {α β r₀ : ℝ} (hα0 : 0 < α)
    (hαr₀ : α < r₀) (hr₀β : r₀ < β) (hoff : r₀ ∉ M.cornerRadii)
    (h2β : M.cutMoment 2 β ≠ ⊤) (hrhs : ContinuousAt M.rhsScalar r₀) :
    ContinuousAt (fun r' => ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r₀ :=
  hrhs.congr (M.eventually_tsum_sMomentInfFlux_eq_rhsScalar hα0 hαr₀ hr₀β hoff h2β).symm

/-- **`hGcont` in its exact consumed shape**, from continuity of the scalar factor on the
window. -/
theorem hGcont_of_rhsScalar {α β : ℝ} (hα0 : 0 < α) (h2β : M.cutMoment 2 β ≠ ⊤)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hrhs : ∀ r ∈ Set.Ioo α β, ContinuousAt M.rhsScalar r) :
    ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r :=
  fun r hr =>
    M.continuousAt_tsum_sMomentInfFlux_of_continuousAt_rhsScalar hα0 hr.1 hr.2 (hoff r hr) h2β
      (hrhs r hr)

/-- **`hGcont` from continuity of `K'` and of the excluded mass**, the two scalar quantities the
derivative value is built from. -/
theorem hGcont_of_scalar_continuity {α β : ℝ} (hα0 : 0 < α)
    (h2β : M.cutMoment 2 β ≠ ⊤) (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r ∈ Set.Ioo α β, ContinuousAt M.exclScalar r) :
    ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r :=
  M.hGcont_of_rhsScalar hα0 h2β hoff fun r hr => M.continuousAt_rhsScalar (hK r hr) (hex r hr)

/-- **`hGcont` is exactly the continuity of the scalar factor** — with no side condition on
`K'` or on `β_c`: on the window the total vertex sum agrees with `M.rhsScalar` near every point. -/
theorem continuousAt_tsum_sMomentInfFlux_iff_continuousAt_rhsScalar {α β r₀ : ℝ} (hα0 : 0 < α)
    (hαr₀ : α < r₀) (hr₀β : r₀ < β) (hoff : r₀ ∉ M.cornerRadii)
    (h2β : M.cutMoment 2 β ≠ ⊤) :
    ContinuousAt (fun r' => ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r₀ ↔ ContinuousAt M.rhsScalar r₀ := by
  have hev := M.eventually_tsum_sMomentInfFlux_eq_rhsScalar hα0 hαr₀ hr₀β hoff h2β
  exact ⟨fun hg => hg.congr hev, fun hrhs => hrhs.congr hev.symm⟩

/-- **A uniform bound for the whole infinite vertex sum on a radius window.**  The summed flux is
bounded on `[a, b]` by `β_c C |B_b| (cutMoment 2 b).toReal²`, with `C` a bound for `|K'|` on the
window and no moment assumed at any interior radius.  This is the window domination of the sum
itself — obtained from the closed form, not from a per-vertex sup-majorant. -/
theorem abs_tsum_sMomentInfFlux_le_of_window {a b C : ℝ} (ha : 0 < a)
    (hoff : ∀ r ∈ Set.Icc a b, r ∉ M.cornerRadii) (h2b : M.cutMoment 2 b ≠ ⊤)
    (hC : ∀ r ∈ Set.Icc a b, |deriv M.K r| ≤ C) (hCnn : 0 ≤ C) :
    ∀ r ∈ Set.Icc a b,
      |∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r| ≤
      (M.betaCrit : ℝ) * C * (((M.ball b).ncard : ℝ) * (M.cutMoment 2 b).toReal ^ 2) := by
  intro r hr
  have hclosed : (∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv r) = M.rhsScalar r :=
    M.tsum_sMomentInfFlux_eq_rhsScalar (lt_of_lt_of_le ha hr.1)
      (by rw [M.attainedRadii_eq_cornerRadii]; exact hoff r hr)
      (M.cutMoment_ne_top_of_le hr.2 2 h2b)
  rw [hclosed]
  exact M.abs_rhsScalar_le_of_window (le_of_lt ha) hC hCnn h2b (Nat.cast_nonneg _) r hr

/-! ## 3. Sharpness: summed-flux continuity is excluded-mass continuity -/

/-- **At a nonvanishing-derivative point of the window, `hGcont` and the continuity of the
excluded mass are the same statement.**  Hence there is no separate "joint-uniform estimate" to be
found for the summed flux: the total vertex sum is a scalar function, and its only analytic
content is `r ↦ (exclMass r).toReal`. -/
theorem continuousAt_tsum_sMomentInfFlux_iff_continuousAt_exclScalar {α β r₀ : ℝ}
    (hα0 : 0 < α) (hαr₀ : α < r₀) (hr₀β : r₀ < β) (hoff : r₀ ∉ M.cornerRadii)
    (h2β : M.cutMoment 2 β ≠ ⊤) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hK : ContinuousAt (fun r => deriv M.K r) r₀) (hK0 : deriv M.K r₀ ≠ 0) :
    ContinuousAt (fun r' => ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r₀ ↔ ContinuousAt M.exclScalar r₀ := by
  have hev := M.eventually_tsum_sMomentInfFlux_eq_rhsScalar hα0 hαr₀ hr₀β hoff h2β
  constructor
  · intro hg
    exact (M.continuousAt_rhsScalar_iff hβ hK hK0).mp (hg.congr hev)
  · intro hex
    exact M.continuousAt_tsum_sMomentInfFlux_of_continuousAt_rhsScalar hα0 hαr₀ hr₀β hoff h2β
      (M.continuousAt_rhsScalar hK hex)

/-! ## 4. The endpoint derivative theorems with `hGcont` deleted -/

/-- The envelope endpoint theorem of `OffCorner/RadiusPivotalWeight` with `hGcont` removed: it is
derived from continuity of `K'` and of the excluded mass on the window.  `hcontinf` and the
envelope data are unchanged, and `h2β` remains an input. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_scalar
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 C : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hC0 : 0 ≤ C) (hCb : ∀ r ∈ Set.Ioo α β, -(deriv M.K r) ≤ C)
    (hKβ : deriv M.K β < 0)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r ∈ Set.Ioo α β, ContinuousAt M.exclScalar r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 :=
  M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope T hTmono hT S hSmono hS hα0 hαr0
    hr0β hoff hKd h2β hC0 hCb hKβ hcontinf (M.hGcont_of_scalar_continuity hα0 h2β hoff hK hex)

/-- The measurability endpoint theorem of `OffCorner/RadiusMeasurability/Main` with `hGcont`
removed; `hboundint` and `hcontinf` are unchanged. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability_of_scalar
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r ∈ Set.Ioo α β, ContinuousAt M.exclScalar r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 :=
  M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability T hTmono hT S hSmono hS hα0
    hαr0 hr0β hoff hKd h2β hboundint hcontinf
    (M.hGcont_of_scalar_continuity hα0 h2β hoff hK hex)

/-! ## 5. The real remaining scalar input: a frozen-window moment

Off the corner the window `ballF M r` does not move at all, so the excluded mass is a *fixed*
integrand against the varying law `cutLaw r`.  This isolates the one analytic input that is
actually missing, and shows it is not an annulus/moving-window estimate. -/

/-- **`ballF` is locally constant off the corner.**  If no attained radius lies between `r` and
`r₀`, the two truncated balls coincide. -/
theorem ballF_eq_of_offCorner_window {r r₀ : ℝ} (hr : 0 < r) (hr₀ : 0 < r₀)
    (hoff : ∀ s : ℝ, s ∈ Set.Icc (min r r₀) (max r r₀) → s ∉ M.attainedRadii) :
    E1Sign.ballF M r = E1Sign.ballF M r₀ := by
  classical
  ext y
  rw [E1Sign.mem_ballF, E1Sign.mem_ballF, M.mem_ball_iff_dist_le, M.mem_ball_iff_dist_le]
  by_cases hy : y = 0
  · subst hy
    have hz : toVec (0 : M.V) = 0 := by funext i; simp [toVec]
    have h00 : M.S.dist (0 : M.V) 0 = 0 := by
      simp [SourceNormData.dist, hz, M.S.ρ_zero]
    rw [h00]
    exact ⟨fun _ => le_of_lt hr₀, fun _ => le_of_lt hr⟩
  · have hat : M.S.dist y 0 ∈ M.attainedRadii := ⟨y, hy, rfl⟩
    constructor
    · intro hle
      by_contra hcon
      rw [not_le] at hcon
      exact hoff (M.S.dist y 0)
        ⟨le_of_lt (lt_of_le_of_lt (min_le_right _ _) hcon), le_trans hle (le_max_left _ _)⟩ hat
    · intro hle
      by_contra hcon
      rw [not_le] at hcon
      exact hoff (M.S.dist y 0)
        ⟨le_of_lt (lt_of_le_of_lt (min_le_left _ _) hcon), le_trans hle (le_max_right _ _)⟩ hat

/-- The excluded mass with the window frozen at `r₀`: only the law carries the radius. -/
theorem exclMass_eq_frozenWindow {r r₀ : ℝ} (hB : E1Sign.ballF M r = E1Sign.ballF M r₀) :
    E1Sign.exclMass M r = ∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r₀,
      ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
        ∂(M.cutLaw r) := by
  simp only [E1Sign.exclMass]
  rw [hB]

/-- **The frozen-window identity holds on a whole neighbourhood of an off-corner radius.** -/
theorem eventually_exclMass_eq_frozenWindow {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hoff : r₀ ∉ M.attainedRadii) :
    E1Sign.exclMass M =ᶠ[𝓝 r₀] fun r => ∫⁻ ω, clusterVol ω (0 : M.V) *
      ∑ y ∈ E1Sign.ballF M r₀,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
          ∂(M.cutLaw r) := by
  classical
  obtain ⟨ε, hε, hεr⟩ := M.exists_nhds_notMem_attainedRadii hoff
  refine Filter.mem_of_superset (Metric.ball_mem_nhds r₀ (lt_min hε hr₀)) ?_
  intro r hrball
  rw [Metric.mem_ball, Real.dist_eq] at hrball
  have hrlt : |r - r₀| < ε := lt_of_lt_of_le hrball (min_le_left _ _)
  have hrpos : 0 < r := by
    have : |r - r₀| < r₀ := lt_of_lt_of_le hrball (min_le_right _ _)
    rw [abs_lt] at this
    linarith [this.1]
  have hIcc : ∀ s ∈ Set.Icc (min r r₀) (max r r₀), |s - r₀| < ε := by
    intro s hs
    have habs : |s - r₀| ≤ |r - r₀| := by
      rcases le_total r r₀ with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at hs
        rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]
        linarith [hs.1]
      · rw [min_eq_right hle, max_eq_left hle] at hs
        rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]
        linarith [hs.2]
    exact lt_of_le_of_lt habs hrlt
  exact M.exclMass_eq_frozenWindow (M.ballF_eq_of_offCorner_window hrpos hr₀
    (fun s hs => hεr s (hIcc s hs)))

/-- **Excluded-mass continuity is continuity of a frozen-window moment in the law.**  The moving
window is *not* the obstruction off the corner: `(exclMass r).toReal` is continuous at an
off-corner `r₀ > 0` exactly when
`r ↦ (∫⁻ ω, |K_0| ∑_{y ∈ B_{r₀}} 1(y ∉ K_0) |K_y| ∂(cutLaw r)).toReal` is. -/
theorem continuousAt_exclScalar_iff_frozenWindow {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hoff : r₀ ∉ M.attainedRadii) :
    ContinuousAt M.exclScalar r₀ ↔
      ContinuousAt (fun r => (∫⁻ ω, clusterVol ω (0 : M.V) *
        ∑ y ∈ E1Sign.ballF M r₀,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
            ∂(M.cutLaw r)).toReal) r₀ := by
  have hev := M.eventually_exclMass_eq_frozenWindow hr₀ hoff
  have hev' : M.exclScalar =ᶠ[𝓝 r₀] (fun r => (∫⁻ ω, clusterVol ω (0 : M.V) *
      ∑ y ∈ E1Sign.ballF M r₀,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
          ∂(M.cutLaw r)).toReal) := by
    filter_upwards [hev] with r hr
    simp only [SourceModelData.exclScalar]
    rw [hr]
  exact ⟨fun h => h.congr hev', fun h => h.congr hev'.symm⟩

/-- **`hGcont` from the frozen-window input.**  The only remaining analytic datum is, at each
off-corner point `r` of the window, the continuity in the law of the frozen window moment
`B_r`. -/
theorem hGcont_of_frozenWindow {α β : ℝ} (hα0 : 0 < α)
    (h2β : M.cutMoment 2 β ≠ ⊤) (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r)
    (hfix : ∀ r ∈ Set.Ioo α β,
      ContinuousAt (fun s => (∫⁻ ω, clusterVol ω (0 : M.V) *
        ∑ y ∈ E1Sign.ballF M r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
            ∂(M.cutLaw s)).toReal) r) :
    ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r :=
  M.hGcont_of_scalar_continuity hα0 h2β hoff hK fun r hr =>
    (M.continuousAt_exclScalar_iff_frozenWindow (hα0.trans hr.1)
      (by rw [M.attainedRadii_eq_cornerRadii]; exact hoff r hr)).mpr (hfix r hr)

/-- The envelope endpoint theorem with the summed-flux premise reduced to the frozen-window
moment input (`hK` is the continuity of `K'`, `hfix` the frozen-window continuity). -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_frozenWindow
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 C : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hC0 : 0 ≤ C) (hCb : ∀ r ∈ Set.Ioo α β, -(deriv M.K r) ≤ C)
    (hKβ : deriv M.K β < 0)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r)
    (hfix : ∀ r ∈ Set.Ioo α β,
      ContinuousAt (fun s => (∫⁻ ω, clusterVol ω (0 : M.V) *
        ∑ y ∈ E1Sign.ballF M r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
            ∂(M.cutLaw s)).toReal) r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 :=
  M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope T hTmono hT S hSmono hS hα0 hαr0
    hr0β hoff hKd h2β hC0 hCb hKβ hcontinf (M.hGcont_of_frozenWindow hα0 h2β hoff hK hfix)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-- The tail endpoint derivative with `hGcont` supplied by scalar regularity rather than assumed
as a separate input. Local assembly of the accepted tail and summed-flux reductions. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail_of_scalar
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R α β r0 : ℝ} (hRpos : 0 < R) (hRα : R < α)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r ∈ Set.Ioo α β, ContinuousAt M.exclScalar r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 := by
  have hα0 : 0 < α := lt_trans hRpos hRα
  exact M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail T hTmono hT S hSmono hS
    hRpos hRα hlow hupp hαr0 hr0β hoff h2β hcontinf
    (M.hGcont_of_scalar_continuity hα0 h2β hoff hK hex)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms tsum_sMomentInfFlux_eq_rhsScalar
#print axioms tsum_sMomentInfFlux_eq_rhsScalar_on_window
#print axioms eventually_tsum_sMomentInfFlux_eq_rhsScalar
#print axioms continuousAt_tsum_sMomentInfFlux_of_continuousAt_rhsScalar
#print axioms continuousAt_tsum_sMomentInfFlux_iff_continuousAt_rhsScalar
#print axioms abs_tsum_sMomentInfFlux_le_of_window
#print axioms hGcont_of_rhsScalar
#print axioms hGcont_of_scalar_continuity
#print axioms continuousAt_tsum_sMomentInfFlux_iff_continuousAt_exclScalar
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_scalar
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability_of_scalar
#print axioms ballF_eq_of_offCorner_window
#print axioms exclMass_eq_frozenWindow
#print axioms eventually_exclMass_eq_frozenWindow
#print axioms continuousAt_exclScalar_iff_frozenWindow
#print axioms hGcont_of_frozenWindow
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_frozenWindow
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail_of_scalar
