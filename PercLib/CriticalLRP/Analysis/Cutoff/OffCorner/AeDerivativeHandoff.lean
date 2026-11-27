/- Integrated from the independently rebuilt and accepted
`.ultramath/smwyop3kc/m4/AeDerivativeHandoff.lean` at production base
`e8c25f3936540fbe66322454ff596091b18b7436`. -/

module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusSummedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusTailDeriv
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.CornerSafe
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Defs
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.Divergence
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CriticalDivergence
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Statistics
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.MomentHom
public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case23
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.NearWindow

/-!
# Almost-everywhere off-corner derivative handoff for the cutoff first mass

Swarm `smwyop3kc`, member `m4`, direction (4) (*off-corner derivative handoff*).

The Case-3 scope wrappers of `VolumeMoments/HigherMoments/I420Case3/Scope/Main.lean`
consume, as the first input of Proposition I.4.2,

* `hderiv : ∀ t, r₀ ≤ t → HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t`
* `hflux  : ∀ t, r₀ ≤ t → f' t = β_c |K'(t)| (exclMass t).toReal`

i.e. a derivative **at every** radius of the tail.  The shipped off-corner machinery
(`OffCorner/RadiusSummedFlux`, `OffCorner/RadiusTailDeriv`, `OffCorner/ScalarFactor`,
`IntegralFluxInterchange`) can only produce the derivative on a window that meets
**no** attained radius, and the attained radii `M.attainedRadii = M.cornerRadii` are
infinite above every bound (`CornerRadii: locally finite, with `1 ≤ ncard` in nondegenerate
windows).  Hence the everywhere-on-the-tail shape is *not* what the model supplies; the
corner-safe shape of `VolumeMoments/FirstMoment/CornerSafe.lean` is:

* `AbsolutelyContinuousOnInterval` of the mass on `[r₀, R]`, and
* the differential equation `(I.4.6)` only **almost everywhere**.

This file supplies exactly the missing link between the two: the pointwise off-corner
derivative at every non-attained radius of the tail (with one uniform threshold for the
analytic inputs), the resulting `∀ᵐ`-statements, the pointwise form of `(I.4.6)`, and the
composition into `CornerSafe.first_moment_asymptotic_ae` at the model.

Nothing here proves continuity of the excluded mass, the second cutoff moment, the
per-vertex flux or the absolute continuity of the mass; those stay explicit hypotheses.
No statement here differentiates at an attained radius, and no off-corner formula is used
as a global or critical-endpoint derivative theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

open Orchestration

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The attained radii of a tail are Lebesgue-null -/

/-- **Corner radii of a tail are null.**  `Ici r₀ ∩ M.attainedRadii` is a countable union of
the finite sets `M.attainedRadii ∩ Icc r₀ (r₀ + n)`
(`SourceModelData.finite_attainedRadii_inter_Icc`), hence Lebesgue-null.  Consequently a
radius of the tail is off-corner almost everywhere — this is the bookkeeping that lets the
off-corner derivative theorems of `OffCorner/` be used in the a.e. shape of
`CornerSafe`. -/
theorem volume_attainedRadii_inter_Ici (r₀ : ℝ) :
    volume (M.attainedRadii ∩ Set.Ici r₀) = 0 := by
  have hcover : M.attainedRadii ∩ Set.Ici r₀
      = ⋃ n : ℕ, (M.attainedRadii ∩ Set.Icc r₀ (r₀ + (n : ℝ))) := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_iUnion, Set.mem_Icc]
    constructor
    · rintro ⟨hr, hr0⟩
      obtain ⟨n, hn⟩ := exists_nat_ge (r - r₀ : ℝ)
      exact ⟨n, hr, hr0, by linarith⟩
    · rintro ⟨n, hr, hr0, -⟩
      exact ⟨hr, hr0⟩
  rw [hcover]
  exact measure_iUnion_null fun n => M.volume_attainedRadii_inter_Icc r₀ (r₀ + (n : ℝ))

/-- **The attained radii are unbounded.**  The source norm scales (`ρ (c • v) = |c| ρ v`), so
the lattice points `n • x` attain arbitrarily large radii.  Consequently no unbounded radius
window is free of corner radii, and the window hypothesis
`∀ r ∈ Ioo α β, r ∉ M.cornerRadii` of every shipped off-corner derivative theorem forces
`β < ∞`: a derivative at *every* radius of a tail is not what those theorems provide. -/
theorem attainedRadii_unbounded (M : SourceModelData) :
    ∀ B : ℝ, ∃ r ∈ M.attainedRadii, B ≤ r := by
  intro B
  set x : M.V := fun i => if i = (⟨0, M.hd⟩ : Fin M.d) then 1 else 0 with hx
  have hxne : x ≠ 0 := by
    intro h
    have h1 : x ⟨0, M.hd⟩ = (0 : ℤ) := by rw [h]; rfl
    simp [hx] at h1
  have hvne : toVec x ≠ (0 : Fin M.d → ℝ) := toVec_ne_zero hxne
  have hρ : 0 < M.S.ρ (toVec x) := M.S.ρ_pos (toVec x) hvne
  obtain ⟨n, hn⟩ := exists_nat_ge (max (B / M.S.ρ (toVec x)) 1 : ℝ)
  have hn1 : 1 ≤ n := by
    have := le_trans (le_max_right (B / M.S.ρ (toVec x)) 1) hn
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hB : B ≤ (n : ℝ) * M.S.ρ (toVec x) := by
    have h : B / M.S.ρ (toVec x) ≤ (n : ℝ) :=
      le_trans (le_max_left _ _) hn
    rw [div_le_iff₀ hρ] at h
    linarith
  have htoVec : toVec (n • x) = (n : ℝ) • toVec x := by
    funext i
    simp only [toVec, Pi.smul_apply, nsmul_eq_mul]
    push_cast
    ring
  have hxne' : (n • x : M.V) ≠ 0 := by
    intro h
    have hx1 : x ⟨0, M.hd⟩ = (1 : ℤ) := by simp [hx]
    have hval : (n • x) ⟨0, M.hd⟩ = (n : ℤ) := by
      rw [Pi.smul_apply, hx1]
      simp
    rw [h] at hval
    simp only [Pi.zero_apply] at hval
    have h2 : (n : ℝ) = 0 := by exact_mod_cast hval.symm
    exact hnpos.ne' h2
  refine ⟨M.S.dist (n • x) 0, ⟨n • x, hxne', rfl⟩, ?_⟩
  rw [SourceNormData.dist_zero_right, htoVec, M.S.ρ_smul]
  rw [abs_of_pos hnpos]
  exact hB

/-- Off-corner almost everywhere on a tail. -/
theorem ae_notMem_attainedRadii_Ici (r₀ : ℝ) :
    ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)), t ∉ M.attainedRadii := by
  rw [ae_restrict_iff' measurableSet_Ici, ae_iff]
  have hset : {t : ℝ | ¬(t ∈ Set.Ici r₀ → t ∉ M.attainedRadii)}
      = M.attainedRadii ∩ Set.Ici r₀ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, not_imp, not_not, and_comm]
  rw [hset]
  exact M.volume_attainedRadii_inter_Ici r₀

/-! ## 2. The pointwise off-corner derivative in the `hderiv`/`hflux` shape

The shipped off-corner derivative theorems need a radius *window* free of attained radii.
At a single non-attained radius such a window exists (`exists_nhds_notMem_attainedRadii`),
so the derivative is available at every non-attained radius of a tail.  The window is
chosen inside `Ioo (max R a₀) ∞` so that the tail envelope `exists_deriv_bounds` and the
window-uniform analytic inputs (second moment, per-vertex flux continuity, `K'` continuity,
excluded-mass continuity) apply. -/

/-- **Off-corner derivative of the cutoff first mass, at a single radius of a tail.**

The derivative value is written in the standardized `(I.4.5)` form
`β_c |K'(t)| (exclMass t).toReal` consumed by `hflux` of
`I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux`, and the differentiated
function is the model's cutoff mass `fun r => (M.cutMassAt r 0).toReal` consumed by `hderiv`.

The analytic inputs are *window-uniform on a tail*: finiteness of the second cutoff moment,
per-vertex flux continuity, continuity of `deriv K` and continuity of the excluded mass
for every radius `≥ a₀`.  The tail envelope is passed as its threshold `R` with `R < a₀`. -/
theorem hasDerivAt_cutMassAt_toReal_of_offCorner
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    {t : ℝ} (ht : a₀ < t) (htoff : t ∉ M.attainedRadii) :
    HasDerivAt (fun r => (M.cutMassAt r 0).toReal)
      ((M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal) t := by
  obtain ⟨ε, hε, hεr⟩ := M.exists_nhds_notMem_attainedRadii htoff
  have ha₀0 : 0 < a₀ := lt_trans hRpos hRa₀
  have ht0 : 0 < t := lt_trans ha₀0 ht
  have hδpos : 0 < min ε ((t - a₀) / 2) := lt_min hε (half_pos (by linarith))
  -- the corner-free window around `t`, kept inside `Ioi a₀`
  have hαlt : a₀ < t - min ε ((t - a₀) / 2) := by
    have h : min ε ((t - a₀) / 2) ≤ (t - a₀) / 2 := min_le_right _ _
    linarith
  have hβgt : t < t + min ε ((t - a₀) / 2) := by
    linarith
  have hoff : ∀ r ∈ Set.Ioo (t - min ε ((t - a₀) / 2)) (t + min ε ((t - a₀) / 2)),
      r ∉ M.cornerRadii := by
    intro r hr
    rw [← M.attainedRadii_eq_cornerRadii]
    refine hεr r ?_
    have h1 : min ε ((t - a₀) / 2) ≤ ε := min_le_left _ _
    rw [abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hderiv := M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail_of_scalar
    T hTmono hT S hSmono hS hRpos (lt_trans hRa₀ hαlt) hlow hupp
    (by linarith) hβgt hoff (h2 _ (by linarith))
    (fun y r hr => hcontinf y r (le_trans (le_of_lt hαlt) (le_of_lt hr.1)))
    (fun r hr => hK r (le_trans (le_of_lt hαlt) (le_of_lt hr.1)))
    (fun r hr => hex r (le_trans (le_of_lt hαlt) (le_of_lt hr.1)))
  have hval : M.rhsScalar t
      = (M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal := by
    rw [rhsScalar, coeffRHS, exclScalar, ← abs_of_nonpos (M.deriv_K_nonpos ht0)]
  rw [hval] at hderiv
  exact hderiv

/-! ## 3. The almost-everywhere off-corner derivative on a tail -/

/-- **Almost-everywhere off-corner derivative of the cutoff first mass.**  This is the
`hderiv`/`hflux` pair of the Case-3 scope wrappers weakened from *every* radius of the tail to
almost every radius, which is the form the shipped off-corner theorems actually supply
(Section 1 gives that the excluded set — the attained radii — is Lebesgue-null).

The derivative value is the standardized flux `β_c |K'(t)| (exclMass t).toReal`. -/
theorem ae_hasDerivAt_cutMassAt_toReal
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r) :
    ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)), HasDerivAt (fun r => (M.cutMassAt r 0).toReal)
      ((M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal) t := by
  filter_upwards [M.ae_notMem_attainedRadii_Ici r₀, ae_restrict_mem measurableSet_Ici]
    with t htoff ht
  exact M.hasDerivAt_cutMassAt_toReal_of_offCorner T hTmono hT S hSmono hS hRpos hRa₀ hlow hupp
    h2 hcontinf hK hex (lt_of_lt_of_le ha₀r₀ ht) htoff

/-- **The tail threshold is produced by the source power law.**  Same as
`ae_hasDerivAt_cutMassAt_toReal`, with `R` and both halves of the envelope supplied by
`SourceModelData.exists_deriv_bounds`. -/
theorem exists_ae_hasDerivAt_cutMassAt_toReal
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n) :
    ∃ R : ℝ, 0 < R ∧ ∀ {a₀ r₀ : ℝ}, R < a₀ → a₀ < r₀ →
      (∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤) →
      (∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
        (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r) →
      (∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r) →
      (∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r) →
      ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)), HasDerivAt (fun r => (M.cutMassAt r 0).toReal)
        ((M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal) t := by
  obtain ⟨R, hRpos, -, hlow, hupp⟩ := M.exists_deriv_bounds
  exact ⟨R, hRpos, fun hRa₀ ha₀r₀ h2 hcontinf hK hex =>
    M.ae_hasDerivAt_cutMassAt_toReal T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀ hlow hupp
      h2 hcontinf hK hex⟩

/-! ## 4. The pointwise and almost-everywhere form of `(I.4.6)`

`PivotFlux.cutMass_ODE_of_flux` converts the flux identity `F' t = β_c |K'(t)| (exclMass t).toReal`
into the standardized ODE `(I.4.6)`, but it is stated with the flux identity on a whole tail.
Its proof is pointwise, so the same conclusion holds at a single radius; the version below
makes that explicit, which is what the a.e. handoff of `CornerSafe` consumes. -/

/-- **The two spellings of the off-corner derivative value.**  For positive radius the
standardized flux `β_c |K'(t)| (exclMass t).toReal` and the scalar factor
`M.rhsScalar t = β_c (-K'(t)) (exclMass t).toReal` coincide, since `K' ≤ 0` (`K` is antitone). -/
theorem betaCrit_abs_deriv_mul_eq_rhsScalar {t : ℝ} (ht : 0 < t) :
    (M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal = M.rhsScalar t := by
  rw [rhsScalar, coeffRHS, exclScalar, ← abs_of_nonpos (M.deriv_K_nonpos ht)]

/-- **`(I.4.6)` at a single radius.**  The derivative value `β_c |K'(t)| (exclMass t).toReal`
equals the standardized right-hand side `(1 - cutError t) β_c t^{-α-1} χ(t)²` at every radius of
the second-moment-finite tail. -/
theorem rhsScalar_eq_ode_at {a₀ : ℝ} (ha₀ : 0 < a₀)
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤) {t : ℝ} (ht : a₀ ≤ t) :
    M.rhsScalar t = (M.betaCrit : ℝ) * (1 - I420Case3.cutError M t) * t ^ (-M.α - 1) *
      (M.cutMassReal t) ^ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le ha₀ ht
  have hflux : ∀ s : ℝ, t ≤ s → M.rhsScalar s
      = (M.betaCrit : ℝ) * |deriv M.K s| * (E1Sign.exclMass M s).toReal := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ht0 hs
    rw [rhsScalar, coeffRHS, exclScalar, ← abs_of_nonpos (M.deriv_K_nonpos hs0)]
  have h := PivotFlux.cutMass_ODE_of_flux M ht0 (fun s hs => h2 s (le_trans ht hs)) hflux t le_rfl
  have h1 : (1 - (1 - (1 - PivotFlux.cutE0 M t) * (1 - PivotFlux.cutE1 M t)))
      = (1 - I420Case3.cutError M t) := by
    rw [I420Case3.cutError]
  rw [h1] at h
  have hcm : M.cutMassReal t = (M.cutMassAt t 0).toReal := rfl
  rw [hcm, h]
  ring

/-- **The almost-everywhere standardized ODE `(I.4.6)` at the model.**  In the exact shape of
the `hae` hypothesis of `CornerSafe.first_moment_asymptotic_ae`, with `A = β_c` and
`h = cutError M`. -/
theorem ae_hasDerivAt_cutMassAt_toReal_ode
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r) :
    ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)), HasDerivAt (fun r => (M.cutMassAt r 0).toReal)
      ((M.betaCrit : ℝ) * (1 - I420Case3.cutError M t) * t ^ (-M.α - 1) *
        (M.cutMassReal t) ^ 2) t := by
  have ha₀0 : 0 < a₀ := lt_trans hRpos hRa₀
  filter_upwards [M.ae_hasDerivAt_cutMassAt_toReal T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀
    hlow hupp h2 hcontinf hK hex, ae_restrict_mem measurableSet_Ici] with t ht hmem
  have ht0 : 0 < t := lt_of_lt_of_le ha₀0 (le_trans (le_of_lt ha₀r₀) hmem)
  rw [M.betaCrit_abs_deriv_mul_eq_rhsScalar ht0] at ht
  rw [M.rhsScalar_eq_ode_at ha₀0 h2 (le_trans (le_of_lt ha₀r₀) hmem)] at ht
  exact ht

/-! ## 5. Case 3 of Proposition I.4.2 at the model, corner-safe

The scope wrappers `I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3` and its `_flux`
variant feed `hP` of `case3_hAend_hAmid_cutPoly_source_of_finite` from
`I42C.first_moment_asymptotic_of_rpow_lower`, which needs the pointwise derivative
`hderiv` at **every** radius of the tail.  The theorem below produces the same conclusion
`f r / ((α/β_c) r^α) → 1` from the corner-safe inputs instead: absolute continuity of the
mass, and the a.e. ODE of Section 4. -/

/-- **Proposition I.4.2, Case 3, corner-safe form, at the actual cutoff mass.** -/
theorem first_moment_asymptotic_ae_of_offCorner_of_hac
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hac : ∀ R', r₀ ≤ R' →
      AbsolutelyContinuousOnInterval (fun r => (M.cutMassAt r 0).toReal) r₀ R')
    (hinf : Tendsto (fun r => (M.cutMassAt r 0).toReal) atTop atTop)
    (hmeas : Measurable (I420Case3.cutError M))
    {C : ℝ} (hC : ∀ t : ℝ, r₀ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0)) :
    Tendsto (fun r => (M.cutMassAt r 0).toReal / (M.α / (M.betaCrit : ℝ) * r ^ M.α))
      atTop (𝓝 1) := by
  have ha₀0 : 0 < a₀ := lt_trans hRpos hRa₀
  have hr₀0 : 0 < r₀ := lt_trans ha₀0 ha₀r₀
  have hpos : ∀ t : ℝ, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal := by
    intro t ht
    have h2t : M.cutMoment 2 t ≠ ⊤ := h2 t (le_trans (le_of_lt ha₀r₀) ht)
    have hfinA : M.cutMassAt t 0 ≠ ⊤ :=
      ne_top_of_le_ne_top h2t (E1Sign.cutMassAt_le_cutMoment_two M t)
    have h1 : (1 : ℝ) ≤ (M.cutMassAt t 0).toReal := by
      have hle := ENNReal.toReal_mono hfinA (E1Sign.one_le_cutMassAt M t)
      simpa using hle
    linarith
  exact CornerSafe.first_moment_asymptotic_ae hβ M.hα hr₀0 hac hpos hinf
    (M.ae_hasDerivAt_cutMassAt_toReal_ode T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀ hlow hupp
      h2 hcontinf hK hex)
    hmeas hC h0

/-- **Absolute continuity of the cutoff mass on a tail, from the off-corner data.**

`CornerSafe`'s corner-safe Lemma I.4.5 needs `AbsolutelyContinuousOnInterval` of the mass on
every `[r₀, R]`.  This is *derived* here rather than assumed: the incremental bound of
`LocalAC/Interface` needs a majorant for the derivative off the corner set, and the off-corner
derivative of Section 2 together with the window bound `abs_rhsScalar_le_of_window` supplies the
constant majorant `β_c C₀ |B_{R'}| (cutMoment 2 R')²`, where `C₀ = 2 r₀^{-d-α-1}` dominates
`|K'|` on `[r₀, R']` by the tail envelope.  The corner set of the window is finite
(`finite_cornerRadii_inter_Ioo`) and the mass is continuous there
(`continuousAt_cutMassReal`). -/
theorem cutMassReal_absolutelyContinuousOn_of_offCorner
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r) :
    ∀ R' : ℝ, r₀ ≤ R' →
      AbsolutelyContinuousOnInterval (fun r => (M.cutMassAt r 0).toReal) r₀ R' := by
  intro R' hR'
  have ha₀0 : 0 < a₀ := lt_trans hRpos hRa₀
  have hr₀0 : 0 < r₀ := lt_trans ha₀0 ha₀r₀
  have hRr₀ : R < r₀ := lt_trans hRa₀ ha₀r₀
  -- the constant slope bound on `[r₀, R']`, from the tail envelope
  have hKbound : ∀ r ∈ Set.Icc r₀ R', |deriv M.K r| ≤ 2 * r₀ ^ (-(M.d : ℝ) - M.α - 1) := by
    intro r hr
    have hRr : R < r := lt_of_lt_of_le hRr₀ hr.1
    have hle := hupp r hRr
    have hmono := Real.rpow_le_rpow_of_nonpos hr₀0 hr.1 M.tail_rpow_exponent_nonpos
    linarith
  have hC₀nn : (0 : ℝ) ≤ 2 * r₀ ^ (-(M.d : ℝ) - M.α - 1) := by
    have : 0 < r₀ ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hr₀0 _
    linarith
  have h2R' : M.cutMoment 2 R' ≠ ⊤ := h2 R' (le_trans (le_of_lt ha₀r₀) hR')
  -- continuity of the mass on the window
  have hfin1 : M.cutMassAt (R' + 1) 0 ≠ ⊤ :=
    ne_top_of_le_ne_top (h2 (R' + 1) (by linarith))
      (E1Sign.cutMassAt_le_cutMoment_two M (R' + 1))
  have hcont : ContinuousOn M.cutMassReal (Set.Icc r₀ R') := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hr₀0 hr.1
    exact (M.continuousAt_cutMassReal r hr0 (by linarith [hr.2]) hfin1).continuousWithinAt
  -- the off-corner derivative bound against a constant majorant
  have hgood : ∀ u ∈ Set.Ioo r₀ R', u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤
        (M.betaCrit : ℝ) * (2 * r₀ ^ (-(M.d : ℝ) - M.α - 1)) *
          (((M.ball R').ncard : ℝ) * (M.cutMoment 2 R').toReal ^ 2) := by
    intro u hu huoff
    have huoff' : u ∉ M.attainedRadii := by
      rw [M.attainedRadii_eq_cornerRadii]
      exact huoff
    have hu0 : 0 < u := lt_trans hr₀0 hu.1
    have hderiv := M.hasDerivAt_cutMassAt_toReal_of_offCorner T hTmono hT S hSmono hS hRpos hRa₀
      hlow hupp h2 hcontinf hK hex (lt_trans ha₀r₀ hu.1) huoff'
    refine ⟨hderiv.differentiableAt, ?_⟩
    have hdv : deriv M.cutMassReal u
        = (M.betaCrit : ℝ) * |deriv M.K u| * (E1Sign.exclMass M u).toReal := hderiv.deriv
    rw [hdv, M.betaCrit_abs_deriv_mul_eq_rhsScalar hu0]
    exact M.abs_rhsScalar_le_of_window (le_of_lt hr₀0) hKbound hC₀nn h2R'
      (Nat.cast_nonneg _) u ⟨hu.1.le, hu.2.le⟩
  exact M.cutMassReal_absolutelyContinuousOn_of_continuousOn_interior hR' hcont
    intervalIntegrable_const continuous_const.continuousOn
    (M.finite_cornerRadii_inter_Ioo r₀ R') hgood

/-- **The same, with the divergence `χ(r) → ∞` discharged** from the source lower two-point
bound (`I42C.uncutFirstMoment_eq_top_of_rpow_lower` + `tendsto_cutMassAt_atTop_nhds_top`).
This is the exact `hP` input of
`I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite`, in corner-safe form. -/
theorem first_moment_asymptotic_ae_of_rpow_lower_of_hac
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hac : ∀ R', r₀ ≤ R' →
      AbsolutelyContinuousOnInterval (fun r => (M.cutMassAt r 0).toReal) r₀ R')
    (hmeas : Measurable (I420Case3.cutError M))
    {C c : ℝ} (hC : ∀ t : ℝ, r₀ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0))
    (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow2 : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) :
    Tendsto (fun r => (M.cutMassAt r 0).toReal / (M.α / (M.betaCrit : ℝ) * r ^ M.α))
      atTop (𝓝 1) :=
  M.first_moment_asymptotic_ae_of_offCorner_of_hac T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀ hβ
    hlow hupp h2 hcontinf hK hex hac
    (I42C.tendsto_cutMassAt_toReal_atTop M
      (I42C.tendsto_cutMassAt_atTop_nhds_top M
        (I42C.uncutFirstMoment_eq_top_of_rpow_lower M hc hαd hlow2)) hfin)
    hmeas hC h0

/-- **Interval-integral transport of the off-corner flux.**  For `r₀ ≤ a ≤ b`,

`∫ t in a..b, β_c |K'(t)| (exclMass t).toReal = χ(b) - χ(a)`,

i.e. the parameterised transport of `(I.4.5)` on an arbitrary interval of the tail.  The only
exceptional set is `M.attainedRadii` (null by Section 1), which the integral does not see; the
absolute continuity needed for the fundamental theorem is item
`cutMassReal_absolutelyContinuousOn_of_offCorner`. -/
theorem intervalIntegral_rhsScalar_eq_sub
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    {a b : ℝ} (har₀ : r₀ ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, M.rhsScalar t = M.cutMassReal b - M.cutMassReal a := by
  have hACb := M.cutMassReal_absolutelyContinuousOn_of_offCorner T hTmono hT S hSmono hS hRpos
    hRa₀ ha₀r₀ hlow hupp h2 hcontinf hK hex b (le_trans har₀ hab)
  have hsub : Set.uIcc a b ⊆ Set.uIcc r₀ b := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (le_trans har₀ hab)]
    exact Set.Icc_subset_Icc har₀ le_rfl
  have hAC : AbsolutelyContinuousOnInterval M.cutMassReal a b := hACb.mono hsub
  have hFTC : ∫ t in a..b, deriv M.cutMassReal t = M.cutMassReal b - M.cutMassReal a :=
    hAC.integral_deriv_eq_sub
  rw [← hFTC]
  refine intervalIntegral.integral_congr_ae ?_
  have hae := (ae_restrict_iff' measurableSet_Ici).1
    (M.ae_hasDerivAt_cutMassAt_toReal T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀ hlow hupp
      h2 hcontinf hK hex)
  filter_upwards [hae] with t ht htu
  have htu' : t ∈ Set.Ioc a b := by
    rw [← Set.uIoc_of_le hab]
    exact htu
  have htge : r₀ ≤ t := le_trans har₀ (le_of_lt htu'.1)
  have h0t : 0 < t := lt_of_lt_of_le (lt_trans (lt_trans hRpos hRa₀) ha₀r₀) htge
  have h1 : deriv M.cutMassReal t
      = (M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal := (ht htge).deriv
  rw [h1]
  exact (M.betaCrit_abs_deriv_mul_eq_rhsScalar h0t).symm

/-- **The same transport in the standardized `(I.4.6)` form.** -/
theorem intervalIntegral_ode_eq_sub
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    {a b : ℝ} (har₀ : r₀ ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, (M.betaCrit : ℝ) * (1 - I420Case3.cutError M t) * t ^ (-M.α - 1) *
        (M.cutMassReal t) ^ 2 = M.cutMassReal b - M.cutMassReal a := by
  rw [← M.intervalIntegral_rhsScalar_eq_sub T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀ hlow hupp
    h2 hcontinf hK hex har₀ hab]
  refine intervalIntegral.integral_congr fun t htu => ?_
  rw [Set.uIcc_of_le hab] at htu
  have htge : a₀ ≤ t := le_trans (le_of_lt ha₀r₀) (le_trans har₀ htu.1)
  exact (M.rhsScalar_eq_ode_at (lt_trans hRpos hRa₀) h2 htge).symm

/-- **Proposition I.4.2, Case 3, corner-safe form at the actual cutoff mass**, with the
absolute continuity of the mass *derived* from the off-corner data
(`cutMassReal_absolutelyContinuousOn_of_offCorner`).  The remaining inputs are the
window-uniform off-corner data, the measurability / boundedness / vanishing of the defect
`cutError`, and the divergence `χ → ∞`. -/
theorem first_moment_asymptotic_ae_of_offCorner
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hinf : Tendsto (fun r => (M.cutMassAt r 0).toReal) atTop atTop)
    (hmeas : Measurable (I420Case3.cutError M))
    {C : ℝ} (hC : ∀ t : ℝ, r₀ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0)) :
    Tendsto (fun r => (M.cutMassAt r 0).toReal / (M.α / (M.betaCrit : ℝ) * r ^ M.α))
      atTop (𝓝 1) :=
  M.first_moment_asymptotic_ae_of_offCorner_of_hac T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀ hβ
    hlow hupp h2 hcontinf hK hex
    (M.cutMassReal_absolutelyContinuousOn_of_offCorner T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀
      hlow hupp h2 hcontinf hK hex)
    hinf hmeas hC h0

/-- **The same with the divergence `χ(r) → ∞` discharged** from the source lower two-point
bound.  This is the exact `hP` input of
`I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite`, with absolute continuity and the
a.e. ODE both derived. -/
theorem first_moment_asymptotic_ae_of_rpow_lower
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R a₀ r₀ : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hmeas : Measurable (I420Case3.cutError M))
    {C c : ℝ} (hC : ∀ t : ℝ, r₀ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0))
    (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow2 : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) :
    Tendsto (fun r => (M.cutMassAt r 0).toReal / (M.α / (M.betaCrit : ℝ) * r ^ M.α))
      atTop (𝓝 1) :=
  M.first_moment_asymptotic_ae_of_rpow_lower_of_hac T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀ hβ
    hlow hupp h2 hcontinf hK hex
    (M.cutMassReal_absolutelyContinuousOn_of_offCorner T hTmono hT S hSmono hS hRpos hRa₀ ha₀r₀
      hlow hupp h2 hcontinf hK hex)
    hmeas hC h0 hc hαd hlow2 hfin

/-- The same corner-safe first-moment asymptotic using the source's actual
uncut critical-mean divergence input.  Global measurability of the composite
defect is supplied by the independently proved statistics package. -/
theorem first_moment_asymptotic_ae_of_critical_divergence
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ C : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (hlowenv : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hC : ∀ t : ℝ, r₀ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal / (M.α / (M.betaCrit : ℝ) * r ^ M.α))
      atTop (𝓝 1) :=
  M.first_moment_asymptotic_ae_of_offCorner T hTmono hT Se hSmono hS hRpos hRa₀ ha₀r₀
    hβ hlowenv huppenv h2 hcontinf hK hex
    (I42C.tendsto_cutMassAt_toReal_atTop M
      (I42C.tendsto_cutMassAt_atTop_nhds_top M htop) hfin)
    (E1Sign.measurable_cutError M) hC h0

#print axioms first_moment_asymptotic_ae_of_critical_divergence

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP

open Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.volume_attainedRadii_inter_Ici
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.attainedRadii_unbounded
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ae_notMem_attainedRadii_Ici
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassAt_toReal_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ae_hasDerivAt_cutMassAt_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_ae_hasDerivAt_cutMassAt_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.betaCrit_abs_deriv_mul_eq_rhsScalar
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.rhsScalar_eq_ode_at
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ae_hasDerivAt_cutMassAt_toReal_ode
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.first_moment_asymptotic_ae_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.first_moment_asymptotic_ae_of_rpow_lower

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

/-! ## 6. Case 3 of Proposition I.4.20 at source balls, with the corner-safe first moment

`case3_hAend_hAmid_cutPoly_source_of_HD_case3` (Scope/Main) obtains its first-moment input
from `I42C.first_moment_asymptotic_of_rpow_lower`, i.e. it carries the pointwise derivative
`hderiv` at every radius of the tail plus the ODE `hode`.  The theorem below is the same
assembly with that input replaced by

* absolute continuity of the cutoff mass on `[r₀, R]` (`hac`),
* the a.e. ODE of Section 4, whose inputs are window-uniform off-corner data (`h2`, `hcontinf`,
  `hK`, `hex`) and the vanishing/boundedness/measurability of `cutError`.

The `(HD)(3)` tail `hTail` and the window moment finiteness are discharged exactly as in the
scope wrapper. -/
theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_ae_of_hac (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ c C : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit) (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlowenv : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hac : ∀ R', r₀ ≤ R' →
      AbsolutelyContinuousOnInterval (fun r => (M.cutMassAt r 0).toReal) r₀ R')
    (hmeas : Measurable (cutError M))
    (hC : ∀ t : ℝ, r₀ ≤ t → |cutError M t| ≤ C)
    (h0 : Tendsto (cutError M) atTop (𝓝 0))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
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
    (M.first_moment_asymptotic_ae_of_rpow_lower_of_hac T hTmono hT Se hSmono hS hRpos hRa₀ ha₀r₀
      hβ hlowenv huppenv h2 hcontinf hK hex hac hmeas hC h0 hc hαd hlow hfin)
    hTri 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2
    hMa hc3 hgm

/-- **Case 3 of Proposition I.4.20 at source balls, corner-safe.**  Same conclusion as
`case3_hAend_hAmid_cutPoly_source_of_HD_case3`, but every first-moment input (`hderiv`, `hpos`,
`hode`) is replaced by the window-uniform off-corner data `h2`, `hcontinf`, `hK`, `hex` and the
defect data `hmeas`, `hC`, `h0`; the absolute continuity of the mass is derived. -/
theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_ae (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ c C : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit) (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlowenv : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hmeas : Measurable (cutError M))
    (hC : ∀ t : ℝ, r₀ ≤ t → |cutError M t| ≤ C)
    (h0 : Tendsto (cutError M) atTop (𝓝 0))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
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
    (M.first_moment_asymptotic_ae_of_rpow_lower T hTmono hT Se hSmono hS hRpos hRa₀ ha₀r₀
      hβ hlowenv huppenv h2 hcontinf hK hex hmeas hC h0 hc hαd hlow hfin)
    hTri 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2
    hMa hc3 hgm

/-- **The normalized `(I.4.21)` form of Case 3 at source balls, corner-safe.**  Same conclusion
as `case3_i421_cutPoly_source_of_HD_case3`, with `hderiv`, `hpos`, `hode` replaced by the
window-uniform off-corner data; the windowed moment finiteness is still discharged by
translation invariance (`powMomentAt_cutProb_apply_eq_zero`). -/
theorem case3_i421_cutPoly_source_of_HD_case3_ae (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ c C : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < M.betaCrit) (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlowenv : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (hmeas : Measurable (cutError M))
    (hC : ∀ t : ℝ, r₀ ≤ t → |cutError M t| ≤ C)
    (h0 : Tendsto (cutError M) atTop (𝓝 0))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
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
    (M.first_moment_asymptotic_ae_of_rpow_lower T hTmono hT Se hSmono hS hRpos hRa₀ ha₀r₀
      hβ hlowenv huppenv h2 hcontinf hK hex hmeas hC h0 hc hαd hlow hfin)
    hTri 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2
    hMa hMb hc3 hgm

end I420Case3

end PercLib.CriticalLRP

/-! ## Axiom audit of the Case-3 headline -/

#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3_ae
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3_ae_of_hac
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_absolutelyContinuousOn_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegral_rhsScalar_eq_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegral_ode_eq_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.first_moment_asymptotic_ae_of_offCorner
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.first_moment_asymptotic_ae_of_rpow_lower

#print axioms PercLib.CriticalLRP.I420Case3.case3_i421_cutPoly_source_of_HD_case3_ae
