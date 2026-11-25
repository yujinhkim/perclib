/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0 license.

The off-sphere condition of the landed `p = 2` off-corner derivative is the off-corner condition at
positive radius, so it holds at almost every radius of the window.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.RadiusMoments
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.Sharpness

/-!
# The off-sphere condition is the off-corner condition

`Analysis/Cutoff/SecondMoment/SourceWitness/OffCorner.lean` proves, at the literal power-law
witness and an off-corner window `[a, b]`, the `p = 2` radius derivative

`HasDerivAt (fun r => M.cutMomentReal 2 r) (powLawCoeff β_c d α r0 * (M.p2RHS r0).toReal) r0`

at every radius `r0 ∈ (a, b)` satisfying the *off-sphere* condition
`hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0`, and `RadiusMoments.lean` eliminates the *corner*
exception set from pointwise derivative formulae (`ae_hasDerivAt_of_offCorner`).  The two
conditions had not been identified.

This file proves that they coincide:

* `sphereRadii_eq_attainedRadii_union` / `sphereRadii_eq_cornerRadii_union`: the vertex radii
  `M.sphereRadii` are the landed corner radii `M.attainedRadii = M.cornerRadii` together with `0`;
* `offSphere_iff_notMem_cornerRadii`: at every positive radius, the off-sphere hypothesis of the
  derivative is *equivalent* to `r0 ∉ M.cornerRadii`;
* `countable_sphereRadii`, `volume_sphereRadii`: the vertex radii are countable and Lebesgue-null
  (the nullity is derived from the landed `M.volume_cornerRadii`), so the off-sphere condition
  fails only on a null set, and every nondegenerate interval contains an off-sphere radius
  (`exists_mem_Ioo_notMem_sphereRadii`).

Consequently the off-sphere hypothesis disappears from the almost-everywhere form of the
derivative, which is the input that a radius-integration step consumes:

* `ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner`, with the fourth cutoff moment on
  the window as the only analytic input;
* `ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical`, with that moment
  discharged through `SourceModelData.cutMoment_ne_top_of_subcritical_first`, so that the remaining
  inputs are exactly `β_c > 0` and the staged subcritical first-moment finiteness `hsub`;
* the corresponding existence forms `exists_hasDerivAt_...`, which hold at some radius of every
  nondegenerate window, and the same statements on the concrete nondegenerate window
  `[7/2, 39/10]`.

Two further consequences are recorded: `IsOffCornerWindow.mono` (off-corner windows restrict to
sub-windows) and `hasDerivAt_cutMomentReal_two_sourceModelWitness_offCornerRadii`, the landed
pointwise derivative restated with the hypothesis `r0 ∉ M.cornerRadii`.  The monotonicity in the
radius makes the paper's derivative expression nonnegative a.e. on the window
(`ae_nonneg_powLawCoeff_mul_p2RHS_sourceModelWitness_of_subcritical`), a sign constraint on `p2RHS`.

Nothing here proves the subcritical first-moment finiteness `hsub`: it is taken as the sharpness
input of the staged `Sharpness.lean`, exactly where that file leaves it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. The vertex radius set and its relation to the corner radii -/

theorem SourceModelData.mem_sphereRadii {M : SourceModelData} {r : ℝ} :
    r ∈ M.sphereRadii ↔ ∃ y : M.V, M.S.ρ (toVec y) = r :=
  Iff.rfl

/-- **The vertex radii are the landed attained radii together with `0`.** -/
theorem SourceModelData.sphereRadii_eq_attainedRadii_union (M : SourceModelData) :
    M.sphereRadii = M.attainedRadii ∪ {0} := by
  have h0 : toVec (0 : M.V) = 0 := by
    funext i
    simp [toVec]
  ext r
  rw [SourceModelData.mem_sphereRadii, Set.mem_union, SourceModelData.mem_attainedRadii,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      exact Or.inr (by rw [h0]; exact M.S.ρ_zero)
    · exact Or.inl ⟨y, hy, SourceNormData.dist_zero_right M.S y⟩
  · rintro (⟨y, _hy, hd⟩ | h0')
    · exact ⟨y, by rw [← SourceNormData.dist_zero_right M.S y]; exact hd⟩
    · subst h0'
      exact ⟨0, by rw [h0]; exact M.S.ρ_zero⟩

/-- **The vertex radii are the corner radii together with `0`.**  This is the set whose complement
the off-sphere hypothesis of the derivative quantifies over. -/
theorem SourceModelData.sphereRadii_eq_cornerRadii_union (M : SourceModelData) :
    M.sphereRadii = M.cornerRadii ∪ {0} := by
  rw [M.sphereRadii_eq_attainedRadii_union, SourceModelData.attainedRadii_eq_cornerRadii]

/-- The off-sphere condition of the derivative, as membership in the vertex radius set. -/
theorem SourceModelData.offSphere_iff {M : SourceModelData} {r : ℝ} :
    M.OffSphere r ↔ ∀ y : M.V, M.S.ρ (toVec y) ≠ r := by
  refine ⟨fun h y hy => h ⟨y, hy⟩, fun h hy => ?_⟩
  obtain ⟨y, hy'⟩ := hy
  exact h y hy'

/-- **At positive radius the off-sphere condition is the off-corner condition**: the landed
hypothesis `∀ y, M.S.ρ (toVec y) ≠ r0` of the off-corner derivative holds exactly when
`r0 ∉ M.cornerRadii`. -/
theorem SourceModelData.offSphere_iff_notMem_cornerRadii {M : SourceModelData} {r : ℝ}
    (hr : 0 < r) : M.OffSphere r ↔ r ∉ M.cornerRadii := by
  simp only [SourceModelData.OffSphere, M.sphereRadii_eq_cornerRadii_union, Set.mem_union,
    Set.mem_singleton_iff, not_or]
  exact ⟨fun h => h.1, fun h => ⟨h, by rintro rfl; exact lt_irrefl 0 hr⟩⟩

/-- **Off-corner windows pass to sub-windows**: the corner condition on `[a, b]` restricts to any
sub-interval with positive left endpoint. -/
theorem SourceModelData.IsOffCornerWindow.mono {M : SourceModelData} {a b a' b' : ℝ}
    (h : M.IsOffCornerWindow a b) (ha' : 0 < a') (haa : a ≤ a') (hab' : a' ≤ b')
    (hb'b : b' ≤ b) : M.IsOffCornerWindow a' b' :=
  ⟨ha', hab', fun r hr =>
    h.2.2 r ⟨le_trans haa hr.1, le_trans hr.2 hb'b⟩⟩

/-! ## 2. Countability and nullity of the vertex radii -/

/-- **The vertex radii of the source lattice are countable**: they are the image of the countable
vertex type under the norm. -/
theorem SourceModelData.countable_sphereRadii (M : SourceModelData) : M.sphereRadii.Countable :=
  Set.countable_range (fun y : M.V => M.S.ρ (toVec y))

/-- **The vertex radii are Lebesgue-null**, from the landed nullity of the corner radii. -/
theorem SourceModelData.volume_sphereRadii (M : SourceModelData) : volume M.sphereRadii = 0 := by
  rw [M.sphereRadii_eq_cornerRadii_union]
  exact measure_union_null M.volume_cornerRadii (by simp)

/-! ## 3. Non-vacuity of the off-sphere condition in any nondegenerate interval -/

/-- **Every nondegenerate interval contains an off-sphere radius**: a null set cannot contain an
interval of positive length. -/
theorem SourceModelData.exists_mem_Ioo_notMem_sphereRadii (M : SourceModelData) {a b : ℝ}
    (hab : a < b) : ∃ r : ℝ, r ∈ Set.Ioo a b ∧ r ∉ M.sphereRadii := by
  by_contra h
  have hsub : Set.Ioo a b ⊆ M.sphereRadii := by
    intro r hr
    by_contra hr'
    exact h ⟨r, hr, hr'⟩
  have hmono : volume (Set.Ioo a b) ≤ volume M.sphereRadii := measure_mono hsub
  rw [M.volume_sphereRadii, Real.volume_Ioo] at hmono
  exact (lt_irrefl (0 : ℝ≥0∞))
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)) hmono)

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-! ## 4. The off-corner derivative at almost every radius of the window -/

/-- **The landed pointwise off-corner derivative with the off-corner hypothesis.**  This is a
restatement of `hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner` in the library's own
vocabulary: by `offSphere_iff_notMem_cornerRadii` its sphere condition is `r0 ∉ M.cornerRadii`.  No
new content; it is recorded because the library states cutoff differentiability at off-corner
radii. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_offCornerRadii
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b r0 : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (har : a < r0) (hrb : r0 < b)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc a b →
      (sourceModelWitness d hd α hα).cutMoment 4 t ≠ ⊤)
    (hoff : r0 ∉ (sourceModelWitness d hd α hα).cornerRadii) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα hwin har hrb h4
    (SourceModelData.offSphere_iff.mp
      ((SourceModelData.offSphere_iff_notMem_cornerRadii (lt_trans hwin.1 har)).mpr hoff))

/-- **The `p = 2` off-corner derivative holds at almost every radius of an off-corner window.**

The landed pointwise theorem needs the off-sphere condition at the differentiation point; by
`offSphere_iff_notMem_cornerRadii` that is the off-corner condition, which the landed corner
elimination `ae_hasDerivAt_of_offCorner_two` removes on a null set.  The fourth cutoff moment
remains an explicit input. -/
theorem ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc a b →
      (sourceModelWitness d hd α hα).cutMoment 4 t ≠ ⊤) :
    ∀ᵐ r0 ∂(volume.restrict (Set.Ioo a b)),
      HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
        (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
          * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  (sourceModelWitness d hd α hα).ae_hasDerivAt_of_offCorner_two
    (fun u => powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α u
      * ((sourceModelWitness d hd α hα).p2RHS u).toReal)
    (fun _u hu hoff =>
      hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα hwin hu.1 hu.2 h4
        (SourceModelData.offSphere_iff.mp
          ((SourceModelData.offSphere_iff_notMem_cornerRadii (lt_trans hwin.1 hu.1)).mpr hoff)))

/-- **The off-corner derivative at almost every radius, conditional only on the sharpness input.**

The fourth cutoff moment on the window is discharged by
`SourceModelData.cutMoment_ne_top_of_subcritical_first`, so the remaining inputs are exactly
positivity of `β_c`, the staged subcritical first-moment finiteness `hsub`, and the off-corner
window. -/
theorem ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (hβ : 0 < (sourceModelWitness d hd α hα).betaCrit)
    (hsub : ∀ β : ℝ≥0, β < (sourceModelWitness d hd α hα).betaCrit →
      (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
        ∂((sourceModelWitness d hd α hα).law β)) ≠ ⊤)
    {a b : ℝ} (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b) :
    ∀ᵐ r0 ∂(volume.restrict (Set.Ioo a b)),
      HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
        (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
          * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα hwin
    (fun t ht => (sourceModelWitness d hd α hα).cutMoment_ne_top_of_subcritical_first hβ hsub
      (p := 4) (by norm_num) (lt_trans hwin.1 ht.1))

/-! ## 5. Existence form: the off-sphere hypothesis disappears -/

/-- **The derivative holds at some radius of every nondegenerate off-corner window**, with the
off-sphere condition discharged. -/
theorem exists_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b) (hab : a < b)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc a b →
      (sourceModelWitness d hd α hα).cutMoment 4 t ≠ ⊤) :
    ∃ r0 : ℝ, r0 ∈ Set.Ioo a b ∧
      HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
        (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
          * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 := by
  obtain ⟨r0, hr0, hne⟩ :=
    SourceModelData.exists_mem_Ioo_notMem_sphereRadii (sourceModelWitness d hd α hα) hab
  exact ⟨r0, hr0, hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα hwin
    hr0.1 hr0.2 h4 (SourceModelData.offSphere_iff.mp hne)⟩

/-- **The derivative holds at some radius of every nondegenerate off-corner window, conditional
only on the sharpness input.** -/
theorem exists_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (hβ : 0 < (sourceModelWitness d hd α hα).betaCrit)
    (hsub : ∀ β : ℝ≥0, β < (sourceModelWitness d hd α hα).betaCrit →
      (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
        ∂((sourceModelWitness d hd α hα).law β)) ≠ ⊤)
    {a b : ℝ} (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b) (hab : a < b) :
    ∃ r0 : ℝ, r0 ∈ Set.Ioo a b ∧
      HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
        (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
          * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  exists_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα hwin hab
    (fun t ht => (sourceModelWitness d hd α hα).cutMoment_ne_top_of_subcritical_first hβ hsub
      (p := 4) (by norm_num) (lt_trans hwin.1 ht.1))

open PercLib.CriticalLRP.Orchestration in
/-- **The paper's `p = 2` off-corner derivative expression is nonnegative almost everywhere.**

The second cutoff moment is nondecreasing in the radius, so its derivative is nonnegative wherever
it exists; at almost every radius of an off-corner window the landed derivative identifies that
derivative with `powLawCoeff β_c d α r0 * (p2RHS r0)ᵗᵒᴿᵉᵃˡ`.  Hence the paper's right-hand side is
nonnegative a.e. on every nondegenerate off-corner window, conditionally only on `β_c > 0` and the
staged subcritical first-moment finiteness `hsub`.  This is a sign constraint on `p2RHS` obtained
without evaluating it. -/
theorem ae_nonneg_powLawCoeff_mul_p2RHS_sourceModelWitness_of_subcritical
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (hβ : 0 < (sourceModelWitness d hd α hα).betaCrit)
    (hsub : ∀ β : ℝ≥0, β < (sourceModelWitness d hd α hα).betaCrit →
      (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
        ∂((sourceModelWitness d hd α hα).law β)) ≠ ⊤)
    {a b : ℝ} (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b) (hab : a < b) :
    ∀ᵐ r0 ∂(volume.restrict (Set.Ioo a b)),
      0 ≤ powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal := by
  have h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ω =>
      pow_le_pow_right₀ (SourceModelData.one_le_clusterVol ω (0 : (sourceModelWitness d hd α
hα).V))
        (by norm_num : 2 ≤ 4))
    exact (sourceModelWitness d hd α hα).cutMoment_ne_top_of_subcritical_first hβ hsub
      (p := 4) (by norm_num) (lt_trans hwin.1 hab)
  filter_upwards [ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical
      d hd α hα hβ hsub hwin,
    SourceModelData.ae_deriv_nonneg_cutMomentReal
      (M := sourceModelWitness d hd α hα) hab 2 h2b] with r0 hd hnn
  simpa only [← hd.deriv] using hnn

/-! ## 6. The nondegenerate window `[7/2, 39/10]` -/

/-- **Almost-everywhere derivative on the concrete nondegenerate window `[7/2, 39/10]`**, above the
corner radius `2`, conditional only on `β_c > 0` and the staged subcritical first-moment finiteness
`hsub`. -/
theorem ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_seven_halves_of_subcritical
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (hβ : 0 < (sourceModelWitness d hd α hα).betaCrit)
    (hsub : ∀ β : ℝ≥0, β < (sourceModelWitness d hd α hα).betaCrit →
      (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
        ∂((sourceModelWitness d hd α hα).law β)) ≠ ⊤) :
    ∀ᵐ r0 ∂(volume.restrict (Set.Ioo (7 / 2 : ℝ) (39 / 10))),
      HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
        (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
          * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical d hd α hα hβ hsub
    (isOffCornerWindow_sourceModelWitness_seven_halves d hd α hα)

/-- **Existence of an off-sphere radius in the nondegenerate window `[7/2, 39/10]`** at which the
derivative formula holds, conditional only on `β_c > 0` and `hsub`. -/
theorem exists_hasDerivAt_cutMomentReal_two_sourceModelWitness_seven_halves_of_subcritical
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (hβ : 0 < (sourceModelWitness d hd α hα).betaCrit)
    (hsub : ∀ β : ℝ≥0, β < (sourceModelWitness d hd α hα).betaCrit →
      (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
        ∂((sourceModelWitness d hd α hα).law β)) ≠ ⊤) :
    ∃ r0 : ℝ, r0 ∈ Set.Ioo (7 / 2 : ℝ) (39 / 10) ∧
      HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
        (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
          * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  exists_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical d hd α hα hβ hsub
    (isOffCornerWindow_sourceModelWitness_seven_halves d hd α hα) (by norm_num)

end PercLib.CriticalLRP.Orchestration.Witness

/-! ## Axiom audit -/

set_option linter.hashCommand false

open PercLib.CriticalLRP.Orchestration in
#print axioms SourceModelData.sphereRadii_eq_attainedRadii_union
open PercLib.CriticalLRP.Orchestration in
#print axioms SourceModelData.sphereRadii_eq_cornerRadii_union
open PercLib.CriticalLRP.Orchestration in
#print axioms SourceModelData.offSphere_iff
open PercLib.CriticalLRP.Orchestration in
#print axioms SourceModelData.offSphere_iff_notMem_cornerRadii
open PercLib.CriticalLRP.Orchestration in
#print axioms SourceModelData.countable_sphereRadii
open PercLib.CriticalLRP.Orchestration in
#print axioms SourceModelData.volume_sphereRadii
open PercLib.CriticalLRP.Orchestration in
#print axioms SourceModelData.exists_mem_Ioo_notMem_sphereRadii
open PercLib.CriticalLRP.Orchestration.Witness in
#print axioms ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner
open PercLib.CriticalLRP.Orchestration.Witness in
#print axioms ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical
open PercLib.CriticalLRP.Orchestration.Witness in
#print axioms exists_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner
open PercLib.CriticalLRP.Orchestration.Witness in
#print axioms exists_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical
open PercLib.CriticalLRP.Orchestration.Witness in
#print axioms ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_seven_halves_of_subcritical
open PercLib.CriticalLRP.Orchestration.Witness in
#print axioms exists_hasDerivAt_cutMomentReal_two_sourceModelWitness_seven_halves_of_subcritical
open PercLib.CriticalLRP.Orchestration.Witness in
#print axioms ae_nonneg_powLawCoeff_mul_p2RHS_sourceModelWitness_of_subcritical
open PercLib.CriticalLRP.Orchestration.Witness in
#print axioms hasDerivAt_cutMomentReal_two_sourceModelWitness_offCornerRadii
open PercLib.CriticalLRP.Orchestration in
#print axioms SourceModelData.IsOffCornerWindow.mono
