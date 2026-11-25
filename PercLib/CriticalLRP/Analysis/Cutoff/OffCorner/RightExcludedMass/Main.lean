module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RightExcludedMass.Defs

/-!
# Right-hand excluded-mass limit and the right corner derivative at attained radii

Direction B6 of swarm `smwv6er9k`.  The production modules are read from the read-only
orchestration worktree; this file adds no change to them.

## What is proved here

`E1Sign.exclMass M r` is the excluded mass `E_{β_c,r}[|K| Σ_{y∈B_r} 1(y∉K)|K_y|]` of the source
cutoff law at radius `r`, and `exclScalar r = (exclMass r).toReal`.

* `exclMass_eq_exclMassStrict_add_exclMassShell` — the exact window decomposition at *every*
  radius: the closed window `{ρ ≤ r}` splits into the strict window `{ρ < r}` and the shell
  `{ρ = r}`, and the shell term is named separately.
* `tendsto_exclScalar_nhdsGT` — **the right-hand excluded-mass limit at every positive radius**,
  with *no* no-sphere hypothesis: `exclScalar r → exclScalar r₀` as `r ↓ r₀`, from finiteness of
  the second and third cutoff moments at one radius `r₁ > r₀`.  This is the right-hand companion
  of the landed `continuousAt_exclScalar`, which needs the closed and strict windows to agree.
  At an attained radius the right limit is the closed-window value `exclScalar r₀` itself. The
  strict value is at most that value (`exclScalarStrict_le_exclScalar`), with the exact shell
  decomposition of the difference. The shell discrepancy is stated separately below.
* `tendsto_rhsScalar_nhdsGT` — the same statement for the derivative value
  `rhsScalar r = β_c(-K'(r)) (exclMass r).toReal`, the right-hand side of the source differential
  equation (I.4.6).
* `hasDerivWithinAt_Ici_of_hasDerivAt_Ioo` — the right-endpoint upgrade: differentiability with a
  derivative family on `(a, b)`, continuity at `a` and convergence of the family along `𝓝[>] a`
  give the right derivative at `a`.  (The left-endpoint analogue for `Iic` is landed in
  `Analysis/Cutoff/CornerOneSided`.)
* `hasDerivWithinAt_cutMassReal_rhsScalar_Ici` — the corner right derivative of the cutoff mass at
  an attained radius.  Its only remaining input is the off-corner derivative family on one right
  window `(r₀, r₁)`, which is exactly the conclusion of the landed off-corner Russo theorems (all
  of their analytic inputs remain theirs).  With that family available, the right derivative at the
  attained radius `r₀` exists and equals the **closed-window** value `rhsScalar r₀`.
The tail-threshold assembly and exact closed/strict discrepancy are proved in
`RightExcludedMass.Corner`; the left/right bridge is in `RightExcludedMass.Bridge`.  Nothing here
asserts that the source statement (I.4.1) is complete, and nothing here claims the left-hand
limit, which is a separate direction.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. Measurability of the excluded integrands -/

theorem measurable_exclTerm (y : M.V) :
    Measurable fun ω : Config M.V =>
      ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y := by
  have hset : MeasurableSet {ω : Config M.V | y ∉ cluster ω (0 : M.V)} :=
    (measurableSet_cluster_mem (0 : M.V) y).compl
  have hind : Measurable fun ω : Config M.V =>
      ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y :=
    Measurable.ite hset measurable_const measurable_const
  exact hind.mul (measurable_clusterVol y)

theorem measurable_exclWindowSum (s : Finset M.V) :
    Measurable fun ω : Config M.V =>
      ∑ y ∈ s,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y :=
  Finset.measurable_sum s fun y _ => M.measurable_exclTerm y

theorem measurable_exclMassStrictFun (r : ℝ) :
    Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) *
      ∑ y ∈ M.ballFLt r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y :=
  (measurable_clusterVol (0 : M.V)).mul (M.measurable_exclWindowSum _)

theorem measurable_exclShellFun (r : ℝ) : Measurable (M.exclShellFun r) :=
  (measurable_clusterVol (0 : M.V)).mul (M.measurable_exclWindowSum _)

/-! ## 2. The exact window decomposition at every radius -/

/-- **The closed window is the strict window plus the shell.**  At every radius, the excluded
mass splits into the strict-window mass and the shell mass, with the same law `cutLaw r` on both
sides. -/
theorem exclMass_eq_exclMassStrict_add_exclMassShell (r : ℝ) :
    E1Sign.exclMass M r = M.exclMassStrict r + M.exclMassShell r := by
  have hsub : M.ballFLt r ⊆ E1Sign.ballF M r := fun y hy =>
    (E1Sign.mem_ballF M).mpr (le_of_lt (M.mem_ballFLt.mp hy))
  have hsum : ∀ ω : Config M.V,
      (∑ y ∈ E1Sign.ballF M r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
        = (∑ y ∈ M.ballFLt r,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
          + ∑ y ∈ M.shellF r,
              ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y := by
    intro ω
    rw [← Finset.sum_sdiff hsub, M.ballFLt_sdiff_shellF, add_comm]
  have h1 : E1Sign.exclMass M r = ∫⁻ ω, (clusterVol ω (0 : M.V) *
        (∑ y ∈ M.ballFLt r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
      + clusterVol ω (0 : M.V) *
        (∑ y ∈ M.shellF r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y))
      ∂(M.cutLaw r) := by
    rw [E1Sign.exclMass]
    exact lintegral_congr fun ω => by rw [hsum ω, mul_add]
  rw [h1, lintegral_add_left (M.measurable_exclMassStrictFun r)]
  rfl

/-- The strict-window excluded mass is at most the closed-window one, at every radius. -/
theorem exclMassStrict_le_exclMass (r : ℝ) :
    M.exclMassStrict r ≤ E1Sign.exclMass M r := by
  rw [E1Sign.exclMass, exclMassStrict]
  refine lintegral_mono fun ω => ?_
  refine mul_le_mul' le_rfl ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun y hy => (E1Sign.mem_ballF M).mpr (le_of_lt (M.mem_ballFLt.mp hy)))
    (fun _ _ _ => zero_le)

/-- The strict-window excluded mass is finite as soon as the closed-window one is. -/
theorem exclMassStrict_ne_top {r b : ℝ} (hrb : r ≤ b) (h2b : M.cutMoment 2 b ≠ ⊤) :
    M.exclMassStrict r ≠ ⊤ :=
  ne_top_of_le_ne_top (M.exclMass_ne_top_of_le hrb h2b) (M.exclMassStrict_le_exclMass r)

/-! ## 3. Right-hand excluded-mass limit at every positive radius -/

/-- **Right continuity of the excluded mass at every positive radius.**  Unlike the two-sided
statement `continuousAt_exclScalar`, no condition on the sphere `{ρ = r₀}` is needed: the left
side is where the window moves, and on the right the closed window is already the one used in
`exclMass r₀`.  The two ingredients are the landed right continuity of the pair mass
(`tendsto_pairMassReal_nhdsGT`, second cutoff moment) and of the connected mass
(`tendsto_connMassReal_nhdsGT`, third cutoff moment), together with the exact decomposition
`pairMass = connMass + exclMass` on the window. -/
theorem tendsto_exclScalar_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤) :
    Tendsto M.exclScalar (𝓝[>] r0) (𝓝 (M.exclScalar r0)) := by
  have h2r0 : M.cutMoment 2 r0 ≠ ⊤ := M.cutMoment_ne_top_of_le (le_of_lt hr1) 2 h2
  have hpair := M.tendsto_pairMassReal_nhdsGT r0 hr0 hr1 h2
  have hconn := M.tendsto_connMassReal_nhdsGT r0 hr0 hr1 h3
  have hsub := hpair.sub hconn
  have hlim : (E1Sign.pairMass M r0).toReal - (E1Sign.connMass M r0).toReal
      = M.exclScalar r0 :=
    (M.exclScalar_eq_pairMassReal_sub_connMassReal_of_le (le_refl r0) h2r0).symm
  rw [hlim] at hsub
  refine hsub.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr1] with r hr
  exact (M.exclScalar_eq_pairMassReal_sub_connMassReal_of_le (le_of_lt hr.2) h2).symm

/-- **Right continuity of the derivative value `rhsScalar r = β_c(-K'(r)) (exclMass r).toReal`**
at every positive radius, from continuity of `r ↦ K'(r)` there and the right continuity of the
excluded mass. -/
theorem tendsto_rhsScalar_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤)
    (hK : ContinuousAt (fun r => deriv M.K r) r0) :
    Tendsto M.rhsScalar (𝓝[>] r0) (𝓝 (M.rhsScalar r0)) := by
  have hex := M.tendsto_exclScalar_nhdsGT r0 hr0 hr1 h2 h3
  have hcoeff : ContinuousAt M.coeffRHS r0 := hK.neg.const_mul ((M.betaCrit : ℝ))
  exact (hcoeff.tendsto.mono_left nhdsWithin_le_nhds).mul hex

end SourceModelData

/-! ## 4. The right-endpoint derivative upgrade -/

/-- **Right-endpoint upgrade.**  Differentiability with an explicit derivative family on the open
interval `(a, b)`, continuity of `f` at the left endpoint `a` within that interval, and convergence
of the family along `𝓝[>] a` give the right derivative of `f` at `a`.

This is the mirror image of the landed `hasDerivWithinAt_Iic_of_hasDerivAt_Ioo`; it is a
specialisation of Mathlib's `hasDerivWithinAt_Ici_of_tendsto_deriv`. -/
theorem hasDerivWithinAt_Ici_of_hasDerivAt_Ioo {f F : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt f (F x) x)
    (hcont : ContinuousWithinAt f (Set.Ioo a b) a)
    (hF : Tendsto F (𝓝[>] a) (𝓝 L)) :
    HasDerivWithinAt f L (Set.Ici a) a := by
  have hs : Set.Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
  have hdiffOn : DifferentiableOn ℝ f (Set.Ioo a b) :=
    fun x hx => (hdiff x hx).differentiableAt.differentiableWithinAt
  have hderiv : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 L) := by
    refine hF.congr' ?_
    filter_upwards [hs] with x hx
    exact (hdiff x hx).deriv.symm
  exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiffOn hcont hs hderiv

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 5. The right corner derivative of the cutoff mass at an attained radius -/

/-- **Right derivative of the cutoff mass at any positive radius, given the off-corner derivative
on one right window.**  On the right of an attained radius the closed window is already the
correct one, so the limiting derivative value is the full closed-window value `rhsScalar r₀`, not
its strict-window part.  The off-corner family on `(r₀, r₁)` is the exact input; every analytic
hypothesis behind it (moments, flux continuity, measurability, exhaustions, tail bounds) is
unchanged and stays with the landed off-corner theorems.

Hypotheses: `0 < r₀ < r₁`; finiteness of the second and third cutoff moments at `r₁` (the second
gives the right continuity of `rhsScalar`, the third the right continuity of the excluded mass);
continuity of `r ↦ K'(r)` at `r₀`; finiteness of the cutoff mass at `r₁`; and the off-corner
derivative family on `(r₀, r₁)`. -/
theorem hasDerivWithinAt_cutMassReal_rhsScalar_Ici {r0 r1 : ℝ} (hr0 : 0 < r0) (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤)
    (hK : ContinuousAt (fun r => deriv M.K r) r0)
    (hdiff : ∀ r ∈ Set.Ioo r0 r1, HasDerivAt M.cutMassReal (M.rhsScalar r) r)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) :
    HasDerivWithinAt M.cutMassReal (M.rhsScalar r0) (Set.Ici r0) r0 := by
  have hright := M.tendsto_cutMassReal_nhdsGT r0 hr0 hr1 hfin
  have hcont : ContinuousWithinAt M.cutMassReal (Set.Ioo r0 r1) r0 := by
    rw [ContinuousWithinAt]
    have hset : Set.Ioo r0 r1 = Set.Ioi r0 ∩ Set.Iio r1 := by
      ext x
      simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
    rw [hset, nhdsWithin_inter_of_mem'
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr1))]
    exact hright
  exact hasDerivWithinAt_Ici_of_hasDerivAt_Ioo hr1 hdiff hcont
    (M.tendsto_rhsScalar_nhdsGT r0 hr0 hr1 h2 h3 hK)

/-- Off the sphere the strict-window value coincides with the closed-window one: the corner
statement degenerates correctly.  (Consistency check, no new input.) -/
theorem exclMassStrict_eq_exclMass_of_no_sphere {r : ℝ}
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r) :
    M.exclMassStrict r = E1Sign.exclMass M r := by
  rw [E1Sign.exclMass, exclMassStrict, M.ballFLt_eq_ballF_of_no_sphere hsphere]

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_exclTerm

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_exclWindowSum

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_exclMassStrictFun

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_exclShellFun

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMass_eq_exclMassStrict_add_exclMassShell

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassStrict_le_exclMass

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassStrict_ne_top

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_exclScalar_nhdsGT

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_rhsScalar_nhdsGT

#print axioms PercLib.CriticalLRP.Orchestration.hasDerivWithinAt_Ici_of_hasDerivAt_Ioo

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivWithinAt_cutMassReal_rhsScalar_Ici

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassStrict_eq_exclMass_of_no_sphere

end PercLib.CriticalLRP.Orchestration
