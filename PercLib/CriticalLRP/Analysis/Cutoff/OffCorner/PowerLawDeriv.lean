/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Critical LRP I (arXiv:2508.18807v1): off-corner `C¹` regularity of the *literal* power-law
kernel, and discharge of the kernel-derivative hypotheses of the endpoint regularity wrappers
for the explicit source model.

Swarm `smwv2c2lw`, member `m4`, direction d1.  Scratch packet: no production writes, no axioms
beyond the three standard ones.
-/
module

public import PercLib.CriticalLRP.Orchestration.ModelWitness.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.KernelFactor.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusSummedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusFrozenCylinder
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusExcludedMass
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusOneSided

/-!
# `C¹` regularity of the explicit power-law source kernel

`SourceModelData` records only `DifferentiableOn ℝ K (Set.Ioi 0)` (`K_diff`), so every off-corner
endpoint statement in `Analysis/Cutoff/OffCorner` carries the window continuity of the kernel
derivative,

`hK : ∀ r ∈ Ioo α β, ContinuousAt (fun r' => deriv M.K r') r`,

as a hypothesis.  For an *abstract* model that hypothesis is a genuine extra input: `K_diff`
alone does not make `deriv K` continuous, and `exists_error` only pins the *absolute value*
`|deriv K r| = (1 + δ r) r^{-d-α-1}` against a log-error function `δ` that is assumed measurable
and `→ 0`, not continuous.  This file therefore proves the statement for the one model that the
repository actually exhibits -- the literal power law of `Orchestration/ModelWitness/Defs.lean`,
`K r = r^{-d-α}/(d+α)` with `d ≥ 1`, `α > 0` (`sourceModelWitness`) -- and then instantiates the
landed wrappers with the kernel side discharged.

## What is proved

* `hasDerivAt_powLawKernel`, `deriv_powLawKernel`: at every `x > 0` the literal `rpow` formula
  has derivative `-x^{-d-α-1}`; `abs_powLawKernelDeriv` identifies its absolute value with the
  source's `|J'(r)| = r^{-d-α-1}` (Definition I.1.3, display `(*)`, at `δ ≡ 0`).
* `continuousAt_deriv_powLawKernel`, `continuousOn_deriv_powLawKernel`: `r ↦ (r^{-d-α-1})(-1)`
  is continuous at every positive radius, hence `r ↦ deriv K r` is continuous on `Ioi 0`.
* `sourceModelWitness_hK`: the exact `hK` shape consumed by `RadiusSummedFlux`,
  `RadiusFrozenCylinder`, `RadiusPivotalWeight`, `RadiusMeasurability/Main`, `ScalarFactor/Main`
  and `KernelFactor/Main`, at the model's own parameters `d ≥ 1`, `α > 0`; the wrappers' window
  hypothesis `0 < α` is discharged in the form `0 < a` and no condition on `b` is needed.
* `sourceModelWitness_hCb`, `sourceModelWitness_hKβ`, `sourceModelWitness_deriv_ne_zero`: the
  derivative bound `-(K' r) ≤ a^{-d-α-1}` on `Ioo a b`, the sign `K' b < 0` and the nonvanishing
  `K' r ≠ 0`, the other three kernel-side hypotheses of the same wrappers.
* `sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope` and
  `..._of_measurability` and `..._of_endpoint_of_pivotalMass`: the landed off-corner endpoint
  derivative theorems instantiated at the explicit model, with `hK`, `hKd`, `hCb`, `hC0`, `hKβ`
  **removed**.  What remains is visible and non-kernel: the radius window `a < r0 < b` off the
  corner set, the finite second cutoff moment `cutMoment 2 b ≠ ⊤`, the per-vertex flux continuity
  `hcontinf` (or, in the `pivotalMass` form, its sufficient condition `hB`, continuity of the
  normalized pivotal mass), and `exclScalar` continuity.
* `sourceModelWitness_hGcont`: the summed-flux continuity `hGcont` of the same wrappers for the
  explicit model, from `hK` and `exclScalar` continuity.
* `sourceModelWitness_continuousAt_tsum_sMomentInfFlux_iff_continuousAt_exclScalar`: at an
  off-corner radius of the window, and given `β_c ≠ 0`, summed-flux continuity for the explicit
  model is *equivalent* to `exclScalar` continuity -- the sharp form of the previous item.
* `sourceModelWitness_continuousAt_cutEdgeDeriv`: every non-loop, strictly shorter edge of the
  explicit model has a continuous activated weight off corner (given `β_c ≠ 0`), and
  `sourceModelWitness_continuousAt_cutKernelFactor`: its kernel factor is continuous at every
  positive radius.
* `sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_cylinderApprox`: the
  furthest-reduced endpoint statement of the tree at the explicit model, where the
  `exclScalar` continuity is replaced by the explicit uniform cylinder approximation `hcyl`.
* `sourceModelWitness_eventually_abs_sMomentInfFlux_le_strictWeight`: the left one-sided envelope
  of `RadiusOneSided` at *every* positive radius for the explicit model, with its two missing
  inputs proved and only `cutMoment 1 r₀ ≠ ⊤` left.
* `sourceModelWitness_coeffRHS_eq`, `sourceModelWitness_rhsScalar_eq`,
  `sourceModelWitness_hasDerivAt_cutMassReal_powerLaw`: the same endpoint statement written in the
  paper's scale, `d/dt cutMassReal = β_c r0 ^ (-(d) - α - 1) (exclMass r0)` at `r0`.

## What is *not* claimed

Nothing is asserted about an abstract `SourceModelData`, and no moment, critical-parameter
(`β_c ≠ 0`) or probability statement is derived.  In particular `hcontinf`, `hB` and `hGcont`
remain inputs; this file only removes the kernel-derivative ones.  No new definitions are
introduced, so no separate `Defs` module is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-! ## 1. The literal power law: derivative, sign, and absolute value -/

/-- **Derivative of the literal power-law kernel.**  For the exact `rpow` expression
`r ↦ r ^ (-(d) - α) / (d + α)` of `SourceModelData.K` at the witness model, the derivative at a
positive radius is `-x ^ (-(d) - α - 1)`.  This is the pointwise content of Definition I.1.3 with
logarithmic error `δ ≡ 0`. -/
theorem hasDerivAt_powLawKernel {d : ℕ} {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun r : ℝ => r ^ (-(d : ℝ) - α) / ((d : ℝ) + α))
      (-(x ^ (-(d : ℝ) - α - 1))) x := by
  have hc : (0 : ℝ) < (d : ℝ) + α := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have h : HasDerivAt (fun r : ℝ => r ^ (-(d : ℝ) - α) / ((d : ℝ) + α))
      (((-(d : ℝ) - α) * x ^ (-(d : ℝ) - α - 1)) / ((d : ℝ) + α)) x :=
    (Real.hasDerivAt_rpow_const (p := -(d : ℝ) - α) (Or.inl hx.ne')).div_const ((d : ℝ) + α)
  refine h.congr_deriv ?_
  have hc' : ((d : ℝ) + α) ≠ 0 := hc.ne'
  field_simp
  ring

/-- The literal power-law kernel is differentiable at every positive radius. -/
theorem differentiableAt_powLawKernel {d : ℕ} {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (fun r : ℝ => r ^ (-(d : ℝ) - α) / ((d : ℝ) + α)) x :=
  (hasDerivAt_powLawKernel hα hx).differentiableAt

/-- Pointwise derivative formula for the literal power law. -/
theorem deriv_powLawKernel {d : ℕ} {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 0 < x) :
    deriv (fun r : ℝ => r ^ (-(d : ℝ) - α) / ((d : ℝ) + α)) x = -(x ^ (-(d : ℝ) - α - 1)) :=
  (hasDerivAt_powLawKernel hα hx).deriv

/-- The derivative formula as a function of the radius is continuous at every positive
radius. -/
theorem continuousAt_powLawKernelDeriv {α : ℝ} {d : ℕ} {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun r : ℝ => -(r ^ (-(d : ℝ) - α - 1))) x :=
  (Real.continuousAt_rpow_const x (-(d : ℝ) - α - 1) (Or.inl hx.ne')).neg

/-- The derivative formula as a function of the radius is continuous on `Ioi 0`. -/
theorem continuousOn_powLawKernelDeriv {d : ℕ} {α : ℝ} :
    ContinuousOn (fun r : ℝ => -(r ^ (-(d : ℝ) - α - 1))) (Ioi 0) :=
  fun _ hx => (continuousAt_powLawKernelDeriv (d := d) (α := α) hx).continuousWithinAt

/-- **`C¹` at a point for the literal power law.**  The *derivative* `r ↦ deriv K r` (not merely
the kernel) is continuous at every positive radius. -/
theorem continuousAt_deriv_powLawKernel {d : ℕ} {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 0 < x) :
    ContinuousAt
      (fun r : ℝ => deriv (fun s : ℝ => s ^ (-(d : ℝ) - α) / ((d : ℝ) + α)) r) x := by
  refine (continuousAt_powLawKernelDeriv (d := d) (α := α) hx).congr ?_
  filter_upwards [Ioi_mem_nhds hx] with r hr
  exact (deriv_powLawKernel hα hr).symm

/-- **`C¹` on `Ioi 0` for the literal power law.** -/
theorem continuousOn_deriv_powLawKernel {d : ℕ} {α : ℝ} (hα : 0 < α) :
    ContinuousOn
      (fun r : ℝ => deriv (fun s : ℝ => s ^ (-(d : ℝ) - α) / ((d : ℝ) + α)) r) (Ioi 0) :=
  fun _ hx => (continuousAt_deriv_powLawKernel hα hx).continuousWithinAt

/-- The derivative `-x^{-d-α-1}` is strictly negative at a positive radius. -/
theorem powLawKernelDeriv_neg {d : ℕ} {α : ℝ} {x : ℝ} (hx : 0 < x) :
    -(x ^ (-(d : ℝ) - α - 1)) < 0 := by
  have hpos : (0 : ℝ) < x ^ (-(d : ℝ) - α - 1) := Real.rpow_pos_of_pos hx _
  linarith

/-- The derivative `-x^{-d-α-1}` does not vanish at a positive radius. -/
theorem powLawKernelDeriv_ne_zero {d : ℕ} {α : ℝ} {x : ℝ} (hx : 0 < x) :
    -(x ^ (-(d : ℝ) - α - 1)) ≠ 0 :=
  ne_of_lt (powLawKernelDeriv_neg (d := d) (α := α) hx)

/-- **The source's derivative modulus.**  `|K' r| = r^{-d-α-1}` exactly: Definition I.1.3 with
`δ ≡ 0`. -/
theorem abs_powLawKernelDeriv {d : ℕ} {α : ℝ} {x : ℝ} (hx : 0 < x) :
    |-(x ^ (-(d : ℝ) - α - 1))| = x ^ (-(d : ℝ) - α - 1) := by
  have hpos : (0 : ℝ) < x ^ (-(d : ℝ) - α - 1) := Real.rpow_pos_of_pos hx _
  rw [abs_neg, abs_of_pos hpos]

end PercLib.CriticalLRP.Orchestration.Witness

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-! ## 2. The witness model: `K` is the literal power law -/

/-- The kernel of the explicit witness model *is* the literal power-law formula, definitionally. -/
theorem sourceModelWitness_K_eq (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    (sourceModelWitness d hd α hα).K
      = fun r : ℝ => r ^ (-(d : ℝ) - α) / ((d : ℝ) + α) := rfl

/-- The witness kernel is differentiable at every positive radius. -/
theorem differentiableAt_sourceModelWitness_K (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ (sourceModelWitness d hd α hα).K x := by
  rw [sourceModelWitness_K_eq d hd α hα]
  exact differentiableAt_powLawKernel hα hx

/-- **Derivative of the witness kernel.**  At every positive radius the derivative of the
explicit model's kernel is `-r ^ (-(d) - α - 1)`. -/
theorem deriv_sourceModelWitness_K (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {x : ℝ}
    (hx : 0 < x) :
    deriv (sourceModelWitness d hd α hα).K x = -(x ^ (-(d : ℝ) - α - 1)) := by
  rw [sourceModelWitness_K_eq d hd α hα]
  exact deriv_powLawKernel hα hx

/-- The witness kernel's derivative satisfies the source's modulus formula with `δ ≡ 0`:
`|K' r| = r ^ (-(d) - α - 1)`.  In particular the `exists_error` field of the witness is met by
the zero error function, and this is the derivative itself, not a bound. -/
theorem abs_deriv_sourceModelWitness_K (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {x : ℝ}
    (hx : 0 < x) :
    |deriv (sourceModelWitness d hd α hα).K x| = (1 + 0) * x ^ (-(d : ℝ) - α - 1) := by
  rw [deriv_sourceModelWitness_K d hd α hα hx, add_zero, one_mul]
  exact abs_powLawKernelDeriv hx

/-- **`C¹` at a point for the witness model.** -/
theorem continuousAt_deriv_sourceModelWitness_K (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun r => deriv (sourceModelWitness d hd α hα).K r) x := by
  rw [sourceModelWitness_K_eq d hd α hα]
  exact continuousAt_deriv_powLawKernel hα hx

/-- **`C¹` on `Ioi 0` for the witness model.** -/
theorem continuousOn_deriv_sourceModelWitness_K (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    ContinuousOn (fun r => deriv (sourceModelWitness d hd α hα).K r) (Ioi 0) := by
  rw [sourceModelWitness_K_eq d hd α hα]
  exact continuousOn_deriv_powLawKernel hα

/-- The witness kernel's derivative is strictly negative at a positive radius. -/
theorem deriv_sourceModelWitness_K_neg (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {x : ℝ}
    (hx : 0 < x) : deriv (sourceModelWitness d hd α hα).K x < 0 := by
  rw [deriv_sourceModelWitness_K d hd α hα hx]
  exact powLawKernelDeriv_neg hx

/-- The witness kernel's derivative does not vanish at a positive radius. -/
theorem deriv_sourceModelWitness_K_ne_zero (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {x : ℝ}
    (hx : 0 < x) : deriv (sourceModelWitness d hd α hα).K x ≠ 0 :=
  ne_of_lt (deriv_sourceModelWitness_K_neg d hd α hα hx)

/-! ## 3. The kernel-side hypotheses of the off-corner wrappers, discharged -/

/-- **The window hypothesis `hK` of every off-corner endpoint wrapper, for the explicit model.**
`r ↦ deriv K r` is continuous on the whole window `Ioo a b` as soon as its left endpoint `a` is
positive; no bound on `b` is needed. -/
theorem sourceModelWitness_hK (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ}
    (ha : 0 < a) :
    ∀ r ∈ Set.Ioo a b, ContinuousAt (fun r' => deriv (sourceModelWitness d hd α hα).K r') r :=
  fun _r hr => continuousAt_deriv_sourceModelWitness_K d hd α hα (lt_trans ha hr.1)

/-- The differentiability hypothesis `hKd` of the same wrappers, for the explicit model. -/
theorem sourceModelWitness_hKd (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ}
    (ha : 0 < a) :
    ∀ r ∈ Set.Ioo a b, DifferentiableAt ℝ (sourceModelWitness d hd α hα).K r :=
  fun _r hr => differentiableAt_sourceModelWitness_K d hd α hα (lt_trans ha hr.1)

/-- **The derivative envelope `hCb` of the off-corner wrappers, for the explicit model**, with
the explicit constant `a ^ (-(d) - α - 1)`: on `Ioo a b` the derivative modulus is at most its
value at the left endpoint. -/
theorem sourceModelWitness_hCb (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) (a b : ℝ)
    (ha : 0 < a) :
    ∀ r ∈ Set.Ioo a b,
      -(deriv (sourceModelWitness d hd α hα).K r) ≤ a ^ (-(d : ℝ) - α - 1) := by
  intro r hr
  rw [deriv_sourceModelWitness_K d hd α hα (lt_trans ha hr.1)]
  have hq : -(d : ℝ) - α - 1 ≤ 0 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  simpa only [neg_neg] using Real.rpow_le_rpow_of_nonpos ha (le_of_lt hr.1) hq

/-- The sign hypothesis `hKβ` of the off-corner wrappers, for the explicit model. -/
theorem sourceModelWitness_hKβ (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {b : ℝ}
    (hb : 0 < b) : deriv (sourceModelWitness d hd α hα).K b < 0 :=
  deriv_sourceModelWitness_K_neg d hd α hα hb

/-- The nonvanishing hypothesis `hK0 : deriv M.K r₀ ≠ 0` of the kernel-factor wrappers, for the
explicit model. -/
theorem sourceModelWitness_deriv_ne_zero (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r₀ : ℝ}
    (hr₀ : 0 < r₀) : deriv (sourceModelWitness d hd α hα).K r₀ ≠ 0 :=
  deriv_sourceModelWitness_K_ne_zero d hd α hα hr₀

end PercLib.CriticalLRP.Orchestration.Witness

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-! ## 4. The landed off-corner endpoint theorems at the explicit model, kernel side discharged

Each theorem below is exactly a landed wrapper of `Analysis/Cutoff/OffCorner` with the model `M`
specialized to `sourceModelWitness d hd α hα` and the four kernel-side hypotheses `hKd`, `hK`,
`hC0`/`hCb` and `hKβ` **removed** because §2–§3 prove them.  The hypotheses that remain are the
ones that are genuinely about the cutoff law: the radius window and its off-corner condition, the
finite second cutoff moment at the right endpoint, `hcontinf` (or its sufficient condition `hB`),
and `exclScalar` continuity. -/

/-- **Per-vertex flux continuity at the explicit model.**  From continuity of the normalized
pivotal mass at a positive radius, the off-corner singleton flux of the power-law model is
continuous there. -/
theorem sourceModelWitness_continuousAt_sMomentInfFlux (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r₀ : ℝ} (hr₀ : 0 < r₀) (y : (sourceModelWitness d hd α hα).V)
    (hB : ContinuousAt ((sourceModelWitness d hd α hα).normalizedPivotMass y) r₀) :
    ContinuousAt (sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
      ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
      (sourceModelWitness d hd α hα).cutProb
      (sourceModelWitness d hd α hα).cutEdgeDeriv) r₀ :=
  (sourceModelWitness d hd α hα).continuousAt_sMomentInfFlux_of_continuousAt_deriv hr₀
    (continuousAt_deriv_sourceModelWitness_K d hd α hα hr₀) hB

/-- **`hcontinf` for the explicit model** in the exact window shape consumed by the endpoint
wrappers, from continuity of the normalized pivotal mass on the window. -/
theorem sourceModelWitness_hcontinf (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ}
    (ha : 0 < a)
    (hB : ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b,
      ContinuousAt ((sourceModelWitness d hd α hα).normalizedPivotMass y) r) :
    ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv) r :=
  (sourceModelWitness d hd α hα).hcontinf_of_continuousAt_deriv_of_continuousAt_normalizedPivotMass
    ha (sourceModelWitness_hK d hd α hα ha) hB

/-- **Individual activated edge weights of the explicit model are continuous off corner.**  The
`iff` of `KernelFactor/Main` transfers the proved continuity of `deriv K` to the weight of every
non-loop edge shorter than the radius; `β_c ≠ 0` is kept as an explicit hypothesis. -/
theorem sourceModelWitness_continuousAt_cutEdgeDeriv (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) (hβ : ((sourceModelWitness d hd α hα).betaCrit : ℝ) ≠ 0)
    {x y : (sourceModelWitness d hd α hα).V} (hxy : x ≠ y) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdist : (sourceModelWitness d hd α hα).S.dist x y < r₀) :
    ContinuousAt (fun r => (sourceModelWitness d hd α hα).cutEdgeDeriv r s(x, y)) r₀ :=
  ((sourceModelWitness d hd α hα).continuousAt_cutEdgeDeriv_iff_continuousAt_deriv hβ hxy hr₀
    hdist).mpr (continuousAt_deriv_sourceModelWitness_K d hd α hα hr₀)

/-- **The kernel factor of the explicit model is continuous at a positive radius**, from the
proved continuity of `deriv K` (`KernelFactor/Main`, sufficiency direction). -/
theorem sourceModelWitness_continuousAt_cutKernelFactor (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ContinuousAt (fun r => (sourceModelWitness d hd α hα).cutKernelFactor r) r₀ :=
  (sourceModelWitness d hd α hα).continuousAt_cutKernelFactor_of_continuousAt_deriv hr₀
    (continuousAt_deriv_sourceModelWitness_K d hd α hα hr₀)

/-- **The envelope endpoint derivative theorem at the explicit model.**  This is
`SourceModelData.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_scalar` with
`hKd`, `hK`, `hC0`, `hCb = a ^ (-(d) - α - 1)` and `hKβ` discharged. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0) (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hcontinf : ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv) r)
    (hex : ∀ r ∈ Set.Ioo a b, ContinuousAt (sourceModelWitness d hd α hα).exclScalar r) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      ((sourceModelWitness d hd α hα).rhsScalar r0) r0 :=
  SourceModelData.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_scalar
    (sourceModelWitness d hd α hα) T hTmono hT S hSmono hS (α := a) (β := b) (r0 := r0)
    (C := a ^ (-(d : ℝ) - α - 1)) ha har0 hr0b hoff
    (sourceModelWitness_hKd d hd α hα ha) h2b (Real.rpow_nonneg ha.le _)
    (sourceModelWitness_hCb d hd α hα a b ha)
    (sourceModelWitness_hKβ d hd α hα (lt_trans ha (lt_trans har0 hr0b)))
    hcontinf (sourceModelWitness_hK d hd α hα ha) hex

/-- **The same envelope endpoint theorem with `hcontinf` reduced to its sufficient condition**
`hB`: continuity of the normalized pivotal mass on the window.  The kernel derivative and the flux
no longer appear among the hypotheses. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_pivotalMass
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0) (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hB : ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b,
      ContinuousAt ((sourceModelWitness d hd α hα).normalizedPivotMass y) r)
    (hex : ∀ r ∈ Set.Ioo a b, ContinuousAt (sourceModelWitness d hd α hα).exclScalar r) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      ((sourceModelWitness d hd α hα).rhsScalar r0) r0 :=
  sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope d hd α hα T hTmono
    hT S hSmono hS ha har0 hr0b hoff h2b
    (sourceModelWitness_hcontinf d hd α hα ha hB) hex

end PercLib.CriticalLRP.Orchestration.Witness

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-- **`hGcont` for the explicit model** in the exact window shape consumed by
`RadiusPivotalWeight` and `RadiusMeasurability/Main`: the total vertex sum of singleton fluxes is
continuous on the window, from the proved kernel-derivative continuity and `exclScalar`
continuity.  The finite second cutoff moment at the right endpoint stays an input. -/
theorem sourceModelWitness_hGcont (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ}
    (ha : 0 < a) (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (hex : ∀ r ∈ Set.Ioo a b, ContinuousAt (sourceModelWitness d hd α hα).exclScalar r) :
    ∀ r ∈ Set.Ioo a b, ContinuousAt (fun r' => ∑' y : (sourceModelWitness d hd α hα).V,
      sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv r') r :=
  (sourceModelWitness d hd α hα).hGcont_of_scalar_continuity ha h2b hoff
    (sourceModelWitness_hK d hd α hα ha) hex

/-- **The measurability endpoint derivative theorem at the explicit model.**  This is
`SourceModelData.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability_of_scalar` with
`hKd`, `hK` and `hGcont` discharged; the dominator's interval integrability `hboundint` is
retained. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0) (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hboundint : ∀ y : (sourceModelWitness d hd α hα).V, ∀ a' ∈ Set.Ioo a b,
      ∀ b' ∈ Set.Ioo a b, IntervalIntegrable
        (sMomentWeight (0 : (sourceModelWitness d hd α hα).V)
          ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
          (sourceModelWitness d hd α hα).cutProb
          (sourceModelWitness d hd α hα).cutEdgeDeriv) volume a' b')
    (hcontinf : ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv) r)
    (hex : ∀ r ∈ Set.Ioo a b, ContinuousAt (sourceModelWitness d hd α hα).exclScalar r) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      ((sourceModelWitness d hd α hα).rhsScalar r0) r0 :=
  SourceModelData.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability_of_scalar
    (sourceModelWitness d hd α hα) T hTmono hT S hSmono hS (α := a) (β := b) (r0 := r0)
    ha har0 hr0b hoff (sourceModelWitness_hKd d hd α hα ha) h2b hboundint hcontinf
    (sourceModelWitness_hK d hd α hα ha) hex

end PercLib.CriticalLRP.Orchestration.Witness

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-- **Sharpness at the explicit model: summed-flux continuity *is* excluded-mass continuity.**
This is `SourceModelData.continuousAt_tsum_sMomentInfFlux_iff_continuousAt_exclScalar` with the
two kernel-side hypotheses `hK` and `hK0` discharged, at an off-corner radius of the window.  So
for the power-law model the summed flux has no separate analytic content beyond
`r ↦ exclScalar r`; the critical-parameter hypothesis `β_c ≠ 0` and the finite second moment at
`β` remain inputs. -/
theorem sourceModelWitness_continuousAt_tsum_sMomentInfFlux_iff_continuousAt_exclScalar
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {a b r₀ : ℝ} (ha : 0 < a) (har₀ : a < r₀) (hr₀b : r₀ < b)
    (hoff : r₀ ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hβ : ((sourceModelWitness d hd α hα).betaCrit : ℝ) ≠ 0) :
    ContinuousAt (fun r' => ∑' y : (sourceModelWitness d hd α hα).V,
      sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv r') r₀ ↔
      ContinuousAt (sourceModelWitness d hd α hα).exclScalar r₀ :=
  (sourceModelWitness d hd α hα).continuousAt_tsum_sMomentInfFlux_iff_continuousAt_exclScalar
    ha har₀ hr₀b hoff h2b hβ (continuousAt_deriv_sourceModelWitness_K d hd α hα
      (lt_trans ha har₀)) (deriv_sourceModelWitness_K_ne_zero d hd α hα (lt_trans ha har₀))

/-- **The furthest-reduced endpoint derivative of the tree at the explicit model**: the
`RadiusFrozenCylinder.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_cylinderApprox`
statement with `hKd`, `hK`, `hC0`, `hCb`, `hKβ` discharged.  The opaque `exclScalar` continuity is
replaced, exactly as in the landed wrapper, by the explicit uniform cylinder-approximation datum
`hcyl` for the frozen window, which is *not* proved here and remains the open condition. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_cylinderApprox
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0) (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hcontinf : ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv) r)
    (hcyl : ∀ r ∈ Set.Ioo a b, ∀ ε > 0,
      ∃ (S' : Finset (Sym2 (sourceModelWitness d hd α hα).V))
        (g : (↥S' → Prop) → ℝ), 0 ≤ g ∧ ∃ δ > 0,
      ∀ s, |s - r| < δ →
        |(∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V) *
            ∑ y ∈ E1Sign.ballF (sourceModelWitness d hd α hα) r,
            ((cluster ω (0 : (sourceModelWitness d hd α hα).V))ᶜ).indicator
              (fun _ => (1 : ℝ≥0∞)) y *
              clusterVol ω y ∂((sourceModelWitness d hd α hα).cutLaw s)).toReal
          - (∫⁻ ω, ENNReal.ofReal (g (S'.restrict ω))
              ∂((sourceModelWitness d hd α hα).cutLaw s)).toReal| ≤ ε) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      ((sourceModelWitness d hd α hα).rhsScalar r0) r0 :=
  SourceModelData.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_cylinderApprox
    (sourceModelWitness d hd α hα) T hTmono hT S hSmono hS (α := a) (β := b) (r0 := r0)
    (C := a ^ (-(d : ℝ) - α - 1)) ha har0 hr0b hoff
    (sourceModelWitness_hKd d hd α hα ha) h2b (Real.rpow_nonneg ha.le _)
    (sourceModelWitness_hCb d hd α hα a b ha)
    (sourceModelWitness_hKβ d hd α hα (lt_trans ha (lt_trans har0 hr0b)))
    hcontinf (sourceModelWitness_hK d hd α hα ha) hcyl

/-- **The left one-sided envelope of `RadiusOneSided` at the explicit model.**  At *every*
positive radius -- corner or not -- the singleton flux is eventually, from the left, at most
`1 + ε` times the strict-weight pivotal total there.  The two inputs that file names as absent
from `SourceModelData` (`ContinuousAt (fun r => deriv M.K r) r₀` and `deriv M.K r₀ < 0`) are
discharged by §2; the finite first cutoff moment `M.cutMoment 1 r₀ ≠ ⊤` stays an input. -/
theorem sourceModelWitness_eventually_abs_sMomentInfFlux_le_strictWeight
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hvol : (sourceModelWitness d hd α hα).cutMoment 1 r₀ ≠ ⊤)
    (y : (sourceModelWitness d hd α hα).V) :
    ∀ ε > 0, ∀ᶠ r in 𝓝[<] r₀,
      |sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
          ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
          (sourceModelWitness d hd α hα).cutProb
          (sourceModelWitness d hd α hα).cutEdgeDeriv r| ≤
        (1 + ε) * ∑' e : Sym2 (sourceModelWitness d hd α hα).V,
          |(sourceModelWitness d hd α hα).cutEdgeDerivLeft r₀ e| *
            (2 * ((sourceModelWitness d hd α hα).cutLaw r₀).real
              {ω : Config (sourceModelWitness d hd α hα).V | e ∈ touchSet ω (0 : _)}) :=
  (sourceModelWitness d hd α hα).eventually_abs_sMomentInfFlux_le_strictWeight_of_continuousAt_deriv
    hr₀ (deriv_sourceModelWitness_K_neg d hd α hα hr₀)
    (continuousAt_deriv_sourceModelWitness_K d hd α hα hr₀) hvol y


/-! ## 5. The derivative value in the paper's own scale

The off-corner derivative value of the cutoff mass is `rhsScalar r0 = β_c (-K'(r0)) (exclMass r0)`
(`ScalarFactor/Defs`).  With §2 the coefficient is the explicit power `β_c r0 ^ (-(d) - α - 1)`, so
the endpoint theorems above read: *the derivative of the cutoff mass at `r0` is
`β_c r0 ^ (-(d) - α - 1) (exclMass r0)`.* -/

/-- **The coefficient `β_c (-K'(r))` of the explicit model** is `β_c r ^ (-(d) - α - 1)`. -/
theorem sourceModelWitness_coeffRHS_eq (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r : ℝ}
    (hr : 0 < r) :
    (sourceModelWitness d hd α hα).coeffRHS r
      = ((sourceModelWitness d hd α hα).betaCrit : ℝ) * r ^ (-(d : ℝ) - α - 1) := by
  rw [SourceModelData.coeffRHS, deriv_sourceModelWitness_K d hd α hα hr, neg_neg]

/-- **The derivative value `rhsScalar` of the explicit model** is
`β_c r ^ (-(d) - α - 1) (exclMass r).toReal`. -/
theorem sourceModelWitness_rhsScalar_eq (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r : ℝ}
    (hr : 0 < r) :
    (sourceModelWitness d hd α hα).rhsScalar r
      = ((sourceModelWitness d hd α hα).betaCrit : ℝ) * r ^ (-(d : ℝ) - α - 1) *
          (sourceModelWitness d hd α hα).exclScalar r := by
  rw [SourceModelData.rhsScalar, sourceModelWitness_coeffRHS_eq d hd α hα hr]

/-- **The off-corner endpoint derivative of the explicit model, in the paper's scale.**  This is
`sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope` with the derivative
value written out: `d/dt cutMassReal = β_c r0 ^ (-(d) - α - 1) (exclMass r0)` at `r0`. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_powerLaw
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0) (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hcontinf : ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv) r)
    (hex : ∀ r ∈ Set.Ioo a b, ContinuousAt (sourceModelWitness d hd α hα).exclScalar r) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d hd α hα).exclScalar r0) r0 := by
  have h := sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope
    d hd α hα T hTmono hT S hSmono hS ha har0 hr0b hoff h2b hcontinf hex
  rwa [sourceModelWitness_rhsScalar_eq d hd α hα (lt_trans ha har0)] at h

end PercLib.CriticalLRP.Orchestration.Witness

/-! ## 5.1. The endpoint derivative with explicit second and third moments
-/

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-- The envelope endpoint derivative at the explicit model, with both the kernel and summed-flux
regularity inputs supplied. Only off-corner geometry, moments, and per-vertex flux continuity
remain as analytic inputs. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_moments
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0) (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤)
    (hcontinf : ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv) r) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      ((sourceModelWitness d hd α hα).rhsScalar r0) r0 := by
  exact SourceModelData.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_moments
    (sourceModelWitness d hd α hα) T hTmono hT S hSmono hS (α := a) (β := b) (r0 := r0)
    (C := a ^ (-(d : ℝ) - α - 1)) ha har0 hr0b hoff
    (sourceModelWitness_hKd d hd α hα ha) h2b h3b (Real.rpow_nonneg ha.le _)
    (sourceModelWitness_hCb d hd α hα a b ha)
    (sourceModelWitness_hKβ d hd α hα (lt_trans ha (lt_trans har0 hr0b)))
    hcontinf (sourceModelWitness_hK d hd α hα ha)

/-- The same endpoint derivative in the paper's explicit power-law scale. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (T : ℕ → Finset (sourceModelWitness d hd α hα).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd α hα).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ n, e ∈ S n)
    {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0) (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤)
    (hcontinf : ∀ y : (sourceModelWitness d hd α hα).V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : (sourceModelWitness d hd α hα).V)
        ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
        (sourceModelWitness d hd α hα).cutProb
        (sourceModelWitness d hd α hα).cutEdgeDeriv) r) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d hd α hα).exclScalar r0) r0 := by
  have h := sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_moments
    d hd α hα T hTmono hT S hSmono hS ha har0 hr0b hoff h2b h3b hcontinf
  rwa [sourceModelWitness_rhsScalar_eq d hd α hα (lt_trans ha har0)] at h

end PercLib.CriticalLRP.Orchestration.Witness

/-! ## 6. Axiom audit

The `#print axioms` commands below are audit output, not library content, so the `hashCommand`
and long-line style linters are switched off from here to the end of the file. -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_powLawKernel
#print axioms PercLib.CriticalLRP.Orchestration.Witness.deriv_powLawKernel
#print axioms PercLib.CriticalLRP.Orchestration.Witness.continuousAt_deriv_powLawKernel
#print axioms PercLib.CriticalLRP.Orchestration.Witness.continuousOn_deriv_powLawKernel
#print axioms PercLib.CriticalLRP.Orchestration.Witness.deriv_sourceModelWitness_K
#print axioms PercLib.CriticalLRP.Orchestration.Witness.abs_deriv_sourceModelWitness_K
#print axioms PercLib.CriticalLRP.Orchestration.Witness.continuousAt_deriv_sourceModelWitness_K
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hK
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hCb
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_continuousAt_cutEdgeDeriv
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hGcont
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_pivotalMass
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_continuousAt_tsum_sMomentInfFlux_iff_continuousAt_exclScalar
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_continuousAt_cutKernelFactor
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_cylinderApprox
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_eventually_abs_sMomentInfFlux_le_strictWeight
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_coeffRHS_eq
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_rhsScalar_eq
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw

#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_moments

#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_moments
