/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Critical LRP I, `p = 2`: the source power-law coefficient inputs of the integrated radius identity.

Swarm `smwvfwkks`, member `m2`, direction (C).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PowerLawDeriv
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Completion
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.WindowFlux

/-!
# The `p = 2` radius identity at the source power law: coefficient inputs discharged

The integrated assembly `SourceModelData.hasDerivAt_cutMomentReal_two_integrated` (module
`SecondMoment/Integrated/Completion`) still takes inputs that are statements about the scalar
coefficient `M.coeffRHS r = β_c (-K'(r))` rather than about the flux:

* `hcoefcont` — `ContinuousAt M.coeffRHS r0` at the off-corner radius;
* a constant `C` with `0 ≤ C` and `|M.coeffRHS r| ≤ C` on the window `[a, r0]`;
* the resulting interval integrability of `M.rhsScalarTwo` (derived there from those two).

At the explicit power-law witness `sourceModelWitness d hd α hα` of
`Orchestration/ModelWitness/Defs.lean` these are *identities*, not inputs: by
`OffCorner/PowerLawDeriv.deriv_sourceModelWitness_K` the kernel derivative is
`K'(r) = -r^{-d-α-1}` at every positive radius (Definition I.1.3 with `δ ≡ 0`), so

`M.coeffRHS r = β_c r^{-d-α-1} = powLawCoeff β_c d α r`.

## What is proved

* `coeffRHS_sourceModelWitness_eq`, `rhsScalarTwo_sourceModelWitness_eq` — the coefficient and
  the right-hand side in the source's own power-law scale.
* `continuousAt_coeffRHS_sourceModelWitness`, `continuousOn_coeffRHS_sourceModelWitness`,
  `continuousOn_coeffRHS_sourceModelWitness_Icc` — `r ↦ β_c r^{-d-α-1}` is continuous at every
  positive radius and on every compact subinterval of `(0, ∞)`; `hcoefcont` is discharged.
* `coeffRHS_sourceModelWitness_nonneg`, `abs_coeffRHS_sourceModelWitness`,
  `antitoneOn_coeffRHS_sourceModelWitness` — `β_c |J'(r)|` has no sign change and decreases, so the
  supremum on `[a, ∞)` is attained at `a`.
* `abs_coeffRHS_sourceModelWitness_le` — the explicit bound
  `|M.coeffRHS r| ≤ powLawCoeffBound β_c d α a = |β_c| a^{-d-α-1}` for `r ≥ a > 0`: the
  quantitative compact-window coefficient bound, in the source's constants.
* `intervalIntegrable_rhsScalarTwo_sourceModelWitness` — `hfluxInt`-side consequence:
  `M.rhsScalarTwo` is interval integrable on `[a, r0]`, with `0 < a`, from the described bound.
* `continuousAt_rhsScalarTwo_sourceModelWitness` — the landed off-sphere continuity
  `continuousAt_rhsScalarTwo_of_no_sphere` with `hcoefcont` supplied.
* `sourceNormWitness_norm_toVec_eq_zero_or_one_le`, `toVec_eq_zero_iff`,
  `sourceModelWitness_sphere_ne` — the off-sphere condition is *satisfiable* at the witness for
  every radius `0 < r0 < 2`: the norm `ρ(v) = 2‖v‖` of an integral vector is `0` or at least `2`.
* `isOffCornerWindow_sourceModelWitness` — the off-corner window condition is satisfiable:
  `IsOffCornerWindow (1/2) 1`, because every edge length `2‖z‖` of a nonzero integral vector is
  at least `2`.
* `hasDerivAt_cutMomentReal_two_sourceModelWitness` — the integrated assembly at the witness with
  `hcoefcont`, `C`, `hC0`, `hC`, and the three per-window flux inputs (`hfluxMeas`, `hfluxNN`,
  `hfluxInt`, all unconditional at a finite window) removed; moment finiteness is required only at
  the right endpoint, by monotonicity of `cutMoment`.
* `hasDerivAt_cutMomentReal_two_sourceModelWitness_powerLaw` — the same in the paper's scale,
  with derivative `β_c r0^{-d-α-1} (p2RHS r0).toReal`.
* `hasDerivAt_cutMomentReal_two_sourceModelWitness_smallRadius` — the fully instantiated form on
  the fixed off-corner window `[1/2, 1]`, off sphere, whose only remaining inputs are the
  finiteness of the second and fourth cutoff moments and the two flux inputs `hfluxMono` and
  `hfluxConv`.
* `boxVerts`, `boxEdges` (`Defs.lean`), `boxVerts_mono`, `boxEdges_mono`,
  `exists_mem_boxVerts`, `exists_mem_boxEdges` — an explicit monotone family of finite edge
  windows, the boxes `[-n, n]^d`, exhausting `Sym2 (ℤ^d)`; the flux inputs can therefore be stated
  for one fixed family instead of an arbitrary one.
* `hasDerivAt_cutMomentReal_two_sourceModelWitness_box` — the same at the canonical box family.
* `cutKernel_sourceModelWitness_eq_zero`, `cutLaw_sourceModelWitness_eq_dirac`,
  `clusterVol_empty_config`, `cutMoment_sourceModelWitness_eq_one` — **below radius `2` the cut
  kernel of the witness vanishes identically** (every non-loop edge has `ρ`-length `≥ 2`), so the
  cut law is the point mass at the empty configuration, the origin is isolated, and
  `M.cutMoment p r = 1` for every `p : ℕ` and every `r < 2`.
* `cutMoment_two_one_sourceModelWitness`, `cutMoment_four_sourceModelWitness` — hence the moment
  finiteness inputs `cutMoment 2 1 ≠ ⊤` and `cutMoment 4 r1 ≠ ⊤` (`r1 < 2`) hold outright.
* `hasDerivAt_cutMomentReal_two_sourceModelWitness_box_noMoments` — **the end point of this
  direction**: for `d ≥ 1`, `α > 0`, every `r0 ∈ (1/2, 1)` and every `r1 ∈ (r0, 2)`,
  `HasDerivAt (fun r => M.cutMomentReal 2 r) (β_c r0^{-d-α-1} (p2RHS r0).toReal) r0` follows from
  the two flux inputs `hfluxMono`, `hfluxConv` along the box family alone.  Every coefficient,
  moment, window-geometry and sphere hypothesis is discharged.

## What is *not* claimed

This file retains its original conditional `hfluxMono`/`hfluxConv` interface rather than
deriving it. Those inputs are now supplied separately by `FluxConv/Envelope.Summable` for a
fixed radius, and `SourceWitness/OffCorner` additionally discharges the majorant and radius
exchange for the nondegenerate off-corner derivative with `h4` on the radius window. The
conditional interfaces in this file are therefore legacy shapes, not statements that those
results remain unproved. The separate `SourceWitness/SmallRadius.lean` also closes the literal
`r₀ < 2` instance directly, without needing a flux limit or a moment majorant. No `θ = 0`-type
hypothesis is used
to obtain a moment: the moments below radius `2` are computed from the kernel vanishing, not from
a criticality or finite-first-moment assumption.  Every statement below is about the literal
witness kernel of the repository; nothing is asserted for an abstract `SourceModelData`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-! ## 1. The coefficient and the right-hand side in the source's scale -/

/-- **The source coefficient is the literal power law.**  At every positive radius the coefficient
`β_c (-K'(r))` of the witness model is `powLawCoeff β_c d α r = β_c r^{-d-α-1}`. -/
theorem coeffRHS_sourceModelWitness_eq (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r : ℝ}
    (hr : 0 < r) :
    (sourceModelWitness d hd α hα).coeffRHS r
      = powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r :=
  sourceModelWitness_coeffRHS_eq d hd α hα hr

/-- **The `p = 2` right-hand side in the source's scale**:
`M.rhsScalarTwo r = β_c r^{-d-α-1} (p2RHS r).toReal` at every positive radius, i.e. the paper's
`β |J'(r)| (exclMassQuad r + 2 exclMassSqLin r)`. -/
theorem rhsScalarTwo_sourceModelWitness_eq (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r : ℝ}
    (hr : 0 < r) :
    (sourceModelWitness d hd α hα).rhsScalarTwo r
      = powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r
        * ((sourceModelWitness d hd α hα).p2RHS r).toReal := by
  rw [SourceModelData.rhsScalarTwo, coeffRHS_sourceModelWitness_eq d hd α hα hr]

/-! ## 2. Continuity of the coefficient at every positive radius -/

/-- **`hcoefcont` at the witness model.**  The coefficient `r ↦ β_c (-K'(r))` is continuous at
every positive radius, because the derivative of the literal power law is continuous there
(`continuousAt_deriv_sourceModelWitness_K`). -/
theorem continuousAt_coeffRHS_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) :
    ContinuousAt (sourceModelWitness d hd α hα).coeffRHS r := by
  unfold SourceModelData.coeffRHS
  exact (continuousAt_deriv_sourceModelWitness_K d hd α hα hr).neg.const_mul
    (((sourceModelWitness d hd α hα).betaCrit : ℝ))

/-- Continuity of the source coefficient on the whole positive halfline. -/
theorem continuousOn_coeffRHS_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    ContinuousOn (sourceModelWitness d hd α hα).coeffRHS (Set.Ioi 0) :=
  fun _r hr => (continuousAt_coeffRHS_sourceModelWitness d hd α hα hr).continuousWithinAt

/-- Continuity of the source coefficient on a compact radius window inside `(0, ∞)`. -/
theorem continuousOn_coeffRHS_sourceModelWitness_Icc (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (sourceModelWitness d hd α hα).coeffRHS (Set.Icc a b) :=
  fun _r hr =>
    (continuousAt_coeffRHS_sourceModelWitness d hd α hα (lt_of_lt_of_le ha hr.1)).continuousWithinAt

/-! ## 3. Sign and monotonicity of the modulus `β_c |J'|` -/

/-- **The source coefficient is nonnegative off the corner**: `β_c (-K'(r)) = β_c r^{-d-α-1} ≥ 0`,
the kernel being decreasing. -/
theorem coeffRHS_sourceModelWitness_nonneg (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r : ℝ}
    (hr : 0 < r) : 0 ≤ (sourceModelWitness d hd α hα).coeffRHS r := by
  rw [coeffRHS_sourceModelWitness_eq d hd α hα hr]
  unfold powLawCoeff
  exact mul_nonneg (by positivity) (Real.rpow_nonneg hr.le _)

/-- `|β_c (-K'(r))| = β_c (-K'(r))`: the source coefficient has no sign change. -/
theorem abs_coeffRHS_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r : ℝ}
    (hr : 0 < r) :
    |(sourceModelWitness d hd α hα).coeffRHS r| = (sourceModelWitness d hd α hα).coeffRHS r :=
  abs_of_nonneg (coeffRHS_sourceModelWitness_nonneg d hd α hα hr)

/-- **The source coefficient is decreasing on `(0, ∞)`**, at the exact power `r^{-d-α-1}`: the
modulus `β_c |J'(r)|` of Definition I.1.3 is antitone. -/
theorem antitoneOn_coeffRHS_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    AntitoneOn (sourceModelWitness d hd α hα).coeffRHS (Set.Ioi 0) := by
  intro s hs t _ht hst
  rw [coeffRHS_sourceModelWitness_eq d hd α hα hs,
    coeffRHS_sourceModelWitness_eq d hd α hα (lt_of_lt_of_le hs hst)]
  unfold powLawCoeff
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos hs hst (by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith)

/-! ## 4. The explicit compact-window coefficient bound -/

/-- The explicit constant `powLawCoeffBound β d α a = |β| a^{-d-α-1}` is nonnegative for `a > 0`. -/
theorem powLawCoeffBound_nonneg {β a : ℝ} {d : ℕ} {α : ℝ} (ha : 0 < a) :
    0 ≤ powLawCoeffBound β d α a := by
  unfold powLawCoeffBound
  exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ha.le _)

/-- **The compact-window bound on the source coefficient.**  On the halfline `[a, ∞)` with
`a > 0` the modulus of the witness coefficient is dominated by its exact value at `a`:
`|β_c (-K'(r))| ≤ |β_c| a^{-d-α-1}`.  This is the quantitative coefficient bound the integrated
assembly consumes as `hC`, in the source's own constants. -/
theorem abs_coeffRHS_sourceModelWitness_le (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {a r : ℝ} (ha : 0 < a) (har : a ≤ r) :
    |(sourceModelWitness d hd α hα).coeffRHS r|
      ≤ powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a := by
  have hr : 0 < r := lt_of_lt_of_le ha har
  have hβ : (0 : ℝ) ≤ ((sourceModelWitness d hd α hα).betaCrit : ℝ) := by positivity
  have hpow : r ^ (-(d : ℝ) - α - 1) ≤ a ^ (-(d : ℝ) - α - 1) :=
    Real.rpow_le_rpow_of_nonpos ha har (by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith)
  rw [abs_coeffRHS_sourceModelWitness d hd α hα hr,
    coeffRHS_sourceModelWitness_eq d hd α hα hr, powLawCoeffBound, powLawCoeff,
    abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left hpow hβ

/-- The bound is attained: at the left endpoint itself the coefficient equals the constant. -/
theorem abs_coeffRHS_sourceModelWitness_eq_bound (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {a : ℝ} (ha : 0 < a) :
    |(sourceModelWitness d hd α hα).coeffRHS a|
      = powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a := by
  rw [abs_coeffRHS_sourceModelWitness d hd α hα ha,
    coeffRHS_sourceModelWitness_eq d hd α hα ha, powLawCoeffBound, powLawCoeff,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((sourceModelWitness d hd α hα).betaCrit : ℝ))]

/-! ## 5. Interval integrability of the right-hand side, and off-sphere continuity -/

/-- Measurability of `M.rhsScalarTwo` from the pointwise window-flux convergence: it is the
`liminf` of the (measurable) window fluxes.  Extracted from the interior of
`hasDerivAt_cutMomentReal_two_of_finite` so that the interval-integrability consequence below does
not need a separate measurability input. -/
theorem measurable_rhsScalarTwo_of_tendsto_windowFlux (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)}
    (hmeas : ∀ n, Measurable ((sourceModelWitness d hd α hα).windowFlux (S n)))
    (hconv : ∀ t : ℝ, Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (S n) t)
      atTop (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t))) :
    Measurable fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t := by
  have hlim : (fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t)
      = fun t => liminf (fun n => (sourceModelWitness d hd α hα).windowFlux (S n) t) atTop := by
    funext t
    exact (hconv t).liminf_eq.symm
  rw [hlim]
  exact Measurable.liminf hmeas

/-- **`IntervalIntegrable` of the `p = 2` right-hand side at the witness model**, from the explicit
power-law coefficient bound: on `[a, r0]` with `0 < a`, `M.rhsScalarTwo = β_c r^{-d-α-1} * p2RHS`
is dominated by the constant `|β_c| a^{-d-α-1}` times the finite `p2RHS r0` bound. -/
theorem intervalIntegrable_rhsScalarTwo_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a r0 : ℝ} (ha : 0 < a) (har : a ≤ r0)
    (hmeas : Measurable fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t)
    (h4 : (sourceModelWitness d hd α hα).cutMoment 4 r0 ≠ ⊤) :
    IntervalIntegrable (fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t) volume a r0 :=
  (sourceModelWitness d hd α hα).intervalIntegrable_rhsScalarTwo_of_coeffBound har hmeas
    (powLawCoeffBound_nonneg (d := d) (α := α) (β := _) ha)
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le d hd α hα ha hr.1) h4

/-- **`IntervalIntegrable` of `M.rhsScalarTwo` with the measurability supplied by the window
flux.**  Same statement as above, but the measurability input is produced from a monotone
exhaustive window family and its pointwise convergence, as in the integrated assembly. -/
theorem intervalIntegrable_rhsScalarTwo_sourceModelWitness_of_flux (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a r0 : ℝ} (ha : 0 < a) (har : a ≤ r0)
    {S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)}
    (hfluxMeas : ∀ n, Measurable ((sourceModelWitness d hd α hα).windowFlux (S n)))
    (hfluxConv : ∀ t : ℝ, Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (S n) t)
      atTop (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t)))
    (h4 : (sourceModelWitness d hd α hα).cutMoment 4 r0 ≠ ⊤) :
    IntervalIntegrable (fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t) volume a r0 :=
  intervalIntegrable_rhsScalarTwo_sourceModelWitness d hd α hα ha har
    (measurable_rhsScalarTwo_of_tendsto_windowFlux d hd α hα hfluxMeas hfluxConv) h4

/-- **Off-sphere continuity of `M.rhsScalarTwo` at the witness model**, with the coefficient
continuity of §2 discharged: the landed `continuousAt_rhsScalarTwo_of_no_sphere` needs only the
off-sphere condition at `r0`, a strictly larger radius with finite fourth moment, and `hcoefcont`. -/
theorem continuousAt_rhsScalarTwo_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r0 r1 : ℝ} (hr0 : 0 < r0) (hr1 : r0 < r1)
    (h4 : (sourceModelWitness d hd α hα).cutMoment 4 r1 ≠ ⊤)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0) :
    ContinuousAt (fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t) r0 :=
  (sourceModelWitness d hd α hα).continuousAt_rhsScalarTwo_of_no_sphere' hr0 hr1 h4 hsphere
    (continuousAt_coeffRHS_sourceModelWitness d hd α hα hr0)

/-! ## 6. The witness model has no sphere below radius `2` and its window `[1/2, 1]` is off corner

The source norm of the witness is `ρ(v) = 2‖v‖`, and every nonzero integral vector has sup norm at
least `1`.  Hence the `ρ`-lengths of edges are `0` or at least `2`: no radius `0 < r0 < 2` is on a
sphere, and the window `[1/2, 1]` contains no edge length. -/

/-- `toVec` sends the zero integral vector to the zero real vector. -/
theorem toVec_zero {d : ℕ} : toVec (0 : Fin d → ℤ) = (0 : Fin d → ℝ) := by
  funext i
  simp [toVec]

/-- `toVec` is injective at zero: an integral vector whose real image vanishes is zero. -/
theorem toVec_eq_zero_iff {d : ℕ} {z : Fin d → ℤ} : toVec z = 0 ↔ z = 0 := by
  constructor
  · intro h
    funext i
    have hi : ((z i : ℤ) : ℝ) = 0 := congrFun h i
    exact_mod_cast hi
  · rintro rfl
    exact toVec_zero

/-- **A nonzero integral vector has sup norm at least `1`**, and the zero vector has norm `0`. -/
theorem sourceNormWitness_norm_toVec_eq_zero_or_one_le {d : ℕ} (y : Fin d → ℤ) :
    ‖toVec y‖ = 0 ∨ 1 ≤ ‖toVec y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact Or.inl (by rw [toVec_zero]; simp)
  · refine Or.inr ?_
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      simpa only [Pi.zero_apply] using (Function.ne_iff.mp hy)
    have h1 : (1 : ℝ) ≤ ‖toVec y i‖ := by
      have hcast : toVec y i = ((y i : ℤ) : ℝ) := rfl
      rw [hcast, Real.norm_eq_abs, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hi
    exact le_trans h1 (norm_le_pi_norm (toVec y) i)

/-- **The off-sphere condition at the witness model**, for every radius `0 < r0 < 2`: the
`ρ`-length of an integral vector is `0` or at least `2`. -/
theorem sourceModelWitness_sphere_ne (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r0 : ℝ}
    (hr0 : 0 < r0) (h2 : r0 < 2) :
    ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0 := by
  intro y hEq
  have hval : (sourceModelWitness d hd α hα).S.ρ (toVec y) = 2 * ‖toVec y‖ := rfl
  rw [hval] at hEq
  rcases sourceNormWitness_norm_toVec_eq_zero_or_one_le y with h0 | h1
  · rw [h0, mul_zero] at hEq
    linarith
  · linarith

/-- **The window `[1/2, 1]` is off corner at the witness model**: every `ρ`-length of a nonzero
edge is `2‖z‖ ≥ 2`, so no corner radius lies in `[1/2, 1]`. -/
theorem isOffCornerWindow_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    (sourceModelWitness d hd α hα).IsOffCornerWindow (1 / 2) 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rintro r ⟨hr1, hr2⟩ ⟨x, y, hxy, hdist⟩
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hnorm : 1 ≤ ‖toVec (x - y)‖ := by
    rcases sourceNormWitness_norm_toVec_eq_zero_or_one_le (x - y) with h0 | h1
    · exact absurd (toVec_eq_zero_iff.mp (norm_eq_zero.mp h0)) hsub
    · exact h1
  have hdist' : 2 * ‖toVec (x - y)‖ = r := by
    rw [SourceNormData.dist] at hdist
    exact hdist
  linarith

/-! ## 7. The integrated radius identity at the witness model -/

/-- **The `p = 2` off-corner radius derivative at the source power law.**

This is `SourceModelData.hasDerivAt_cutMomentReal_two_integrated` at `sourceModelWitness d hd α hα`
with every coefficient-side input discharged: `hcoefcont` is `continuousAt_coeffRHS_sourceModelWitness`,
the constant `C` is the explicit `powLawCoeffBound β_c d α a` with `hC0`/`hC` the bound of §4, and
the three per-window flux inputs `hfluxMeas`, `hfluxNN`, `hfluxInt` are the unconditional
`measurable_windowFlux`, `windowFlux_nonneg` and `intervalIntegrable_windowFlux_family`.
Finiteness of the second cutoff moment is required only at the right endpoint `b`, by monotonicity
of `M.cutMoment`.

The remaining inputs are the off-corner window, the monotone exhaustive window family, the
finiteness of the second and fourth cutoff moments, the off-sphere condition, and the two genuine
flux inputs `hfluxMono`, `hfluxConv`. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b r0 r1 : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hr1 : r0 < r1) (h4 : (sourceModelWitness d hd α hα).cutMoment 4 r1 ≠ ⊤)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0)
    (hfluxMono : ∀ (n : ℕ) (t : ℝ),
      (sourceModelWitness d hd α hα).windowFlux (S n) t
        ≤ (sourceModelWitness d hd α hα).windowFlux (S (n + 1)) t)
    (hfluxConv : ∀ t : ℝ, Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (S n) t)
      atTop (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t))) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      ((sourceModelWitness d hd α hα).rhsScalarTwo r0) r0 := by
  have ha : 0 < a := hwin.1
  have hr0 : 0 < r0 := lt_trans ha har
  have hfin : ∀ x ∈ Set.Icc a b, (sourceModelWitness d hd α hα).cutMoment 2 x ≠ ⊤ :=
    fun x hx => ne_top_of_le_ne_top h2b
      ((sourceModelWitness d hd α hα).cutMoment_monotone 2 hx.2)
  exact (sourceModelWitness d hd α hα).hasDerivAt_cutMomentReal_two_integrated hwin S hSmono hS
    har hrb hfin hr1 h4 hsphere
    (continuousAt_coeffRHS_sourceModelWitness d hd α hα hr0)
    (powLawCoeffBound_nonneg (d := d) (α := α)
      (β := ((sourceModelWitness d hd α hα).betaCrit : ℝ)) ha)
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le d hd α hα ha hr.1)
    (fun n => (sourceModelWitness d hd α hα).measurable_windowFlux (S n))
    (fun n t => (sourceModelWitness d hd α hα).windowFlux_nonneg (S n) t)
    hfluxMono hfluxConv

/-- **The same derivative in the paper's own scale**: at the source power law the off-corner
radius derivative of the second cutoff moment is `β_c r0^{-d-α-1} (p2RHS r0).toReal`. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_powerLaw (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b r0 r1 : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hr1 : r0 < r1) (h4 : (sourceModelWitness d hd α hα).cutMoment 4 r1 ≠ ⊤)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0)
    (hfluxMono : ∀ (n : ℕ) (t : ℝ),
      (sourceModelWitness d hd α hα).windowFlux (S n) t
        ≤ (sourceModelWitness d hd α hα).windowFlux (S (n + 1)) t)
    (hfluxConv : ∀ t : ℝ, Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (S n) t)
      atTop (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t))) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 := by
  have h := hasDerivAt_cutMomentReal_two_sourceModelWitness d hd α hα hwin S hSmono hS har hrb
    h2b hr1 h4 hsphere hfluxMono hfluxConv
  rwa [rhsScalarTwo_sourceModelWitness_eq d hd α hα (lt_trans hwin.1 har)] at h

/-- **The fully instantiated `p = 2` off-corner derivative at the source power law**, on the fixed
off-corner window `[1/2, 1]` and off sphere.

Both geometric inputs are discharged by §6: `isOffCornerWindow_sourceModelWitness` and
`sourceModelWitness_sphere_ne`.  What remains is exactly the moment finiteness (`cutMoment 2` at
`1`, `cutMoment 4` at `r1`) and the two flux inputs `hfluxMono`, `hfluxConv`, whose analysis is the
subject of the other directions. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_smallRadius (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ k, e ∈ S k)
    {r0 r1 : ℝ} (hr0lo : 1 / 2 < r0) (hr0hi : r0 < 1)
    (h2 : (sourceModelWitness d hd α hα).cutMoment 2 1 ≠ ⊤)
    (hr1 : r0 < r1) (h4 : (sourceModelWitness d hd α hα).cutMoment 4 r1 ≠ ⊤)
    (hfluxMono : ∀ (n : ℕ) (t : ℝ),
      (sourceModelWitness d hd α hα).windowFlux (S n) t
        ≤ (sourceModelWitness d hd α hα).windowFlux (S (n + 1)) t)
    (hfluxConv : ∀ t : ℝ, Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (S n) t)
      atTop (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t))) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_powerLaw d hd α hα
    (isOffCornerWindow_sourceModelWitness d hd α hα) S hSmono hS hr0lo hr0hi h2 hr1 h4
    (sourceModelWitness_sphere_ne d hd α hα (lt_trans (by norm_num) hr0lo)
      (lt_trans hr0hi (by norm_num)))
    hfluxMono hfluxConv

/-! ## 8. The canonical box family is monotone and exhaustive -/

/-- The vertex boxes `[-n, n]^d` are monotone in `n`. -/
theorem boxVerts_mono (d : ℕ) : Monotone (boxVerts d) := by
  intro m n hmn
  refine Fintype.piFinset_subset _ _ fun _i => ?_
  have hmn' : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  exact Finset.Icc_subset_Icc (by linarith) hmn'

/-- The canonical edge windows are monotone in `n`. -/
theorem boxEdges_mono (d : ℕ) : Monotone (boxEdges d) :=
  (Finset.monotone_sym2 (α := Fin d → ℤ)).comp (boxVerts_mono d)

/-- **Every vertex of the witness lattice lies in some box.** -/
theorem exists_mem_boxVerts (d : ℕ) (x : Fin d → ℤ) : ∃ n : ℕ, x ∈ boxVerts d n := by
  choose m hm using fun i => exists_nat_ge (|x i| : ℤ)
  refine ⟨∑ i, m i, ?_⟩
  rw [boxVerts, Fintype.mem_piFinset]
  intro i
  have hmi : m i ≤ ∑ j, m j :=
    Finset.single_le_sum (f := m) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hmi' : ((m i : ℕ) : ℤ) ≤ ((∑ j, m j : ℕ) : ℤ) := by exact_mod_cast hmi
  have hx := abs_le.mp (hm i)
  rw [Finset.mem_Icc]
  constructor <;> linarith

/-- **Every edge of the witness lattice lies in some canonical window**: the family exhausts
`Sym2 (Fin d → ℤ)`. -/
theorem exists_mem_boxEdges (d : ℕ) (e : Sym2 (Fin d → ℤ)) : ∃ n, e ∈ boxEdges d n := by
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨nx, hx⟩ := exists_mem_boxVerts d x
    obtain ⟨ny, hy⟩ := exists_mem_boxVerts d y
    exact ⟨max nx ny,
      Finset.mk_mem_sym2_iff.mpr
        ⟨boxVerts_mono d (le_max_left nx ny) hx, boxVerts_mono d (le_max_right nx ny) hy⟩⟩

/-- **The fully instantiated `p = 2` off-corner derivative at the source power law**, for the
canonical box windows `boxEdges d n` instead of an arbitrary monotone exhaustive family.

On the fixed off-corner window `[1/2, 1]` and off sphere, the only remaining inputs are the
finiteness of `cutMoment 2` at `1` and of `cutMoment 4` at `r1`, and the two flux inputs
`hfluxMono`, `hfluxConv` for the explicit family `boxEdges d n`. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_box (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r0 r1 : ℝ} (hr0lo : 1 / 2 < r0) (hr0hi : r0 < 1)
    (h2 : (sourceModelWitness d hd α hα).cutMoment 2 1 ≠ ⊤)
    (hr1 : r0 < r1) (h4 : (sourceModelWitness d hd α hα).cutMoment 4 r1 ≠ ⊤)
    (hfluxMono : ∀ (n : ℕ) (t : ℝ),
      (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t
        ≤ (sourceModelWitness d hd α hα).windowFlux (boxEdges d (n + 1)) t)
    (hfluxConv : ∀ t : ℝ,
      Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t)
        atTop (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t))) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_smallRadius d hd α hα (boxEdges d)
    (boxEdges_mono d) (exists_mem_boxEdges d) hr0lo hr0hi h2 hr1 h4 hfluxMono hfluxConv

/-! ## 9. Every cutoff moment of the witness is `1` below radius `2`

The witness norm is `ρ(v) = 2‖v‖`, so every non-loop edge has `ρ`-length at least `2`.  Below
radius `2` the cut kernel therefore vanishes identically, at every `β_c`: the cut law is the point
mass at the empty configuration, the cluster of the origin is a singleton, and `|K_0| = 1`.  Hence
`M.cutMoment p r = 1` for every `p` and every `r < 2` — in particular the finiteness inputs
`cutMoment 2 ≠ ⊤`, `cutMoment 4 ≠ ⊤` of the assembly are discharged outright on small windows. -/

/-- Two distinct lattice vertices are at `ρ`-distance at least `2`: the norm of a nonzero integral
vector is at least `1`. -/
theorem one_le_norm_toVec_of_ne {d : ℕ} {x y : Fin d → ℤ} (hxy : x ≠ y) :
    1 ≤ ‖toVec (x - y)‖ := by
  rcases sourceNormWitness_norm_toVec_eq_zero_or_one_le (x - y) with h0 | h1
  · exact absurd (toVec_eq_zero_iff.mp (norm_eq_zero.mp h0)) (sub_ne_zero.mpr hxy)
  · exact h1

/-- **The cut kernel of the witness vanishes below radius `2`.** -/
theorem cutKernel_sourceModelWitness_eq_zero (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r : ℝ} (hr : r < 2) :
    (sourceModelWitness d hd α hα).cutKernel r = fun _ => 0 := by
  funext e
  induction e using Sym2.ind with
  | h x y =>
    rw [SourceModelData.cutKernel, cutRadialSym, radialSym_mk]
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, ite_false]
      exact FiniteVolume.cutoffProfile_of_lt (by
        have h1 : 1 ≤ ‖toVec (x - y)‖ := one_le_norm_toVec_of_ne hxy
        have hval : (sourceModelWitness d hd α hα).S.dist x y = 2 * ‖toVec (x - y)‖ := rfl
        rw [hval]
        linarith)

/-- **The cut law of the witness at radius below `2` is the point mass at the empty
configuration**, for every `β_c`: all edge probabilities `1 - exp(-β_c · 0)` vanish. -/
theorem cutLaw_sourceModelWitness_eq_dirac (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r : ℝ} (hr : r < 2) :
    (sourceModelWitness d hd α hα).cutLaw r
      = Measure.dirac (∅ : Config (sourceModelWitness d hd α hα).V) := by
  have hJ : (sourceModelWitness d hd α hα).cutKernel r = fun _ => 0 :=
    cutKernel_sourceModelWitness_eq_zero d hd α hα hr
  have hprob : bernoulliEdgeProb ((sourceModelWitness d hd α hα).cutKernel r)
        ((sourceModelWitness d hd α hα).cutKernel_nonneg r)
        ((sourceModelWitness d hd α hα).betaCrit) = fun _ => (0 : unitInterval) := by
    funext e
    apply Subtype.ext
    rw [bernoulliEdgeProb_coe]
    have h0 : (sourceModelWitness d hd α hα).cutKernel r e = 0 := by rw [hJ]
    rw [h0, mul_zero, neg_zero, Real.exp_zero]
    norm_num
  change edgeMeasure (bernoulliEdgeProb ((sourceModelWitness d hd α hα).cutKernel r)
    ((sourceModelWitness d hd α hα).cutKernel_nonneg r)
    ((sourceModelWitness d hd α hα).betaCrit))
      = Measure.dirac (∅ : Config (sourceModelWitness d hd α hα).V)
  rw [hprob]
  exact edgeMeasure_zero

/-- With no open pair, the cluster volume of the origin is `1`. -/
theorem clusterVol_empty_config {V : Type*} [Countable V] (o : V) :
    clusterVol (∅ : Config V) o = 1 := by
  rw [clusterVol_eq_encard, cluster_empty, Set.encard_singleton]
  norm_num

/-- **Every cutoff moment of the witness is `1` below radius `2`**: no edge shorter than `2`
exists, so the origin is isolated. -/
theorem cutMoment_sourceModelWitness_eq_one (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (p : ℕ) {r : ℝ} (hr : r < 2) :
    (sourceModelWitness d hd α hα).cutMoment p r = 1 := by
  have hmeas : Measurable fun ω : Config (sourceModelWitness d hd α hα).V =>
      (clusterVol ω (0 : (sourceModelWitness d hd α hα).V)) ^ p :=
    (measurable_clusterVol (0 : (sourceModelWitness d hd α hα).V)).pow_const p
  rw [SourceModelData.cutMoment, cutLaw_sourceModelWitness_eq_dirac d hd α hα hr,
    lintegral_dirac' _ hmeas, clusterVol_empty_config, one_pow]

/-- The second cutoff moment at radius `1` is finite at the witness. -/
theorem cutMoment_two_one_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    (sourceModelWitness d hd α hα).cutMoment 2 1 ≠ ⊤ := by
  rw [cutMoment_sourceModelWitness_eq_one d hd α hα 2 (by norm_num)]
  exact ENNReal.one_ne_top

/-- The fourth cutoff moment at any radius below `2` is finite at the witness. -/
theorem cutMoment_four_sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r : ℝ} (hr : r < 2) :
    (sourceModelWitness d hd α hα).cutMoment 4 r ≠ ⊤ := by
  rw [cutMoment_sourceModelWitness_eq_one d hd α hα 4 hr]
  exact ENNReal.one_ne_top

/-- **The `p = 2` off-corner radius derivative at the source power law, with no moment
hypotheses.**

For every `r0 ∈ (1/2, 1)` and every `r1 ∈ (r0, 2)`, the cutoff moments `cutMoment 2 1` and
`cutMoment 4 r1` are both `1` (§9), so the only remaining inputs of
`hasDerivAt_cutMomentReal_two_sourceModelWitness_box` are the two flux inputs `hfluxMono` and
`hfluxConv` along the canonical box family `boxEdges d n`.  The conclusion is the source's own
value `β_c r0^{-d-α-1} (p2RHS r0).toReal`. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_box_noMoments (d : ℕ) (hd : 1 ≤ d)
    (α : ℝ) (hα : 0 < α) {r0 r1 : ℝ} (hr0lo : 1 / 2 < r0) (hr0hi : r0 < 1)
    (hr1 : r0 < r1) (hr12 : r1 < 2)
    (hfluxMono : ∀ (n : ℕ) (t : ℝ),
      (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t
        ≤ (sourceModelWitness d hd α hα).windowFlux (boxEdges d (n + 1)) t)
    (hfluxConv : ∀ t : ℝ, Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t)
      atTop (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t))) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_box d hd α hα hr0lo hr0hi
    (cutMoment_two_one_sourceModelWitness d hd α hα) hr1
    (cutMoment_four_sourceModelWitness d hd α hα hr12) hfluxMono hfluxConv

end PercLib.CriticalLRP.Orchestration.Witness

/-! ## 10. Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.Witness.coeffRHS_sourceModelWitness_eq
#print axioms PercLib.CriticalLRP.Orchestration.Witness.rhsScalarTwo_sourceModelWitness_eq
#print axioms PercLib.CriticalLRP.Orchestration.Witness.continuousAt_coeffRHS_sourceModelWitness
#print axioms PercLib.CriticalLRP.Orchestration.Witness.antitoneOn_coeffRHS_sourceModelWitness
#print axioms PercLib.CriticalLRP.Orchestration.Witness.abs_coeffRHS_sourceModelWitness_le
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.intervalIntegrable_rhsScalarTwo_sourceModelWitness
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.continuousAt_rhsScalarTwo_sourceModelWitness
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_sphere_ne
#print axioms PercLib.CriticalLRP.Orchestration.Witness.isOffCornerWindow_sourceModelWitness
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_smallRadius
#print axioms PercLib.CriticalLRP.Orchestration.Witness.boxEdges_mono
#print axioms PercLib.CriticalLRP.Orchestration.Witness.exists_mem_boxEdges
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_box
#print axioms PercLib.CriticalLRP.Orchestration.Witness.cutMoment_sourceModelWitness_eq_one
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_box_noMoments
