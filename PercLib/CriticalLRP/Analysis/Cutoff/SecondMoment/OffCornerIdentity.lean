/-
Integrated and independently rebuilt from accepted Ultramath `smwywszgo`, member `m2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwywszgo`, member `m2`, direction `d1`.

# The integrated `p = 2` radius identity on off-corner windows, with every flux input derived

The landed chain left, on an off-corner window `[a, b]`, two *flux* hypotheses open:

* `hfluxMaj`/`hG` — a uniform-in-window majorant of `M.windowFlux (S n)` and its interval
  integrability.  These were closed in `WindowMajorant/Main.lean`:
  `windowFlux_le_windowMajorant_of_cutMoment_four_le` gives the pointwise domination by
  `M.windowMajorant C b`, and `intervalIntegrable_windowMajorant` gives its interval integrability
  — the latter from *global* measurability of `M.rhsScalarTwo`.
* `hfluxConv` — the fixed-radius insertion convergence
  `M.windowFlux (S n) t → M.rhsScalarTwo t`.  `FluxConv/Envelope/Summable.lean` proves it
  (`tendsto_windowFlux_of_cutMoment_four`) from *one* radius of finiteness of the fourth cutoff
  moment, but the landed assemblies still take it as a hypothesis, in the global form
  `∀ t, …` (`ac_and_ae_hasDerivAt_cutMomentReal_two_assembled`) or in the window-local form
  `∀ t ∈ Ioc a b, …` (`Integrated/LocalFTC.lean`).

This file removes both, on an off-corner window, and so produces the integrated identity and the
`hac`/`hae` pair of the `p = 2` radius picture with **no flux hypothesis at all**.  The only
analytic inputs left are the coefficient bound `|M.coeffRHS| ≤ C` on the window and finiteness of
the second cutoff moment at the right endpoint `b`.

## The two reductions

**Finiteness at `b` gives finiteness everywhere on `[a, b]`.**  `M.cutMoment 4` is monotone in the
radius (`M.cutMoment_monotone`), so `M.cutMoment 4 t ≤ M.cutMoment 4 b` for `t ≤ b`, and
`M.cutMoment 4 b ≠ ⊤` propagates down to every `t ∈ [a, b]`.  The fourth moment at `b` in turn
follows from the second at `b` by `CaseOne.cutMoment_four_ne_top_of_two`
(the mixed Case-1 estimate `E|K|⁴ ≤ 15 E|K|² (E|K|)⁴`).

This is what makes `hfluxConv` derivable on the window: `tendsto_windowFlux_of_cutMoment_four`
needs the fourth moment only at the single radius at which it is evaluated, and every such radius
lies in `(a, b]`.

**Measurability is not needed globally.**  `intervalIntegrable_windowMajorant` asks for
`Measurable fun t => M.rhsScalarTwo t` on the whole line.  Only a.e. strong measurability on the
window `(a, b]` is consumed, and that is `aeStronglyMeasurable_rhsScalarTwo_restrict`, which is a
`liminf` of the (measurable) window fluxes along the convergence we have just derived
(`intervalIntegrable_windowMajorant_ae` below).

## What is proved

* `cutMoment_four_ne_top_of_cutMoment_two_le` — the fourth moment is finite on `[a, b]` from the
  second moment at `b`;
* `tendsto_windowFlux_of_cutMoment_four_le`, `tendsto_windowFlux_of_cutMoment_two_le` — `hfluxConv`
  on `(a, b]`, with no hypothesis beyond finiteness of the fourth (resp. second) moment at `b` and a
  monotone edge-exhausting window family;
* `intervalIntegrable_windowMajorant_ae` — the interval integrability half of the majorant with
  measurability only on the window;
* `integral_rhsScalarTwo_eq_sub_of_offCornerWindow_of_cutMoment_four` and
  `integral_rhsScalarTwo_eq_sub_of_offCornerWindow` — **the integrated identity on an off-corner
  window with no flux hypothesis**: the majorant and the window-local convergence are both derived;
* `ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner` — absolute continuity, the a.e. radius
  derivative, the a.e. `deriv` equality, the integrated identity, and interval integrability of
  `M.rhsScalarTwo`, all on an off-corner window, from the same inputs;
* `hasDerivAt_cutMomentReal_two_offCorner` — the pointwise radius derivative at an off-sphere
  interior radius `r0 ∈ (a, b)`, from the same inputs plus the off-sphere condition and continuity
  of `M.coeffRHS` at `r0`;
* §4: the witness instances.  `[1/2, 1]` is below the radius where the witness cut kernel vanishes,
  so the second moment there is `1` and the whole off-corner picture holds **unconditionally**
  (`ac_and_ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_box_unconditional`); and at the
  nondegenerate radius `37/10` on `[7/2, 39/10]` the only remaining hypothesis is
  `M.cutMoment 2 (39/10) ≠ ⊤`, the coefficient bound being the exact power law.

## What is not proved here

Windows that *contain* corner radii are not touched: `M.IsOffCornerWindow a b` is a hypothesis of
every statement below, and it is what makes the finite-window Russo identity integrable over the
whole window.  No derivative is claimed at an attained radius, no finite box replaces the model, and
no infinite moment is passed through `toReal`.  The passage from off-corner subwindows to arbitrary
radius intervals is a separate, purely real-analytic bridge (continuity of the moment in the radius
plus `finite_cornerRadii_inter_Ioo`), which this file does not attempt.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentTail
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.LocalFTC
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.WindowMajorant.Witness

/-!
# Off-corner radius identity with the flux inputs discharged
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. Finiteness of the fourth cutoff moment on the window -/

/-- **The fourth cutoff moment is finite on `[a, b]` as soon as the second is finite at `b`.**

Both monotonicities are used: `M.cutMoment 2 t ≤ M.cutMoment 2 b` for `t ≤ b`
(`M.cutMoment_monotone`), and the Case-1 mixed estimate
`M.cutMoment 4 b ≤ 15 M.cutMoment 2 b (M.cutMoment 1 b)⁴`
(`CaseOne.cutMoment_four_ne_top_of_two`).  No hypothesis is made on the law at any other radius:
the finiteness statement is a statement about the numbers `M.cutMoment p r`, and those are monotone
in `r` regardless of how the law itself varies. -/
theorem cutMoment_four_ne_top_of_cutMoment_two_le {a b : ℝ} (h2b : M.cutMoment 2 b ≠ ⊤)
    (hab : a ≤ b) : ∀ t ∈ Set.Icc a b, M.cutMoment 4 t ≠ ⊤ := by
  have h4b : M.cutMoment 4 b ≠ ⊤ := CaseOne.cutMoment_four_ne_top_of_two M h2b
  intro t ht
  exact ne_top_of_le_ne_top h4b (M.cutMoment_monotone 4 ht.2)

/-! ## 2. The fixed-radius flux convergence on the window -/

/-- **`hfluxConv` on `(a, b]` from finiteness of the fourth moment at `b`.**

`tendsto_windowFlux_of_cutMoment_four` needs the fourth moment at the one radius at which it is
evaluated; at `t ∈ (a, b]` that radius satisfies `t ≤ b`, so finiteness at `b` suffices by
monotonicity.  The off-corner condition is *not* used: the convergence is a fixed-radius insertion
statement, unconditional in the window. -/
theorem tendsto_windowFlux_of_cutMoment_four_le {a b : ℝ} (ha : 0 < a)
    (h4b : M.cutMoment 4 b ≠ ⊤) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k) :
    ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)) := by
  intro t ht
  exact M.tendsto_windowFlux_of_cutMoment_four t (lt_trans ha ht.1)
    (ne_top_of_le_ne_top h4b (M.cutMoment_monotone 4 ht.2)) S hSmono hS

/-- **`hfluxConv` on `(a, b]` from finiteness of the second moment at `b`** — the Case-1 shape, in
which the second moment is the input and the fourth is derived. -/
theorem tendsto_windowFlux_of_cutMoment_two_le {a b : ℝ} (ha : 0 < a)
    (h2b : M.cutMoment 2 b ≠ ⊤) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k) :
    ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)) :=
  M.tendsto_windowFlux_of_cutMoment_four_le ha
    (CaseOne.cutMoment_four_ne_top_of_two M h2b) S hSmono hS

/-! ## 3. The majorant's interval integrability, measured only on the window -/

/-- **`IntervalIntegrable (M.windowMajorant C b) volume a b` with measurability only on `(a, b]`.**

`intervalIntegrable_windowMajorant` of `WindowMajorant/Main.lean` asks for `Measurable` on the whole
line; the only analytic input it uses is
`intervalIntegrable_rhsScalarTwo_of_coeffBound`, whose measurability hypothesis is consumed by
`IntervalIntegrable.mono_fun'` on `(a, b]`.  The a.e. form
`intervalIntegrable_rhsScalarTwo_of_coeffBound_ae` therefore suffices, and the affine rewriting of
the majorant is unchanged (`windowMajorant_eq_affine`). -/
theorem intervalIntegrable_windowMajorant_ae {a b C : ℝ} (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable (fun t => M.rhsScalarTwo t)
      (volume.restrict (Set.uIoc a b)))
    (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C) (h4b : M.cutMoment 4 b ≠ ⊤) :
    IntervalIntegrable (M.windowMajorant C b) volume a b := by
  have hbase : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound_ae hab hmeas hC0 hC h4b
  rw [M.windowMajorant_eq_affine C b]
  exact (hbase.const_mul 2).add
    (intervalIntegrable_const (c := 2 * M.windowMajorantConst C b))

/-! ## 4. The integrated identity on an off-corner window, no flux hypothesis -/

/-- **The integrated `p = 2` radius identity on an off-corner window, from the fourth moment at
`b`.**

This is `integral_rhsScalarTwo_eq_sub_of_window_majorant_pos` with *both* residual flux inputs
discharged:

* `hfluxMaj` is `windowFlux_le_windowMajorant_of_cutMoment_four_le` at the explicit majorant
  `G = M.windowMajorant C b`;
* `hG` is `intervalIntegrable_windowMajorant_ae`, whose a.e. measurability input is the `liminf`
  of the window fluxes on the window (`aeStronglyMeasurable_rhsScalarTwo_restrict`);
* `hfluxConv` is `tendsto_windowFlux_of_cutMoment_four_le`.

The window-moment convergence `hmoment` is `tendsto_windowMoment_sub`, applied at each `x ∈ [a, b]`
with the second moment finite there (from the fourth at `b`, or from
`CaseOne.cutMoment_four_ne_top_of_two`).

Remaining inputs: the off-corner window, a monotone edge-exhausting family, the coefficient bound on
`[a, b]`, and `M.cutMoment 4 b ≠ ⊤`.  No `∀ t, …` convergence, no majorant, no global
measurability, no off-sphere condition and no continuity of `M.rhsScalarTwo` appear. -/
theorem integral_rhsScalarTwo_eq_sub_of_offCornerWindow_of_cutMoment_four {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k) (h4b : M.cutMoment 4 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C) :
    ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a := by
  have ha : 0 < a := hwin.1
  have hab : a ≤ b := hwin.2.1
  have hfluxConv : ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)) :=
    M.tendsto_windowFlux_of_cutMoment_four_le ha h4b S hSmono hS
  have hAE : AEStronglyMeasurable (fun t => M.rhsScalarTwo t)
      (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact M.aeStronglyMeasurable_rhsScalarTwo_restrict S hfluxConv
  have hG : IntervalIntegrable (M.windowMajorant C b) volume a b :=
    M.intervalIntegrable_windowMajorant_ae hab hAE hC0 hC h4b
  have hGon : IntegrableOn (M.windowMajorant C b) (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hG
  have hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b,
      M.windowFlux (S n) t ≤ M.windowMajorant C b t :=
    M.windowFlux_le_windowMajorant_of_cutMoment_four_le ha hab h4b hC0 hC S
  have h2b : ∀ x ∈ Set.Icc a b, M.cutMoment 2 x ≠ ⊤ := by
    intro x hx
    exact ne_top_of_le_ne_top
      (ne_top_of_le_ne_top h4b (M.cutMoment_monotone 4 hx.2))
      (M.cutMoment_two_le_cutMoment_four x)
  have hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)) :=
    fun x hx => M.tendsto_windowMoment_sub S hSmono hS (h2b x hx)
      (h2b a ⟨le_rfl, hab⟩)
  exact M.integral_rhsScalarTwo_eq_sub_of_window_majorant_pos hwin S hfluxMaj hGon hfluxConv
    hmoment

/-- **The same from finiteness of the second moment at `b`** — the Case-1 input shape. -/
theorem integral_rhsScalarTwo_eq_sub_of_offCornerWindow {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k) (h2b : M.cutMoment 2 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C) :
    ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a :=
  M.integral_rhsScalarTwo_eq_sub_of_offCornerWindow_of_cutMoment_four hwin S hSmono hS
    (CaseOne.cutMoment_four_ne_top_of_two M h2b) hC0 hC

/-! ## 5. `hac` and `hae` on the off-corner window -/

/-- **The `p = 2` radius picture on an off-corner window, with the flux inputs discharged.**

Outputs, from `Smwyvlg99M1.ac_and_ae_hasDerivAt_cutMomentReal_two_of_identity`:

* `AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b`;
* for a.e. radius of `(a, b)`, `HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r`;
* `deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Ioo a b)] M.rhsScalarTwo`;
* the integrated identity on `[a, b]`;
* `IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b`.

The two inputs of that interface are both produced here: interval integrability by
`intervalIntegrable_rhsScalarTwo_of_coeffBound_ae` (a.e. measurability on the window, from the
derived convergence), and the identity by
`integral_rhsScalarTwo_eq_sub_of_offCornerWindow_of_cutMoment_four`.

Nothing is claimed at the endpoint `b`, and nothing is claimed at a radius in `M.cornerRadii`:
this is an off-corner window statement. -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k) (h4b : M.cutMoment 4 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C) :
    AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b ∧
      (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r) ∧
      (deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo a b)]
        fun t => M.rhsScalarTwo t) ∧
      (∀ x ∈ Set.Icc a b,
        ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) ∧
      IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b := by
  have ha : 0 < a := hwin.1
  have hab : a ≤ b := hwin.2.1
  have hfluxConv : ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)) :=
    M.tendsto_windowFlux_of_cutMoment_four_le ha h4b S hSmono hS
  have hAE : AEStronglyMeasurable (fun t => M.rhsScalarTwo t)
      (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact M.aeStronglyMeasurable_rhsScalarTwo_restrict S hfluxConv
  have hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound_ae hab hAE hC0 hC h4b
  exact Smwyvlg99M1.ac_and_ae_hasDerivAt_cutMomentReal_two_of_identity M hab hint
    (M.integral_rhsScalarTwo_eq_sub_of_offCornerWindow_of_cutMoment_four hwin S hSmono hS h4b
      hC0 hC)

/-- **The same from finiteness of the second moment at `b`.** -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k) (h2b : M.cutMoment 2 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C) :
    AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b ∧
      (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r) ∧
      (deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo a b)]
        fun t => M.rhsScalarTwo t) ∧
      (∀ x ∈ Set.Icc a b,
        ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) ∧
      IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
  M.ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner hwin S hSmono hS
    (CaseOne.cutMoment_four_ne_top_of_two M h2b) hC0 hC

/-! ## 6. The pointwise radius derivative on an off-corner window -/

/-- **The off-corner radius derivative at an off-sphere interior radius, with no flux
hypothesis.**

This is `hasDerivAt_cutMomentReal_two_of_window_majorant_pos` with `hfluxMaj`, `hG`, `hfluxConv`,
`hmoment` and `hrhsInt` all derived; the pointwise derivative at `r0` needs in addition the
off-sphere condition `hsphere` and continuity of `M.coeffRHS` at `r0`, which are exactly the inputs
of `continuousAt_rhsScalarTwo_of_no_sphere`.

Unlike the a.e. statement of §5 this *does* claim the derivative at a particular radius `r0`, and
that radius is by hypothesis not a `ρ`-length. -/
theorem hasDerivAt_cutMomentReal_two_offCorner {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b) (h4b : M.cutMoment 4 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (hcoef : ContinuousAt M.coeffRHS r0) (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have ha : 0 < a := hwin.1
  have hab : a ≤ b := hwin.2.1
  have hr0 : 0 < r0 := lt_trans ha har
  have hfluxConv : ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)) :=
    M.tendsto_windowFlux_of_cutMoment_four_le ha h4b S hSmono hS
  have hAE : AEStronglyMeasurable (fun t => M.rhsScalarTwo t)
      (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact M.aeStronglyMeasurable_rhsScalarTwo_restrict S hfluxConv
  have hG : IntervalIntegrable (M.windowMajorant C b) volume a b :=
    M.intervalIntegrable_windowMajorant_ae hab hAE hC0 hC h4b
  have hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b,
      M.windowFlux (S n) t ≤ M.windowMajorant C b t :=
    M.windowFlux_le_windowMajorant_of_cutMoment_four_le ha hab h4b hC0 hC S
  have h2b : ∀ x ∈ Set.Icc a b, M.cutMoment 2 x ≠ ⊤ := by
    intro x hx
    exact ne_top_of_le_ne_top
      (ne_top_of_le_ne_top h4b (M.cutMoment_monotone 4 hx.2))
      (M.cutMoment_two_le_cutMoment_four x)
  have hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)) :=
    fun x hx => M.tendsto_windowMoment_sub S hSmono hS (h2b x hx)
      (h2b a ⟨le_rfl, hab⟩)
  have hcont : ContinuousAt (fun t => M.rhsScalarTwo t) r0 :=
    M.continuousAt_rhsScalarTwo_of_no_sphere r0 hr0 hrb h4b hsphere hcoef
  have hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound_ae hab hAE hC0 hC h4b
  exact M.hasDerivAt_cutMomentReal_two_of_window_majorant_pos hwin S har hrb hfluxMaj hG
    hfluxConv hmoment hcont hint

/-- **The same from finiteness of the second moment at `b`.** -/
theorem hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b) (h2b : M.cutMoment 2 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (hcoef : ContinuousAt M.coeffRHS r0) (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  M.hasDerivAt_cutMomentReal_two_offCorner hwin S hSmono hS har hrb
    (CaseOne.cutMoment_four_ne_top_of_two M h2b) hC0 hC hcoef hsphere

/-- **The off-corner picture on a positive tail, with the coefficient bound discharged.**

`Smwyvlg99M1.exists_coeffRHS_bound_of_deriv_decay` produces, from the model's own sharpness field
`M.exists_error` (i.e. `|deriv M.K r| = (1 + δ r) r^{-d-α-1}` with `δ r → 0`), a radius `R` beyond
which the coefficient bound `|M.coeffRHS| ≤ C` holds on every window `[a, b]` with `R ≤ a ≤ b`.
Composing it with §5 removes `hC0`/`hC`:

for every off-corner window `[a, b]` of the tail `[R, ∞)`, every monotone edge-exhausting window
family, and every finite second cutoff moment at `b`, absolute continuity, the a.e. radius
derivative, the a.e. `deriv` equality, the integrated identity and the interval integrability of
`M.rhsScalarTwo` all hold on `[a, b]`.

The coefficient bound is the *only* thing this removes: no continuity of `M.rhsScalarTwo` at any
radius is produced, which is why the pointwise derivative of §6 is not stated here. -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner_tail :
    ∃ R : ℝ, ∀ {a b : ℝ}, R ≤ a → M.IsOffCornerWindow a b →
      ∀ (S : ℕ → Finset (Sym2 M.V)), Monotone S → (∀ e : Sym2 M.V, ∃ k, e ∈ S k) →
      M.cutMoment 2 b ≠ ⊤ →
      AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b ∧
        (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
          HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r) ∧
        (deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo a b)]
          fun t => M.rhsScalarTwo t) ∧
        (∀ x ∈ Set.Icc a b,
          ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) ∧
        IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b := by
  obtain ⟨R, hR⟩ := Smwyvlg99M1.exists_coeffRHS_bound_of_deriv_decay M
  refine ⟨R, fun {a b} hRa hwin S hSmono hS h2b => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hR a b hRa hwin.1 hwin.2.1
  exact M.ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two hwin S hSmono hS h2b
    hC0 hC

end SourceModelData

/-! ## 7. The source power law: the off-corner picture with the coefficient bound discharged

At the witness the coefficient is the literal power law `β_c r^{-d-α-1}` and its modulus is
decreasing, so `|M.coeffRHS r| ≤ powLawCoeffBound β_c d α a` on `[a, ∞)` is
`abs_coeffRHS_sourceModelWitness_le`.  The only remaining non-geometric hypothesis of §5 and §6 is
therefore finiteness of the second cutoff moment at the right endpoint. -/

namespace Witness

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.Orchestration.SourceModelData

/-- **The integrated `p = 2` identity at the witness on an arbitrary off-corner window**, with the
coefficient bound discharged.  The conclusion is stated in the paper's scale only through
`M.rhsScalarTwo`, whose value is the power law (`rhsScalarTwo_sourceModelWitness_eq`); no further
hypothesis is needed for the identity itself. -/
theorem integral_rhsScalarTwo_eq_sub_sourceModelWitness_offCorner
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V))
    (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ k, e ∈ S k)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤) :
    ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, (sourceModelWitness d hd α hα).rhsScalarTwo t
        = (sourceModelWitness d hd α hα).cutMomentReal 2 x
          - (sourceModelWitness d hd α hα).cutMomentReal 2 a :=
  (sourceModelWitness d hd α hα).integral_rhsScalarTwo_eq_sub_of_offCornerWindow hwin S hSmono hS
    h2b (powLawCoeffBound_nonneg (d := d) (α := α)
      (β := ((sourceModelWitness d hd α hα).betaCrit : ℝ)) hwin.1)
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le d hd α hα hwin.1 hr.1)

/-- **`hac`/`hae` at the witness on an arbitrary off-corner window**, with the coefficient bound
discharged: the only hypotheses are the off-corner window, a monotone edge-exhausting family, and
finiteness of the second cutoff moment at `b`. -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V))
    (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ k, e ∈ S k)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤) :
    AbsolutelyContinuousOnInterval
        (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r) a b ∧
      (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
        HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
          ((sourceModelWitness d hd α hα).rhsScalarTwo r) r) ∧
      (deriv (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
        =ᵐ[volume.restrict (Set.Ioo a b)]
          fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t) ∧
      (∀ x ∈ Set.Icc a b,
        ∫ t in a..x, (sourceModelWitness d hd α hα).rhsScalarTwo t
          = (sourceModelWitness d hd α hα).cutMomentReal 2 x
            - (sourceModelWitness d hd α hα).cutMomentReal 2 a) ∧
      IntervalIntegrable (fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t) volume a b :=
  (sourceModelWitness d hd α hα).ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two
    hwin S hSmono hS h2b (powLawCoeffBound_nonneg (d := d) (α := α)
      (β := ((sourceModelWitness d hd α hα).betaCrit : ℝ)) hwin.1)
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le d hd α hα hwin.1 hr.1)

/-- **The witness off-corner radius derivative at an arbitrary off-sphere radius**, with the
majorant, the flux convergence and the coefficient bound all discharged.  The statement is in the
paper's scale; the only non-geometric hypothesis is `cutMoment 2 b ≠ ⊤`. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_cutMoment_two
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b r0 : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V))
    (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 := by
  have h := (sourceModelWitness d hd α hα).hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two
    hwin S hSmono hS har hrb h2b (powLawCoeffBound_nonneg (d := d) (α := α)
      (β := ((sourceModelWitness d hd α hα).betaCrit : ℝ)) hwin.1)
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le d hd α hα hwin.1 hr.1)
    (continuousAt_coeffRHS_sourceModelWitness d hd α hα (lt_trans hwin.1 har)) hsphere
  rwa [rhsScalarTwo_sourceModelWitness_eq d hd α hα (lt_trans hwin.1 har)] at h

/-- **The off-corner picture is unconditional below radius `2`.**  On `[1/2, 1]` every cutoff moment
of the witness is `1` (`cutMoment_sourceModelWitness_eq_one`), so the second moment at `b = 1` is
finite for free; the geometry (`isOffCornerWindow_sourceModelWitness`) and the window family
(`boxEdges d`) are explicit.  Hence absolute continuity, the a.e. radius derivative, the a.e.
`deriv` equality, the integrated identity and the interval integrability hold on `[1/2, 1]` with
**no hypothesis at all**. -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_box_unconditional
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    AbsolutelyContinuousOnInterval
        (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r) (1 / 2) 1 ∧
      (∀ᵐ r ∂volume, r ∈ Set.Ioo (1 / 2 : ℝ) 1 →
        HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
          ((sourceModelWitness d hd α hα).rhsScalarTwo r) r) ∧
      (deriv (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
        =ᵐ[volume.restrict (Set.Ioo (1 / 2 : ℝ) 1)]
          fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t) ∧
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) 1,
        ∫ t in (1 / 2)..x, (sourceModelWitness d hd α hα).rhsScalarTwo t
          = (sourceModelWitness d hd α hα).cutMomentReal 2 x
            - (sourceModelWitness d hd α hα).cutMomentReal 2 (1 / 2)) ∧
      IntervalIntegrable (fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t)
        volume (1 / 2) 1 :=
  ac_and_ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα
    (isOffCornerWindow_sourceModelWitness d hd α hα) (boxEdges d) (boxEdges_mono d)
    (exists_mem_boxEdges d)
    (by
      rw [cutMoment_sourceModelWitness_eq_one d hd α hα 2 (by norm_num)]
      exact ENNReal.one_ne_top)

/-- **The nondegenerate witness derivative at `r0 = 37/10`**, on the off-corner window
`[7/2, 39/10]`, conditional only on `cutMoment 2 (39/10) ≠ ⊤`.

`37/10 > 2`, so the witness cut law there is not the Dirac law at the empty configuration and the
conclusion is not a degenerate value.  Everything else — the coefficient bound, the majorant, the
flux convergence, the off-corner and off-sphere conditions — is discharged. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_three_and_seven_of_cutMoment_two
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 (39 / 10) ≠ ⊤) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α (37 / 10)
        * ((sourceModelWitness d hd α hα).p2RHS (37 / 10)).toReal) (37 / 10) :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_cutMoment_two d hd α hα
    (isOffCornerWindow_sourceModelWitness_seven_halves d hd α hα) (boxEdges d) (boxEdges_mono d)
    (exists_mem_boxEdges d) (by norm_num) (by norm_num) h2b
    (sourceModelWitness_sphere_ne_seven_tenths d hd α hα)

end Witness

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms
  SourceModelData.cutMoment_four_ne_top_of_cutMoment_two_le
#print axioms
  SourceModelData.tendsto_windowFlux_of_cutMoment_four_le
#print axioms
  SourceModelData.tendsto_windowFlux_of_cutMoment_two_le
#print axioms
  SourceModelData.intervalIntegrable_windowMajorant_ae
#print axioms
  SourceModelData.integral_rhsScalarTwo_eq_sub_of_offCornerWindow_of_cutMoment_four
#print axioms
  SourceModelData.integral_rhsScalarTwo_eq_sub_of_offCornerWindow
#print axioms
  SourceModelData.ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner
#print axioms
  SourceModelData.ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two
#print axioms
  SourceModelData.hasDerivAt_cutMomentReal_two_offCorner
#print axioms
  SourceModelData.hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two
#print axioms
  SourceModelData.ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner_tail
#print axioms
  Witness.integral_rhsScalarTwo_eq_sub_sourceModelWitness_offCorner
#print axioms
  Witness.ac_and_ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner
#print axioms
  Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_cutMoment_two
#print axioms
  Witness.ac_and_ae_hasDerivAt_cutMomentReal_two_sourceModelWitness_box_unconditional
#print axioms
  Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_three_and_seven_of_cutMoment_two

end PercLib.CriticalLRP.Orchestration
