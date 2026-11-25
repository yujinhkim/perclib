/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvgnqju`, member `m2`, direction `d2`.

# The radius-integral exchange without monotonicity of the window fluxes

The landed analytic core of the integrated `p = 2` radius identity is

`intervalIntegral_eq_of_monotone_window` (`Integrated/Main.lean`):

if `F n` are nonnegative measurable radius functions with interval integrals `p n`, increasing
pointwise to `Flim`, and `p n → L`, then `∫ t in a..b, Flim t = L`.

Its two monotonicity inputs are the *only* reason the window-index order enters the radius
identity: `hmomMono` was already removed in `Integrated/Assembly.lean` (the `'` core), but the
flux monotonicity `∀ n t, F n t ≤ F (n + 1) t` — `hfluxMono` of the model, which for the source
model is not derivable — is still used there, through the `ℝ≥0∞` monotone convergence theorem.

This file proves the replacement: **dominated convergence in the window index**.  If the window
fluxes are pointwise dominated on the radius window by one fixed function whose interval integral
is finite, then the exchange goes through with no order assumption on the window family at all:

* `intervalIntegral_eq_of_dominated_window` — the analytic core with `hmono`, `hpmono` and the
  nonnegativity of `F` dropped, replaced by an interval-integrable majorant `G` and the norm
  domination `‖F n t‖ ≤ G t` on the window;
* `intervalIntegral_eq_of_majorant_window` — the one-sided form of the same statement for a
  nonnegative family, phrased with `IsWindowMajorantOn` (`Defs.lean`), which is the form in which
  the model-level bound `M.windowFlux (S n) t ≤ M.rhsScalarTwo t` of `RadiusFTC.lean` is fed in;
* `intervalIntegral_eq_of_sup_window` — the same statement with the *canonical* majorant
  `t ↦ ⨆ n, ‖F n t‖`, i.e. domination by the pointwise supremum over the window index.  This is
  the weakest hypothesis in the family `‖F n‖ ≤ G`: it does not require an explicitly constructed
  envelope, only that the supremum over `n` be interval integrable.

No monotone convergence and no `ℝ≥0∞` reasoning is used; the whole content is Lebesgue dominated
convergence plus uniqueness of limits.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Defs

/-!
# Exchange of a radius integral with the window limit, by dominated convergence
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

/-- **Dominated convergence for interval integrals in the window index.**

Let `F n` be measurable radius functions with interval integrals `p n` on `[a, b]`, pointwise
dominated there by an interval-integrable function `G`, converging almost everywhere on `[a, b]`
to `Flim`, and let `p n → L`.  Then `∫ t in a..b, Flim t = L`.

Compared with `intervalIntegral_eq_of_monotone_window` this drops the pointwise monotonicity
`∀ n t, F n t ≤ F (n + 1) t`, the monotonicity `Monotone p` of the integrals, and the
nonnegativity of `F`; it adds the majorant `G`.  Nothing needs the order of the window index. -/
theorem intervalIntegral_eq_of_dominated_window {F : ℕ → ℝ → ℝ} {Flim : ℝ → ℝ}
    {p : ℕ → ℝ} {G : ℝ → ℝ} {L a b : ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Set.uIoc a b)))
    (hbound : ∀ n, ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ‖F n t‖ ≤ G t)
    (hG : IntervalIntegrable G volume a b)
    (hconv : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → Tendsto (fun n => F n t) atTop (𝓝 (Flim t)))
    (hstep : ∀ n, ∫ t in a..b, F n t = p n)
    (hL : Tendsto p atTop (𝓝 L)) :
    ∫ t in a..b, Flim t = L := by
  have hDCT : Tendsto (fun n => ∫ t in a..b, F n t) atTop (𝓝 (∫ t in a..b, Flim t)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume) G
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hG
      (by simpa only [Set.uIoc_of_le le_rfl] using hconv)
  have hp : Tendsto (fun n => ∫ t in a..b, F n t) atTop (𝓝 L) := by
    simpa only [hstep] using hL
  exact tendsto_nhds_unique hDCT hp

/-- **The one-sided form for a nonnegative family**, phrased with a uniform majorant
`IsWindowMajorantOn F G (Ioc a b)`.

This is the exact shape consumed at the model level: `F n = M.windowFlux (S n)` is nonnegative at
every radius (`windowFlux_nonneg`), and `G = M.rhsScalarTwo` dominates it on the window. -/
theorem intervalIntegral_eq_of_majorant_window {F : ℕ → ℝ → ℝ} {Flim : ℝ → ℝ}
    {p : ℕ → ℝ} {G : ℝ → ℝ} {L a b : ℝ} (hab : a ≤ b)
    (hnn : ∀ n t, 0 ≤ F n t)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Set.uIoc a b)))
    (hmaj : IsWindowMajorantOn F G (Set.Ioc a b))
    (hG : IntervalIntegrable G volume a b)
    (hconv : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (Flim t)))
    (hstep : ∀ n, ∫ t in a..b, F n t = p n)
    (hL : Tendsto p atTop (𝓝 L)) :
    ∫ t in a..b, Flim t = L := by
  refine intervalIntegral_eq_of_dominated_window hmeas ?_ hG ?_ hstep hL
  · intro n
    refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hab] at ht
    exact hmaj.norm_le hnn ht
  · refine Eventually.of_forall fun t ht => ?_
    exact hconv t

/-- **Domination by the pointwise supremum over the window index.**

The canonical majorant of the family is `t ↦ sSup (range fun n => ‖F n t‖)`, the supremum in the
window index taken pointwise in the radius.  The hypotheses below are exactly: the family is
pointwise bounded in the window index, and that supremum is interval integrable.  No explicitly
constructed envelope is needed; the sup itself is the weakest majorant of the family
`‖F n t‖ ≤ G t`. -/
theorem intervalIntegral_eq_of_sSup_window {F : ℕ → ℝ → ℝ} {Flim : ℝ → ℝ} {p : ℕ → ℝ}
    {L a b : ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Set.uIoc a b)))
    (hbdd : ∀ t, BddAbove (Set.range fun n => ‖F n t‖))
    (hsup : IntervalIntegrable (fun t => sSup (Set.range fun n => ‖F n t‖)) volume a b)
    (hconv : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → Tendsto (fun n => F n t) atTop (𝓝 (Flim t)))
    (hstep : ∀ n, ∫ t in a..b, F n t = p n)
    (hL : Tendsto p atTop (𝓝 L)) :
    ∫ t in a..b, Flim t = L := by
  refine intervalIntegral_eq_of_dominated_window
    (G := fun t => sSup (Set.range fun n => ‖F n t‖)) hmeas (fun n => ?_) hsup hconv hstep hL
  refine Eventually.of_forall fun t _ =>
    le_csSup (hbdd t) (Set.mem_range_self n)

/-- **A uniform bound on the window fluxes is enough.**  If the window fluxes are bounded on the
radius window by one constant, independently of the window index, then the exchange holds with no
monotonicity in the window index.  This is the qualitative form of the majorant hypothesis that is
easiest to check in applications. -/
theorem intervalIntegral_eq_of_bounded_window {F : ℕ → ℝ → ℝ} {Flim : ℝ → ℝ} {p : ℕ → ℝ}
    {L a b C : ℝ} (hC : 0 ≤ C)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Set.uIoc a b)))
    (hbdd : ∀ n, ∀ t ∈ Set.uIoc a b, ‖F n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → Tendsto (fun n => F n t) atTop (𝓝 (Flim t)))
    (hstep : ∀ n, ∫ t in a..b, F n t = p n)
    (hL : Tendsto p atTop (𝓝 L)) :
    ∫ t in a..b, Flim t = L :=
  intervalIntegral_eq_of_dominated_window (G := fun _ => C) hmeas
    (fun n => Eventually.of_forall fun t ht => hbdd n t ht)
    (intervalIntegrable_const (c := C) (μ := volume)) hconv hstep hL

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.intervalIntegral_eq_of_dominated_window
#print axioms PercLib.CriticalLRP.Orchestration.intervalIntegral_eq_of_majorant_window
#print axioms PercLib.CriticalLRP.Orchestration.intervalIntegral_eq_of_sSup_window
#print axioms PercLib.CriticalLRP.Orchestration.intervalIntegral_eq_of_bounded_window
