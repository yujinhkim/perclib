/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Definitions for the local-uniform pivotal-series exchange at `p = 2`

Swarm `smwvdggcc`, member `m2`, direction (A).

Integration donor: `.ultramath/smwvdggcc/m2`; independently checked at `70d28dd23e81d39713b39719197c5a492f8bca8c`.

The formal target is, at an off-sphere radius `r0`,

`HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0`.

The route of this direction is the abstract exchange theorem
`PercLib.CriticalLRP.hasDerivAt_integral_of_windowFlux`: it produces the derivative of
`r ↦ ∫ ω, g ω ∂(μ r)` from (i) the finite-window Russo derivatives, (ii) pointwise convergence of
the window expectations to the infinite-volume one, and (iii) **local uniform** convergence of the
finite-window pivotal flux sums to the infinite pivotal flux.

This file introduces only the vocabulary needed to state (iii) for the `p = 2` functional
`g = |K_o|²`:

* `volSq o` — the real-valued `p = 2` cluster-volume functional `ω ↦ (|K_o(ω)|).toReal²`;
* `windowFlux`, `limitFlux` — the finite-window pivotal sum and the infinite pivotal series;
* `insertionFlux` — the finite-window *insertion error* `Σ_{e∈S} |c_r(e)| |P_S(e) − P(e)|`,
  the quantity whose local uniformity is the paper's "insertion tolerance" input;
* `LocallyUniformLimitFlux` — hypothesis (T1): the infinite pivotal series is the locally uniform
  limit of its windowed versions;
* `UniformInsertionFlux` — hypothesis (T2): the insertion errors vanish locally uniformly in `r`.

No mathematical statement is asserted here: this is a definition layer only.
-/
module

public import PercLib.CriticalLRP.RussoInf.Exchange

/-!
# Window flux vocabulary for the `p = 2` off-corner derivative
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.SecondMomentExchange

variable {V : Type*} [Countable V]

/-- The `p = 2` cluster-volume functional `|K_o|²` read as a real number,
`ω ↦ (clusterVol ω o).toReal ^ 2`.

This is the observation differentiated by Lemma I.4.1 at `p = 2`.  It is genuinely unbounded:
no cap, no truncation and no `⊤ ↦ 0` conversion is built into it.  (`ENNReal.toReal_pow` makes it
agree with `(clusterVol ω o ^ 2).toReal` for *every* configuration, so the `ℝ≥0∞` and real forms
are interchangeable without a finiteness hypothesis.) -/
def volSq (o : V) : Config V → ℝ := fun ω => (clusterVol ω o).toReal ^ 2

/-- The finite-window pivotal flux sum
`Σ_{e ∈ S} c_r(e) · pivotalFlux (μ r) (cutFun S g) e`
whose derivative role is the right-hand side of the finite-graph Russo identity. -/
def windowFlux (g : Config V → ℝ) (c : ℝ → Sym2 V → ℝ) (μ : ℝ → Measure (Config V))
    (S : Finset (Sym2 V)) (r : ℝ) : ℝ :=
  ∑ e ∈ S, c r e * pivotalFlux (μ r) (cutFun S g) e

/-- The infinite pivotal flux series `Σ'_e c_r(e) · pivotalFlux (μ r) g e`. -/
def limitFlux (g : Config V → ℝ) (c : ℝ → Sym2 V → ℝ) (μ : ℝ → Measure (Config V))
    (r : ℝ) : ℝ :=
  ∑' e, c r e * pivotalFlux (μ r) g e

/-- The finite-window **insertion error**,
`Σ_{e ∈ S} |c_r(e)| · |pivotalFlux (μ r) (cutFun S g) e − pivotalFlux (μ r) g e|`.

This is the quantity that the paper's insertion-tolerance/restoration input (Lemma I.4.12 and its
use of sharpness) controls *uniformly in the radius*. -/
def insertionFlux (g : Config V → ℝ) (c : ℝ → Sym2 V → ℝ) (μ : ℝ → Measure (Config V))
    (S : Finset (Sym2 V)) (r : ℝ) : ℝ :=
  ∑ e ∈ S, |c r e| * |pivotalFlux (μ r) (cutFun S g) e - pivotalFlux (μ r) g e|

/-- **(T1)** The infinite pivotal flux series is the *locally uniform* limit of its windows:
`fun k r => Σ_{e ∈ S k} c_r(e) pivotalFlux (μ r) g e ⟶ Φ` locally uniformly on `I`.

`r ↦ Φ r` is the candidate derivative; for the source model it is `M.rhsScalarTwo`, whose value is
fixed by the fixed-radius FLUX identity `∑'_e M.cutEdgeDeriv r e · pivotalFlux (M.cutLaw r) |K|² =
M.rhsScalarTwo r`. -/
def LocallyUniformLimitFlux (g : Config V → ℝ) (c : ℝ → Sym2 V → ℝ)
    (μ : ℝ → Measure (Config V)) (S : ℕ → Finset (Sym2 V)) (Φ : ℝ → ℝ) (I : Set ℝ) : Prop :=
  TendstoLocallyUniformlyOn (fun k r => ∑ e ∈ S k, c r e * pivotalFlux (μ r) g e) Φ atTop I

/-- **(T2)** The insertion errors vanish *locally uniformly in the radius* on `I`. -/
def UniformInsertionFlux (g : Config V → ℝ) (c : ℝ → Sym2 V → ℝ)
    (μ : ℝ → Measure (Config V)) (S : ℕ → Finset (Sym2 V)) (I : Set ℝ) : Prop :=
  TendstoLocallyUniformlyOn (fun k r => insertionFlux g c μ (S k) r) (fun _ => (0 : ℝ)) atTop I

end PercLib.CriticalLRP.SecondMomentExchange

end

end
