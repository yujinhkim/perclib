/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwttizjk`, member `m4`, direction D8.

The **local integrability clause** of source-style logarithmic integrability.

The repository predicate `PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable h` (paper,
p. 26) records only the global clause `∫_{r₀}^∞ |h r| dr / r < ∞`.  Hutchcroft writes that as an
improper integral of the density `r ↦ h r / r` on `(0, ∞)`, and Lemma I.4.3 applies it to the
open-triangle tail `∇_r`.  For an improper integral `∫_{R1}^∞` to be the limit of the interval
integrals `∫_{R1}^{R}` one needs the density to be integrable on each compact subinterval of
`(0, ∞)`; that hypothesis is *not* part of `LogarithmicallyIntegrable`, whose `IntegrableOn`
statement lives on `Ioi r₀`.  The predicates below name it, and `LogTailLocal/Core.lean` proves
it for the tail from antitone finiteness alone.

Deliberately absent: any statement about the size of `h` at `∞`, about a tail mass, or about a
window.  The clause here is local on `(0, ∞)` and is a statement about the *function* `h`, not
about `r ↦ ∫_{‖x‖ ≥ r} ⋯`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Analysis.RegularVariation

/-!
# Local integrability clause of logarithmic integrability

Candidate definitions for the source-style local clause; see the header comment above.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Analysis.LogTailLocal

/-- **Local integrability on the compacta of `(0, ∞)`.**  `h` is integrable on every interval
`[R1, R2]` with `0 < R1 ≤ R2`.  This is the clause which makes `∫_{r₀}^∞ h r dr / r` an improper
integral of a density rather than a formal symbol: it is exactly what is needed for the interval
integrals `∫_{R1}^{R}` to exist for every `R ≥ R1`.

Note that this is a statement about the function `h` near *finite* radii only.  It carries no
information about the decay of `h` at `∞` and must not be confused with finiteness of a tail mass
such as `r ↦ ∫_{‖x‖ ≥ r} ⋯`. -/
def IntegrableOnPositiveCompacts (h : ℝ → ℝ) : Prop :=
  ∀ R1 R2 : ℝ, 0 < R1 → R1 ≤ R2 → IntegrableOn h (Icc R1 R2) volume

/-- **Local integrability of the logarithmic density.**  The function `r ↦ h r / r` is integrable
on every `[R1, R2]` with `0 < R1 ≤ R2`.  This is the local form of the integrand in the source
integral `∫_{r₀}^∞ |h r| dr / r`; away from `0` it is implied by `IntegrableOnPositiveCompacts h`
(see `LogTailLocal.logWeightedIntegrableOnPositiveCompacts_of_integrableOnPositiveCompacts`). -/
def LogWeightedIntegrableOnPositiveCompacts (h : ℝ → ℝ) : Prop :=
  ∀ R1 R2 : ℝ, 0 < R1 → R1 ≤ R2 →
    IntegrableOn (fun r => h r / r) (Icc R1 R2) volume

/-- **Boundedness on the compacta of `(0, ∞)`.**  A local bound is what an `ℝ≥0∞`-valued tail has
to supply before its `.toReal` can be integrated: `⊤` is sent to `0` by `ENNReal.toReal`, so
monotonicity, and therefore any bound, is only available once the values are known to be finite. -/
def BoundedOnPositiveCompacts (h : ℝ → ℝ) : Prop :=
  ∀ R1 R2 : ℝ, 0 < R1 → R1 ≤ R2 → ∃ C : ℝ, ∀ r ∈ Icc R1 R2, |h r| ≤ C

/-- **Source-style logarithmic integrability.**  The repository's `LogarithmicallyIntegrable`
(the global clause `∫_{r₀}^∞ |h r| dr / r < ∞` together with measurability), *plus* the separate
local clause `IntegrableOnPositiveCompacts h`.

The local clause is not redundant given the global one: `IntegrableOn` on `Ioi r₀` constrains only
the behaviour near `∞`, and says nothing about any compact interval.  Keeping the two clauses
separate is the point of this definition; do not collapse it back into
`LogarithmicallyIntegrable`. -/
def SourceLogIntegrable (h : ℝ → ℝ) : Prop :=
  LogarithmicallyIntegrable h ∧ IntegrableOnPositiveCompacts h

/-- **Source-style logarithmically integrable error function**: the repository's
`IsLogErrorFunction` (log-integrable, `h → 0`) together with the local clause.  This is the shape
in which the tail enters the ODE lemmas of `Analysis/RegularVariation.lean`, which integrate `h`
over `[r, R]` and therefore need the interval integrals to exist.  (Those lemmas additionally
require a *global* bound `|h t| ≤ C` for all `t ≥ r₀`, which the local clause does not give; for
`∇` that bound is `exists_bound_nablaTail_of_logRadialBound`.) -/
def SourceLogErrorFunction (h : ℝ → ℝ) : Prop :=
  IsLogErrorFunction h ∧ IntegrableOnPositiveCompacts h

/-- **Non-redundance witness.**  The function which is `(x - 1)⁻¹` on `[1, 2]` and `0` elsewhere.

It has a single non-integrable singularity at the *interior* point `1` of `(0, ∞)`.  Being `0` far
out, its logarithmic integral `∫_{r₀}^∞ |h r| dr / r` converges for `r₀ = 3`; but it is neither
integrable nor bounded on `[1, 2]`.  `LogTailLocal/Counterexample.lean` turns this into a
Lean-checked refutation of `LogarithmicallyIntegrable h → IntegrableOnPositiveCompacts h`, which is
why the source-style predicate keeps the two clauses separate.  The singularity has to be at an
interior point: a spike at `0` would be invisible to `IntegrableOnPositiveCompacts`, whose
intervals all satisfy `0 < R1`. -/
noncomputable def invSpike (x : ℝ) : ℝ := if x ∈ Icc 1 2 then (x - 1)⁻¹ else 0

end PercLib.CriticalLRP.Analysis.LogTailLocal
