/-
Definitions for the `p = 4`, `k = 2` fourth cluster-moment tree-graph bound.
Ultramath `smwpq441z` member m3 (Direction C).

Everything is stated for the native countable Bernoulli bond law `law π`; no
moment-finiteness, local-finiteness or translation assumption is built into a
definition.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Mixed.Defs

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- The probability that `a` and `b` are both connected to the common centre `c`. -/
noncomputable def jointP (π : Sym2 V → unitInterval) (a b c : V) : ℝ≥0∞ :=
  law π (conn a c ∩ conn b c)

/-- The native second cluster moment at `v`, as an extended nonnegative quantity. -/
noncomputable def secondMoment (π : Sym2 V → unitInterval) (v : V) : ℝ≥0∞ :=
  ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
    (PercLib.CriticalLRP.cluster ω v)) ^ 2 ∂(law π)

/-- The native first cluster moment (susceptibility) at `v`. -/
noncomputable def firstMoment (π : Sym2 V → unitInterval) (v : V) : ℝ≥0∞ :=
  ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
    (PercLib.CriticalLRP.cluster ω v) ∂(law π)

/-- Three increasing events with three pairwise disjoint finite open certificates.  This is the
certificate object of threefold BK. -/
def ThreeCertEvent (A₀ A₁ A₂ : Set (Config V)) : Set (Config V) :=
  {ω | ∃ W₀ W₁ W₂ : Set (Sym2 V),
        W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧
        W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧
        W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧
        Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₁ W₂}

/-- The five-slot integrand of the `p = 4`, `k = 2` regrouping: two joint connection events and
one two-point event, all measured from the same centre `c`. -/
noncomputable def starK2 (π : Sym2 V → unitInterval) (i₀ i₁ i₂ i₃ i₄ c : V) : ℝ≥0∞ :=
  jointP π i₀ i₁ c * (tau π i₂ c * jointP π i₃ i₄ c)

/-- **The `p = 4`, `k = 2` slot diagram.**  The right-hand side of the threefold BK bound for the
`k`-th labelled comb pattern, with both branch vertices `u`, `w` union-bounded away: the sole
remaining index is the common centre `c` (the middle vertex of the comb). -/
noncomputable def slotDiagramK2 (π : Sym2 V → unitInterval) (k : Fin 15)
    (T : Fin 5 → V) : ℝ≥0∞ :=
  ∑' c, starK2 π (T (pat k 0)) (T (pat k 1)) (T (pat k 2)) (T (pat k 3)) (T (pat k 4)) c

end PercLib.CriticalLRP.TreeExpansion.FivePoint
