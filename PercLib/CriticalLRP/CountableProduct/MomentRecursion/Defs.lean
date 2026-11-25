/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Renewal quantities for small-row-sum moment estimates

Accepted from independent submission `smwp81k72` direction D2.  The quantities
record only the pruning, offspring summands and off-diagonal row sum; they are
not a Galton–Watson process, a first-hit partition, or a moment bound.
-/
module

public import PercLib.CriticalLRP.CountableProduct.Renewal
public import PercLib.Percolation.Bond.RowSum

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set
open PercLib.Percolation.Bond PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.MomentRecursion

open PercLib.CriticalLRP.Renewal

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The volume of the pruned cluster of `y`: the cluster of `y` after every edge at `o`
is closed.  This is the offspring term of the renewal recursion. -/
noncomputable def prunedVol (o y : V) (ω : Config V) : ℝ≥0∞ :=
  ((cluster (ω ∩ blockT o) y).encard : ℝ≥0∞)

/-- One summand of the offspring sum: the pruned cluster of `y` when `{o,y}` is open. -/
noncomputable def offspringTerm (o y : V) (ω : Config V) : ℝ≥0∞ :=
  if (y ≠ o ∧ s(o, y) ∈ ω) then prunedVol o y ω else 0

/-- The offspring sum at the root `o`: one pruned cluster per open edge at `o`. -/
noncomputable def offspring (o : V) (ω : Config V) : ℝ≥0∞ :=
  ∑' y : V, offspringTerm o y ω

/-- The open-edge indicator of a single pair, with the classical decidability instance
fixed once at definition time (so that the `Finset` products below have a canonical
instance and do not depend on which `Decidable` instance a rewrite picks up). -/
noncomputable def edgeInd (e : Sym2 V) : Config V → ℝ≥0∞ :=
  fun ω => if e ∈ ω then 1 else 0

/-- The off-diagonal row sum of the intensities at `v`, in `ℝ≥0∞`. -/
noncomputable def rowSum (π : Sym2 V → unitInterval) (v : V) : ℝ≥0∞ :=
  ∑' w : V, if w = v then 0 else (unitInterval.toNNReal (π s(v, w)) : ℝ≥0∞)

end PercLib.CriticalLRP.MomentRecursion
