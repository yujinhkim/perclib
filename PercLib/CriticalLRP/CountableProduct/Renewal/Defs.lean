/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Definitions for the one-step renewal decomposition

Accepted from independent audit `smwp7ai5u` direction D3.  The pruned cluster,
the root-edge indicator and the arbitrary-set counting volume are generic
Bernoulli-percolation objects, not a Galton–Watson law and not a cluster bound.
-/
module

public import PercLib.CriticalLRP.Correlation.ThirdMoment

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set
open PercLib.Percolation.Bond PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Renewal

variable {V : Type*} [Countable V]

/-- The counting measure of a vertex set, in the `ℝ≥0∞` cluster-volume normalisation. -/
noncomputable def setVol (S : Set V) : ℝ≥0∞ :=
  ∑' z : V, S.indicator (fun _ => (1 : ℝ≥0∞)) z

/-- The pairs of `V` not incident to `o`: the edges left after closing every edge at `o`. -/
def blockT (o : V) : Set (Sym2 V) := {e | o ∉ e}

/-- The contribution of the vertex `y` to the renewal at the root `o`: the cluster of `y`
after every edge at `o` is closed, when the edge `{o,y}` is open, and nothing otherwise. -/
def renewTerm (ω : Config V) (o y : V) : Set V :=
  {z | y ≠ o ∧ s(o, y) ∈ ω ∧ z ∈ cluster (ω ∩ blockT o) y}

end PercLib.CriticalLRP.Renewal
