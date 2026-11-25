/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for the D-2 host-graph specialization, using the canonical cylinder
marginal, countable almost-everywhere conjunction and mathlib's fromEdgeSet API.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Cylinder

/-!
# Host graphs as supported bond profiles

The hypothesis is zero probability on every pair outside the host edge set,
including diagonal pairs. This yields configuration containment as well as graph
containment. The general bond law continues to allow arbitrary diagonal values.
-/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- Almost surely no pair outside the host edge set is open. -/
theorem ae_config_subset_host (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (hq : ∀ e, e ∉ G.edgeSet → q e = 0) :
    ∀ᵐ ω ∂law q, ω ⊆ G.edgeSet := by
  have he (e : Sym2 V) : ∀ᵐ ω ∂law q, e ∈ ω → e ∈ G.edgeSet := by
    by_cases h : e ∈ G.edgeSet
    · exact Filter.Eventually.of_forall (fun _ _ => h)
    · have hz : law q {ω | e ∈ ω} = 0 := by
        simpa [law, hq e h] using PercLib.Probability.prodBernoulli_setOf_mem q e
      rw [ae_iff]
      simpa [h] using hz
  filter_upwards [ae_all_iff.mpr he] with ω hω
  exact fun e he => hω e he

/-- Almost surely the graph of open edges is a subgraph of the host graph. -/
theorem ae_openGraph_le_host (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (hq : ∀ e, e ∉ G.edgeSet → q e = 0) :
    ∀ᵐ ω ∂law q, openGraph ω ≤ G := by
  filter_upwards [ae_config_subset_host G q hq] with ω hω
  simpa [openGraph] using SimpleGraph.fromEdgeSet_mono hω

/-- Both configuration and graph containment form the host-specialization target. -/
def HostContainment (G : SimpleGraph V) (q : Sym2 V → unitInterval) : Prop :=
  (∀ e, e ∉ G.edgeSet → q e = 0) →
    ∀ᵐ ω ∂law q, ω ⊆ G.edgeSet ∧ openGraph ω ≤ G

theorem hostContainment (G : SimpleGraph V) (q : Sym2 V → unitInterval) :
    HostContainment G q := by
  intro hq
  exact (ae_config_subset_host G q hq).and (ae_openGraph_le_host G q hq)

example (G : SimpleGraph V) : ∀ᵐ ω ∂law (fun _ : Sym2 V => 0),
    ω ⊆ G.edgeSet ∧ openGraph ω ≤ G :=
  hostContainment G _ (fun _ _ => rfl)

-- Inhomogeneous host profiles, including probability one on host edges.
example (G : SimpleGraph Bool) (p : Sym2 Bool → unitInterval) :
    let q := fun e => if e ∈ G.edgeSet then p e else 0
    ∀ᵐ ω ∂law q, ω ⊆ G.edgeSet ∧ openGraph ω ≤ G := by
  classical
  exact hostContainment G _ (fun e he => by simp [he])

end PercLib.Percolation.Bond
