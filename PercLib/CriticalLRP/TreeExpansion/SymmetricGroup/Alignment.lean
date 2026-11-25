/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

/-
# Atom-level alignment of the finite tree-expansion law with the native `edgeMeasure` law

`PercLib/CriticalLRP/TreeExpansion/` works with a *finite* edge set `E`, the configuration space
`Finset E`, the product law `configurationLaw p` and the finite sums `prob`, `expectReal`
(`PercLib/CriticalLRP/FiniteBernoulli.lean`, `TreeGraph/ThreePoint.lean`, `TreeGraph/Spatial.lean`).
The I.4.7/I.4.8 consumer `Hrest.cE1_le_three_mul_cube_div_of_finite`
(`VolumeMoments/ErrorBounds.lean`) works instead with the *native* law `edgeMeasure π` on
`Config V := Sym2 V → Prop` and the extended cardinality `Percolation.cardFun`.

This file records, for a **finite** vertex type and the complete-graph edge map
`PercLib.CriticalLRP.idBondGraph V : Sym2 V → Sym2 V`, that the two descriptions are the same model:

* `edgeSetOf_toFs` / `openGraph_toFs` : the open graph of the tree-expansion configuration
  `toFs ω` is the native open graph of `ω`;
* `conn_toFs_iff` / `cluster_toFs` : tree-expansion `Conn`/`clusterF` compute the native
  connectivity and cluster;
* `edgeMeasure_atom` : the native law `edgeMeasure π` puts mass `configurationLaw p (toFs ω)`
  on the atom `{ω}`, with `p e = π e`.

These are the parts of the `expectReal`-versus-`∫⁻ ⋯ ∂edgeMeasure` alignment that hold at
*finite* `V`; the summation step `∑_ω ↦ ∫⁻` and the infinite-`V` case are not formalized.
See `OBSTRUCTION.md`.

Names are primed so that this file can be imported together with `ThirdMomentInstance.lean`.
-/
public import PercLib.CriticalLRP.TreeExpansion.SymmetricGroup.Basic
public import PercLib.CriticalLRP.VolumeMoments.ErrorBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Compatibility with the native complete graph -/
/-- The edge set of the tree-expansion open graph of `toFs ω`, for the complete-graph edge map,
is exactly the native configuration `ω`. -/
theorem edgeSetOf_toFs' (ω : PercLib.CriticalLRP.Config V) :
    PercLib.CriticalLRP.TreeGraph.edgeSetOf (PercLib.CriticalLRP.idBondGraph V)
        (PercLib.CriticalLRP.TreeGraph.toFs ω) = (ω : Set (Sym2 V)) := by
  ext e
  simp only [PercLib.CriticalLRP.TreeGraph.edgeSetOf, Set.mem_ofPred_eq,
    PercLib.CriticalLRP.TreeGraph.mem_toFs, PercLib.CriticalLRP.idBondGraph]
  exact ⟨fun ⟨a, ha, hae⟩ => hae ▸ ha, fun he => ⟨e, he, rfl⟩⟩

/-- The tree-expansion open graph of `toFs ω` is the native open graph of `ω`. -/
theorem openGraph_toFs' (ω : PercLib.CriticalLRP.Config V) :
    PercLib.CriticalLRP.TreeGraph.openGraph (PercLib.CriticalLRP.idBondGraph V)
        (PercLib.CriticalLRP.TreeGraph.toFs ω) = PercLib.CriticalLRP.openGraph ω := by
  have h : PercLib.CriticalLRP.openGraph ω = SimpleGraph.fromEdgeSet
      (PercLib.CriticalLRP.TreeGraph.edgeSetOf (PercLib.CriticalLRP.idBondGraph V)
        (PercLib.CriticalLRP.TreeGraph.toFs ω)) := by
    rw [PercLib.CriticalLRP.openGraph, PercLib.Percolation.Bond.openGraph, edgeSetOf_toFs']
  rw [h]
  rfl

/-- Tree-expansion connectivity of `toFs ω` is the native connectivity of `ω`. -/
theorem conn_toFs_iff' (ω : PercLib.CriticalLRP.Config V) (x y : V) :
    PercLib.CriticalLRP.TreeGraph.Conn (PercLib.CriticalLRP.idBondGraph V) (PercLib.CriticalLRP.TreeGraph.toFs ω) x y
      ↔ PercLib.CriticalLRP.Connects ω x y := by
  show (PercLib.CriticalLRP.TreeGraph.openGraph (PercLib.CriticalLRP.idBondGraph V)
      (PercLib.CriticalLRP.TreeGraph.toFs ω)).Reachable x y ↔
    (PercLib.CriticalLRP.openGraph ω).Reachable x y
  rw [openGraph_toFs']

/-- The native cluster is the tree-expansion cluster, seen as a set. -/
theorem cluster_toFs' (ω : PercLib.CriticalLRP.Config V) (x : V) :
    PercLib.CriticalLRP.cluster ω x
      = ((PercLib.CriticalLRP.TreeGraph.clusterF (PercLib.CriticalLRP.idBondGraph V)
          (PercLib.CriticalLRP.TreeGraph.toFs ω) x : Finset V) : Set V) := by
  ext y
  simp only [PercLib.CriticalLRP.mem_cluster_iff, PercLib.CriticalLRP.TreeGraph.mem_clusterF,
    Finset.mem_coe]
  exact (conn_toFs_iff' ω x y).symm

/-- The native law `edgeMeasure π` is the finite product law `Percolation.edgeLaw π`. -/
theorem edgeMeasure_eq_edgeLaw' (π : Sym2 V → unitInterval) :
    PercLib.CriticalLRP.edgeMeasure π = PercLib.CriticalLRP.Percolation.edgeLaw π := by
  rw [PercLib.CriticalLRP.edgeMeasure_eq_infinitePi,
    PercLib.CriticalLRP.Percolation.edgeLaw_eq_infinitePi]

/-- **Atom alignment.**  The mass the native law `edgeMeasure π` puts on a single configuration
`ω` is the finite product law `configurationLaw` of the tree-expansion development, evaluated at
`toFs ω`. -/
theorem edgeMeasure_atom' (π : Sym2 V → unitInterval) (ω : PercLib.CriticalLRP.Config V) :
    (PercLib.CriticalLRP.edgeMeasure π).real {ω} =
      PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ))
        (PercLib.CriticalLRP.TreeGraph.toFs ω) := by
  rw [edgeMeasure_eq_edgeLaw', PercLib.CriticalLRP.Percolation.edgeLaw_real_singleton,
    PercLib.CriticalLRP.configurationLaw]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases h : e ∈ ω <;> simp [PercLib.CriticalLRP.TreeGraph.mem_toFs, h]

end

end PercLib.CriticalLRP.TreeExpansion
