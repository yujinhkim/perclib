module

public import PercLib.CriticalLRP.RussoInf.FluxBase
public import PercLib.CriticalLRP.RussoInf.Geometry

/-!
# Opening one pivotal edge: the half of the merge identity that needs no path induction

Swarm `smwv9oxuv`, member `m2`.

Production has two facts about forcing a single edge:

* `cluster_forceOn_singleton_eq_of_notMem_touchSet` — if the edge misses the cluster, the cluster is
  *unchanged*;
* `cluster_forceOn_singleton_empty_subset` — forcing it open only *grows* the cluster.

The case that carries the `p`-th moment increment is the one where the edge joins the cluster to a
new component: for `e = s(x,y)` with `x` already in the cluster of `o`, forcing `e` open must put
the *whole* cluster of `y` into the cluster of `o`,

  `cluster ω o ∪ cluster ω y ⊆ cluster (ω ∪ {s(x,y)}) o`.

That inclusion is proved here, unconditionally and without path induction: `x` is already reachable
from `o`, and `y` becomes adjacent to `x`, so every vertex of the cluster of `y` becomes reachable
from `o` by `trans`.  At the level of volumes it gives the lower bound

  `|K_o| + |K_y| ≤ |K_o after the flip|`,  i.e.  `|K_y| ≤ Δ|K_o|`  when `y ∉ K_o`,

which is the direction in which the source's `2|K||K_y|` term is bounded from below by the second
order increment `2 g Δg + (Δg)²` of `QuadraticFlux.flipDiff_sq`.

**What is not proved here.**  The reverse inclusion
`cluster (ω ∪ {s(x,y)}) o ⊆ cluster ω o ∪ cluster ω y`, hence the *equality*
`cluster (ω ∪ {s(x,y)}) o = cluster ω o ∪ cluster ω y` and the exact statement `Δ|K_o| = |K_y|`.
That direction needs a path induction (any walk in `ω ∪ {s(x,y)}` uses the new edge at most once,
and splitting it there gives the bound); it is a genuine gap and is *not* claimed here.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Opening a pivotal edge pulls in the cluster of its far endpoint.**  If `x` lies in the cluster
of `o`, then after the edge `s(x,y)` is forced open, every vertex of the cluster of `y` lies in the
cluster of `o`.  Consequently the cluster only grows by at least the cluster of `y`. -/
theorem cluster_union_edge_subset {o x y : V} {ω : Config V} (hxy : x ≠ y)
    (hx : x ∈ cluster ω o) :
    cluster ω o ∪ cluster ω y ⊆ cluster (ω ∪ {s(x, y)}) o := by
  have hmono : ∀ (v : V), cluster ω v ⊆ cluster (ω ∪ {s(x, y)}) v := fun v =>
    cluster_mono (fun e he => Set.mem_union_left _ he) v
  intro z hz
  rcases hz with h | h
  · exact hmono o h
  · have h1 : Connects (ω ∪ {s(x, y)}) o x := hmono o (mem_cluster_iff.mp hx)
    have h2 : (openGraph (ω ∪ {s(x, y)})).Adj x y := by
      rw [openGraph_adj]
      exact ⟨hxy, Set.mem_union_right _ (Set.mem_singleton _)⟩
    exact mem_cluster_iff.mpr (h1.trans (h2.reachable.trans (hmono y (mem_cluster_iff.mp h))))

end PercLib.CriticalLRP
