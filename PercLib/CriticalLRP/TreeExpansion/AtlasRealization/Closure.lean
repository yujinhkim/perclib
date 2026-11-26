/- Independently verified join of Ultramath work: smwwsmqji, members m1 and m2. -/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Transport.Main
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.OrbitCount.Endpoint

/-!
Join the independently rebuilt child-swap transport and the transversal assembly.
The resulting finite-group tree-graph and ordinary moment bounds have no transport premise.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion.Real

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]
variable {α : Type*} [DecidableEq α]

/-- The transport premise of the transversal assembly follows from preservation of the
realized atlas and its two atlas-edge endpoints. -/
theorem swapTransport_of_endpoint_preserving (ends : E → Sym2 V) (y : α → V) (c : V) :
    SwapTransport ends y c := by
  intro t t' h φ
  obtain ⟨I⟩ := nonempty_swapIso t y h
  exact ⟨I.phi φ, (diagEvent_eq_of_swapIso I φ).le⟩

/-- Finite-graph tree-graph inequality with the source's transversal tree sum. -/
theorem treeGraphBound_of_atlasRealization (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : TreeGraph.BKIncreasing pr) (ends : E → Sym2 V) :
    TreeGraphBound pr ends (fun a b => prob pr {ω | Conn ends ω a b}) :=
  treeGraphBound_of_swapTransport pr hp hp1 hBK ends
    (fun _ _ => swapTransport_of_endpoint_preserving _ _ _)

/-- The corresponding ordinary moment bound on a transitive finite group. -/
theorem moment_bound_of_atlasRealization [AddCommGroup V] (pr : E → ℝ)
    (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : TreeGraph.BKIncreasing pr) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, TreeGraph.twoPoint pr ends a b = TreeGraph.twoPoint pr ends o (b - a))
    (q : ℕ) (hq : 1 ≤ q) :
    (∑ x : Fin q → V, TreeGraph.prob pr {s | ∀ i : Fin q, TreeGraph.Conn ends s o (x i)})
      ≤ (VolumeMoments.M (q - 1) : ℝ) * (TreeGraph.clusterVolume pr ends o) ^ (2 * q - 1) :=
  moment_bound_of_swapTransport pr hp hp1 hBK ends o
    (fun _ _ => swapTransport_of_endpoint_preserving _ _ _) hinv q hq

end PercLib.CriticalLRP.TreeExpansion.Real

set_option linter.hashCommand false
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.swapTransport_of_endpoint_preserving
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.treeGraphBound_of_atlasRealization
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.moment_bound_of_atlasRealization
