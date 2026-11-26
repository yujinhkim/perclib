/-
Independent UltraMath work, swarm `smwwsmqji`, member `m1`.
Production base `50c2eed0682a7e1b078ae771dbef463ebe00701d`, Lean 4.35.0 (read-only package
`.scratch/critical-lrp-orchestration`). Nothing outside this directory is modified.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.OrbitCount.Assembly
public import PercLib.CriticalLRP.TreeExpansion.Moments

/-!
# (I.2.2) and (I.2.3) from the child-swap transport

`OrbitCount/Assembly.lean` proves the tree-graph bound with the source tree sum `treeSum` from the
explicit child-swap transport hypothesis `SwapTransport`.  This file puts that in the exact shape of
source inequalities (I.2.2) and (I.2.3):

* `treeGraphBound_of_swapTransport`: `TreeGraphBound`, i.e. (I.2.2), with the two-point function
  as kernel;
* `moment_bound_of_swapTransport`: the `q`-th moment bound with coefficient `(2q-3)!!`, i.e.
  (I.2.3), obtained by production's `moment_bound_of_tree_graph` (which needs only BK, the
  translation invariance `P(a ↔ b) = T(b - a)` and (I.2.2)).

The sole extra premise is the deterministic transport of a diagram event across child swaps; it is
not a restatement of either inequality (it mentions neither `treeSum`, `prob`, `clusterVolume` nor
any moment).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Source inequality (I.2.2) from the child-swap transport.**  The tree-graph inequality with
the two-point function as kernel and the source tree sum, for every root configuration
`x : Fin (m+1) → V`. -/
theorem treeGraphBound_of_swapTransport (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V)
    (htrans : ∀ (m : ℕ) (x : Fin (m + 1) → V),
      SwapTransport ends (fun j : Fin m => x (Fin.succ j)) (x 0)) :
    TreeGraphBound pr ends (fun a b => prob pr {ω | Conn ends ω a b}) := by
  intro m hm x
  have h := prob_conn_le_treeSum_of_swapTransport (q := m) pr hp hp1 hBK ends (x 0) hm
    (fun j : Fin m => x (Fin.succ j)) (htrans m x)
  have hset : {ω : Finset E | ∀ i : Fin (m + 1), Conn ends ω (x 0) (x i)}
      = {ω : Finset E | ∀ j : Fin m, Conn ends ω (x 0) (x (Fin.succ j))} := by
    ext ω
    constructor
    · intro h' j
      exact h' (Fin.succ j)
    · intro h' i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact conn_refl ends ω (x 0)
      · exact h' j
  rw [hset]
  exact h

/-- **Source inequality (I.2.3) from the child-swap transport.**  For a translation-invariant
two-point function on a finite additive commutative group, the `q`-th moment of the cluster volume
is at most `(2q-3)!! (E|K|)^(2q-1)`. -/
theorem moment_bound_of_swapTransport [AddCommGroup V] (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (o : V)
    (htrans : ∀ (m : ℕ) (x : Fin (m + 1) → V),
      SwapTransport ends (fun j : Fin m => x (Fin.succ j)) (x 0))
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (q : ℕ) (hq : 1 ≤ q) :
    (∑ x : Fin q → V, prob pr {s | ∀ i : Fin q, Conn ends s o (x i)})
      ≤ (VolumeMoments.M (q - 1) : ℝ) * (clusterVolume pr ends o) ^ (2 * q - 1) :=
  moment_bound_of_tree_graph pr hp hp1 ends o hinv
    (treeGraphBound_of_swapTransport pr hp hp1 hBK ends htrans) q hq

end PercLib.CriticalLRP.TreeExpansion.Real
