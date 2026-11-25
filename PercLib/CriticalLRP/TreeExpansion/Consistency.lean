/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
A consistency check on the definition of the tree sum `treeSum` (the right-hand side of
(I.2.2)): at `m = 1` the tree sum is the single two-point function `P_β(v ↔ x_0)`, so the
tree-graph inequality is an identity there. This also shows the `2^{-(m-1)}`
normalisation is right at the first nontrivial index.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Moment

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The tree sum at `m = 1`: the single tree with one leaf contributes `k v x₀`. -/
theorem treeSum_one (k : V → V → ℝ) (v : V) (x : Fin 1 → V) :
    treeSum k 1 v x = k v (x 0) := by
  have hterm : ∀ t : RTree.LT (Fin 1),
      RTree.wt k t.val (fun q => x (RTree.leafOfPos t.val q)) v = k v (x 0) := by
    intro t
    rw [RTree.eq_theLT1 t]
    rfl
  rw [treeSum, Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_const, Finset.card_univ,
    RTree.card_LT_fin_one]
  simp

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- At `m = 1` the tree-graph inequality (I.2.2) is an identity: both sides equal
`P(x₀ ↔ x₁)`. -/
theorem treeGraphBound_one_holds (pr : E → ℝ) (ends : E → Sym2 V) (x : Fin 2 → V) :
    prob pr {s | ∀ i : Fin 2, Conn ends s (x 0) (x i)}
      = treeSum (twoPoint pr ends) 1 (x 0) (fun j => x (Fin.succ j)) := by
  rw [treeSum_one]
  congr 1
  ext s
  constructor
  · intro h
    exact h 1
  · intro h i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact conn_refl ends s _
    · have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      exact h

end PercLib.CriticalLRP.TreeExpansion
