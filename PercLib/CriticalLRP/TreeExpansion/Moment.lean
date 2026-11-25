/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The cluster moment `E|K_o|^q` as a sum of connection probabilities, and inequality
(I.2.3) in the paper's own form `E_β|K|^p ≤ (2p−3)!! (E_β|K|)^{2p−1}`.

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22.

`RTree.clusterMoment_eq_expectation` is the identity

  `E[|K_o|^q] = ∑_{x : Fin q → V} P(o ↔ x_0, ..., o ↔ x_{q−1})`

(generalising `TreeGraph.expectation_clusterVol_sq` from `q = 2`), and
`moment_bound_expectation` is (I.2.3) with `E|K_o|^q` on the left.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Moments
public import PercLib.CriticalLRP.TreeGraph.Spatial

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
open Classical
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `|K_o|^q` as a sum of indicator products over `q`-tuples. -/
theorem clusterVol_pow_eq_sum (ends : E → Sym2 V) (s : Finset E) (o : V) (q : ℕ) :
    (clusterVol ends s o : ℝ) ^ q
      = ∑ x : Fin q → V, ∏ i : Fin q, (if Conn ends s o (x i) then (1 : ℝ) else 0) := by
  classical
  have hcoe : (clusterVol ends s o : ℝ)
      = ∑ y : V, (if Conn ends s o y then (1 : ℝ) else 0) := by
    rw [clusterVol_eq_sum]
    push_cast
    rfl
  rw [hcoe]
  rw [Finset.sum_pow']
  have hpi : (Fintype.piFinset fun _ : Fin q => (Finset.univ : Finset V)) = Finset.univ := by
    ext p
    simp [Fintype.mem_piFinset]
  rw [hpi]

/-- **The cluster moment as a sum of connection probabilities.**
`E|K_o|^q = ∑_{x : Fin q → V} P(o ↔ x_i for all i)`. -/
theorem clusterMoment_eq_expectation (pr : E → ℝ) (ends : E → Sym2 V) (o : V) (q : ℕ) :
    expectReal pr (fun s => (clusterVol ends s o : ℝ) ^ q)
      = ∑ x : Fin q → V, prob pr {s | ∀ i : Fin q, Conn ends s o (x i)} := by
  classical
  have h1 : ∀ s : Finset E, (clusterVol ends s o : ℝ) ^ q
      = ∑ x : Fin q → V, indicatorR {s' | ∀ i : Fin q, Conn ends s' o (x i)} s := by
    intro s
    rw [clusterVol_pow_eq_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_boole]
    simp [indicatorR]
  simp only [h1, expectReal, prob_eq_sum_indicator, Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ### (I.2.3) with the cluster moment on the left -/

variable [AddCommGroup V]

/-- **Inequality (I.2.3)**: `E_β|K_o|^q ≤ (2q−3)!! (E_β|K_o|)^{2q−1}`, i.e.
`E|K|^q ≤ VolumeMoments.M (q−1) · (E|K|)^{2q−1}`, for Bernoulli bond percolation on a
finite weighted graph with a translation-invariant two-point function, derived from the
tree-graph inequality (I.2.2) (`TreeGraphBound`). -/
theorem moment_bound_expectation
    (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (q : ℕ) (hq : 1 ≤ q) :
    expectReal pr (fun s => (clusterVol ends s o : ℝ) ^ q)
      ≤ (VolumeMoments.M (q - 1) : ℝ) * (clusterVolume pr ends o) ^ (2 * q - 1) := by
  rw [clusterMoment_eq_expectation]
  exact moment_bound_of_tree_graph pr hp hp1 ends o hinv hTG q hq

end PercLib.CriticalLRP.TreeExpansion
