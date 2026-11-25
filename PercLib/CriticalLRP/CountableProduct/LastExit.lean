/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The honest last-exit description of a restored ghost connection

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Proposition I.3.1 (p. 29):

  "If the origin is connected to the ghost field in the model without cut-off but not in the
   model with cut-off then, in the monotone coupling, there must exist an edge in the boundary
   of the cluster in the cut-off model that becomes open in the non-cut-off model and whose
   other endpoint is connected to the ghost by a path that is disjoint from the cluster of the
   origin in the cut-off model."

This is the deterministic core of the exploration, and this file proves it exactly.  Let
`ω ⊆ ω_F` be the cut-off and full configurations in the monotone coupling, `K` the cut-off
cluster of the origin, `g` a marked (ghost) vertex with `o ↔ g` in `ω_F` and `o ↛ g` in `ω`.
Then there are

* `x ∈ K` and `y ∉ K`,
* an edge `s(x,y)` that is open in `ω_F` and closed in `ω` (a *restored* edge),
* and a walk `q` from `y` to `g` whose edges are open in `ω_F` and whose **every vertex lies
  outside `K`**,

i.e. the ghost connection continues in the region outside the cut-off cluster and never
re-enters it.  The proof is the "last exit" argument: among all vertices of a fixed `ω_F`-walk
from `o` to `g`, take the largest index whose vertex lies in `K`; the next vertex is outside
`K`, the connecting edge is restored, and the remaining suffix avoids `K` completely.

Because the continuation avoids `K`, its coordinates (the edges with both endpoints outside
`K`, and the marks outside `K`) are disjoint from the coordinates that decide `{K_r(o) = K}`
(`cluster_eq_finset_congr` in `RestorationLaw.lean`).  This is the honest disjoint-path
description that replaces the paper's cluster-restoration independence claim; note that the
continuation is an `ω_F`-connection, i.e. the off-cluster factor is a **full-law** quantity
(compare `i35_cutoffForm_fails` in `GhostI35.lean`).

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.RestorationCompl
public import PercLib.CriticalLRP.CountableProduct.GhostCutoffCounterexample
public import PercLib.CriticalLRP.CountableProduct.RestorationLaw

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- **The last-exit lemma (walk form).**

Let `K` be closed under taking `ω`-neighbours of its points (e.g. `K` is a union of `ω`-clusters),
and let `p` be a walk from `o ∈ K` to `g ∉ K` all of whose edges are open in `ω_F ⊇ ω`.  Then
there are `x ∈ K`, `y ∉ K`, an edge `s(x,y)` open in `ω_F` but not in `ω`, and a walk `q` from
`y` to `g` with all edges open in `ω_F` and all vertices outside `K`. -/
theorem exists_last_exit {ω ωF : Config V} {K : Set V} {o g : V}
    (hclos : ∀ {u v : V}, u ∈ K → s(u, v) ∈ ω → v ∈ K)
    (ho : o ∈ K) (hg : g ∉ K) (p : (⊤ : SimpleGraph V).Walk o g)
    (hp : ∀ e ∈ p.edges, e ∈ ωF) :
    ∃ (x y : V) (q : (⊤ : SimpleGraph V).Walk y g),
      x ∈ K ∧ y ∉ K ∧ s(x, y) ∈ ωF ∧ s(x, y) ∉ ω ∧
        (∀ e ∈ q.edges, e ∈ ωF) ∧ (∀ e ∈ q.edges, ∀ v ∈ e, v ∉ K) := by
  -- auxiliary form, starting from an arbitrary vertex
  have aux : ∀ {a z : V} (p : (⊤ : SimpleGraph V).Walk a z), (∀ e ∈ p.edges, e ∈ ωF) →
      z ∉ K →
      (∃ (x y : V) (q : (⊤ : SimpleGraph V).Walk y z),
        x ∈ K ∧ y ∉ K ∧ s(x, y) ∈ ωF ∧ s(x, y) ∉ ω ∧
          (∀ e ∈ q.edges, e ∈ ωF) ∧ (∀ e ∈ q.edges, ∀ v ∈ e, v ∉ K)) ∨
        (a ∉ K ∧ ∀ e ∈ p.edges, ∀ v ∈ e, v ∉ K) := by
    intro a z p
    induction p with
    | nil =>
      intro _ hz
      exact Or.inr ⟨hz, by simp⟩
    | cons hadj p' ih =>
      rename_i s0 m tgt
      intro hp hz
      have hp' : ∀ e ∈ p'.edges, e ∈ ωF := fun e he =>
        hp e (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ he)
      have hfirst : s(s0, m) ∈ ωF :=
        hp _ (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..)
      rcases ih hp' hz with hexit | ⟨hmK, hinner⟩
      · exact Or.inl hexit
      · by_cases hs0K : s0 ∈ K
        · refine Or.inl ⟨s0, m, p', hs0K, hmK, hfirst, ?_, hp', hinner⟩
          intro hmem
          exact hmK (hclos hs0K hmem)
        · refine Or.inr ⟨hs0K, ?_⟩
          intro e he w hw
          rw [SimpleGraph.Walk.edges_cons] at he
          rcases List.mem_cons.mp he with rfl | he'
          · rcases Sym2.mem_iff.mp hw with rfl | rfl
            · exact hs0K
            · exact hmK
          · exact hinner e he' w hw
  rcases aux p hp hg with hexit | ⟨hoK, -⟩
  · exact hexit
  · exact absurd ho hoK

/-- **The last-exit lemma for the cut-off cluster.**

In the monotone coupling `ω ⊆ ω_F` with `ω` the cut-off configuration, let `K` be the cut-off
cluster of `o`.  If the ghost field `G` is met by `K` in the full configuration but by no vertex
in the cut-off one, then there are `x ∈ K`, `y ∉ K`, a restored edge `s(x,y)` (open in `ω_F`,
closed in `ω`) and an `ω_F`-walk from `y` to a marked vertex that avoids `K` entirely. -/
theorem exists_last_exit_ghost {ω ωF : Config V} {G : Set V} {o g : V}
    (_hmono : ∀ e, e ∈ ω → e ∈ ωF) (_hgG : g ∈ G)
    (hfull : Connects ωF o g) (hcut : ¬ Connects ω o g) :
    ∃ (x y : V) (q : (⊤ : SimpleGraph V).Walk y g),
      x ∈ cluster ω o ∧ y ∉ cluster ω o ∧ s(x, y) ∈ ωF ∧ s(x, y) ∉ ω ∧
        (∀ e ∈ q.edges, e ∈ ωF) ∧
          (∀ e ∈ q.edges, ∀ v ∈ e, v ∉ cluster ω o) := by
  have ho : o ∈ cluster ω o := cluster_mem_self ω o
  have hg : g ∉ cluster ω o := fun hmem => hcut (mem_cluster_iff.mp hmem)
  have hclos : ∀ {u v : V}, u ∈ cluster ω o → s(u, v) ∈ ω → v ∈ cluster ω o := by
    intro u v hu huv
    by_cases huv_eq : u = v
    · subst huv_eq; exact hu
    · refine mem_cluster_iff.mpr ?_
      refine connects_trans (mem_cluster_iff.mp hu) ?_
      rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
      exact Relation.ReflTransGen.single (by rw [openGraph_adj]; exact ⟨huv_eq, huv⟩)
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr hfull
  exact exists_last_exit hclos ho hg p hp

end PercLib.CriticalLRP
