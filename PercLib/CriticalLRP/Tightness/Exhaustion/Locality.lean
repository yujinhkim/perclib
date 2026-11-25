/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Finite-dimensional dependence of the restricted window volume

The restricted volume `vol A ω u W` only sees the edges with both endpoints in `A`.  For a
*finite* `A` (every member of an exhaustion) this says that the finite-subgraph events of
`Passage` are genuinely finite-cylinder events, i.e. that the hypothesis
`hfin` of the exhaustion theorems is a statement about the finite subgraph.

Proving that the *law* of those finitely many coordinates is the finite weighted graph's own
product law is the cylinder/independence step (a separate task), not done here.
-/
module

public import PercLib.CriticalLRP.Tightness.Exhaustion.Passage

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace Exhaustion

variable {V : Type*} [Countable V]

/-- An edge whose two endpoints lie in `A`. -/
def EdgeIn (A : Set V) (e : Sym2 V) : Prop := ∃ z ∈ A, ∃ w ∈ A, s(z, w) = e

/-- Every edge of a walk joins two vertices of the walk's own support. -/
lemma walk_edges_mem_support {G : SimpleGraph V} {x y : V} (p : G.Walk x y) :
    ∀ e ∈ p.edges, ∃ z ∈ p.support, ∃ w ∈ p.support, s(z, w) = e := by
  induction p with
  | nil => intro e he; exact absurd he (by simp)
  | @cons u v w h p' ih =>
      intro e he
      rw [SimpleGraph.Walk.edges_cons] at he
      rw [SimpleGraph.Walk.support_cons]
      rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨u, List.mem_cons_self, v, List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p'),
          rfl⟩
      · obtain ⟨z, hz, w', hw', hzw⟩ := ih e he'
        exact ⟨z, List.mem_cons_of_mem _ hz, w', List.mem_cons_of_mem _ hw', hzw⟩

/-- **Self-determination of restricted connectivity.**  Two configurations that agree on all
edges with both endpoints in `A` have the same `A`-restricted connectivity. -/
lemma pathIn_congr_forward {A : Set V} {ω ω' : Config V}
    (h : ∀ e, EdgeIn A e → (e ∈ ω → e ∈ ω')) {x y : V} (hp : PathIn A ω x y) :
    PathIn A ω' x y := by
  obtain ⟨p, he, hv⟩ := hp
  refine ⟨p, fun e hel => ?_, hv⟩
  obtain ⟨z, hz, w, hw, hzw⟩ := walk_edges_mem_support p e hel
  have hedge : EdgeIn A (s(z, w)) := ⟨z, hv z hz, w, hv w hw, rfl⟩
  exact hzw ▸ h (s(z, w)) hedge (hzw ▸ he e hel)

/-- Equivalence form of self-determination. -/
theorem pathIn_congr {A : Set V} {ω ω' : Config V}
    (h : ∀ e, EdgeIn A e → (e ∈ ω ↔ e ∈ ω')) {x y : V} :
    PathIn A ω x y ↔ PathIn A ω' x y :=
  ⟨pathIn_congr_forward (fun e he => (h e he).mp) ,
    pathIn_congr_forward (fun e he => (h e he).mpr)⟩

/-- **The restricted window volume is a function of the edges inside `A`.** -/
theorem vol_congr {A : Set V} {ω ω' : Config V}
    (h : ∀ e, EdgeIn A e → (e ∈ ω ↔ e ∈ ω')) (u : V) (W : Finset V) :
    vol A ω u W = vol A ω' u W := by
  classical
  simp only [vol]
  rw [Finset.filter_congr (fun y _ => pathIn_congr h)]

/-! ## Finite-window bounds

For arbitrary untruncated extended-cardinal observables an edian may fail to exist when the value
`⊤` has too much mass. This does not affect a finite-window cluster maximum, which is bounded by
the window cardinality. -/

/-- A finite-window volume is bounded by the window cardinality. -/
theorem volFull_le_card (ω : Config V) (u : V) (W : Finset V) :
    volFull ω u W ≤ (W.card : ℝ≥0∞) := by
  classical
  simp only [volFull]
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))

/-- The repository's `|K_u ∩ W|` is bounded by the window cardinality: truncation to a finite
window rules out the value `⊤`, whatever the ambient clusters do. -/
theorem clusterVolIn_le_window_card (ω : Config V) (u : V) (W : Finset V) :
    clusterVolIn ω u (W : Set V) ≤ (W.card : ℝ≥0∞) := by
  rw [← volFull_eq_clusterVolIn]
  exact volFull_le_card ω u W

/-- The window maximum is bounded by the window cardinality. -/
theorem maxVolFull_le_card (ω : Config V) (W : Finset V) :
    maxVolFull ω W ≤ (W.card : ℝ≥0∞) := by
  classical
  exact Finset.sup_le (fun w _ => volFull_le_card ω w W)

/-- Consequently `|K_max(W)|` is never `⊤` for a finite window (quantitative form of the
repository's `clusterMaxVol_ne_top`). -/
theorem clusterMaxVol_le_window_card (ω : Config V) (W : Finset V) :
    Percolation.clusterMaxVol ω W ≤ (W.card : ℝ≥0∞) := by
  rw [← maxVolFull_eq_clusterMaxVol]
  exact maxVolFull_le_card ω W

/-- **Contrast case, untruncated variables only.**  For an arbitrary `ℝ≥0∞`-valued `X`, if the
value `⊤` carries more than `e^{-1}` of the mass then no natural threshold puts the tail below
`e^{-1}`, so the edian of `X` does not exist.  This is the situation of an untruncated cluster
volume, not of `Percolation.clusterMaxVol ω W` with `W` finite (see the lemmas above). -/
theorem edian_existence_fails_of_top_mass {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ≥0∞} (h : ENNReal.ofReal (Real.exp (-1)) < μ {ω | X ω = ⊤}) :
    ¬ ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1)) := by
  rintro ⟨n, hn⟩
  have hsub : {ω : Ω | X ω = ⊤} ⊆ {ω | (n : ℝ≥0∞) ≤ X ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hω]
    exact le_top
  exact absurd (hn.trans_lt h) (not_lt.mpr (measure_mono hsub))

end Exhaustion

end PercLib.CriticalLRP
