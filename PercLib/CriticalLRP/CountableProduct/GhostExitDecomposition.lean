/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Decomposition of a new full-law ghost-hit into finite exit blocks

A new ghost-hit in the monotone coupling forces a last exit from a finite cutoff
cluster, and the ghost avoids that cluster. At positive intensity, ghost avoidance
also rules out an infinite cluster almost surely. These are the deterministic and
null-event inputs to the later countable summation; this file does not assert that
the summation or global restoration inequality is already proved.
-/
module

public import PercLib.CriticalLRP.CountableProduct.GhostMixedBlock

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The **exit event** of the monotone coupling: the ghost meets the full configuration
`ω ∪ η` at the cluster of `o` but not the cut-off configuration `ω`. -/
def exitEvent (o : V) : Set ((Config V × Config V) × (V → Prop)) :=
  {z | GhostConnected o (unionConf z.1, z.2) ∧ ¬ GhostConnected o (z.1.1, z.2)}

theorem measurableSet_exitEvent (o : V) :
    MeasurableSet (exitEvent (V := V) o) := by
  have h1 : MeasurableSet {z : (Config V × Config V) × (V → Prop) |
      GhostConnected o (unionConf z.1, z.2)} :=
    (measurableSet_ghostConnected o).preimage
      ((measurable_unionConf.comp measurable_fst).prodMk measurable_snd)
  have h2 : MeasurableSet {z : (Config V × Config V) × (V → Prop) |
      GhostConnected o (z.1.1, z.2)} :=
    (measurableSet_ghostConnected o).preimage
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h : exitEvent (V := V) o
      = {z : (Config V × Config V) × (V → Prop) | GhostConnected o (unionConf z.1, z.2)}
        ∩ {z : (Config V × Config V) × (V → Prop) | ¬ GhostConnected o (z.1.1, z.2)} := rfl
  rw [h]
  exact h1.inter h2.compl

/-- **The exit decomposition, at the level of the coupling.**  If the ghost reaches the full
cluster of `o` but not the cut-off cluster, and the cut-off cluster is finite, then there are a
finite cluster shape `K`, `x ∈ K`, `y`, such that the per-cluster block `blockSet o K x y` holds:
`{x,y}` is fresh, the ghost avoids `K`, and the ghost is reached from `y` by a walk avoiding `K`. -/
theorem exitEvent_subset_blockSet (o : V) (ω η : Config V) (G : V → Prop)
    (hfin : (cluster ω o).Finite)
    (hG : GhostConnected o (unionConf (ω, η), G)) (hnG : ¬ GhostConnected o (ω, G)) :
    ∃ (K : Finset V) (x y : V), o ∈ K ∧ ((ω, η), G) ∈ blockSet o K x y := by
  classical
  obtain ⟨x, hx, y, hy, hfull, hnot, v, hGv, q, hq⟩ :=
    exists_fresh_exit_of_ghost (ω := ω) (θ := unionConf (ω, η))
      (fun e he => Or.inl he) hG hnG
  -- the fresh edge lies in `η`
  have hfresh : s(x, y) ∈ η := by
    rcases hfull with h | h
    · exact absurd h hnot
    · exact h
  -- the ghost avoids the cut-off cluster
  have havoid : ∀ u ∈ cluster ω o, ¬ G u := by
    intro u hu huG
    exact hnG ⟨u, hu, huG⟩
  -- the off-cluster walk lies in the restricted configuration
  have hoff : offCluster (cluster ω o) y (unionConf (ω, η), G) := by
    obtain ⟨q', hq'⟩ := exists_walk_top_of_walk q
    have hq'edges : ∀ e ∈ q'.edges, e ∈ restrictConf (cluster ω o) (unionConf (ω, η)) := by
      intro e he
      have he' : e ∈ q.edges := by rw [← hq']; exact he
      rw [mem_restrictConf]
      exact ⟨edgeSet_openGraph_subset (q.edges_subset_edgeSet he'),
        hq.not_mem_edgeTouch e he'⟩
    obtain ⟨q'', hq''⟩ := exists_walk_openGraph_of_walk_top q' hq'edges
    exact ⟨v, hq.end_notMem, hGv, mem_cluster_iff.mpr q''.reachable⟩
  refine ⟨hfin.toFinset, x, y, hfin.mem_toFinset.mpr (cluster_mem_self ω o), ?_⟩
  rw [blockSet_mem]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hfin.coe_toFinset]
  · exact hfresh
  · intro u hu
    exact havoid u (hfin.mem_toFinset.mp hu)
  · rw [hfin.coe_toFinset]
    exact hoff

/-- The event that the ghost misses the cluster of `o` is the event that the ghost avoids that
cluster, as a set of ghost fields. -/
theorem ghostAvoidSet_eq (o : V) (θ : Config V) :
    {G : V → Prop | ¬ GhostConnected o (θ, G)} = {G : V → Prop | ∀ v ∈ cluster θ o, ¬ G v} := by
  ext G
  constructor
  · rintro h v hv hvG
    exact h ⟨v, hv, hvG⟩
  · rintro h ⟨v, hv, hvG⟩
    exact h v hv hvG

/-- The ghost cannot avoid an infinite cluster at positive intensity: the event that the ghost
misses the cut-off cluster while the cut-off cluster is infinite is null. -/
theorem measure_avoid_infinite (ρ q : Sym2 V → unitInterval) (h : ℝ≥0) (hh : 0 < h) (o : V) :
    (((edgeMeasure ρ).prod (edgeMeasure q)).prod (ghostLaw h))
      {z : (Config V × Config V) × (V → Prop) |
        ¬ GhostConnected o (z.1.1, z.2) ∧ clusterVol z.1.1 o = ⊤} = 0 := by
  classical
  set S : Set ((Config V × Config V) × (V → Prop)) :=
    {z | ¬ GhostConnected o (z.1.1, z.2) ∧ clusterVol z.1.1 o = ⊤} with hS
  have hmeas : MeasurableSet S := by
    have h2 : MeasurableSet {z : (Config V × Config V) × (V → Prop) |
        GhostConnected o (z.1.1, z.2)} :=
      (measurableSet_ghostConnected o).preimage
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h3 : MeasurableSet {z : (Config V × Config V) × (V → Prop) |
        clusterVol z.1.1 o = ⊤} :=
      (measurable_clusterVol o (measurableSet_singleton ⊤)).preimage
        (measurable_fst.comp measurable_fst)
    have := h2.compl.inter h3
    exact this
  have hsec : ∀ p : Config V × Config V,
      (ghostLaw h) (Prod.mk p ⁻¹' S)
        = if clusterVol p.1 o = ⊤ then ghostMass h p.1 o else 0 := by
    intro p
    have hset : Prod.mk p ⁻¹' S
        = if clusterVol p.1 o = ⊤ then {G : V → Prop | ¬ GhostConnected o (p.1, G)}
            else (∅ : Set (V → Prop)) := by
      by_cases hp : clusterVol p.1 o = ⊤
      · rw [ite_eq_left hp]
        ext G
        simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq, hp, and_true]
      · rw [ite_eq_right hp]
        ext G
        simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq, Set.mem_empty_iff_false, hp,
          and_false, iff_false, not_false_eq_true, IsEmpty.forall_iff]
    rw [hset]
    by_cases hp : clusterVol p.1 o = ⊤
    · rw [ite_eq_left hp, ite_eq_left hp, ghostAvoidSet_eq o p.1]
      exact ghostLaw_avoids h (cluster p.1 o)
    · rw [ite_eq_right hp, ite_eq_right hp, measure_empty]
  have hzero : ∀ p : Config V × Config V,
      (if clusterVol p.1 o = ⊤ then ghostMass h p.1 o else 0) = 0 := by
    intro p
    by_cases hp : clusterVol p.1 o = ⊤
    · rw [ite_eq_left hp]
      exact ghostMass_of_infinite hh p.1 o (inInfiniteCluster_iff_infinite p.1 o |>.mp hp)
    · rw [ite_eq_right hp]
  rw [Measure.prod_apply hmeas]
  have hcongr : ∫⁻ p : Config V × Config V, (ghostLaw h) (Prod.mk p ⁻¹' S)
        ∂((edgeMeasure ρ).prod (edgeMeasure q))
      = ∫⁻ p : Config V × Config V,
          (if clusterVol p.1 o = ⊤ then ghostMass h p.1 o else 0)
          ∂((edgeMeasure ρ).prod (edgeMeasure q)) :=
    lintegral_congr hsec
  rw [hcongr]
  simp only [hzero]
  simp

end PercLib.CriticalLRP
