/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The global full-law ghost-restoration inequality

Assembles the countable summation of `blockSet_measure_le` over the exit decomposition of
`exitEvent_subset_blockSet`, with the weighted cluster-shape identity
`E_ρ[|K_o| e^{-h|K_o|}] = Σ_K |K| P_ρ(K_o = K) e^{-h|K|}`.

Everything here is conditional only on the degree hypothesis `D` and the full-law ghost-hit
bound `G`, and uses the monotone coupling `ω ∪ η ~ P_π` throughout.
-/
module

public import PercLib.CriticalLRP.CountableProduct.GhostExitDecomposition

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The coupled triple law `P_ρ ⊗ P_{q} ⊗ Ghost_h` of the monotone shift coupling. -/
noncomputable abbrev coupledMeasure (π ρ : Sym2 V → unitInterval) (h : ℝ≥0) :
    Measure ((Config V × Config V) × (V → Prop)) :=
  ((edgeMeasure ρ).prod (edgeMeasure (shiftProb π ρ))).prod (ghostLaw h)

/-- The full-law ghost-connection event seen through the coupled triple. -/
def fullGhostSet (o : V) : Set ((Config V × Config V) × (V → Prop)) :=
  {z | GhostConnected o (unionConf z.1, z.2)}

/-- The cut-off ghost-connection event seen through the coupled triple. -/
def cutGhostSet (o : V) : Set ((Config V × Config V) × (V → Prop)) :=
  {z | GhostConnected o (z.1.1, z.2)}

theorem measurableSet_fullGhostSet (o : V) : MeasurableSet (fullGhostSet o) := by
  have h : fullGhostSet o = (Prod.map unionConf (id : (V → Prop) → (V → Prop))) ⁻¹'
      GhostConnected o := rfl
  rw [h]
  exact (measurableSet_ghostConnected o).preimage
    (measurable_unionConf.prodMap measurable_id)

theorem measurableSet_cutGhostSet (o : V) : MeasurableSet (cutGhostSet o) := by
  have h : cutGhostSet o = (Prod.map Prod.fst (id : (V → Prop) → (V → Prop))) ⁻¹'
      GhostConnected o := rfl
  rw [h]
  exact (measurableSet_ghostConnected o).preimage (measurable_fst.prodMap measurable_id)

theorem coupledMeasure_fullGhostSet (π ρ : Sym2 V → unitInterval)
    (hρπ : ∀ e, ρ e ≤ π e) (h : ℝ≥0) (o : V) :
    coupledMeasure π ρ h (fullGhostSet o) = ghostHits π h o := by
  have hmap : (coupledMeasure π ρ h).map
      (Prod.map unionConf (id : (V → Prop) → (V → Prop))) =
      (edgeMeasure π).prod (ghostLaw h) := by
    rw [coupledMeasure, ← Measure.map_prod_map ((edgeMeasure ρ).prod (edgeMeasure (shiftProb π ρ)))
      (ghostLaw h) measurable_unionConf measurable_id,
      unionMeasure_eq_edgeMeasure hρπ, Measure.map_id]
  calc coupledMeasure π ρ h (fullGhostSet o)
      = coupledMeasure π ρ h ((Prod.map unionConf (id : (V → Prop) → (V → Prop))) ⁻¹'
          GhostConnected o) := rfl
    _ = (coupledMeasure π ρ h).map (Prod.map unionConf (id : (V → Prop) → (V → Prop)))
          (GhostConnected o) := by
        rw [Measure.map_apply (measurable_unionConf.prodMap measurable_id)
          (measurableSet_ghostConnected o)]
    _ = ((edgeMeasure π).prod (ghostLaw h)) (GhostConnected o) := by rw [hmap]
    _ = ghostHits π h o := rfl

theorem coupledMeasure_cutGhostSet (π ρ : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) :
    coupledMeasure π ρ h (cutGhostSet o) = ghostHits ρ h o := by
  have hfst : map Prod.fst ((edgeMeasure ρ).prod (edgeMeasure (shiftProb π ρ))) = edgeMeasure ρ := by
    have := (Measure.fst_prod (μ := edgeMeasure ρ) (ν := edgeMeasure (shiftProb π ρ)))
    simpa [Measure.fst] using this
  have hmap : (coupledMeasure π ρ h).map
      (Prod.map Prod.fst (id : (V → Prop) → (V → Prop))) =
      (edgeMeasure ρ).prod (ghostLaw h) := by
    rw [coupledMeasure, ← Measure.map_prod_map ((edgeMeasure ρ).prod (edgeMeasure (shiftProb π ρ)))
      (ghostLaw h) measurable_fst measurable_id,
      hfst, Measure.map_id]
  calc coupledMeasure π ρ h (cutGhostSet o)
      = coupledMeasure π ρ h ((Prod.map Prod.fst (id : (V → Prop) → (V → Prop))) ⁻¹'
          GhostConnected o) := rfl
    _ = (coupledMeasure π ρ h).map (Prod.map Prod.fst (id : (V → Prop) → (V → Prop)))
          (GhostConnected o) := by
        rw [Measure.map_apply (measurable_fst.prodMap measurable_id)
          (measurableSet_ghostConnected o)]
    _ = ((edgeMeasure ρ).prod (ghostLaw h)) (GhostConnected o) := by rw [hmap]
    _ = ghostHits ρ h o := rfl

/-- The cut-off connection event is contained in the full connection event. -/
theorem cutGhostSet_subset_fullGhostSet (o : V) : cutGhostSet o ⊆ fullGhostSet o := by
  rintro ⟨⟨ω, η⟩, G⟩ ⟨v, hv, hGv⟩
  exact ⟨v, cluster_mono (fun e he => Or.inl he) o hv, hGv⟩

/-- The exit event is the difference of the two connection events. -/
theorem exitEvent_eq_sdiff (o : V) :
    exitEvent o = fullGhostSet o \ cutGhostSet o := rfl

/-- **Exact additive decomposition of the full-law ghost-hit probability**: the full-law
probability is the cut-off probability plus the coupled probability of a fresh exit. -/
theorem ghostHits_eq_add_exitEvent (π ρ : Sym2 V → unitInterval)
    (hρπ : ∀ e, ρ e ≤ π e) (h : ℝ≥0) (o : V) :
    ghostHits π h o = ghostHits ρ h o + coupledMeasure π ρ h (exitEvent o) := by
  have hsplit := measure_inter_add_sdiff (μ := coupledMeasure π ρ h)
    (fullGhostSet o) (measurableSet_cutGhostSet o)
  rw [Set.inter_eq_right.mpr (cutGhostSet_subset_fullGhostSet o), ← exitEvent_eq_sdiff] at hsplit
  rw [coupledMeasure_fullGhostSet π ρ hρπ h o,
    coupledMeasure_cutGhostSet π ρ h o] at hsplit
  exact hsplit.symm

/-! ## The weighted cluster-shape identity

`E_ρ[|K_o| e^{-h|K_o|}]` is the sum over finite cluster shapes `K` of `|K| P_ρ(K_o = K) e^{-h|K|}`.
The `|K|` multiplicity is exactly the one produced by summing the per-cluster bound over the
`x ∈ K`. -/

theorem weightedGhostMass_eq_tsum (ρ : Sym2 V → unitInterval) (h : ℝ≥0) (hh : 0 < h) (o : V) :
    (∑' K : Finset V, (K.card : ℝ≥0∞) *
        (edgeMeasure ρ) {ω : Config V | cluster ω o = (K : Set V)} * ghostW h ^ K.card)
      = weightedGhostMass ρ h o := by
  classical
  have hpoint : ∀ ω : Config V,
      clusterVol ω o * ghostMass h ω o
        = ∑' K : Finset V, (if cluster ω o = (K : Set V) then
            (K.card : ℝ≥0∞) * ghostW h ^ K.card else 0) := by
    intro ω
    by_cases hfin : (cluster ω o).Finite
    · have hK : cluster ω o = ((hfin.toFinset : Finset V) : Set V) := by
        rw [hfin.coe_toFinset]
      rw [tsum_eq_single hfin.toFinset]
      · rw [ite_eq_left hK]
        have hvol : clusterVol ω o = (hfin.toFinset.card : ℝ≥0∞) := by
          rw [clusterVol_eq_encard, hfin.encard_eq_coe_toFinset_card]
          norm_cast
        have hgm : ghostMass h ω o = ghostW h ^ hfin.toFinset.card := by
          rw [ghostMass_of_finite h ω o hfin, Set.ncard_eq_toFinset_card (cluster ω o) hfin]
        rw [hvol, hgm]
      · intro K hK
        rw [ite_eq_right]
        intro hcontra
        refine hK (Finset.ext fun v => ?_)
        have hmem : v ∈ (K : Set V) ↔ v ∈ (hfin.toFinset : Set V) := by
          rw [← hcontra, hfin.coe_toFinset]
        simpa using hmem
    · have hinf : (cluster ω o).Infinite := hfin
      have htop : clusterVol ω o = ⊤ := (clusterVol_eq_top_iff ω o).mpr hinf
      have hgm : ghostMass h ω o = 0 := ghostMass_of_infinite hh ω o hinf
      rw [htop, hgm, mul_zero]
      symm
      rw [ENNReal.tsum_eq_zero]
      intro K
      rw [ite_eq_right]
      intro hcontra
      apply hinf
      rw [hcontra]
      exact K.finite_toSet
  have hmeas : ∀ K : Finset V, Measurable fun ω : Config V =>
      (if cluster ω o = (K : Set V) then (K.card : ℝ≥0∞) * ghostW h ^ K.card else 0) := by
    intro K
    exact Measurable.ite (measurableSet_cluster_eq_finset o K) measurable_const measurable_const
  rw [weightedGhostMass]
  symm
  calc ∫⁻ ω, clusterVol ω o * ghostMass h ω o ∂(edgeMeasure ρ)
      = ∫⁻ ω, ∑' K : Finset V, (if cluster ω o = (K : Set V) then
            (K.card : ℝ≥0∞) * ghostW h ^ K.card else 0) ∂(edgeMeasure ρ) :=
        lintegral_congr hpoint
    _ = ∑' K : Finset V, ∫⁻ ω, (if cluster ω o = (K : Set V) then
            (K.card : ℝ≥0∞) * ghostW h ^ K.card else 0) ∂(edgeMeasure ρ) :=
        lintegral_tsum (fun K => (hmeas K).aemeasurable)
    _ = ∑' K : Finset V, (K.card : ℝ≥0∞) *
          (edgeMeasure ρ) {ω : Config V | cluster ω o = (K : Set V)} * ghostW h ^ K.card := by
        refine tsum_congr fun K => ?_
        have hid : (fun ω : Config V => if cluster ω o = (K : Set V) then
              (K.card : ℝ≥0∞) * ghostW h ^ K.card else 0)
            = ({ω : Config V | cluster ω o = (K : Set V)}.indicator
                (fun _ => (K.card : ℝ≥0∞) * ghostW h ^ K.card)) := by
          funext ω
          by_cases hω : cluster ω o = (K : Set V) <;> simp [hω]
        rw [hid, lintegral_indicator (measurableSet_cluster_eq_finset o K), setLIntegral_const]
        ac_rfl


/-! ## The deterministic exit decomposition with `x` in the cluster shape -/

/-- A finite cluster is one of the finset shapes: the set of finite clusters is the union of the
events `{cluster · o = K}`. -/
theorem cluster_eq_finset_of_finite {ω : Config V} {o : V} (hfin : (cluster ω o).Finite) :
    cluster ω o = ((hfin.toFinset : Finset V) : Set V) := by
  rw [hfin.coe_toFinset]

/-- **The exit decomposition** (deterministic part), with the origin `x` of the fresh edge lying
in the finite cluster shape `K`: a new ghost-hit at `o` that is not a ghost-hit of the cut-off
configuration is contained either in a per-cluster block `blockSet o K x y` with `x ∈ K`, or in
the null event that the cut-off cluster of `o` is infinite. -/
theorem exitEvent_subset_iUnion_blockSet (o : V) :
    exitEvent o ⊆ (⋃ (K : Finset V) (x : {x : V // x ∈ K}) (y : V), blockSet o K x.1 y)
      ∪ {z : (Config V × Config V) × (V → Prop) | clusterVol z.1.1 o = ⊤} := by
  rintro ⟨⟨ω, η⟩, G⟩ ⟨hG, hnG⟩
  by_cases htop : clusterVol ω o = ⊤
  · exact Or.inr htop
  · have hfin : (cluster ω o).Finite := by
      by_contra hinf
      exact htop ((clusterVol_eq_top_iff ω o).mpr hinf)
    obtain ⟨x, hx, y, hy, hfull, hnot, v, hGv, q, hq⟩ :=
      exists_fresh_exit_of_ghost (ω := ω) (θ := unionConf (ω, η))
        (fun e he => Or.inl he) hG hnG
    have hfresh : s(x, y) ∈ η := by
      rcases hfull with h | h
      · exact absurd h hnot
      · exact h
    have havoid : ∀ u ∈ cluster ω o, ¬ G u := by
      intro u hu huG
      exact hnG ⟨u, hu, huG⟩
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
    refine Or.inl ?_
    refine Set.mem_iUnion.mpr ⟨hfin.toFinset, ?_⟩
    refine Set.mem_iUnion.mpr ⟨⟨x, hfin.mem_toFinset.mpr hx⟩, ?_⟩
    refine Set.mem_iUnion.mpr ⟨y, ?_⟩
    rw [blockSet_mem]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hfin.coe_toFinset]
    · exact hfresh
    · intro u hu
      exact havoid u (hfin.mem_toFinset.mp hu)
    · rw [hfin.coe_toFinset]
      exact hoff

theorem measurableSet_iUnion_blockSet (o : V) :
    MeasurableSet (⋃ (K : Finset V) (x : {x : V // x ∈ K}) (y : V), blockSet o K x.1 y) :=
  MeasurableSet.iUnion fun K => MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y =>
    measurableSet_blockSet o K x.1 y

theorem measurableSet_clusterVol_top (o : V) :
    MeasurableSet {z : (Config V × Config V) × (V → Prop) | clusterVol z.1.1 o = ⊤} :=
  (measurable_clusterVol o (measurableSet_singleton ⊤)).preimage
    (measurable_fst.comp measurable_fst)

/-- The part of the exit event carried by an infinite cut-off cluster is null. -/
theorem coupledMeasure_exitEvent_inter_infinite (π ρ : Sym2 V → unitInterval) (h : ℝ≥0)
    (hh : 0 < h) (o : V) :
    coupledMeasure π ρ h (exitEvent o ∩
      {z : (Config V × Config V) × (V → Prop) | clusterVol z.1.1 o = ⊤}) = 0 := by
  refine measure_mono_null ?_ (measure_avoid_infinite ρ (shiftProb π ρ) h hh o)
  rintro z ⟨hz, htop⟩
  exact ⟨hz.2, htop⟩

/-- **The countable union bound for the exit event.** -/
theorem coupledMeasure_exitEvent_le_tsum (π ρ : Sym2 V → unitInterval) (h : ℝ≥0)
    (hh : 0 < h) (o : V) :
    coupledMeasure π ρ h (exitEvent o) ≤
      ∑' (K : Finset V) (x : {x : V // x ∈ K}) (y : V),
        coupledMeasure π ρ h (blockSet o K x.1 y) := by
  have hzero := coupledMeasure_exitEvent_inter_infinite π ρ h hh o
  have hsplit := measure_inter_add_sdiff (μ := coupledMeasure π ρ h) (exitEvent o)
    (measurableSet_clusterVol_top o)
  have hsub : exitEvent o \ {z : (Config V × Config V) × (V → Prop) | clusterVol z.1.1 o = ⊤}
      ⊆ ⋃ (K : Finset V) (x : {x : V // x ∈ K}) (y : V), blockSet o K x.1 y := by
    intro z hz
    rcases hz with ⟨hzE, hznot⟩
    rcases exitEvent_subset_iUnion_blockSet o hzE with h | h
    · exact h
    · exact absurd h hznot
  calc coupledMeasure π ρ h (exitEvent o)
      = coupledMeasure π ρ h (exitEvent o ∩
          {z : (Config V × Config V) × (V → Prop) | clusterVol z.1.1 o = ⊤})
        + coupledMeasure π ρ h (exitEvent o \
          {z : (Config V × Config V) × (V → Prop) | clusterVol z.1.1 o = ⊤}) := hsplit.symm
    _ = coupledMeasure π ρ h (exitEvent o \
          {z : (Config V × Config V) × (V → Prop) | clusterVol z.1.1 o = ⊤}) := by
        rw [hzero, zero_add]
    _ ≤ coupledMeasure π ρ h
          (⋃ (K : Finset V) (x : {x : V // x ∈ K}) (y : V), blockSet o K x.1 y) :=
        measure_mono hsub
    _ ≤ ∑' K : Finset V,
          coupledMeasure π ρ h (⋃ (x : {x : V // x ∈ K}) (y : V), blockSet o K x.1 y) :=
        measure_iUnion_le _
    _ ≤ ∑' K : Finset V, ∑' x : {x : V // x ∈ K},
          coupledMeasure π ρ h (⋃ y : V, blockSet o K x.1 y) :=
        ENNReal.tsum_le_tsum fun K => measure_iUnion_le _
    _ ≤ ∑' (K : Finset V) (x : {x : V // x ∈ K}) (y : V),
          coupledMeasure π ρ h (blockSet o K x.1 y) :=
        ENNReal.tsum_le_tsum fun K =>
          ENNReal.tsum_le_tsum fun x => measure_iUnion_le _

/-- **Pure summation lemma**: the per-cluster bound `|K| P(K) e^{-h|K|} G q_{xy}` summed over
shapes, origins in the shape and targets is bounded by `D` times the weighted cluster-shape sum
times `G`.  The origin-local degree bound `D` is applied once for each `x ∈ K`, which is exactly
what produces the factor `|K|`. -/
theorem tsum_subtype_mul_le (A W : Finset V → ℝ≥0∞) (q : V → V → ℝ≥0∞) (D G : ℝ≥0∞)
    (hD : ∀ x : V, (∑' y : V, q x y) ≤ D) :
    (∑' (K : Finset V) (x : {x : V // x ∈ K}) (y : V), (A K * W K * G) * q x.1 y)
      ≤ D * (∑' K : Finset V, (K.card : ℝ≥0∞) * A K * W K) * G := by
  calc (∑' (K : Finset V) (x : {x : V // x ∈ K}) (y : V), (A K * W K * G) * q x.1 y)
      = ∑' K : Finset V, ∑' x : {x : V // x ∈ K}, (A K * W K * G) * (∑' y : V, q x.1 y) := by
        refine tsum_congr fun K => tsum_congr fun x => ?_
        exact ENNReal.tsum_mul_left
    _ ≤ ∑' K : Finset V, ∑' x : {x : V // x ∈ K}, (A K * W K * G) * D := by
        refine ENNReal.tsum_le_tsum fun K => ENNReal.tsum_le_tsum fun x => ?_
        exact mul_le_mul_right (hD x.1) _
    _ = ∑' K : Finset V, (K.card : ℝ≥0∞) * (A K * W K * G * D) := by
        refine tsum_congr fun K => ?_
        rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    _ = (∑' K : Finset V, (K.card : ℝ≥0∞) * A K * W K) * (G * D) := by
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun K => ?_
        ac_rfl
    _ = D * (∑' K : Finset V, (K.card : ℝ≥0∞) * A K * W K) * G := by
        ac_rfl

/-- **The exit probability is bounded by the global error term.** -/
theorem coupledMeasure_exitEvent_le (π ρ : Sym2 V → unitInterval) (h : ℝ≥0)
    (hρπ : ∀ e, ρ e ≤ π e) (hh : 0 < h) (o : V) (D G : ℝ≥0∞)
    (hD : ∀ x : V, (∑' y : V,
      ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)) ≤ D)
    (hG : ∀ y : V, ghostHits π h y ≤ G) :
    coupledMeasure π ρ h (exitEvent o) ≤ D * weightedGhostMass ρ h o * G := by
  have hblock : (∑' (K : Finset V) (x : {x : V // x ∈ K}) (y : V),
        coupledMeasure π ρ h (blockSet o K x.1 y))
      ≤ ∑' (K : Finset V) (x : {x : V // x ∈ K}) (y : V),
          ((edgeMeasure ρ) {ω : Config V | cluster ω o = (K : Set V)} * ghostW h ^ K.card * G)
            * ENNReal.ofReal ((shiftProb π ρ (s(x.1, y)) : unitInterval) : ℝ) := by
    refine ENNReal.tsum_le_tsum fun K => ENNReal.tsum_le_tsum fun x =>
      ENNReal.tsum_le_tsum fun y => ?_
    calc coupledMeasure π ρ h (blockSet o K x.1 y)
        ≤ (edgeMeasure ρ) {ω : Config V | cluster ω o = (K : Set V)} *
            ENNReal.ofReal ((shiftProb π ρ (s(x.1, y)) : unitInterval) : ℝ) *
              ghostW h ^ K.card * G :=
          blockSet_measure_le π ρ h hρπ o G hG K x.1 y x.2
      _ = ((edgeMeasure ρ) {ω : Config V | cluster ω o = (K : Set V)} * ghostW h ^ K.card * G)
            * ENNReal.ofReal ((shiftProb π ρ (s(x.1, y)) : unitInterval) : ℝ) := by
          ac_rfl
  refine (coupledMeasure_exitEvent_le_tsum π ρ h hh o).trans (hblock.trans ?_)
  have hmain := tsum_subtype_mul_le
    (fun K : Finset V => (edgeMeasure ρ) {ω : Config V | cluster ω o = (K : Set V)})
    (fun K : Finset V => ghostW h ^ K.card)
    (fun x y : V => ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)) D G hD
  refine hmain.trans ?_
  rw [weightedGhostMass_eq_tsum ρ h hh o]


/-! ## The global full-law ghost-restoration inequality -/

/-- **Global full-law ghost-restoration inequality (I.3.5), single full-law factor.**
Under `ρ ≤ π`, at positive intensity `h`, if `D` bounds the origin-local fresh-edge mass
`∑'_y q_{xy}` at every vertex `x` and `G` bounds the full-law ghost-hit probability at every
target `y`, then

`ghostHits π h o ≤ ghostHits ρ h o + D · E_ρ[|K_o| e^{-h|K_o|}] · G`.

No cutoff ghost probability appears: `G` is a full-law quantity, and the `|K|` factor is the
genuine multiplicity of the summation over the origin `x ∈ K` of the exit edge. -/
theorem ghostHits_le_add_weightedGhostMass (π ρ : Sym2 V → unitInterval) (h : ℝ≥0)
    (hρπ : ∀ e, ρ e ≤ π e) (hh : 0 < h) (o : V) (D G : ℝ≥0∞)
    (hD : ∀ x : V, (∑' y : V,
      ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)) ≤ D)
    (hG : ∀ y : V, ghostHits π h y ≤ G) :
    ghostHits π h o ≤ ghostHits ρ h o + D * weightedGhostMass ρ h o * G := by
  rw [ghostHits_eq_add_exitEvent π ρ hρπ h o]
  exact add_le_add_right (coupledMeasure_exitEvent_le π ρ h hρπ hh o D G hD hG) _

/-- The same inequality with the optimal origin-local constant `D = ⨆_x ∑'_y q_{xy}`. -/
theorem ghostHits_le_add_weightedGhostMass_iSup (π ρ : Sym2 V → unitInterval) (h : ℝ≥0)
    (hρπ : ∀ e, ρ e ≤ π e) (hh : 0 < h) (o : V) (G : ℝ≥0∞)
    (hG : ∀ y : V, ghostHits π h y ≤ G) :
    ghostHits π h o ≤ ghostHits ρ h o +
      (⨆ x : V, ∑' y : V, ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ))
        * weightedGhostMass ρ h o * G :=
  ghostHits_le_add_weightedGhostMass π ρ h hρπ hh o _ G
    (fun x => le_iSup (fun x : V =>
      ∑' y : V, ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)) x) hG


/-- Every ghost-hit probability is at most `1`. -/
theorem ghostHits_le_one (π : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) :
    ghostHits π h o ≤ 1 := by
  rw [ghostHits, ← measure_univ (μ := (edgeMeasure π).prod (ghostLaw h))]
  exact measure_mono (Set.subset_univ _)

/-- The inequality with the full-law factor taken to be the trivial bound `G = 1`; this removes
the second hypothesis entirely, leaving only the origin-local fresh-edge degree bound `D`. -/
theorem ghostHits_le_add_weightedGhostMass_one (π ρ : Sym2 V → unitInterval) (h : ℝ≥0)
    (hρπ : ∀ e, ρ e ≤ π e) (hh : 0 < h) (o : V) (D : ℝ≥0∞)
    (hD : ∀ x : V, (∑' y : V,
      ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)) ≤ D) :
    ghostHits π h o ≤ ghostHits ρ h o + D * weightedGhostMass ρ h o := by
  have h := ghostHits_le_add_weightedGhostMass π ρ h hρπ hh o D 1 hD
    (fun y => ghostHits_le_one π h y)
  simpa using h


/-- The same inequality with the optimal full-law factor `G = ⨆_y ghostHits π h y`. -/
theorem ghostHits_le_add_weightedGhostMass_gsup (π ρ : Sym2 V → unitInterval) (h : ℝ≥0)
    (hρπ : ∀ e, ρ e ≤ π e) (hh : 0 < h) (o : V) (D : ℝ≥0∞)
    (hD : ∀ x : V, (∑' y : V,
      ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)) ≤ D) :
    ghostHits π h o ≤ ghostHits ρ h o +
      D * weightedGhostMass ρ h o * (⨆ y : V, ghostHits π h y) :=
  ghostHits_le_add_weightedGhostMass π ρ h hρπ hh o D _
    hD (fun y => le_iSup (fun y : V => ghostHits π h y) y)

/-- The inequality with both optimal constants `D = ⨆_x ∑'_y q_{xy}` and
`G = ⨆_y ghostHits π h y`, and no extra hypotheses. -/
theorem ghostHits_le_add_weightedGhostMass_iSup_iSup (π ρ : Sym2 V → unitInterval) (h : ℝ≥0)
    (hρπ : ∀ e, ρ e ≤ π e) (hh : 0 < h) (o : V) :
    ghostHits π h o ≤ ghostHits ρ h o +
      (⨆ x : V, ∑' y : V, ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ))
        * weightedGhostMass ρ h o * (⨆ y : V, ghostHits π h y) :=
  ghostHits_le_add_weightedGhostMass_gsup π ρ h hρπ hh o _
    (fun x => le_iSup (fun x : V =>
      ∑' y : V, ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)) x)

/-- Alternate explicitly quantified interface to the accepted global restoration bound. -/
theorem ghostHits_le_of_degree {π ρ : Sym2 V → unitInterval} (hρπ : ∀ e, ρ e ≤ π e)
    {h : ℝ≥0} (hh : 0 < h) (o : V) (D G : ℝ≥0∞)
    (hD : ∀ x : V, (∑' y : V,
      ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)) ≤ D)
    (hG : ∀ y : V, ghostHits π h y ≤ G) :
    ghostHits π h o ≤ ghostHits ρ h o + D * weightedGhostMass ρ h o * G :=
  ghostHits_le_add_weightedGhostMass π ρ h hρπ hh o D G hD hG

end PercLib.CriticalLRP
