/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The per-cluster factorization of the full-law ghost-restoration error

For a fixed finite cutoff cluster `K`, this module factors the independent edge
and ghost blocks. It bounds the joint weight of a fresh exit edge, ghost avoidance
of `K`, and an off-cluster ghost-hit by
`P_ρ(cluster = K) * q_{x,y} * ghostW h ^ |K| * G`, where `G` bounds the
**full-law** ghost-hit probability at every vertex.

The fresh edge is not assumed independent of the random cluster by assertion.
Instead, the cluster event is measurable for the fixed block of edges touching
`K`, and the off-cluster walk uses the complementary block. The remaining outer
union is identified with the full law by `unionMeasure_eq_edgeMeasure`.
-/
module

public import PercLib.CriticalLRP.CountableProduct.GhostIndependence

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

/-! ## The off-cluster exploration event is insensitive to the two blocks it avoids -/

/-- `restrictConf` depends only on the edges that touch neither endpoint of anything in `K`. -/
theorem restrictConf_congr {K : Set V} {θ θ' : Config V}
    (h : ∀ e, e ∉ edgeTouch K → (e ∈ θ' ↔ e ∈ θ)) : restrictConf K θ' = restrictConf K θ := by
  ext e
  by_cases he : e ∈ edgeTouch K
  · simp [mem_restrictConf, he]
  · rw [mem_restrictConf, mem_restrictConf, h e he]

/-- The off-cluster exploration event only depends on the configuration through the edges that
avoid `K`. -/
theorem offCluster_congr_conf {K : Set V} {y : V} {θ θ' : Config V} {G : V → Prop}
    (h : ∀ e, e ∉ edgeTouch K → (e ∈ θ' ↔ e ∈ θ)) :
    (offCluster K y (θ', G) ↔ offCluster K y (θ, G)) := by
  have hcl := restrictConf_congr h
  constructor
  · rintro ⟨v, hvK, hv, hcl'⟩
    exact ⟨v, hvK, hv, hcl ▸ hcl'⟩
  · rintro ⟨v, hvK, hv, hcl'⟩
    exact ⟨v, hvK, hv, hcl.symm ▸ hcl'⟩

/-- The off-cluster exploration event only depends on the ghost marks outside `K`. -/
theorem offCluster_congr_ghost {K : Set V} {y : V} {θ : Config V} {G G' : V → Prop}
    (h : ∀ v, v ∉ K → (G' v ↔ G v)) :
    (offCluster K y (θ, G') ↔ offCluster K y (θ, G)) := by
  constructor
  · rintro ⟨v, hvK, hv, hcl⟩
    exact ⟨v, hvK, (h v hvK).mp hv, hcl⟩
  · rintro ⟨v, hvK, hv, hcl⟩
    exact ⟨v, hvK, (h v hvK).mpr hv, hcl⟩

/-- The off-cluster exploration event is contained in the event that the ghost hits the cluster
of `y`: the marked vertex is reached by an open walk. -/
theorem offCluster_subset_ghostConnected (K : Set V) (y : V) :
    offCluster K y ⊆ GhostConnected y := by
  rintro ⟨θ, G⟩ ⟨v, -, hGv, hv⟩
  exact ⟨v, cluster_mono (fun e he => he.1) y hv, hGv⟩

/-! ## The per-cluster block -/

/-- The block of the exit decomposition attached to a finite cluster shape `K`, a boundary vertex
`x ∈ K` and a target `y`: the cut-off cluster is `K`, the edge `{x,y}` is fresh, the ghost avoids
`K`, and the ghost is reached from `y` by a walk avoiding `K`. -/
def blockSet (o : V) (K : Finset V) (x y : V) : Set ((Config V × Config V) × (V → Prop)) :=
  {z | (cluster z.1.1 o = (K : Set V) ∧ s(x, y) ∈ z.1.2) ∧
        ((∀ v ∈ K, ¬ z.2 v) ∧ offCluster (K : Set V) y (unionConf z.1, z.2))}

theorem blockSet_mem {o : V} {K : Finset V} {x y : V} {z : (Config V × Config V) × (V → Prop)} :
    z ∈ blockSet o K x y ↔ (cluster z.1.1 o = (K : Set V) ∧ s(x, y) ∈ z.1.2) ∧
      ((∀ v ∈ K, ¬ z.2 v) ∧ offCluster (K : Set V) y (unionConf z.1, z.2)) := Iff.rfl

theorem measurableSet_blockSet (o : V) (K : Finset V) (x y : V) :
    MeasurableSet (blockSet (V := V) o K x y) := by
  have h1 : MeasurableSet {z : (Config V × Config V) × (V → Prop) |
      cluster z.1.1 o = (K : Set V)} :=
    (measurableSet_cluster_eq_finset o K).preimage (measurable_fst.comp measurable_fst)
  have h2 : MeasurableSet {z : (Config V × Config V) × (V → Prop) | s(x, y) ∈ z.1.2} :=
    (measurableSet_mem (s(x, y))).preimage (measurable_snd.comp measurable_fst)
  have h3 : MeasurableSet {z : (Config V × Config V) × (V → Prop) | ∀ v ∈ K, ¬ z.2 v} := by
    rw [show {z : (Config V × Config V) × (V → Prop) | ∀ v ∈ K, ¬ z.2 v}
        = ⋂ v ∈ K, {z : (Config V × Config V) × (V → Prop) | ¬ z.2 v} from by
      ext z; simp]
    refine Finset.measurableSet_biInter K fun v _ => ?_
    have h : Measurable fun z : (Config V × Config V) × (V → Prop) => z.2 v :=
      (measurable_pi_apply v).comp measurable_snd
    have := h (t := {q : Prop | ¬ q}) (by measurability)
    simpa using this
  have h4 : MeasurableSet {z : (Config V × Config V) × (V → Prop) |
      offCluster (K : Set V) y (unionConf z.1, z.2)} :=
    (measurableSet_offCluster (K : Set V) y).preimage
      ((measurable_unionConf.comp measurable_fst).prodMk measurable_snd)
  have h : blockSet (V := V) o K x y
      = ({z : (Config V × Config V) × (V → Prop) | cluster z.1.1 o = (K : Set V)}
          ∩ {z : (Config V × Config V) × (V → Prop) | s(x, y) ∈ z.1.2})
        ∩ ({z : (Config V × Config V) × (V → Prop) | ∀ v ∈ K, ¬ z.2 v}
            ∩ {z : (Config V × Config V) × (V → Prop) |
                offCluster (K : Set V) y (unionConf z.1, z.2)}) := rfl
  rw [h]
  exact (h1.inter h2).inter (h3.inter h4)

/-- The indicator of an intersection of two sets is the product of the indicators. -/
theorem indicator_inter_one {α : Type*} [MeasurableSpace α] (s t : Set α) (z : α) :
    (s ∩ t).indicator (fun _ => (1 : ℝ≥0∞)) z
      = s.indicator (fun _ => (1 : ℝ≥0∞)) z * t.indicator (fun _ => (1 : ℝ≥0∞)) z := by
  by_cases hs : z ∈ s <;> by_cases ht : z ∈ t <;> simp [hs, ht]

/-- **The indicator of the per-cluster block factorises into the four coordinate blocks**: the
cut-off cluster (which sees only the edges meeting `K`), the fresh edge (a single edge meeting
`K`), the avoidance of `K` by the ghost (the marks on `K`), and the off-cluster exploration (the
edges avoiding `K` and the marks outside `K`). -/
theorem blockSet_indicator (o : V) (K : Finset V) (x y : V)
    (ω η : Config V) (G : V → Prop) :
    (blockSet o K x y).indicator (fun _ => (1 : ℝ≥0∞)) ((ω, η), G)
      = (({ω' : Config V | cluster ω' o = (K : Set V)}.indicator (fun _ => (1 : ℝ≥0∞)) ω)
          * (if s(x, y) ∈ η then (1 : ℝ≥0∞) else 0))
        * (ghostAvoidInd K G
            * (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G)) := by
  have hT : blockSet (V := V) o K x y
      = ({z : (Config V × Config V) × (V → Prop) | cluster z.1.1 o = (K : Set V)}
          ∩ {z : (Config V × Config V) × (V → Prop) | s(x, y) ∈ z.1.2})
        ∩ ({z : (Config V × Config V) × (V → Prop) | ∀ v ∈ K, ¬ z.2 v}
            ∩ {z : (Config V × Config V) × (V → Prop) |
                offCluster (K : Set V) y (unionConf z.1, z.2)}) := rfl
  rw [hT, indicator_inter_one, indicator_inter_one, indicator_inter_one]
  have h3 : ({z : (Config V × Config V) × (V → Prop) | ∀ v ∈ K, ¬ z.2 v}).indicator
        (fun _ => (1 : ℝ≥0∞)) ((ω, η), G) = ghostAvoidInd K G := by
    by_cases h : ∀ v ∈ K, ¬ G v
    · rw [Set.indicator_of_mem (show ((ω, η), G) ∈ {z : (Config V × Config V) × (V → Prop) |
          ∀ v ∈ K, ¬ z.2 v} from h), ghostAvoidInd,
        Set.indicator_of_mem (show G ∈ ghostAvoids K from h)]
    · rw [Set.indicator_of_notMem (show ((ω, η), G) ∉ {z : (Config V × Config V) × (V → Prop) |
          ∀ v ∈ K, ¬ z.2 v} from h), ghostAvoidInd,
        Set.indicator_of_notMem (show G ∉ ghostAvoids K from h)]
  rw [h3]
  rfl



/-! ## The per-cluster mixed block bound -/

/-- The mass of the fresh edge `{x,y}` under the shift law: `q_{xy}`. -/
theorem lintegral_coord_true (q : Sym2 V → unitInterval) (a : Sym2 V) :
    ∫⁻ c : Prop, (if c then (1 : ℝ≥0∞) else 0)
        ∂(bernoulliMeasure (True : Prop) (False : Prop) (q a))
      = ENNReal.ofReal ((q a : unitInterval) : ℝ) := by
  have hfun : (fun c : Prop => if c then (1 : ℝ≥0∞) else 0)
      = ({True} : Set Prop).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext c
    by_cases hc : c <;> simp [hc]
  rw [hfun, lintegral_indicator (measurableSet_singleton True), setLIntegral_one, ber_true]



theorem unionConf_forceOn_of_notMem {S : Set (Sym2 V)} {e : Sym2 V} (he : e ∉ S)
    (ω η' η : Config V) :
    (e ∈ unionConf (ω, forceOn S η' η) ↔ e ∈ unionConf (ω, η)) := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rwa [mem_forceOn_of_notMem he] at h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [mem_forceOn_of_notMem he]; exact h)

theorem unionConf_congr_of_forget {S : Set (Sym2 V)} {ω ω' η : Config V}
    (hag : ∀ e, e ∉ S → (e ∈ ω' ↔ e ∈ ω)) {e : Sym2 V} (he : e ∉ S) :
    (e ∈ unionConf (ω', η) ↔ e ∈ unionConf (ω, η)) := by
  constructor
  · rintro (h | h)
    · exact Or.inl ((hag e he).mp h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((hag e he).mpr h)
    · exact Or.inr h

/-! ## Measurability of the off-cluster integrands -/

theorem measurable_off_indicator (K : Set V) (y : V) :
    Measurable fun p : Config V × (V → Prop) =>
      (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) p :=
  Measurable.indicator measurable_const (measurableSet_offCluster K y)

theorem measurable_off_pair (K : Set V) (y : V) (ω : Config V) :
    Measurable fun p : Config V × (V → Prop) =>
      (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, p.1), p.2) :=
  (measurable_off_indicator K y).comp
    ((measurable_unionConf.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)

theorem measurable_off_integral_G (h : ℝ≥0) (K : Set V) (y : V) :
    Measurable fun θ : Config V =>
      ∫⁻ G, (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) (θ, G) ∂(ghostLaw h) :=
  Measurable.lintegral_prod_right' (measurable_off_indicator K y)

theorem measurable_off_integral_eta (h : ℝ≥0) (K : Set V) (y : V) (ω : Config V) :
    Measurable fun η : Config V =>
      ∫⁻ G, (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G)
        ∂(ghostLaw h) :=
  Measurable.lintegral_prod_right' (measurable_off_pair K y ω)

theorem measurable_off_integral_pair (h : ℝ≥0) (K : Set V) (y : V) :
    Measurable fun p : Config V × Config V =>
      ∫⁻ G, (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf p, G)
        ∂(ghostLaw h) :=
  Measurable.lintegral_prod_right' (f := fun q : (Config V × Config V) × (V → Prop) =>
    (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf q.1, q.2))
    (measurable_off_indicator K y |>.comp
      ((measurable_unionConf.comp measurable_fst).prodMk measurable_snd))

theorem measurable_off_integral_omega (h : ℝ≥0) (K : Set V) (y : V) :
    Measurable fun ω : Config V =>
      ∫⁻ η, ∫⁻ G, (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G)
        ∂(ghostLaw h) ∂(edgeMeasure (shiftProb π ρ)) :=
  Measurable.lintegral_prod_right' (f := fun p : Config V × Config V =>
    ∫⁻ G, (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf p, G) ∂(ghostLaw h))
    (measurable_off_integral_pair h K y)

/-- **The per-cluster mixed block bound.**  For a finite cluster shape `K`, a vertex `x ∈ K`, any
`y`, a full-law ghost-hit bound `G`, the joint probability in the monotone coupling
`(ω, η, ghost)` of

* the cut-off cluster of `o` being `K`,
* the edge `{x,y}` being fresh (present in `η`),
* the ghost avoiding `K`,
* the ghost being reached from `y` by a walk avoiding `K`,

is at most `P_ρ(cluster = K) · q_{xy} · e^{-h|K|} · G`. -/
theorem blockSet_measure_le (π ρ : Sym2 V → unitInterval) (h : ℝ≥0)
    (hρπ : ∀ e, ρ e ≤ π e) (o : V) (G : ℝ≥0∞) (hG : ∀ y : V, ghostHits π h y ≤ G)
    (K : Finset V) (x y : V) (hx : x ∈ K) :
    (((edgeMeasure ρ).prod (edgeMeasure (shiftProb π ρ))).prod (ghostLaw h)) (blockSet o K x y)
      ≤ edgeMeasure ρ {ω : Config V | cluster ω o = (K : Set V)} *
          ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ) * ghostW h ^ K.card * G := by
  classical
  set q : Sym2 V → unitInterval := shiftProb π ρ with hq
  set S : Set (Sym2 V) := edgeTouch (K : Set V) with hS
  set AK : Set (Config V) := {ω : Config V | cluster ω o = (K : Set V)} with hAK
  set a : Sym2 V := s(x, y) with ha
  set T : Set ((Config V × Config V) × (V → Prop)) := blockSet o K x y with hT
  have hTmeas : MeasurableSet T := measurableSet_blockSet o K x y
  have hoffmeas : MeasurableSet (offCluster (K : Set V) y) := measurableSet_offCluster _ _
  have hAKmeas : MeasurableSet AK := measurableSet_cluster_eq_finset o K
  have haK : a ∈ S := by
    rw [ha, hS]
    exact ⟨x, Finset.mem_coe.mpr hx, Sym2.mem_mk_left x y⟩
  have hifmeas : Measurable fun η : Config V => (if η a then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_mem a) measurable_const measurable_const
  -- master measurability of the off-cluster indicator on the product space
  have hmaster : Measurable fun p : Config V × (V → Prop) =>
      (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) p :=
    Measurable.indicator measurable_const hoffmeas
  have havoidm : Measurable fun G : V → Prop => ghostAvoidInd K G :=
    Measurable.indicator measurable_const (measurableSet_ghostAvoids K)
  have hAKm : Measurable fun ω : Config V => AK.indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    Measurable.indicator measurable_const hAKmeas
  -- the indicator factorisation of the block
  have hTind : ∀ (ω η : Config V) (G : V → Prop),
      T.indicator (fun _ => (1 : ℝ≥0∞)) ((ω, η), G)
        = (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω * (if η a then (1 : ℝ≥0∞) else 0))
          * (ghostAvoidInd K G
              * (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G)) := by
    intro ω η G
    have hh := blockSet_indicator o K x y ω η G
    rw [← hT, ← hAK, ← ha] at hh
    exact hh
  -- the remaining function of the cut-off configuration
  set gfun : Config V → ℝ≥0∞ :=
    fun ω => ∫⁻ η, ∫⁻ G, (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞))
      (unionConf (ω, η), G) ∂(ghostLaw h) ∂(edgeMeasure q) with hgfun
  -- Step 1: the measure is the integral of the indicator
  have hstep1 : (((edgeMeasure ρ).prod (edgeMeasure q)).prod (ghostLaw h)) T
      = ∫⁻ z, T.indicator (fun _ => (1 : ℝ≥0∞)) z
          ∂(((edgeMeasure ρ).prod (edgeMeasure q)).prod (ghostLaw h)) := by
    rw [lintegral_indicator hTmeas (fun _ => (1 : ℝ≥0∞)), setLIntegral_one]
  -- Step 2: Tonelli
  have hTindmeas : Measurable fun z : (Config V × Config V) × (V → Prop) =>
      T.indicator (fun _ => (1 : ℝ≥0∞)) z :=
    Measurable.indicator measurable_const hTmeas
  have hstep2 : ∫⁻ z, T.indicator (fun _ => (1 : ℝ≥0∞)) z
        ∂(((edgeMeasure ρ).prod (edgeMeasure q)).prod (ghostLaw h))
      = ∫⁻ ω, ∫⁻ η, ∫⁻ G, T.indicator (fun _ => (1 : ℝ≥0∞)) ((ω, η), G)
          ∂(ghostLaw h) ∂(edgeMeasure q) ∂(edgeMeasure ρ) := by
    rw [lintegral_prod (μ := (edgeMeasure ρ).prod (edgeMeasure q)) (ν := ghostLaw h)
      _ hTindmeas.aemeasurable]
    exact lintegral_prod (μ := edgeMeasure ρ) (ν := edgeMeasure q)
      (f := fun p : Config V × Config V => ∫⁻ G,
        T.indicator (fun _ => (1 : ℝ≥0∞)) ((p.1, p.2), G) ∂(ghostLaw h))
      (Measurable.lintegral_prod_right' (hTindmeas.comp (measurable_fst.prodMk measurable_snd))).aemeasurable
  -- Step 3: the ghost integral, using the avoidance factorisation
  have hstep3 : ∀ ω η : Config V,
      ∫⁻ G, T.indicator (fun _ => (1 : ℝ≥0∞)) ((ω, η), G) ∂(ghostLaw h)
        = (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω * (if η a then (1 : ℝ≥0∞) else 0))
          * (ghostW h ^ K.card * ∫⁻ G, (offCluster (K : Set V) y).indicator
              (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) ∂(ghostLaw h)) := by
    intro ω η
    have hinv : ∀ G G' : V → Prop, (∀ v, v ∉ (K : Set V) → (G' v ↔ G v)) →
        (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G')
          = (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) := by
      intro G G' hag
      by_cases h4 : (unionConf (ω, η), G) ∈ offCluster (K : Set V) y
      · have h4' : (unionConf (ω, η), G') ∈ offCluster (K : Set V) y :=
          (offCluster_congr_ghost hag).mpr h4
        rw [Set.indicator_of_mem h4, Set.indicator_of_mem h4']
      · have h4' : (unionConf (ω, η), G') ∉ offCluster (K : Set V) y :=
          fun hh => h4 ((offCluster_congr_ghost (fun v hv => (hag v hv).symm)).mpr hh)
        rw [Set.indicator_of_notMem h4, Set.indicator_of_notMem h4']
    have hmeas : Measurable fun G : V → Prop =>
        (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) :=
      hmaster.comp (measurable_const.prodMk measurable_id)
    have hkey : ∫⁻ G, ghostAvoidInd K G * ((offCluster (K : Set V) y).indicator
          (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G)) ∂(ghostLaw h)
        = ghostW h ^ K.card * ∫⁻ G, (offCluster (K : Set V) y).indicator
            (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) ∂(ghostLaw h) :=
      lintegral_ghostAvoid_mul h K hmeas hinv
    have hfac := hTind ω η
    have hconst : Measurable fun G : V → Prop => ghostAvoidInd K G *
        (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) :=
      havoidm.mul hmeas
    simp only [hfac]
    rw [lintegral_const_mul _ hconst, hkey]
  -- Step 4: the fresh-edge integral
  have hstep4 : ∀ ω : Config V,
      ∫⁻ η, (∫⁻ G, T.indicator (fun _ => (1 : ℝ≥0∞)) ((ω, η), G) ∂(ghostLaw h))
          ∂(edgeMeasure q)
        = (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω)
          * (ghostW h ^ K.card * (ENNReal.ofReal ((q a : unitInterval) : ℝ) * gfun ω)) := by
    intro ω
    have hoffint : Measurable fun η : Config V =>
        ∫⁻ G, (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞))
          (unionConf (ω, η), G) ∂(ghostLaw h) :=
      measurable_off_integral_eta h (K : Set V) y ω
    have hgerr : Measurable fun η : Config V =>
        ghostW h ^ K.card * ∫⁻ G, (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞))
          (unionConf (ω, η), G) ∂(ghostLaw h) := measurable_const.mul hoffint
    have hinvη : ∀ η' η : Config V,
        (ghostW h ^ K.card * ∫⁻ G, (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞))
          (unionConf (ω, forceOn ({a} : Set (Sym2 V)) η' η), G) ∂(ghostLaw h))
        = ghostW h ^ K.card * ∫⁻ G, (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞))
            (unionConf (ω, η), G) ∂(ghostLaw h) := by
      intro η' η
      congr 1
      refine lintegral_congr fun G => ?_
      have hagree : ∀ e, e ∉ S → (e ∈ unionConf (ω, forceOn ({a} : Set (Sym2 V)) η' η)
          ↔ e ∈ unionConf (ω, η)) := by
        intro e he
        have hne : e ≠ a := fun hh => he (hh ▸ haK)
        exact unionConf_forceOn_of_notMem (S := ({a} : Set (Sym2 V))) (by simpa using hne) ω η' η
      have hiff := offCluster_congr_conf (K := (K : Set V)) (y := y)
        (θ := unionConf (ω, η)) (θ' := unionConf (ω, forceOn ({a} : Set (Sym2 V)) η' η))
        (G := G) (by rw [← hS]; exact hagree)
      by_cases h4 : (unionConf (ω, η), G) ∈ offCluster (K : Set V) y
      · have h4' : (unionConf (ω, forceOn ({a} : Set (Sym2 V)) η' η), G)
            ∈ offCluster (K : Set V) y := hiff.mpr h4
        rw [Set.indicator_of_mem h4, Set.indicator_of_mem h4']
      · have h4' : (unionConf (ω, forceOn ({a} : Set (Sym2 V)) η' η), G)
            ∉ offCluster (K : Set V) y := fun hh => h4 (hiff.mp hh)
        rw [Set.indicator_of_notMem h4, Set.indicator_of_notMem h4']
    have hcoord := lintegral_coord_mul q a (f := fun c : Prop => if c then (1 : ℝ≥0∞) else 0)
      hgerr hinvη
    rw [lintegral_coord_true q a] at hcoord
    calc ∫⁻ η, (∫⁻ G, T.indicator (fun _ => (1 : ℝ≥0∞)) ((ω, η), G) ∂(ghostLaw h))
          ∂(edgeMeasure q)
        = ∫⁻ η, (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω)
            * ((if η a then (1 : ℝ≥0∞) else 0)
              * (ghostW h ^ K.card * ∫⁻ G, (offCluster (K : Set V) y).indicator
                  (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) ∂(ghostLaw h)))
            ∂(edgeMeasure q) := by
          refine lintegral_congr fun η => ?_
          rw [hstep3 ω η, mul_assoc]
      _ = (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω)
            * ∫⁻ η, ((if η a then (1 : ℝ≥0∞) else 0)
              * (ghostW h ^ K.card * ∫⁻ G, (offCluster (K : Set V) y).indicator
                  (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) ∂(ghostLaw h)))
            ∂(edgeMeasure q) := by
          rw [lintegral_const_mul (f := fun η : Config V => (if η a then (1 : ℝ≥0∞) else 0)
            * (ghostW h ^ K.card * ∫⁻ G, (offCluster (K : Set V) y).indicator
                (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) ∂(ghostLaw h))) (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω) (hifmeas.mul hgerr)]
      _ = (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω)
            * (ENNReal.ofReal ((q a : unitInterval) : ℝ)
              * ∫⁻ η, (ghostW h ^ K.card * ∫⁻ G, (offCluster (K : Set V) y).indicator
                  (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) ∂(ghostLaw h))
                ∂(edgeMeasure q)) := by
          rw [hcoord]
      _ = (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω)
            * (ghostW h ^ K.card * (ENNReal.ofReal ((q a : unitInterval) : ℝ) * gfun ω)) := by
          rw [lintegral_const_mul _ hoffint]
          simp only [hgfun]
          ac_rfl
  -- Step 5: factor out the cut-off cluster event
  have hoffintg : Measurable fun ω : Config V =>
      ∫⁻ η, ∫⁻ G, (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞))
        (unionConf (ω, η), G) ∂(ghostLaw h) ∂(edgeMeasure q) := by
    rw [show (fun ω : Config V => ∫⁻ η, ∫⁻ G, (offCluster (K : Set V) y).indicator
        (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) ∂(ghostLaw h) ∂(edgeMeasure q))
      = (fun ω : Config V => ∫⁻ η, ∫⁻ G, (offCluster (K : Set V) y).indicator
        (fun _ => (1 : ℝ≥0∞)) (unionConf (ω, η), G) ∂(ghostLaw h)
          ∂(edgeMeasure (shiftProb π ρ))) from by rw [hq]]
    exact measurable_off_integral_omega h (K : Set V) y
  have hgfunblock : Measurable[blockSigma Sᶜ] gfun := by
    refine measurable_blockSigma_compl_of_forget hoffintg ?_
    intro ω ω' hag
    simp only [hgfun]
    have : ∀ η : Config V, ∀ e, e ∉ S →
        (e ∈ unionConf (ω', η) ↔ e ∈ unionConf (ω, η)) := by
      intro η e he
      exact unionConf_congr_of_forget (S := S) (e := e) hag (by rwa [hS] at he)
    refine lintegral_congr fun η => ?_
    refine lintegral_congr fun G => ?_
    have hiff2 := offCluster_congr_conf (K := (K : Set V)) (y := y)
      (θ := unionConf (ω, η)) (θ' := unionConf (ω', η)) (G := G) (by rw [← hS]; exact this η)
    by_cases h4 : (unionConf (ω, η), G) ∈ offCluster (K : Set V) y
    · have h4' : (unionConf (ω', η), G) ∈ offCluster (K : Set V) y := hiff2.mpr h4
      rw [Set.indicator_of_mem h4, Set.indicator_of_mem h4']
    · have h4' : (unionConf (ω', η), G) ∉ offCluster (K : Set V) y := fun hh => h4 (hiff2.mp hh)
      rw [Set.indicator_of_notMem h4, Set.indicator_of_notMem h4']
  have hAKblock : Measurable[blockSigma S] (AK.indicator (fun _ => (1 : ℝ≥0∞))) :=
    Measurable.indicator measurable_const (by
      rw [hAK, hS]; exact measurableSet_cluster_eq_finset_blockSigma o K)
  have hstep5 : ∫⁻ ω, (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω)
        * (ghostW h ^ K.card * (ENNReal.ofReal ((q a : unitInterval) : ℝ) * gfun ω))
        ∂(edgeMeasure ρ)
      = ghostW h ^ K.card * ENNReal.ofReal ((q a : unitInterval) : ℝ)
        * ((edgeMeasure ρ) AK * ∫⁻ ω, gfun ω ∂(edgeMeasure ρ)) := by
    have hfac : ∀ ω : Config V, (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω)
        * (ghostW h ^ K.card * (ENNReal.ofReal ((q a : unitInterval) : ℝ) * gfun ω))
        = (ghostW h ^ K.card * ENNReal.ofReal ((q a : unitInterval) : ℝ))
          * (AK.indicator (fun _ => (1 : ℝ≥0∞)) ω * gfun ω) := by
      intro ω; ac_rfl
    simp only [hfac]
    rw [lintegral_const_mul (f := fun ω : Config V => AK.indicator (fun _ => (1 : ℝ≥0∞)) ω * gfun ω) _ (hAKm.mul hoffintg)]
    rw [lintegral_mul_of_indep_blocks ρ S hAKblock hgfunblock]
    rw [lintegral_indicator hAKmeas (fun _ => (1 : ℝ≥0∞)), setLIntegral_one]
  -- Step 6: the off-cluster probability is a full-law ghost-hit probability
  have hstep6 : ∫⁻ ω, gfun ω ∂(edgeMeasure ρ) ≤ G := by
    have h1 : ∫⁻ ω, gfun ω ∂(edgeMeasure ρ)
        = ∫⁻ p : Config V × Config V, ∫⁻ G, (offCluster (K : Set V) y).indicator
            (fun _ => (1 : ℝ≥0∞)) (unionConf p, G) ∂(ghostLaw h)
            ∂((edgeMeasure ρ).prod (edgeMeasure q)) := by
      rw [hgfun]
      exact (lintegral_prod (μ := edgeMeasure ρ) (ν := edgeMeasure q)
        (f := fun p : Config V × Config V => ∫⁻ G, (offCluster (K : Set V) y).indicator
          (fun _ => (1 : ℝ≥0∞)) (unionConf p, G) ∂(ghostLaw h))
        (measurable_off_integral_pair h (K : Set V) y).aemeasurable).symm
    have hFmeas : Measurable fun θ : Config V =>
        ∫⁻ G, (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) (θ, G)
          ∂(ghostLaw h) :=
      measurable_off_integral_G h (K : Set V) y
    have h2 : ∫⁻ p : Config V × Config V, ∫⁻ G, (offCluster (K : Set V) y).indicator
          (fun _ => (1 : ℝ≥0∞)) (unionConf p, G) ∂(ghostLaw h)
          ∂((edgeMeasure ρ).prod (edgeMeasure q))
        = ∫⁻ θ, ∫⁻ G, (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) (θ, G)
            ∂(ghostLaw h) ∂(edgeMeasure π) := by
      rw [← lintegral_map hFmeas measurable_unionConf]
      rw [hq, unionMeasure_eq_edgeMeasure hρπ]
    have h3 : ∫⁻ θ, ∫⁻ G, (offCluster (K : Set V) y).indicator (fun _ => (1 : ℝ≥0∞)) (θ, G)
          ∂(ghostLaw h) ∂(edgeMeasure π)
        ≤ ∫⁻ θ, ∫⁻ G, (GhostConnected y).indicator (fun _ => (1 : ℝ≥0∞)) (θ, G)
            ∂(ghostLaw h) ∂(edgeMeasure π) := by
      refine lintegral_mono fun θ => lintegral_mono fun G => ?_
      by_cases h4 : (θ, G) ∈ offCluster (K : Set V) y
      · rw [Set.indicator_of_mem h4,
          Set.indicator_of_mem (offCluster_subset_ghostConnected (K : Set V) y h4)]
      · rw [Set.indicator_of_notMem h4]; exact zero_le
    have h4 : ∫⁻ θ, ∫⁻ G, (GhostConnected y).indicator (fun _ => (1 : ℝ≥0∞)) (θ, G)
          ∂(ghostLaw h) ∂(edgeMeasure π) = ghostHits π h y := by
      have hsec : ∀ θ : Config V, ∫⁻ G, (GhostConnected y).indicator
            (fun _ => (1 : ℝ≥0∞)) (θ, G) ∂(ghostLaw h)
          = (ghostLaw h) (Prod.mk θ ⁻¹' (GhostConnected y)) := by
        intro θ
        have hfun : (fun G : V → Prop => (GhostConnected y).indicator
              (fun _ => (1 : ℝ≥0∞)) (θ, G))
            = (Prod.mk θ ⁻¹' (GhostConnected y)).indicator (fun _ => (1 : ℝ≥0∞)) := by
          funext G
          by_cases hG : (θ, G) ∈ GhostConnected y
          · rw [Set.indicator_of_mem hG,
              Set.indicator_of_mem (show G ∈ Prod.mk θ ⁻¹' (GhostConnected y) from hG)]
          · rw [Set.indicator_of_notMem hG]
            exact Eq.symm (Set.indicator_of_notMem (s := Prod.mk θ ⁻¹' (GhostConnected y))
              (f := fun _ => (1 : ℝ≥0∞)) (fun hh => hG hh))
        rw [hfun, lintegral_indicator
          ((measurableSet_ghostConnected y).preimage measurable_prodMk_left), setLIntegral_one]
      simp only [hsec]
      rw [ghostHits, Measure.prod_apply (measurableSet_ghostConnected y)]
    calc ∫⁻ ω, gfun ω ∂(edgeMeasure ρ) = _ := h1
      _ = _ := h2
      _ ≤ _ := h3
      _ = ghostHits π h y := h4
      _ ≤ G := hG y
  -- put the steps together
  have hmain : (((edgeMeasure ρ).prod (edgeMeasure q)).prod (ghostLaw h)) T
      = ghostW h ^ K.card * ENNReal.ofReal ((q a : unitInterval) : ℝ) *
          ((edgeMeasure ρ) AK * ∫⁻ ω, gfun ω ∂(edgeMeasure ρ)) := by
    rw [hstep1, hstep2]
    simp only [hstep4]
    exact hstep5
  rw [hT] at hmain
  rw [hmain]
  calc ghostW h ^ K.card * ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ) *
        (edgeMeasure ρ {ω : Config V | cluster ω o = (K : Set V)} * ∫⁻ ω, gfun ω ∂(edgeMeasure ρ))
      ≤ ghostW h ^ K.card * ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ) *
        (edgeMeasure ρ {ω : Config V | cluster ω o = (K : Set V)} * G) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hstep6)
    _ = edgeMeasure ρ {ω : Config V | cluster ω o = (K : Set V)} *
        ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ) * ghostW h ^ K.card * G := by
        ac_rfl

end PercLib.CriticalLRP
