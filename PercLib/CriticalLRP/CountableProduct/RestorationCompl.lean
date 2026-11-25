/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.4.12: restoration at the edge set touching the cluster of the origin

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.12 (p. 39):

  "Let `ω` and `ω'` be independent percolation configurations, and let `ω̃` be defined by
   setting `ω̃(e) = ω(e)` for every edge `e` touching the cluster `K_0` of `0` in `ω` and
   `ω̃(e) = ω'(e)` for every other edge `e`, so that `ω̃` has the same law as `ω`."

The present file proves the law-preservation claim for this *complementary* coupling, in which
the base configuration `ω` is kept on its own touching set and the independent copy `ω'` is used
on the complement:

  `((edgeMeasure π).prod (edgeMeasure π)).map (p ↦ forceOn (touchSet p.2 o)ᶜ p.1 p.2)
     = edgeMeasure π`     (`edgeMeasure_map_forceOn_touchSet_compl`),

and, for general self-determined families `S` of edge sets,
`edgeMeasure_map_forceOn_compl` (with `cylinder_prob_forceOn_compl` the cylinder-level form).

This is genuinely different from `edgeMeasure_map_forceOn_touchSet` of
`RandomRestoration.lean`, which resamples the touching set itself (fresh on `touchSet`, base
off it).  Neither statement implies the other: the two maps act oppositely on the random set.

## Method (no disintegration over the uncountable family of touching sets)

The proof rests on a deterministic property of a family `S ω` of edge sets, *self-determination*:

  if `ω'` agrees with `ω` on every edge of `S ω`, then `S ω' = S ω`.

The touching set has this property (`selfDetermined_touchSet`): the open cluster of `o` and all
edges incident to it are determined by the states of those edges.

Self-determination makes the "trace" event `{ω | B ∩ S ω = A}` measurable for the σ-algebra of
the edges *outside* `B \ A` (`measurableSet_blockS_eq_blockSigma`), because `S ω ⊆ (B \ A)ᶜ`, so
the event is unchanged by changing coordinates in `B \ A`.  Independence of the two edge blocks
under the product law `edgeMeasure π` then gives the factorisation

  `∫ f · 1_{B ∩ S = A} = (∫ f) · μ{B ∩ S = A}`  for `f` depending only on `B \ A`,

which is the only probabilistic input.  Summing over the finitely many possible traces `A ⊆ B`
(`lintegral_Phi`) computes every cylinder probability of the restored configuration, and cylinder
probabilities determine the law.

## Deterministic comparison in the same coupling

`cluster_forceOn_compl_touchSet` / `touchSet_forceOn_compl_touchSet`: the restored configuration
has the same cluster of `o`, and the same touching set, as the base.

`mem_cluster_forceOn_compl_iff` / `cluster_forceOn_compl_disjoint`: for `y ∉ K_0`, the cluster of
`y` in the restored configuration is exactly the set of endpoints of `ω'`-open walks from `y` that
avoid `K_0`, hence is disjoint from `K_0`.

`not_cluster_subset_forceOn_compl`: the paper's following assertion `K_y ⊆ K̃_y` for `y ∉ K_0`
is **false** for the coupling printed there (three-vertex counterexample, with
`cluster_forceOn_compl_empty` the general reason: with `ω' = ∅` the restored cluster of `y ∉ K_0`
is `{y}`).  The paper's subsequent cluster argument therefore needs the other coupling, which
resamples the touching set; both law statements are true and both are now available in the
development.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.RandomRestoration

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Self-determined families of edge sets -/

/-- A family `S ω` of sets of edges is **self-determined** if the configuration restricted to
`S ω` determines `S ω`. -/
def SelfDetermined (S : Config V → Set (Sym2 V)) : Prop :=
  ∀ ω ω' : Config V, (∀ e, e ∈ S ω → (e ∈ ω' ↔ e ∈ ω)) → S ω' = S ω

/-- If `ω'` agrees with `ω` on every edge touching the cluster of `o` in `ω`, then the two
configurations have the same touching set. -/
theorem touchSet_eq_of_eqOn {ω ω' : Config V} {o : V}
    (h : ∀ e, e ∈ touchSet ω o → (e ∈ ω' ↔ e ∈ ω)) :
    touchSet ω' o = touchSet ω o := by
  have hcl := cluster_eq_of_eqOn_touchSet (ω := ω) (ω' := ω') (o := o) h
  refine Set.ext fun e => ?_
  simp only [mem_touchSet]
  rw [hcl]

/-- **The touching set is self-determined.** -/
theorem selfDetermined_touchSet (o : V) :
    SelfDetermined (fun ω : Config V => touchSet ω o) :=
  fun ω ω' h => touchSet_eq_of_eqOn (ω := ω) (ω' := ω') h

/-! ## The trace of a self-determined family on a finite edge set -/

/-- The edges of the finite set `B` that lie in `S ω`. -/
noncomputable def blockS (S : Config V → Set (Sym2 V)) (B : Finset (Sym2 V)) (ω : Config V) :
    Finset (Sym2 V) :=
  B.filter (fun e => e ∈ S ω)

variable {S : Config V → Set (Sym2 V)}

theorem mem_blockS {B : Finset (Sym2 V)} {ω : Config V} {e : Sym2 V} :
    e ∈ blockS S B ω ↔ e ∈ B ∧ e ∈ S ω :=
  Finset.mem_filter

theorem blockS_subset (B : Finset (Sym2 V)) (ω : Config V) : blockS S B ω ⊆ B :=
  Finset.filter_subset _ _

theorem blockS_eq_iff {B A : Finset (Sym2 V)} {ω : Config V} (hA : A ⊆ B) :
    blockS S B ω = A ↔ ∀ e ∈ B, (e ∈ S ω ↔ e ∈ A) := by
  constructor
  · intro h e he
    have h1 : e ∈ blockS S B ω ↔ e ∈ A := by rw [h]
    rw [mem_blockS] at h1
    exact ⟨fun hS => h1.mp ⟨he, hS⟩, fun heA => (h1.mpr heA).2⟩
  · intro h
    refine Finset.ext fun e => ?_
    rw [mem_blockS]
    exact ⟨fun h' => (h e h'.1).mp h'.2, fun heA => ⟨hA heA, (h e (hA heA)).mpr heA⟩⟩

/-- The event that the trace of `S` on `B` equals `A` is measurable. -/
theorem measurableSet_blockS_eq (hmeas : ∀ e, MeasurableSet {ω : Config V | e ∈ S ω})
    (B A : Finset (Sym2 V)) : MeasurableSet {ω : Config V | blockS S B ω = A} := by
  classical
  by_cases hA : A ⊆ B
  · have hset : {ω : Config V | blockS S B ω = A}
        = ⋂ e ∈ B, {ω : Config V | (e ∈ S ω ↔ e ∈ A)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact blockS_eq_iff hA
    rw [hset]
    refine Finset.measurableSet_biInter B fun e _ => ?_
    by_cases he : e ∈ A
    · have h' : {ω : Config V | (e ∈ S ω ↔ e ∈ A)} = {ω : Config V | e ∈ S ω} := by
        ext ω
        simp [he]
      rw [h']
      exact hmeas e
    · have h' : {ω : Config V | (e ∈ S ω ↔ e ∈ A)} = {ω : Config V | e ∉ S ω} := by
        ext ω
        simp [he]
      rw [h']
      exact (hmeas e).compl
  · obtain ⟨e, heA, heB⟩ := Finset.not_subset.mp hA
    have hempty : {ω : Config V | blockS S B ω = A} = (∅ : Set (Config V)) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have h1 : e ∈ blockS S B ω := by rw [h]; exact heA
      exact heB (blockS_subset B ω h1)
    rw [hempty]
    exact MeasurableSet.empty

/-! ## Change of finitely many coordinates and block measurability -/

/-- An event which is unchanged by changing the states of the edges in `G` is measurable for the
σ-algebra generated by the edges outside `G`. -/
theorem measurableSet_blockSigma_compl_of_agree {G : Set (Sym2 V)} {C : Set (Config V)}
    (hC : MeasurableSet C)
    (h : ∀ ω ω' : Config V, (∀ e, e ∉ G → (e ∈ ω' ↔ e ∈ ω)) → (ω ∈ C → ω' ∈ C)) :
    MeasurableSet[blockSigma Gᶜ] C := by
  have hh : MeasurableSet[blockSigma Gᶜ] (forceOn G (∅ : Config V) ⁻¹' C) :=
    hC.preimage (measurable_forceOn_block G ∅)
  have heq : forceOn G (∅ : Config V) ⁻¹' C = C := by
    ext ω
    constructor
    · intro hω
      exact h (forceOn G (∅ : Config V) ω) ω
        (fun e he => (mem_forceOn_of_notMem he ∅ ω).symm) hω
    · intro hω
      exact h ω (forceOn G (∅ : Config V) ω) (fun e he => mem_forceOn_of_notMem he ∅ ω) hω
  rwa [heq] at hh

/-- **The trace event lies in the σ-algebra of the edges outside `B \ A`.** -/
theorem measurableSet_blockS_eq_blockSigma (hdet : SelfDetermined S)
    (hmeas : ∀ e, MeasurableSet {ω : Config V | e ∈ S ω}) (B A : Finset (Sym2 V)) :
    MeasurableSet[blockSigma ((↑(B \ A) : Set (Sym2 V)))ᶜ] {ω : Config V | blockS S B ω = A} := by
  classical
  by_cases hA : A ⊆ B
  · refine measurableSet_blockSigma_compl_of_agree (measurableSet_blockS_eq hmeas B A) ?_
    intro ω ω' hag hω
    have hSsub : S ω ⊆ ((↑(B \ A) : Set (Sym2 V)))ᶜ := by
      intro e heS he
      obtain ⟨heB, heA⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp he)
      have hmem : e ∈ blockS S B ω := Finset.mem_filter.mpr ⟨heB, heS⟩
      rw [hω] at hmem
      exact heA hmem
    have hSw : S ω' = S ω := hdet ω ω' (fun e he => hag e (fun hmem => hSsub he hmem))
    have hb : blockS S B ω' = blockS S B ω := by
      simp only [blockS, hSw]
    show blockS S B ω' = A
    rw [hb]
    exact hω
  · obtain ⟨e, heA, heB⟩ := Finset.not_subset.mp hA
    have hempty : {ω : Config V | blockS S B ω = A} = (∅ : Set (Config V)) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have h1 : e ∈ blockS S B ω := by rw [h]; exact heA
      exact heB (blockS_subset B ω h1)
    rw [hempty]
    exact MeasurableSpace.measurableSet_empty (blockSigma ((↑(B \ A) : Set (Sym2 V)))ᶜ)

/-! ## The weight of a cylinder event and its integral -/

section Weights

variable (π : Sym2 V → unitInterval)

/-- The `ℝ≥0∞`-indicator of the event that `ω` has the states `t` on the finite edge set `G`. -/
noncomputable def cylW (t : Sym2 V → Set Prop) (G : Finset (Sym2 V)) (ω : Config V) : ℝ≥0∞ :=
  ∏ e ∈ G, if ω e ∈ t e then 1 else 0

/-- The `edgeMeasure π`-probability of the cylinder event prescribing the states `t` on `G`. -/
noncomputable def bw (t : Sym2 V → Set Prop) (G : Finset (Sym2 V)) : ℝ≥0∞ :=
  ∏ e ∈ G, bernoulliMeasure (True : Prop) (False : Prop) (π e) (t e)

/-- Cylinder events are measurable. -/
theorem measurableSet_edgeCyl (G : Finset (Sym2 V)) (t : Sym2 V → Set Prop) :
    MeasurableSet (edgeCyl G t) := by
  rw [show edgeCyl G t = ⋂ e ∈ G, {ω : Config V | ω e ∈ t e} from by
    ext ω
    simp [edgeCyl]]
  exact Finset.measurableSet_biInter G fun e _ => measurableSet_eval t e

theorem measurable_cylW {t : Sym2 V → Set Prop} (G : Finset (Sym2 V)) :
    Measurable (cylW (V := V) t G) := by
  refine Finset.measurable_prod G fun e _ => ?_
  exact Measurable.ite (measurableSet_eval t e) measurable_const measurable_const

/-- `cylW` depends only on the states of the edges in `G`. -/
theorem measurable_cylW_block {t : Sym2 V → Set Prop} (G : Finset (Sym2 V)) :
    Measurable[blockSigma (↑G : Set (Sym2 V))] (cylW (V := V) t G) := by
  refine Finset.measurable_prod (m := blockSigma (↑G : Set (Sym2 V)))
    (f := fun e (ω : Config V) => if ω e ∈ t e then (1 : ℝ≥0∞) else 0) G ?_
  intro e he
  have hcoord : Measurable[blockSigma (↑G : Set (Sym2 V))] fun ω : Config V => ω e :=
    measurable_iff_comap_le.mpr
      (le_iSup_of_le e (le_iSup_of_le (Finset.mem_coe.mpr he) le_rfl))
  exact Measurable.ite (m := blockSigma (↑G : Set (Sym2 V)))
    (hcoord (t := t e) (by measurability)) measurable_const measurable_const

theorem cylW_eq_indicator {t : Sym2 V → Set Prop} (G : Finset (Sym2 V)) :
    cylW (V := V) t G = (edgeCyl G t).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext ω
  rw [cylW, Finset.prod_boole]
  simp [edgeCyl, Set.indicator_apply]

theorem lintegral_cylW (t : Sym2 V → Set Prop) (G : Finset (Sym2 V)) :
    ∫⁻ ω, cylW (V := V) t G ω ∂(edgeMeasure π) = bw (V := V) π t G := by
  rw [cylW_eq_indicator, lintegral_indicator (measurableSet_edgeCyl G t), setLIntegral_one,
    edgeMeasure_edgeCyl π G t (fun e => by measurability), bw]

end Weights

/-! ## Independence of two complementary edge blocks -/

theorem blockSigma_mono {S T : Set (Sym2 V)} (h : S ⊆ T) : blockSigma S ≤ blockSigma T :=
  iSup₂_le fun e he => le_iSup_of_le e (le_iSup_of_le (h he) le_rfl)

/-- Integrals factorise over two complementary blocks of independent edges. -/
theorem lintegral_mul_of_indep_blocks (π : Sym2 V → unitInterval) (A : Set (Sym2 V))
    {f g : Config V → ℝ≥0∞} (hf : Measurable[blockSigma A] f)
    (hg : Measurable[blockSigma Aᶜ] g) :
    ∫⁻ ω, f ω * g ω ∂(edgeMeasure π)
      = (∫⁻ ω, f ω ∂(edgeMeasure π)) * (∫⁻ ω, g ω ∂(edgeMeasure π)) :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (blockSigma_le A) (blockSigma_le Aᶜ) (independent_blocks π A) hf hg

/-! ## The trace indicator, the section measure and the integral of the section integrand -/

section Main

variable (π : Sym2 V → unitInterval)

/-- The indicator of the trace event `{ω | blockS S B ω = A}` is measurable for the σ-algebra of
the edges outside `B \ A`. -/
theorem measurable_traceIndicator (hdet : SelfDetermined S)
    (hmeas : ∀ e, MeasurableSet {ω : Config V | e ∈ S ω}) (B A : Finset (Sym2 V)) :
    Measurable[blockSigma ((↑(B \ A) : Set (Sym2 V)))ᶜ]
      (fun ω : Config V => if blockS S B ω = A then (1 : ℝ≥0∞) else 0) :=
  Measurable.ite (measurableSet_blockS_eq_blockSigma hdet hmeas B A) measurable_const
    measurable_const

/-- The trace indicator times the cylinder weight of the trace. -/
theorem measurable_traceProd (hdet : SelfDetermined S)
    (hmeas : ∀ e, MeasurableSet {ω : Config V | e ∈ S ω}) {t : Sym2 V → Set Prop}
    (B A : Finset (Sym2 V)) :
    Measurable[blockSigma ((↑(B \ A) : Set (Sym2 V)))ᶜ]
      (fun ω : Config V => (if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω) := by
  refine Measurable.mul (measurable_traceIndicator (S := S) hdet hmeas B A) ?_
  refine (measurable_cylW_block (V := V) (t := t) A).mono (blockSigma_mono ?_) le_rfl
  intro e he
  simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff]
  exact fun hmem => hmem.2 he

theorem measurable_traceProd_ambient (hmeas : ∀ e, MeasurableSet {ω : Config V | e ∈ S ω})
    {t : Sym2 V → Set Prop} (B A : Finset (Sym2 V)) :
    Measurable fun ω : Config V => (if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω :=
  Measurable.mul
    (Measurable.ite (measurableSet_blockS_eq hmeas B A) measurable_const measurable_const)
    (measurable_cylW A)

/-- The section of the restoring map over the base configuration `ω`. -/
theorem innerMeasure_eq {t : Sym2 V → Set Prop} (B : Finset (Sym2 V)) (ω : Config V) :
    (edgeMeasure π) {η : Config V | ∀ e ∈ B, forceOn (S ω)ᶜ η ω e ∈ t e}
      = cylW (V := V) t (blockS S B ω) ω * bw (V := V) π t (B \ blockS S B ω) := by
  have hAiff : ∀ e ∈ B, (e ∈ S ω ↔ e ∈ blockS S B ω) :=
    (blockS_eq_iff (blockS_subset B ω)).mp rfl
  have hset : {η : Config V | ∀ e ∈ B, forceOn (S ω)ᶜ η ω e ∈ t e}
      = if (∀ e ∈ blockS S B ω, ω e ∈ t e) then edgeCyl (B \ blockS S B ω) t else ∅ := by
    by_cases h : ∀ e ∈ blockS S B ω, ω e ∈ t e
    · rw [ite_eq_left h]
      ext η
      simp only [Set.mem_ofPred_eq, edgeCyl]
      constructor
      · intro H e he
        obtain ⟨heB, heA⟩ := Finset.mem_sdiff.mp he
        have hne : e ∉ S ω := fun hS => heA ((hAiff e heB).mp hS)
        have h2 := H e heB
        rwa [forceOn_apply_of_mem (S := (S ω)ᶜ) (by simpa using hne)] at h2
      · intro H e heB
        by_cases hS : e ∈ S ω
        · have h2 := forceOn_apply_of_notMem (S := (S ω)ᶜ) (η := η) (ω := ω) (by simpa using hS)
          rw [h2]
          exact h e ((hAiff e heB).mp hS)
        · have h2 := forceOn_apply_of_mem (S := (S ω)ᶜ) (η := η) (ω := ω) (by simpa using hS)
          rw [h2]
          exact H e (Finset.mem_sdiff.mpr ⟨heB, fun hA' => hS ((hAiff e heB).mpr hA')⟩)
    · rw [ite_eq_right h]
      ext η
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro H
      exact h fun e heA =>
        (by
          have heB : e ∈ B := blockS_subset B ω heA
          have hS : e ∈ S ω := (hAiff e heB).mpr heA
          have h2 := H e heB
          rwa [forceOn_apply_of_notMem (S := (S ω)ᶜ) (η := η) (ω := ω) (by simpa using hS)] at h2)
  rw [hset]
  by_cases h : ∀ e ∈ blockS S B ω, ω e ∈ t e
  · rw [ite_eq_left h, edgeMeasure_edgeCyl π (B \ blockS S B ω) t (fun e => by measurability)]
    have h1 : cylW (V := V) t (blockS S B ω) ω = 1 := by
      rw [cylW, Finset.prod_boole, ite_eq_left h]
    rw [h1, one_mul]
    rfl
  · rw [ite_eq_right h, measure_empty]
    have h1 : cylW (V := V) t (blockS S B ω) ω = 0 := by
      rw [cylW, Finset.prod_boole, ite_eq_right h]
    rw [h1, zero_mul]

/-- The section integrand of the restoring map. -/
noncomputable def Phi (t : Sym2 V → Set Prop) (B : Finset (Sym2 V)) (ω : Config V) : ℝ≥0∞ :=
  cylW (V := V) t (blockS S B ω) ω * bw (V := V) π t (B \ blockS S B ω)

theorem Phi_eq_innerMeasure {t : Sym2 V → Set Prop} (B : Finset (Sym2 V)) (ω : Config V) :
    Phi (S := S) π t B ω
      = (edgeMeasure π) {η : Config V | ∀ e ∈ B, forceOn (S ω)ᶜ η ω e ∈ t e} :=
  (innerMeasure_eq π B ω).symm

/-- Pointwise expansion of the section integrand over the possible traces. -/
theorem Phi_eq_sum {t : Sym2 V → Set Prop} (B : Finset (Sym2 V)) (ω : Config V) :
    Phi (S := S) π t B ω
      = ∑ A ∈ B.powerset, (if blockS S B ω = A then (1 : ℝ≥0∞) else 0)
          * (cylW (V := V) t A ω * bw (V := V) π t (B \ A)) := by
  classical
  rw [Finset.sum_eq_single (s := B.powerset) (blockS S B ω)
    (f := fun A => (if blockS S B ω = A then (1 : ℝ≥0∞) else 0)
      * (cylW (V := V) t A ω * bw (V := V) π t (B \ A)))
    (by
      intro A _ hne
      rw [ite_eq_right (fun h => hne h.symm), zero_mul])
    (by
      intro hnot
      exact absurd (Finset.mem_powerset.mpr (blockS_subset B ω)) hnot)]
  rw [ite_eq_left rfl, one_mul]
  rfl

/-- Pointwise expansion of the cylinder weight of `B` over the possible traces. -/
theorem cylW_eq_sum {t : Sym2 V → Set Prop} (B : Finset (Sym2 V)) (ω : Config V) :
    cylW (V := V) t B ω
      = ∑ A ∈ B.powerset, cylW (V := V) t (B \ A) ω
          * ((if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω) := by
  classical
  rw [Finset.sum_eq_single (s := B.powerset) (blockS S B ω)
    (f := fun A => cylW (V := V) t (B \ A) ω
      * ((if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω))
    (by
      intro A _ hne
      rw [ite_eq_right (fun h => hne h.symm), zero_mul, mul_zero])
    (by
      intro hnot
      exact absurd (Finset.mem_powerset.mpr (blockS_subset B ω)) hnot)]
  rw [ite_eq_left rfl, one_mul]
  exact (Finset.prod_sdiff (blockS_subset B ω)
    (f := fun e => if ω e ∈ t e then (1 : ℝ≥0∞) else 0)).symm

end Main

/-! ## The integral of the section integrand -/

section Integral

variable (π : Sym2 V → unitInterval)

/-- **The expectation of the section integrand** is the cylinder probability. -/
theorem lintegral_Phi (hdet : SelfDetermined S)
    (hmeas : ∀ e, MeasurableSet {ω : Config V | e ∈ S ω}) (t : Sym2 V → Set Prop)
    (B : Finset (Sym2 V)) :
    ∫⁻ ω, Phi (S := S) π t B ω ∂(edgeMeasure π) = bw (V := V) π t B := by
  classical
  have hCI : ∀ A ∈ B.powerset,
      (∫⁻ ω, (if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω
          ∂(edgeMeasure π)) * bw (V := V) π t (B \ A)
        = ∫⁻ ω, cylW (V := V) t (B \ A) ω
            * ((if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω)
            ∂(edgeMeasure π) := by
    intro A hA
    rw [← lintegral_cylW (π := π) t (B \ A)]
    rw [mul_comm (∫⁻ ω, (if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω
      ∂(edgeMeasure π))]
    exact (lintegral_mul_of_indep_blocks π (↑(B \ A) : Set (Sym2 V))
      (measurable_cylW_block (B \ A)) (measurable_traceProd (S := S) hdet hmeas B A)).symm
  have hstep : (fun ω => Phi (S := S) π t B ω)
      = fun ω => ∑ A ∈ B.powerset,
          ((if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω)
            * bw (V := V) π t (B \ A) := by
    funext ω
    rw [Phi_eq_sum (S := S) (π := π) (t := t) B ω]
    exact Finset.sum_congr rfl fun A _ => (mul_assoc _ _ _).symm
  have h1 : ∫⁻ ω, Phi (S := S) π t B ω ∂(edgeMeasure π)
      = ∑ A ∈ B.powerset,
          (∫⁻ ω, (if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω
            ∂(edgeMeasure π)) * bw (V := V) π t (B \ A) := by
    rw [hstep, lintegral_finsetSum]
    · refine Finset.sum_congr rfl fun A _ => ?_
      exact lintegral_mul_const _
        (measurable_traceProd_ambient (S := S) (t := t) hmeas B A)
    · intro A _
      exact Measurable.mul (f := fun ω : Config V =>
          (if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω)
        (g := fun _ => bw (V := V) π t (B \ A))
        (measurable_traceProd_ambient (S := S) (t := t) hmeas B A) measurable_const
  have hfun : (fun ω => ∑ A ∈ B.powerset, cylW (V := V) t (B \ A) ω
      * ((if blockS S B ω = A then (1 : ℝ≥0∞) else 0) * cylW (V := V) t A ω))
      = cylW (V := V) t B := by
    funext ω
    exact (cylW_eq_sum (S := S) (t := t) B ω).symm
  rw [h1, Finset.sum_congr rfl hCI, ← lintegral_finsetSum]
  · rw [hfun]
    exact lintegral_cylW (π := π) t B
  · intro A _
    exact Measurable.mul (measurable_cylW (B \ A))
      (measurable_traceProd_ambient (S := S) (t := t) hmeas B A)

end Integral

/-! ## The cylinder probability of the restored configuration -/

section Restoration

variable (π : Sym2 V → unitInterval)

/-- Measurability of the restoring map. -/
theorem measurable_forceOn_compl_pair (hmeas : ∀ e, MeasurableSet {ω : Config V | e ∈ S ω}) :
    Measurable fun q : Config V × Config V => forceOn (S q.1)ᶜ q.2 q.1 := by
  refine measurable_pi_iff.mpr fun e => ?_
  refine measurable_to_prop ?_
  have hset : {q : Config V × Config V | forceOn (S q.1)ᶜ q.2 q.1 e}
      = ({q : Config V × Config V | e ∉ S q.1} ∩ {q : Config V × Config V | q.2 e})
        ∪ ({q : Config V × Config V | e ∈ S q.1} ∩ {q : Config V × Config V | q.1 e}) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union]
    have hff := forceOn_apply (S q.1)ᶜ q.2 q.1 e
    simp only [Set.mem_compl_iff] at hff
    rw [hff]
    tauto
  have hpre : (fun q : Config V × Config V => forceOn (S q.1)ᶜ q.2 q.1 e) ⁻¹' {True}
      = {q : Config V × Config V | forceOn (S q.1)ᶜ q.2 q.1 e} := by
    ext q
    simp
  rw [hpre, hset]
  have hmain : MeasurableSet {q : Config V × Config V | e ∈ S q.1} :=
    MeasurableSet.preimage (hmeas e) measurable_fst
  have hfresh : MeasurableSet {q : Config V × Config V | q.1 e} :=
    MeasurableSet.preimage (measurableSet_mem e) measurable_fst
  have hbase : MeasurableSet {q : Config V × Config V | q.2 e} :=
    MeasurableSet.preimage (measurableSet_mem e) measurable_snd
  exact MeasurableSet.union (MeasurableSet.inter hmain.compl hbase)
    (MeasurableSet.inter hmain hfresh)

/-- **The cylinder probability of the restored configuration**: keeping the base configuration on
the edges of `S` and using the independent copy elsewhere does not change any cylinder
probability. -/
theorem cylinder_prob_forceOn_compl (hdet : SelfDetermined S)
    (hmeas : ∀ e, MeasurableSet {ω : Config V | e ∈ S ω}) (B : Finset (Sym2 V))
    (t : Sym2 V → Set Prop) :
    ((edgeMeasure π).prod (edgeMeasure π))
      {q : Config V × Config V | ∀ e ∈ B, forceOn (S q.1)ᶜ q.2 q.1 e ∈ t e}
      = bw (V := V) π t B := by
  have hpre : {q : Config V × Config V | ∀ e ∈ B, forceOn (S q.1)ᶜ q.2 q.1 e ∈ t e}
      = (fun q : Config V × Config V => forceOn (S q.1)ᶜ q.2 q.1) ⁻¹' edgeCyl B t := rfl
  rw [hpre, Measure.prod_apply
    ((measurableSet_edgeCyl B t).preimage (measurable_forceOn_compl_pair (S := S) hmeas))]
  rw [show (fun ω => (edgeMeasure π)
        (Prod.mk ω ⁻¹' ((fun q : Config V × Config V => forceOn (S q.1)ᶜ q.2 q.1) ⁻¹'
          edgeCyl B t)))
      = Phi (S := S) π t B from funext fun ω => innerMeasure_eq (S := S) π B ω]
  exact lintegral_Phi (S := S) π hdet hmeas t B

/-- **Restoration at a self-determined random edge set (complementary form).**  If the family
`S ω` is self-determined and each `e ∈ S ω` is measurable in `ω`, then keeping the base
configuration on `S ω` and using an independent copy of the law elsewhere preserves the law. -/
theorem edgeMeasure_map_forceOn_compl (hdet : SelfDetermined S)
    (hmeas : ∀ e, MeasurableSet {ω : Config V | e ∈ S ω}) :
    ((edgeMeasure π).prod (edgeMeasure π)).map
      (fun q : Config V × Config V => forceOn (S q.1)ᶜ q.2 q.1) = edgeMeasure π := by
  refine eq_edgeMeasure_of_cyl π _ ?_
  intro B t _
  rw [Measure.map_apply (measurable_forceOn_compl_pair (S := S) hmeas)
    (measurableSet_edgeCyl B t)]
  exact cylinder_prob_forceOn_compl (S := S) π hdet hmeas B t

end Restoration

/-! ## Lemma I.4.12: restoration at the touching set of the cluster of the origin -/

/-- **Lemma I.4.12 (restoration, complementary coupling).**  Let `ω` and `ω'` be independent with
law `edgeMeasure π`, and let `ω̃(e) = ω(e)` for every edge touching the cluster of `o` in `ω` and
`ω̃(e) = ω'(e)` for every other edge.  Then `ω̃` has law `edgeMeasure π`. -/
theorem edgeMeasure_map_forceOn_touchSet_compl (π : Sym2 V → unitInterval) (o : V) :
    ((edgeMeasure π).prod (edgeMeasure π)).map
      (fun p : Config V × Config V => forceOn (touchSet p.2 o)ᶜ p.1 p.2) = edgeMeasure π := by
  have h := edgeMeasure_map_forceOn_compl (S := fun ω : Config V => touchSet ω o) π
    (selfDetermined_touchSet o) (fun e => measurableSet_mem_touchSet o e)
  have hswap : (fun p : Config V × Config V => forceOn (touchSet p.2 o)ᶜ p.1 p.2)
      = (fun q : Config V × Config V => forceOn (touchSet q.1 o)ᶜ q.2 q.1) ∘ Prod.swap := rfl
  rw [hswap, ← Measure.map_map
    (measurable_forceOn_compl_pair (S := fun ω : Config V => touchSet ω o)
      (fun e => measurableSet_mem_touchSet o e)) measurable_swap,
    Measure.prod_swap, h]

/-- **The deterministic comparison in the coupling**: the restored configuration has the same
cluster of `o` as the base configuration. -/
theorem cluster_forceOn_compl_touchSet (η ω : Config V) (o : V) :
    cluster (forceOn (touchSet ω o)ᶜ η ω) o = cluster ω o :=
  cluster_eq_of_eqOn_touchSet (ω := ω) (ω' := forceOn (touchSet ω o)ᶜ η ω) (o := o)
    (fun e he => by
      have hne : e ∉ (touchSet ω o)ᶜ := by simpa using he
      exact mem_forceOn_of_notMem (S := (touchSet ω o)ᶜ) hne η ω)

theorem touchSet_forceOn_compl_touchSet (η ω : Config V) (o : V) :
    touchSet (forceOn (touchSet ω o)ᶜ η ω) o = touchSet ω o := by
  refine touchSet_eq_of_eqOn fun e he => ?_
  have hne : e ∉ (touchSet ω o)ᶜ := by simpa using he
  exact mem_forceOn_of_notMem (S := (touchSet ω o)ᶜ) hne η ω

/-- **Restoration for long-range Bernoulli bond percolation** (§I.1.2: edges open independently
with probability `1 - exp(-β J e)`), in the complementary coupling of Lemma I.4.12. -/
theorem longRangeMeasure_map_forceOn_touchSet_compl (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (o : V) :
    ((longRangeMeasure J hJ β).prod (longRangeMeasure J hJ β)).map
      (fun p : Config V × Config V => forceOn (touchSet p.2 o)ᶜ p.1 p.2) =
        longRangeMeasure J hJ β :=
  edgeMeasure_map_forceOn_touchSet_compl (bernoulliEdgeProb J hJ β) o

/-- The edge `s(u,v)` touches `cluster ω o` iff one of its endpoints does. -/
theorem mem_touchSet_pair_iff {ω : Config V} {o u v : V} :
    s(u, v) ∈ touchSet ω o ↔ u ∈ cluster ω o ∨ v ∈ cluster ω o := by
  rw [mem_touchSet]
  constructor
  · rintro ⟨w, hw, hwc⟩
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact Or.inl hwc
    · exact Or.inr hwc
  · rintro (h | h)
    · exact ⟨u, Sym2.mem_mk_left u v, h⟩
    · exact ⟨v, Sym2.mem_mk_right u v, h⟩

/-- **No `ω̃`-open walk from outside `K_0` ever visits `K_0`**: none of its edges touches `K_0`
and its endpoint lies outside `K_0`. -/
theorem walk_edges_not_mem_cluster {ω ω' : Config V} {o : V} {a : V} (ha : a ∉ cluster ω o) :
    ∀ {z : V} (p : (⊤ : SimpleGraph V).Walk a z),
      (∀ e ∈ p.edges, e ∈ forceOn (touchSet ω o)ᶜ ω' ω) →
      (∀ e ∈ p.edges, ∀ v ∈ e, v ∉ cluster ω o) ∧ z ∉ cluster ω o := by
  intro z p
  induction p with
  | nil =>
    intro _
    exact ⟨fun e he => by simp at he, ha⟩
  | cons h p' ih =>
    rename_i u v wz
    intro hp
    have hfirst : s(u, v) ∈ forceOn (touchSet ω o)ᶜ ω' ω :=
      hp _ (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..)
    have hu : u ∉ cluster ω o := ha
    have hv : v ∉ cluster ω o := by
      by_contra hvc
      have hT : s(u, v) ∈ touchSet ω o := mem_touchSet_pair_iff.mpr (Or.inr hvc)
      have hopen : s(u, v) ∈ ω := by
        have hstep := mem_forceOn_of_notMem (S := (touchSet ω o)ᶜ) (by simpa using hT) ω' ω
        rwa [hstep] at hfirst
      have hconn : Connects ω u v := by
        rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
        exact Relation.ReflTransGen.single (by
          rw [openGraph_adj]
          exact ⟨h, hopen⟩)
      have hcv : Connects ω o v := mem_cluster_iff.mp hvc
      exact hu (mem_cluster_iff.mpr (connects_trans hcv (connects_symm hconn)))
    have hp' : ∀ e ∈ p'.edges, e ∈ forceOn (touchSet ω o)ᶜ ω' ω := fun e he =>
      hp e (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ he)
    have ih' := ih hv hp'
    refine ⟨?_, ih'.2⟩
    intro e he w hw
    rw [SimpleGraph.Walk.edges_cons] at he
    rcases List.mem_cons.mp he with rfl | he'
    · rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hu
      · exact hv
    · exact ih'.1 e he' w hw

/-- **The cluster of `y` in the restored configuration, for `y` outside `K_0`.** -/
theorem mem_cluster_forceOn_compl_iff {ω ω' : Config V} {o y z : V}
    (hy : y ∉ cluster ω o) :
    z ∈ cluster (forceOn (touchSet ω o)ᶜ ω' ω) y ↔
      ∃ p : (⊤ : SimpleGraph V).Walk y z,
        (∀ e ∈ p.edges, e ∈ ω') ∧ (∀ e ∈ p.edges, ∀ v ∈ e, v ∉ cluster ω o) := by
  constructor
  · intro hz
    have hconn : Connects (forceOn (touchSet ω o)ᶜ ω' ω) y z := mem_cluster_iff.mp hz
    obtain ⟨p, hp⟩ := pathConnects_iff.mpr hconn
    have havoid := (walk_edges_not_mem_cluster (ω := ω) (ω' := ω') (o := o) hy p hp).1
    refine ⟨p, fun e he => ?_, havoid⟩
    have hoff : e ∉ touchSet ω o := fun hT => by
      obtain ⟨v, hv, hvc⟩ := hT
      exact havoid e he v hv hvc
    have hstep := forceOn_apply_of_mem (S := (touchSet ω o)ᶜ) (η := ω') (ω := ω)
      (by simpa using hoff)
    exact Eq.mp hstep (hp e he)
  · rintro ⟨p, hp, havoid⟩
    have hpc : PathConnects (forceOn (touchSet ω o)ᶜ ω' ω) y z := by
      refine ⟨p, fun e he => ?_⟩
      have hoff : e ∉ touchSet ω o := fun hT => by
        obtain ⟨v, hv, hvc⟩ := hT
        exact havoid e he v hv hvc
      have hstep := forceOn_apply_of_mem (S := (touchSet ω o)ᶜ) (η := ω') (ω := ω)
        (by simpa using hoff)
      change forceOn (touchSet ω o)ᶜ ω' ω e
      rw [hstep]
      exact hp e he
    exact mem_cluster_iff.mpr (pathConnects_iff.mp hpc)

/-- **The cluster of `y` in the restored configuration avoids `K_0`** when `y ∉ K_0`. -/
theorem cluster_forceOn_compl_disjoint {ω ω' : Config V} {o y z : V}
    (hy : y ∉ cluster ω o) (hz : z ∈ cluster (forceOn (touchSet ω o)ᶜ ω' ω) y) :
    z ∉ cluster ω o := by
  have hconn : Connects (forceOn (touchSet ω o)ᶜ ω' ω) y z := mem_cluster_iff.mp hz
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr hconn
  exact (walk_edges_not_mem_cluster (ω := ω) (ω' := ω') (o := o) hy p hp).2

/-- **The touching set of the restored configuration agrees with that of the base.** -/
theorem touchSet_forceOn_compl' (ω ω' : Config V) (o : V) :
    touchSet (forceOn (touchSet ω o)ᶜ ω' ω) o = touchSet ω o :=
  touchSet_forceOn_compl_touchSet ω' ω o


/-! ## The cluster of a vertex outside `K_0` when the fresh configuration is empty -/

/-- A vertex at which no open edge is incident is a cluster on its own. -/
theorem cluster_eq_singleton_of_isolated {ω : Config V} {v : V}
    (h : ∀ u, s(v, u) ∉ ω) : cluster ω v = {v} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨cluster_mem_self ω v, ?_⟩
  intro w hw
  rw [mem_cluster_iff, Connects, SimpleGraph.reachable_iff_reflTransGen] at hw
  induction hw with
  | refl => rfl
  | @tail a b hab hstep ih =>
    subst ih
    rw [openGraph_adj] at hstep
    exact absurd hstep.2 (h b)

/-- **In the complementary coupling with an empty fresh configuration**, the cluster of a vertex
outside `K_0` is the singleton `{y}`. -/
theorem cluster_forceOn_compl_empty {ω : Config V} {o y : V} (hy : y ∉ cluster ω o) :
    cluster (forceOn (touchSet ω o)ᶜ (∅ : Config V) ω) y = {y} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    obtain ⟨p, hp, -⟩ := (mem_cluster_forceOn_compl_iff (ω' := (∅ : Config V)) hy).mp hz
    cases p with
    | nil => rfl
    | cons h p' =>
      exact absurd (hp _ (by
        rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_self ..)) (by simp)
  · rw [Set.singleton_subset_iff]
    exact cluster_mem_self _ y

/-! ## The paper's subsequent inclusion fails in the printed coupling

The paper follows the definition of `ω̃` with the assertion that, on the event `y ∉ K_0`, the
cluster of `y` in `ω` is contained in the cluster of `y` in `ω̃`.  In the coupling printed there
(base kept on the edges touching `K_0`, fresh configuration elsewhere) that assertion is false: a
vertex `y ∉ K_0` is connected in `ω̃` only through edges *not* touching `K_0`, and those carry the
values of the fresh configuration `ω'`.  The following theorem is the resulting counterexample on
a three-vertex graph. -/

/-- The three-vertex configuration with the single open edge `{1,2}`. -/
def threeConfig : Config (Fin 3) := {s(1, 2)}

/-- Vertex `0` is isolated in `threeConfig`. -/
theorem cluster_threeConfig_zero : cluster (threeConfig) (0 : Fin 3) = {0} := by
  refine cluster_eq_singleton_of_isolated fun u => ?_
  fin_cases u <;> simp [threeConfig]

/-- In `threeConfig`, vertex `2` lies in the cluster of vertex `1`. -/
theorem mem_cluster_threeConfig_one_two : (2 : Fin 3) ∈ cluster threeConfig 1 := by
  rw [mem_cluster_iff, Connects, SimpleGraph.reachable_iff_reflTransGen]
  refine Relation.ReflTransGen.single ?_
  rw [openGraph_adj]
  exact ⟨by decide, by simp [threeConfig]⟩

/-- **The paper's inclusion `K_y ⊆ K̃_y` fails in the printed coupling**: on a three-vertex graph
with `ω` opening only the edge `{1,2}` and `ω' = ∅`, vertex `1` lies outside `K_0 = {0}` and its
cluster in `ω` is not contained in its cluster in `ω̃ = forceOn (touchSet ω 0)ᶜ ω' ω`. -/
theorem not_cluster_subset_forceOn_compl :
    ¬ (cluster threeConfig (1 : Fin 3) ⊆
        cluster (forceOn (touchSet threeConfig (0 : Fin 3))ᶜ (∅ : Config (Fin 3))
          threeConfig) 1) := by
  intro hsub
  have h1 : (1 : Fin 3) ∉ cluster threeConfig 0 := by
    rw [cluster_threeConfig_zero]
    simp
  have h2 : (2 : Fin 3) ∈ cluster (forceOn (touchSet threeConfig (0 : Fin 3))ᶜ
      (∅ : Config (Fin 3)) threeConfig) 1 :=
    hsub mem_cluster_threeConfig_one_two
  have hempty : cluster (forceOn (touchSet threeConfig (0 : Fin 3))ᶜ (∅ : Config (Fin 3))
      threeConfig) 1 = {1} :=
    cluster_forceOn_compl_empty (ω := threeConfig) (o := (0 : Fin 3)) h1
  rw [hempty] at h2
  exact absurd h2 (by simp)

end PercLib.CriticalLRP
