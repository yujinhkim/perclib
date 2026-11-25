/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.BK.Edges

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

/-!
# The OR-lift identity and BK for edge-dependent Bernoulli parameters

This file completes the reduction of the BK inequality for edge-dependent parameters to the case
`p ≤ 1/2` (`bk_edge_finiteWitness_half`): replacing each edge `e` by `liftMult p hp e` parallel
edges of parameter `liftParam p hp e ∈ (0, 1/2]` and forgetting the multiplicities recovers the law
with parameters `p`.  The proof computes the two measures on the boxes generating the product
σ-algebra (`Measure.eq_infinitePi`), using the per-fibre "OR of independent coins" computation
`map_exists_bitLaw`.
-/

set_option maxHeartbeats 1000000

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section LiftIdentity
attribute [local instance] Classical.propDecidable

variable [Countable E]

/-- The "at least one open copy" map on one fibre. -/
theorem measurable_exists_fiber (p : E → unitInterval) (hp : ∀ e, p e < 1) (e : E) :
    Measurable (fun h : liftIdx p hp e → Prop => ∃ j, h j) := by
  have : MeasurableSet {h : liftIdx p hp e → Prop | ∃ j, h j} := by
    have heq : {h : liftIdx p hp e → Prop | ∃ j, h j} =
        ⋃ j : liftIdx p hp e, {h : liftIdx p hp e → Prop | h j} := by
      ext h
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun j => measurableSet_setOfPred.mpr (measurable_pi_apply j)
  exact measurableSet_setOfPred.mp this

/-- The OR-lifted law, as a product measure on `liftSpace → Prop`. -/
noncomputable def liftPi (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    Measure (liftSpace p hp → Prop) :=
  Measure.infinitePi (fun z : liftSpace p hp => bitLaw (liftParam p hp z.1))

/-- The projection from the OR-lifted configuration to the original one. -/
noncomputable def liftProjConfig (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (liftSpace p hp → Prop) → (E → Prop) :=
  fun ω e => ∃ j : liftIdx p hp e, ω ⟨e, j⟩

theorem measurable_liftProjConfig (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    Measurable (liftProjConfig p hp) := by
  unfold liftProjConfig
  rw [measurable_pi_iff]
  intro e
  have h : Measurable (fun c : liftSpace p hp → Prop => fun j : liftIdx p hp e => c ⟨e, j⟩) := by
    rw [measurable_pi_iff]
    intro j
    exact measurable_pi_apply (⟨e, j⟩ : liftSpace p hp)
  exact (measurable_exists_fiber p hp e).comp h

theorem prod_measurable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {s : Finset ι} {t : (i : ι) → Set (X i)}
    (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (Set.pi (s : Set ι) t) :=
  MeasurableSet.pi s.countable_toSet fun i _ => ht i

/-- The OR-lift identity, on boxes. -/
theorem liftPi_map_liftProjConfig (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (liftPi p hp).map (liftProjConfig p hp) = Measure.infinitePi (fun e => bitLaw (p e)) := by
  refine Measure.eq_infinitePi (μ := fun e => bitLaw (p e))
    (ν := (liftPi p hp).map (liftProjConfig p hp)) ?_
  intro s t ht
  have hbox : ∀ e, MeasurableSet {h : liftIdx p hp e → Prop | (∃ j, h j) ∈ t e} :=
    fun e => (measurable_exists_fiber p hp e) (ht e)
  have hpre : (liftProjConfig p hp) ⁻¹' (Set.pi (s : Set E) t) =
      (⇑(MeasurableEquiv.piCurry (fun (e : E) (_ : liftIdx p hp e) => Prop))) ⁻¹'
        (Set.pi (s : Set E) fun e => {h : liftIdx p hp e → Prop | (∃ j, h j) ∈ t e}) := by
    ext ω
    constructor
    · intro hω e he
      exact hω e he
    · intro hω e he
      exact hω e he
  rw [Measure.map_apply (measurable_liftProjConfig p hp) (prod_measurable (X := fun _ : E => Prop) ht),
    hpre, liftPi]
  have hcurry : (Measure.infinitePi (fun z : liftSpace p hp => bitLaw (liftParam p hp z.1))).map
      (⇑(MeasurableEquiv.piCurry (fun (e : E) (_ : liftIdx p hp e) => Prop))) =
      Measure.infinitePi (fun e => Measure.infinitePi
        (fun _ : liftIdx p hp e => bitLaw (liftParam p hp e))) :=
    Measure.infinitePi_map_piCurry
      (μ := fun (e : E) (_ : liftIdx p hp e) => bitLaw (liftParam p hp e))
  have hstep : (Measure.infinitePi (fun z : liftSpace p hp => bitLaw (liftParam p hp z.1)))
      ((⇑(MeasurableEquiv.piCurry (fun (e : E) (_ : liftIdx p hp e) => Prop))) ⁻¹'
        (Set.pi (s : Set E) fun e => {h : liftIdx p hp e → Prop | (∃ j, h j) ∈ t e}))
      = ((Measure.infinitePi (fun z : liftSpace p hp => bitLaw (liftParam p hp z.1))).map
          (⇑(MeasurableEquiv.piCurry (fun (e : E) (_ : liftIdx p hp e) => Prop))))
        (Set.pi (s : Set E) fun e => {h : liftIdx p hp e → Prop | (∃ j, h j) ∈ t e}) :=
    (Measure.map_apply
      (MeasurableEquiv.piCurry (fun (e : E) (_ : liftIdx p hp e) => Prop)).measurable
      (prod_measurable (X := fun e : E => liftIdx p hp e → Prop) (s := s)
        (t := fun e => {h : liftIdx p hp e → Prop | (∃ j, h j) ∈ t e}) hbox)).symm
  rw [hstep, hcurry,
    Measure.infinitePi_pi (μ := fun e => Measure.infinitePi
      (fun _ : liftIdx p hp e => bitLaw (liftParam p hp e))) (s := s)
      (t := fun e => {h : liftIdx p hp e → Prop | (∃ j, h j) ∈ t e}) (fun i _ => hbox i)]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hset : {h : liftIdx p hp e → Prop | (∃ j, h j) ∈ t e} =
      (fun h : liftIdx p hp e → Prop => ∃ j, h j) ⁻¹' (t e) := rfl
  rw [hset, ← Measure.map_apply (measurable_exists_fiber p hp e) (ht e),
    map_exists_bitLaw (liftParam p hp e) (liftIdx p hp e)]
  have hcard : Fintype.card (liftIdx p hp e) = liftMult p hp e := by
    unfold liftIdx
    simp
  rw [hcard, orParameter_liftMult]

/-- The projection as a map of `Set`s agrees with `liftProjConfig`. -/
theorem liftProj_image_eq (p : E → unitInterval) (hp : ∀ e, p e < 1)
    (ω : Set (liftSpace p hp)) : liftProj p hp '' ω = {e | liftProjConfig p hp ω e} := by
  ext e
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨j, hj⟩
    exact ⟨⟨e, j⟩, hj, rfl⟩

/-- The projection as a map of `Set`s. -/
theorem liftLaw_map_sigmaFst (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (liftLaw p hp).map (fun ω => liftProj p hp '' ω) = edgeLaw p := by
  have hfun : (fun ω : Set (liftSpace p hp) => liftProj p hp '' ω) =
      (fun ω : Set (liftSpace p hp) => fun e => liftProjConfig p hp ω e) := by
    funext ω
    exact liftProj_image_eq p hp ω
  rw [hfun]
  have hLL : liftLaw p hp = liftPi p hp := edgeLaw_eq_infinitePi _
  rw [hLL]
  change Measure.map (liftProjConfig p hp) (liftPi p hp) = edgeLaw p
  rw [liftPi_map_liftProjConfig, edgeLaw_eq_infinitePi]

end LiftIdentity

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EdgeBK
attribute [local instance] Classical.propDecidable
variable [Countable E]

/-- **The BK inequality for edge-dependent Bernoulli parameters** (Hutchcroft,
arXiv:2508.18807, Section I.2.1): for increasing finitely witnessed events `A`, `B` and edge
probabilities `p e < 1`, `P(A ∘ B) ≤ P(A) P(B)`. -/
theorem bkEdge (p : E → unitInterval) (hp : ∀ e, p e < 1)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (edgeLaw p).real (DisjointOccurrence A B) ≤ (edgeLaw p).real A * (edgeLaw p).real B := by
  let A' : Set (Set (liftSpace p hp)) := (fun ω => liftProj p hp '' ω) ⁻¹' A
  let B' : Set (Set (liftSpace p hp)) := (fun ω => liftProj p hp '' ω) ⁻¹' B
  have hreal (C : Set (Set E)) (hC : MeasurableSet C) :
      (edgeLaw p).real C = (liftLaw p hp).real ((fun ω => liftProj p hp '' ω) ⁻¹' C) := by
    rw [← liftLaw_map_sigmaFst p hp]
    simp only [Measure.real, Measure.map_apply (measurable_liftProj_image p hp) hC]
  have hmA : MeasurableSet A := measurableSet_finiteWitness A hA hfA
  have hmB : MeasurableSet B := measurableSet_finiteWitness B hB hfB
  have hmAB : MeasurableSet (DisjointOccurrence A B) :=
    measurableSet_finiteWitness _ (disjointOccurrence_upper A B)
      (finiteWitness_disjointOccurrence A B)
  have h1 : (edgeLaw p).real (DisjointOccurrence A B) =
      (liftLaw p hp).real ((fun ω => liftProj p hp '' ω) ⁻¹' DisjointOccurrence A B) :=
    hreal _ hmAB
  have h2 : (liftLaw p hp).real ((fun ω => liftProj p hp '' ω) ⁻¹' DisjointOccurrence A B) ≤
      (liftLaw p hp).real (DisjointOccurrence A' B') :=
    measureReal_mono (image_preimage_disjointOccurrence (liftProj p hp) A B)
  have h3 : (liftLaw p hp).real (DisjointOccurrence A' B') ≤
      (liftLaw p hp).real A' * (liftLaw p hp).real B' :=
    bk_edge_finiteWitness_half (fun z : liftSpace p hp => liftParam p hp z.1)
      (fun z => liftParam_le p hp z.1) A' B'
      (fun _ _ h hω => hA (Set.image_mono h) hω)
      (fun _ _ h hω => hB (Set.image_mono h) hω)
      (finiteWitness_image_preimage (liftProj p hp) A hfA)
      (finiteWitness_image_preimage (liftProj p hp) B hfB)
  have h4 : (liftLaw p hp).real A' = (edgeLaw p).real A := (hreal A hmA).symm
  have h5 : (liftLaw p hp).real B' = (edgeLaw p).real B := (hreal B hmB).symm
  calc (edgeLaw p).real (DisjointOccurrence A B)
      = (liftLaw p hp).real ((fun ω => liftProj p hp '' ω) ⁻¹' DisjointOccurrence A B) := h1
    _ ≤ (liftLaw p hp).real (DisjointOccurrence A' B') := h2
    _ ≤ (liftLaw p hp).real A' * (liftLaw p hp).real B' := h3
    _ = (edgeLaw p).real A * (edgeLaw p).real B := by rw [h4, h5]

end EdgeBK

end Percolation

end PercLib.CriticalLRP
