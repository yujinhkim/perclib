/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.BK.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option maxHeartbeats 1000000

/-!
# BK and Harris--FKG for edge-dependent Bernoulli parameters

Hutchcroft's model (`arXiv:2508.18807`, Definition I.1.3) is Bernoulli bond percolation on a
weighted graph `G = (V, E, J)` with edge probabilities `p_e = 1 - exp(-β J_e)`, which depend on the
edge.  The constant-parameter development in `BK.lean` uses Mathlib's `setBernoulli`; here we set up
the genuinely edge-dependent product law `edgeLaw p` on `Set E` and prove the same results for it.

The main export is `bkEdge`.
-/

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EdgeLaw
attribute [local instance] Classical.propDecidable

/-- Bernoulli bond percolation with edge-dependent open probabilities `p : E → unitInterval`. -/
noncomputable def edgeLaw (p : E → unitInterval) : Measure (Set E) :=
  (Measure.infinitePi (fun e => bitLaw (p e))).map (fun f : E → Prop => {e | f e})

instance edgeLaw_isProbabilityMeasure (p : E → unitInterval) :
    IsProbabilityMeasure (edgeLaw p) := by
  unfold edgeLaw
  infer_instance

/-- `edgeLaw` is the product of the Bernoulli laws, transported along the identity identification of
`E → Prop` with `Set E`. -/
theorem edgeLaw_eq_infinitePi (p : E → unitInterval) :
    edgeLaw p = Measure.infinitePi (fun e => bitLaw (p e)) := by
  show Measure.map MeasurableEquiv.setOfPred
    (Measure.infinitePi (fun e => bitLaw (p e))) = _
  have h : (⇑MeasurableEquiv.setOfPred : (E → Prop) → Set E) = id := rfl
  rw [h]
  exact Measure.map_id

/-- The constant-parameter law of `Graph.lean` is the special case of `edgeLaw` with constant
parameter. -/
theorem law_eq_edgeLaw (q : unitInterval) :
    (law q : Measure (Set E)) = edgeLaw (fun _ => q) := by
  unfold law edgeLaw
  rw [setBernoulli_eq_map]
  simp only [bitLaw, Set.mem_univ]

theorem edgeLaw_real_singleton [Fintype E] (p : E → unitInterval) (ω : Set E) :
    (edgeLaw p).real {ω} = ∏ e, if e ∈ ω then (p e : ℝ) else 1 - p e := by
  have hm : Measurable (fun f : E → Prop => {e | f e}) := measurable_setOfPred
  have he : (fun f : E → Prop => {e | f e}) ⁻¹' ({ω} : Set (Set E)) =
      {fun e => (e ∈ ω : Prop)} := by
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.ext_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      funext e
      exact propext (h e)
    · intro h e
      rw [h]
  rw [edgeLaw, Measure.real, Measure.map_apply hm MeasurableSet.of_discrete, he,
    Measure.infinitePi_singleton_of_fintype, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases h : e ∈ ω
  · have hs : MeasurableSet ({True} : Set Prop) := MeasurableSet.of_discrete
    have := bernoulliMeasure_real_apply_of_mem_of_notMem (x := True) (y := False)
      (p := p e) hs (by simp) (by simp)
    simpa [bitLaw, h] using this
  · have hs : MeasurableSet ({False} : Set Prop) := MeasurableSet.of_discrete
    have := bernoulliMeasure_real_apply_of_notMem_of_mem (x := True) (y := False)
      (p := p e) hs (by simp) (by simp)
    simpa [bitLaw, h] using this

theorem measurable_set_restrict' (s : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply e.val).comp MeasurableEquiv.setOfPred.symm.measurable))

theorem edgeLaw_map_restrict (p : E → unitInterval) (s : Set E) :
    (edgeLaw p : Measure (Set E)).map (fun ω => (Subtype.val ⁻¹' ω : Set s)) =
      edgeLaw (fun e : s => p e) := by
  have hm := measurable_set_restrict' (E := E) s
  unfold edgeLaw
  rw [Measure.map_map hm measurable_setOfPred]
  have he : (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ∘
      (fun f : E → Prop => {e | f e}) =
      (fun f : s → Prop => {e | f e}) ∘ s.domRestrict := rfl
  rw [he, ← Measure.map_map measurable_setOfPred (by fun_prop),
    Measure.infinitePi_map_restrict']

end EdgeLaw

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EdgeAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology

theorem edge_atom_modular [Fintype E] (p : E → unitInterval) (a b : Set E) :
    (edgeLaw p).real {a} * (edgeLaw p).real {b} =
      (edgeLaw p).real {a ∩ b} * (edgeLaw p).real {a ∪ b} := by
  simp only [edgeLaw_real_singleton, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases ha : e ∈ a <;> by_cases hb : e ∈ b <;> simp [ha, hb, mul_comm]

/-- Harris--FKG for nonnegative increasing observables under the edge-dependent product law. -/
theorem association_edge_finite [Fintype E] (p : E → unitInterval) (f g : Set E → ℝ)
    (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    (∫ ω, f ω ∂edgeLaw p) * (∫ ω, g ω ∂edgeLaw p) ≤ ∫ ω, f ω * g ω ∂edgeLaw p := by
  have h := fkg f g (fun ω : Set E => (edgeLaw p).real {ω})
    (fun _ => measureReal_nonneg) hf0 hg0 hf hg
    (fun a b => (edge_atom_modular p a b).le)
  have hsum : (∑ ω : Set E, (edgeLaw p).real {ω}) = 1 := by
    simp
  rw [hsum, one_mul] at h
  simpa only [integral_fintype Integrable.of_finite, smul_eq_mul] using h

theorem association_edge_events_finite [Fintype E] (p : E → unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (edgeLaw p).real A * (edgeLaw p).real B ≤ (edgeLaw p).real (A ∩ B) := by
  have hm (S : Set (Set E)) (hS : IsUpperSet S) :
      Monotone (S.indicator (fun _ => (1 : ℝ))) := by
    intro a b hab
    by_cases ha : a ∈ S
    · simp [ha, hS hab ha]
    · simp only [Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have he : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
      B.indicator (fun _ => (1 : ℝ)) ω) = (A ∩ B).indicator (fun _ => 1) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [ha, hb]
  have h := association_edge_finite p _ _ (hm A hA) (hm B hB)
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
  rw [he] at h
  simpa only [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet B),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet (A ∩ B)),
    smul_eq_mul, mul_one] using h

theorem association_edge_restricted (p : E → unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (edgeLaw p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (edgeLaw p).real {ω | ω ∩ (s : Set E) ∈ B} ≤
      (edgeLaw p).real {ω | ω ∩ (s : Set E) ∈ A ∩ B} := by
  let A' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ A}
  let B' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ B}
  have hA' : IsUpperSet A' := fun _ _ h ha => hA (Set.image_mono h) ha
  have hB' : IsUpperSet B' := fun _ _ h hb => hB (Set.image_mono h) hb
  have he (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) =
      ω ∩ (s : Set E) := by
    ext e
    simp [and_comm]
  have hl (C : Set (Set E)) :
      (edgeLaw (fun e : (s : Set E) => p e) : Measure (Set (s : Set E))).real
          {η | Subtype.val '' η ∈ C} =
        (edgeLaw p).real {ω | ω ∩ (s : Set E) ∈ C} := by
    rw [← edgeLaw_map_restrict p (s : Set E), measureReal_def,
      Measure.map_apply (measurable_set_restrict' _) .of_discrete]
    simp only [Set.preimage_ofPred_eq, he, measureReal_def]
  have ht := association_edge_events_finite (fun e : (s : Set E) => p e) A' B' hA' hB'
  change (edgeLaw (fun e : (s : Set E) => p e)).real {η | Subtype.val '' η ∈ A} *
      (edgeLaw (fun e : (s : Set E) => p e)).real {η | Subtype.val '' η ∈ B} ≤
    (edgeLaw (fun e : (s : Set E) => p e)).real {η | Subtype.val '' η ∈ A ∩ B} at ht
  simpa only [hl] using ht

/-- Harris--FKG for upper sets that are finitely witnessed, edge-dependent parameters. -/
theorem association_edge_finiteWitness [Countable E] (p : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (edgeLaw p).real A * (edgeLaw p).real B ≤ (edgeLaw p).real (A ∩ B) := by
  let := Encodable.ofCountable E
  have hfAB : FiniteWitness (A ∩ B) := by
    intro ω hω
    obtain ⟨s, hs, hsa⟩ := hfA ω hω.1
    obtain ⟨t, ht, htb⟩ := hfB ω hω.2
    refine ⟨s ∪ t, ?_, hA ?_ hsa, hB ?_ htb⟩
    · simpa only [Finset.coe_union] using Set.union_subset hs ht
    · simp only [Finset.coe_union]; exact Set.subset_union_left
    · simp only [Finset.coe_union]; exact Set.subset_union_right
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (edgeLaw p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((edgeLaw p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := edgeLaw p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto
    ((hlim A hA hfA).mul (hlim B hB hfB)) (hlim (A ∩ B) (hA.inter hB) hfAB)
    (Filter.Eventually.of_forall fun n => association_edge_restricted p A B hA hB (edgeExhaustion n))

end EdgeAssociation

section EdgeFiniteProbability
attribute [local instance] Classical.propDecidable

/-- Probability of `A` under the edge-dependent product law restricted to the finite edge set
`s`: the sum over the `2^{|s|}` open subsets of `s`, weighted by the product of the open and closed
edge probabilities. -/
noncomputable def finiteProbabilityEdge (p : E → unitInterval) (s : Finset E)
    (A : Set (Set E)) : ℝ :=
  ∑ t ∈ s.powerset, if (t : Set E) ∈ A then
    (∏ e ∈ t, (p e : ℝ)) * ∏ e ∈ s \ t, (1 - p e : ℝ) else 0

theorem finiteProbabilityEdge_nonneg (p : E → unitInterval) (s : Finset E) (A : Set (Set E)) :
    0 ≤ finiteProbabilityEdge p s A := by
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun e _ => (p e).2.1
    · exact Finset.prod_nonneg fun e _ => sub_nonneg.mpr (p e).2.2
  · exact le_rfl

theorem finiteProbabilityEdge_mono (p : E → unitInterval) (s : Finset E)
    {A B : Set (Set E)} (h : A ⊆ B) : finiteProbabilityEdge p s A ≤ finiteProbabilityEdge p s B := by
  apply Finset.sum_le_sum
  intro t _
  split_ifs with ha hb hb
  · exact le_rfl
  · exact (hb (h ha)).elim
  · exact mul_nonneg (Finset.prod_nonneg fun e _ => (p e).2.1)
      (Finset.prod_nonneg fun e _ => sub_nonneg.mpr (p e).2.2)
  · exact le_rfl

theorem finiteProbabilityEdge_union_add_inter (p : E → unitInterval) (s : Finset E)
    (A B : Set (Set E)) :
    finiteProbabilityEdge p s (A ∪ B) + finiteProbabilityEdge p s (A ∩ B) =
      finiteProbabilityEdge p s A + finiteProbabilityEdge p s B := by
  simp only [finiteProbabilityEdge, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ha : (t : Set E) ∈ A <;> by_cases hb : (t : Set E) ∈ B <;> simp [ha, hb]

@[simp] theorem finiteProbabilityEdge_empty (p : E → unitInterval) (A : Set (Set E)) :
    finiteProbabilityEdge p ∅ A = if ∅ ∈ A then 1 else 0 := by
  simp [finiteProbabilityEdge]

theorem finiteProbabilityEdge_insert (p : E → unitInterval) (s : Finset E) (e : E)
    (he : e ∉ s) (A : Set (Set E)) :
    finiteProbabilityEdge p (insert e s) A =
      (1 - p e : ℝ) * finiteProbabilityEdge p s A +
        (p e : ℝ) * finiteProbabilityEdge p s (openSection A e) := by
  have hd : Disjoint s.powerset (s.powerset.image (insert e)) := by
    apply Finset.disjoint_left.mpr
    intro t ht himg
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp himg
    exact he ((Finset.mem_powerset.mp ht) (by simp))
  have hinj : Set.InjOn (insert e) (↑s.powerset : Set (Finset E)) := by
    intro t ht r hr h
    have ht' : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    have hr' : e ∉ r := fun h => he (Finset.mem_powerset.mp hr h)
    have hh := congrArg (fun t : Finset E => t.erase e) h
    simpa [ht', hr'] using hh
  have key : ∀ t ∈ s.powerset,
      (if (t : Set E) ∈ A then
          (∏ e' ∈ t, (p e' : ℝ)) * ∏ e' ∈ insert e s \ t, (1 - p e' : ℝ) else 0) +
        (if ((insert e t : Finset E) : Set E) ∈ A then
          (∏ e' ∈ insert e t, (p e' : ℝ)) *
            ∏ e' ∈ insert e s \ insert e t, (1 - p e' : ℝ) else 0) =
      (1 - p e : ℝ) * (if (t : Set E) ∈ A then
          (∏ e' ∈ t, (p e' : ℝ)) * ∏ e' ∈ s \ t, (1 - p e' : ℝ) else 0) +
        (p e : ℝ) * (if (t : Set E) ∈ openSection A e then
          (∏ e' ∈ t, (p e' : ℝ)) * ∏ e' ∈ s \ t, (1 - p e' : ℝ) else 0) := by
    intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    have het : e ∉ t := fun h => he (hts h)
    have h1 : insert e s \ t = insert e (s \ t) := by
      ext x
      by_cases hx : x = e
      · subst hx
        simp [Finset.mem_sdiff, Finset.mem_insert, he, het]
      · simp [Finset.mem_sdiff, Finset.mem_insert, hx]
    have h2 : insert e s \ insert e t = s \ t := by
      ext x
      by_cases hx : x = e
      · subst hx
        simp [Finset.mem_sdiff, Finset.mem_insert, he]
      · simp [Finset.mem_sdiff, Finset.mem_insert, hx]
    have hcoe : ((insert e t : Finset E) : Set E) = insert e (t : Set E) := Finset.coe_insert ..
    have hprod1 : (∏ e' ∈ insert e t, (p e' : ℝ)) = (p e : ℝ) * ∏ e' ∈ t, (p e' : ℝ) := by
      rw [Finset.prod_insert het]
    have hprod2 : (∏ e' ∈ insert e (s \ t), (1 - p e' : ℝ)) =
        (1 - p e : ℝ) * ∏ e' ∈ s \ t, (1 - p e' : ℝ) := by
      rw [Finset.prod_insert (by simp [Finset.mem_sdiff, he] : e ∉ s \ t)]
    rw [h1, hprod2, h2, hprod1, hcoe]
    simp only [openSection, Set.mem_ofPred_eq]
    by_cases hA : (t : Set E) ∈ A <;> by_cases hB : insert e (t : Set E) ∈ A <;>
      simp [hA, hB] <;> ring
  calc finiteProbabilityEdge p (insert e s) A
      = ∑ t ∈ (insert e s).powerset, (if (t : Set E) ∈ A then
          (∏ e' ∈ t, (p e' : ℝ)) * ∏ e' ∈ insert e s \ t, (1 - p e' : ℝ) else 0) := rfl
    _ = (∑ t ∈ s.powerset, (if (t : Set E) ∈ A then
          (∏ e' ∈ t, (p e' : ℝ)) * ∏ e' ∈ insert e s \ t, (1 - p e' : ℝ) else 0)) +
        (∑ t ∈ s.powerset, (if ((insert e t : Finset E) : Set E) ∈ A then
          (∏ e' ∈ insert e t, (p e' : ℝ)) *
            ∏ e' ∈ insert e s \ insert e t, (1 - p e' : ℝ) else 0)) := by
        rw [Finset.powerset_insert, Finset.sum_union hd, Finset.sum_image hinj]
    _ = ∑ t ∈ s.powerset,
        ((if (t : Set E) ∈ A then
          (∏ e' ∈ t, (p e' : ℝ)) * ∏ e' ∈ insert e s \ t, (1 - p e' : ℝ) else 0) +
         (if ((insert e t : Finset E) : Set E) ∈ A then
          (∏ e' ∈ insert e t, (p e' : ℝ)) *
            ∏ e' ∈ insert e s \ insert e t, (1 - p e' : ℝ) else 0)) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ t ∈ s.powerset,
        ((1 - p e : ℝ) * (if (t : Set E) ∈ A then
            (∏ e' ∈ t, (p e' : ℝ)) * ∏ e' ∈ s \ t, (1 - p e' : ℝ) else 0) +
          (p e : ℝ) * (if (t : Set E) ∈ openSection A e then
            (∏ e' ∈ t, (p e' : ℝ)) * ∏ e' ∈ s \ t, (1 - p e' : ℝ) else 0)) :=
        Finset.sum_congr rfl key
    _ = (1 - p e : ℝ) * finiteProbabilityEdge p s A +
          (p e : ℝ) * finiteProbabilityEdge p s (openSection A e) := by
        simp only [finiteProbabilityEdge, Finset.mul_sum, Finset.sum_add_distrib]

end EdgeFiniteProbability


end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EdgeBKHalf
attribute [local instance] Classical.propDecidable
open Filter Topology

/-- BK for `p ≤ 1/2` on a finite edge set, edge-dependent parameters, by induction on the edge
set. -/
theorem finiteProbabilityEdge_disjointOccurrence_le_half (p : E → unitInterval)
    (hp : ∀ e, (p e : ℝ) ≤ 1 / 2) (s : Finset E) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    finiteProbabilityEdge p s (DisjointOccurrence A B) ≤
      finiteProbabilityEdge p s A * finiteProbabilityEdge p s B := by
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    simp only [finiteProbabilityEdge_empty, empty_mem_disjointOccurrence]
    by_cases ha : (∅ : Set E) ∈ A <;> by_cases hb : (∅ : Set E) ∈ B <;> simp [ha, hb]
  | @insert e s he ih =>
    let A1 := openSection A e
    let B1 := openSection B e
    let D00 := DisjointOccurrence A B
    let D10 := DisjointOccurrence A1 B
    let D01 := DisjointOccurrence A B1
    have hD : D00 ⊆ D10 ∩ D01 := by
      intro ω hω
      exact ⟨disjointOccurrence_mono (subset_openSection hA e) (Set.Subset.refl _) hω,
        disjointOccurrence_mono (Set.Subset.refl _) (subset_openSection hB e) hω⟩
    have hsec : finiteProbabilityEdge p s (openSection D00 e) ≤
        finiteProbabilityEdge p s D10 + finiteProbabilityEdge p s D01 -
          finiteProbabilityEdge p s D00 := by
      have h1 := finiteProbabilityEdge_mono p s (openSection_disjointOccurrence A B hA hB e)
      have h2 := finiteProbabilityEdge_mono p s hD
      have h3 := finiteProbabilityEdge_union_add_inter p s D10 D01
      change finiteProbabilityEdge p s (openSection D00 e) ≤
        finiteProbabilityEdge p s (D10 ∪ D01) at h1
      linarith
    have h00 := ih A B hA hB
    have h10 := ih A1 B (openSection_upper hA e) hB
    have h01 := ih A B1 hA (openSection_upper hB e)
    have ha := finiteProbabilityEdge_mono p s (subset_openSection hA e)
    have hb := finiteProbabilityEdge_mono p s (subset_openSection hB e)
    have hcoef : 0 ≤ 1 - 2 * (p e : ℝ) := by linarith [hp e]
    have hdif : 0 ≤ ((p e : ℝ) ^ 2) *
        (finiteProbabilityEdge p s A1 - finiteProbabilityEdge p s A) *
        (finiteProbabilityEdge p s B1 - finiteProbabilityEdge p s B) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ha)) (sub_nonneg.mpr hb)
    rw [finiteProbabilityEdge_insert p s e he, finiteProbabilityEdge_insert p s e he,
      finiteProbabilityEdge_insert p s e he]
    have hm := mul_le_mul_of_nonneg_left hsec (p e).2.1
    have hm00 := mul_le_mul_of_nonneg_left h00 hcoef
    have hm10 := mul_le_mul_of_nonneg_left h10 (p e).2.1
    have hm01 := mul_le_mul_of_nonneg_left h01 (p e).2.1
    change (1 - (p e : ℝ)) * finiteProbabilityEdge p s D00 +
      (p e : ℝ) * finiteProbabilityEdge p s (openSection D00 e) ≤
      ((1 - (p e : ℝ)) * finiteProbabilityEdge p s A + (p e : ℝ) * finiteProbabilityEdge p s A1) *
      ((1 - (p e : ℝ)) * finiteProbabilityEdge p s B + (p e : ℝ) * finiteProbabilityEdge p s B1)
    nlinarith

theorem finiteProbabilityEdge_univ [Fintype E] (p : E → unitInterval) (A : Set (Set E)) :
    finiteProbabilityEdge p Finset.univ A = (edgeLaw p).real A := by
  have he : (edgeLaw p).real A = ∑ ω : Set E, if ω ∈ A then (edgeLaw p).real {ω} else 0 := by
    have h := integral_fintype (μ := edgeLaw p) (f := A.indicator (fun _ => (1 : ℝ)))
      Integrable.of_finite
    rw [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A)] at h
    simpa [smul_eq_mul, mul_ite, Set.indicator_apply] using h
  rw [he, finiteProbabilityEdge]
  apply Finset.sum_bij (fun (t : Finset E) _ => (t : Set E))
  · simp
  · intro a _ b _ h
    exact Finset.coe_injective h
  · intro ω _
    exact ⟨ω.toFinset, by simp, by simp⟩
  · intro t ht
    have hts : t ⊆ Finset.univ := Finset.subset_univ t
    by_cases h : (t : Set E) ∈ A
    · simp only [h, ite_true]
      rw [edgeLaw_real_singleton, ← Finset.compl_eq_univ_sdiff]
      rw [← Finset.union_compl (s := t), Finset.prod_union disjoint_compl_right]
      congr 1
      · exact Finset.prod_congr rfl fun e he => by simp [he]
      · exact Finset.prod_congr rfl fun e he => by
          have het : e ∉ t := by simpa using he
          simp [het]
    · simp only [h, ite_false]

theorem bk_edge_finite_half [Fintype E] (p : E → unitInterval)
    (hp : ∀ e, (p e : ℝ) ≤ 1 / 2) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (edgeLaw p).real (DisjointOccurrence A B) ≤ (edgeLaw p).real A * (edgeLaw p).real B := by
  simpa only [finiteProbabilityEdge_univ] using
    finiteProbabilityEdge_disjointOccurrence_le_half p hp Finset.univ A B hA hB

theorem bk_edge_restricted_half (p : E → unitInterval) (hp : ∀ e, (p e : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (edgeLaw p).real {ω | ω ∩ (s : Set E) ∈ DisjointOccurrence A B} ≤
      (edgeLaw p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (edgeLaw p).real {ω | ω ∩ (s : Set E) ∈ B} := by
  let f : (s : Set E) ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
  have hreal (C : Set (Set E)) :
      (edgeLaw p).real {ω | ω ∩ (s : Set E) ∈ C} =
        (edgeLaw (fun e : (s : Set E) => p e)).real {η : Set (s : Set E) | f '' η ∈ C} := by
    rw [← edgeLaw_map_restrict p (s : Set E)]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_set_restrict' _) MeasurableSet.of_discrete]
    congr 2
    ext ω
    change ω ∩ (s : Set E) ∈ C ↔ f '' (Subtype.val ⁻¹' ω) ∈ C
    have he : f '' (Subtype.val ⁻¹' ω) = ω ∩ (s : Set E) := by
      ext e
      simp [f, and_comm]
    rw [he]
  rw [hreal, hreal, hreal]
  have hh := bk_edge_finite_half (fun e : (s : Set E) => p e) (fun e => hp e)
    ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B)
    (fun _ _ h hω => hA (Set.image_mono h) hω)
    (fun _ _ h hω => hB (Set.image_mono h) hω)
  rw [← disjointOccurrence_image] at hh
  exact hh

theorem bk_edge_finiteWitness_half [Countable E] (p : E → unitInterval)
    (hp : ∀ e, (p e : ℝ) ≤ 1 / 2) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (edgeLaw p).real (DisjointOccurrence A B) ≤ (edgeLaw p).real A * (edgeLaw p).real B := by
  let := Encodable.ofCountable E
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (edgeLaw p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((edgeLaw p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := edgeLaw p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  apply le_of_tendsto_of_tendsto
    (hlim _ (disjointOccurrence_upper A B) (finiteWitness_disjointOccurrence A B))
    ((hlim A hA hfA).mul (hlim B hB hfB))
  exact Filter.Eventually.of_forall fun n => bk_edge_restricted_half p hp A B hA hB (edgeExhaustion n)

end EdgeBKHalf

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EdgeORLift
attribute [local instance] Classical.propDecidable

/-- For an edge with `p e < 1`, the number of parallel copies used in the OR-lift. -/
noncomputable def liftMult (p : E → unitInterval) (hp : ∀ e, p e < 1) (e : E) : ℕ :=
  Classical.choose (exists_orParameter (p e) (hp e))

/-- The parameter of each of the parallel copies. -/
noncomputable def liftParam (p : E → unitInterval) (hp : ∀ e, p e < 1) (e : E) : unitInterval :=
  Classical.choose (Classical.choose_spec (exists_orParameter (p e) (hp e)))

theorem liftParam_le (p : E → unitInterval) (hp : ∀ e, p e < 1) (e : E) :
    (liftParam p hp e : ℝ) ≤ 1 / 2 :=
  (Classical.choose_spec (Classical.choose_spec (exists_orParameter (p e) (hp e)))).1

theorem orParameter_liftMult (p : E → unitInterval) (hp : ∀ e, p e < 1) (e : E) :
    orParameter (liftParam p hp e) (liftMult p hp e) = p e :=
  (Classical.choose_spec (Classical.choose_spec (exists_orParameter (p e) (hp e)))).2

attribute [irreducible] liftMult liftParam

/-- The fibres of the OR-lifted edge set. -/
noncomputable def liftIdx (p : E → unitInterval) (hp : ∀ e, p e < 1) : E → Type :=
  fun e => Fin (liftMult p hp e)

/-- The edge set of the OR-lift: `liftMult p hp e` parallel copies of each edge `e`. -/
noncomputable abbrev liftSpace (p : E → unitInterval) (hp : ∀ e, p e < 1) : Type _ :=
  (e : E) × liftIdx p hp e

noncomputable instance liftIdx_countable (p : E → unitInterval) (hp : ∀ e, p e < 1) (e : E) :
    Countable (liftIdx p hp e) := by
  unfold liftIdx
  infer_instance

noncomputable instance liftIdx_fintype (p : E → unitInterval) (hp : ∀ e, p e < 1) (e : E) :
    Fintype (liftIdx p hp e) := by
  unfold liftIdx
  infer_instance

/-- The projection of the OR-lifted edge set onto the original edge set. -/
noncomputable def liftProj (p : E → unitInterval) (hp : ∀ e, p e < 1) : liftSpace p hp → E :=
  fun z => z.1

instance liftSpace_countable [Countable E] (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    Countable (liftSpace p hp) := by
  unfold liftSpace
  infer_instance

/-- The law of the OR-lifted configuration. -/
noncomputable def liftLaw (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    Measure (Set (liftSpace p hp)) :=
  edgeLaw (fun z : liftSpace p hp => liftParam p hp z.1)

instance liftLaw_isProbabilityMeasure (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    IsProbabilityMeasure (liftLaw p hp) := by
  unfold liftLaw
  infer_instance

theorem measurable_liftProj_image (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    Measurable (fun ω : Set (liftSpace p hp) => liftProj p hp '' ω) := by
  have hproj : ∀ ω : Set (liftSpace p hp),
      liftProj p hp '' ω = {e | ∃ j : liftIdx p hp e, (⟨e, j⟩ : liftSpace p hp) ∈ ω} := by
    intro ω
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases x with ⟨e', j⟩
      exact ⟨j, hx⟩
    · rintro ⟨j, hj⟩
      exact ⟨⟨e, j⟩, hj, rfl⟩
  have he : (fun ω : Set (liftSpace p hp) => liftProj p hp '' ω) =
      (fun f : E → Prop => {e | f e}) ∘
        (fun ω e => ∃ j : liftIdx p hp e, (⟨e, j⟩ : liftSpace p hp) ∈ ω) := by
    funext ω
    rw [hproj]
    rfl
  rw [he]
  refine measurable_setOfPred.comp (Measurable.of_eval fun e => ?_)
  have : MeasurableSet {ω : Set (liftSpace p hp) | ∃ j : liftIdx p hp e,
      (⟨e, j⟩ : liftSpace p hp) ∈ ω} := by
    have heq : {ω : Set (liftSpace p hp) | ∃ j : liftIdx p hp e,
        (⟨e, j⟩ : liftSpace p hp) ∈ ω} =
        ⋃ j : liftIdx p hp e,
          {ω : Set (liftSpace p hp) | (⟨e, j⟩ : liftSpace p hp) ∈ ω} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun j => measurableSet_setOfPred.mpr
      ((measurable_pi_apply (⟨e, j⟩ : liftSpace p hp)).comp
        MeasurableEquiv.setOfPred.symm.measurable)
  exact measurableSet_setOfPred.mp this

end EdgeORLift

end Percolation

end PercLib.CriticalLRP
