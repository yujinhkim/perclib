module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RightExcludedMass.Corner
public import PercLib.Probability.HarrisDecreasing
public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv
public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerOneSided
public import PercLib.CriticalLRP.MomentMonotonicity.Temperature

/-!
# Positivity of the shell term of the excluded mass

Direction B6 of swarm `smwv6er9k`.

* `edgeMeasure_all_closed` — the probability that every edge of a finite set is closed is the
  product of the closed per-edge probabilities.
* `ae_far_edge_closed` — an edge longer than the cutoff is closed almost surely.

The corresponding shell-mass positivity proof is in `RightExcludedMass.Positive`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

/-- **Closed finite cylinders.**  The probability that every edge of a finite set is closed is the
product of the closed per-edge probabilities.  (Complement duality plus the landed open-cylinder
formula `edgeMeasure_cylinder`.) -/
theorem edgeMeasure_all_closed {V : Type*} [Countable V] (π : Sym2 V → unitInterval)
    (s : Finset (Sym2 V)) :
    edgeMeasure π {ω : Config V | ∀ e ∈ s, e ∉ ω}
      = ∏ e ∈ s, (unitInterval.toNNReal (unitInterval.symm (π e)) : ℝ≥0∞) := by
  have hA : MeasurableSet {ω : Config V | ∀ e ∈ s, e ∈ ω} := by
    have h : {ω : Config V | ∀ e ∈ s, e ∈ ω} = {ω : Config V | (s : Set (Sym2 V)) ⊆ ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe]
    rw [h]
    exact PercLib.Probability.measurableSet_setOf_finset_subset' s
  have hset : {ω : Config V | ∀ e ∈ s, e ∉ ω}
      = {ω : Config V | ωᶜ ∈ {ω : Config V | ∀ e ∈ s, e ∈ ω}} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
  rw [hset]
  change PercLib.Probability.prodBernoulli π _ = _
  rw [PercLib.Probability.prodBernoulli_preimage_compl π hA]
  exact PercLib.Probability.prodBernoulli_subset _ s

/-- A closed per-edge probability is positive. -/
theorem unitInterval_toNNReal_symm_pos {x : unitInterval} (hx : x < 1) :
    (0 : ℝ≥0∞) < (unitInterval.toNNReal (unitInterval.symm x) : ℝ≥0∞) := by
  have hxr : (x : ℝ) < 1 := hx
  have hxr : (x : ℝ) < 1 := hx
  have hreal : (0 : ℝ) < ((unitInterval.symm x : unitInterval) : ℝ) := by
    rw [unitInterval.coe_symm_eq]
    linarith
  exact_mod_cast hreal

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## The cut-off law is a Bernoulli edge law -/

theorem cutLaw_all_closed {r : ℝ} (G : Finset (Sym2 M.V)) :
    (M.cutLaw r) {ω : Config M.V | ∀ e ∈ G, e ∉ ω}
      = ∏ e ∈ G, (unitInterval.toNNReal (unitInterval.symm (M.cutProb r e)) : ℝ≥0∞) := by
  rw [E1Sign.cutLaw_eq]
  exact PercLib.CriticalLRP.edgeMeasure_all_closed (M.cutProb r) G

/-- All edges of the finite cylinder are closed with positive probability. -/
theorem cutLaw_all_closed_pos {r : ℝ} (G : Finset (Sym2 M.V)) :
    0 < (M.cutLaw r) {ω : Config M.V | ∀ e ∈ G, e ∉ ω} := by
  rw [M.cutLaw_all_closed G]
  refine Finset.prod_induction _ (fun b : ℝ≥0∞ => 0 < b)
    (fun _ _ => fun ha hb => ENNReal.mul_pos ha.ne' hb.ne') zero_lt_one (fun e _ => ?_)
  exact PercLib.CriticalLRP.unitInterval_toNNReal_symm_pos (E1Sign.cutProb_lt_one M r e)

/-- **Edges longer than the cutoff radius are closed almost surely.** -/
theorem ae_far_edge_closed {r : ℝ} (x : M.V) (hxr : r < M.S.ρ (toVec x)) :
    ∀ᵐ ω ∂(M.cutLaw r), s(0, x) ∉ ω := by
  have hprob : ((M.cutProb r s(0, x) : unitInterval) : ℝ) = 0 := by
    by_cases hx : x = 0
    · subst hx
      exact M.cutProb_coe_loop r 0
    · have hlt : r < M.S.dist 0 x := by
        rw [SourceNormData.dist, toVec_sub_eq_neg x 0, SourceNormData.ρ_neg M.S, sub_zero]
        exact hxr
      have hkernel : M.cutKernel r s(0, x) = 0 := by
        rw [M.cutKernel_mk, ite_eq_right (Ne.symm hx),
          PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_lt hlt]
      rw [M.cutProb_coe_eq, hkernel, mul_zero, neg_zero, Real.exp_zero, sub_self]
  have hzero : (M.cutLaw r) {ω : Config M.V | s(0, x) ∈ ω} = 0 := by
    have hevent : {ω : Config M.V | s(0, x) ∈ ω} =
        {ω : Config M.V | ∀ e ∈ ({s(0, x)} : Finset (Sym2 M.V)), e ∈ ω} := by
      ext ω
      simp
    rw [E1Sign.cutLaw_eq, hevent, PercLib.CriticalLRP.edgeMeasure_cylinder]
    have hp : M.cutProb r s(0, x) = (0 : unitInterval) := Subtype.ext hprob
    simp [hp]
  apply ae_iff.mpr
  simpa only [Set.mem_ofPred_eq, not_not] using hzero

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.edgeMeasure_all_closed

#print axioms PercLib.CriticalLRP.unitInterval_toNNReal_symm_pos

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_all_closed

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_all_closed_pos

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ae_far_edge_closed

end PercLib.CriticalLRP.Orchestration
