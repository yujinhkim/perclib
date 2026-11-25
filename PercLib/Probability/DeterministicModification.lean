/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New deterministic modification identities from mathlib's coordinatewise
infinite-product pushforward theorem. No upstream proof copied.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Coupling.Monotone

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PercLib.Probability
variable {ι : Type*}

/-- Closing all coordinates outside an arbitrary deterministic set masks exactly
those Bernoulli marginals. No countability or finiteness assumption is needed. -/
theorem prodBernoulli_map_inter (q : ι → unitInterval) (E : Set ι)
    [DecidablePred (· ∈ E)] :
    (prodBernoulli q).map (· ∩ E) =
      prodBernoulli (fun i => if i ∈ E then q i else 0) := by
  classical
  let f : ι → Prop → Prop := fun i b => b ∧ i ∈ E
  have hf : ∀ i, Measurable (f i) := by intro i; dsimp [f]; fun_prop
  have hS : Measurable (fun p : ι → Prop => {i | p i}) :=
    MeasurableEquiv.setOfPred.measurable
  rw [prodBernoulli_eq_map, Measure.map_map (by fun_prop) hS, prodBernoulli_eq_map]
  change (Measure.infinitePi fun i => bernoulliMeasure True False (q i)).map
    ((fun p : ι → Prop => {i | p i}) ∘ (fun p i => f i (p i))) = _
  rw [← Measure.map_map hS (by fun_prop), Measure.infinitePi_map_pi _ hf]
  congr 1
  congr 1
  funext i
  rw [map_bernoulliMeasure]
  by_cases hi : i ∈ E <;> simp [f, hi]

/-- Opening every coordinate in an arbitrary deterministic set fixes its marginals
at one and preserves all remaining Bernoulli probabilities. -/
theorem prodBernoulli_map_union (q : ι → unitInterval) (E : Set ι)
    [DecidablePred (· ∈ E)] :
    (prodBernoulli q).map (· ∪ E) =
      prodBernoulli (fun i => if i ∈ E then 1 else q i) := by
  classical
  let f : ι → Prop → Prop := fun i b => b ∨ i ∈ E
  have hf : ∀ i, Measurable (f i) := by intro i; dsimp [f]; fun_prop
  have hS : Measurable (fun p : ι → Prop => {i | p i}) :=
    MeasurableEquiv.setOfPred.measurable
  rw [prodBernoulli_eq_map, Measure.map_map (by fun_prop) hS, prodBernoulli_eq_map]
  change (Measure.infinitePi fun i => bernoulliMeasure True False (q i)).map
    ((fun p : ι → Prop => {i | p i}) ∘ (fun p i => f i (p i))) = _
  rw [← Measure.map_map hS (by fun_prop), Measure.infinitePi_map_pi _ hf]
  congr 1
  congr 1
  funext i
  rw [map_bernoulliMeasure]
  by_cases hi : i ∈ E <;> simp [f, hi]

/-- Deleting an arbitrary set of coordinates fixes their probabilities at zero. -/
theorem prodBernoulli_map_sdiff (q : ι → unitInterval) (E : Set ι)
    [DecidablePred (· ∈ E)] :
    (prodBernoulli q).map (· \ E) =
      prodBernoulli (fun i => if i ∈ E then 0 else q i) := by
  simpa only [Set.sdiff_eq_compl_inter, Set.inter_comm, Set.mem_compl_iff, ite_not] using
    prodBernoulli_map_inter q Eᶜ

/-- Deterministically closing coordinates decreases every upper event. -/
theorem prodBernoulli_preimage_inter_le (q : ι → unitInterval) (E : Set ι)
    {A : Set (Set ι)} (hA : IsUpperSet A) :
    prodBernoulli q ((· ∩ E) ⁻¹' A) ≤ prodBernoulli q A :=
  measure_mono (fun _ h => hA Set.inter_subset_left h)

/-- Deterministically opening coordinates increases every upper event. -/
theorem prodBernoulli_le_preimage_union (q : ι → unitInterval) (E : Set ι)
    {A : Set (Set ι)} (hA : IsUpperSet A) :
    prodBernoulli q A ≤ prodBernoulli q ((· ∪ E) ⁻¹' A) :=
  measure_mono (fun _ h => hA Set.subset_union_left h)

/-- Masked-profile formulation of the deterministic comparison. -/
theorem prodBernoulli_inter_profile_le (q : ι → unitInterval) (E : Set ι)
    [DecidablePred (· ∈ E)] {A : Set (Set ι)} (hA : IsUpperSet A)
    (hm : MeasurableSet A) :
    prodBernoulli (fun i => if i ∈ E then q i else 0) A ≤ prodBernoulli q A := by
  rw [← prodBernoulli_map_inter q E, Measure.map_apply (by fun_prop) hm]
  exact prodBernoulli_preimage_inter_le q E hA

/-- The corresponding comparison with probabilities fixed at one. -/
theorem prodBernoulli_le_union_profile (q : ι → unitInterval) (E : Set ι)
    [DecidablePred (· ∈ E)] {A : Set (Set ι)} (hA : IsUpperSet A)
    (hm : MeasurableSet A) :
    prodBernoulli q A ≤ prodBernoulli (fun i => if i ∈ E then 1 else q i) A := by
  rw [← prodBernoulli_map_union q E, Measure.map_apply (by fun_prop) hm]
  exact prodBernoulli_le_preimage_union q E hA

-- Measurability already belongs to mathlib's set-valued measurable-function API.
example (E : Set ι) : Measurable (fun ω : Set ι => ω ∩ E) := by fun_prop
example (E : Set ι) : Measurable (fun ω : Set ι => ω ∪ E) := by fun_prop
example (E : Set ι) : Measurable (fun ω : Set ι => ω \ E) := by fun_prop

-- Empty/full modifying sets, and the extreme profiles, require no exceptions.
example (q : ι → unitInterval) :
    (prodBernoulli q).map (· ∩ (∅ : Set ι)) = prodBernoulli (fun _ => 0) := by
  simpa using prodBernoulli_map_inter q (∅ : Set ι)

example (q : ι → unitInterval) :
    (prodBernoulli q).map (· ∪ (Set.univ : Set ι)) = prodBernoulli (fun _ => 1) := by
  simpa using prodBernoulli_map_union q (Set.univ : Set ι)

example (E : Set ι) [DecidablePred (· ∈ E)] :
    (prodBernoulli (fun _ : ι => 1)).map (· ∩ E) =
      prodBernoulli (fun i => if i ∈ E then 1 else 0) :=
  prodBernoulli_map_inter _ E

example (q : ι → unitInterval) :
    (prodBernoulli q).map (· \ (∅ : Set ι)) = prodBernoulli q := by
  simp

end PercLib.Probability

namespace PercLib.Percolation.Bond
open PercLib.Probability
variable {V : Type*}

/-- Restricting the configuration to a host edge set masks its bond profile. -/
theorem law_map_inter_edgeSet (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    [DecidablePred (· ∈ G.edgeSet)] :
    (law q).map (· ∩ G.edgeSet) = law (fun e => if e ∈ G.edgeSet then q e else 0) :=
  prodBernoulli_map_inter q G.edgeSet

/-- Restricting to a host graph cannot increase its two-point function. -/
theorem tau_mask_edgeSet_le [Countable V] (G : SimpleGraph V)
    (q : Sym2 V → unitInterval) [DecidablePred (· ∈ G.edgeSet)] (x y : V) :
    tau (fun e => if e ∈ G.edgeSet then q e else 0) x y ≤ tau q x y :=
  prodBernoulli_inter_profile_le q G.edgeSet
    (fun _ _ h hc => conn_mono h hc) (measurableSet_conn x y)

end PercLib.Percolation.Bond
