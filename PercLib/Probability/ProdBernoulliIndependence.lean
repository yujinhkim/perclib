/-
Adapted and generalised from Tom Hutchcroft's near-critical-diffusivity,
Percolation/Literature/BernoulliPercolation.lean at
c820fea91a7482c1755de0ec94ecb9f59ccfcacc, under the native-source permission R-3.
Source declarations: bondPercolation_iIndepFun_mem, bondPercolation_indep_holds.
The profile is arbitrary and no countability, host, or diagonal hypothesis remains.
Block consequences use mathlib's independence API directly.
-/
module

public import PercLib.Probability.ProdBernoulli
public import Mathlib.Probability.Independence.InfinitePi

/-! # Coordinate and block independence for the canonical Bernoulli law

Configurations remain sets of indices. Blocks may be infinite; their observables
must be measurable in the product sigma algebra. No alternative law is introduced.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace PercLib.Probability

variable {ι : Type*}

/-- Coordinate membership predicates are mutually independent for every profile. -/
theorem prodBernoulli_iIndepFun_mem (p : ι → unitInterval) :
    iIndepFun (fun i (ω : Set ι) => i ∈ ω) (prodBernoulli p) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => measurable_set_mem i)]
  have hS : Measurable (fun q : ι → Prop => {i | q i}) :=
    MeasurableEquiv.setOfPred.measurable
  have h : (prodBernoulli p).map (fun (ω : Set ι) i => i ∈ ω) =
      Measure.infinitePi (fun i => bernoulliMeasure True False (p i)) := by
    rw [prodBernoulli_eq_map, Measure.map_map (by fun_prop) hS]
    exact Measure.map_id
  rw [h]
  congrm Measure.infinitePi fun i => ?_
  rw [prodBernoulli_eq_map, Measure.map_map (measurable_set_mem i) hS]
  exact (Measure.infinitePi_map_eval (fun j => bernoulliMeasure True False (p j)) i).symm

/-- The open-coordinate events are mutually independent, including endpoint profiles. -/
theorem prodBernoulli_iIndepSet_mem (p : ι → unitInterval) :
    iIndepSet (fun i => {ω : Set ι | i ∈ ω}) (prodBernoulli p) := by
  rw [← iIndep_comap_mem_iff]
  exact prodBernoulli_iIndepFun_mem p

/-- Disjoint blocks of coordinates are independent as predicate-valued tuples. -/
theorem prodBernoulli_indepFun_restrict (p : ι → unitInterval)
    (S T : Set ι) (hST : Disjoint S T) :
    IndepFun (fun (ω : Set ι) (i : S) => (i : ι) ∈ ω)
      (fun (ω : Set ι) (i : T) => (i : ι) ∈ ω) (prodBernoulli p) :=
  (prodBernoulli_iIndepFun_mem p).indepFun_set S T hST (fun i => measurable_set_mem i)

/-- Disjoint restrictions, expressed as configurations on the two subtype blocks. -/
theorem prodBernoulli_indepFun_blocks (p : ι → unitInterval)
    (S T : Set ι) (hST : Disjoint S T) :
    IndepFun (fun ω : Set ι => {i : S | (i : ι) ∈ ω})
      (fun ω : Set ι => {i : T | (i : ι) ∈ ω}) (prodBernoulli p) :=
  (prodBernoulli_indepFun_restrict p S T hST).comp
    MeasurableEquiv.setOfPred.measurable MeasurableEquiv.setOfPred.measurable

/-- Measurable observables of disjoint blocks are independent. -/
theorem prodBernoulli_indepFun_block_observables (p : ι → unitInterval)
    (S T : Set ι) (hST : Disjoint S T)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : Set S → α) (g : Set T → β) (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun ω : Set ι => f {i : S | (i : ι) ∈ ω})
      (fun ω : Set ι => g {i : T | (i : ι) ∈ ω}) (prodBernoulli p) :=
  (prodBernoulli_indepFun_blocks p S T hST).comp hf hg

/-- The joint probability of measurable events on disjoint blocks factors. -/
theorem prodBernoulli_block_inter (p : ι → unitInterval)
    (S T : Set ι) (hST : Disjoint S T)
    (A : Set (Set S)) (B : Set (Set T)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    prodBernoulli p {ω | {i : S | (i : ι) ∈ ω} ∈ A ∧ {i : T | (i : ι) ∈ ω} ∈ B} =
      prodBernoulli p {ω | {i : S | (i : ι) ∈ ω} ∈ A} *
        prodBernoulli p {ω | {i : T | (i : ι) ∈ ω} ∈ B} :=
  (prodBernoulli_indepFun_blocks p S T hST).measure_inter_preimage_eq_mul A B hA hB

/-- Finite disjoint blocks are a specialization, without restricting the ambient type. -/
theorem prodBernoulli_indepFun_finset (p : ι → unitInterval)
    (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun (fun (ω : Set ι) (i : S) => (i : ι) ∈ ω)
      (fun (ω : Set ι) (i : T) => (i : ι) ∈ ω) (prodBernoulli p) :=
  (prodBernoulli_iIndepFun_mem p).indepFun_finset S T hST
    (fun i => measurable_set_mem i)

/-- Empty ambient index type. -/
example : iIndepSet (fun i : Empty => {ω : Set Empty | i ∈ ω})
    (prodBernoulli (fun _ => 0)) := prodBernoulli_iIndepSet_mem _

/-- A mixed endpoint profile still gives independent distinct coordinates. -/
example : IndepFun (fun ω : Set Bool => false ∈ ω) (fun ω : Set Bool => true ∈ ω)
    (prodBernoulli (fun b => if b then 1 else 0)) :=
  (prodBernoulli_iIndepFun_mem _).indepFun (by decide)

/-- Two infinite disjoint blocks, with an arbitrary inhomogeneous profile. -/
example (p : ℤ → unitInterval) :
    IndepFun (fun ω : Set ℤ => {i : Set.Iio (0 : ℤ) | (i : ℤ) ∈ ω})
      (fun ω : Set ℤ => {i : Set.Ici (0 : ℤ) | (i : ℤ) ∈ ω}) (prodBernoulli p) :=
  prodBernoulli_indepFun_blocks p _ _ (Set.disjoint_left.mpr (by
    intro i hi hj
    exact (not_lt_of_ge (show 0 ≤ i from hj)) (show i < 0 from hi)))

end PercLib.Probability
