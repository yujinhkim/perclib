/-
Standard-Borel interface for canonical configurations. New glue from pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679: countable products, measurable equivalences,
and transport of Polish topologies. No new configuration or probability law is introduced.
-/
module

public import PercLib.Probability.ProdBernoulli
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.CondDistrib

/-! # Standard Borel configuration spaces

For countably many indices, the existing measurable space on `Set ι` is standard
Borel. This enables regular conditional distributions on the canonical product law.
The countability hypothesis is essential; no uncountable extension is asserted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace PercLib.Probability

/-- Countable configurations inherit a Polish realization from their predicate tuples. -/
instance (priority := 100) instStandardBorelSpaceSet {ι : Type*} [Countable ι] :
    StandardBorelSpace (Set ι) := by
  let e : Set ι ≃ᵐ (ι → Prop) := MeasurableEquiv.setOfPred.symm
  obtain ⟨t, hb, hp⟩ := StandardBorelSpace.polish (α := ι → Prop)
  let := t
  have := hb
  have := hp
  let : TopologicalSpace (Set ι) := TopologicalSpace.induced e t
  refine ⟨⟨inferInstance, ?_, e.toEquiv.polishSpace_induced⟩⟩
  refine ⟨?_⟩
  rw [borel_comap, ← BorelSpace.measurable_eq]
  exact e.measurableEmbedding.comap_eq.symm

-- The empty index type is allowed.
example : StandardBorelSpace (Set Empty) := inferInstance

-- Canonical bond configurations are sets of unordered pairs; `Sym2 V` is countable.
example {V : Type*} [Countable V] :
    StandardBorelSpace (Set (Sym2 V)) := inferInstance

-- Conditioning the entire bond configuration on one bond now elaborates as a Markov kernel.
example {V : Type*} [Countable V] (q : Sym2 V → unitInterval) (e : Sym2 V) :
    IsMarkovKernel
      (condDistrib (id : Set (Sym2 V) → Set (Sym2 V))
        (fun ω => e ∈ ω) (prodBernoulli q)) := inferInstance

end PercLib.Probability
