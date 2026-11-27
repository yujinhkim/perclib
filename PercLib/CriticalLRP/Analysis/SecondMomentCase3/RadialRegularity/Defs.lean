/-
Ultramath swarm `smwzlje3f`, member `m7`, direction `d3`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f` with m3/m7 sources.
Integration based on production commit `caf06cb0a9face27c4dce7b4a13703d40d4568ac`.

# Monotone exhaustive finite windows on a countable vertex type

The second-moment radius calculus of `Analysis/SecondMomentCornerIdentity.lean` consumes a
monotone family `S : ℕ → Finset (Sym2 M.V)` of finite edge windows that exhausts the edge set
(`∀ e, ∃ k, e ∈ S k`).  That family is not a hypothesis on the model: the source vertex set is
`M.V = Fin M.d → ℤ`, hence countable, and every countable type carries such a family.

This file supplies the construction once, so that the window family never has to appear among the
model-level hypotheses of a consumer.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCornerIdentity

/-! # Exhausting finite windows -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

@[expose] public section

noncomputable section

open Set

namespace PercLib.CriticalLRP.Orchestration.Smwzlje3fM7

/-- **Every countable nonempty type has a monotone exhaustive family of finite subsets.**
Enumerate the type as `f : ℕ → α` and take the initial segments of the enumeration.

This is the `hSmono`/`hS` pair of the off-corner flux calculus
(`SourceModelData.ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two` and
`SmwywszgoM5.ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii_tail_no_meas`): the family is
bookkeeping about the vertex set, not an input of the percolation model. -/
theorem exists_monotone_finset_exhausting (α : Type*) [Countable α] [Nonempty α] :
    ∃ S : ℕ → Finset α, Monotone S ∧ ∀ a : α, ∃ k, a ∈ S k := by
  classical
  have hcnt : (univ : Set α).Countable := countable_univ
  obtain ⟨f, hf⟩ :=
    (countable_iff_exists_subset_range (s := (univ : Set α))).1 hcnt
  refine ⟨fun k => (Finset.range k).image f, fun a b hab => ?_, fun a => ?_⟩
  · exact Finset.image_subset_image (Finset.range_mono hab)
  · obtain ⟨n, hn⟩ := hf (mem_univ a)
    exact ⟨n + 1, Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_self n), hn⟩⟩

namespace SourceModelData

variable (M : SourceModelData)

/-- **The source edge set admits a monotone exhaustive family of finite windows.**
`M.V = Fin M.d → ℤ` is countable, so `Sym2 M.V` is countable
(`Quotient.countable` of `M.V × M.V`), and `exists_monotone_finset_exhausting` applies. -/
theorem exists_windowFinsets :
    ∃ S : ℕ → Finset (Sym2 M.V), Monotone S ∧ ∀ e : Sym2 M.V, ∃ k, e ∈ S k := by
  haveI : Nonempty M.V := ⟨0⟩
  haveI : Nonempty (Sym2 M.V) := ⟨s((0 : M.V), (0 : M.V))⟩
  exact exists_monotone_finset_exhausting (Sym2 M.V)

end SourceModelData

end PercLib.CriticalLRP.Orchestration.Smwzlje3fM7

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.exists_monotone_finset_exhausting
#print axioms PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.exists_windowFinsets
