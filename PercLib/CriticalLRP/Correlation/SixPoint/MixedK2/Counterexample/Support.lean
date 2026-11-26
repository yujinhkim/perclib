/-
Coordinator-integrated from the independently rebuilt `smwxb4a1l/m3` Line6 artifact
at production base `8d1c9eb3738a26cc63afc07f525ba4af357bd905`.
-/
/-
Probability of cylinders and the almost-sure support for the six-vertex line profile.

Ultramath swarm `smwxb4a1l`, member `m3`, direction `HUB-LINK-COUNTEREXAMPLE`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Defs

/-!
# The line profile: cylinder probabilities and almost-sure support

The profile `lineProfile θ` opens the five line edges with probability `θ` and every other
pair with probability `0`.  Hence: the probability that a finite set of line edges is open
is `θ ^ card`, and almost surely no non-line pair is open.
-/

@[expose] public section

namespace PercLib.CriticalLRP.Counterexample.Line6

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

/-! ## Values of the profile -/

theorem lineProfile_of_mem {θ : unitInterval} {e : Sym2 (Fin 6)} (h : e ∈ lineEdges) :
    lineProfile θ e = θ := by
  simp only [lineProfile, h, ite_true]

theorem lineProfile_of_not_mem {θ : unitInterval} {e : Sym2 (Fin 6)} (h : e ∉ lineEdges) :
    lineProfile θ e = 0 := by
  simp only [lineProfile, h, ite_false]

/-- The `ℝ≥0∞`-weight of a line edge. -/
theorem toNNReal_lineProfile_of_mem {θ : unitInterval} {e : Sym2 (Fin 6)} (h : e ∈ lineEdges) :
    (unitInterval.toNNReal (lineProfile θ e) : ℝ≥0∞) = (unitInterval.toNNReal θ : ℝ≥0∞) := by
  rw [lineProfile_of_mem h]

/-- The `ℝ≥0∞`-weight of a pair that is not a line edge vanishes. -/
theorem toNNReal_lineProfile_of_not_mem {θ : unitInterval} {e : Sym2 (Fin 6)}
    (h : e ∉ lineEdges) : (unitInterval.toNNReal (lineProfile θ e) : ℝ≥0∞) = 0 := by
  rw [lineProfile_of_not_mem h]
  simp

/-- The weight of a line edge is `eps`. -/
theorem toNNReal_lineProfile_theta {e : Sym2 (Fin 6)} (h : e ∈ lineEdges) :
    (unitInterval.toNNReal (lineProfile theta e) : ℝ≥0∞) = eps := by
  rw [toNNReal_lineProfile_of_mem h]
  rfl

/-! ## Cylinder probabilities -/

/-- The probability that all edges of a finite set of line edges are open. -/
theorem law_subset_lineEdges (θ : unitInterval) (F : Finset (Sym2 (Fin 6)))
    (hF : F ⊆ lineEdges) :
    law (lineProfile θ) {ω : Config (Fin 6) | (F : Set (Sym2 (Fin 6))) ⊆ ω}
      = (unitInterval.toNNReal θ : ℝ≥0∞) ^ F.card := by
  rw [law, prodBernoulli_subset]
  rw [Finset.prod_congr rfl (fun e he => toNNReal_lineProfile_of_mem (hF he)),
    Finset.prod_const]

/-- The probability that all edges of a finite set of line edges are open, at `θ = 1/64`. -/
theorem law_subset_lineEdges_theta (F : Finset (Sym2 (Fin 6))) (hF : F ⊆ lineEdges) :
    law (lineProfile theta) {ω : Config (Fin 6) | (F : Set (Sym2 (Fin 6))) ⊆ ω}
      = eps ^ F.card := by
  rw [law_subset_lineEdges theta F hF]
  rfl

/-! ## Almost-sure support -/

theorem measurableSet_lineSupportCompl : MeasurableSet lineSupportCompl :=
  MeasurableSet.iUnion fun e => measurableSet_mem e.1

theorem lineSupport_eq_compl : lineSupport = (lineSupportCompl)ᶜ := by
  ext ω
  simp only [lineSupport, lineSupportCompl, Set.mem_ofPred_eq, Set.mem_compl_iff,
    Set.mem_iUnion]
  constructor
  · intro h
    rintro ⟨e, he⟩
    exact e.2 (h he)
  · intro h e he
    by_contra hne
    exact h ⟨⟨e, hne⟩, he⟩

theorem lineSupportCompl_eq_compl : lineSupportCompl = (lineSupport)ᶜ := by
  rw [lineSupport_eq_compl, compl_compl]

theorem measurableSet_lineSupport : MeasurableSet lineSupport := by
  rw [lineSupport_eq_compl]
  exact measurableSet_lineSupportCompl.compl

/-- No non-line pair is open, almost surely. -/
theorem law_lineSupport_compl (θ : unitInterval) :
    law (lineProfile θ) (lineSupport)ᶜ = 0 := by
  rw [← lineSupportCompl_eq_compl]
  refine measure_iUnion_null fun e => ?_
  rw [law, prodBernoulli_setOf_mem, toNNReal_lineProfile_of_not_mem e.2]

/-- The line support has full measure. -/
theorem law_lineSupport (θ : unitInterval) : law (lineProfile θ) (lineSupport) = 1 := by
  have h := measure_add_measure_compl (μ := law (lineProfile θ))
    (s := lineSupport) measurableSet_lineSupport
  rw [law_lineSupport_compl θ, add_zero, measure_univ] at h
  exact h

/-- Two events that agree on the line support have the same probability. -/
theorem law_congr_of_lineSupport {θ : unitInterval} {A B : Set (Config (Fin 6))}
    (h : ∀ ω : Config (Fin 6), ω ∈ lineSupport → (ω ∈ A ↔ ω ∈ B)) :
    law (lineProfile θ) A = law (lineProfile θ) B := by
  have hnull : law (lineProfile θ) (lineSupport)ᶜ = 0 := law_lineSupport_compl θ
  have hA : law (lineProfile θ) A = law (lineProfile θ) (A ∩ lineSupport) := by
    have hsplit := measure_inter_add_sdiff (μ := law (lineProfile θ)) (s := A)
      measurableSet_lineSupport
    have hzero : law (lineProfile θ) (A \ lineSupport) = 0 :=
      measure_mono_null (Set.sdiff_subset_compl A lineSupport) hnull
    rw [hzero, add_zero] at hsplit
    exact hsplit.symm
  have hB : law (lineProfile θ) B = law (lineProfile θ) (B ∩ lineSupport) := by
    have hsplit := measure_inter_add_sdiff (μ := law (lineProfile θ)) (s := B)
      measurableSet_lineSupport
    have hzero : law (lineProfile θ) (B \ lineSupport) = 0 :=
      measure_mono_null (Set.sdiff_subset_compl B lineSupport) hnull
    rw [hzero, add_zero] at hsplit
    exact hsplit.symm
  rw [hA, hB]
  congr 1
  ext ω
  constructor
  · rintro ⟨hA, hS⟩
    exact ⟨(h ω hS).mp hA, hS⟩
  · rintro ⟨hB, hS⟩
    exact ⟨(h ω hS).mpr hB, hS⟩

end PercLib.CriticalLRP.Counterexample.Line6
