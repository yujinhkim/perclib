/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m3/.
-/

/- Sharpness of the Case 1 discrepancy inequality in the degenerate no-open-edge law.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main

/-!
# Sharpness of the Case 1 discrepancy inequality

The Case 1 inequality proved in `Case1.lean` is
`prodFactor ≤ mixedExcl + windowMoment`, i.e.
`|B| E|K|^a E|K|^b − A_ℓ(r) ≤ E[|K|^{a+b}|K ∩ B|]`.

This file evaluates all three quantities for the law with no open edges,
`π₀ = 0`, where `edgeMeasure π₀ = dirac ∅` and every cluster is a singleton:
`|K_y| = 1`, `K_o = {o}`.  Then

* `mixedExcl = |B ∖ {o}|`,
* `prodFactor = |B|`,
* `windowMoment = 1{o ∈ B}`,

so the discrepancy is `1{o ∈ B}` — *exactly* the window moment.  The inequality
therefore has a genuine equality case: the factor `1(y ∉ K_o)` in the excluded
expectation and the window `|K_o ∩ B|` in the bound are normalised consistently
(a wrong multiplicity in either would break the equality here).

No percolation statement is claimed: this is a consistency check of the formal
statement, not evidence about transitive lattices.
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case1

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterVol_empty (v : V) : clusterVol (∅ : Config V) v = 1 := by
  rw [clusterVol_eq_encard, cluster_empty, Set.encard_singleton]
  norm_num

theorem powMomentAt_zero (o : V) (a : ℕ) : powMomentAt (fun _ => (0 : unitInterval)) a o = 1 := by
  have hmeas : Measurable fun ω : Config V => clusterVol ω o ^ a :=
    (measurable_clusterVol o).pow_const a
  simp only [powMomentAt, edgeMeasure_zero]
  rw [lintegral_dirac' (∅ : Config V) hmeas, clusterVol_empty, one_pow]

theorem mixedExcl_zero (o : V) (a b : ℕ) (B : Finset V) :
    mixedExcl (fun _ => (0 : unitInterval)) o a b B
      = (((B.filter (fun y => y ≠ o)).card : ℕ) : ℝ≥0∞) := by
  have hmeas : Measurable fun ω : Config V =>
      clusterVol ω o ^ a *
        ∑ y ∈ B, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ b :=
    ((measurable_clusterVol o).pow_const a).mul
      (Finset.measurable_sum B fun y _ =>
        (measurable_const.indicator (measurableSet_cluster_mem o y).compl).mul
          ((measurable_clusterVol y).pow_const b))
  simp only [mixedExcl, edgeMeasure_zero]
  rw [lintegral_dirac' (∅ : Config V) hmeas]
  simp only [clusterVol_empty, cluster_empty, one_pow, one_mul]
  have hpt : ∀ x : V,
      ({o} : Set V)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x * 1 = if x ≠ o then 1 else 0 := by
    intro x
    by_cases hx : x = o
    · rw [hx, Set.indicator_of_notMem (by simp), zero_mul, ite_eq_right (by simp)]
    · rw [Set.indicator_of_mem (by simpa using hx), mul_one, ite_eq_left hx]
  trans ∑ x ∈ B, (if x ≠ o then (1 : ℝ≥0∞) else 0)
  · exact Finset.sum_congr rfl fun x _ => hpt x
  · rw [Finset.sum_boole]

theorem prodFactor_zero (o : V) (a b : ℕ) (B : Finset V) :
    prodFactor (fun _ => (0 : unitInterval)) o a b B = ((B.card : ℕ) : ℝ≥0∞) := by
  rw [prodFactor]
  simp only [powMomentAt_zero, mul_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem windowMoment_zero (o : V) (k : ℕ) (B : Finset V) :
    windowMoment (fun _ => (0 : unitInterval)) o k B = (if o ∈ B then 1 else 0) := by
  have hmeas : Measurable fun ω : Config V => clusterVol ω o ^ k * clusterVolIn ω o (B : Set V) :=
    ((measurable_clusterVol o).pow_const k).mul (measurable_clusterVolIn o (B : Set V))
  simp only [windowMoment, edgeMeasure_zero]
  rw [lintegral_dirac' (∅ : Config V) hmeas]
  rw [clusterVol_empty, one_pow, one_mul]
  unfold clusterVolIn
  rw [cluster_empty]
  by_cases ho : o ∈ B
  · have hsub : ({o} : Set V) ⊆ (B : Set V) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ho
    rw [ite_eq_left ho, Set.inter_eq_self_of_subset_left hsub, Set.encard_singleton]
    norm_num
  · have hemp : ({o} : Set V) ∩ (B : Set V) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hx hxB
      rw [hx] at hxB
      exact ho hxB
    rw [ite_eq_right ho, hemp, Set.encard_empty]
    norm_num

/-- **Sharpness in the no-edge law**: the Case 1 inequality
`prodFactor ≤ mixedExcl + windowMoment` is an equality, so the discrepancy
`|B| E|K|^a E|K|^b − A_ℓ(r)` equals the mixed cluster-window moment
`E[|K|^{a+b}|K ∩ B|] = 1{o ∈ B}` exactly. -/
theorem prodFactor_zero_eq (o : V) (a b : ℕ) (B : Finset V) :
    prodFactor (fun _ => (0 : unitInterval)) o a b B
      = mixedExcl (fun _ => (0 : unitInterval)) o a b B
        + windowMoment (fun _ => (0 : unitInterval)) o (a + b) B := by
  rw [prodFactor_zero, mixedExcl_zero, windowMoment_zero]
  by_cases ho : o ∈ B
  · rw [ite_eq_left ho]
    have herase : B.filter (fun y => y ≠ o) = B.erase o := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [herase, ← Finset.card_erase_add_one ho]
    push_cast
    ring
  · rw [ite_eq_right ho, add_zero]
    have hfilter : B.filter (fun y => y ≠ o) = B := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact h.1
      · intro hx
        exact ⟨hx, fun hxo => by rw [hxo] at hx; exact ho hx⟩
    rw [hfilter]

end I420Case1

end PercLib.CriticalLRP
