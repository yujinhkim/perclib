/-
A non-vacuous instance of the random revealed set hypothesis: a two-coordinate
"one-step exploration" in which the coordinate `true` is revealed exactly when the
coordinate `false` is found open in the first copy, while `false` itself is always revealed.

This is the combinatorial pattern of [GZ24, Example 4.4]: the revealed set contains every
coordinate whose value the exploration inspects, so it is self-determined.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.RandomAmalgam

/-!
# A genuinely random self-determined revealed set

`Sfam 0 = {false}` and `Sfam 1 = univ`, with index `1` exactly when `(false, false) ∈ ω`.
Since `false` is revealed in both branches, the selection is self-determined although it is
not a function of a fixed set: the main theorem of `RandomAmalgam.lean` therefore applies to
a genuinely random revealed set, not only to constant families.
-/

@[expose] public section

open MeasureTheory
open PercLib.Probability
open scoped ENNReal

namespace PercLib.GladkovAmalgam

/-- The two-member family: `{false}` and everything. -/
noncomputable def stepFam (n : ℕ) : Set Bool :=
  if n = 1 then Set.univ else {false}

/-- Reveal the second coordinate exactly when the first copy is open at the first one. -/
noncomputable def stepIdx (ω : Set (Bool × Bool)) : ℕ := by
  classical
  exact if (false, false) ∈ ω then 1 else 0

theorem stepFam_zero : stepFam 0 = ({false} : Set Bool) := by
  unfold stepFam
  split_ifs <;> simp_all

theorem stepFam_one : stepFam 1 = (Set.univ : Set Bool) := by
  unfold stepFam
  split_ifs <;> simp_all

theorem stepIdx_of_mem (ω : Set (Bool × Bool)) (h : (false, false) ∈ ω) : stepIdx ω = 1 := by
  unfold stepIdx
  split_ifs
  rfl

theorem stepIdx_of_notMem (ω : Set (Bool × Bool)) (h : (false, false) ∉ ω) : stepIdx ω = 0 := by
  unfold stepIdx
  split_ifs
  rfl

theorem stepFam_measurable :
    ∀ i : Bool, MeasurableSet {ω : Set (Bool × Bool) | i ∈ stepFam (stepIdx ω)} := by
  intro i
  cases i
  · exact MeasurableSet.of_discrete
  · have hEq : {ω : Set (Bool × Bool) | true ∈ stepFam (stepIdx ω)} =
        {ω : Set (Bool × Bool) | (false, false) ∈ ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      by_cases h : (false, false) ∈ ω
      · rw [stepIdx_of_mem ω h, stepFam_one]
        simp [h]
      · rw [stepIdx_of_notMem ω h, stepFam_zero]
        simp [h]
    rw [hEq]
    exact MeasurableSet.of_discrete

/-- The selection is self-determined: the only inspected coordinate, `false`, is always
revealed. -/
theorem step_selfDetermined : SelfDetermined stepFam stepIdx := by
  classical
  intro ω ω' hagree
  by_cases h : (false, false) ∈ ω
  · have h1 : stepIdx ω = 1 := stepIdx_of_mem ω h
    rw [h1, stepFam_one] at hagree
    have hmem : (false, false) ∈ ω' := by
      have hiff := congrArg (fun s : Set (Bool × Bool) => (false, false) ∈ s) hagree
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true] at hiff
      exact hiff.mp h
    rw [stepIdx_of_mem ω' hmem, h1]
  · have h1 : stepIdx ω = 0 := stepIdx_of_notMem ω h
    rw [h1, stepFam_zero] at hagree
    have hmem : (false, false) ∉ ω' := by
      intro hc
      have hiff := congrArg (fun s : Set (Bool × Bool) => (false, false) ∈ s) hagree
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, and_iff_left] at hiff
      exact h (hiff.mpr hc)
    rw [stepIdx_of_notMem ω' hmem, h1]

/-- **Non-vacuity.** The random amalgamation theorem applies to a genuinely random revealed
set: `S` is `{false}` or `univ` according to the first copy at `false`. -/
theorem step_random_amalgam_indep (q : Bool → unitInterval) {A B : Set (Set Bool)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    prodBernoulli (twoProfile q) {ω : Set (Bool × Bool) |
        amalFirstRand stepFam stepIdx ω ∈ A ∧ amalSecondRand stepFam stepIdx ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B :=
  prodBernoulli_random_amalgam_indep q (by exact Measurable.of_discrete) stepFam_measurable
    step_selfDetermined hA hB

end PercLib.GladkovAmalgam
