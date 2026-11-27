/-
Integrated Ultramath work, swarm `smwyop3kc`, member `m2`.
Production worktree: `.scratch/critical-lrp-orchestration` (read only), HEAD
`2e544875fbae83810bd1aa1de1d8faddcdeacc05`.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.Main

/-!
# Padding a moment function outside the orders used by the induction step

`moment_upper_bound_of_percolation` (Proposition I.4.20's step (I.4.19)) states
the positivity hypothesis `hmom` for every order `m : ℕ`.  Its proof only ever
consumes the orders `1`, `2` and `p` (through `mom 1`, `mom 2`, `mom p` and
`mixedMoment p`, `drivingTerm p`), so a moment function that is padded outside
`[1, p]` by the constant `1` is enough — provided the padding does not change
the hypotheses.  `padMom` is that padding; it changes nothing on `[1, p]`, and
therefore nothing in `mom 1`, `mom 2`, `mom p`, `momentRatio`, `mixedMoment`,
`drivingTerm`, or in the binomial derivative identity.

This module only introduces the definition and its reductions.  No theorem of
the paper is used.
-/

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- The moment function with every order outside `[1, p]` replaced by `1`.

The value `1` is positive and nonnegative, so it discharges the "junk" orders
of the interface without any claim about the model at those orders. -/
def padMom (p : ℕ) (mom : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun m r => if 1 ≤ m ∧ m ≤ p then mom m r else 1

theorem padMom_apply_of_mem {p m : ℕ} (mom : ℕ → ℝ → ℝ) (r : ℝ)
    (hm : 1 ≤ m ∧ m ≤ p) : padMom p mom m r = mom m r := by
  simp [padMom, hm]

theorem padMom_apply_of_not_mem {p m : ℕ} (mom : ℕ → ℝ → ℝ) (r : ℝ)
    (hm : ¬ (1 ≤ m ∧ m ≤ p)) : padMom p mom m r = 1 := by
  simp [padMom, hm]

/-- `padMom` is positive as soon as the original moments are positive on `[1, p]`. -/
theorem padMom_pos {p : ℕ} {mom : ℕ → ℝ → ℝ}
    (hmom : ∀ m, 1 ≤ m → m ≤ p → ∀ x, 0 < x → 0 < mom m x) :
    ∀ m x, 0 < x → 0 < padMom p mom m x := by
  intro m x hx
  by_cases hm : 1 ≤ m ∧ m ≤ p
  · rw [padMom_apply_of_mem mom x hm]
    exact hmom m hm.1 hm.2 x hx
  · rw [padMom_apply_of_not_mem mom x hm]
    exact one_pos

/-- `padMom` is nonnegative as soon as the original moments are positive on `[1, p]`. -/
theorem padMom_nonneg {p : ℕ} {mom : ℕ → ℝ → ℝ}
    (hmom : ∀ m, 1 ≤ m → m ≤ p → ∀ x, 0 < x → 0 < mom m x) :
    ∀ m x, 0 < x → 0 ≤ padMom p mom m x :=
  fun m x hx => (padMom_pos hmom m x hx).le

/-- On `2 ≤ p`, `padMom` does not change `momentRatio`. -/
theorem momentRatio_padMom (p : ℕ) (hp : 2 ≤ p) (mom : ℕ → ℝ → ℝ) :
    momentRatio (padMom p mom) = momentRatio mom := by
  funext r
  unfold momentRatio
  rw [padMom_apply_of_mem mom r ⟨le_refl 1, by omega⟩,
    padMom_apply_of_mem mom r ⟨by norm_num, hp⟩]

/-- On `2 ≤ p`, `padMom` does not change `mixedMoment`. -/
theorem mixedMoment_padMom (p : ℕ) (hp : 2 ≤ p) (mom : ℕ → ℝ → ℝ) (r : ℝ) :
    mixedMoment p (padMom p mom) r = mixedMoment p mom r := by
  unfold mixedMoment
  rw [momentRatio_padMom p hp mom,
    padMom_apply_of_mem mom r ⟨le_refl 1, by omega⟩]

end PercLib.CriticalLRP.VolumeMoments.HigherMoments
