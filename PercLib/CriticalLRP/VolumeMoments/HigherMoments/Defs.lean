/- Integrated from independently rebuilt Ultramath work.
Production base ed48eea0fa7697ac0e16db08e39b60ebb7c70e02.
Scratch source: ../../.ultramath/smwvlmbqa/m2/Defs.lean; migrated to current namespaces.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.Convolution

/-!
# Higher-moment induction data for Proposition I.4.20

Source: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Proposition I.4.20 and its proof (pp. 47--52).

This file only introduces the notation used in the induction step: the ratio
`E|K|²/E|K|`, the double-factorial normaliser `(2p-3)!!` in `ℝ`, the paper's
driving term `α(p-2)(2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`, and the target
`(2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`.  No theorem of the paper is used here; the
whole point of the separation is that every definition lives in this one module
so that the proof modules import a fixed interface.

The convention is the paper's: `mom p r` denotes `E_{β_c,r}|K|^p` (an abstract
moment function; no probability space is fixed here), and
`dblFact n = (2n-1)!!` with `dblFact 0 = 1`.
-/

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- The odd double factorial `(2n-1)!!` of the paper, as a real number.
`dblFact 0 = 1` encodes `(-1)!! = 0!! = 1`. -/
def dblFact (n : ℕ) : ℝ := ((M n : ℕ) : ℝ)

/-- The paper's ratio `E|K|² / E|K|` for a moment function `mom`. -/
def momentRatio (mom : ℕ → ℝ → ℝ) (r : ℝ) : ℝ := mom 2 r / mom 1 r

/-- The target of the induction step (I.4.19):
`(2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`. -/
def mixedMoment (p : ℕ) (mom : ℕ → ℝ → ℝ) (r : ℝ) : ℝ :=
  dblFact (p - 1) * momentRatio mom r ^ ((p : ℝ) - 1) * mom 1 r

/-- The driving term of the induction step in the proof of Proposition I.4.20,
`α (p-2) (2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`.  (Its regular variation index is
`(2p-1)α`, the content of `drivingTerm_regularlyVarying`.) -/
def drivingTerm (p : ℕ) (α : ℝ) (mom : ℕ → ℝ → ℝ) (r : ℝ) : ℝ :=
  α * ((p : ℝ) - 2) * dblFact (p - 1) * momentRatio mom r ^ ((p : ℝ) - 1) * mom 1 r

@[simp] theorem dblFact_zero : dblFact 0 = 1 := by
  simp [dblFact]

@[simp] theorem dblFact_one : dblFact 1 = 1 := by
  simp [dblFact]

theorem dblFact_pos (n : ℕ) : 0 < dblFact n := by
  unfold dblFact
  exact_mod_cast M_pos n

theorem dblFact_succ (n : ℕ) : dblFact (n + 1) = (2 * (n : ℝ) + 1) * dblFact n := by
  unfold dblFact
  rw [M_succ]
  push_cast
  ring

theorem dblFact_ne_zero (n : ℕ) : dblFact n ≠ 0 := (dblFact_pos n).ne'

/-- `drivingTerm` is the paper's `α (p-2)` multiple of the target `mixedMoment`. -/
theorem drivingTerm_eq_smul (p : ℕ) (α : ℝ) (mom : ℕ → ℝ → ℝ) (r : ℝ) :
    drivingTerm p α mom r = α * ((p : ℝ) - 2) * mixedMoment p mom r := by
  unfold drivingTerm mixedMoment
  ring

theorem momentRatio_pos {mom : ℕ → ℝ → ℝ} {r : ℝ} (h1 : 0 < mom 1 r) (h2 : 0 < mom 2 r) :
    0 < momentRatio mom r := by
  unfold momentRatio
  exact div_pos h2 h1

theorem mixedMoment_pos {p : ℕ} {mom : ℕ → ℝ → ℝ} {r : ℝ}
    (h1 : 0 < mom 1 r) (h2 : 0 < mom 2 r) : 0 < mixedMoment p mom r := by
  unfold mixedMoment
  exact mul_pos (mul_pos (dblFact_pos _) (Real.rpow_pos_of_pos (momentRatio_pos h1 h2) _)) h1

theorem drivingTerm_pos {p : ℕ} {α : ℝ} {mom : ℕ → ℝ → ℝ} {r : ℝ}
    (hp : 3 ≤ p) (hα : 0 < α) (h1 : 0 < mom 1 r) (h2 : 0 < mom 2 r) :
    0 < drivingTerm p α mom r := by
  rw [drivingTerm_eq_smul]
  have hp2 : 0 < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  exact mul_pos (mul_pos hα hp2) (mixedMoment_pos h1 h2)

/-- The index arithmetic of the induction step: the gap between the driving
index `(2p-1)α` and the linear index `(p+1)α` is exactly `(p-2)α`.  This is
why the constant `α(p-2)(2p-3)!!` of `drivingTerm` is exactly cancelled by
`1/(b-a)` in Lemma I.4.22. -/
theorem drivingIndex_sub_linearIndex (p : ℕ) (α : ℝ) :
    (2 * (p : ℝ) - 1) * α - ((p : ℝ) + 1) * α = ((p : ℝ) - 2) * α := by
  ring

theorem drivingIndex_pos {p : ℕ} {α : ℝ} (hp : 3 ≤ p) (hα : 0 < α) :
    0 < (2 * (p : ℝ) - 1) * α := by
  have : (0 : ℝ) < 2 * (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  exact mul_pos this hα

end PercLib.CriticalLRP.VolumeMoments.HigherMoments
