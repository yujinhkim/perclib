/-
Accepted from Ultramath `smwzg77c3`, member `m7`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d6`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The window cost of the two diagonal repairs

`Main.lean` shows that the uniform per-vertex two-term estimate of Lemma I.4.17 at `p = 3`,
`q = 0` cannot hold at the basepoint, and `Defs.lean` records two corrected readings:
`StarTwoTermBoundFar` (exclude a spatial ball) and `StarTwoTermBoundAdd` (add the term
`C5 * T(0,y) * chi^5`).

This file prices both repairs at the level of the Case-3 window sum.  The hypotheses are exactly
what the window sum consumes:

* `sum_{y in s} T^3(0,y) <= a` — the `l = 3` polygon budget (the source's `nabla_r <= nabla`),
* `T^4(0,y) <= b` per vertex and `0 <= b` — the `l = 4` polygon budget,
* `sum_{y in s} T(0,y) <= chi` (additive form only) — the column sum, i.e. the first moment.

* `sum_le_twoTerm_add`: the additive repair keeps the two source terms and replaces the extra term
  by `C5 * chi * chi^5`, i.e. `C5 * chi^2 / |B_r|` in the Case-3 error.
* `sum_le_twoTerm_far`: the far-region repair keeps the two source terms and adds
  `|s \ sfar| * chi3`, the near count times the trivial per-vertex bound
  (`SourceModelData.connCubeVertexMass_le_cutMoment_three`, `chi3 = (M.cutMoment 3 r).toReal`).

Everything is real arithmetic: no `RR>=0` subtraction and no `top`-to-`0` conversion occurs.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepair.Defs

/-! # Window assembly for the two repairs -/

noncomputable section

open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.Smwzg77c3.M7

/-- **Window cost of the additive repair.**  If the per-vertex estimate holds with the extra term
`C5 * T1 y * chi^5`, and the window sums of `T^3`, `T^4` and `T1` are controlled by `a`, `b` and
`chi`, then the window sum of `F` is bounded by the two source terms plus `C5 * chi * chi^5`. -/
theorem sum_le_twoTerm_add {ι : Type*} (s : Finset ι) (F T1 T3 T4 : ι → ℝ)
    {χ C3 C4 C5 a b : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hC5 : 0 ≤ C5) (hχ : 0 ≤ χ)
    (h : ∀ y ∈ s, F y ≤ C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3 + C5 * T1 y * χ ^ 5)
    (h3 : ∑ y ∈ s, T3 y ≤ a) (h4 : ∀ y ∈ s, T4 y ≤ b) (h1 : ∑ y ∈ s, T1 y ≤ χ) :
    ∑ y ∈ s, F y
      ≤ C3 * a * χ ^ 4 + (s.card : ℝ) * C4 * b * χ ^ 3 + C5 * χ * χ ^ 5 := by
  have hχ3 : (0 : ℝ) ≤ χ ^ 3 := pow_nonneg hχ 3
  have hχ4 : (0 : ℝ) ≤ χ ^ 4 := pow_nonneg hχ 4
  have hχ5 : (0 : ℝ) ≤ χ ^ 5 := pow_nonneg hχ 5
  have e1 : ∑ y ∈ s, C5 * T1 y * χ ^ 5 = C5 * (∑ y ∈ s, T1 y) * χ ^ 5 := by
    rw [← Finset.sum_mul, Finset.mul_sum]
  have e3 : ∑ y ∈ s, C3 * T3 y * χ ^ 4 = C3 * (∑ y ∈ s, T3 y) * χ ^ 4 := by
    rw [← Finset.sum_mul, Finset.mul_sum]
  have e4 : ∑ y ∈ s, C4 * T4 y * χ ^ 3 = C4 * (∑ y ∈ s, T4 y) * χ ^ 3 := by
    rw [← Finset.sum_mul, Finset.mul_sum]
  have h4sum : ∑ y ∈ s, T4 y ≤ (s.card : ℝ) * b := by
    calc ∑ y ∈ s, T4 y ≤ ∑ _y ∈ s, b := Finset.sum_le_sum h4
      _ = (s.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ y ∈ s, F y
      ≤ ∑ y ∈ s, (C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3 + C5 * T1 y * χ ^ 5) :=
        Finset.sum_le_sum h
    _ = (∑ y ∈ s, C3 * T3 y * χ ^ 4) + (∑ y ∈ s, C4 * T4 y * χ ^ 3)
          + (∑ y ∈ s, C5 * T1 y * χ ^ 5) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = C3 * (∑ y ∈ s, T3 y) * χ ^ 4 + C4 * (∑ y ∈ s, T4 y) * χ ^ 3
          + C5 * (∑ y ∈ s, T1 y) * χ ^ 5 := by
        rw [e3, e4, e1]
    _ ≤ C3 * a * χ ^ 4 + C4 * ((s.card : ℝ) * b) * χ ^ 3 + C5 * χ * χ ^ 5 := by
        have i3 : C3 * (∑ y ∈ s, T3 y) * χ ^ 4 ≤ C3 * a * χ ^ 4 := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC3) hχ4
          linarith
        have i4 : C4 * (∑ y ∈ s, T4 y) * χ ^ 3 ≤ C4 * ((s.card : ℝ) * b) * χ ^ 3 := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4sum hC4) hχ3
          linarith
        have i1 : C5 * (∑ y ∈ s, T1 y) * χ ^ 5 ≤ C5 * χ * χ ^ 5 := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC5) hχ5
          linarith
        linarith
    _ = C3 * a * χ ^ 4 + (s.card : ℝ) * C4 * b * χ ^ 3 + C5 * χ * χ ^ 5 := by ring

/-- **Window cost of the far-region repair.**  If the two-term estimate holds off a vertex region
`sfar` and the near part `s \ sfar` only carries the trivial bound `chi3`, then the window sum is
the two source terms plus `|s \ sfar| * chi3`.  This is the per-vertex `hgap` analogue of the
landed near/far budget for the `l = 3` polygon factor
(`SecondMomentCase3.sum_perVertex_le_nearFar`); in the model the near bound is
`SourceModelData.connCubeVertexMass_le_cutMoment_three` with `chi3 = (M.cutMoment 3 r).toReal`. -/
theorem sum_le_twoTerm_far {ι : Type*} [DecidableEq ι] (s sfar : Finset ι) (hs : sfar ⊆ s)
    (F T3 T4 : ι → ℝ) {χ C3 C4 a b chi3 : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hχ : 0 ≤ χ) (hb : 0 ≤ b)
    (hfar : ∀ y ∈ sfar, F y ≤ C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3)
    (hnear : ∀ y ∈ s \ sfar, F y ≤ chi3)
    (hT3nn : ∀ y ∈ s, 0 ≤ T3 y)
    (h3 : ∑ y ∈ s, T3 y ≤ a) (h4 : ∀ y ∈ s, T4 y ≤ b) :
    ∑ y ∈ s, F y
      ≤ C3 * a * χ ^ 4 + (s.card : ℝ) * C4 * b * χ ^ 3 + ((s \ sfar).card : ℝ) * chi3 := by
  have hχ3 : (0 : ℝ) ≤ χ ^ 3 := pow_nonneg hχ 3
  have hχ4 : (0 : ℝ) ≤ χ ^ 4 := pow_nonneg hχ 4
  have hsplit : ∑ y ∈ s, F y = ∑ y ∈ sfar, F y + ∑ y ∈ s \ sfar, F y := by
    rw [← Finset.sum_sdiff hs, add_comm]
  have e3 : ∑ y ∈ sfar, C3 * T3 y * χ ^ 4 = C3 * (∑ y ∈ sfar, T3 y) * χ ^ 4 := by
    rw [← Finset.sum_mul, Finset.mul_sum]
  have e4 : ∑ y ∈ sfar, C4 * T4 y * χ ^ 3 = C4 * (∑ y ∈ sfar, T4 y) * χ ^ 3 := by
    rw [← Finset.sum_mul, Finset.mul_sum]
  have hfar' : ∑ y ∈ sfar, F y ≤ C3 * (∑ y ∈ sfar, T3 y) * χ ^ 4
      + C4 * (∑ y ∈ sfar, T4 y) * χ ^ 3 := by
    calc ∑ y ∈ sfar, F y
        ≤ ∑ y ∈ sfar, (C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3) := Finset.sum_le_sum hfar
      _ = (∑ y ∈ sfar, C3 * T3 y * χ ^ 4) + (∑ y ∈ sfar, C4 * T4 y * χ ^ 3) :=
          Finset.sum_add_distrib
      _ = C3 * (∑ y ∈ sfar, T3 y) * χ ^ 4 + C4 * (∑ y ∈ sfar, T4 y) * χ ^ 3 := by
          rw [e3, e4]
  have h3' : ∑ y ∈ sfar, T3 y ≤ a := by
    have hle : ∑ y ∈ sfar, T3 y ≤ ∑ y ∈ s, T3 y :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => hT3nn _ ‹_›)
    linarith
  have h4' : ∑ y ∈ sfar, T4 y ≤ (s.card : ℝ) * b := by
    have hsum : ∑ y ∈ sfar, T4 y ≤ (sfar.card : ℝ) * b := by
      calc ∑ y ∈ sfar, T4 y ≤ ∑ _y ∈ sfar, b := Finset.sum_le_sum (fun y hy => h4 y (hs hy))
        _ = (sfar.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (sfar.card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hs
    calc ∑ y ∈ sfar, T4 y ≤ (sfar.card : ℝ) * b := hsum
      _ ≤ (s.card : ℝ) * b := mul_le_mul_of_nonneg_right hcard hb
  have hnear' : ∑ y ∈ s \ sfar, F y ≤ ((s \ sfar).card : ℝ) * chi3 := by
    calc ∑ y ∈ s \ sfar, F y ≤ ∑ _y ∈ s \ sfar, chi3 := Finset.sum_le_sum hnear
      _ = ((s \ sfar).card : ℝ) * chi3 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hy3 : C3 * (∑ y ∈ sfar, T3 y) * χ ^ 4 ≤ C3 * a * χ ^ 4 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3' hC3) hχ4
    linarith
  have hy4 : C4 * (∑ y ∈ sfar, T4 y) * χ ^ 3 ≤ C4 * ((s.card : ℝ) * b) * χ ^ 3 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4' hC4) hχ3
    linarith
  have hmid : C3 * (∑ y ∈ sfar, T3 y) * χ ^ 4 + C4 * (∑ y ∈ sfar, T4 y) * χ ^ 3
      ≤ C3 * a * χ ^ 4 + C4 * ((s.card : ℝ) * b) * χ ^ 3 := by linarith
  have hfin : C3 * a * χ ^ 4 + C4 * ((s.card : ℝ) * b) * χ ^ 3 + ((s \ sfar).card : ℝ) * chi3
      = C3 * a * χ ^ 4 + (s.card : ℝ) * C4 * b * χ ^ 3
        + ((s \ sfar).card : ℝ) * chi3 := by ring
  rw [hsplit]
  linarith [hfar', hnear', hmid, hfin]

end PercLib.CriticalLRP.Smwzg77c3.M7

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.sum_le_twoTerm_add
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.sum_le_twoTerm_far
