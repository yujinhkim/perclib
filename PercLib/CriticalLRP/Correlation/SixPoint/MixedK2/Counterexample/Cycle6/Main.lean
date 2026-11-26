/-
Main constants: the `p = 5`, `k = 2` two-hub slot bound fails for the translation-invariant
six-cycle profile at `1/64`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Cycle6.Reach

/-!
# The pointwise two-hub bound fails on `ZMod 6`

The tuple `(y, z, w, q, r) = (0, 3, 3, 3, 3)` has connection probability at least `eps ^ 3`,
while every two-hub slot diagram is at most `32 * eps ^ 6` per hub pair and hence at most
`105 * 1152 * eps ^ 6` in total.
-/

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Counterexample.Cycle6

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion.HubK2
open PercLib.CriticalLRP.TreeExpansion.FivePoint

/-! ## The diagram bound -/

theorem jointP_le (a b c : ZMod 6) :
    jointP (stepProfile theta) a b c ≤ 2 * eps ^ max (cdist a c) (cdist b c) := by
  rcases le_total (cdist a c) (cdist b c) with h | h
  · rw [Nat.max_eq_right h]
    refine (measure_mono (s := conn a c ∩ conn b c) (t := conn b c)
      Set.inter_subset_right).trans (tau_le b c)
  · rw [Nat.max_eq_left h]
    refine (measure_mono (s := conn a c ∩ conn b c) (t := conn a c)
      Set.inter_subset_left).trans (tau_le a c)

/-! ### The exponent count in the six slot cases -/

theorem exp_all3 (c1 c2 : ZMod 6) :
    6 ≤ max (cdist 3 c1) (cdist 3 c1) + cdist 0 c1 + max (cdist 3 c2) (cdist 3 c2)
      + cdist 0 c2 + cdist 3 c1 := by
  have k1 := cdist_zero_three c1
  have k2 := cdist_zero_three c2
  omega

theorem exp_a0 (c1 c2 : ZMod 6) :
    6 ≤ max (cdist 0 c1) (cdist 3 c1) + cdist 0 c1 + max (cdist 3 c2) (cdist 3 c2)
      + cdist 0 c2 + cdist 3 c1 := by
  have k1 := cdist_zero_three c1
  have k2 := cdist_zero_three c2
  omega

theorem exp_b0 (c1 c2 : ZMod 6) :
    6 ≤ max (cdist 3 c1) (cdist 0 c1) + cdist 0 c1 + max (cdist 3 c2) (cdist 3 c2)
      + cdist 0 c2 + cdist 3 c1 := by
  have k1 := cdist_zero_three c1
  have k2 := cdist_zero_three c2
  omega

theorem exp_d0 (c1 c2 : ZMod 6) :
    6 ≤ max (cdist 3 c1) (cdist 3 c1) + cdist 0 c1 + max (cdist 0 c2) (cdist 3 c2)
      + cdist 0 c2 + cdist 3 c1 := by
  have k1 := cdist_zero_three c1
  have k2 := cdist_zero_three c2
  have m2 : cdist 3 c2 ≤ max (cdist 0 c2) (cdist 3 c2) := Nat.le_max_right _ _
  omega

theorem exp_e0 (c1 c2 : ZMod 6) :
    6 ≤ max (cdist 3 c1) (cdist 3 c1) + cdist 0 c1 + max (cdist 3 c2) (cdist 0 c2)
      + cdist 0 c2 + cdist 3 c1 := by
  have k1 := cdist_zero_three c1
  have k2 := cdist_zero_three c2
  have m2 : cdist 3 c2 ≤ max (cdist 3 c2) (cdist 0 c2) := Nat.le_max_left _ _
  omega

theorem exp_f0 (c1 c2 : ZMod 6) :
    6 ≤ max (cdist 3 c1) (cdist 3 c1) + cdist 0 c1 + max (cdist 3 c2) (cdist 3 c2)
      + cdist 0 c2 + cdist 0 c1 := by
  have k1 := cdist_zero_three c1
  have k2 := cdist_zero_three c2
  omega

/-! ### The `hubStar` bound at a fixed exponent -/

theorem hubStar_le_of_exp {a b d e f c1 c2 : ZMod 6}
    (hE : 6 ≤ max (cdist a c1) (cdist b c1) + cdist 0 c1 + max (cdist d c2) (cdist e c2)
      + cdist 0 c2 + cdist f c1) :
    hubStar (stepProfile theta) 0 a b d e f c1 c2 ≤ 32 * eps ^ 6 := by
  have hpow : eps ^ (max (cdist a c1) (cdist b c1) + cdist 0 c1 + max (cdist d c2) (cdist e c2)
      + cdist 0 c2 + cdist f c1) ≤ eps ^ 6 :=
    pow_le_pow_right_of_le_one' eps_le_one hE
  have h1 : jointP (stepProfile theta) a b c1 ≤ 2 * eps ^ max (cdist a c1) (cdist b c1) :=
    jointP_le a b c1
  have h2 : tau (stepProfile theta) 0 c1 ≤ 2 * eps ^ cdist 0 c1 := tau_le 0 c1
  have h3 : jointP (stepProfile theta) d e c2 ≤ 2 * eps ^ max (cdist d c2) (cdist e c2) :=
    jointP_le d e c2
  have h4 : tau (stepProfile theta) 0 c2 ≤ 2 * eps ^ cdist 0 c2 := tau_le 0 c2
  have h5 : tau (stepProfile theta) f c1 ≤ 2 * eps ^ cdist f c1 := tau_le f c1
  calc hubStar (stepProfile theta) 0 a b d e f c1 c2
      ≤ ((2 * eps ^ max (cdist a c1) (cdist b c1) * (2 * eps ^ cdist 0 c1)) *
          ((2 * eps ^ max (cdist d c2) (cdist e c2)) * (2 * eps ^ cdist 0 c2))) *
          (2 * eps ^ cdist f c1) := by
        unfold hubStar
        gcongr
    _ = 32 * eps ^ (max (cdist a c1) (cdist b c1) + cdist 0 c1 + max (cdist d c2) (cdist e c2)
          + cdist 0 c2 + cdist f c1) := by
        rw [pow_add, pow_add, pow_add, pow_add]
        ring
    _ ≤ 32 * eps ^ 6 := mul_le_mul' le_rfl hpow

/-! ### The bound for one slot diagram -/

theorem leaves_eq_ite (i : Fin 5) : leaves i = if i = 0 then (0 : ZMod 6) else 3 :=
  leaves_eq i

theorem hubStar_le_slot (σ : Equiv.Perm (Fin 5)) (c1 c2 : ZMod 6) :
    hubStar (stepProfile theta) 0 (leaves (σ 0)) (leaves (σ 1)) (leaves (σ 2))
      (leaves (σ 3)) (leaves (σ 4)) c1 c2 ≤ 32 * eps ^ 6 := by
  obtain ⟨i, hi⟩ := σ.surjective 0
  have hval : ∀ j : Fin 5, leaves (σ j) = if j = i then 0 else 3 := by
    intro j
    rw [leaves_eq]
    by_cases hj : j = i
    · rw [ite_pos_eq (by rw [hj]; exact hi), ite_pos_eq hj]
    · rw [ite_neg_eq ?_, ite_neg_eq hj]
      intro hsj
      exact hj (σ.injective (by rw [hsj, hi]))
  rw [hval 0, hval 1, hval 2, hval 3, hval 4]
  fin_cases i
  · exact hubStar_le_of_exp (exp_a0 c1 c2)
  · exact hubStar_le_of_exp (exp_b0 c1 c2)
  · exact hubStar_le_of_exp (exp_d0 c1 c2)
  · exact hubStar_le_of_exp (exp_e0 c1 c2)
  · exact hubStar_le_of_exp (exp_f0 c1 c2)

theorem tsum_zmod6_const (x : ℝ≥0∞) : (∑' _c : ZMod 6, x) = 6 * x := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ZMod.card]
  simp

theorem slotK2_le (σ : Equiv.Perm (Fin 5)) :
    slotK2 (stepProfile theta) σ 0 leaves ≤ 1152 * eps ^ 6 := by
  unfold slotK2
  calc ∑' c1, ∑' c2, hubStar (stepProfile theta) 0 (leaves (σ 0)) (leaves (σ 1))
        (leaves (σ 2)) (leaves (σ 3)) (leaves (σ 4)) c1 c2
      ≤ ∑' _c1 : ZMod 6, ∑' _c2 : ZMod 6, (32 * eps ^ 6) :=
        ENNReal.tsum_le_tsum fun c1 => ENNReal.tsum_le_tsum fun c2 => hubStar_le_slot σ c1 c2
    _ = 1152 * eps ^ 6 := by
        rw [tsum_zmod6_const, tsum_zmod6_const]
        ring

/-! ## The numerical comparison -/

theorem num_lt_nn : (105 : ℝ≥0) * (1152 * (1 / 64 : ℝ≥0) ^ 6) < (1 / 64 : ℝ≥0) ^ 3 := by
  rw [← NNReal.coe_lt_coe]
  push_cast
  norm_num

theorem num_lt : (105 : ℝ≥0∞) * (1152 * eps ^ 6) < eps ^ 3 := by
  have h1 : (105 : ℝ≥0∞) = ((105 : ℝ≥0) : ℝ≥0∞) := by norm_num
  have h2 : (1152 : ℝ≥0∞) = ((1152 : ℝ≥0) : ℝ≥0∞) := by norm_num
  rw [h1, h2, eps_eq, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul,
    ← ENNReal.coe_mul, ENNReal.coe_lt_coe]
  exact num_lt_nn

/-! ## The refutation -/

/-- `eps ^ 3` is at most the probability that `0` and `3` are connected. -/
theorem law_conn_three_ge :
    eps ^ 3 ≤ law (stepProfile theta)
      (conn (0 : ZMod 6) 0 ∩ conn 0 3 ∩ conn 0 3 ∩ conn 0 3 ∩ conn 0 3) := by
  rw [conn_self, Set.univ_inter, Set.inter_self, Set.inter_self, Set.inter_self]
  exact eps_cube_le_law_conn_three

theorem tsum_slotK2_le (pat : Fin 105 → Equiv.Perm (Fin 5)) :
    (∑' s : Fin 105, slotK2 (stepProfile theta) (pat s) 0 (![0, 3, 3, 3, 3] : Fin 5 → ZMod 6))
      ≤ 105 * (1152 * eps ^ 6) := by
  calc (∑' s : Fin 105, slotK2 (stepProfile theta) (pat s) 0 (![0, 3, 3, 3, 3] : Fin 5 → ZMod 6))
      ≤ ∑' _s : Fin 105, (1152 * eps ^ 6) := ENNReal.tsum_le_tsum fun s => slotK2_le (pat s)
    _ = 105 * (1152 * eps ^ 6) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp

/-- **The pointwise two-hub bound fails at the explicit tuple** `(0, 3, 3, 3, 3)`. -/
theorem hpoint_fails_at (pat : Fin 105 → Equiv.Perm (Fin 5)) :
    (∑' s : Fin 105,
      slotK2 (stepProfile theta) (pat s) 0 (![0, 3, 3, 3, 3] : Fin 5 → ZMod 6)) <
      law (stepProfile theta)
        (conn (0 : ZMod 6) 0 ∩ conn 0 3 ∩ conn 0 3 ∩ conn 0 3 ∩ conn 0 3) :=
  lt_of_le_of_lt (tsum_slotK2_le pat) (lt_of_lt_of_le num_lt law_conn_three_ge)

/-- **The pointwise two-hub premise is false.**  For every family of `105` slot labellings, the
pointwise bound of `fifth_moment_mixed_k2_le_of_hubBound` fails at `(0, 3, 3, 3, 3)` for the
translation-invariant profile `stepProfile theta` on `ZMod 6` with `theta = 1/64`. -/
theorem hpoint_false (pat : Fin 105 → Equiv.Perm (Fin 5)) :
    ¬ (∀ y z w q r : ZMod 6,
      law (stepProfile theta) (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' s : Fin 105, slotK2 (stepProfile theta) (pat s) 0 ![y, z, w, q, r]) := by
  intro h
  exact absurd (h 0 3 3 3 3) (not_le.2 (hpoint_fails_at pat))

/-- **The hypothesis bundle of the production consumer is unsatisfiable at this profile.**  The
translation invariance `hq` holds, but `hpoint` fails, so
`fifth_moment_mixed_k2_le_of_hubBound` cannot be applied non-vacuously at `stepProfile theta`. -/
theorem hubBound_bundle_false (pat : Fin 105 → Equiv.Perm (Fin 5)) :
    ¬ ((∀ x y g : ZMod 6, stepProfile theta s(x + g, y + g) = stepProfile theta s(x, y)) ∧
      (∀ y z w q r : ZMod 6,
        law (stepProfile theta) (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
          ∑' s : Fin 105, slotK2 (stepProfile theta) (pat s) 0 ![y, z, w, q, r])) :=
  fun h => hpoint_false pat h.2

/-- **Translation invariance of the profile.**  This is the `hq` hypothesis of
`fifth_moment_mixed_k2_le_of_hubBound` at the six-cycle profile. -/
theorem hq_stepProfile (x y g : ZMod 6) :
    stepProfile theta s(x + g, y + g) = stepProfile theta s(x, y) := by
  rw [stepProfile_mk, stepProfile_mk, stepFun, stepFun]
  have e1 : (y + g) - (x + g) = y - x := by abel
  have e2 : (x + g) - (y + g) = x - y := by abel
  rw [e1, e2]

end PercLib.CriticalLRP.Counterexample.Cycle6
