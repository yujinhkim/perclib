module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.Basic

/-!
# Generic convolution assembly (`a + b < d`): radial profile freezing
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

/-! ## §2 Halving the radius at most doubles the logarithmic profile -/

/-- `Λ A ≤ 2 Λ (A/2)`: halving the radius at most halves the logarithmic profile. -/
lemma LamR_halve {A : ℝ} (hA : 0 ≤ A) : LamR A ≤ 2 * LamR (A / 2) := by
  have h := LamR_le_two_of_le_two_mul (n := A) (m := A / 2) hA (by linarith)
  linarith

/-- Freezing the log power at half the radius costs a factor `2^c`. -/
lemma LamR_rpow_halve_le {c A : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) :
    LamR (A / 2) ^ (-c) ≤ (2 : ℝ) ^ c * LamR A ^ (-c) := by
  have hA2 : (0 : ℝ) ≤ A / 2 := by linarith
  have hposA : 0 < LamR (A / 2) := LamR_pos hA2
  have hposA' : 0 < LamR A := LamR_pos hA
  have h2 : LamR A ≤ 2 * LamR (A / 2) := LamR_halve hA
  have h2' : (2 * LamR (A / 2)) ^ (-c) ≤ LamR A ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) h2 (by linarith)
  have hexp : (2 * LamR (A / 2)) ^ (-c) = (2 : ℝ) ^ (-c) * LamR (A / 2) ^ (-c) :=
    Real.mul_rpow (by norm_num) hposA.le
  rw [hexp] at h2'
  have hp : (0 : ℝ) < (2 : ℝ) ^ c := Real.rpow_pos_of_pos (by norm_num) _
  have hm := mul_le_mul_of_nonneg_left h2' hp.le
  have he : (2 : ℝ) ^ c * (2 : ℝ) ^ (-c) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  rw [← mul_assoc, he, one_mul] at hm
  exact hm

/-- Freezing the whole log factor at half the radius. -/
lemma LamR_rpow_freeze {c A v : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hv : A / 2 ≤ v) :
    LamR v ^ (-c) ≤ (2 : ℝ) ^ c * LamR A ^ (-c) := by
  have hA2 : (0 : ℝ) ≤ A / 2 := by linarith
  have hv0 : (0 : ℝ) ≤ v := le_trans hA2 hv
  refine (Real.rpow_le_rpow_of_nonpos (LamR_pos hA2) (LamR_mono hA2 hv) (by linarith)).trans ?_
  exact LamR_rpow_halve_le hc hA

/-! ## §3 Halving the radius in the power profile -/

/-- For a nonpositive exponent, halving the base costs a factor `2^(-e)`. -/
lemma one_add_halve_rpow_le {e A : ℝ} (he : e ≤ 0) (hA : 0 ≤ A) :
    (1 + A / 2) ^ e ≤ (2 : ℝ) ^ (-e) * (1 + A) ^ e := by
  have h1 : (1 + A / 2) ^ e ≤ ((1 + A) / 2) ^ e := by
    refine Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < (1 + A) / 2) ?_ he
    linarith
  have h2 : ((1 + A) / 2) ^ e = (2 : ℝ) ^ (-e) * (1 + A) ^ e := by
    rw [Real.div_rpow (by linarith) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
    ring
  linarith [h1, h2]

/-- The same with a nonnegative exponent, without a constant. -/
lemma one_add_halve_rpow_le' {e A : ℝ} (he : 0 ≤ e) (hA : 0 ≤ A) :
    (1 + A / 2) ^ e ≤ (1 + A) ^ e :=
  Real.rpow_le_rpow (by linarith) (by linarith) he

/-- Freezing the power factor at half the radius. -/
lemma one_add_rpow_freeze {e A v : ℝ} (he : e ≤ 0) (hA : 0 ≤ A) (hv : A / 2 ≤ v) :
    (1 + v) ^ e ≤ (2 : ℝ) ^ (-e) * (1 + A) ^ e := by
  have hA2 : (0 : ℝ) ≤ A / 2 := by linarith
  refine (Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < 1 + A / 2) (by linarith) he).trans ?_
  exact one_add_halve_rpow_le he hA

/-! ## §4 Combined `Wt` freezing -/

/-- **Freezing both factors of `Wt e c` at half the radius `A/2`.**  For `e ≥ 0`, `c ≥ 0` and
`v ≥ A/2 ≥ 0`, `Wt e c v ≤ 2^(e+c) ⟨A⟩^{-e} Λ(A)^{-c}`. -/
lemma Wt_freeze_halve {e c A v : ℝ} (he : 0 ≤ e) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hv : A / 2 ≤ v) :
    Wt e c v ≤ (2 : ℝ) ^ (e + c) * ((1 + A) ^ (-e) * LamR A ^ (-c)) := by
  have hv0 : (0 : ℝ) ≤ v := le_trans (by linarith : (0 : ℝ) ≤ A / 2) hv
  have hp : (1 + v) ^ (-e) ≤ (2 : ℝ) ^ e * (1 + A) ^ (-e) := by
    have h := one_add_rpow_freeze (e := -e) (by linarith : -e ≤ 0) hA hv
    simpa using h
  have hl := LamR_rpow_freeze hc hA hv
  have hc0 : (0 : ℝ) ≤ LamR v ^ (-c) := Real.rpow_nonneg (LamR_nonneg hv0) _
  have hb0 : (0 : ℝ) ≤ (2 : ℝ) ^ e * (1 + A) ^ (-e) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _)
  calc Wt e c v = (1 + v) ^ (-e) * LamR v ^ (-c) := rfl
    _ ≤ ((2 : ℝ) ^ e * (1 + A) ^ (-e)) * ((2 : ℝ) ^ c * LamR A ^ (-c)) :=
        mul_le_mul hp hl hc0 hb0
    _ = ((2 : ℝ) ^ e * (2 : ℝ) ^ c) * ((1 + A) ^ (-e) * LamR A ^ (-c)) := by ring
    _ = (2 : ℝ) ^ (e + c) * ((1 + A) ^ (-e) * LamR A ^ (-c)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- Freezing only the log power of the ball profile at half the radius. -/
lemma ball_profile_halve {a c A : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    (1 + A / 2) ^ a * LamR (A / 2) ^ (-c) ≤
      (2 : ℝ) ^ c * ((1 + A) ^ a * LamR A ^ (-c)) := by
  have hA2 : (0 : ℝ) ≤ A / 2 := by linarith
  have hp := one_add_halve_rpow_le' ha hA
  have hl := LamR_rpow_halve_le hc hA
  have hp0 : (0 : ℝ) ≤ (1 + A) ^ a := Real.rpow_nonneg (by linarith) _
  have hl0 : (0 : ℝ) ≤ LamR (A / 2) ^ (-c) := Real.rpow_nonneg (LamR_nonneg hA2) _
  calc (1 + A / 2) ^ a * LamR (A / 2) ^ (-c)
      ≤ (1 + A) ^ a * ((2 : ℝ) ^ c * LamR A ^ (-c)) := mul_le_mul hp hl hl0 hp0
    _ = (2 : ℝ) ^ c * ((1 + A) ^ a * LamR A ^ (-c)) := by ring

end CriticalLRPConv
