/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Sup-norm lattice-ball cardinality asymptotics

This module proves the normalized-volume asymptotic aspect of Lemma I.4.6 for
`latticeBallR`. Its exact sup-norm count is `(2 * floor r + 1)^d`, hence it is
asymptotic to `2^d * r^d`, not to bare `r^d`. The factor `2^d` is the Lebesgue
volume of the sup-norm unit ball. After dividing by this volume, the normalized
cardinality is asymptotic to `r^d`, exactly the normalization allowed by the
paper's Definition I.1.3.

Scope: this does not prove the arbitrary-norm statement or the sharper
`|B_r| = r^d ± O(r^(d-1))` remainder. Those remain separate obligations.
-/

module

public import PercLib.CriticalLRP.Tightness.LemmaI26Averaging

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal Asymptotics

namespace PercLib.CriticalLRP.Percolation

/-- The dominant linear term in the exact sup-norm lattice-ball cardinality. -/
theorem tendsto_two_mul_natFloor_add_one_div :
    Tendsto (fun r : ℝ => (2 * (⌊r⌋₊ : ℝ) + 1) / r) atTop (𝓝 2) := by
  have h := (tendsto_nat_floor_div_atTop (R := ℝ)).const_mul (2 : ℝ)
  have hsum := h.add (tendsto_inv_atTop_zero (𝕜 := ℝ))
  convert hsum using 1
  · funext r
    ring
  · norm_num

/-- Raw sup-norm lattice-ball cardinality, normalized only by `r^d`.
The limit is the volume `2^d` of the sup-norm unit ball. -/
theorem tendsto_card_supBall_div_pow (d : ℕ) :
    Tendsto (fun r : ℝ => (((2 * ⌊r⌋₊ + 1) ^ d : ℕ) : ℝ) / r ^ d)
      atTop (𝓝 ((2 : ℝ) ^ d)) := by
  have h := tendsto_two_mul_natFloor_add_one_div.pow d
  convert h using 1
  funext r
  push_cast
  exact (div_pow _ _ _).symm

/-- The cardinality of `latticeBallR`, normalized only by `r^d`. -/
theorem tendsto_latticeBallR_card_div_pow {d : ℕ} :
    Tendsto (fun r : ℝ => (latticeBallR (d := d) r 0).encard.toENNReal.toReal / r ^ d)
      atTop (𝓝 ((2 : ℝ) ^ d)) := by
  apply (tendsto_card_supBall_div_pow d).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  rw [card_latticeBallR hr, ENat.toENNReal_coe, ENNReal.toReal_natCast]


/-- Unit-ball-measure normalization for the exact sup-norm lattice count.
After dividing by the volume `2^d` of the sup-norm unit ball, the lattice
count has the source-normalized asymptotic `r^d`. -/
theorem tendsto_card_supBall_div_unitBallVolume_mul_pow (d : ℕ) :
    Tendsto (fun r : ℝ => (((2 * ⌊r⌋₊ + 1) ^ d : ℕ) : ℝ) /
        ((2 : ℝ) ^ d * r ^ d)) atTop (𝓝 1) := by
  have h := (tendsto_card_supBall_div_pow d).div_const ((2 : ℝ) ^ d)
  have hne : (2 : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  convert h using 1
  · funext r
    field_simp [hne]
  · rw [div_self hne]

/-- The source-normalized asymptotic cardinality of `latticeBallR`. -/
theorem tendsto_latticeBallR_card_div_unitBallVolume_mul_pow {d : ℕ} :
    Tendsto (fun r : ℝ => (latticeBallR (d := d) r 0).encard.toENNReal.toReal /
        ((2 : ℝ) ^ d * r ^ d)) atTop (𝓝 1) := by
  apply (tendsto_card_supBall_div_unitBallVolume_mul_pow d).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  rw [card_latticeBallR hr, ENat.toENNReal_coe, ENNReal.toReal_natCast]

/-- In asymptotic-equivalence notation, the raw sup-norm lattice-ball count is
`2^d * r^d`; the factor is the continuous unit-ball volume. -/
theorem isEquivalent_latticeBallR_unitBallVolume_mul_pow {d : ℕ} :
    (fun r : ℝ => (latticeBallR (d := d) r 0).encard.toENNReal.toReal) ~[atTop]
      (fun r => (2 : ℝ) ^ d * r ^ d) :=
  Asymptotics.isEquivalent_of_tendsto_one
    tendsto_latticeBallR_card_div_unitBallVolume_mul_pow

end PercLib.CriticalLRP.Percolation

#print axioms PercLib.CriticalLRP.Percolation.tendsto_two_mul_natFloor_add_one_div
#print axioms PercLib.CriticalLRP.Percolation.tendsto_card_supBall_div_pow
#print axioms PercLib.CriticalLRP.Percolation.tendsto_latticeBallR_card_div_pow

#print axioms PercLib.CriticalLRP.Percolation.tendsto_card_supBall_div_unitBallVolume_mul_pow
#print axioms PercLib.CriticalLRP.Percolation.tendsto_latticeBallR_card_div_unitBallVolume_mul_pow
#print axioms PercLib.CriticalLRP.Percolation.isEquivalent_latticeBallR_unitBallVolume_mul_pow
