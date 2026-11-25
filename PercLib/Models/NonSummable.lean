/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 120 (Q-4, item 5), written on 2026-11-14 by PROVER-E. No upstream
proof is copied.
-/
module

public import PercLib.Models.TranslationInvariant
public import PercLib.Percolation.Bond.InfiniteDegree

/-!
# Non-summable translation-invariant kernels percolate at every positive intensity

On a countable additive group with `J s(x, y) = k (y - x)`, the off-diagonal row of `J` is
`∑'_{z ≠ 0} k z` at every vertex (`rowSum_eq_of_translationInvariant`). If that sum is
infinite, both critical intensities vanish, at every root. This file adds no definition.
-/

@[expose] public section

open scoped ENNReal NNReal
open Classical
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {G : Type*} [AddGroup G]

/-- **A non-summable translation-invariant kernel has root critical intensity zero at
every vertex.** -/
theorem rootCriticalIntensity_eq_zero_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x,y) = k (y - x))
    (hk : (∑' z, if z = 0 then 0 else (k z : ℝ≥0∞)) = ∞) (v : G) :
    rootCriticalIntensity J v = 0 :=
  rootCriticalIntensity_eq_zero_of_rowSum_eq_top J v
    (by rw [rowSum_eq_of_translationInvariant J k hJ v]; exact hk)

/-- **A non-summable translation-invariant kernel has global critical intensity zero.** -/
theorem globalCriticalIntensity_eq_zero_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x,y) = k (y - x))
    (hk : (∑' z, if z = 0 then 0 else (k z : ℝ≥0∞)) = ∞) :
    globalCriticalIntensity J = 0 :=
  globalCriticalIntensity_eq_zero_of_rowSum_eq_top J 0
    (by rw [rowSum_eq_of_translationInvariant J k hJ 0]; exact hk)

/-! ### Non-vacuity: the constant kernel on `ℤ`. -/

example (v : ℤ) : rootCriticalIntensity (fun _ : Sym2 ℤ => 1) v = 0 ∧
    globalCriticalIntensity (fun _ : Sym2 ℤ => 1) = 0 := by
  refine ⟨rootCriticalIntensity_eq_zero_of_translationInvariant _ (fun _ => 1)
      (fun _ _ => rfl) ?_ v,
    globalCriticalIntensity_eq_zero_of_translationInvariant _ (fun _ => 1)
      (fun _ _ => rfl) ?_⟩ <;>
  convert tsum_ite_const_eq_top (V := ℤ) (c := ((1 : ℝ≥0) : ℝ≥0∞)) 0 (by simp)

end PercLib.Models
