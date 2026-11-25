/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The native second moment is exactly the joint star-pair sum. This closes the cubic
mixed-moment target; no moment-finiteness assumption is made.
-/
module

public import PercLib.CriticalLRP.Correlation.CubicMixed.Basic

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

variable {V : Type*}

theorem joinSum_eq_cardFun_sq [Countable V] (π : Sym2 V → unitInterval) (o : V) :
    (∑' x, ∑' w, law π (conn o w ∩ conn x w)) =
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω o)) ^ 2 ∂(law π) := by
  rw [lintegral_cardFun_sq_eq π o]
  apply tsum_congr; intro x; apply tsum_congr; intro w
  apply congrArg
  ext ω
  constructor
  · rintro ⟨h₀w, hxw⟩
    have h₀x : PercLib.CriticalLRP.Connects ω o x :=
      PercLib.CriticalLRP.connects_trans h₀w (PercLib.CriticalLRP.connects_symm hxw)
    exact ⟨h₀x, h₀w⟩
  · rintro ⟨h₀x, h₀w⟩
    have hwo : ω ∈ conn w o := by rwa [conn_symm o w] at h₀w
    have hxw : ω ∈ conn w x := conn_trans (x := w) (y := o) (z := x) hwo h₀x
    rw [conn_symm w x] at hxw
    exact ⟨h₀w, hxw⟩

/-- Completing the cubic mixed-moment theorem using equality of the star-pair function and
native second cluster moment. -/
theorem third_moment_mixed_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω 0)) ^ 3 ∂(law π) ≤
      3 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω 0) ∂(law π)) ^ 2 *
        (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω 0)) ^ 2 ∂(law π)) := by
  rw [← joinSum_eq_cardFun_sq π 0]
  exact cubic_le_chi_sq_mul_joinSum π hinv

#print axioms PercLib.CriticalLRP.TreeExpansion.joinSum_eq_cardFun_sq
#print axioms PercLib.CriticalLRP.TreeExpansion.third_moment_mixed_le

end PercLib.CriticalLRP.TreeExpansion
