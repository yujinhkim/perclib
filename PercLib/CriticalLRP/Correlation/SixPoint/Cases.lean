/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The complete admissible range at `p = 5` in Lemma I.4.16, combining the
ordinary `k = 0` and mixed `k = 1` bounds.  No finite-moment premise is used.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.Assembly

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- Every admissible `k` at `p = 5` for a countable abelian group with a
fully translation-invariant opening profile. -/
theorem fifth_moment_all_k_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (k : ℕ) (hk : k ≤ 1) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ k *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ (9 - 3 * k) := by
  interval_cases k
  · simpa using fifth_moment_ordinary_le π hq
  · simpa using fifth_moment_le π hq

/-- Every admissible `k` at `p = 5` for the canonical power-law law. -/
theorem latticeLongRange_fifth_moment_all_k_le (d : ℕ) (α : ℝ) (β : NNReal)
    (k : ℕ) (hk : k ≤ 1) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 5
        ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 2
        ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ^ k *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))
          ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ^ (9 - 3 * k) := by
  have h := fifth_moment_all_k_le
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (PercLib.CriticalLRP.TreeExpansion.lrKernel_unitInterval_translation_of_pair d α β)
    k hk
  simpa only [PercLib.CriticalLRP.latticeLongRangeMeasure,
    PercLib.CriticalLRP.longRangeMeasure] using h

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_all_k_le
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.latticeLongRange_fifth_moment_all_k_le

end PercLib.CriticalLRP.TreeExpansion.SixPoint
