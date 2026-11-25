/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Complete admissible-`k` formulations of Lemma I.4.16 for `p = 3` and `p = 4`.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Final

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **All admissible `k` at `p = 3`.** The two cases `k = 0,1` are the ordinary and mixed
third-moment bounds, with `(2 * 3 - 1 - 3k) = 5 - 3k`. -/
theorem third_moment_all_k_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a)) (k : ℕ) (hk : k ≤ 1) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 3
        ∂(law π) ≤
      3 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ k *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ (5 - 3 * k) := by
  interval_cases k
  · simpa using PercLib.CriticalLRP.TreeExpansion.Native.third_moment_native π hinv
  · convert PercLib.CriticalLRP.TreeExpansion.third_moment_mixed_le π hinv using 1
    ring

/-- **All admissible `k` at `p = 4`.** Full profile invariance supplies both the ordinary and
mixed cases; `secondMoment_root_independent` needed at `k = 2` is discharged in `MixedK2`. -/
theorem fourth_moment_all_k_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : ℕ) (hk : k ≤ 2) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 4
        ∂(law π) ≤
      15 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ k *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ (7 - 3 * k) := by
  interval_cases k
  · simpa using fourth_moment_le π (tau_hinv π hq)
  · simpa using fourth_moment_mixed_le π (tau_hinv π hq)
  · simpa using fourth_moment_mixed_k2_le π hq

#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.third_moment_all_k_le
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.fourth_moment_all_k_le

end PercLib.CriticalLRP.TreeExpansion.FivePoint
