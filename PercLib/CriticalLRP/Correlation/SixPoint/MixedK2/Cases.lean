/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m4/Cases.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Assembly
public import PercLib.CriticalLRP.Correlation.SixPoint.Cases

/-!
The complete admissible `k`-range at `p = 5`, modulo the pointwise two-hub event bound.
Ultramath `smwvk712v` member `m4`, direction C.

Lemma I.4.16 at `p = 5` allows `0 ≤ k ≤ ⌈(p-1)/2⌉ = 2`.  The production tree already holds
`k = 0` (`fifth_moment_ordinary_le`) and `k = 1` (`fifth_moment_le`); the new `k = 2` bound of
`Assembly.lean` supplies the third.  Everything below is unconditional in `k` except the
single per-shape pointwise five-point event bound `hpoint` for the `k = 2` case, which is the
deterministic cover plus the regrouped BK step.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **Every admissible `k` at `p = 5`.**  Given the pointwise two-hub event bound, all of
`k = 0, 1, 2` hold for a countable abelian group with a fully translation-invariant profile. -/
theorem fifth_moment_all_k_le_of_hubBound [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (pat : Fin 105 → Equiv.Perm (Fin 5))
    (hpoint : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' s : Fin 105, slotK2 π (pat s) 0 ![y, z, w, q, r])
    (k : ℕ) (hk : k ≤ 2) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ k *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ (9 - 3 * k) := by
  interval_cases k
  · simpa using PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le π hq
  · simpa using PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_le π hq
  · simpa using fifth_moment_mixed_k2_le_of_hubBound π hq pat hpoint

/-- **Every admissible `k` at `p = 5` at the canonical power-law law**, modulo the two-hub
pointwise event bound read at the canonical profile. -/
theorem latticeLongRange_fifth_moment_all_k_le_of_hubBound (d : ℕ) (α : ℝ) (β : NNReal)
    (pat : Fin 105 → Equiv.Perm (Fin 5))
    (hpoint : ∀ y z w q r : Fin d → ℤ,
      law (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
        (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' s : Fin 105,
          slotK2 (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) (pat s) 0
            ![y, z, w, q, r])
    (k : ℕ) (hk : k ≤ 2) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 5
        ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 2
        ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ^ k *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))
          ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ^ (9 - 3 * k) := by
  have h := fifth_moment_all_k_le_of_hubBound
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (PercLib.CriticalLRP.TreeExpansion.lrKernel_unitInterval_translation_of_pair d α β)
    pat hpoint k hk
  simpa only [PercLib.CriticalLRP.latticeLongRangeMeasure,
    PercLib.CriticalLRP.longRangeMeasure] using h

end PercLib.CriticalLRP.TreeExpansion.HubK2
