/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m4/Assembly.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Eval

/-!
Analytic assembly of the `p = 5`, `k = 2` fifth-moment bound.  Ultramath `smwvk712v` member
`m4`, direction C.

This is the `k = 2` companion of the production consumers `fifth_moment_le_of_105diagrams`
(`k = 0`) and `fifth_moment_le` (`k = 1`): the fivefold moment identity `lintegral_cardFun_five_eq`,
the interchange of the five terminal sums with the `105`-fold shape sum, and the exact
evaluation of every two-hub slot diagram to `(E|K|^2)^2 (E|K|)^3` give

  `E|K|^5 ≤ 105 (E|K|^2)^2 (E|K|)^3`,

which is the intended Lemma I.4.16 bound at `p = 5`, `k = 2` (the largest admissible
`k`, since `⌈(p-1)/2⌉ = 2`). The remaining premise is the per-shape pointwise
five-point event bound `hpoint`: the candidate deterministic cover by `105`
two-hub shapes, together with the ninefold BK step. This premise is not
supplied. `Counterexample.Line6.hpoint_false` proves that it fails on the
non-transitive six-vertex line; that does not refute the paper's transitive
Lemma I.4.16. Neither conditional assembly below completes that source case
without a repaired event cover.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-! ## The index arithmetic -/

/-- `105 = 7!! = (2 * 5 - 3)!!`: the number of shapes at `p = 5`. -/
theorem seven_doubleFactorial : Nat.doubleFactorial 7 = 105 := by decide

/-! ## The abstract consumer -/

/-- **Conditional analytic consumer for `p = 5`, `k = 2`.**  A pointwise five-point event bound
by `105` diagrams, together with the exact evaluation of each diagram, gives the native fifth
moment bound with coefficient `105` and exponents `2` and `3`. -/
theorem fifth_moment_le_of_hubDiagrams [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (D : Fin 105 → V → V → V → V → V → ℝ≥0∞)
    (hpoint : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' s : Fin 105, D s y z w q r)
    (hsum : ∀ s : Fin 105,
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D s y z w q r)
        = secondMoment π 0 ^ 2 * (∑' x, tau π 0 x) ^ 3) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  have hmain :
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
        105 * (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    rw [lintegral_cardFun_five_eq π 0]
    calc ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
          law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r)
        ≤ ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s : Fin 105, D s y z w q r :=
          ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
            ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
              ENNReal.tsum_le_tsum fun r => hpoint y z w q r
      _ = ∑' s : Fin 105, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D s y z w q r :=
          tsum_fin_five_swap (F := fun y z w q r s => D s y z w q r)
      _ = ∑' _s : Fin 105, secondMoment π 0 ^ 2 * (∑' x, tau π 0 x) ^ 3 :=
          tsum_congr fun s => hsum s
      _ = 105 * (secondMoment π 0 ^ 2 * (∑' x, tau π 0 x) ^ 3) :=
          tsum_fin105_const _
      _ = 105 * (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by ring
  simpa only [secondMoment, firstMoment, ← firstMoment_eq] using hmain

/-! ## The diagram consumer -/

/-- **`p = 5`, `k = 2` from the pointwise two-hub event bound alone.**  Here the diagram family
is the explicit two-hub slot diagram `slotK2` with an arbitrary family of `105` leaf labellings;
the diagram evaluation is discharged by `tsum_slotK2_five`, so `hpoint` is the only premise. -/
theorem fifth_moment_mixed_k2_le_of_hubBound [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (pat : Fin 105 → Equiv.Perm (Fin 5))
    (hpoint : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' s : Fin 105, slotK2 π (pat s) 0 ![y, z, w, q, r]) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 :=
  fifth_moment_le_of_hubDiagrams π (fun s y z w q r => slotK2 π (pat s) 0 ![y, z, w, q, r])
    hpoint fun s => tsum_slotK2_five π hq (pat s) 0

/-- **`firstMoment` normaliser.**  The same statement with the susceptibility written as the
native first moment, for comparison with the `p = 4`, `k = 2` bound of
`fourth_moment_mixed_k2_le`. -/
theorem fifth_moment_le_of_hubDiagrams_firstMoment [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (D : Fin 105 → V → V → V → V → V → ℝ≥0∞)
    (hpoint : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' s : Fin 105, D s y z w q r)
    (hsum : ∀ s : Fin 105,
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D s y z w q r)
        = secondMoment π 0 ^ 2 * firstMoment π 0 ^ 3) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 :=
  fifth_moment_le_of_hubDiagrams π D hpoint fun s => by
    rw [hsum s, firstMoment_eq]

end PercLib.CriticalLRP.TreeExpansion.HubK2
