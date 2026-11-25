/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m4/Norm.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Chain

/-!
Normaliser audit for the `p = 5`, `k = 2` layer.

The `k = 2` evaluation is proved twice: once with the susceptibility written as the raw sum
`∑' x, tau 0 x` (the form the centre sums produce), and once with the native first moment
`firstMoment π 0` and the native second moment `secondMoment π 0` (the forms that occur in
`E|K|^2` and `E|K|`).  The identifications are recorded here so that the two normalisations
cannot drift apart:

* `secondMoment π o` *is* `∫⁻ ω, |K_o|^2 ∂ law π` (by definition), and
* `firstMoment π o` *is* `∫⁻ ω, |K_o| ∂ law π` (by definition) and `∑' y, tau π o y`
  (`firstMoment_eq`),
* `secondMoment π o = ∑' a, ∑' b, jointP π a b o` (`secondMoment_eq`).
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- The native second moment is the integral of the squared cluster size. -/
theorem secondMoment_eq_lintegral (π : Sym2 V → unitInterval) (o : V) :
    secondMoment π o =
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω o)) ^ 2 ∂(law π) := rfl

/-- The native first moment is the integral of the cluster size. -/
theorem firstMoment_eq_lintegral (π : Sym2 V → unitInterval) (o : V) :
    firstMoment π o =
      ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω o) ∂(law π) := rfl

/-- **Fan evaluation in the native normalisers.** -/
theorem tsum_slotK2_native [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 5)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, slotK2 π σ o ![y, z, w, q, r])
      = secondMoment π o ^ 2 * firstMoment π o ^ 3 := by
  rw [tsum_slotK2_five π hq σ o, firstMoment_eq]

/-- **Chain evaluation in the native normalisers.** -/
theorem tsum_slotChain_native [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 5)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, slotChain π σ o ![y, z, w, q, r])
      = secondMoment π o ^ 2 * firstMoment π o ^ 3 := by
  rw [tsum_slotChain_five π hq σ o, firstMoment_eq]

end PercLib.CriticalLRP.TreeExpansion.HubK2
