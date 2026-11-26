/- Independently rebuilt from `smwx3hvzx`, member `m1` finding f1.
Production integration revision: `c491c66109f24f38fa27cbccbcc52d11a14a8c33`.

Summation of the hub evaluation over the actual hub position, with translation invariance.

Source: Lemma I.4.16 of T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, p. 44, the last equality of

  `3 sum_{x,y,z,w} P(0 <-> x, w) P(w <-> y) P(w <-> z) = 3 E|K|^2 (E|K|)^2`,

i.e. the sums over the free pair point `x` and the hub position `w` produce the *second* cluster
moment, and the two remaining sums over `y` and `z` produce the square of the first moment.

## Content

* `firstMoment_eq_chi` -- the project's `firstMoment` (integral of `cardFun`) is `chi`.
* `tau_row_sum` -- the row sum of the two-point function at any vertex is the first moment
  (translation invariance of `tau`, `tsum_row_eq`).
* `hubPairSum_eq_secondMoment` -- **the hub sum**: summing the three-point function `jointP o x w`
  over the hub position `w` (outer) and the free point `x` gives the native second cluster
  moment at the origin.  This is `tsum_jointP_centre` written with the hub outermost; the hub is
  not summed "for free": translation invariance of the edge law is used, and the origin `o` stays
  pinned inside the three-point function.
* `hubSplitSum_eq`, `hubSplitSum_eq_pow` -- the full hub evaluation sum equals
  `secondMoment * firstMoment * firstMoment`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Evaluation.SourceDiag

/-!
# Hub summation
-/

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond (tau law)
open PercLib.CriticalLRP.TreeExpansion.FivePoint (jointP secondMoment firstMoment)

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace HubJointEval

variable {V : Type*}

/-- The project's `firstMoment` (integral of the cardinality of the cluster) is the
susceptibility `chi`. -/
theorem firstMoment_eq_chi [Countable V] (π : Sym2 V → unitInterval) (v : V) :
    firstMoment π v = PercLib.Percolation.Bond.chi π v := by
  rw [firstMoment, PercLib.Percolation.Bond.chi]
  exact lintegral_congr fun ω => PercLib.CriticalLRP.Percolation.cardFun_eq_encard _

/-- **The row sum of the two-point function is the first moment.**  Translation invariance of
`tau` moves the row `w` to the origin's row, and the latter sums to `chi` (Tonelli). -/
theorem tau_row_sum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (w : V) :
    (∑' y, tau π w y) = firstMoment π 0 := by
  rw [firstMoment_eq_chi, PercLib.Percolation.Bond.chi_eq_tsum_tau]
  exact PercLib.CriticalLRP.TreeExpansion.tsum_row_eq (tau π) 0
    (PercLib.CriticalLRP.TreeExpansion.FivePoint.tau_hinv π hq) w

/-- **The hub sum is the second moment.**  Summing the three-point function `jointP π o x w` over
the hub position `w` (outer sum) and the free point `x` gives the native second cluster moment at
the origin `o`.

The origin stays *inside* the three-point function: this is the source's `E|K|^2` slot, and the
identity is the translation-invariance identity `tsum_jointP_centre`, not a factorisation into
two two-point functions. -/
theorem hubPairSum_eq_secondMoment [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    hubPairSum π o = secondMoment π o := by
  rw [PercLib.CriticalLRP.TreeExpansion.FivePoint.secondMoment_root_independent π hq o]
  exact PercLib.CriticalLRP.TreeExpansion.FivePoint.tsum_jointP_centre π hq o

/-- The two leaf sums of one hub block collapse to the square of the first moment, leaving the
joint pair sum untouched. -/
theorem hubBlock_factor [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o w : V) :
    (∑' x, ∑' y, ∑' z, hubSplitValue π o x y z w)
      = (∑' x, jointP π o x w) * (firstMoment π 0 * firstMoment π 0) := by
  have hfz : ∀ (x : V) (y : V),
      (∑' z, hubSplitValue π o x y z w)
        = (jointP π o x w * tau π w y) * firstMoment π 0 := by
    intro x y
    simp only [hubSplitValue]
    rw [show (∑' z, jointP π o x w * (tau π w y * tau π w z))
        = ∑' z, (jointP π o x w * tau π w y) * tau π w z from
      tsum_congr fun z => (mul_assoc _ _ _).symm]
    rw [ENNReal.tsum_mul_left, tau_row_sum π hq w]
  have hfy : ∀ x : V,
      (∑' y, ∑' z, hubSplitValue π o x y z w)
        = jointP π o x w * (firstMoment π 0 * firstMoment π 0) := by
    intro x
    rw [show (∑' y, ∑' z, hubSplitValue π o x y z w)
        = ∑' y, (jointP π o x w * tau π w y) * firstMoment π 0 from
      tsum_congr fun y => hfz x y]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, mul_assoc, tau_row_sum π hq w]
  exact (tsum_congr fun x => hfy x).trans ENNReal.tsum_mul_right

/-- **The summed hub evaluation.**  The sum of the hub-split blocks over the hub position, the
pair point and the two leaf endpoints is the second cluster moment times the square of the first
cluster moment. -/
theorem hubSplitSum_eq [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    hubSplitSum π o = secondMoment π o * (firstMoment π 0 * firstMoment π 0) := by
  rw [hubSplitSum]
  rw [show (∑' w, ∑' x, ∑' y, ∑' z, hubSplitValue π o x y z w)
      = ∑' w, (∑' x, jointP π o x w) * (firstMoment π 0 * firstMoment π 0) from
    tsum_congr fun w => hubBlock_factor π hq o w]
  rw [ENNReal.tsum_mul_right,
    show (∑' i, ∑' x, jointP π o x i) = hubPairSum π o from rfl,
    hubPairSum_eq_secondMoment π hq o]

/-- The same, in the squared form used by the source's display. -/
theorem hubSplitSum_eq_pow [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    hubSplitSum π o = secondMoment π o * (firstMoment π 0) ^ 2 := by
  rw [hubSplitSum_eq π hq o, pow_two]

end HubJointEval
