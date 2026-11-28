/-
# `p = 6`, `k = 2`: exact arm, slot and coefficient accounting

Integrated from the independently reviewed bounded submission `.ultramath/smwzvo8ss/m4`.
Production integration follows commit `0e0638f5d113361bde593404f092dfd66828c050`.
This is only coefficient/exponent bookkeeping and a wrapper for the existing slot evaluation;
it supplies neither an event realization nor the mixed sixth moment.

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.16
("generalized tree-graph inequality", p. 43):

  `E_β |K|^p ≤ (2p-3)!! (E_β |K|^2)^k (E_β |K|)^{2p-1-3k}`  for `0 ≤ k ≤ ⌈(p-1)/2⌉`.

At `p = 6`, `k = 2` this is `E|K|^6 ≤ 945 (E|K|^2)^2 (E|K|)^5`.

The atlas of an `RTree` with `p` leaves has `2p - 1` edges, of which `3k` are the `k` hub
three-stars and `2p - 1 - 3k` are off-hub.  The two-hub slot diagram keeps one *joint* pair
of leaves at each hub (summing to `E|K|^2`) and one two-point link from each hub to the root
(susceptibility `E|K|`), so the `3k` hub edges are *not* BK-split; the collapsed exponent
identity `2k + (2p - 1 - 3k) = 2p - 1 - k` is what turns `χ^{2p-1}` into
`(E|K|^2)^k χ^{2p-1-3k}` times the `k` susceptibility factors.  This file records that
arithmetic exactly at `p = 6, k = 2` and restates the already-proved per-shape mass bound in
the `Fin 6` leaf-index form consumed by the sixth-moment assembly.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Main

/-! Exact bookkeeping for the `p = 6`, `k = 2` regrouping. -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators Topology
open PercLib.Percolation.Bond
open PercLib.Probability

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ## Coefficients -/

/-- The source coefficient `(2p-3)!!` at `p = 6` is `9!! = 945`. -/
theorem nine_doubleFactorial : Nat.doubleFactorial (2 * 6 - 3) = 945 := by decide

/-- The `945` shapes factor as `105 * 9`: the `105` shapes of the `p = 5`, `k = 2` family
(the source's `15 * 7` pattern/arm index) times the `2p - 3 = 9` slots that adding the sixth
free leaf opens. -/
theorem shape_factorization : 945 = 105 * 9 := by norm_num

/-- The `p = 5`, `k = 2` coefficient and its slot factor. -/
theorem five_shape_factorization : Nat.doubleFactorial (2 * 5 - 3) = 15 * 7 := by decide

/-- The seven-point cover of `Correlation/SixPoint/SevenPoint.lean` uses `15 * 7 * 8 = 840`
slots: one slot short of `945 = 15 * 7 * 9`. -/
theorem seven_point_deficit : 15 * 7 * 8 = 840 ∧ 840 < 945 := by decide

/-! ## Arm and exponent arithmetic -/

/-- `p = 6`, `k = 2`: the `3k = 6` hub-star edges plus the `2p - 1 - 3k = 5` off-hub edges are
exactly the `2p - 1 = 11` atlas edges. -/
theorem p6k2_atlas_edges : 3 * 2 + (2 * 6 - 1 - 3 * 2) = 2 * 6 - 1 := by norm_num

/-- The generalized bound does not use the hub edges as `3k` separate two-point factors: each
hub contributes `2` collapsed arms (its joint pair, one second moment) plus `1` root link (one
susceptibility), so the total exponent is `2k + (2p - 1 - 3k) = 2p - 1 - k`. -/
theorem p6k2_collapsed_exponent : 2 * 2 + (2 * 6 - 1 - 3 * 2) = 2 * 6 - 1 - 2 := by norm_num

/-- The same identity at `p = 5`, `k = 2`, the instance its landed proof consumes. -/
theorem p5k2_collapsed_exponent : 2 * 2 + (2 * 5 - 1 - 3 * 2) = 2 * 5 - 1 - 2 := by norm_num

/-- The `k = 1` boundary: one hub three-star at `p = 6` leaves `2p - 1 - 3 = 8` off-hub arms. -/
theorem p6k1_atlas_edges : 3 * 1 + (2 * 6 - 1 - 3 * 1) = 2 * 6 - 1 := by norm_num

/-- The bound `3k ≤ 2p - 1` at `p = 6`, `k = 2` is not a truncated subtraction. -/
theorem p6k2_hub_edges_le : 3 * 2 ≤ 2 * 6 - 1 := by norm_num

/-! ## The per-shape mass in `Fin 6` leaf form -/

/-- **Per-shape mass of the `p = 6` two-hub slot, `Fin 6` form.**

The `p = 6`, `k = 2` slot diagram is the two-hub integrand of `Slot6`: two joint pairs (each
summing to `E|K|^2` at its hub), two two-point links to the root, and two residual free leaves
(one susceptibility each).  Its exact leaf-and-hub mass is `(E|K|^2)^2 (E|K|)^4`, at most the
source's `(E|K|^2)^2 (E|K|)^5` because `E|K| ≥ 1`.  This is the `hbound` side of the
sixth-moment assembly; no cover is asserted. -/
theorem six_shape_mass_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (o : V)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' L : Fin 6 → V, slotK2Six π (Equiv.refl (Fin 6)) o L)
      ≤ secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5 := by
  rw [tsum_fin6_apply, tsum_slotK2Six_six π hq (Equiv.refl (Fin 6)) o]
  exact mul_le_mul' le_rfl
    (pow_le_pow_right₀ (one_le_susceptibility π o) (by norm_num : 4 ≤ 5))

/-- The exact value, for the record: `(E|K|^2)^2 (E|K|)^4`. -/
theorem six_shape_mass_eq [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (o : V)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' L : Fin 6 → V, slotK2Six π (Equiv.refl (Fin 6)) o L)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 4 := by
  rw [tsum_fin6_apply]
  exact tsum_slotK2Six_six π hq (Equiv.refl (Fin 6)) o

end PercLib.CriticalLRP.TreeExpansion.HubK2

/-! ## Axiom audit

Every theorem above rests on at most `propext`, `Classical.choice`, `Quot.sound`; there is no
`sorry`/`admit`/`native_decide` and no new axiom. -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.nine_doubleFactorial
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.shape_factorization
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.five_shape_factorization
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.seven_point_deficit
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.p6k2_atlas_edges
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.p6k2_collapsed_exponent
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.p5k2_collapsed_exponent
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.p6k1_atlas_edges
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.p6k2_hub_edges_le
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.six_shape_mass_le
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.six_shape_mass_eq
