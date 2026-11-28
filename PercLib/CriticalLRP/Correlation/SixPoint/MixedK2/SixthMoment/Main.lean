/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m1.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m1/Main.lean`.
-/

/-
Ultramath `smwzqts7r`, member `m1`, direction `d2`.

# `p = 6`, `k = 2` assembly: the cover gives the sixth-moment bound

Hutchcroft, arXiv:2508.18807v1, Lemma I.4.16 at `p = 6`, `k = 2`:

  `E|K|^6 ≤ 945 (E|K|^2)^2 (E|K|)^5`.

This file contains the complete extended-nonnegative accounting of the `k = 2` regrouping:

* `tsum_six_fin945_swap` — the `945`-fold shape sum may be taken outside the six free-leaf
  sums;
* `sixth_moment_of_sixCover` — a cover of the sixfold joint connection probability by the
  `945` two-hub slot diagrams implies the sixth-moment bound at the native law;
* `sixthMomentMixed_of_sixCover` — the same at a `SourceModelData` cutoff law, giving exactly
  `CaseTwo.SixthMomentMixed M`.

The single retained hypothesis is `SixCover`, the deterministic combinatorial input of the
source's proof (the union bound over the `945 = 9!!` binary trees with six labelled leaves
followed by the BK inequality).  Everything else is proved here.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Defs
public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Slot6
public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.SixFold

/-! Conditional sixth-moment assembly from an explicitly retained event cover. -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators Topology
open PercLib.Percolation.Bond
open PercLib.Probability

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ## Index bookkeeping for the `945` shapes -/

/-- The `945`-fold shape sum may be moved outside the six free-leaf sums. -/
theorem tsum_six_fin945_swap [Countable V]
    (F : V → V → V → V → V → V → Fin 945 → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' f, ∑' t : Fin 945, F a b c d e f t)
      = ∑' t : Fin 945, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' f, F a b c d e f t := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' f, ∑' t : Fin 945, F a b c d e f t)
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' t : Fin 945, ∑' f, F a b c d e f t :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          tsum_congr fun e => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' d, ∑' t : Fin 945, ∑' e, ∑' f, F a b c d e f t :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' t : Fin 945, ∑' d, ∑' e, ∑' f, F a b c d e f t :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' t : Fin 945, ∑' c, ∑' d, ∑' e, ∑' f, F a b c d e f t :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' t : Fin 945, ∑' b, ∑' c, ∑' d, ∑' e, ∑' f, F a b c d e f t :=
        tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' t : Fin 945, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' f, F a b c d e f t :=
        ENNReal.tsum_comm

/-- The constant shape sum: `9!! = 945`. -/
theorem tsum_fin945_const (c : ℝ≥0∞) : (∑' _ : Fin 945, c) = 945 * c := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- `9!! = 945`, the number `(2p-3)!!` of Lemma I.4.16 at `p = 6`. -/
theorem doubleFactorial_nine : Nat.doubleFactorial (2 * 6 - 3) = 945 := by decide

/-- The susceptibility is at least one: `E|K_0| ≥ P(0 ↔ 0) = 1`. -/
theorem one_le_susceptibility [Countable V] (π : Sym2 V → unitInterval) (o : V) :
    1 ≤ ∑' x, tau π o x := by
  have h : tau π o o = 1 := by
    rw [tau, conn_self, measure_univ]
  calc (1 : ℝ≥0∞) = tau π o o := h.symm
    _ ≤ ∑' x, tau π o x := ENNReal.le_tsum o

/-! ## The abstract consumer: a `945`-shape cover gives the sixth-moment bound -/

/-- **The `p = 6`, `k = 2` moment bound from the shape cover.**

Given a pointwise bound of the sixfold joint connection probability by the sum of the `945`
two-hub slot diagrams (the residual `SixCover`), the sixth cluster moment satisfies
`E|K|^6 ≤ 945 (E|K|^2)^2 (E|K|)^5`.

The only other inputs are the exact sixfold moment identity `lintegral_cardFun_six_eq` and the
exact diagram evaluation `tsum_slotK2Six_six`, both proved here. -/
theorem sixth_moment_of_sixCover [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (o : V) (pat : Fin 945 → Equiv.Perm (Fin 6))
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (hcover : SixCover π o pat) : SixthMomentLe π o := by
  have hmass : ∀ t : Fin 945,
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s, slotK2Six π (pat t) o ![y, z, w, q, r, s])
        ≤ secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5 := by
    intro t
    rw [tsum_slotK2Six_six π hq (pat t) o]
    exact mul_le_mul' le_rfl
      (pow_le_pow_right₀ (one_le_susceptibility π o) (by norm_num : 4 ≤ 5))
  have hmain :
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω o)) ^ 6 ∂(law π)
        ≤ 945 * (secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5) := by
    rw [SixFold.lintegral_cardFun_six_eq π o]
    calc ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
          law π (conn o y ∩ conn o z ∩ conn o w ∩ conn o q ∩ conn o r ∩ conn o s)
        ≤ ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s, ∑' t : Fin 945,
            slotK2Six π (pat t) o ![y, z, w, q, r, s] :=
          ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
            ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
              ENNReal.tsum_le_tsum fun r => ENNReal.tsum_le_tsum fun s =>
                hcover y z w q r s
      _ = ∑' t : Fin 945, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
            slotK2Six π (pat t) o ![y, z, w, q, r, s] :=
          tsum_six_fin945_swap (fun y z w q r s t => slotK2Six π (pat t) o ![y, z, w, q, r, s])
      _ ≤ ∑' _t : Fin 945, secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5 :=
          ENNReal.tsum_le_tsum hmass
      _ = 945 * (secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5) := tsum_fin945_const _
  simpa only [SixthMomentLe, secondMoment, firstMoment, ← firstMoment_eq, mul_assoc]
    using hmain

/-! ## The cover as an event cover

The abstract form in which the cover appears in the source's proof: the joint connection event
is contained in the union of `945` shape events, and each shape's summed mass is at most
`(E|K|^2)^2 (E|K|)^5`.  This form does not presuppose that the shapes are the two-hub diagrams,
so it is the honest non-vacuous residual. -/
theorem sixth_moment_of_eventCover [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (o : V)
    {E : Fin 945 → (Fin 6 → V) → Set (Config V)}
    (hcover : ∀ y z w q r s : V,
      conn o y ∩ conn o z ∩ conn o w ∩ conn o q ∩ conn o r ∩ conn o s ⊆
        ⋃ t : Fin 945, E t ![y, z, w, q, r, s])
    (hbound : ∀ t : Fin 945,
      (∑' L : Fin 6 → V, law π (E t L))
        ≤ secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5) : SixthMomentLe π o := by
  have hmain :
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω o)) ^ 6 ∂(law π)
        ≤ 945 * (secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5) := by
    rw [SixFold.lintegral_cardFun_six_eq π o]
    calc ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
          law π (conn o y ∩ conn o z ∩ conn o w ∩ conn o q ∩ conn o r ∩ conn o s)
        ≤ ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
            law π (⋃ t : Fin 945, E t ![y, z, w, q, r, s]) :=
          ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
            ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
              ENNReal.tsum_le_tsum fun r => ENNReal.tsum_le_tsum fun s =>
                measure_mono (hcover y z w q r s)
      _ ≤ ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s, ∑' t : Fin 945,
            law π (E t ![y, z, w, q, r, s]) :=
          ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
            ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
              ENNReal.tsum_le_tsum fun r => ENNReal.tsum_le_tsum fun s =>
                measure_iUnion_le _
      _ = ∑' t : Fin 945, ∑' L : Fin 6 → V, law π (E t L) := by
          rw [tsum_six_fin945_swap
            (fun y z w q r s t => law π (E t ![y, z, w, q, r, s]))]
          exact tsum_congr fun t => (tsum_fin6 (G := fun L => law π (E t L))).symm
      _ ≤ ∑' _t : Fin 945, secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5 :=
          ENNReal.tsum_le_tsum hbound
      _ = 945 * (secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5) := tsum_fin945_const _
  simpa only [SixthMomentLe, secondMoment, firstMoment, ← firstMoment_eq, mul_assoc]
    using hmain

end PercLib.CriticalLRP.TreeExpansion.HubK2
