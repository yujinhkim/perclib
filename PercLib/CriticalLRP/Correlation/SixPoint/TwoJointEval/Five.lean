/-
Ultramath swarm `smwxenel0`, member `m1`, direction d2 (`TWO-JOINT-MIDDLE-EVALUATION`).

The same one-split evaluation with the five terminal sums in an *arbitrary* order.

The assembly of the `p = 5`, `k = 2` fifth moment sums the five non-root terminals of a
labelled pattern, and the pattern `pat k` sends comb slots to labels, so the terminal
sums appear in an order determined by `pat k`.  Here the value
`(secondMoment π 0)^2 * (∑' x, tau π 0 x)^3` is shown for every reindexing of the five
terminals, so no case analysis over the fifteen patterns is needed at this step.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointEval.Eval

/-!
# Terminal reindexing and evaluation for all fifteen patterns

Only the middle split is evaluated; other splits and the moment assembly remain open.
-/


open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.TwoJointEval

variable {V : Type*}

/-- A fivefold nested sum as one sum over `Fin 5 → V`. -/
theorem tsum_fin5 (G : (Fin 5 → V) → ℝ≥0∞) :
    (∑' X : Fin 5 → V, G X) =
      ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, G ![x0, x1, x2, x3, x4] := by
  rw [← Equiv.tsum_eq fin5Prod.symm G]
  simp only [ENNReal.tsum_prod']
  rfl

/-- A fivefold sum is invariant under permuting the five index positions. -/
theorem tsum_fin5_perm (σ : Equiv.Perm (Fin 5)) (G : (Fin 5 → V) → ℝ≥0∞) :
    (∑' X : Fin 5 → V, G (fun i => X (σ i))) = ∑' X : Fin 5 → V, G X :=
  Equiv.tsum_eq (Equiv.arrowCongr σ.symm (Equiv.refl V)) G

/-- **The `j = 2` two-joint slot at any terminal order, root on the first joint.**  The
five terminal slots `b1, b2, b3, b4, t` are read through an arbitrary permutation `σ` of
five free labels; the value is the `p = 5`, `k = 2` monomial `(E|K|²)²(E|K|)³`. -/
theorem midSlotK2_tsum_root_joint_of_perm [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V)
    (σ : Equiv.Perm (Fin 5)) :
    (∑' u : Fin 5 → V,
        midSlotK2 π o (u (σ 0)) (u (σ 1)) (u (σ 2)) (u (σ 3)) (u (σ 4))) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  have hbase : (∑' u : Fin 5 → V,
      midSlotK2 π o (u 0) (u 1) (u 2) (u 3) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    rw [tsum_fin5 (G := fun u => midSlotK2 π o (u 0) (u 1) (u 2) (u 3) (u 4))]
    exact midSlotK2_tsum_root_joint π hq o
  rw [show (∑' u : Fin 5 → V,
      midSlotK2 π o (u (σ 0)) (u (σ 1)) (u (σ 2)) (u (σ 3)) (u (σ 4))) =
      ∑' u : Fin 5 → V, midSlotK2 π o (u 0) (u 1) (u 2) (u 3) (u 4) from
    tsum_fin5_perm σ (G := fun u => midSlotK2 π o (u 0) (u 1) (u 2) (u 3) (u 4))]
  exact hbase

/-- **The `j = 2` two-joint slot at any terminal order, root on the residual chain.** -/
theorem midSlotK2_tsum_root_chain_of_perm [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (r : V)
    (σ : Equiv.Perm (Fin 5)) :
    (∑' u : Fin 5 → V,
        midSlotK2 π (u (σ 0)) (u (σ 1)) r (u (σ 2)) (u (σ 3)) (u (σ 4))) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  have hbase : (∑' u : Fin 5 → V,
      midSlotK2 π (u 0) (u 1) r (u 2) (u 3) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    rw [tsum_fin5 (G := fun u => midSlotK2 π (u 0) (u 1) r (u 2) (u 3) (u 4))]
    exact midSlotK2_tsum_root_chain π hq r
  rw [show (∑' u : Fin 5 → V,
      midSlotK2 π (u (σ 0)) (u (σ 1)) r (u (σ 2)) (u (σ 3)) (u (σ 4))) =
      ∑' u : Fin 5 → V, midSlotK2 π (u 0) (u 1) r (u 2) (u 3) (u 4) from
    tsum_fin5_perm σ (G := fun u => midSlotK2 π (u 0) (u 1) r (u 2) (u 3) (u 4))]
  exact hbase

end PercLib.CriticalLRP.SixPoint.TwoJointEval

namespace PercLib.CriticalLRP.SixPoint.TwoJointEval

variable {V : Type*}

/-! ## The residual-chain normal form

The three residual two-point factors of the accepted `j = 2` grouping share the split
point `c` (`b2 - c - v` and `t - c`), so they are *not* three independently peelable
factors: `∑' c, tau π b2 c * tau π c v` is not a product of susceptibilities.  What does
hold is the exact normal form below: the two-point column sums at `c` are taken first
(over `t`, then over `b2`), and only then the column sum at `v`.  The order of the two
sums at `c` is forced, and this is precisely why the chain still yields `(E|K|)³`. -/

/-- **Residual-chain normal form.**  The chain `b2 - c - v`, `t - c` of the accepted
two-joint slot contributes exactly `(E|K|)³`, in the summation order `t`, `b2`, `c`. -/
theorem residual_chain_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (v : V) :
    (∑' c, ∑' b2, ∑' t, tau π b2 c * (tau π c v * tau π t c)) =
      (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)) := by
  classical
  have ht : ∀ (c b2 : V),
      (∑' t, tau π b2 c * (tau π c v * tau π t c)) =
        (tau π b2 c * tau π c v) * (∑' x, tau π 0 x) := by
    intro c b2
    rw [show (∑' t, tau π b2 c * (tau π c v * tau π t c)) =
        ∑' t, (tau π b2 c * tau π c v) * tau π t c from
      tsum_congr fun t => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c]
  rw [tsum_congr fun c => tsum_congr fun b2 => ht c b2]
  have hb2 : ∀ c : V,
      (∑' b2, (tau π b2 c * tau π c v) * (∑' x, tau π 0 x)) =
        (tau π c v * (∑' x, tau π 0 x)) * (∑' x, tau π 0 x) := by
    intro c
    rw [show (∑' b2, (tau π b2 c * tau π c v) * (∑' x, tau π 0 x)) =
        ∑' b2, (tau π c v * (∑' x, tau π 0 x)) * tau π b2 c from
      tsum_congr fun b2 => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c]
  rw [tsum_congr fun c => hb2 c]
  have hc : (∑' c, (tau π c v * (∑' x, tau π 0 x)) * (∑' x, tau π 0 x)) =
      (∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)) := by
    rw [show (∑' c, (tau π c v * (∑' x, tau π 0 x)) * (∑' x, tau π 0 x)) =
        ∑' c, ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)) * tau π c v from
      tsum_congr fun c => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq v]
    ring
  rw [hc]

/-! ## The constant `105 = 7!!` -/

/-- **The `k = 2` constant.**  If each of the `15 * 7 = 105` labelled pattern/split slots
costs at most `C`, the whole shape sum costs at most `7!! * C = 105 * C` — the constant of
Lemma I.4.16 at `p = 5`, `k = 2`. -/
theorem tsum_fin15_fin7_le (C : ℝ≥0∞) (f : Fin 15 × Fin 7 → ℝ≥0∞) (h : ∀ p, f p ≤ C) :
    (∑' p : Fin 15 × Fin 7, f p) ≤ Nat.doubleFactorial 7 * C := by
  have hdf : Nat.doubleFactorial 7 = 105 := by
    rw [← PercLib.CriticalLRP.TreeExpansion.SixPoint.card_fin15_mul_fin7_eq_sevenDoubleFactorial,
      PercLib.CriticalLRP.TreeExpansion.SixPoint.card_fin15_mul_fin7]
  calc (∑' p : Fin 15 × Fin 7, f p) ≤ ∑' _ : Fin 15 × Fin 7, C := ENNReal.tsum_le_tsum h
    _ = 105 * C := PercLib.CriticalLRP.TreeExpansion.SixPoint.tsum_fin15_fin7_const C
    _ = Nat.doubleFactorial 7 * C := by rw [hdf]; norm_num

end PercLib.CriticalLRP.SixPoint.TwoJointEval
