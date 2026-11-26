/-
Ultramath swarm `smwxenel0`, member `m1`, direction d2 (`TWO-JOINT-MIDDLE-EVALUATION`).

Free-vertex evaluation of the accepted middle-split two-joint slot.

Two theorems carry the content:

* `midSlot_peel_joint` -- with the root `o` on an ear of the first joint pair,
  `∑' v b1 b3 b4 c b2 t twoJointProd π o b1 b2 b3 b4 t v c = (E|K|²)² (E|K|)³`,
  where `E|K|² = secondMoment π 0` and `E|K| = ∑' x, tau π 0 x`.  Each factor is
  produced by exactly one summation:
  `t`, `b2`, `c` by the two-point row/column sums (`tau_col`), `b3, b4` by the free
  three-point function `secondMoment_eq` at `v` (root-independent), and `b1, v` by the
  root-anchored double star `tsum_jointP_centre`.
* `midSlot_peel_chain` -- with the root `r` on the residual chain (`b2` slot),
  the same value, the two joint pairs now both being free three-point functions and the
  convergence of the `v` sum coming from the residual link `τ c v`.

No probability is assumed translation invariant beyond the full profile invariance
`hq : ∀ x y g, π s(x + g, y + g) = π s(x, y)`; nothing about `tau` alone is assumed.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointEval.Bridge

/-!
# Evaluation of the middle split’s two root placements

Only the middle split is evaluated; other splits and the moment assembly remain open.
-/


open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.TwoJointEval

variable {V : Type*}

/-! ## Seven nested extended sums -/

/-- A sevenfold nested sum as one sum over `Fin 7 → V`. -/
theorem tsum_fin7 (G : (Fin 7 → V) → ℝ≥0∞) :
    (∑' X : Fin 7 → V, G X) =
      ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' x6,
        G ![x0, x1, x2, x3, x4, x5, x6] := by
  rw [← Equiv.tsum_eq fin7Prod.symm G]
  simp only [ENNReal.tsum_prod']
  rfl

/-- A sevenfold sum is invariant under permuting the seven index positions. -/
theorem tsum_fin7_perm (σ : Equiv.Perm (Fin 7)) (G : (Fin 7 → V) → ℝ≥0∞) :
    (∑' X : Fin 7 → V, G (fun i => X (σ i))) = ∑' X : Fin 7 → V, G X :=
  Equiv.tsum_eq (Equiv.arrowCongr σ.symm (Equiv.refl V)) G

/-- The nested form of `tsum_fin7_perm`. -/
theorem tsum_seven_perm (σ : Equiv.Perm (Fin 7))
    (H : V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' x6,
        H (![x0, x1, x2, x3, x4, x5, x6] (σ 0)) (![x0, x1, x2, x3, x4, x5, x6] (σ 1))
          (![x0, x1, x2, x3, x4, x5, x6] (σ 2)) (![x0, x1, x2, x3, x4, x5, x6] (σ 3))
          (![x0, x1, x2, x3, x4, x5, x6] (σ 4)) (![x0, x1, x2, x3, x4, x5, x6] (σ 5))
          (![x0, x1, x2, x3, x4, x5, x6] (σ 6)))
      = ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' x6,
          H x0 x1 x2 x3 x4 x5 x6 := by
  rw [← tsum_fin7 (G := fun X => H (X (σ 0)) (X (σ 1)) (X (σ 2)) (X (σ 3)) (X (σ 4))
    (X (σ 5)) (X (σ 6)))]
  rw [tsum_fin7_perm σ (G := fun X => H (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6))]
  rw [tsum_fin7 (G := fun X => H (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6))]
  rfl

/-! ## The root-joint peel -/

/-- **Free-vertex evaluation, root on an ear of the first joint pair.**  In the peel order
`v, b1, b3, b4, c, b2, t`, the five summation steps are

* `t` and `b2`: the two-point column sums at `c`, giving one `E|K|` each;
* `c`: the two-point column sum at `v`, giving the third `E|K|`;
* `b3, b4`: the free three-point function at `v`, i.e. `secondMoment π v = E|K|²`;
* `b1, v`: the root-anchored double star, i.e. `secondMoment π 0` again. -/
theorem midSlot_peel_joint [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    (∑' v, ∑' b1, ∑' b3, ∑' b4, ∑' c, ∑' b2, ∑' t,
        twoJointProd π o b1 b2 b3 b4 t v c)
      = (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  classical
  -- peel `t`
  have ht : ∀ (v b1 b3 b4 c b2 : V),
      (∑' t, twoJointProd π o b1 b2 b3 b4 t v c) =
        jointP π o b1 v * (jointP π b3 b4 v *
          (tau π b2 c * (tau π c v * (∑' x, tau π 0 x)))) := by
    intro v b1 b3 b4 c b2
    rw [show (∑' t, twoJointProd π o b1 b2 b3 b4 t v c) =
        ∑' t, (jointP π o b1 v * (jointP π b3 b4 v * (tau π b2 c * tau π c v))) *
          tau π t c from
      tsum_congr fun t => by simp only [twoJointProd]; ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c]
    ring
  -- peel `b2`
  have hb2 : ∀ (v b1 b3 b4 c : V),
      (∑' b2, jointP π o b1 v * (jointP π b3 b4 v *
          (tau π b2 c * (tau π c v * (∑' x, tau π 0 x))))) =
        jointP π o b1 v * (jointP π b3 b4 v *
          ((∑' x, tau π 0 x) * (tau π c v * (∑' x, tau π 0 x)))) := by
    intro v b1 b3 b4 c
    rw [show (∑' b2, jointP π o b1 v * (jointP π b3 b4 v *
        (tau π b2 c * (tau π c v * (∑' x, tau π 0 x))))) =
        ∑' b2, (jointP π o b1 v * (jointP π b3 b4 v *
          (tau π c v * (∑' x, tau π 0 x)))) * tau π b2 c from
      tsum_congr fun b2 => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c]
    ring
  -- peel `c`
  have hc : ∀ (v b1 b3 b4 : V),
      (∑' c, jointP π o b1 v * (jointP π b3 b4 v *
          ((∑' x, tau π 0 x) * (tau π c v * (∑' x, tau π 0 x))))) =
        jointP π o b1 v * (jointP π b3 b4 v *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro v b1 b3 b4
    rw [show (∑' c, jointP π o b1 v * (jointP π b3 b4 v *
        ((∑' x, tau π 0 x) * (tau π c v * (∑' x, tau π 0 x))))) =
        ∑' c, (jointP π o b1 v * (jointP π b3 b4 v *
          ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) * tau π c v from
      tsum_congr fun c => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq v]
    ring
  -- peel `b3, b4`: the free three-point function at `v`
  have hb34 : ∀ (v b1 : V),
      (∑' b3, ∑' b4, jointP π o b1 v * (jointP π b3 b4 v *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        jointP π o b1 v * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro v b1
    rw [show (∑' b3, ∑' b4, jointP π o b1 v * (jointP π b3 b4 v *
        ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        ∑' b3, ∑' b4, (jointP π o b1 v *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) *
          jointP π b3 b4 v from
      tsum_congr fun b3 => tsum_congr fun b4 => by ring]
    simp only [ENNReal.tsum_mul_left]
    rw [show (∑' b3, ∑' b4, jointP π b3 b4 v) = secondMoment π v from
      (secondMoment_eq π v).symm]
    rw [secondMoment_root_independent π hq v]
    ring
  -- peel `b1, v`: the root-anchored double star
  have hb1v :
      (∑' v, ∑' b1, jointP π o b1 v * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    rw [show (∑' v, ∑' b1, jointP π o b1 v * (secondMoment π 0 *
        ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        ∑' v, ∑' b1, (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) *
          jointP π o b1 v from
      tsum_congr fun v => tsum_congr fun b1 => by ring]
    simp only [ENNReal.tsum_mul_left]
    rw [show (∑' v, ∑' b1, jointP π o b1 v) = secondMoment π 0 from
      tsum_jointP_centre π hq o]
    ring
  rw [tsum_congr fun v => tsum_congr fun b1 => tsum_congr fun b3 => tsum_congr fun b4 =>
      tsum_congr fun c => tsum_congr fun b2 => ht v b1 b3 b4 c b2]
  rw [tsum_congr fun v => tsum_congr fun b1 => tsum_congr fun b3 => tsum_congr fun b4 =>
      tsum_congr fun c => hb2 v b1 b3 b4 c]
  rw [tsum_congr fun v => tsum_congr fun b1 => tsum_congr fun b3 => tsum_congr fun b4 =>
      hc v b1 b3 b4]
  rw [tsum_congr fun v => tsum_congr fun b1 => hb34 v b1]
  rw [hb1v]
  ring

/-! ## The root-on-chain peel -/

/-- **Free-vertex evaluation, root on the residual chain.**  Both joint pairs are now free
three-point functions and each contributes `E|K|²` through `secondMoment_eq`; the three
residual links give `E|K|` each.  The `v` sum converges through the residual link `τ c v`,
not through a root-anchored joint. -/
theorem midSlot_peel_chain [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (r : V) :
    (∑' c, ∑' v, ∑' b4, ∑' b3, ∑' b1, ∑' b0, ∑' t,
        twoJointProd π b0 b1 r b3 b4 t v c)
      = (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  classical
  -- peel `t`
  have ht : ∀ (c v b4 b3 b1 b0 : V),
      (∑' t, twoJointProd π b0 b1 r b3 b4 t v c) =
        jointP π b0 b1 v * (jointP π b3 b4 v *
          (tau π r c * (tau π c v * (∑' x, tau π 0 x)))) := by
    intro c v b4 b3 b1 b0
    rw [show (∑' t, twoJointProd π b0 b1 r b3 b4 t v c) =
        ∑' t, (jointP π b0 b1 v * (jointP π b3 b4 v * (tau π r c * tau π c v))) *
          tau π t c from
      tsum_congr fun t => by simp only [twoJointProd]; ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c]
    ring
  -- peel the free joint pair `b0, b1`
  have hb01 : ∀ (c v b4 b3 : V),
      (∑' b1, ∑' b0, jointP π b0 b1 v * (jointP π b3 b4 v *
          (tau π r c * (tau π c v * (∑' x, tau π 0 x))))) =
        jointP π b3 b4 v * (secondMoment π 0 *
          (tau π r c * (tau π c v * (∑' x, tau π 0 x)))) := by
    intro c v b4 b3
    rw [show (∑' b1, ∑' b0, jointP π b0 b1 v * (jointP π b3 b4 v *
        (tau π r c * (tau π c v * (∑' x, tau π 0 x))))) =
        ∑' b1, ∑' b0, (jointP π b3 b4 v *
          (tau π r c * (tau π c v * (∑' x, tau π 0 x)))) * jointP π b0 b1 v from
      tsum_congr fun b1 => tsum_congr fun b0 => by ring]
    simp only [ENNReal.tsum_mul_left]
    rw [show (∑' b1, ∑' b0, jointP π b0 b1 v) = ∑' a, ∑' b, jointP π a b v from
      ENNReal.tsum_comm]
    rw [← secondMoment_eq π v]
    rw [secondMoment_root_independent π hq v]
    ring
  -- peel the second free joint pair `b3, b4`
  have hb34 : ∀ (c v : V),
      (∑' b4, ∑' b3, jointP π b3 b4 v * (secondMoment π 0 *
          (tau π r c * (tau π c v * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (secondMoment π 0 *
          (tau π r c * (tau π c v * (∑' x, tau π 0 x)))) := by
    intro c v
    rw [show (∑' b4, ∑' b3, jointP π b3 b4 v * (secondMoment π 0 *
        (tau π r c * (tau π c v * (∑' x, tau π 0 x))))) =
        ∑' b4, ∑' b3, (secondMoment π 0 *
          (tau π r c * (tau π c v * (∑' x, tau π 0 x)))) * jointP π b3 b4 v from
      tsum_congr fun b4 => tsum_congr fun b3 => by ring]
    simp only [ENNReal.tsum_mul_left]
    rw [show (∑' b4, ∑' b3, jointP π b3 b4 v) = ∑' a, ∑' b, jointP π a b v from
      ENNReal.tsum_comm]
    rw [← secondMoment_eq π v]
    rw [secondMoment_root_independent π hq v]
    ring
  -- peel `v`: the residual link `τ c v` carries the convergence of the joint centre
  have hv : ∀ (c : V),
      (∑' v, secondMoment π 0 * (secondMoment π 0 *
          (tau π r c * (tau π c v * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (secondMoment π 0 *
          (tau π r c * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro c
    rw [show (∑' v, secondMoment π 0 * (secondMoment π 0 *
        (tau π r c * (tau π c v * (∑' x, tau π 0 x))))) =
        ∑' v, (secondMoment π 0 * (secondMoment π 0 *
          (tau π r c * (∑' x, tau π 0 x)))) * tau π c v from
      tsum_congr fun v => by ring]
    rw [ENNReal.tsum_mul_left, tau_row π hq c]
    ring
  -- peel `c`: the residual ear `τ r c`
  have hcr :
      (∑' c, secondMoment π 0 * (secondMoment π 0 *
          (tau π r c * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    rw [show (∑' c, secondMoment π 0 * (secondMoment π 0 *
        (tau π r c * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x))))) =
        ∑' c, (secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) * tau π r c from
      tsum_congr fun c => by ring]
    rw [ENNReal.tsum_mul_left, tau_row π hq r]
    ring
  rw [tsum_congr fun c => tsum_congr fun v => tsum_congr fun b4 => tsum_congr fun b3 =>
      tsum_congr fun b1 => tsum_congr fun b0 => ht c v b4 b3 b1 b0]
  rw [tsum_congr fun c => tsum_congr fun v => tsum_congr fun b4 => tsum_congr fun b3 =>
      hb01 c v b4 b3]
  rw [tsum_congr fun c => tsum_congr fun v => hb34 c v]
  rw [tsum_congr fun c => hv c]
  rw [hcr]
  ring

/-! ## The slot evaluations in the terminal order of the assembly -/

/-- **The `j = 2` two-joint slot evaluates to `(E|K|²)² (E|K|)³`, root on the first
joint.**  This is the `k = 2` companion of the production `slotU_tsum`
(`E|K|² (E|K|)^6` at `k = 1`). -/
theorem midSlotK2_tsum_root_joint [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, midSlotK2 π o b1 b2 b3 b4 t) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine Eq.trans ?_ (midSlot_peel_joint π hq o)
  simp only [midSlotK2]
  exact tsum_seven_perm permJoint
    (H := fun y0 y1 y2 y3 y4 y5 y6 => twoJointProd π o y1 y5 y2 y3 y6 y0 y4)

/-- **The `j = 2` two-joint slot evaluates to `(E|K|²)² (E|K|)³`, root on the residual
chain** (the `b2` slot; the `t` slot is the same statement by `tau_comm`). -/
theorem midSlotK2_tsum_root_chain [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (r : V) :
    (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, midSlotK2 π b0 b1 r b3 b4 t) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine Eq.trans ?_ (midSlot_peel_chain π hq r)
  simp only [midSlotK2]
  exact tsum_seven_perm permChain
    (H := fun y0 y1 y2 y3 y4 y5 y6 => twoJointProd π y5 y4 r y3 y2 y6 y1 y0)

end PercLib.CriticalLRP.SixPoint.TwoJointEval
