/-
The fifteen leaf-labelled slot diagrams of the `p = 4`, `k = 2` regrouping all evaluate to
`E|K_0|^2 * (E|K_0| * E|K_0|^2)`.  Ultramath `smwpq441z` member m3 (Direction C).
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Sum

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- Pull a constant times a two-point weight out of the centre sum. -/
theorem tsum_const_mul_tau [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (A : ℝ≥0∞) :
    (∑' c, A * (tau π 0 c * A)) = A * ((∑' x, tau π 0 x) * A) := by
  rw [show (∑' c, A * (tau π 0 c * A)) = ∑' c, A * A * tau π 0 c from
    tsum_congr fun c => by ring]
  rw [ENNReal.tsum_mul_left]
  ring

/-- **All fifteen leaf-labelled slot diagrams evaluate to the same product.**  The centre is
the middle vertex of the comb, kept by all three BK certificate groups; the four free leaves
are a permutation of the four terminals `1,2,3,4` in every pattern, so the leaf sum produces
the first-moment factor and the two joint double sums produce the two second-moment factors. -/
theorem tsum_slotDiagramK2 [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : Fin 15) :
    (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π k ![0, x1, x2, x3, x4])
      = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
  fin_cases k
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 0 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) 0 (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (3)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) 0 (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (3)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π x1 x2 0 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![0, 1, 2, 3] (by decide))
            (H := fun p q r s => starK2 π p q 0 r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_tauSlot π c]
          rw [show (∑' c, secondMoment π c * (tau π 0 c * secondMoment π c))
              = ∑' c, secondMoment π 0 * (tau π 0 c * secondMoment π 0) from
            tsum_congr fun c => by rw [secondMoment_root_independent π hq c]]
          exact tsum_const_mul_tau π (secondMoment π 0)

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 1 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (3)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (3)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π x1 x2 0 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![0, 2, 1, 3] (by decide))
            (H := fun p q r s => starK2 π p q 0 r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_tauSlot π c]
          rw [show (∑' c, secondMoment π c * (tau π 0 c * secondMoment π c))
              = ∑' c, secondMoment π 0 * (tau π 0 c * secondMoment π 0) from
            tsum_congr fun c => by rw [secondMoment_root_independent π hq c]]
          exact tsum_const_mul_tau π (secondMoment π 0)

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 2 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (3)) 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (3)) 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π x1 x2 0 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![0, 3, 1, 2] (by decide))
            (H := fun p q r s => starK2 π p q 0 r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_tauSlot π c]
          rw [show (∑' c, secondMoment π c * (tau π 0 c * secondMoment π c))
              = ∑' c, secondMoment π 0 * (tau π 0 c * secondMoment π 0) from
            tsum_congr fun c => by rw [secondMoment_root_independent π hq c]]
          exact tsum_const_mul_tau π (secondMoment π 0)

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 3 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (3)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (3)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![1, 0, 2, 3] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 4 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (3)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (3)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![2, 0, 1, 3] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 5 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![3, 0, 1, 2] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 6 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (3)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (3)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![0, 1, 2, 3] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 7 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (3)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (3)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![2, 1, 0, 3] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 8 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![3, 1, 0, 2] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 9 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (3)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (3)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![0, 2, 1, 3] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 10 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (3)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (3)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![1, 2, 0, 3] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 11 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![3, 2, 0, 1] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 12 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (2)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![0, 3, 1, 2] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 13 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (1)) (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (2)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![1, 3, 0, 2] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, slotDiagramK2 π 14 ![0, x1, x2, x3, x4])
        = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) c := by
          simp only [slotDiagramK2, pat]
          exact tsum_move_last_five (F := fun x1 x2 x3 x4 c => starK2 π 0 (![x1, x2, x3, x4] (2)) (![x1, x2, x3, x4] (3)) (![x1, x2, x3, x4] (0)) (![x1, x2, x3, x4] (1)) c)
      _ = ∑' c, ∑' x1, ∑' x2, ∑' x3, ∑' x4, starK2 π 0 x1 x2 x3 x4 c := by
          refine tsum_congr fun c => ?_
          exact tsum_four_perm (Equiv.ofBijective ![2, 3, 0, 1] (by decide))
            (H := fun p q r s => starK2 π 0 p q r s c)
      _ = secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0) := by
          rw [tsum_congr fun c => starK2_tsum_root_jointSlot π c]
          rw [show (∑' c, (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c))
              = ∑' c, (∑' p, jointP π 0 p c) * ((∑' x, tau π 0 x) * secondMoment π 0) from
            tsum_congr fun c => by
              rw [tau_col π hq c, secondMoment_root_independent π hq c]]
          rw [ENNReal.tsum_mul_right, tsum_jointP_centre π hq 0]

end PercLib.CriticalLRP.TreeExpansion.FivePoint
