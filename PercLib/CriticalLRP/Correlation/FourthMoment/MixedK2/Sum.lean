/-
Evaluation of the `p = 4`, `k = 2` common-centre double-star diagrams.
Ultramath `smwpq441z` member m3 (Direction C).

The three BK certificate groups of the shallow/deep regrouping leave two joint connection
events and one two-point event, all measured from the *same* centre.  This file sums the
resulting double-star over the four free leaves and the centre and finds exactly
`E|K_0|^2 * (E|K_0| * E|K_0|^2)` — i.e. the squared native second moment times the first
moment — provided the second moment is root independent (proved in `Transport.lean` from the
full translation invariance `hq`).
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Defs
public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Transport
public import PercLib.CriticalLRP.Correlation.FourthMoment.Mixed

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ### The first moment -/

theorem firstMoment_eq [Countable V] (π : Sym2 V → unitInterval) (x : V) :
    firstMoment π x = ∑' y, tau π x y := by
  rw [firstMoment,
    show (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω x) ∂(law π)) =
      ∫⁻ ω, ((PercLib.CriticalLRP.cluster ω x).encard : ℝ≥0∞) ∂(law π) from
    lintegral_congr fun ω => PercLib.CriticalLRP.Percolation.cardFun_eq_encard _]
  exact chi_eq_tsum_tau π x

/-! ### The two canonical five-slot sums -/

/-- **Root in the two-point slot.**  The two joint events each carry both free endpoints, so
each double sum is the native second moment at the centre. -/
theorem starK2_tsum_root_tauSlot [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (c : V) :
    (∑' p, ∑' q, ∑' r, ∑' s, starK2 π p q 0 r s c)
      = secondMoment π c * (tau π 0 c * secondMoment π c) := by
  have hstep : (∑' p, ∑' q, ∑' r, ∑' s, starK2 π p q 0 r s c)
      = ∑' p, ∑' q, (jointP π p q c * tau π 0 c) * secondMoment π c := by
    refine tsum_congr fun p => tsum_congr fun q => ?_
    rw [show (∑' r, ∑' s, starK2 π p q 0 r s c)
        = ∑' r, ∑' s, (jointP π p q c * tau π 0 c) * jointP π r s c from
      tsum_congr fun r => tsum_congr fun s => by simp only [starK2]; ring]
    rw [tsum_two_const_mul, ← secondMoment_eq π c]
  rw [hstep, tsum_two_mul_const, tsum_two_mul_const, ← secondMoment_eq π c]
  ring

/-- **Root in a joint slot.**  The far joint pair and the two-point factor sum out to the
susceptibility and the second moment; the near joint pair keeps the root and one free
endpoint. -/
theorem starK2_tsum_root_jointSlot [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (c : V) :
    (∑' p, ∑' q, ∑' r, ∑' s, starK2 π 0 p q r s c)
      = (∑' p, jointP π 0 p c) * ((∑' q, tau π q c) * secondMoment π c) := by
  have hstep : (∑' p, ∑' q, ∑' r, ∑' s, starK2 π 0 p q r s c)
      = ∑' p, ∑' q, jointP π 0 p c * (tau π q c * secondMoment π c) := by
    refine tsum_congr fun p => tsum_congr fun q => ?_
    rw [show (∑' r, ∑' s, starK2 π 0 p q r s c)
        = ∑' r, ∑' s, (jointP π 0 p c * tau π q c) * jointP π r s c from
      tsum_congr fun r => tsum_congr fun s => by simp only [starK2]; ring]
    rw [tsum_two_const_mul, ← secondMoment_eq π c]
    ring
  have hfac : ∀ p : V, (∑' q, jointP π 0 p c * (tau π q c * secondMoment π c))
      = jointP π 0 p c * ((∑' q, tau π q c) * secondMoment π c) := by
    intro p
    rw [show (∑' q, jointP π 0 p c * (tau π q c * secondMoment π c))
        = ∑' q, (jointP π 0 p c * secondMoment π c) * tau π q c from
      tsum_congr fun q => by ring]
    rw [ENNReal.tsum_mul_left]
    ring
  rw [hstep, show (∑' p, ∑' q, jointP π 0 p c * (tau π q c * secondMoment π c))
      = ∑' p, jointP π 0 p c * ((∑' q, tau π q c) * secondMoment π c) from
    tsum_congr hfac]
  rw [ENNReal.tsum_mul_right]

end PercLib.CriticalLRP.TreeExpansion.FivePoint
