/- Coordinator-assembled total of the marked-depth coefficients.
Production base: `80951640d68930030716cfd90af38fee830518f2`.
The strict candidate was `.scratch/verification/marked-count-total/Main.lean`. -/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Relabel.Defs
public import PercLib.CriticalLRP.Correlation.I417.Marked.Numerics
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.ExactCount.Exact

/-! The exact total of the marked-depth coefficients. -/

@[expose] public section

namespace PercLib.CriticalLRP.I417Marked

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.I417MarkedRelabel (finLabelEquiv ltOnMapLabelEquiv)

/-- The marked fully labelled shape family, before pairing with its marked position, has
cardinality `2^p * M(p)`. -/
theorem card_ltOn_label_eq_plane_count (p : ℕ) :
    Fintype.card (LTon (Label p) (Finset.univ : Finset (Label p))) =
      2 ^ p * VolumeMoments.M p := by
  let e := ltOnMapLabelEquiv (finLabelEquiv p)
  exact (Fintype.card_congr e).symm.trans ((Fintype.card_congr
    (Real.ltonUnivEquivLT (Fin (p + 1)))).trans (RTree.card_LT_fin_eq p))

/-- The coefficient function totals exactly `2^p`. -/
theorem card_markedShapes_eq_plane_count (p : ℕ) :
    (markedShapes p).card = 2 ^ p * VolumeMoments.M p := by
  rw [card_markedShapes, card_ltOn_label_eq_plane_count]

/-- The marked-depth coefficients sum to the exact plane-family count. -/
theorem sum_markedCount_eq_plane_count (p : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 (p + 1), markedCount p ℓ) = 2 ^ p * VolumeMoments.M p := by
  rw [sum_markedCount, card_markedShapes_eq_plane_count]

/-- The product convention `M(p)` is the double factorial `(2p-1)!!`. -/
theorem M_eq_doubleFactorial_two_mul_sub_one (p : ℕ) :
    VolumeMoments.M p = Nat.doubleFactorial (2 * p - 1) := by
  cases p with
  | zero => rfl
  | succ m =>
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
      exact VolumeMoments.M_eq_doubleFactorial m

/-- The marked coefficients total `2^p * (2p-1)!!`, even at `p = 0`. -/
theorem sum_markedCount_eq_two_pow_mul_dfactorial (p : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 (p + 1), markedCount p ℓ) =
      2 ^ p * Nat.doubleFactorial (2 * p - 1) := by
  rw [sum_markedCount_eq_plane_count, M_eq_doubleFactorial_two_mul_sub_one]

end PercLib.CriticalLRP.I417Marked

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I417Marked.card_ltOn_label_eq_plane_count
#print axioms PercLib.CriticalLRP.I417Marked.card_markedShapes_eq_plane_count
#print axioms PercLib.CriticalLRP.I417Marked.sum_markedCount_eq_plane_count
#print axioms PercLib.CriticalLRP.I417Marked.sum_markedCount_eq_two_pow_mul_dfactorial
