/- Closed interface between the accepted cutoff matrix-power calculus and the real-valued
I.4.18 analytic assembly. The only remaining inputs are source analytic estimates. -/
module

public import PercLib.CriticalLRP.Analysis.Polygon.Model
public import PercLib.CriticalLRP.Analysis.Polygon.Bridge
public import PercLib.CriticalLRP.Analysis.KernelPower.Model

open MeasureTheory Measure
open scoped ENNReal NNReal BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I418C
open PercLib.CriticalLRP.KernelPower

variable (M : SourceModelData)

/-- Discharge the real matrix-power handoff from the accepted cutoff layer. Finite `χ` makes
all extended-real powers and their real sums finite; it is the only conversion hypothesis. -/
theorem source_powerInputs (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y) :
    PowerInputs (polyK (M.cutTwoPoint r)) M.triSelf (M.cutMassAt r 0).toReal := by
  refine ⟨?_, ?_, M.cutPolyK_comp_toReal r hχ, ?_, ?_, ?_, ?_, ?_, M.source_triSup r hTri hB2 hB3 hlink⟩
  · exact fun n x y => polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) n x y
  · exact fun x y => polyK_zero (M.cutTwoPoint r) x y
  · intro n
    have hsum : (∑' y : M.V, Kpow (M.cutTwoPointE r) 3 0 y *
        Kpow (M.cutTwoPointE r) n y 0) ≠ ⊤ := by
      rw [← M.cutKpow_comp r n]
      exact M.cutKpow_ne_top_of_chi_ne_top r hχ (n + 3) 0 0
    have hreal := ENNReal.summable_toReal hsum
    simpa only [ENNReal.toReal_mul, M.cutKpow_toReal_eq_polyK r hχ] using hreal
  · intro n
    simpa only [M.cutKpow_toReal_eq_polyK r hχ] using M.cutKpow_colSum_toReal r hχ n 0
  · intro n
    have hsum : (∑' x : M.V, Kpow (M.cutTwoPointE r) n x 0) ≠ ⊤ := by
      rw [M.cutKpow_colSum r n 0]
      exact ENNReal.pow_ne_top hχ
    have hreal := ENNReal.summable_toReal hsum
    simpa only [M.cutKpow_toReal_eq_polyK r hχ] using hreal
  · intro n hn y
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have h := M.cutKpow_entry r m y 0
    have hreal := ENNReal.toReal_mono (ENNReal.pow_ne_top hχ) h
    simpa only [M.cutKpow_toReal_eq_polyK r hχ, ENNReal.toReal_pow,
      Nat.succ_sub_one, Nat.add_sub_cancel] using hreal
  · rw [polyK_one]
    exact M.cutTwoPoint_self_eq_one r 0

/-- Real-valued diagonal maximality inherited from the genuine infinite-cutoff power. -/
theorem source_polyK_le_diag (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (ell : ℕ) (x : M.V) :
    polyK (M.cutTwoPoint r) ell 0 x ≤ polyK (M.cutTwoPoint r) ell 0 0 := by
  have h := PercLib.CriticalLRP.KernelPower.SourceModelData.cutTwoPoint_Kpow_le_diag M r ell 0 x
  change (Kpow (M.cutTwoPointE r) ell 0 x) ≤ (Kpow (M.cutTwoPointE r) ell 0 0) at h
  have hreal := ENNReal.toReal_mono (M.cutKpow_ne_top_of_chi_ne_top r hχ ell 0 0) h
  simpa only [M.cutKpow_toReal_eq_polyK r hχ] using hreal

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP.I418C

open PercLib.CriticalLRP Orchestration

/-- The analytic assembly without a manually supplied `PowerInputs` or diagonal hypothesis.
The remaining inputs are precisely finite-cutoff-susceptibility conversion, the uncut threefold
comparison/summability data, normalized ball count, and the first-moment lower comparison. -/
theorem source_polygon_bound_of_cutoff_data
    (M : SourceModelData)
    (r R trc : ℝ) (s : Finset M.V) {c₀ K cc : ℝ}
    (hr : 1 ≤ r) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hχfin : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = M.α / (4 * (M.d : ℝ)))
    (hfar : ∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y)
    (htailc : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc)
    (htrc : 0 ≤ trc)
    (hcard : (s.card : ℝ) ≤ K * R ^ (M.d : ℝ))
    (hR : R = r ^ (M.α / (2 * (M.d : ℝ))))
    (hχ : c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K / c₀) * (trc + r ^ (-cc)) *
        ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  exact source_polygon_bound M r R trc (M.cutMassAt r 0).toReal s hr hc₀ hK
    hB2 hB3 hlink (M.source_powerInputs r hχfin hTri hB2 hB3 hlink)
    hell hct hfar htailc htrc hcard hR hχ (fun x => M.source_polyK_le_diag r hχfin ell x)

end PercLib.CriticalLRP.I418C
