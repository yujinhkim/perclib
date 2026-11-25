/- Validated real/extended-real bridge for the I.4.18 analytic assembly. -/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.KpowSum
public import PercLib.CriticalLRP.Analysis.Polygon.Core

open MeasureTheory Measure
open scoped ENNReal NNReal BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I418C
open PercLib.CriticalLRP.KernelPower

variable (M : SourceModelData)

/-- Every cutoff matrix-power entry is finite if the cutoff susceptibility is finite. -/
theorem cutKpow_ne_top_of_chi_ne_top (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ)
    (x y : M.V) : Kpow (M.cutTwoPointE r) n x y ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    classical
    rw [Kpow_zero]
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [deltaE]
    split_ifs <;> simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hχ) (M.cutKpow_entry r m x y)

/-- The `ENNReal` power of the cutoff two-point function, read in `ℝ`, is `polyK`. -/
theorem cutKpow_toReal_eq_polyK (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ)
    (x y : M.V) :
    (Kpow (M.cutTwoPointE r) n x y).toReal = polyK (M.cutTwoPoint r) n x y := by
  induction n generalizing x y with
  | zero =>
      classical
      by_cases h : x = y
      · subst y
        simp [Kpow_zero, deltaE, polyK_zero]
      · simp [Kpow_zero, deltaE, polyK_zero, h]
  | succ n ih =>
      rw [Kpow_succ, polyK_succ]
      have hfin : ∀ u : M.V, Kpow (M.cutTwoPointE r) n x u * M.cutTwoPointE r u y ≠ ⊤ :=
        fun u => ENNReal.mul_ne_top (M.cutKpow_ne_top_of_chi_ne_top r hχ n x u)
          (ne_top_of_le_ne_top ENNReal.one_ne_top (M.cutTwoPointE_le_one r u y))
      rw [ENNReal.tsum_toReal_eq hfin]
      refine tsum_congr fun u => ?_
      rw [ENNReal.toReal_mul, ih x u, M.cutTwoPointE_eq_ofReal,
        ENNReal.toReal_ofReal (M.cutTwoPoint_nonneg r u y)]

/-- Real-valued composition, obtained from `cutKpow_comp` with no additional hypothesis. -/
theorem cutPolyK_comp_toReal (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ) :
    polyK (M.cutTwoPoint r) (n + 3) (0 : M.V) 0 =
      ∑' y, polyK (M.cutTwoPoint r) 3 0 y * polyK (M.cutTwoPoint r) n y 0 := by
  rw [← M.cutKpow_toReal_eq_polyK r hχ (n + 3) 0 0, M.cutKpow_comp]
  have hfin : ∀ u : M.V,
      Kpow (M.cutTwoPointE r) 3 0 u * Kpow (M.cutTwoPointE r) n u 0 ≠ ⊤ :=
    fun u => ENNReal.mul_ne_top (M.cutKpow_ne_top_of_chi_ne_top r hχ 3 0 u)
      (M.cutKpow_ne_top_of_chi_ne_top r hχ n u 0)
  rw [ENNReal.tsum_toReal_eq hfin]
  refine tsum_congr fun u => ?_
  rw [ENNReal.toReal_mul, M.cutKpow_toReal_eq_polyK r hχ,
    M.cutKpow_toReal_eq_polyK r hχ]

end PercLib.CriticalLRP.Orchestration.SourceModelData
