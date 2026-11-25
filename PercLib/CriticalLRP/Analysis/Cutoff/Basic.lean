/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m2/Basic.lean ; imports migrated;
auxiliary definitions and probability instances are collected in `Defs.lean`.
-/

/-
Cutoff-law fidelity for Lemma I.4.18: elementary facts about the truncated two-point
function `T_{β_c,r}(x,y) = P_{β_c,r}(x ↔ y)`.

The point of the module is that reflexivity of the connection relation makes the *diagonal*
entry of `T` equal to `1` at **every** cutoff, hence the source's `χ = E|K|` is at least `1`
and the diagonal of the ℓ-fold power is at least `1` for every `ℓ` (`LowOrder.lean` derives
the ℓ = 3 consequence).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Defs

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The truncated law is a probability measure, so every event has mass at most `1`. -/
theorem cutLaw_le_one (r : ℝ) (s : Set (Config M.V)) : M.cutLaw r s ≤ 1 := by
  have h := measure_mono (μ := M.cutLaw r) (Set.subset_univ s)
  rwa [measure_univ] at h

theorem cutTwoPointE_eq_ofReal (r : ℝ) (x y : M.V) :
    M.cutTwoPointE r x y = ENNReal.ofReal (M.cutTwoPoint r x y) := by
  rw [cutTwoPointE, cutTwoPoint, Measure.real_def, ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (M.cutLaw_le_one r _)

theorem cutTwoPointE_le_one (r : ℝ) (x y : M.V) : M.cutTwoPointE r x y ≤ 1 :=
  M.cutLaw_le_one r _

theorem cutTwoPoint_nonneg (r : ℝ) (x y : M.V) : 0 ≤ M.cutTwoPoint r x y :=
  ENNReal.toReal_nonneg

theorem cutTwoPoint_le_one (r : ℝ) (x y : M.V) : M.cutTwoPoint r x y ≤ 1 := by
  rw [cutTwoPoint, Measure.real_def]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (M.cutLaw_le_one r _)

/-- `T_{β_c,r}(x,x) = 1`: the diagonal of the two-point matrix is `1` at every cutoff. -/
theorem cutTwoPointE_self_eq_one (r : ℝ) (x : M.V) : M.cutTwoPointE r x x = 1 := by
  have h : {ω : Config M.V | Connects ω x x} = Set.univ :=
    Set.eq_univ_of_forall fun ω => connects_refl ω x
  rw [cutTwoPointE, h, measure_univ]

theorem cutTwoPoint_self_eq_one (r : ℝ) (x : M.V) : M.cutTwoPoint r x x = 1 := by
  have h : {ω : Config M.V | Connects ω x x} = Set.univ :=
    Set.eq_univ_of_forall fun ω => connects_refl ω x
  rw [cutTwoPoint, Measure.real_def, h, measure_univ, ENNReal.toReal_one]

theorem cutTwoPointE_comm (r : ℝ) (x y : M.V) : M.cutTwoPointE r x y = M.cutTwoPointE r y x := by
  have h : {ω : Config M.V | Connects ω x y} = {ω : Config M.V | Connects ω y x} := by
    ext ω
    exact ⟨fun h => connects_symm h, fun h => connects_symm h⟩
  rw [cutTwoPointE, cutTwoPointE, h]

theorem cutTwoPoint_comm (r : ℝ) (x y : M.V) : M.cutTwoPoint r x y = M.cutTwoPoint r y x := by
  have h := M.cutTwoPointE_comm r x y
  rw [cutTwoPointE_eq_ofReal, cutTwoPointE_eq_ofReal] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (M.cutTwoPoint_nonneg r x y)
    (M.cutTwoPoint_nonneg r y x)).mp h

/-- The *uncut* two-point function of `Defs.lean` also has unit diagonal, for every `β`. -/
theorem twoPointE_self_eq_one (β : ℝ≥0) (x : M.V) :
    M.law β {ω : Config M.V | Connects ω x x} = 1 := by
  have h : {ω : Config M.V | Connects ω x x} = Set.univ :=
    Set.eq_univ_of_forall fun ω => connects_refl ω x
  rw [h, measure_univ]

theorem twoPoint_self_eq_one (β : ℝ≥0) (x : M.V) : M.twoPoint β x x = 1 := by
  have h : {ω : Config M.V | Connects ω x x} = Set.univ :=
    Set.eq_univ_of_forall fun ω => connects_refl ω x
  rw [twoPoint, Measure.real_def, h, measure_univ, ENNReal.toReal_one]

theorem twoPoint_comm (β : ℝ≥0) (x y : M.V) : M.twoPoint β x y = M.twoPoint β y x := by
  have h : {ω : Config M.V | Connects ω x y} = {ω : Config M.V | Connects ω y x} := by
    ext ω
    exact ⟨fun h => connects_symm h, fun h => connects_symm h⟩
  rw [twoPoint, twoPoint, h]

end SourceModelData

end PercLib.CriticalLRP.Orchestration
