/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m2/RowSum.lean ; imports migrated;
auxiliary definitions and probability instances are collected in `Defs.lean`.
-/

/-
Row sums of the truncated two-point function are the source's `χ = E_{β_c,r}|K|`.

Lemma I.4.18 uses `∑_y T(y,0) = E|K|` twice: in the far sum it produces `(E|K|)^{ℓ-3}`,
and in the near sum it produces `(E|K|)^{ℓ-4}` after one factor is paid for by the ball.
Both rest on the identity proved here, which holds at the *actual* truncated law and
requires no translation invariance: `∑_y P_{β_c,r}(x↔y) = E_{β_c,r}|K_x|` for every vertex
`x` (Tonelli over the cluster).  At `x = 0` the right-hand side is definitionally
`M.cutMoment 1 r`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Basic

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Row sums at the truncated law.** The row of the truncated two-point matrix at any
vertex `x` sums to the expected cluster volume of `x`. -/
theorem tsum_cutTwoPointE_eq_cutMassAt (r : ℝ) (x : M.V) :
    ∑' y, M.cutTwoPointE r x y = M.cutMassAt r x := by
  have hind : ∀ y : M.V,
      (fun ω : Config M.V => (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y) =
        {ω : Config M.V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    intro y
    funext ω
    by_cases hy : Connects ω x y
    · have hy' : y ∈ cluster ω x := mem_cluster_iff.mpr hy
      rw [show (cluster ω x).indicator (fun _ => (1:ℝ≥0∞)) y = 1 from Set.indicator_of_mem hy' _,
        show ({ω : Config M.V | Connects ω x y}).indicator (fun _ => (1:ℝ≥0∞)) ω = 1 from
          Set.indicator_of_mem (show ω ∈ {ω : Config M.V | Connects ω x y} from hy) _]
    · have hy' : y ∉ cluster ω x := fun hh => hy (mem_cluster_iff.mp hh)
      rw [show (cluster ω x).indicator (fun _ => (1:ℝ≥0∞)) y = 0 from
          Set.indicator_of_notMem hy' _,
        show ({ω : Config M.V | Connects ω x y}).indicator (fun _ => (1:ℝ≥0∞)) ω = 0 from
          Set.indicator_of_notMem (show ω ∉ {ω : Config M.V | Connects ω x y} from hy) _]
  have hInt : ∀ y : M.V,
      ∫⁻ ω, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(M.cutLaw r) =
        M.cutTwoPointE r x y := by
    intro y
    rw [hind y, lintegral_indicator (measurableSet_connects x y), setLIntegral_one,
      cutTwoPointE]
  have hmeas : ∀ y : M.V, AEMeasurable
      (fun ω : Config M.V => (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y)
      (M.cutLaw r) := by
    intro y
    rw [hind y]
    exact (measurable_const.indicator (measurableSet_connects x y)).aemeasurable
  have hkey : M.cutMassAt r x =
      ∫⁻ ω, ∑' y : M.V, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) y
        ∂(M.cutLaw r) := by
    rw [cutMassAt]
    exact lintegral_congr fun ω => clusterVol_eq_tsum ω x
  rw [hkey, lintegral_tsum hmeas]
  exact tsum_congr fun y => (hInt y).symm

/-- At the origin the truncated cluster mass is the source's `χ = E_{β_c,r}|K|`. -/
theorem cutMassAt_zero_eq_cutMoment (r : ℝ) : M.cutMassAt r 0 = M.cutMoment 1 r := by
  simp [cutMassAt, cutMoment]

/-- **`χ` is the row sum of the truncated two-point matrix.** -/
theorem tsum_cutTwoPointE_eq_cutMoment (r : ℝ) :
    ∑' y, M.cutTwoPointE r 0 y = M.cutMoment 1 r := by
  rw [M.tsum_cutTwoPointE_eq_cutMassAt r 0, M.cutMassAt_zero_eq_cutMoment r]

/-- `χ = E_{β_c,r}|K| ≥ 1`, because the cluster of `0` contains `0`.  (This is what makes the
source's substitution `χ ⪰ r^α` harmless at small `r`, and it is why the `ℓ = 3` line of
Lemma I.4.18 cannot be discharged by `|B_R| χ^{ℓ-4}`.) -/
theorem one_le_cutMoment_one (r : ℝ) : 1 ≤ M.cutMoment 1 r := by
  rw [← M.tsum_cutTwoPointE_eq_cutMoment r]
  calc (1 : ℝ≥0∞) = M.cutTwoPointE r 0 0 := (M.cutTwoPointE_self_eq_one r 0).symm
    _ ≤ ∑' y, M.cutTwoPointE r 0 y := ENNReal.le_tsum 0

/-- The row sum written with `ENNReal.ofReal` of the real-valued two-point function, the form
in which the source's `∑_y T(y,0) = E|K|` is stated. -/
theorem tsum_ofReal_cutTwoPoint_eq_cutMoment (r : ℝ) :
    ∑' y, ENNReal.ofReal (M.cutTwoPoint r 0 y) = M.cutMoment 1 r := by
  rw [← M.tsum_cutTwoPointE_eq_cutMoment r]
  exact tsum_congr fun y => (M.cutTwoPointE_eq_ofReal r 0 y).symm

end SourceModelData

end PercLib.CriticalLRP.Orchestration
