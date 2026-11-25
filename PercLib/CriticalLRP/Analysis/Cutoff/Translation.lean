/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m2/Translation.lean ; imports migrated;
auxiliary definitions and probability instances are collected in `Defs.lean`.
-/

/-
Translation invariance of the range-truncated law, at the actual truncated law.

Lemma I.4.18's first step is "by translation-invariance and positive-definiteness of `T`, `T^ℓ`
is maximized on the diagonal".  Production
(`PercLib/CriticalLRP/CountableProduct/Lattice.lean`) supplies that invariance for a
translation-invariant kernel: `edgeMeasure_shift_invariant`, `twoPointFunction_shift`,
`twoPointFunction_eq_origin`, `connects_shiftConfig`.  This module instantiates it for the
*range-truncated* kernel `M.cutKernel r`, which is radial by construction, and draws the two
consequences Lemma I.4.18 uses:

* `cutTwoPoint_eq_sub`: `T_{β_c,r}(x,y) = T_{β_c,r}(0, y - x)`;
* `cutMassAt_eq_zero`: `E_{β_c,r}|K_x| = E_{β_c,r}|K_0|`, i.e. the source's `χ = E_{β_c,r}|K|`
  needs no subscript.

Nothing here is assumed beyond `SourceModelData`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.LowOrder
public import PercLib.CriticalLRP.CountableProduct.Lattice

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The truncated kernel is invariant under the edge translation `{x,y} ↦ {x+a, y+a}`,
because it is a function of `‖x - y‖` only. -/
theorem cutKernel_shift (r : ℝ) (a : M.V) (e : Sym2 M.V) :
    M.cutKernel r (Sym2.map (fun x => x + a) e) = M.cutKernel r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [Sym2.map_mk]
    simp only [cutKernel, cutRadialSym, radialSym_mk, SourceNormData.dist]
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hne : x + a ≠ y + a := fun hh => hxy (add_right_cancel hh)
      rw [ite_eq_right hxy, ite_eq_right hne]
      have hv : ((x + a) - (y + a) : M.V) = (x - y) := by
        funext i
        simp
      rw [hv]

/-- The edge-open probabilities of the truncated law are translation invariant. -/
theorem cutEdgeProb_shift (r : ℝ) (a : M.V) (e : Sym2 M.V) :
    bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit
        (Sym2.map (fun x => x + a) e) =
      bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e :=
  bernoulliEdgeProb_shift (fun a e => M.cutKernel_shift r a e) (M.cutKernel_nonneg r) M.betaCrit a e

/-- **The truncated law is invariant under lattice translations.** -/
theorem cutLaw_map_shiftConfig (r : ℝ) (a : M.V) :
    (M.cutLaw r).map (shiftConfig a) = M.cutLaw r := by
  rw [cutLaw, longRangeMeasure]
  exact edgeMeasure_shift_invariant _ (fun a e => M.cutEdgeProb_shift r a e) a

/-- **`T_{β_c,r}` is translation invariant.** -/
theorem cutTwoPoint_translate (r : ℝ) (a x y : M.V) :
    M.cutTwoPoint r (x + a) (y + a) = M.cutTwoPoint r x y := by
  have hinv := M.cutLaw_map_shiftConfig r a
  have hmp := Measure.map_apply (μ := M.cutLaw r) (measurable_shiftConfig a)
    (measurableSet_connects (x + a) (y + a))
  have hpre : shiftConfig a ⁻¹' {ω : Config M.V | Connects ω (x + a) (y + a)}
      = {ω : Config M.V | Connects ω x y} := by
    ext ω
    constructor
    · intro h
      have hb : Connects (shiftConfig (-a) (shiftConfig a ω)) ((x + a) + -a) ((y + a) + -a) :=
        connects_shiftConfig (-a) h
      rw [shiftConfig_neg_shift] at hb
      rwa [show (x + a) + -a = x by simp, show (y + a) + -a = y by simp] at hb
    · intro h
      exact connects_shiftConfig a h
  have hmain : (M.cutLaw r) {ω | Connects ω (x + a) (y + a)}
      = (M.cutLaw r) {ω | Connects ω x y} := by
    calc (M.cutLaw r) {ω | Connects ω (x + a) (y + a)}
        = (M.cutLaw r).map (shiftConfig a) {ω | Connects ω (x + a) (y + a)} := by rw [hinv]
      _ = (M.cutLaw r) (shiftConfig a ⁻¹' {ω | Connects ω (x + a) (y + a)}) := hmp
      _ = (M.cutLaw r) {ω | Connects ω x y} := by rw [hpre]
  simp only [cutTwoPoint, Measure.real_def]
  rw [hmain]

/-- **`T_{β_c,r}(x,y)` depends only on `y - x`.** -/
theorem cutTwoPoint_eq_sub (r : ℝ) (x y : M.V) :
    M.cutTwoPoint r x y = M.cutTwoPoint r 0 (y - x) := by
  have h := M.cutTwoPoint_translate r (-x) x y
  rw [show x + -x = (0 : M.V) by simp, show y + -x = y - x by simp [sub_eq_add_neg]] at h
  exact h.symm

/-- Translating a configuration translates its cluster volume with it. -/
theorem clusterVol_shiftConfig (a : M.V) (ω : Config M.V) (v : M.V) :
    clusterVol (shiftConfig a ω) (v + a) = clusterVol ω v := by
  rw [clusterVol_eq_encard, clusterVol_eq_encard, cluster_shiftConfig]
  have h := Set.encard_congr
    (Equiv.Set.image (fun u => u + a) (cluster ω v) (fun _ _ h => add_right_cancel h)).symm
  rw [h]

/-- **The truncated cluster mass does not depend on the vertex.** -/
theorem cutMassAt_translate (r : ℝ) (a x : M.V) :
    M.cutMassAt r (x + a) = M.cutMassAt r x := by
  have hlin : ∫⁻ ω, clusterVol ω (x + a) ∂((M.cutLaw r).map (shiftConfig a)) =
      ∫⁻ ω, clusterVol (shiftConfig a ω) (x + a) ∂(M.cutLaw r) :=
    lintegral_map (measurable_clusterVol (x + a)) (measurable_shiftConfig a)
  rw [M.cutLaw_map_shiftConfig r a] at hlin
  rw [cutMassAt, cutMassAt, hlin]
  exact lintegral_congr fun ω => M.clusterVol_shiftConfig a ω x

/-- `E_{β_c,r}|K_x| = E_{β_c,r}|K_0|` for every vertex `x`: the source's unadorned `χ`. -/
theorem cutMassAt_eq_zero (r : ℝ) (x : M.V) : M.cutMassAt r x = M.cutMassAt r 0 := by
  have h := M.cutMassAt_translate r x 0
  rwa [show (0 : M.V) + x = x by simp] at h

end SourceModelData

end PercLib.CriticalLRP.Orchestration
