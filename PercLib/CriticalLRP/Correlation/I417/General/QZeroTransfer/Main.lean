/-
Accepted from Ultramath `smwzg77c3`, member `m5`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d10`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `q = 0` star moment as a supremum of finite truncations

The source object of Lemma I.4.17 at `p = 3`, `q = 0` is the one-copy star moment
`starMoment π x y p = ∫⁻ ω, 1(x ↔ y) |K_x(ω)|^p` of `I417Gen`.  Its landed labelled expansion is an
infinite sum over *all* label tuples `Fin p → V`, and every BK / tree-graph / correlation bound in
PercLib controls only finitely many labels, usually in finite volume.

This file provides the bridge in the direction an upper bound needs, and its converse:

* `starMoment_eq_iSup_labSum`, `starMoment_le_of_labSum_le`: the star moment is the supremum of
  its finite-label truncations, so a bound whose constants do not depend on the label family
  transfers to the source object;
* `exists_labSum_gt_of_lt`: conversely, a strict violation is already witnessed on a finite family
  of label tuples.  Together these make "prove it on finitely many labels" lossless;
* `starMoment_eq_iSup_truncStar`, `starMoment_le_of_truncStar_le`: the same with the cluster volume
  truncated to a finite vertex set, i.e. the finite-volume form;
* source-model specialisations at `p = 3` via
  `Orchestration.SourceModelData.connCubeVertexMass_eq_starMoment`, including the target's exact
  finite-real shape with `hgapRHS r y C3 C4 = C3 · polyK 3 0 y · χ⁴ + C4 · polyK 4 0 y · χ³`.

Nothing here assumes finiteness of any moment; the `ℝ≥0∞` statements have no side conditions, and
the single real-valued statement converts with `ENNReal.toReal_ofReal` applied only to the explicit
nonnegative right-hand side, so no `⊤ ↦ 0` conversion ever occurs.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroTransfer.Defs

/-! # Supremum identities and their transfer forms -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP

namespace Exhaustion

variable {V : Type*} [Countable V]

/-! ## Finite families of label tuples -/

theorem labSum_mono {π : Sym2 V → unitInterval} {x y : V} {p : ℕ} {F F' : Finset (Fin p → V)}
    (h : F ⊆ F') : labSum π x y p F ≤ labSum π x y p F' :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => bot_le

/-- **The star moment is the supremum of its finite-label truncations.** -/
theorem starMoment_eq_iSup_labSum (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    I417Gen.starMoment π x y p = ⨆ F : Finset (Fin p → V), labSum π x y p F := by
  rw [I417Gen.starMoment_eq_tsum_labelEvent, ENNReal.tsum_eq_iSup_sum]
  simp only [labSum]

/-- **Uniform finite-label bounds transfer to the source object.**  This is the form in which a
labelled BK/tree/correlation argument is usable: it must control every finite family of labels with
constants independent of that family. -/
theorem starMoment_le_of_labSum_le {π : Sym2 V → unitInterval} {x y : V} {p : ℕ} {B : ℝ≥0∞}
    (h : ∀ F : Finset (Fin p → V), labSum π x y p F ≤ B) : I417Gen.starMoment π x y p ≤ B := by
  rw [starMoment_eq_iSup_labSum]
  exact iSup_le h

/-- **Each finite-label truncation is dominated by the source star moment.** -/
theorem labSum_le_starMoment (π : Sym2 V → unitInterval) (x y : V) (p : ℕ)
    (F : Finset (Fin p → V)) : labSum π x y p F ≤ I417Gen.starMoment π x y p := by
  rw [starMoment_eq_iSup_labSum]
  exact le_iSup (fun F : Finset (Fin p → V) => labSum π x y p F) F

/-- **The finite-label form is not merely sufficient but equivalent**: a per-vertex bound holds for
the source star moment iff it holds for every finite family of label tuples. -/
theorem starMoment_le_iff_forall_labSum {π : Sym2 V → unitInterval} {x y : V} {p : ℕ}
    {B : ℝ≥0∞} : I417Gen.starMoment π x y p ≤ B ↔
      ∀ F : Finset (Fin p → V), labSum π x y p F ≤ B :=
  ⟨fun h F => (labSum_le_starMoment π x y p F).trans h, starMoment_le_of_labSum_le⟩

/-- **If the star moment strictly exceeds a bound, a finite family of labels already does.**
The compactness direction: any strict violation of the target is witnessed on finitely many label
tuples, so an exact small-model computation is a legitimate refutation. -/
theorem exists_labSum_gt_of_lt {π : Sym2 V → unitInterval} {x y : V} {p : ℕ} {B : ℝ≥0∞}
    (h : B < I417Gen.starMoment π x y p) : ∃ F : Finset (Fin p → V), B < labSum π x y p F := by
  rw [starMoment_eq_iSup_labSum] at h
  exact lt_iSup_iff.mp h

/-! ## Finite vertex sets -/

theorem truncMass_mono {ω : Config V} {x : V} {S S' : Finset V} (h : S ⊆ S') :
    truncMass ω x S ≤ truncMass ω x S' :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => bot_le

theorem measurable_truncMass (x : V) (S : Finset V) :
    Measurable fun ω : Config V => truncMass ω x S := by
  refine Finset.measurable_sum _ fun w _ => ?_
  exact measurable_const.indicator (measurableSet_cluster_mem x w)

theorem truncMass_le_cardFun (ω : Config V) (x : V) (S : Finset V) :
    truncMass ω x S ≤ Percolation.cardFun (cluster ω x) := by
  rw [truncMass]
  calc ∑ w ∈ S, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w
      ≤ ∑' w, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w := ENNReal.sum_le_tsum S
    _ = ((cluster ω x).encard : ℝ≥0∞) := tsum_indicator_eq_encard _
    _ = Percolation.cardFun (cluster ω x) := by rw [Percolation.cardFun_eq_encard]

/-- **The cluster cardinality is the supremum of its finite-set truncations.** -/
theorem iSup_truncMass (ω : Config V) (x : V) :
    (⨆ S : Finset V, truncMass ω x S) = Percolation.cardFun (cluster ω x) := by
  refine le_antisymm (iSup_le fun S => truncMass_le_cardFun ω x S) ?_
  rw [Percolation.cardFun_eq_encard, ← clusterVol_eq_encard, clusterVol_eq_tsum,
    ENNReal.tsum_eq_iSup_sum]
  simp only [truncMass]
  exact le_rfl

/-- **The cluster cardinality power is the supremum of its finite-set truncations.** -/
theorem iSup_truncMass_pow (ω : Config V) (x : V) (p : ℕ) :
    (⨆ S : Finset V, (truncMass ω x S) ^ p) = Percolation.cardFun (cluster ω x) ^ p := by
  rw [← iSup_truncMass ω x, ENNReal.iSup_pow]

/-- **The star moment is the supremum of its finite-volume truncations.** -/
theorem starMoment_eq_iSup_truncStar (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    I417Gen.starMoment π x y p = ⨆ S : Finset V, truncStar π x y p S := by
  have hfun : (fun ω : Config V => (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        Percolation.cardFun (cluster ω x) ^ p)
      = fun ω => ⨆ S : Finset V, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (truncMass ω x S) ^ p := by
    funext ω
    rw [← iSup_truncMass_pow ω x p, ENNReal.mul_iSup]
  have hmeas : ∀ S : Finset V, Measurable fun ω : Config V =>
      (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω * (truncMass ω x S) ^ p := by
    intro S
    exact (measurable_const.indicator (measurableSet_connSet x y)).mul
      ((measurable_truncMass x S).pow_const p)
  have hdir : Directed (· ≤ ·) fun S : Finset V => fun ω : Config V =>
      (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω * (truncMass ω x S) ^ p := by
    classical
    intro S S'
    have hsub1 : S ⊆ (S ∪ S' : Finset V) := Finset.subset_union_left
    have hsub2 : S' ⊆ (S ∪ S' : Finset V) := Finset.subset_union_right
    refine ⟨S ∪ S', fun ω => ?_, fun ω => ?_⟩
    · exact mul_le_mul_right (pow_le_pow_left' (truncMass_mono hsub1) p) _
    · exact mul_le_mul_right (pow_le_pow_left' (truncMass_mono hsub2) p) _
  simp only [I417Gen.starMoment, truncStar]
  calc ∫⁻ ω, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)
      = ∫⁻ ω, ⨆ S : Finset V, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (truncMass ω x S) ^ p ∂(edgeMeasure π) := by rw [hfun]
    _ = ⨆ S : Finset V, ∫⁻ ω, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (truncMass ω x S) ^ p ∂(edgeMeasure π) :=
        lintegral_iSup_directed (fun S => (hmeas S).aemeasurable) hdir

/-- **Uniform finite-volume bounds transfer to the source object.** -/
theorem starMoment_le_of_truncStar_le {π : Sym2 V → unitInterval} {x y : V} {p : ℕ} {B : ℝ≥0∞}
    (h : ∀ S : Finset V, truncStar π x y p S ≤ B) : I417Gen.starMoment π x y p ≤ B := by
  rw [starMoment_eq_iSup_truncStar]
  exact iSup_le h

/-- **The first moment `E|K_x|` is the supremum of its finite-volume truncations.**  This is the
`chi`-side companion of `starMoment_eq_iSup_truncStar`: with it, both sides of the target are
suprema over the same family of finite vertex sets. -/
theorem lintegral_cardFun_eq_iSup_truncMass (μ : Measure (Config V)) (x : V) :
    ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂μ
      = ⨆ S : Finset V, ∫⁻ ω, truncMass ω x S ∂μ := by
  have hfun : (fun ω : Config V => Percolation.cardFun (cluster ω x))
      = fun ω => ⨆ S : Finset V, truncMass ω x S := by
    funext ω
    exact (iSup_truncMass ω x).symm
  have hmeas : ∀ S : Finset V, Measurable fun ω : Config V => truncMass ω x S :=
    fun S => measurable_truncMass x S
  have hdir : Directed (· ≤ ·) fun S : Finset V => fun ω : Config V => truncMass ω x S := by
    classical
    intro S S'
    have hsub1 : S ⊆ (S ∪ S' : Finset V) := Finset.subset_union_left
    have hsub2 : S' ⊆ (S ∪ S' : Finset V) := Finset.subset_union_right
    exact ⟨S ∪ S', fun ω => truncMass_mono (ω := ω) hsub1,
      fun ω => truncMass_mono (ω := ω) hsub2⟩
  calc ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂μ
      = ∫⁻ ω, ⨆ S : Finset V, truncMass ω x S ∂μ := by rw [hfun]
    _ = ⨆ S : Finset V, ∫⁻ ω, truncMass ω x S ∂μ :=
        lintegral_iSup_directed (fun S => (hmeas S).aemeasurable) hdir

/-- **If the star moment strictly exceeds a bound, some finite vertex set already does.** -/
theorem exists_truncStar_gt_of_lt {π : Sym2 V → unitInterval} {x y : V} {p : ℕ} {B : ℝ≥0∞}
    (h : B < I417Gen.starMoment π x y p) : ∃ S : Finset V, B < truncStar π x y p S := by
  rw [starMoment_eq_iSup_truncStar] at h
  exact lt_iSup_iff.mp h

/-- **Each finite-volume truncation is dominated by the source star moment.** -/
theorem truncStar_le_starMoment (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) (S : Finset V) :
    truncStar π x y p S ≤ I417Gen.starMoment π x y p := by
  simp only [I417Gen.starMoment, truncStar]
  refine lintegral_mono fun ω => ?_
  exact mul_le_mul_right (pow_le_pow_left' (truncMass_le_cardFun ω x S) p) _

/-- **The finite-volume form is equivalent to the source statement.** -/
theorem starMoment_le_iff_forall_truncStar {π : Sym2 V → unitInterval} {x y : V} {p : ℕ}
    {B : ℝ≥0∞} : I417Gen.starMoment π x y p ≤ B ↔
      ∀ S : Finset V, truncStar π x y p S ≤ B :=
  ⟨fun h S => (truncStar_le_starMoment π x y p S).trans h, starMoment_le_of_truncStar_le⟩

end Exhaustion

open Exhaustion

namespace Orchestration
namespace SourceModelData

/-! ## The source model at `p = 3` -/

/-- **`E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` is the supremum of its finite-label truncations.** -/
theorem connCubeVertexMass_eq_iSup_labSum (M : SourceModelData) (r : ℝ) (y : M.V) :
    M.connCubeVertexMass r y =
      ⨆ F : Finset (Fin 3 → M.V), labSum (M.cutProb r) (0 : M.V) y 3 F := by
  rw [M.connCubeVertexMass_eq_starMoment]
  exact starMoment_eq_iSup_labSum (M.cutProb r) 0 y 3

/-- **`E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` is the supremum of its finite-volume truncations.** -/
theorem connCubeVertexMass_eq_iSup_truncStar (M : SourceModelData) (r : ℝ) (y : M.V) :
    M.connCubeVertexMass r y =
      ⨆ S : Finset M.V, truncStar (M.cutProb r) (0 : M.V) y 3 S := by
  rw [M.connCubeVertexMass_eq_starMoment]
  exact starMoment_eq_iSup_truncStar (M.cutProb r) 0 y 3

/-- **A uniform finite-label bound at `p = 3` gives the per-vertex bound of the source model.** -/
theorem connCubeVertexMass_le_of_labSum_le (M : SourceModelData) (r : ℝ) (y : M.V)
    {B : ℝ≥0∞}
    (h : ∀ F : Finset (Fin 3 → M.V), labSum (M.cutProb r) (0 : M.V) y 3 F ≤ B) :
    M.connCubeVertexMass r y ≤ B := by
  rw [M.connCubeVertexMass_eq_starMoment]
  exact starMoment_le_of_labSum_le h

/-- **A uniform finite-volume bound at `p = 3` gives the per-vertex bound of the source model.** -/
theorem connCubeVertexMass_le_of_truncStar_le (M : SourceModelData) (r : ℝ) (y : M.V)
    {B : ℝ≥0∞}
    (h : ∀ S : Finset M.V, truncStar (M.cutProb r) (0 : M.V) y 3 S ≤ B) :
    M.connCubeVertexMass r y ≤ B := by
  rw [M.connCubeVertexMass_eq_starMoment]
  exact starMoment_le_of_truncStar_le h

/-- **Any strict violation of a per-vertex bound is witnessed on finitely many labels.** -/
theorem exists_labSum_gt_of_connCubeVertexMass_gt (M : SourceModelData) (r : ℝ) (y : M.V)
    {B : ℝ≥0∞} (h : B < M.connCubeVertexMass r y) :
    ∃ F : Finset (Fin 3 → M.V), B < labSum (M.cutProb r) (0 : M.V) y 3 F := by
  rw [M.connCubeVertexMass_eq_starMoment] at h
  exact exists_labSum_gt_of_lt h

/-- **The target's exact finite-real shape from the finite-label bound.**  The hypothesis is the
per-vertex two-term estimate in its natural `ℝ≥0∞` parent on finitely many labels; the conclusion is
the target inequality for `(M.connCubeVertexMass r y).toReal` with the same constants and
`χ = (M.cutMassAt r 0).toReal`.  The right-hand side is an honest nonnegative real
(`hgapRHS_nonneg`), and the only conversion is `ENNReal.toReal_ofReal` applied to it. -/
theorem connCubeVertexMass_toReal_le_of_labSum_le (M : SourceModelData) (r : ℝ) (y : M.V)
    {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (h : ∀ F : Finset (Fin 3 → M.V), labSum (M.cutProb r) (0 : M.V) y 3 F ≤
      ENNReal.ofReal (M.hgapRHS r y C3 C4)) :
    (M.connCubeVertexMass r y).toReal ≤ M.hgapRHS r y C3 C4 := by
  have hle := M.connCubeVertexMass_le_of_labSum_le r y h
  have h1 : (M.connCubeVertexMass r y).toReal ≤
      (ENNReal.ofReal (M.hgapRHS r y C3 C4)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (M.hgapRHS_nonneg r y hC3 hC4)] at h1

/-- **The target's finite-real shape from the finite-volume bound**, same conversion. -/
theorem connCubeVertexMass_toReal_le_of_truncStar_le (M : SourceModelData) (r : ℝ) (y : M.V)
    {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (h : ∀ S : Finset M.V, truncStar (M.cutProb r) (0 : M.V) y 3 S ≤
      ENNReal.ofReal (M.hgapRHS r y C3 C4)) :
    (M.connCubeVertexMass r y).toReal ≤ M.hgapRHS r y C3 C4 := by
  have hle := M.connCubeVertexMass_le_of_truncStar_le r y h
  have h1 : (M.connCubeVertexMass r y).toReal ≤
      (ENNReal.ofReal (M.hgapRHS r y C3 C4)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (M.hgapRHS_nonneg r y hC3 hC4)] at h1

/-- **`chi = E_{β_c,r}|K_0|` is the supremum of its finite-volume truncations.** -/
theorem cutMassAt_eq_iSup_truncMass (M : SourceModelData) (r : ℝ) :
    M.cutMassAt r 0
      = ⨆ S : Finset M.V, ∫⁻ ω, truncMass ω (0 : M.V) S ∂(M.cutLaw r) := by
  have h : M.cutMassAt r 0 = ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r) := rfl
  rw [h]
  have h2 : (fun ω : Config M.V => clusterVol ω (0 : M.V))
      = fun ω => Percolation.cardFun (cluster ω (0 : M.V)) := by
    funext ω
    rw [clusterVol_eq_encard, Percolation.cardFun_eq_encard]
  rw [h2]
  exact lintegral_cardFun_eq_iSup_truncMass (M.cutLaw r) 0

end SourceModelData
end Orchestration

end PercLib.CriticalLRP
