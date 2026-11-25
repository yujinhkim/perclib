/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Normalized defect bounds and first-moment reductions

Reviewed from Ultramath `smwtrtcqs`, member `m5`, `ModelI411.lean`.
-/

module

/-
Model-level Lemma I.4.11 at an arbitrary normalized norm.

The abstract normalized inequality `I411.lemma_I_4_11_of_finite` is stated for any
translation-invariant nonnegative kernel `J` on `Fin d → ℤ`.  The source model's cutoff
kernel `M.cutKernel r` is such a kernel for every `r`, by `KernelPower.cutKernel_shift`,
and `M.cutLaw r` *is* its `longRangeMeasure`.  This file instantiates the abstract
theorem at that kernel and identifies its three statistics with the model's own
`M.cutMassAt r 0`, `E1Sign.pairMass M r` and `E1Sign.connMass M r`, giving the paper's

  `𝓔_{1,r} ≤ |B_r|⁻¹ ∑_{y∈B_r} ∇_r(0,y)`

with `∇_r` the cutoff triangle diagram `E1Sign.cutTriangleNabla`, under a finite first
cutoff moment and finiteness of the windowed triangle diagram.  No second or third
moment is assumed: the joint window moment is derived from the first moment.
-/

public import PercLib.CriticalLRP.Analysis.Cutoff.Defect.Triangle.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect
public import PercLib.CriticalLRP.Analysis.KernelPower.Model
public import PercLib.CriticalLRP.VolumeMoments.SecondMoment
public import PercLib.CriticalLRP.Correlation.HvolRootIndependence

/-! # Arbitrary-norm I.4.11 comparisons -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- The cutoff edge probabilities are shift invariant. -/
theorem cutProb_shift_invariant (r : ℝ) (a : M.V) (e : Sym2 M.V) :
    bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit
        (Sym2.map (fun x => x + a) e)
      = bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e :=
  bernoulliEdgeProb_shift (KernelPower.cutKernel_shift M r) (M.cutKernel_nonneg r) M.betaCrit a e

/-- Every cutoff edge probability is strictly below one. -/
theorem cutProb_lt_one' (r : ℝ) (e : Sym2 M.V) :
    bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e < 1 :=
  bernoulliEdgeProb_lt_one (M.cutKernel_nonneg r) M.betaCrit e

/-- The model's own cutoff law is the `edgeMeasure` of its Bernoulli edge probabilities. -/
theorem cutLaw_eq_edgeMeasure (r : ℝ) :
    M.cutLaw r = edgeMeasure (bernoulliEdgeProb (M.cutKernel r)
      (M.cutKernel_nonneg r) M.betaCrit) := rfl

/-- **Second cutoff moment from the first, at an arbitrary normalized norm.**

This is the model-level form of `Hvol.cutoffSecondMoment_ne_top_of_firstMoment`, which was
proved for the `linfNorm` kernel only.  The proof only uses shift invariance of the edge
probabilities and `|K_o|² ≤ (E|K_o|)³`. -/
theorem cutMoment_two_ne_top_of_one (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) :
    M.cutMoment 2 r ≠ ⊤ := by
  have hshift : ∀ (a : M.V) (e : Sym2 M.V),
      bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit
          (Sym2.map (fun x => x + a) e)
        = bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e :=
    cutProb_shift_invariant M r
  have h1' : (∫⁻ ω, clusterVol ω (0 : M.V)
      ∂(edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r)
        M.betaCrit))) ≠ ⊤ := by
    simpa only [SourceModelData.cutMoment, SourceModelData.cutLaw, longRangeMeasure,
      pow_one] using h1
  have hS : ∀ a : M.V, (∫⁻ ω, clusterVol ω a
        ∂(edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r)
          M.betaCrit)))
      ≤ ∫⁻ ω, clusterVol ω (0 : M.V)
        ∂(edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r)
          M.betaCrit)) :=
    fun a => le_of_eq (lintegral_clusterVol_shift_invariant _ hshift a)
  have h2 := lintegral_clusterVol_sq_ne_top
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)
    (cutProb_lt_one' M r) (0 : M.V) hS h1'
  simpa only [SourceModelData.cutMoment, SourceModelData.cutLaw, longRangeMeasure,
    pow_two] using h2

end E1Sign
end PercLib.CriticalLRP

@[expose] public section

namespace PercLib.CriticalLRP
namespace E1Sign

attribute [local instance] Classical.propDecidable

open Orchestration

variable (M : SourceModelData)

/-- The model's joint window moment in `cardFun` form (the shape used by the abstract
I.4.11 assembly). -/
theorem pairMass_eq_cardFun (r : ℝ) :
    pairMass M r = ∫⁻ ω, Percolation.cardFun (cluster ω (0 : M.V)) *
      ∑ y ∈ ballF M r, Percolation.cardFun (cluster ω y) ∂(M.cutLaw r) := by
  rw [pairMass]
  refine lintegral_congr fun ω => ?_
  simp only [clusterVol, Percolation.cardFun_eq_encard]

/-- The model's connected window moment in `cardFun` form.

`|K|² · #{y ∈ B : y ∈ K} = #(B ∩ K) · (|K| · |K|)`. -/
theorem connMass_eq_cardFun (r : ℝ) :
    connMass M r = ∫⁻ ω,
      (((ballF M r).filter fun y => y ∈ cluster ω (0 : M.V)).card : ℝ≥0∞)
        * (Percolation.cardFun (cluster ω (0 : M.V)) *
            Percolation.cardFun (cluster ω (0 : M.V))) ∂(M.cutLaw r) := by
  rw [connMass]
  refine lintegral_congr fun ω => ?_
  have hsum : ∑ y ∈ ballF M r,
        (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
      = (((ballF M r).filter fun y => y ∈ cluster ω (0 : M.V)).card : ℝ≥0∞) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Set.indicator_apply]
  rw [hsum]
  simp only [clusterVol, Percolation.cardFun_eq_encard, pow_two]
  exact mul_comm _ _

/-- **The joint window moment is finite under a finite first cutoff moment.**

At an arbitrary normalized norm this is the model-level form of
`Hvol.cutoffJointSecondMoment_ne_top_of_firstMoment`. -/
theorem pairMass_ne_top_of_cutMoment_one (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) :
    pairMass M r ≠ ⊤ := by
  have hshift : ∀ (a : M.V) (e : Sym2 M.V),
      bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit
          (Sym2.map (fun x => x + a) e)
        = bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e :=
    cutProb_shift_invariant M r
  have h1' : (∫⁻ ω, clusterVol ω (0 : M.V)
      ∂(edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r)
        M.betaCrit))) ≠ ⊤ := by
    simpa only [SourceModelData.cutMoment, SourceModelData.cutLaw, longRangeMeasure,
      pow_one] using h1
  have hmean : ∀ y : M.V, (∫⁻ ω, clusterVol ω y
        ∂(edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r)
          M.betaCrit)))
      = ∫⁻ ω, clusterVol ω (0 : M.V)
        ∂(edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r)
          M.betaCrit)) := by
    intro y
    simpa only [clusterVol, Percolation.cardFun_eq_encard] using
      Hvol.hvol_cardFun hshift (0 : M.V) y
  have hsecond : ∀ y : M.V, (∫⁻ ω, Percolation.cardFun (cluster ω y) *
      Percolation.cardFun (cluster ω y)
      ∂(edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r)
        M.betaCrit))) ≠ ⊤ := by
    intro y
    have hc := lintegral_clusterVol_sq_ne_top
      (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)
      (cutProb_lt_one' M r) y (fun a => ?_) ?_
    · simpa only [clusterVol, Percolation.cardFun_eq_encard] using hc
    · rw [hmean a, hmean y]
    · rw [hmean y]; exact h1'
  have hs := joint_windowMoment_le_sum_second_moments
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit) (0 : M.V)
    (ballF M r)
  have hfin : (∫⁻ ω, Percolation.cardFun (cluster ω (0 : M.V)) *
      ∑ y ∈ ballF M r, Percolation.cardFun (cluster ω y)
      ∂(edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r)
        M.betaCrit))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hs
    rw [ENNReal.sum_ne_top]
    intro y _
    exact ENNReal.add_ne_top.mpr ⟨hsecond 0, hsecond y⟩
  simpa only [pairMass, SourceModelData.cutLaw, longRangeMeasure, clusterVol,
    Percolation.cardFun_eq_encard] using hfin

end E1Sign
end PercLib.CriticalLRP

@[expose] public section

namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- **Lemma I.4.11 at an arbitrary normalized norm (upper half).**

At the actual Definition I.1.5 cutoff law `M.cutLaw r`, the source defect
`𝓔_{1,r} = (|B_r| χ² - pairMass + connMass)/(|B_r| χ²)` satisfies

  `𝓔_{1,r} ≤ |B_r|⁻¹ ∑_{y∈B_r} ∇_r(0,y)`,

with `∇_r(0,y) = ∑_a ∑_b τ_r(0,a) τ_r(a,b) τ_r(b,y)` the windowed cutoff triangle
diagram of `E1Sign.cutTriangleNabla`.  The only premises are a finite first cutoff moment
and finiteness of the windowed triangle diagram; the joint window moment `pairMass` is
*derived* from the first moment, and no second or third moment is assumed. -/
theorem cE1_le_windowTriangle (r : ℝ) (hB : (ballF M r).Nonempty)
    (h1 : M.cutMoment 1 r ≠ ⊤)
    (hD : windowTriangle M r (ballF M r) ≠ ⊤) :
    VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
        (connMass M r).toReal ((M.ball r).ncard : ℝ) ≤
      ((M.ball r).ncard : ℝ)⁻¹ * (windowTriangle M r (ballF M r)).toReal := by
  have hJfin := pairMass_ne_top_of_cutMoment_one M r h1
  have hAfin : (∑' w : M.V, twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r)
      M.betaCrit (0 : M.V) w) ≠ ⊤ := by
    rw [← lintegral_clusterVol_eq_tsum_twoPoint (M.cutKernel_nonneg r) M.betaCrit
      (0 : M.V)]
    simpa only [SourceModelData.cutMoment, SourceModelData.cutLaw, longRangeMeasure,
      pow_one] using h1
  have hD' : (∑ y ∈ ballF M r, ∑' a : M.V, ∑' b : M.V,
      twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit 0 a *
        twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit a b *
          twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit b y) ≠ ⊤ := by
    rw [← windowTriangle_eq]
    exact hD
  have hJfin' : (∫⁻ ω, Percolation.cardFun (cluster ω (0 : M.V)) *
      ∑ y ∈ ballF M r, Percolation.cardFun (cluster ω y)
      ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)) ≠ ⊤ := by
    simpa only [pairMass_eq_cardFun, SourceModelData.cutLaw] using hJfin
  have h := I411.lemma_I_4_11_of_finite (d := M.d) (J := M.cutKernel r)
    (KernelPower.cutKernel_shift M r) (M.cutKernel_nonneg r) M.betaCrit
    (ballF M r) hB hAfin hJfin' hD'
  simpa only [SourceModelData.cutMassAt, SourceModelData.cutLaw, longRangeMeasure,
    pairMass_eq_cardFun, connMass_eq_cardFun, card_ballF, windowTriangle_eq] using h

end E1Sign
end PercLib.CriticalLRP

@[expose] public section

namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- `τ_r` is the model's own `cutTwoPointE`. -/
theorem cutTau_eq_cutTwoPointE (r : ℝ) (x y : M.V) :
    cutTau M r x y = M.cutTwoPointE r x y := rfl

/-- Every cutoff two-point probability is at most the uncut one, in `ofReal` form. -/
theorem cutTau_le_ofReal_twoPoint (r : ℝ) (x y : M.V) :
    cutTau M r x y ≤ ENNReal.ofReal (M.twoPoint M.betaCrit x y) := by
  have h1 : M.cutTwoPointE r x y ≤ M.twoPointE M.betaCrit x y :=
    M.cutTwoPointE_le_twoPointE r x y
  have h2 : M.twoPointE M.betaCrit x y
      = ENNReal.ofReal (M.twoPoint M.betaCrit x y) := by
    rw [SourceModelData.twoPoint, SourceModelData.twoPointE, Measure.real_def,
      ENNReal.ofReal_toReal]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (M.law_le_one M.betaCrit _)
  rw [cutTau_eq_cutTwoPointE, ← h2]
  exact h1

/-- The cutoff triangle diagram is dominated by the paper's uncut open triangle
`∇_{β_c}(0,y)` of `BallAverage.openTriangleNabla`. -/
theorem cutTriangleNabla_le_openTriangleNabla (r : ℝ) (x : M.V) :
    cutTriangleNabla M r x ≤ BallAverage.openTriangleNabla M x := by
  refine ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun b => ?_
  gcongr
  · exact cutTau_le_ofReal_twoPoint M r 0 a
  · exact cutTau_le_ofReal_twoPoint M r a b
  · exact cutTau_le_ofReal_twoPoint M r b x

/-- **Lemma I.4.11 at an arbitrary normalized norm, in the paper's uncut form.**

  `𝓔_{1,r} ≤ |B_r|⁻¹ ∑_{y∈B_r} ∇_{β_c}(0,y)`,

where `∇_{β_c}(0,y)` is the uncut open triangle diagram `BallAverage.openTriangleNabla`
at the critical intensity.  Premises: finite first cutoff moment, finiteness of the
windowed uncut triangle sum, nonempty window.  The second and third moments are not
assumed; the joint window moment is derived from the first moment. -/
theorem cE1_le_windowOpenTriangle (r : ℝ) (hB : (ballF M r).Nonempty)
    (h1 : M.cutMoment 1 r ≠ ⊤)
    (hN : (∑ y ∈ ballF M r, BallAverage.openTriangleNabla M y) ≠ ⊤) :
    VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
        (connMass M r).toReal ((M.ball r).ncard : ℝ) ≤
      ((M.ball r).ncard : ℝ)⁻¹ *
        (∑ y ∈ ballF M r, BallAverage.openTriangleNabla M y).toReal := by
  have hmono : windowTriangle M r (ballF M r)
      ≤ ∑ y ∈ ballF M r, BallAverage.openTriangleNabla M y := by
    rw [windowTriangle_eq]
    exact Finset.sum_le_sum fun y _ => cutTriangleNabla_le_openTriangleNabla M r y
  have hDcut : windowTriangle M r (ballF M r) ≠ ⊤ := ne_top_of_le_ne_top hN hmono
  have htoReal : (windowTriangle M r (ballF M r)).toReal
      ≤ (∑ y ∈ ballF M r, BallAverage.openTriangleNabla M y).toReal :=
    ENNReal.toReal_mono hN hmono
  refine (cE1_le_windowTriangle M r hB h1 hDcut).trans ?_
  exact mul_le_mul_of_nonneg_left htoReal (by positivity)

/-- **The sandwich form of Lemma I.4.11 at an arbitrary normalized norm.**

Both the (landed) sign half and the (new) uncut window-triangle upper half at the actual
cutoff law, from a single first-moment premise. -/
theorem cE1_mem_Icc_windowOpenTriangle (r : ℝ) (hB : (ballF M r).Nonempty)
    (h1 : M.cutMoment 1 r ≠ ⊤)
    (hN : (∑ y ∈ ballF M r, BallAverage.openTriangleNabla M y) ≠ ⊤) :
    0 ≤ VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
          (connMass M r).toReal ((M.ball r).ncard : ℝ) ∧
      VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
          (connMass M r).toReal ((M.ball r).ncard : ℝ) ≤
        ((M.ball r).ncard : ℝ)⁻¹ *
          (∑ y ∈ ballF M r, BallAverage.openTriangleNabla M y).toReal :=
  ⟨cE1_nonneg M r (cutMoment_two_ne_top_of_one M r h1),
    cE1_le_windowOpenTriangle M r hB h1 hN⟩

end E1Sign
end PercLib.CriticalLRP

@[expose] public section

namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- **Lemma I.4.7 sign+upper bound with only a first-moment premise.**

The landed `E1Sign.cE1_mem_Icc` assumes a finite *second* cutoff moment.  At an arbitrary
normalized norm that second moment follows from the first (`cutMoment_two_ne_top_of_one`),
so the sandwich holds under the first-moment premise alone. -/
theorem cE1_mem_Icc_of_cutMoment_one (r : ℝ) (hr : 0 ≤ r)
    (h1 : M.cutMoment 1 r ≠ ⊤) :
    0 ≤ VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
          (connMass M r).toReal ((M.ball r).ncard : ℝ) ∧
      VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
          (connMass M r).toReal ((M.ball r).ncard : ℝ) ≤
        (connMass M r).toReal
          / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2) :=
  cE1_mem_Icc M r hr (cutMoment_two_ne_top_of_one M r h1)

/-- The `hE1` hypothesis of `ChiLower` from a first-moment bound on the ray. -/
theorem chiLower_E1_nonneg_of_cutMoment_one (r₀ : ℝ)
    (h1 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 1 r ≠ ⊤) :
    ∀ t : ℝ, r₀ ≤ t → 0 ≤ VolumeMoments.cE1 (M.cutMassAt t 0).toReal
      (pairMass M t).toReal (connMass M t).toReal ((M.ball t).ncard : ℝ) :=
  chiLower_E1_nonneg M r₀ (fun t ht => cutMoment_two_ne_top_of_one M t (h1 t ht))

end E1Sign
end PercLib.CriticalLRP

@[expose] public section

namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- The cutoff window `B_r` is nonempty for every nonnegative radius (it contains the
origin), so the `Nonempty` premise of the I.4.11 statements is automatic for `r ≥ 0`. -/
theorem ballF_nonempty_of_nonneg {r : ℝ} (hr : 0 ≤ r) : (ballF M r).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_ballF]
  change M.S.ρ (toVec (0 : M.V)) ≤ r
  have h0 : toVec (0 : M.V) = 0 := by
    funext i
    simp [toVec]
  rw [h0, M.S.ρ_zero]
  exact hr

/-- The windowed uncut triangle sum is the landed `BallAverage.ballSum` of the open
triangle. -/
theorem sum_ballF_openTriangleNabla (r : ℝ) :
    (∑ y ∈ ballF M r, BallAverage.openTriangleNabla M y)
      = BallAverage.ballSum M (BallAverage.openTriangleNabla M) r := by
  rw [BallAverage.ballSum, tsum_eq_sum (s := ballF M r)]
  · exact Finset.sum_congr rfl fun y hy => by
      rw [Set.indicator_of_mem ((mem_ballF M).mp hy)]
  · intro x hx
    rw [Set.indicator_of_notMem]
    exact fun h => hx ((mem_ballF M).mpr h)

/-- **Lemma I.4.11 at an arbitrary normalized norm, paper notation.**

For `r ≥ 0`, finite first cutoff moment and finite `ballSum` of the uncut open triangle:

  `𝓔_{1,r} ≤ |B_r|⁻¹ · (∑_{x∈B_r} ∇_{β_c}(0,x))`,

the `BallAverage.ballSum` being the unnormalized lattice-ball sum `∑_{x∈B_r}`. -/
theorem cE1_le_ballSum_openTriangle (r : ℝ) (hr : 0 ≤ r)
    (h1 : M.cutMoment 1 r ≠ ⊤)
    (hN : BallAverage.ballSum M (BallAverage.openTriangleNabla M) r ≠ ⊤) :
    VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
        (connMass M r).toReal ((M.ball r).ncard : ℝ) ≤
      ((M.ball r).ncard : ℝ)⁻¹ *
        (BallAverage.ballSum M (BallAverage.openTriangleNabla M) r).toReal := by
  have hN' : (∑ y ∈ ballF M r, BallAverage.openTriangleNabla M y) ≠ ⊤ := by
    rw [sum_ballF_openTriangleNabla]
    exact hN
  simpa only [sum_ballF_openTriangleNabla] using
    cE1_le_windowOpenTriangle M r (ballF_nonempty_of_nonneg M hr) h1 hN'

/-- The same upper bound with `cE1`'s sign half, in `ballSum` form. -/
theorem cE1_mem_Icc_ballSum_openTriangle (r : ℝ) (hr : 0 ≤ r)
    (h1 : M.cutMoment 1 r ≠ ⊤)
    (hN : BallAverage.ballSum M (BallAverage.openTriangleNabla M) r ≠ ⊤) :
    0 ≤ VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
          (connMass M r).toReal ((M.ball r).ncard : ℝ) ∧
      VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
          (connMass M r).toReal ((M.ball r).ncard : ℝ) ≤
        ((M.ball r).ncard : ℝ)⁻¹ *
          (BallAverage.ballSum M (BallAverage.openTriangleNabla M) r).toReal :=
  ⟨cE1_nonneg M r (cutMoment_two_ne_top_of_one M r h1),
    cE1_le_ballSum_openTriangle M r hr h1 hN⟩

end E1Sign
end PercLib.CriticalLRP

@[expose] public section

namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- **The excluded-expectation bound of (I.4.5)–(I.4.7) from a first-moment premise.**

Strengthens the landed `E1Sign.exclMoment_le` at arbitrary normalized norm: the landed
statement assumes a finite second cutoff moment, here derived from the first. -/
theorem exclMoment_le_of_cutMoment_one (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) :
    I411.exclMoment (M.cutProb r) (0 : M.V) (ballF M r)
      ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 :=
  exclMoment_le M r (cutMoment_two_ne_top_of_one M r h1)

/-- The normalized excluded rate is nonnegative from a first-moment premise. -/
theorem exclRate_nonneg_of_cutMoment_one (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) :
    0 ≤ (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2 - (exclMass M r).toReal)
        / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2) :=
  exclRate_nonneg M r (cutMoment_two_ne_top_of_one M r h1)

end E1Sign
end PercLib.CriticalLRP

@[expose] public section

namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- The cutoff triangle form of I.4.11 with the `Nonempty` window premise discharged from
`r ≥ 0`. -/
theorem cE1_le_windowTriangle_of_nonneg (r : ℝ) (hr : 0 ≤ r)
    (h1 : M.cutMoment 1 r ≠ ⊤)
    (hD : windowTriangle M r (ballF M r) ≠ ⊤) :
    VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
        (connMass M r).toReal ((M.ball r).ncard : ℝ) ≤
      ((M.ball r).ncard : ℝ)⁻¹ * (windowTriangle M r (ballF M r)).toReal :=
  cE1_le_windowTriangle M r (ballF_nonempty_of_nonneg M hr) h1 hD

/-- The connected window moment is finite under a finite first cutoff moment. -/
theorem connMass_ne_top_of_cutMoment_one (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) :
    connMass M r ≠ ⊤ :=
  connMass_ne_top M r (cutMoment_two_ne_top_of_one M r h1)

end E1Sign
end PercLib.CriticalLRP
