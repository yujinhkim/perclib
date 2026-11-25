/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` excluded RHS as a difference of three monotone marked window masses

Swarm `smwvauwsr`, member `m1`, direction `d1`.

The `p = 2` right-hand side of Hutchcroft, *Critical long-range percolation I*, Lemma I.4.1 is

`M.p2RHS r = E[|K| ∑_{y∈B_r, y∉K}|K_y|²] + 2 E[|K|² ∑_{y∈B_r, y∉K}|K_y|]`

(`SecondMoment/Defs`).  Both summands carry the *excluded* indicator `1(y ∉ K_0)`, which is
**antitone** in the configuration: it is the one feature of the `p = 2` RHS that the landed
`p = 1` pair/conn machinery (`OffCorner/PairMassRegularity`, `ConnMassRegularity`) does not
already handle, because every DCT comparison of those files needs an integrand that is
*monotone* in the cut-off radius.

This file removes that obstacle exactly, without any inequality loss.  On the event `y ∈ K_0`
the two clusters coincide, so `|K_y| = |K_0|` and

* `|K_0| · |K_y|²    = |K_0|³ · 1(y ∈ K_0) + |K_0| · 1(y ∉ K_0) · |K_y|²`,
* `|K_0|² · |K_y|    = |K_0|³ · 1(y ∈ K_0) + |K_0|² · 1(y ∉ K_0) · |K_y|`.

Summing over the closed window and integrating gives, with

* `quadPairMass r   = E[|K_0| ∑_{y∈B_r}|K_y|²]`,
* `sqLinPairMass r  = E[|K_0|² ∑_{y∈B_r}|K_y|]`,
* `connCubeMass r   = E[|K_0|³ · #(K_0 ∩ B_r)]`,

the identity `quadPairMass = connCubeMass + exclMassQuad` and
`sqLinPairMass = connCubeMass + exclMassSqLin`, hence

`p2RHS r + 3 · connCubeMass r = quadPairMass r + 2 · sqLinPairMass r`,

i.e. `p2RHS = quadPairMass + 2 sqLinPairMass - 3 connCubeMass`.  Each of the three new objects is
a **monotone** marked window sum (monotone in the cut-off radius and in the configuration), and
each is bounded by the fourth cut-off moment: `connCubeMass r ≤ cutMoment 4 r` and both pair
masses by `|B_r| (cutMoment 2 r + cutMoment 4 r)`.  Consequently the radius regularity of the
`p = 2` RHS reduces to the radius regularity of three monotone marked window sums, which is
exactly the shape the landed escape/box-change DCT handles.

No `sorry`, `admit`, `native_decide` or custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Finiteness
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairMassRegularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusFrozenCylinder
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Defs

/-!
# The monotone decomposition of the `p = 2` excluded RHS

The three monotone marked window masses, the exact two-term splits behind them, and the
resulting `p2RHS + 3 connCubeMass = quadPairMass + 2 sqLinPairMass` with the corresponding
majorants and finiteness statements.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The three monotone marked window masses

`quadPairFun`, `quadPairMass`, `sqLinPairFun`, `sqLinPairMass`, `connCubeFun` and `connCubeMass`
are defined, with their documentation, in `P2Regularity/Defs.lean`; this file imports them and
proves the splits, the majorants and the radius regularity. -/

/-! ## 2. Measurability of the three integrands -/

theorem measurable_markVol_pow (r : ℝ) (k : ℕ) :
    Measurable fun u : Sym2 M.V → ℝ => M.markVol r u ^ k :=
  (M.measurable_markVol r).pow_const k

theorem measurable_clusterVol_param (r : ℝ) (y : M.V) :
    Measurable fun u : Sym2 M.V → ℝ => clusterVol (atParameter (M.cutProb r) u) y :=
  (measurable_clusterVol y).comp (measurable_atParameter _)

theorem measurable_quadPairFun (r : ℝ) : Measurable (M.quadPairFun r) :=
  (M.measurable_markVol r).mul
    (Finset.measurable_sum _ fun y _ => (M.measurable_clusterVol_param r y).pow_const 2)

theorem measurable_sqLinPairFun (r : ℝ) : Measurable (M.sqLinPairFun r) :=
  (M.measurable_markVol_pow r 2).mul
    (Finset.measurable_sum _ fun y _ => M.measurable_clusterVol_param r y)

theorem measurable_connCubeFun (r : ℝ) : Measurable (M.connCubeFun r) :=
  (M.measurable_markVol_pow r 3).mul
    (Finset.measurable_sum _ fun y _ =>
      measurable_const.indicator
        ((measurableSet_cluster_mem (0 : M.V) y).preimage (measurable_atParameter _)))

/-! ## 3. The mark-space form of the two excluded terms -/

theorem exclMassQuad_eq_mark (r : ℝ) :
    M.exclMassQuad r = ∫⁻ u, M.markVol r u *
      ∑ y ∈ E1Sign.ballF M r,
        ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) y *
          clusterVol (atParameter (M.cutProb r) u) y ^ 2 ∂(markMeasure M.V) := by
  rw [exclMassQuad, E1Sign.cutLaw_eq M r, ← markMeasure_map_atParameter]
  refine lintegral_map ?_ (measurable_atParameter _)
  refine (measurable_clusterVol (0 : M.V)).mul (Finset.measurable_sum _ fun y _ => ?_)
  exact (measurable_const.indicator (measurableSet_cluster_mem (0 : M.V) y).compl).mul
    ((measurable_clusterVol y).pow_const 2)

theorem exclMassSqLin_eq_mark (r : ℝ) :
    M.exclMassSqLin r = ∫⁻ u, M.markVol r u ^ 2 *
      ∑ y ∈ E1Sign.ballF M r,
        ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) y *
          clusterVol (atParameter (M.cutProb r) u) y ∂(markMeasure M.V) := by
  rw [exclMassSqLin, E1Sign.cutLaw_eq M r, ← markMeasure_map_atParameter]
  refine lintegral_map ?_ (measurable_atParameter _)
  refine ((measurable_clusterVol (0 : M.V)).pow_const 2).mul
    (Finset.measurable_sum _ fun y _ => ?_)
  exact (measurable_const.indicator (measurableSet_cluster_mem (0 : M.V) y).compl).mul
    (measurable_clusterVol y)


/-- **Transfer of a measurable configuration functional to the mark space.** -/
theorem lintegral_mark_eq_cutLaw (f : Config M.V → ℝ≥0∞) (hf : Measurable f) (r : ℝ) :
    ∫⁻ u, f (atParameter (M.cutProb r) u) ∂(markMeasure M.V) = ∫⁻ ω, f ω ∂(M.cutLaw r) := by
  rw [E1Sign.cutLaw_eq M r, ← markMeasure_map_atParameter]
  exact (lintegral_map hf (measurable_atParameter _)).symm

/-! ## 4. The pointwise summand identities

On the event `y ∈ K_0` the clusters of `y` and of the origin coincide, so `|K_y| = |K_0|` and the
excluded indicator kills the other branch.  These are the `p = 2` companions of
`E1Sign.summand_split`. -/

/-- The `ℓ = 0` summand identity:
`|K_0| |K_y|² = |K_0|³ 1(y ∈ K_0) + |K_0| 1(y ∉ K_0) |K_y|²`. -/
theorem quad_summand_split (ω : Config M.V) (y : M.V) :
    clusterVol ω (0 : M.V) * clusterVol ω y ^ 2
      = clusterVol ω (0 : M.V) ^ 3 *
          (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
        + clusterVol ω (0 : M.V)
            * (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y *
                clusterVol ω y ^ 2) := by
  by_cases h : y ∈ cluster ω (0 : M.V)
  · have hconn : Connects ω (0 : M.V) y := mem_cluster_iff.mp h
    have hcc : clusterVol ω y = clusterVol ω (0 : M.V) :=
      (clusterVol_eq_of_connects hconn).symm
    rw [Set.indicator_of_mem h,
      Set.indicator_of_notMem (s := (cluster ω (0 : M.V))ᶜ) (by simpa using h), hcc]
    ring
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_mem (s := (cluster ω (0 : M.V))ᶜ) (by simpa using h)]
    ring

/-- The `ℓ = 1` summand identity:
`|K_0|² |K_y| = |K_0|³ 1(y ∈ K_0) + |K_0|² 1(y ∉ K_0) |K_y|`. -/
theorem sqLin_summand_split (ω : Config M.V) (y : M.V) :
    clusterVol ω (0 : M.V) ^ 2 * clusterVol ω y
      = clusterVol ω (0 : M.V) ^ 3 *
          (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
        + clusterVol ω (0 : M.V) ^ 2
            * (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y *
                clusterVol ω y) := by
  by_cases h : y ∈ cluster ω (0 : M.V)
  · have hconn : Connects ω (0 : M.V) y := mem_cluster_iff.mp h
    have hcc : clusterVol ω y = clusterVol ω (0 : M.V) :=
      (clusterVol_eq_of_connects hconn).symm
    rw [Set.indicator_of_mem h,
      Set.indicator_of_notMem (s := (cluster ω (0 : M.V))ᶜ) (by simpa using h), hcc]
    ring
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_mem (s := (cluster ω (0 : M.V))ᶜ) (by simpa using h)]
    ring

/-! ## 5. The pointwise integrand identities -/

theorem quadPairFun_apply (r : ℝ) (u : Sym2 M.V → ℝ) :
    M.quadPairFun r u = M.connCubeFun r u + M.markVol r u *
      ∑ y ∈ E1Sign.ballF M r,
        ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) y *
          clusterVol (atParameter (M.cutProb r) u) y ^ 2 := by
  simp only [quadPairFun, connCubeFun, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => quad_summand_split M _ y

theorem sqLinPairFun_apply (r : ℝ) (u : Sym2 M.V → ℝ) :
    M.sqLinPairFun r u = M.connCubeFun r u + M.markVol r u ^ 2 *
      ∑ y ∈ E1Sign.ballF M r,
        ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) y *
          clusterVol (atParameter (M.cutProb r) u) y := by
  simp only [sqLinPairFun, connCubeFun, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => sqLin_summand_split M _ y

/-! ## 6. The exact splits and the three-term identity -/

/-- **The `ℓ = 0` split**: the unexcluded quadratic window mass is the cubic connection mass plus
the excluded quadratic mass. -/
theorem quadPairMass_eq_connCube_add (r : ℝ) :
    M.quadPairMass r = M.connCubeMass r + M.exclMassQuad r := by
  rw [quadPairMass, connCubeMass, M.exclMassQuad_eq_mark r,
    ← lintegral_add_left (M.measurable_connCubeFun r)]
  exact lintegral_congr fun u => M.quadPairFun_apply r u

/-- **The `ℓ = 1` split**: the unexcluded linear window mass is the same cubic connection mass
plus the excluded linear mass. -/
theorem sqLinPairMass_eq_connCube_add (r : ℝ) :
    M.sqLinPairMass r = M.connCubeMass r + M.exclMassSqLin r := by
  rw [sqLinPairMass, connCubeMass, M.exclMassSqLin_eq_mark r,
    ← lintegral_add_left (M.measurable_connCubeFun r)]
  exact lintegral_congr fun u => M.sqLinPairFun_apply r u

/-- **The `p = 2` RHS is a difference of monotone marked window masses.**
`p2RHS + 3 connCubeMass = quadPairMass + 2 sqLinPairMass`; the coefficient `3` is exactly
`1 + 2`, i.e. the two excluded terms lose the *same* cubic connection term. -/
theorem p2RHS_add_three_mul_connCube (r : ℝ) :
    M.p2RHS r + 3 * M.connCubeMass r =
      M.quadPairMass r + 2 * M.sqLinPairMass r := by
  have h0 := M.quadPairMass_eq_connCube_add r
  have h1 := M.sqLinPairMass_eq_connCube_add r
  rw [p2RHS, h0, h1, two_mul, two_mul]
  ring

/-! ## 7. Majorants from the fourth cut-off moment -/

/-- The window count of `K_0 ∩ B_r` is at most `|K_0|`. -/
theorem windowSum_indicator_le_markVol (r : ℝ) (u : Sym2 M.V → ℝ) :
    (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y) ≤ M.markVol r u := by
  have hcl : (∑ y ∈ E1Sign.ballF M r,
      (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y)
      ≤ ∑' y : M.V,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y :=
    ENNReal.sum_le_tsum (E1Sign.ballF M r)
  calc (∑ y ∈ E1Sign.ballF M r,
      (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y)
      ≤ ∑' y : M.V,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y := hcl
    _ = M.markVol r u := (clusterVol_eq_tsum _ _).symm

/-- **`connCubeMass r ≤ cutMoment 4 r`.** -/
theorem connCubeMass_le_fourth (r : ℝ) : M.connCubeMass r ≤ M.cutMoment 4 r := by
  rw [connCubeMass, M.cutMoment_eq_mark 4 r]
  refine lintegral_mono fun u => ?_
  have hN := M.windowSum_indicator_le_markVol r u
  calc M.markVol r u ^ 3 *
        ∑ y ∈ E1Sign.ballF M r,
          (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y
      ≤ M.markVol r u ^ 3 * M.markVol r u := by gcongr
    _ = M.markVol r u ^ 4 := by ring

/-- **`quadPairMass r ≤ |B_r| (cutMoment 2 r + cutMoment 4 r)`.** -/
theorem quadPairMass_le (r : ℝ) :
    M.quadPairMass r ≤
      ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r) := by
  have hpt : ∀ u : Sym2 M.V → ℝ, M.quadPairFun r u ≤
      ∑ y ∈ E1Sign.ballF M r,
        (clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 2 +
          clusterVol (atParameter (M.cutProb r) u) y ^ 4) := by
    intro u
    simp only [quadPairFun, Finset.mul_sum]
    rw [show M.markVol r u = clusterVol (atParameter (M.cutProb r) u) (0 : M.V) from rfl]
    refine Finset.sum_le_sum fun y _ => ?_
    have h := ennnreal_mul_le_sq_add_sq
      (clusterVol (atParameter (M.cutProb r) u) (0 : M.V))
      (clusterVol (atParameter (M.cutProb r) u) y ^ 2)
    simpa [← pow_mul] using h
  calc M.quadPairMass r
      = ∫⁻ u, M.quadPairFun r u ∂(markMeasure M.V) := rfl
    _ ≤ ∫⁻ u, ∑ y ∈ E1Sign.ballF M r,
          (clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 2 +
            clusterVol (atParameter (M.cutProb r) u) y ^ 4) ∂(markMeasure M.V) :=
        lintegral_mono hpt
    _ = ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r) := by
        have hsum : ∫⁻ u, ∑ y ∈ E1Sign.ballF M r,
              (clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 2 +
                clusterVol (atParameter (M.cutProb r) u) y ^ 4) ∂(markMeasure M.V)
            = ∑ y ∈ E1Sign.ballF M r,
              ∫⁻ u, (clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 2 +
                clusterVol (atParameter (M.cutProb r) u) y ^ 4) ∂(markMeasure M.V) :=
          lintegral_finsetSum (E1Sign.ballF M r) fun y _ =>
            ((M.measurable_clusterVol_param r (0 : M.V)).pow_const 2).add
              ((M.measurable_clusterVol_param r y).pow_const 4)
        rw [hsum]
        have hterm : ∀ y ∈ E1Sign.ballF M r,
            (∫⁻ u, (clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 2 +
              clusterVol (atParameter (M.cutProb r) u) y ^ 4) ∂(markMeasure M.V))
              = M.cutMoment 2 r + M.cutMoment 4 r := by
          intro y _
          rw [show (∫⁻ u, (clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 2 +
              clusterVol (atParameter (M.cutProb r) u) y ^ 4) ∂(markMeasure M.V))
              = ∫⁻ ω, (clusterVol ω (0 : M.V) ^ 2 + clusterVol ω y ^ 4) ∂(M.cutLaw r) from
            M.lintegral_mark_eq_cutLaw _ (((measurable_clusterVol (0 : M.V)).pow_const 2).add
              ((measurable_clusterVol y).pow_const 4)) r]
          rw [lintegral_add_left ((measurable_clusterVol (0 : M.V)).pow_const 2),
            M.lintegral_clusterVol_pow_vertex r (0 : M.V) 2,
            M.lintegral_clusterVol_pow_vertex r y 4]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, E1Sign.card_ballF, nsmul_eq_mul]

/-- **`sqLinPairMass r ≤ |B_r| (cutMoment 2 r + cutMoment 4 r)`.** -/
theorem sqLinPairMass_le (r : ℝ) :
    M.sqLinPairMass r ≤
      ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r) := by
  have hpt : ∀ u : Sym2 M.V → ℝ, M.sqLinPairFun r u ≤
      ∑ y ∈ E1Sign.ballF M r,
        (clusterVol (atParameter (M.cutProb r) u) y ^ 2 +
          clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 4) := by
    intro u
    simp only [sqLinPairFun, Finset.mul_sum]
    rw [show M.markVol r u = clusterVol (atParameter (M.cutProb r) u) (0 : M.V) from rfl]
    refine Finset.sum_le_sum fun y _ => ?_
    have h := ennnreal_mul_le_sq_add_sq
      (clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 2)
      (clusterVol (atParameter (M.cutProb r) u) y)
    simpa [← pow_mul, add_comm] using h
  calc M.sqLinPairMass r
      = ∫⁻ u, M.sqLinPairFun r u ∂(markMeasure M.V) := rfl
    _ ≤ ∫⁻ u, ∑ y ∈ E1Sign.ballF M r,
          (clusterVol (atParameter (M.cutProb r) u) y ^ 2 +
            clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 4) ∂(markMeasure M.V) :=
        lintegral_mono hpt
    _ = ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r) := by
        have hsum : ∫⁻ u, ∑ y ∈ E1Sign.ballF M r,
              (clusterVol (atParameter (M.cutProb r) u) y ^ 2 +
                clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 4) ∂(markMeasure M.V)
            = ∑ y ∈ E1Sign.ballF M r,
              ∫⁻ u, (clusterVol (atParameter (M.cutProb r) u) y ^ 2 +
                clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 4) ∂(markMeasure M.V) :=
          lintegral_finsetSum (E1Sign.ballF M r) fun y _ =>
            ((M.measurable_clusterVol_param r y).pow_const 2).add
              ((M.measurable_clusterVol_param r (0 : M.V)).pow_const 4)
        rw [hsum]
        have hterm : ∀ y ∈ E1Sign.ballF M r,
            (∫⁻ u, (clusterVol (atParameter (M.cutProb r) u) y ^ 2 +
              clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 4) ∂(markMeasure M.V))
              = M.cutMoment 2 r + M.cutMoment 4 r := by
          intro y _
          rw [show (∫⁻ u, (clusterVol (atParameter (M.cutProb r) u) y ^ 2 +
              clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 4) ∂(markMeasure M.V))
              = ∫⁻ ω, (clusterVol ω y ^ 2 + clusterVol ω (0 : M.V) ^ 4) ∂(M.cutLaw r) from
            M.lintegral_mark_eq_cutLaw _ (((measurable_clusterVol y).pow_const 2).add
              ((measurable_clusterVol (0 : M.V)).pow_const 4)) r]
          rw [lintegral_add_left ((measurable_clusterVol y).pow_const 2),
            M.lintegral_clusterVol_pow_vertex r y 2,
            M.lintegral_clusterVol_pow_vertex r (0 : M.V) 4]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, E1Sign.card_ballF, nsmul_eq_mul]

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 8. Monotonicity of the three integrands in the cut-off radius

Each of the three new integrands is monotone in `r`: the cut-off clusters only grow, the mark
weight `|K_0|^k` grows with them, and the window `B_r` grows.  This is what the excluded
integrand of `p2RHS` itself lacks, and it is the whole reason for the decomposition. -/

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

theorem quadPairFun_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    M.quadPairFun r ≤ M.quadPairFun r' := by
  intro u
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  simp only [quadPairFun]
  have hvol : M.markVol r u ≤ M.markVol r' u :=
    M.clusterVol_atParameter_mono hr hr' hrr' u 0
  have hsum : (∑ y ∈ E1Sign.ballF M r,
        clusterVol (atParameter (M.cutProb r) u) y ^ 2)
      ≤ ∑ y ∈ E1Sign.ballF M r', clusterVol (atParameter (M.cutProb r') u) y ^ 2 := by
    refine le_trans (Finset.sum_le_sum fun y _ => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (M.ballF_mono hrr') fun _ _ _ => zero_le)
    exact pow_le_pow_left' (M.clusterVol_atParameter_mono hr hr' hrr' u y) 2
  exact mul_le_mul' hvol hsum

theorem sqLinPairFun_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    M.sqLinPairFun r ≤ M.sqLinPairFun r' := by
  intro u
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  simp only [sqLinPairFun]
  have hvol : M.markVol r u ^ 2 ≤ M.markVol r' u ^ 2 :=
    pow_le_pow_left' (M.clusterVol_atParameter_mono hr hr' hrr' u 0) 2
  have hsum : (∑ y ∈ E1Sign.ballF M r,
        clusterVol (atParameter (M.cutProb r) u) y)
      ≤ ∑ y ∈ E1Sign.ballF M r', clusterVol (atParameter (M.cutProb r') u) y := by
    refine le_trans (Finset.sum_le_sum fun y _ => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (M.ballF_mono hrr') fun _ _ _ => zero_le)
    exact M.clusterVol_atParameter_mono hr hr' hrr' u y
  exact mul_le_mul' hvol hsum

theorem connCubeFun_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    M.connCubeFun r ≤ M.connCubeFun r' := by
  intro u
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  simp only [connCubeFun]
  have hvol : M.markVol r u ^ 3 ≤ M.markVol r' u ^ 3 :=
    pow_le_pow_left' (M.clusterVol_atParameter_mono hr hr' hrr' u 0) 3
  have hstep : (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y)
      ≤ ∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r') u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y := by
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases hy : y ∈ cluster (atParameter (M.cutProb r) u) (0 : M.V)
    · have hmem : y ∈ cluster (atParameter (M.cutProb r') u) (0 : M.V) :=
        cluster_mono (fun e he => lt_of_lt_of_le he
          (Subtype.coe_le_coe.mpr (M.cutProb_mono hr hr' hrr' e))) 0 hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  have hsum : (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y)
      ≤ ∑ y ∈ E1Sign.ballF M r',
        (cluster (atParameter (M.cutProb r') u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y :=
    le_trans hstep (Finset.sum_le_sum_of_subset_of_nonneg (M.ballF_mono hrr')
      fun _ _ _ => zero_le)
  exact mul_le_mul' hvol hsum

/-! ## 9. The cluster of the origin is unchanged off the two error events

The excluded indicator and the connection mass need more than the volume comparison
`clusterVol_eq_of_notMem`: they need the *cluster itself* to be the same set at the two radii.
Off the box-change event and the escape event both inclusions hold, one from the box comparison at
the smaller radius and one from monotonicity of the edge probabilities. -/

theorem cluster_eq_of_notMem {r0 r R : ℝ} (hr0 : 0 < r0) (hrr : r0 ≤ r)
    {u : Sym2 M.V → ℝ} (hbox : u ∉ M.markBoxChange r0 r R)
    (hesc : u ∉ M.markEscapeAt r R (0 : M.V)) :
    cluster (atParameter (M.cutProb r) u) (0 : M.V) =
      cluster (atParameter (M.cutProb r0) u) (0 : M.V) := by
  have hr : 0 < r := lt_of_lt_of_le hr0 hrr
  refine le_antisymm ?_ ?_
  · refine M.cluster_subset_of_eq_on_box_gen (R := R) ?_ ?_
    · intro e he hmem
      exact M.lt_cutProb_r0_of_notMem_markBoxChange hbox he hmem
    · intro y hy
      by_contra hcon
      exact hesc ⟨y, hcon, mem_cluster_iff.mpr hy⟩
  · exact cluster_mono (fun e he => lt_of_lt_of_le he
      (Subtype.coe_le_coe.mpr (M.cutProb_mono hr0 hr hrr e))) 0

/-! ## 10. Pointwise identification of the three integrands off the error events -/

/-- The escape event of the *finite* set `insert 0 B_{r₁}` controls the cluster of the origin at
every radius `r ≤ r₁`. -/
theorem notMem_markEscapeAt_of_notMem_union {r r1 R : ℝ} (hr : 0 < r) (hrr : r ≤ r1)
    {u : Sym2 M.V → ℝ}
    (hesc : u ∉ M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1)))
    {v : M.V} (hv : v ∈ insert (0 : M.V) (E1Sign.ballF M r1)) :
    u ∉ M.markEscapeAt r R v := by
  intro hcontra
  exact hesc (M.mem_markEscapeUnion.mpr ⟨v, hv, M.markEscapeAt_mono hr
    (lt_of_lt_of_le hr hrr) hrr v hcontra⟩)

theorem quadPairFun_eq_of_notMem {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hr0r : r0 ≤ r)
    (hrr1 : r ≤ r1) (hwin : E1Sign.ballF M r = E1Sign.ballF M r0) {u : Sym2 M.V → ℝ}
    (hbox : u ∉ M.markBoxChange r0 r R)
    (hesc : u ∉ M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))) :
    M.quadPairFun r u = M.quadPairFun r0 u := by
  have hrr1pos : 0 < r1 := lt_of_lt_of_le (lt_of_lt_of_le hr0 hr0r) hrr1
  have hnotid : ∀ v ∈ insert (0 : M.V) (E1Sign.ballF M r1), u ∉ M.markEscapeAt r R v := by
    intro v hv hcontra
    exact hesc (M.mem_markEscapeUnion.mpr ⟨v, hv, M.markEscapeAt_mono
      (lt_of_lt_of_le hr0 hr0r) hrr1pos hrr1 v hcontra⟩)
  have hvol : M.markVol r u = M.markVol r0 u :=
    M.clusterVol_eq_of_notMem hr0 hr0r hbox
      (hnotid 0 (Finset.mem_insert_self _ _))
  have hsum : (∑ y ∈ E1Sign.ballF M r,
        clusterVol (atParameter (M.cutProb r) u) y ^ 2)
      = ∑ y ∈ E1Sign.ballF M r0, clusterVol (atParameter (M.cutProb r0) u) y ^ 2 := by
    rw [hwin]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [M.clusterVol_eq_of_notMem hr0 hr0r hbox
      (hnotid y (Finset.mem_insert_of_mem (M.ballF_mono (le_trans hr0r hrr1) hy)))]
  simp only [quadPairFun, hvol, hsum]

theorem sqLinPairFun_eq_of_notMem {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hr0r : r0 ≤ r)
    (hrr1 : r ≤ r1) (hwin : E1Sign.ballF M r = E1Sign.ballF M r0) {u : Sym2 M.V → ℝ}
    (hbox : u ∉ M.markBoxChange r0 r R)
    (hesc : u ∉ M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))) :
    M.sqLinPairFun r u = M.sqLinPairFun r0 u := by
  have hrr1pos : 0 < r1 := lt_of_lt_of_le (lt_of_lt_of_le hr0 hr0r) hrr1
  have hnotid : ∀ v ∈ insert (0 : M.V) (E1Sign.ballF M r1), u ∉ M.markEscapeAt r R v := by
    intro v hv hcontra
    exact hesc (M.mem_markEscapeUnion.mpr ⟨v, hv, M.markEscapeAt_mono
      (lt_of_lt_of_le hr0 hr0r) hrr1pos hrr1 v hcontra⟩)
  have hvol : M.markVol r u = M.markVol r0 u :=
    M.clusterVol_eq_of_notMem hr0 hr0r hbox
      (hnotid 0 (Finset.mem_insert_self _ _))
  have hsum : (∑ y ∈ E1Sign.ballF M r,
        clusterVol (atParameter (M.cutProb r) u) y)
      = ∑ y ∈ E1Sign.ballF M r0, clusterVol (atParameter (M.cutProb r0) u) y := by
    rw [hwin]
    refine Finset.sum_congr rfl fun y hy => ?_
    exact M.clusterVol_eq_of_notMem hr0 hr0r hbox
      (hnotid y (Finset.mem_insert_of_mem (M.ballF_mono (le_trans hr0r hrr1) hy)))
  simp only [sqLinPairFun, hvol, hsum]

theorem connCubeFun_eq_of_notMem {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hr0r : r0 ≤ r)
    (hrr1 : r ≤ r1) (hwin : E1Sign.ballF M r = E1Sign.ballF M r0) {u : Sym2 M.V → ℝ}
    (hbox : u ∉ M.markBoxChange r0 r R)
    (hesc : u ∉ M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))) :
    M.connCubeFun r u = M.connCubeFun r0 u := by
  have hrr1pos : 0 < r1 := lt_of_lt_of_le (lt_of_lt_of_le hr0 hr0r) hrr1
  have hnotid : ∀ v ∈ insert (0 : M.V) (E1Sign.ballF M r1), u ∉ M.markEscapeAt r R v := by
    intro v hv hcontra
    exact hesc (M.mem_markEscapeUnion.mpr ⟨v, hv, M.markEscapeAt_mono
      (lt_of_lt_of_le hr0 hr0r) hrr1pos hrr1 v hcontra⟩)
  have hvol : M.markVol r u = M.markVol r0 u :=
    M.clusterVol_eq_of_notMem hr0 hr0r hbox
      (hnotid 0 (Finset.mem_insert_self _ _))
  have hcl : cluster (atParameter (M.cutProb r) u) (0 : M.V)
      = cluster (atParameter (M.cutProb r0) u) (0 : M.V) :=
    M.cluster_eq_of_notMem hr0 hr0r hbox (hnotid 0 (Finset.mem_insert_self _ _))
  have hind : (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y)
      = ∑ y ∈ E1Sign.ballF M r0,
        (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y := by
    rw [hwin, hcl]
  simp only [connCubeFun, hvol, hind]

/-! ## 11. The integrated increment bounds -/

theorem quadPairFun_le_add {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hr0r : r0 ≤ r) (hrr1 : r ≤ r1)
    (hwin : E1Sign.ballF M r = E1Sign.ballF M r0) (u : Sym2 M.V → ℝ) :
    M.quadPairFun r u ≤ M.quadPairFun r0 u +
      (M.markBoxChange r0 r R).indicator (M.quadPairFun r1) u +
      (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
        (M.quadPairFun r1) u := by
  have hmono : M.quadPairFun r u ≤ M.quadPairFun r1 u :=
    M.quadPairFun_mono (lt_of_lt_of_le hr0 hr0r) hrr1 u
  by_cases hbox : u ∈ M.markBoxChange r0 r R
  · rw [Set.indicator_of_mem hbox]
    calc M.quadPairFun r u ≤ M.quadPairFun r1 u := hmono
      _ ≤ M.quadPairFun r0 u + M.quadPairFun r1 u := le_add_self
      _ ≤ M.quadPairFun r0 u + M.quadPairFun r1 u +
            (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
              (M.quadPairFun r1) u := le_self_add
  · rw [Set.indicator_of_notMem hbox]
    by_cases hesc : u ∈ M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))
    · rw [Set.indicator_of_mem hesc]
      calc M.quadPairFun r u ≤ M.quadPairFun r1 u := hmono
        _ ≤ M.quadPairFun r0 u + M.quadPairFun r1 u := le_add_self
        _ = M.quadPairFun r0 u + 0 + M.quadPairFun r1 u := by rw [add_zero]
    · rw [Set.indicator_of_notMem hesc, add_zero, add_zero]
      exact le_of_eq (M.quadPairFun_eq_of_notMem hr0 hr0r hrr1 hwin hbox hesc)

theorem sqLinPairFun_le_add {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hr0r : r0 ≤ r) (hrr1 : r ≤ r1)
    (hwin : E1Sign.ballF M r = E1Sign.ballF M r0) (u : Sym2 M.V → ℝ) :
    M.sqLinPairFun r u ≤ M.sqLinPairFun r0 u +
      (M.markBoxChange r0 r R).indicator (M.sqLinPairFun r1) u +
      (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
        (M.sqLinPairFun r1) u := by
  have hmono : M.sqLinPairFun r u ≤ M.sqLinPairFun r1 u :=
    M.sqLinPairFun_mono (lt_of_lt_of_le hr0 hr0r) hrr1 u
  by_cases hbox : u ∈ M.markBoxChange r0 r R
  · rw [Set.indicator_of_mem hbox]
    calc M.sqLinPairFun r u ≤ M.sqLinPairFun r1 u := hmono
      _ ≤ M.sqLinPairFun r0 u + M.sqLinPairFun r1 u := le_add_self
      _ ≤ M.sqLinPairFun r0 u + M.sqLinPairFun r1 u +
            (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
              (M.sqLinPairFun r1) u := le_self_add
  · rw [Set.indicator_of_notMem hbox]
    by_cases hesc : u ∈ M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))
    · rw [Set.indicator_of_mem hesc]
      calc M.sqLinPairFun r u ≤ M.sqLinPairFun r1 u := hmono
        _ ≤ M.sqLinPairFun r0 u + M.sqLinPairFun r1 u := le_add_self
        _ = M.sqLinPairFun r0 u + 0 + M.sqLinPairFun r1 u := by rw [add_zero]
    · rw [Set.indicator_of_notMem hesc, add_zero, add_zero]
      exact le_of_eq (M.sqLinPairFun_eq_of_notMem hr0 hr0r hrr1 hwin hbox hesc)

theorem connCubeFun_le_add {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hr0r : r0 ≤ r) (hrr1 : r ≤ r1)
    (hwin : E1Sign.ballF M r = E1Sign.ballF M r0) (u : Sym2 M.V → ℝ) :
    M.connCubeFun r u ≤ M.connCubeFun r0 u +
      (M.markBoxChange r0 r R).indicator (M.connCubeFun r1) u +
      (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
        (M.connCubeFun r1) u := by
  have hmono : M.connCubeFun r u ≤ M.connCubeFun r1 u :=
    M.connCubeFun_mono (lt_of_lt_of_le hr0 hr0r) hrr1 u
  by_cases hbox : u ∈ M.markBoxChange r0 r R
  · rw [Set.indicator_of_mem hbox]
    calc M.connCubeFun r u ≤ M.connCubeFun r1 u := hmono
      _ ≤ M.connCubeFun r0 u + M.connCubeFun r1 u := le_add_self
      _ ≤ M.connCubeFun r0 u + M.connCubeFun r1 u +
            (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
              (M.connCubeFun r1) u := le_self_add
  · rw [Set.indicator_of_notMem hbox]
    by_cases hesc : u ∈ M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))
    · rw [Set.indicator_of_mem hesc]
      calc M.connCubeFun r u ≤ M.connCubeFun r1 u := hmono
        _ ≤ M.connCubeFun r0 u + M.connCubeFun r1 u := le_add_self
        _ = M.connCubeFun r0 u + 0 + M.connCubeFun r1 u := by rw [add_zero]
    · rw [Set.indicator_of_notMem hesc, add_zero, add_zero]
      exact le_of_eq (M.connCubeFun_eq_of_notMem hr0 hr0r hrr1 hwin hbox hesc)

/-! ## 12. Finiteness of the three masses from the fourth cut-off moment -/

theorem cutMoment_two_ne_top_of_four {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.cutMoment 2 r ≠ ⊤ :=
  ne_top_of_le_ne_top h4 (M.cutMoment_two_le_four r)

theorem quadPairMass_ne_top {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.quadPairMass r ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp)
      (ENNReal.add_ne_top.mpr ⟨M.cutMoment_two_ne_top_of_four h4, h4⟩))
    (M.quadPairMass_le r)

theorem sqLinPairMass_ne_top {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.sqLinPairMass r ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp)
      (ENNReal.add_ne_top.mpr ⟨M.cutMoment_two_ne_top_of_four h4, h4⟩))
    (M.sqLinPairMass_le r)

theorem connCubeMass_ne_top {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.connCubeMass r ≠ ⊤ :=
  ne_top_of_le_ne_top h4 (M.connCubeMass_le_fourth r)

/-! ## 13. The box-change and escape integrals vanish for any finite measurable integrand -/

theorem tendsto_boxIntegral_toReal (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (_hr1 : r0 < r1)
    (f : (Sym2 M.V → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hfin : (∫⁻ u, f u ∂(markMeasure M.V)) ≠ ⊤) (R : ℝ) :
    Tendsto (fun r => (∫⁻ u in M.markBoxChange r0 r R, f u ∂(markMeasure M.V)).toReal)
      (𝓝[>] r0) (𝓝 0) := by
  set rseq : ℕ → ℝ := fun n => r0 + r0 / ((n : ℝ) + 2) with hrseq
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hrpos : ∀ n : ℕ, r0 < rseq n := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h2 : 0 < r0 / ((n : ℝ) + 2) := div_pos hr0 h1
    simp only [hrseq]
    linarith
  have hseq : Tendsto rseq atTop (𝓝 r0) := by
    have h0 : Tendsto (fun n : ℕ => r0 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa using tendsto_const_nhds.div_atTop h1
    simp only [hrseq]
    simpa using tendsto_const_nhds.add h0
  have hanti : Antitone fun n : ℕ => M.markBoxChange r0 (rseq n) R := by
    intro n m hnm
    refine M.markBoxChange_mono hr0 (lt_trans hr0 (hrpos m)) (lt_trans hr0 (hrpos n)) ?_
    have hd1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have hd2 : (0 : ℝ) < (m : ℝ) + 2 := hden m
    have hcast : ((n : ℝ) + 2) ≤ ((m : ℝ) + 2) := by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith
    simp only [hrseq]
    have : r0 / ((m : ℝ) + 2) ≤ r0 / ((n : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr0.le hd1 hcast
    linarith
  have hnull : markMeasure M.V (⋂ n : ℕ, M.markBoxChange r0 (rseq n) R) = 0 :=
    measure_mono_null (M.iInter_markBoxChange_subset hr0 hseq) (M.measure_boxNull r0 R)
  have hconv : Tendsto (fun n : ℕ => (∫⁻ u in M.markBoxChange r0 (rseq n) R,
      f u ∂(markMeasure M.V)).toReal) atTop (𝓝 0) :=
    tendsto_setLIntegral_toReal_of_antitone (μ := markMeasure M.V) hf hfin
      (fun n => M.measurableSet_markBoxChange r0 (rseq n) R) hanti hnull
  refine tendsto_zero_of_le_seq (r := rseq) ?_ ?_ hrpos hconv
  · intro x y hx hxy
    have hy : 0 < y := lt_of_lt_of_le (lt_trans hr0 hx) hxy
    have hsub : M.markBoxChange r0 x R ⊆ M.markBoxChange r0 y R :=
      M.markBoxChange_mono hr0 (lt_trans hr0 hx) hy hxy
    have hfin' : (∫⁻ u in M.markBoxChange r0 y R, f u ∂(markMeasure M.V)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono_set (Set.subset_univ _))
      rw [Measure.restrict_univ]
      exact hfin
    exact ENNReal.toReal_mono hfin' (lintegral_mono_set hsub)
  · intro x
    exact ENNReal.toReal_nonneg

theorem tendsto_escapeIntegral_toReal (r1 : ℝ) (f : (Sym2 M.V → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hfin : (∫⁻ u, f u ∂(markMeasure M.V)) ≠ ⊤) (hcm : M.cutMassAt r1 0 ≠ ⊤)
    (s : Finset M.V) :
    Tendsto (fun n : ℕ => (∫⁻ u in M.markEscapeUnion r1 (n : ℝ) s, f u
      ∂(markMeasure M.V)).toReal) atTop (𝓝 0) :=
  tendsto_setLIntegral_toReal_of_antitone (μ := markMeasure M.V) hf hfin
    (fun n => M.measurableSet_markEscapeUnion r1 (n : ℝ) s)
    (fun n m hnm => M.markEscapeUnion_antitone (by exact_mod_cast hnm) s)
    (M.measure_iInter_markEscapeUnion_eq_zero hcm)

/-! ## 14. Right continuity of a monotone marked window mass

The DCT skeleton of `PairMassRegularity.tendsto_pairMassReal_nhdsGT`, stated for an arbitrary
integrand family with an explicit increment bound. -/

theorem tendsto_toReal_nhdsGT_of_increment (G : ℝ → (Sym2 M.V → ℝ) → ℝ≥0∞) {r0 r1 : ℝ}
    (hr0 : 0 < r0) (hr1 : r0 < r1)
    (hmeas1 : Measurable (G r1))
    (hfin1 : (∫⁻ u, G r1 u ∂(markMeasure M.V)) ≠ ⊤)
    (hcm : M.cutMassAt r1 0 ≠ ⊤)
    (hmono : ∀ r r', r0 ≤ r → r ≤ r' → r' ≤ r1 → ∀ u, G r u ≤ G r' u)
    (hinc : ∀ r, r0 < r → r ≤ r1 → E1Sign.ballF M r = E1Sign.ballF M r0 → ∀ R u,
      G r u ≤ G r0 u + (M.markBoxChange r0 r R).indicator (G r1) u +
        (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
          (G r1) u) :
    Tendsto (fun r => (∫⁻ u, G r u ∂(markMeasure M.V)).toReal) (𝓝[>] r0)
      (𝓝 ((∫⁻ u, G r0 u ∂(markMeasure M.V)).toReal)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set s : Finset M.V := insert (0 : M.V) (E1Sign.ballF M r1) with hs
  have hfinr0 : (∫⁻ u, G r0 u ∂(markMeasure M.V)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin1 (lintegral_mono fun u => hmono r0 r1 le_rfl hr1.le le_rfl u)
  have hesc_tend := M.tendsto_escapeIntegral_toReal r1 (G r1) hmeas1 hfin1 hcm s
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hesc_tend (ε / 2) (by linarith)
  have hN' : (∫⁻ u in M.markEscapeUnion r1 (N : ℝ) s, G r1 u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    have h := hN N le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h
  have hbox_tend := M.tendsto_boxIntegral_toReal r0 hr0 hr1 (G r1) hmeas1 hfin1 (N : ℝ)
  obtain ⟨δ1, hδ1, hspec1⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hbox_tend) (ε / 2) (by linarith)
  obtain ⟨δ2, hδ2, hwin⟩ := M.exists_ballF_eq_of_right hr1
  refine ⟨min δ1 (min δ2 (r1 - r0)), lt_min hδ1 (lt_min hδ2 (by linarith)), ?_⟩
  intro r hr hdist
  have habs : |r - r0| < min δ1 (min δ2 (r1 - r0)) := by
    rwa [Real.dist_eq] at hdist
  rw [Real.dist_eq, abs_lt] at hdist
  have hb1 := min_le_left δ1 (min δ2 (r1 - r0))
  have hb2 := min_le_right δ1 (min δ2 (r1 - r0))
  have hb3 := min_le_left δ2 (r1 - r0)
  have hb4 := min_le_right δ2 (r1 - r0)
  have hrr1 : r ≤ r1 := by linarith [hdist.2]
  have hrdel2 : r < r0 + δ2 := by linarith [hdist.2]
  have hwinr : E1Sign.ballF M r = E1Sign.ballF M r0 := hwin r ⟨hr, hrdel2⟩
  have hboxsmall : (∫⁻ u in M.markBoxChange r0 r (N : ℝ), G r1 u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    have h2' : dist (∫⁻ u in M.markBoxChange r0 r (N : ℝ), G r1 u
        ∂(markMeasure M.V)).toReal 0 < ε / 2 :=
      hspec1 hr (by rw [Real.dist_eq]; exact lt_of_lt_of_le habs hb1)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h2'
  have hpt_fun : ∀ u : Sym2 M.V → ℝ, G r u ≤ G r0 u +
      (M.markBoxChange r0 r (N : ℝ)).indicator (G r1) u +
      (M.markEscapeUnion r1 (N : ℝ) s).indicator (G r1) u :=
    hinc r hr hrr1 hwinr (N : ℝ)
  have hpt : ∫⁻ u, G r u ∂(markMeasure M.V) ≤
      ∫⁻ u, (G r0 u +
        (M.markBoxChange r0 r (N : ℝ)).indicator (G r1) u +
        (M.markEscapeUnion r1 (N : ℝ) s).indicator (G r1) u) ∂(markMeasure M.V) :=
    lintegral_mono hpt_fun
  have hmeas_box : Measurable fun u : Sym2 M.V → ℝ =>
      (M.markBoxChange r0 r (N : ℝ)).indicator (G r1) u :=
    hmeas1.indicator (M.measurableSet_markBoxChange r0 r (N : ℝ))
  have hmeas_esc : Measurable fun u : Sym2 M.V → ℝ =>
      (M.markEscapeUnion r1 (N : ℝ) s).indicator (G r1) u :=
    hmeas1.indicator (M.measurableSet_markEscapeUnion r1 (N : ℝ) s)
  have hfinr : (∫⁻ u, G r u ∂(markMeasure M.V)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin1 (lintegral_mono fun u => hmono r r1 hr.le hrr1 le_rfl u)
  have hboxfin : (∫⁻ u, (M.markBoxChange r0 r (N : ℝ)).indicator (G r1) u
      ∂(markMeasure M.V)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin1 (lintegral_mono fun u => by
      by_cases hu : u ∈ M.markBoxChange r0 r (N : ℝ)
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu]; exact zero_le)
  have hescfin : (∫⁻ u, (M.markEscapeUnion r1 (N : ℝ) s).indicator (G r1) u
      ∂(markMeasure M.V)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin1 (lintegral_mono fun u => by
      by_cases hu : u ∈ M.markEscapeUnion r1 (N : ℝ) s
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu]; exact zero_le)
  have hsplit1 : (∫⁻ u, G r0 u ∂(markMeasure M.V) +
      (∫⁻ u, (M.markBoxChange r0 r (N : ℝ)).indicator (G r1) u
        ∂(markMeasure M.V))) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinr0, hboxfin⟩
  have hupperfin : (∫⁻ u, G r0 u ∂(markMeasure M.V) +
      (∫⁻ u, (M.markBoxChange r0 r (N : ℝ)).indicator (G r1) u
        ∂(markMeasure M.V)) +
      (∫⁻ u, (M.markEscapeUnion r1 (N : ℝ) s).indicator (G r1) u
        ∂(markMeasure M.V))) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hsplit1, hescfin⟩
  rw [lintegral_add_right (fun u => G r0 u +
      (M.markBoxChange r0 r (N : ℝ)).indicator (G r1) u) hmeas_esc,
    lintegral_add_right (G r0) hmeas_box] at hpt
  have hreal := ENNReal.toReal_mono hupperfin hpt
  rw [ENNReal.toReal_add hsplit1 hescfin, ENNReal.toReal_add hfinr0 hboxfin] at hreal
  have hboxsmall' : (∫⁻ u, (M.markBoxChange r0 r (N : ℝ)).indicator (G r1) u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    rw [M.toReal_indicator_eq_setIntegral (M.measurableSet_markBoxChange r0 r (N : ℝ))
      (G r1)]
    exact hboxsmall
  have hescsmall' : (∫⁻ u, (M.markEscapeUnion r1 (N : ℝ) s).indicator (G r1) u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    rw [M.toReal_indicator_eq_setIntegral (M.measurableSet_markEscapeUnion r1 (N : ℝ) s)
      (G r1)]
    exact hN'
  have hmono2 : (∫⁻ u, G r0 u ∂(markMeasure M.V)).toReal
      ≤ (∫⁻ u, G r u ∂(markMeasure M.V)).toReal :=
    ENNReal.toReal_mono hfinr (lintegral_mono fun u => hmono r0 r le_rfl hr.le hrr1 u)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 15. Right continuity of the three marked window masses

Each is an instance of `tendsto_toReal_nhdsGT_of_increment`, with the monotonicity and the
increment bound supplied by §8–§11 and the moment bound by §12. -/

theorem tendsto_quadPairMass_toReal_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h4 : M.cutMoment 4 r1 ≠ ⊤) :
    Tendsto (fun r => (M.quadPairMass r).toReal) (𝓝[>] r0)
      (𝓝 ((M.quadPairMass r0).toReal)) := by
  have hfin1 : (∫⁻ u, M.quadPairFun r1 u ∂(markMeasure M.V)) ≠ ⊤ := M.quadPairMass_ne_top h4
  refine M.tendsto_toReal_nhdsGT_of_increment (fun r => M.quadPairFun r) hr0 hr1
    (M.measurable_quadPairFun r1) hfin1 ?_ ?_ ?_
  · exact ne_top_of_le_ne_top (M.cutMoment_two_ne_top_of_four h4)
      (E1Sign.cutMassAt_le_cutMoment_two M r1)
  · intro r r' hr0r hrr' hr'r1 u
    exact M.quadPairFun_mono (lt_of_lt_of_le hr0 hr0r) hrr' u
  · intro r _ hrr1 hwin R u
    exact M.quadPairFun_le_add hr0 (le_of_lt ‹r0 < r›) hrr1 hwin u

theorem tendsto_sqLinPairMass_toReal_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h4 : M.cutMoment 4 r1 ≠ ⊤) :
    Tendsto (fun r => (M.sqLinPairMass r).toReal) (𝓝[>] r0)
      (𝓝 ((M.sqLinPairMass r0).toReal)) := by
  have hfin1 : (∫⁻ u, M.sqLinPairFun r1 u ∂(markMeasure M.V)) ≠ ⊤ := M.sqLinPairMass_ne_top h4
  refine M.tendsto_toReal_nhdsGT_of_increment (fun r => M.sqLinPairFun r) hr0 hr1
    (M.measurable_sqLinPairFun r1) hfin1 ?_ ?_ ?_
  · exact ne_top_of_le_ne_top (M.cutMoment_two_ne_top_of_four h4)
      (E1Sign.cutMassAt_le_cutMoment_two M r1)
  · intro r r' hr0r hrr' hr'r1 u
    exact M.sqLinPairFun_mono (lt_of_lt_of_le hr0 hr0r) hrr' u
  · intro r _ hrr1 hwin R u
    exact M.sqLinPairFun_le_add hr0 (le_of_lt ‹r0 < r›) hrr1 hwin u

theorem tendsto_connCubeMass_toReal_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h4 : M.cutMoment 4 r1 ≠ ⊤) :
    Tendsto (fun r => (M.connCubeMass r).toReal) (𝓝[>] r0)
      (𝓝 ((M.connCubeMass r0).toReal)) := by
  have hfin1 : (∫⁻ u, M.connCubeFun r1 u ∂(markMeasure M.V)) ≠ ⊤ := M.connCubeMass_ne_top h4
  refine M.tendsto_toReal_nhdsGT_of_increment (fun r => M.connCubeFun r) hr0 hr1
    (M.measurable_connCubeFun r1) hfin1 ?_ ?_ ?_
  · exact ne_top_of_le_ne_top (M.cutMoment_two_ne_top_of_four h4)
      (E1Sign.cutMassAt_le_cutMoment_two M r1)
  · intro r r' hr0r hrr' hr'r1 u
    exact M.connCubeFun_mono (lt_of_lt_of_le hr0 hr0r) hrr' u
  · intro r _ hrr1 hwin R u
    exact M.connCubeFun_le_add hr0 (le_of_lt ‹r0 < r›) hrr1 hwin u

/-! ## 16. The real-valued `p = 2` RHS identity -/

/-- **The `p = 2` RHS in real form.**  From `p2RHS + 3 connCubeMass = quadPairMass + 2
sqLinPairMass`, so the RHS is the difference of three right-continuous real functions. -/
theorem p2RHS_toReal_eq_pair_sub (r : ℝ) (h4 : M.cutMoment 4 r ≠ ⊤) :
    (M.p2RHS r).toReal = (M.quadPairMass r).toReal + 2 * (M.sqLinPairMass r).toReal
      - 3 * (M.connCubeMass r).toReal := by
  have hA0 : M.quadPairMass r ≠ ⊤ := M.quadPairMass_ne_top h4
  have hA1 : M.sqLinPairMass r ≠ ⊤ := M.sqLinPairMass_ne_top h4
  have hC : M.connCubeMass r ≠ ⊤ := M.connCubeMass_ne_top h4
  have h3C : (3 : ℝ≥0∞) * M.connCubeMass r ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hC
  have h2A1 : (2 : ℝ≥0∞) * M.sqLinPairMass r ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hA1
  have hP : M.p2RHS r ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hA0, h2A1⟩) ?_
    calc M.p2RHS r ≤ M.p2RHS r + 3 * M.connCubeMass r := le_self_add
      _ = M.quadPairMass r + 2 * M.sqLinPairMass r := M.p2RHS_add_three_mul_connCube r
  have h1 : (M.p2RHS r + 3 * M.connCubeMass r).toReal
      = (M.quadPairMass r + 2 * M.sqLinPairMass r).toReal := by
    rw [M.p2RHS_add_three_mul_connCube r]
  rw [ENNReal.toReal_add hP h3C, ENNReal.toReal_add hA0 h2A1,
    ENNReal.toReal_mul, ENNReal.toReal_mul] at h1
  have h3 : ((3 : ℝ≥0∞)).toReal = 3 := ENNReal.toReal_ofNat 3
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := ENNReal.toReal_ofNat 2
  rw [h3, h2] at h1
  linarith

/-! ## 17. Right continuity of the `p = 2` RHS at every positive radius -/

/-- **The `p = 2` right-hand side of Lemma I.4.1 is right continuous in the cut-off radius.**
Hypotheses: `r₀ > 0` and finiteness of the *fourth* cut-off moment at one strictly larger radius
`r₁`.  No attained-radius condition and no two-sided statement is asserted: at an attained radius
the closed window jumps and the right limit is the closed-window mass. -/
theorem tendsto_p2RHS_toReal_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h4 : M.cutMoment 4 r1 ≠ ⊤) :
    Tendsto (fun r => (M.p2RHS r).toReal) (𝓝[>] r0) (𝓝 ((M.p2RHS r0).toReal)) := by
  have h4r0 : M.cutMoment 4 r0 ≠ ⊤ := M.cutMoment_ne_top_of_le hr1.le 4 h4
  have hA0 := M.tendsto_quadPairMass_toReal_nhdsGT r0 hr0 hr1 h4
  have hA1 := M.tendsto_sqLinPairMass_toReal_nhdsGT r0 hr0 hr1 h4
  have hC := M.tendsto_connCubeMass_toReal_nhdsGT r0 hr0 hr1 h4
  have hcomb : Tendsto (fun r => (M.quadPairMass r).toReal + 2 * (M.sqLinPairMass r).toReal
      - 3 * (M.connCubeMass r).toReal) (𝓝[>] r0)
      (𝓝 ((M.quadPairMass r0).toReal + 2 * (M.sqLinPairMass r0).toReal
        - 3 * (M.connCubeMass r0).toReal)) :=
    (hA0.add (hA1.const_mul 2)).sub (hC.const_mul 3)
  have hev : (fun r => (M.p2RHS r).toReal) =ᶠ[𝓝[>] r0]
      fun r => (M.quadPairMass r).toReal + 2 * (M.sqLinPairMass r).toReal
        - 3 * (M.connCubeMass r).toReal := by
    filter_upwards [Ioo_mem_nhdsGT hr1] with r hr
    exact M.p2RHS_toReal_eq_pair_sub r (M.cutMoment_ne_top_of_le (le_of_lt hr.2) 4 h4)
  have hlim := (tendsto_congr' hev).mpr hcomb
  rwa [← M.p2RHS_toReal_eq_pair_sub r0 h4r0] at hlim


/-! ## 18. The derivative weight and the two-sided assembly -/

/-- **Right continuity of the derivative weight `rhsScalarTwo`.**  `rhsScalarTwo` is
`coeffRHS · (p2RHS ·).toReal`, so the right continuity of the `p = 2` excluded RHS is inherited by
the derivative weight as soon as the coefficient `β_c(-K')` is right continuous.  The latter is
the landed per-radius derivative hypothesis of the `p = 1` chain and is left explicit here. -/
theorem tendsto_rhsScalarTwo_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h4 : M.cutMoment 4 r1 ≠ ⊤) (hcoef : ContinuousAt M.coeffRHS r0) :
    Tendsto M.rhsScalarTwo (𝓝[>] r0) (𝓝 (M.rhsScalarTwo r0)) := by
  have hp2 := M.tendsto_p2RHS_toReal_nhdsGT r0 hr0 hr1 h4
  have hcoe : Tendsto M.coeffRHS (𝓝[>] r0) (𝓝 (M.coeffRHS r0)) :=
    hcoef.mono_left nhdsWithin_le_nhds
  exact hcoe.mul hp2

/-- **Two-sided continuity of the `p = 2` RHS from its right continuity and its left limit.**
This is the exact place where the left limit enters: everything else is proved above.  At an
off-sphere radius the left limit is `(p2RHSStrict r₀).toReal`, so the remaining input is the
left-window (monotone convergence) statement, not any RHS algebra. -/
theorem continuousAt_p2RHS_toReal_of_left (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h4 : M.cutMoment 4 r1 ≠ ⊤)
    (hleft : Tendsto (fun r => (M.p2RHS r).toReal) (𝓝[<] r0) (𝓝 ((M.p2RHS r0).toReal))) :
    ContinuousAt (fun r => (M.p2RHS r).toReal) r0 := by
  have hright := M.tendsto_p2RHS_toReal_nhdsGT r0 hr0 hr1 h4
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ1, hδ1, hspec1⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hleft) ε hε
  obtain ⟨δ2, hδ2, hspec2⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hright) ε hε
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun x hx => ?_⟩
  rw [Real.dist_eq] at hx ⊢
  rcases lt_trichotomy x r0 with h | h | h
  · refine hspec1 (show x ∈ Set.Iio r0 from h) ?_
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hx (min_le_left _ _)
  · subst h
    simpa using hε
  · refine hspec2 (show x ∈ Set.Ioi r0 from h) ?_
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hx (min_le_right _ _)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_add_three_mul_connCube
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_le_fourth
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_toReal_nhdsGT_of_increment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_toReal_eq_pair_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_p2RHS_toReal_nhdsGT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.quadPairMass_eq_connCube_add
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sqLinPairMass_eq_connCube_add
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cluster_eq_of_notMem
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_boxIntegral_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_escapeIntegral_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_connCubeMass_toReal_nhdsGT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_rhsScalarTwo_nhdsGT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_p2RHS_toReal_of_left
