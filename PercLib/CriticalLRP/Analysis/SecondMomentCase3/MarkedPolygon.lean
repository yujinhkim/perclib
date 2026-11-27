/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m3`, direction d3.

# The `p = 3`, `q = 0` moment gap via the landed marked joint-moment route

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.17 at
`p = 3`, `q = 0`, and its use in the numerator of display (I.4.16) (proof of
Proposition I.4.15, Case 3, p. 47).

The two-copy (`q ≥ 1`) route to Lemma I.4.17 needs an arm on the fresh copy, and
`I417Gen.prodSet_not_subset_q_zero` records that the covering proof degenerates at `q = 0`.
The marked route of `I417.MarkedJoint` has no such restriction: the marked vertex `w` is the
*last label* of the carrier, so `E[|K_x|^p 1(w ∈ K_x)]` is covered for every `p`.  This file
instantiates that landed machinery at the literal cutoff model objects and records exactly
what it gives for the Case-3 numerator.

## What is proved

* `connCubeVertexMass_eq_jointPow` — the Case-3 per-vertex object
  `M.connCubeVertexMass r y = E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` *is* the marked joint moment
  `I417Gen.jointPow (M.cutProb r) 0 3 y` (`M.cutLaw r` is `edgeMeasure (M.cutProb r)`
  definitionally, and `clusterVol` is `cardFun` of the cluster).
* `connCubeVertexMass_le_markedPolygon` — the marked polygon bound at `p = 3`,
  `ℓ` running over `1 ≤ ℓ ≤ 4`, with `χ = M.cutMassAt r 0` and the cutoff matrix powers.
* `connCubeVertexMass_toReal_le_markedPolygon` — the same in `ℝ`: the per-vertex `p = 3`,
  `q = 0` gap, with the polygon terms `T^ℓ_{β_c,r}(0,y)` for `1 ≤ ℓ ≤ 4`.
* `polyK_colSum_toReal`, `polyK_summable_colSum` — the source's `∑_y T^ℓ(0,y) = χ^ℓ` in `ℝ`.
* `connCubeMass_toReal_le_markedPolygon` — the Case-3 **numerator**
  `E[|K|³|K ∩ B_r|] ≤ (∑_{ℓ≤3} markedCount 3 ℓ) χ^7
   + markedCount 3 4 · Cp · |B_r| · (∇_{r^c}+r^{-c}) · χ^4`,
  with neither `hgap` nor `hT3` assumed.  `exists_connCubeMass_toReal_le_markedPolygon`
  discharges `hpoly4` as well, using the landed all-radius `ℓ = 4` manufacturer.
* `p2ExclError_le_markedResidual` — the resulting `E_{2,r}` bound
  `≤ (c₃^{-1}∑_{ℓ≤3}) χ³/|B_r| + (c₃^{-1} markedCount 3 4 Cp) (∇_{r^c}+r^{-c})`.
* `connCubeMass_toReal_le_of_chi_cube_le`, `p2ExclError_tendsto_zero_of_markedPolygon` — the
  single remaining scalar condition `χ³ ≤ K |B_r| drv` under which the landed Case-3 chain
  produces `E_{2,r} → 0`.

The ℓ-range starts at `1`, not at `3`, as in the paper: the marked carrier has `2p+1 = 7`
edges, of which `ℓ` lie on the `x`–`w` path, and the marked route does not see the
`ℓ ≥ 3` lower bound of the two-copy cover.  This is a *loss* relative to the printed
Lemma I.4.17 at `p = 3`, `q = 0` (which has `3 ≤ ℓ ≤ 4`), but it is an honest one: the
extra `ℓ ∈ {1,2}` terms carry the full `χ` powers and their window sums are `χ^ℓ`, so they
produce the same `χ^7` contribution as the `ℓ = 3` term does after the column sum
`∑_y T^3(0,y) = χ^3`.  Nothing here uses, or claims, the printed `ℓ = 3` sup bound
`T³(0,0) ≤ C(∇_{r^c} + r^{-c})`, which `I418C.one_le_polyK_three` refutes.

## Source scope

The statement of Lemma I.4.17 (`0 ≤ E|K|^p E|K|^q − E[|K_x|^p |K_y|^q 1(x ↮ y)] ≤
∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) (E|K|)^{2p+2q+1-ℓ}`) is quoted here only for orientation;
what this file proves is the `q = 0` *marked* instance obtained from the landed canonical
atlas/BK machinery, and the coefficients are the landed ones (`I417Marked.markedCount 3 ℓ`),
not rescaled.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Relabel.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Bridge
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3

/-! # The `p = 3`, `q = 0` gap at the cutoff model, marked route -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open MeasureTheory Measure Filter
open scoped ENNReal BigOperators Topology

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-- **The Case-3 per-vertex object is the marked joint moment.**  `E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]`
is `I417Gen.jointPow (M.cutProb r) 0 3 y`: the cutoff law is by definition the independent-edge
law of the profile `M.cutProb r`, and `clusterVol` is `cardFun` of the cluster set. -/
theorem connCubeVertexMass_eq_jointPow (r : ℝ) (y : M.V) :
    M.connCubeVertexMass r y =
      PercLib.CriticalLRP.I417Gen.jointPow (M.cutProb r) (0 : M.V) 3 y := by
  have hlaw : M.cutLaw r = PercLib.CriticalLRP.edgeMeasure (M.cutProb r) := rfl
  simp only [connCubeVertexMass, PercLib.CriticalLRP.I417Gen.jointPow, hlaw,
    PercLib.CriticalLRP.Percolation.cardFun_eq_encard, PercLib.CriticalLRP.clusterVol]

/-- The first moment is root-independent at the cutoff law, in the row-sum form the marked
polygon bound takes. -/
theorem cutProb_rowSum (r : ℝ) (v : M.V) :
    ∑' w, PercLib.CriticalLRP.edgeMeasure (M.cutProb r)
      (PercLib.CriticalLRP.connSet v w) = M.cutMassAt r 0 := by
  have hpt : ∀ w : M.V, PercLib.CriticalLRP.edgeMeasure (M.cutProb r)
      (PercLib.CriticalLRP.connSet v w) = M.cutTwoPointE r v w := fun w => rfl
  rw [tsum_congr hpt, M.tsum_cutTwoPointE_eq_cutMassAt r v, M.cutMassAt_eq_zero r v]

/-- **The `p = 3`, `q = 0` per-vertex bound, marked polygon form** (`ℝ≥0∞`).

At the literal cutoff model and window vertex `y`, the connected third window moment is at most
`∑_{ℓ=1}^{4} markedCount 3 ℓ · χ^{7-ℓ} · T^ℓ_{β_c,r}(0,y)`, with `χ = M.cutMassAt r 0` the
source's `E_{β_c,r}|K|` and `T^ℓ` the cutoff matrix power `I420Case3.cutPoly`. -/
theorem connCubeVertexMass_le_markedPolygon (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V) :
    M.connCubeVertexMass r y ≤
      ∑ ℓ ∈ Finset.Icc 1 4, (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ≥0∞) *
        ((M.cutMassAt r 0) ^ (2 * 3 + 1 - ℓ) *
          PercLib.CriticalLRP.I420Case3.cutPoly M r y ℓ) := by
  have h := PercLib.CriticalLRP.I417MarkedRelabel.jointPow_le_markedPolygonBound
    (M.cutProb r) (PercLib.CriticalLRP.AuditM2.cutProb_lt_one M r)
    (M.cutMassAt r 0) (M.cutProb_rowSum r) (0 : M.V) y 3
  rw [connCubeVertexMass_eq_jointPow]
  refine h.trans (le_of_eq ?_)
  simp only [PercLib.CriticalLRP.I417Marked.markedPolygonBound]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [PercLib.CriticalLRP.AuditM2.iterPow_cutProb_eq_cutPoly M r hχ y ℓ]

/-- **The `p = 3`, `q = 0` per-vertex bound in `ℝ`**, with the real matrix powers
`T^ℓ_{β_c,r}(0,y) = I418C.polyK (M.cutTwoPoint r) ℓ 0 y` of Lemma I.4.17. -/
theorem connCubeVertexMass_toReal_le_markedPolygon (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (y : M.V) :
    (M.connCubeVertexMass r y).toReal ≤
      ∑ ℓ ∈ Finset.Icc 1 4, (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
        ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ) *
          PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y) := by
  have hne : ∀ ℓ ∈ Finset.Icc 1 4,
      (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ≥0∞) *
        ((M.cutMassAt r 0) ^ (2 * 3 + 1 - ℓ) *
          PercLib.CriticalLRP.I420Case3.cutPoly M r y ℓ) ≠ ⊤ := by
    intro ℓ _
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top hχ) ?_
    rw [PercLib.CriticalLRP.I420Case3.cutPoly_eq_Kpow M r hχ]
    exact M.cutKpow_ne_top_of_chi_ne_top r hχ ℓ 0 y
  have h1 := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hne)
    (M.connCubeVertexMass_le_markedPolygon r hχ y)
  rw [ENNReal.toReal_sum hne] at h1
  refine h1.trans (Finset.sum_le_sum fun ℓ _ => ?_)
  refine le_of_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_pow,
    PercLib.CriticalLRP.I420Case3.cutPoly,
    ENNReal.toReal_ofReal (PercLib.CriticalLRP.I418C.polyK_nonneg _
      (fun a b => M.cutTwoPoint_nonneg r a b) ℓ 0 y)]

/-- **The source's `∑_y T^ℓ_{β_c,r}(0,y) = χ^ℓ` in `ℝ`**: the column sums of the cutoff
matrix powers at the origin, from the landed `ℝ≥0∞` identity `cutKpow_rowSum`. -/
theorem polyK_colSum_toReal (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (ℓ : ℕ) :
    ∑' y, PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y
      = (M.cutMassAt r 0).toReal ^ ℓ := by
  have hne : ∀ y : M.V, PercLib.CriticalLRP.KernelPower.Kpow (M.cutTwoPointE r) ℓ 0 y ≠ ⊤ :=
    fun y => M.cutKpow_ne_top_of_chi_ne_top r hχ ℓ 0 y
  have hsum : (∑' y, PercLib.CriticalLRP.KernelPower.Kpow (M.cutTwoPointE r) ℓ 0 y) ≠ ⊤ := by
    rw [M.cutKpow_rowSum r ℓ 0]
    exact ENNReal.pow_ne_top hχ
  rw [← tsum_congr (fun y => M.cutKpow_toReal_eq_polyK r hχ ℓ 0 y),
    ← ENNReal.tsum_toReal_eq hne, M.cutKpow_rowSum r ℓ 0, ENNReal.toReal_pow]

/-- Summability of the cutoff matrix-power row at the origin, from the same column sum. -/
theorem polyK_summable_colSum (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (ℓ : ℕ) :
    Summable (fun y => PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y) := by
  have hsum : (∑' y, PercLib.CriticalLRP.KernelPower.Kpow (M.cutTwoPointE r) ℓ 0 y) ≠ ⊤ := by
    rw [M.cutKpow_rowSum r ℓ 0]
    exact ENNReal.pow_ne_top hχ
  have hs := ENNReal.summable_toReal hsum
  simpa only [M.cutKpow_toReal_eq_polyK r hχ] using hs

/-- **The Case-3 numerator from the marked `p = 3`, `q = 0` gap**, with no per-vertex sup
bound and no column-uniform `ℓ = 3` estimate.

Summing `connCubeVertexMass_toReal_le_markedPolygon` over the window `B_r` and using the
column sums `∑_y T^ℓ_{β_c,r}(0,y) = χ^ℓ` for the low polygon orders, the only term that needs
a decay input is `ℓ = 4`, where the landed all-radius polygon bound
(`I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii`, at `ℓ = 4`)
supplies `T⁴(0,y) ≤ Cp · drv · χ` uniformly in `y`.  The result is

`E[|K|³ |K ∩ B_r|] ≤ c · χ^7 + markedCount 3 4 · Cp · |B_r| · drv · χ^4`,

exactly the source's numerator shape `|B_r| · drv · χ^4` plus the honest low-order residual
`χ^7` (i.e. `|B_r| · drv · χ^4 · (χ^3/(|B_r| drv))`). -/
theorem connCubeMass_toReal_le_markedPolygon (c Cp : ℝ) (hCp : 0 ≤ Cp)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 x ≤
        Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
          + PercLib.CriticalLRP.I417Marked.markedCount 3 2
          + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
          * (M.cutMassAt r 0).toReal ^ 7
        + (PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) * Cp
            * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hχne := hχ r hr
  have hχ0 : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
  have hdrv0 : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
  have hd0 : ∀ ℓ : ℕ, (0 : ℝ) ≤ (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) :=
    fun ℓ => Nat.cast_nonneg _
  have hstep1 : ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
        (M.connCubeVertexMass r y).toReal
      ≤ ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
          ∑ ℓ ∈ Finset.Icc 1 4, (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
            ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ) *
              PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y) :=
    Finset.sum_le_sum fun y _ => M.connCubeVertexMass_toReal_le_markedPolygon r hχne y
  rw [M.connCubeMass_toReal_eq_sum_vertex r (hc r hr)]
  refine hstep1.trans ?_
  rw [Finset.sum_comm]
  have hfac : ∀ ℓ : ℕ, ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
        (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
          ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ) *
            PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y)
      = (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
          ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ) *
            ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
              PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y) := by
    intro ℓ
    rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [hfac]
  have hIcc : (Finset.Icc 1 4 : Finset ℕ) = insert 4 (Finset.Icc 1 3) := by
    ext ℓ
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h4mem : (4 : ℕ) ∉ Finset.Icc 1 3 := by simp [Finset.mem_Icc]
  rw [hIcc, Finset.sum_insert h4mem]
  have hcol : ∀ ℓ ∈ Finset.Icc 1 3,
      ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
          PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y
        ≤ (M.cutMassAt r 0).toReal ^ ℓ := by
    intro ℓ _
    refine (Summable.sum_le_tsum _ (fun i _ => PercLib.CriticalLRP.I418C.polyK_nonneg _
      (fun a b => M.cutTwoPoint_nonneg r a b) ℓ 0 i)
      (M.polyK_summable_colSum r hχne ℓ)).trans (le_of_eq (M.polyK_colSum_toReal r hχne ℓ))
  have hfirst : ∑ ℓ ∈ Finset.Icc 1 3, (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
        ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ) *
          ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
            PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y)
      ≤ ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
            + PercLib.CriticalLRP.I417Marked.markedCount 3 2
            + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
          * (M.cutMassAt r 0).toReal ^ 7 := by
    have hsingle : ∀ ℓ ∈ Finset.Icc 1 3,
        (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
          ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ) *
            ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
              PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y)
        ≤ (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ)
            * (M.cutMassAt r 0).toReal ^ 7 := by
      intro ℓ hℓ
      obtain ⟨h1, h3⟩ := Finset.mem_Icc.mp hℓ
      have hpoweq : (M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ)
            * (M.cutMassAt r 0).toReal ^ ℓ = (M.cutMassAt r 0).toReal ^ 7 := by
        rw [← pow_add]
        congr 1
        omega
      calc (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
            ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ) *
              ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
                PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y)
          ≤ (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
              ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ)
                * (M.cutMassAt r 0).toReal ^ ℓ) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcol ℓ hℓ)
              (pow_nonneg hχ0 _)) (hd0 ℓ)
        _ = (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ)
              * (M.cutMassAt r 0).toReal ^ 7 := by rw [hpoweq]
    refine (Finset.sum_le_sum hsingle).trans (le_of_eq ?_)
    have hsum3 : ∑ ℓ ∈ (Finset.Icc 1 3 : Finset ℕ),
          (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ)
        = ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
            + PercLib.CriticalLRP.I417Marked.markedCount 3 2
            + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ) := by
      have hins : (Finset.Icc 1 3 : Finset ℕ) = insert 1 (insert 2 (insert 3 ∅)) := by decide
      rw [hins]
      simp [Nat.cast_add]
      ring
    rw [← Finset.sum_mul, hsum3]
  have hfour : (PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℝ) *
        ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - 4) *
          ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
            PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 y)
      ≤ (PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℝ) * Cp
          * ((M.ball r).ncard : ℝ) * M.case3Driver c r
          * (M.cutMassAt r 0).toReal ^ 4 := by
    have hsumle : ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
          PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 y
        ≤ ((PercLib.CriticalLRP.E1Sign.ballF M r).card : ℝ)
            * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
      calc ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
            PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 y
          ≤ ∑ _y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
              (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :=
            Finset.sum_le_sum fun y _ => hpoly4 r hr y
        _ = ((PercLib.CriticalLRP.E1Sign.ballF M r).card : ℝ)
              * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rw [PercLib.CriticalLRP.E1Sign.card_ballF] at hsumle
    have hexp : (2 * 3 + 1 - 4 : ℕ) = 3 := by norm_num
    rw [hexp]
    calc (PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℝ) *
          ((M.cutMassAt r 0).toReal ^ 3 *
            ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
              PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 y)
        ≤ (PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℝ) *
            ((M.cutMassAt r 0).toReal ^ 3 *
              (((M.ball r).ncard : ℝ)
                * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumle
            (pow_nonneg hχ0 _)) (hd0 4)
      _ = (PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℝ) * Cp
            * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := by ring
  calc (PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℝ) *
        ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - 4) *
          ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
            PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 y)
      + ∑ ℓ ∈ Finset.Icc 1 3, (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
          ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ) *
            ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
              PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y)
      ≤ ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℝ) * Cp
            * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4)
          + ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
              + PercLib.CriticalLRP.I417Marked.markedCount 3 2
              + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
            * (M.cutMassAt r 0).toReal ^ 7 := add_le_add hfour hfirst
    _ = ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
            + PercLib.CriticalLRP.I417Marked.markedCount 3 2
            + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
            * (M.cutMassAt r 0).toReal ^ 7
          + (PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℝ) * Cp
            * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := by ring


end PercLib.CriticalLRP.Orchestration.SourceModelData
namespace PercLib.CriticalLRP.Case3MarkedAlg

/-- **The Case-3 division step, with the residual `χ^7` term retained.**

For `A, B ≥ 0`, `χ, b, c₃, A₂ > 0` and the moment gap `c₃ χ³ ≤ A₂`,

`(A χ^7 + B b drv χ^4) / (b χ A₂) ≤ (A / c₃) (χ³ / b) + (B / c₃) drv`.

The first summand is the low-order polygon residual `χ³/|B_r|` and the second the driver term;
no moment gap beyond `c₃ χ³ ≤ A₂` is used, and the powers are the source's own
(`2p + 2q + 1 = 7` for `p = 3`, `q = 0`). -/
theorem residual_div_le {A B χ b drv A2 c3 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hχ : 0 < χ)
    (hb : 0 < b) (hA2 : 0 < A2) (hc3 : 0 < c3) (hdrv : 0 ≤ drv)
    (hgm : c3 * χ ^ 3 ≤ A2) :
    (A * χ ^ 7 + B * b * drv * χ ^ 4) / (b * χ * A2)
      ≤ (A / c3) * (χ ^ 3 / b) + (B / c3) * drv := by
  have hbχ : (0 : ℝ) < b * χ := by positivity
  have hden : (0 : ℝ) < b * χ * A2 := by positivity
  rw [div_le_iff₀ hden]
  have hkey : ((A / c3) * (χ ^ 3 / b) + (B / c3) * drv) * (b * χ * (c3 * χ ^ 3))
      = A * χ ^ 7 + B * b * drv * χ ^ 4 := by
    field_simp
  have hmul : b * χ * (c3 * χ ^ 3) ≤ b * χ * A2 :=
    mul_le_mul_of_nonneg_left hgm (le_of_lt hbχ)
  have hnonneg : (0 : ℝ) ≤ (A / c3) * (χ ^ 3 / b) + (B / c3) * drv := by positivity
  calc A * χ ^ 7 + B * b * drv * χ ^ 4
      = ((A / c3) * (χ ^ 3 / b) + (B / c3) * drv) * (b * χ * (c3 * χ ^ 3)) := hkey.symm
    _ ≤ ((A / c3) * (χ ^ 3 / b) + (B / c3) * drv) * (b * χ * A2) :=
        mul_le_mul_of_nonneg_left hmul hnonneg

end PercLib.CriticalLRP.Case3MarkedAlg

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-- **The Case-3 error estimate with the marked numerator**, retaining the low-order residual.

Under the marked `p = 3`, `q = 0` gap (no per-vertex `ℓ = 3` sup bound is used), the `ℓ = 4`
polygon bound, and the moment gap `c₃ χ³ ≤ E_{β_c,r}|K|²`, the second-moment excluded error
satisfies

`E_{2,r} ≤ (c₃^{-1} ∑_{ℓ≤3} markedCount 3 ℓ) · χ³/|B_r| + (c₃^{-1} markedCount 3 4 · Cp) · (∇_{r^c} + r^{-c})`.

The first term is the honest residual of the `ℓ ≤ 3` polygon orders; it vanishes exactly when
`χ³ ≺ |B_r|` (case 1, `d > 3α`), and is `O(1)` at the borderline `d = 3α`. -/
theorem p2ExclError_le_markedResidual (c Cp c3 : ℝ) (hCp : 0 ≤ Cp) (hc3 : 0 < c3) {r₀ : ℝ}
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 x ≤
        Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r ≤
      (((PercLib.CriticalLRP.I417Marked.markedCount 3 1
          + PercLib.CriticalLRP.I417Marked.markedCount 3 2
          + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ) / c3)
          * ((M.cutMassAt r 0).toReal ^ 3 / ((M.ball r).ncard : ℝ))
        + (((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp / c3)
            * M.case3Driver c r := by
  filter_upwards [M.connCubeMass_toReal_le_markedPolygon c Cp hCp hc hχ hpoly4, hgm,
    eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)] with r hnum hg hr0 hr1
  have h2r := h2 r hr0
  have h1ne : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2r
  have hχeq : (M.cutMoment 1 r).toReal = (M.cutMassAt r 0).toReal := by
    rw [← M.cutMassAt_zero_eq_cutMoment r]
  have hχpos : (0 : ℝ) < (M.cutMassAt r 0).toReal := by
    have h := M.one_le_cutMoment_one_toReal r h1ne
    rw [hχeq] at h
    linarith
  have hA2pos : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have h := M.one_le_cutMoment_two_toReal r h2r
    linarith
  have hbpos : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r (le_trans zero_le_one hr1)
  have hp2 := M.p2ExclError_le_connCubeMass_div r (le_trans zero_le_one hr1) h2r (hc r hr1)
  rw [hχeq] at hp2
  have hden : (0 : ℝ) < ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal
      * (M.cutMoment 2 r).toReal := by positivity
  refine hp2.trans ?_
  refine (div_le_div_of_nonneg_right hnum hden.le).trans ?_
  exact PercLib.CriticalLRP.Case3MarkedAlg.residual_div_le
    (A := ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
      + PercLib.CriticalLRP.I417Marked.markedCount 3 2
      + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ))
    (B := ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp)
    (χ := (M.cutMassAt r 0).toReal) (b := ((M.ball r).ncard : ℝ))
    (drv := M.case3Driver c r) (A2 := (M.cutMoment 2 r).toReal) (c3 := c3)
    (by positivity) (by positivity) hχpos hbpos hA2pos hc3
    (M.case3Driver_nonneg_of_one_le hr1) hg


/-- **The single scalar condition that replaces the `ℓ = 3` sup bound.**

If in addition `χ³ ≼ |B_r| · (∇_{r^c} + r^{-c})` — the honest form of the `ℓ ≤ 3` residual
being negligible — then the Case-3 numerator takes exactly the shape
`K' |B_r| drv χ^4` that the landed Case-3 chain consumes as `hnum`
(`p2ExclError_le_case3Driver`), with the explicit constant
`K' = (∑_{ℓ≤3} markedCount 3 ℓ) · K + markedCount 3 4 · Cp`. -/
theorem connCubeMass_toReal_le_of_chi_cube_le (c Cp K : ℝ) (hCp : 0 ≤ Cp) (hK : 0 ≤ K)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 x ≤
        Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hsmall : ∀ᶠ r : ℝ in atTop,
      (M.cutMassAt r 0).toReal ^ 3 ≤ K * ((M.ball r).ncard : ℝ) * M.case3Driver c r) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      ((((PercLib.CriticalLRP.I417Marked.markedCount 3 1
            + PercLib.CriticalLRP.I417Marked.markedCount 3 2
            + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ) * K
          + ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp)
        * ((M.ball r).ncard : ℝ) * M.case3Driver c r
          * (M.cutMassAt r 0).toReal ^ 4) := by
  filter_upwards [M.connCubeMass_toReal_le_markedPolygon c Cp hCp hc hχ hpoly4, hsmall,
    eventually_ge_atTop (1 : ℝ)] with r hnum hsm hr1
  have hχ0 : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
  have hb0 : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := Nat.cast_nonneg _
  have hdrv0 : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
  have hA0 : (0 : ℝ) ≤ ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
      + PercLib.CriticalLRP.I417Marked.markedCount 3 2
      + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp :=
    mul_nonneg (Nat.cast_nonneg _) hCp
  have h1 : ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
        + PercLib.CriticalLRP.I417Marked.markedCount 3 2
        + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
        * (M.cutMassAt r 0).toReal ^ 7
      ≤ ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
          + PercLib.CriticalLRP.I417Marked.markedCount 3 2
          + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
          * (K * ((M.ball r).ncard : ℝ) * M.case3Driver c r)
          * (M.cutMassAt r 0).toReal ^ 4 := by
    have hmain : (M.cutMassAt r 0).toReal ^ 4 * (M.cutMassAt r 0).toReal ^ 3
        ≤ K * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := by
      calc (M.cutMassAt r 0).toReal ^ 4 * (M.cutMassAt r 0).toReal ^ 3
          ≤ (M.cutMassAt r 0).toReal ^ 4
              * (K * ((M.ball r).ncard : ℝ) * M.case3Driver c r) :=
            mul_le_mul_of_nonneg_left hsm (pow_nonneg hχ0 4)
        _ = K * ((M.ball r).ncard : ℝ) * M.case3Driver c r
              * (M.cutMassAt r 0).toReal ^ 4 := by ring
    calc ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
          + PercLib.CriticalLRP.I417Marked.markedCount 3 2
          + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
          * (M.cutMassAt r 0).toReal ^ 7
        = ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
            + PercLib.CriticalLRP.I417Marked.markedCount 3 2
            + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
            * ((M.cutMassAt r 0).toReal ^ 4 * (M.cutMassAt r 0).toReal ^ 3) := by
          rw [show (M.cutMassAt r 0).toReal ^ 7
            = (M.cutMassAt r 0).toReal ^ 4 * (M.cutMassAt r 0).toReal ^ 3 by ring]
      _ ≤ ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
            + PercLib.CriticalLRP.I417Marked.markedCount 3 2
            + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
            * (K * ((M.ball r).ncard : ℝ) * M.case3Driver c r
              * (M.cutMassAt r 0).toReal ^ 4) := mul_le_mul_of_nonneg_left hmain hA0
      _ = ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
            + PercLib.CriticalLRP.I417Marked.markedCount 3 2
            + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
            * (K * ((M.ball r).ncard : ℝ) * M.case3Driver c r)
            * (M.cutMassAt r 0).toReal ^ 4 := by ring
  calc (M.connCubeMass r).toReal
      ≤ ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
          + PercLib.CriticalLRP.I417Marked.markedCount 3 2
          + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
          * (M.cutMassAt r 0).toReal ^ 7
        + ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp
          * ((M.ball r).ncard : ℝ) * M.case3Driver c r
          * (M.cutMassAt r 0).toReal ^ 4 := hnum
    _ ≤ (((PercLib.CriticalLRP.I417Marked.markedCount 3 1
            + PercLib.CriticalLRP.I417Marked.markedCount 3 2
            + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ) * K
          + ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp)
          * ((M.ball r).ncard : ℝ) * M.case3Driver c r
          * (M.cutMassAt r 0).toReal ^ 4 := by
        have h2 : ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp
            * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4
            ≤ (((PercLib.CriticalLRP.I417Marked.markedCount 3 1
                + PercLib.CriticalLRP.I417Marked.markedCount 3 2
                + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ) * K
              + ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp)
              * ((M.ball r).ncard : ℝ) * M.case3Driver c r
              * (M.cutMassAt r 0).toReal ^ 4 := by
          have hAK : (0 : ℝ) ≤ ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
              + PercLib.CriticalLRP.I417Marked.markedCount 3 2
              + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ) * K :=
            mul_nonneg hA0 hK
          have hnon : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) * M.case3Driver c r
              * (M.cutMassAt r 0).toReal ^ 4 := by positivity
          nlinarith [hAK, hnon, hB0]
        linarith [h1, h2]

/-- **Capstone: the Case-3 error `E_{2,r} → 0` with the marked numerator only.**

Every analytic input of the landed Case-3 chain `p2ExclError_tendsto_zero_of_case3` is kept
except `hnum`: it is *derived* here from the marked `p = 3`, `q = 0` gap, the `ℓ = 4` polygon
bound and the one scalar condition `χ³ ≼ |B_r| drv`.  In particular neither the per-vertex
`p = 3`, `q = 0` moment gap `hgap` nor the column-uniform `ℓ = 3` sup bound `hT3` is assumed. -/
theorem p2ExclError_tendsto_zero_of_markedPolygon (c Cp K c3 : ℝ) (hCp : 0 ≤ Cp) (hK : 0 ≤ K)
    (hc3 : 0 < c3) {r₀ : ℝ}
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 x ≤
        Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hsmall : ∀ᶠ r : ℝ in atTop,
      (M.cutMassAt r 0).toReal ^ 3 ≤ K * ((M.ball r).ncard : ℝ) * M.case3Driver c r)
    (hgm : ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hK' : (0 : ℝ) ≤ (((PercLib.CriticalLRP.I417Marked.markedCount 3 1
        + PercLib.CriticalLRP.I417Marked.markedCount 3 2
        + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ) * K
      + ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp) :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hK) (mul_nonneg (Nat.cast_nonneg _) hCp)
  exact M.p2ExclError_tendsto_zero_of_case3 (K := (((PercLib.CriticalLRP.I417Marked.markedCount 3 1
        + PercLib.CriticalLRP.I417Marked.markedCount 3 2
        + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ) * K
      + ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp))
    (r₀ := r₀) hK' hc3 h2 hc
    (M.connCubeMass_toReal_le_of_chi_cube_le c Cp K hCp hK hc hχ hpoly4 hsmall) hgm hdrv

/-- **The `ℓ = 4` polygon input discharged by the landed all-radius manufacturer.**

`SecondMomentCase3.exists_polygonBound_four` (itself
`I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii` at `ℓ = 4`)
produces the constants `c`, `Cp` of `connCubeMass_toReal_le_markedPolygon`, so the numerator
bound below has no polygon-side hypothesis left.  The only remaining inputs are the two
finiteness statements carried by the landed chain; the scalar condition on `χ³` is the one
recorded separately in `connCubeMass_toReal_le_of_chi_cube_le`. -/
theorem exists_connCubeMass_toReal_le_markedPolygon
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) :
    ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧ ∀ᶠ r : ℝ in atTop,
      (M.connCubeMass r).toReal ≤
        ((PercLib.CriticalLRP.I417Marked.markedCount 3 1
            + PercLib.CriticalLRP.I417Marked.markedCount 3 2
            + PercLib.CriticalLRP.I417Marked.markedCount 3 3 : ℕ) : ℝ)
            * (M.cutMassAt r 0).toReal ^ 7
          + ((PercLib.CriticalLRP.I417Marked.markedCount 3 4 : ℕ) : ℝ) * Cp
            * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := by
  obtain ⟨c, Cp, hcpos, hCppos, hbound⟩ :=
    PercLib.CriticalLRP.Orchestration.SourceModelData.exists_polygonBound_four M hP hTri
  exact ⟨c, Cp, hcpos, hCppos, M.connCubeMass_toReal_le_markedPolygon c Cp hCppos.le
    hc hχ (fun r hr x => hbound r (lt_of_lt_of_le one_pos hr) x)⟩

end PercLib.CriticalLRP.Orchestration.SourceModelData

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Case3MarkedAudit

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_eq_jointPow
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_le_markedPolygon
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_toReal_le_markedPolygon
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.polyK_colSum_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_markedPolygon
#print axioms PercLib.CriticalLRP.Case3MarkedAlg.residual_div_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_markedResidual
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_of_chi_cube_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_markedPolygon
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_connCubeMass_toReal_le_markedPolygon

end PercLib.CriticalLRP.Case3MarkedAudit
