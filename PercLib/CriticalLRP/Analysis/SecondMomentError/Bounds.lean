/-
Integrated and independently rebuilt from accepted Ultramath `smwytmnfc`, member `m2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwytmnfc`, member `m2`, direction d1, integrated at production base
`1ec5a682a47b12ced34931ce440a902cc4924184`.

# The two bounds of (I.4.16) for the source second-moment excluded error

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, display (I.4.16):

```
                                  E_{β_c,r}[ |K|³ |K ∩ B_r| ]
    0 ≤ E_{2,r} ≤ ----------------------------------------------- .
                     |B_r| E_{β_c,r}|K| E_{β_c,r}|K|²
```

Both halves are *covariance* statements.  With `U := E[|K|∑_{y∈B_r} 1(y∉K)|K_y|²]`,
`P := |B_r| E|K| E|K|²` and `C := E[|K|³ #(K ∩ B_r)]`, the numerator of `E_{2,r}` is `P − U`:

* `U ≤ P` is the disconnected half of Lemma I.2.1, i.e. `M.exclMassQuad_le_ball_mul_moments`;
* `P ≤ U + C` is the Harris–FKG half with the connected third moment retained, i.e.
  `M.ball_mul_moments_le_exclMassQuad_add_connCubeMass`.

So `0 ≤ P − U ≤ C`, and dividing by the positive `P` gives (I.4.16).  This file carries out that
division in `ℝ`, with the `ℝ≥0∞ → ℝ` conversion justified by the explicit finiteness hypotheses
`M.cutMoment 2 r ≠ ⊤` (which forces `M.cutMoment 1 r ≠ ⊤` and `M.exclMassQuad r ≠ ⊤` through
the covariance bound) and `M.connCubeMass r ≠ ⊤` (the genuine extra input, supplied in the paper
by the tree-graph inequality).  There is no `toReal ⊤ = 0` step anywhere: if any of those objects
is `⊤`, the statements are not made.

No asymptotic statement is made here: (I.4.16) is a pointwise inequality in `r`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentError.Defs

/-! # Second-moment error: Bounds -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP
namespace SecondMomentError

/-! ## Elementary real algebra of `cE2`

`VolumeMoments.cE2 A A2 U b = (b·A·A2 − U) / (b·A·A2)` is the paper's `E_{2,r}` before any
probabilistic input: the next two lemmas are the whole of the arithmetic. -/

/-- `E_{2,r} ≥ 0` when the excluded mass does not exceed the mean-field window product. -/
theorem cE2_nonneg {A A2 U b : ℝ} (hA : 0 < A) (hA2 : 0 < A2) (hb : 0 < b)
    (hU : U ≤ b * A * A2) :
    0 ≤ VolumeMoments.cE2 A A2 U b := by
  unfold VolumeMoments.cE2
  refine div_nonneg ?_ (by positivity)
  linarith

/-- `E_{2,r} ≤ C / (b·A·A2)`: the deficit `b·A·A2 − U` is at most the connected third moment. -/
theorem cE2_le {A A2 U C b : ℝ} (hA : 0 < A) (hA2 : 0 < A2) (hb : 0 < b)
    (hU : b * A * A2 ≤ U + C) :
    VolumeMoments.cE2 A A2 U b ≤ C / (b * A * A2) := by
  have hden : (0 : ℝ) < b * A * A2 := by positivity
  unfold VolumeMoments.cE2
  rw [div_le_div_iff_of_pos_right hden]
  linarith

/-- The two halves of (I.4.16) in pure real form. -/
theorem cE2_mem_Icc {A A2 U C b : ℝ} (hA : 0 < A) (hA2 : 0 < A2) (hb : 0 < b)
    (hU : U ≤ b * A * A2) (hU' : b * A * A2 ≤ U + C) :
    0 ≤ VolumeMoments.cE2 A A2 U b ∧
      VolumeMoments.cE2 A A2 U b ≤ C / (b * A * A2) :=
  ⟨cE2_nonneg hA hA2 hb hU, cE2_le hA hA2 hb hU'⟩

end SecondMomentError

namespace Orchestration
namespace SourceModelData

open SecondMomentError

variable (M : SourceModelData)

/-! ## The model denominator -/

/-- `|B_r| E|K| E|K|²` is finite as soon as the second cutoff moment is: the first moment is
smaller (`cutMoment_one_le_cutMoment_two`) and `|B_r|` is finite. -/
theorem p2WindowProduct_ne_top (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.p2WindowProduct r ≠ ⊤ := by
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hb : ((M.ball r).ncard : ℝ≥0∞) ≠ ⊤ := by simp
  simp only [p2WindowProduct]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hb h1) h2

/-- The `ℝ≥0∞ → ℝ` conversion of the denominator is the product of the converted factors. -/
theorem p2WindowProduct_toReal (r : ℝ) :
    (M.p2WindowProduct r).toReal
      = ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal := by
  simp only [p2WindowProduct, ENNReal.toReal_mul, ENNReal.toReal_natCast]

/-- `E|K| ≥ 1` in `ℝ`, from the root being in its own cluster. -/
theorem one_le_cutMoment_one_toReal (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) :
    (1 : ℝ) ≤ (M.cutMoment 1 r).toReal := by
  have h := ENNReal.toReal_mono h1 (M.one_le_cutMoment_one r)
  simpa using h

/-- `E|K|² ≥ 1` in `ℝ`. -/
theorem one_le_cutMoment_two_toReal (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (1 : ℝ) ≤ (M.cutMoment 2 r).toReal := by
  have hmono := M.cutMoment_one_le_cutMoment_two r
  have h := ENNReal.toReal_mono h2 (le_trans (M.one_le_cutMoment_one r) hmono)
  simpa using h

/-- The closed window `B_r` contains the origin as soon as `0 ≤ r`, so it is non-empty. -/
theorem ball_ncard_pos (r : ℝ) (hr : 0 ≤ r) : 0 < (M.ball r).ncard := by
  have hzero : (0 : M.V) ∈ M.ball r := by
    change M.S.ρ (toVec (0 : M.V)) ≤ r
    have h0 : toVec (0 : M.V) = 0 := by
      funext i
      simp [toVec]
    rw [h0, M.S.ρ_zero]
    exact hr
  exact (Set.ncard_pos (M.finite_ball r)).mpr ⟨0, hzero⟩

/-! ## (I.4.16): the two bounds at the actual cutoff model -/

/-- **The sign half of (I.4.16).**  `0 ≤ E_{2,r}` at the source cutoff moments. -/
theorem p2ExclError_nonneg (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    0 ≤ M.p2ExclError r := by
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have htop : M.p2WindowProduct r ≠ ⊤ := M.p2WindowProduct_ne_top r h2
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := M.one_le_cutMoment_one_toReal r h1
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := M.one_le_cutMoment_two_toReal r h2
    linarith
  have hU : (M.exclMassQuad r).toReal
      ≤ ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal := by
    have h := ENNReal.toReal_mono htop (M.exclMassQuad_le_ball_mul_moments r)
    rwa [M.p2WindowProduct_toReal r] at h
  exact SecondMomentError.cE2_nonneg hA hA2 hb hU

/-- **The upper half of (I.4.16), in the paper's shape.**

`E_{2,r} ≤ E_{β_c,r}[|K|³ |K ∩ B_r|] / (|B_r| E|K| E|K|²)`.

The single extra finiteness input beyond the second cutoff moment is `M.connCubeMass r ≠ ⊤`, the
connected third window moment of the right-hand side. -/
theorem p2ExclError_le_connCubeMass_div (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤)
    (hc : M.connCubeMass r ≠ ⊤) :
    M.p2ExclError r ≤ (M.connCubeMass r).toReal
      / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal) := by
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have htop : M.p2WindowProduct r ≠ ⊤ := M.p2WindowProduct_ne_top r h2
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := M.one_le_cutMoment_one_toReal r h1
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := M.one_le_cutMoment_two_toReal r h2
    linarith
  have hUfin : M.exclMassQuad r ≠ ⊤ :=
    ne_top_of_le_ne_top htop (M.exclMassQuad_le_ball_mul_moments r)
  have hsum : (M.exclMassQuad r + M.connCubeMass r) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hUfin, hc⟩
  have hU : ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal
      ≤ (M.exclMassQuad r).toReal + (M.connCubeMass r).toReal := by
    have h := ENNReal.toReal_mono hsum (M.ball_mul_moments_le_exclMassQuad_add_connCubeMass r)
    rw [ENNReal.toReal_add hUfin hc] at h
    simpa only [p2WindowProduct, ENNReal.toReal_mul, ENNReal.toReal_natCast] using h
  exact SecondMomentError.cE2_le hA hA2 hb hU

/-- **Both halves of (I.4.16)** at the actual cutoff model, as an interval. -/
theorem p2ExclError_mem_Icc (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤)
    (hc : M.connCubeMass r ≠ ⊤) :
    0 ≤ M.p2ExclError r ∧
      M.p2ExclError r ≤ (M.connCubeMass r).toReal
        / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal) :=
  ⟨M.p2ExclError_nonneg r hr h2, M.p2ExclError_le_connCubeMass_div r hr h2 hc⟩

/-- **The upper half of (I.4.16) with the paper's expectation
`E_{β_c,r}[|K_0|³ #(K_0 ∩ B_r)]` displayed as an integral**, via `M.connCubeMass_eq_lintegral`:
the same bound with the numerator written as the cutoff-law integral of
`|K_0|³ · #{y ∈ B_r : y ∈ K_0}`. -/
theorem p2ExclError_le_connCubeLin_div (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤)
    (hlin : (∫⁻ ω, clusterVol ω (0 : M.V) ^ 3 *
        ∑ y ∈ E1Sign.ballF M r,
          (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(M.cutLaw r)) ≠ ⊤) :
    M.p2ExclError r ≤ (∫⁻ ω, clusterVol ω (0 : M.V) ^ 3 *
        ∑ y ∈ E1Sign.ballF M r,
          (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(M.cutLaw r)).toReal
      / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal) := by
  have hc : M.connCubeMass r ≠ ⊤ := by
    rw [M.connCubeMass_eq_lintegral r]
    exact hlin
  have h := M.p2ExclError_le_connCubeMass_div r hr h2 hc
  rwa [M.connCubeMass_eq_lintegral r] at h

/-- **The paper's first step in Case 1**: `E[|K|³ #(K ∩ B_r)] ≤ E|K|⁴`, so (I.4.16) also gives
`E_{2,r} ≤ E_{β_c,r}|K|⁴ / (|B_r| E|K| E|K|²)`. -/
theorem p2ExclError_le_fourth_div (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤)
    (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.p2ExclError r ≤ (M.cutMoment 4 r).toReal
      / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal) := by
  have hc : M.connCubeMass r ≠ ⊤ := M.connCubeMass_ne_top h4
  refine (M.p2ExclError_le_connCubeMass_div r hr h2 hc).trans ?_
  have hle : (M.connCubeMass r).toReal ≤ (M.cutMoment 4 r).toReal :=
    ENNReal.toReal_mono h4 (M.connCubeMass_le_fourth r)
  have hden : (0 : ℝ) < ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal
      * (M.cutMoment 2 r).toReal := by
    have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
      exact_mod_cast M.ball_ncard_pos r hr
    have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
    have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
      have := M.one_le_cutMoment_one_toReal r h1
      linarith
    have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
      have := M.one_le_cutMoment_two_toReal r h2
      linarith
    positivity
  exact div_le_div_of_nonneg_right hle hden.le

/-! ## The second displayed form of `E_{2,r}`

The paper also writes the numerator as
`|B_r| E|K| E|K|² − E[|K| ∑_{y∈B_r}|K_y|²] + E[|K|³ #(K ∩ B_r)]`.
At the model, `E[|K| ∑_{y∈B_r}|K_y|²]` is `M.quadPairMass r`, and
`M.quadPairMass r = M.connCubeMass r + M.exclMassQuad r` is the per-vertex split of that sum into
its connected and excluded parts.  Hence the two displayed definitions of `E_{2,r}` agree. -/
theorem p2ExclError_eq_second_form (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤)
    (hc : M.connCubeMass r ≠ ⊤) :
    M.p2ExclError r =
      (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal
        - (M.quadPairMass r).toReal + (M.connCubeMass r).toReal)
      / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal) := by
  have htop : M.p2WindowProduct r ≠ ⊤ := M.p2WindowProduct_ne_top r h2
  have hUfin : M.exclMassQuad r ≠ ⊤ :=
    ne_top_of_le_ne_top htop (M.exclMassQuad_le_ball_mul_moments r)
  have hsplit : (M.quadPairMass r).toReal
      = (M.connCubeMass r).toReal + (M.exclMassQuad r).toReal := by
    rw [M.quadPairMass_eq_connCube_add r, ENNReal.toReal_add hc hUfin]
  have hexcl : (M.exclMassQuad r).toReal
      = (M.quadPairMass r).toReal - (M.connCubeMass r).toReal := by
    rw [hsplit]; ring
  simp only [p2ExclError, VolumeMoments.cE2]
  rw [hexcl]
  ring

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
