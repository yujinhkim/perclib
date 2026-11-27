/-
Accepted and independently rebuilt from Ultramath `smwzg77c3`, member `m3`, direction `d3`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The per-vertex two-term `hgap` at `p = 3`, `q = 0` is false at the root

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.  Lemma I.4.17 (printed p. 45), Proposition I.4.20 (printed p. 48), and the
proof of Proposition I.4.15, Case 3 (printed pp. 46–47).

## The result

`not_hasPerVertexTwoTermHgap`: for every `c > 0` and every model `M` satisfying the source's
Case-3 inputs `QZeroDiagInputs M c`, and for every pair of constants `C₃, C₄ ≥ 0`, the per-vertex
estimate

`(M.connCubeVertexMass r y).toReal ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³`   (`r ≥ 1`, all `y`)

**fails**.  This is *not* a claim about Lemma I.4.17 in the range `q ≥ 1`, nor about
Propositions I.4.15/I.4.20: it is a statement about the `q = 0` per-vertex two-term form, which is
what the Case-3 numerator consumer asks for.

## Why it fails, in one line

At the root `y = 0` (which is in every window `B_r` for `r ≥ 1`):

* the left-hand side is `E_{β_c,r}[|K_0|³ 1(0 ∈ K_0)] = E_{β_c,r}|K|³`, i.e. the **third cutoff
  moment**, `⪰ c χ^5` by the source's Proposition I.4.20 together with `E|K|² ⪰ χ³`
  (`connCubeVertexMass_zero`, `thirds_lower`);
* the right-hand side is `C₃ T³(0,0) χ⁴ + C₄ T⁴(0,0) χ³`.  The source's triangle condition is
  exactly `T³(0,0) ≤ ∇ = M.triSelf`, and diagonal maximality (`PowerInputs.comp` with `n = 1`
  plus `PowerInputs.triSup`) gives `T⁴(0,0) ≤ ∇ χ`.  Both terms are therefore `⪯ χ⁴`, while the
  left-hand side is `⪰ χ^5`,
  and `χ = E_{β_c,r}|K|` is unbounded (`chi_unbounded`).

So the two-term form is off by exactly one power of `χ` at the diagonal.  This is not an artefact
of the constants: `T³(0,0)` is the triangle diagram `∇`, bounded *away from* `χ` — indeed
`1 ≤ T³(0,0) ≤ ∇` — whereas the sum `∑_y T³(0,y)` equals `χ³` (`PowerInputs.colsum 3`).

## The corrected shape

The failure is intrinsic to evaluating `T³` at the diagonal, and it disappears as soon as the
estimate is *summed over the window*, which is how the source uses Lemma I.4.17:

```
∑_{y ∈ B_r} T³(0,y) = χ³   (PowerInputs.colsum 3)
```

so the summed `ℓ = 3` term is `C₃ χ⁴ · χ³ = C₃ χ^7` on the nose, and the diagonal value `∇` is a
factor `χ³ / ∇` smaller than the row sum.  Consequently (i) the per-vertex two-term form is false,
(ii) any per-vertex form that is summed must carry the `ℓ = 1, 2` terms `T(0,y) χ^6` and
`T²(0,y) χ^5` (the `χ^7` / `χ^6` residuals that the landed all-`p` marked bound produces), and
(iii) the genuinely summable statement — the one the source actually needs at p. 46 — is the
*window-summed* bound with the diagonal figure, which is a different (and weaker per term)
inequality that no per-vertex estimate with `T^ℓ(0,y)` can supply.

`NOTE.md` in this directory records the source quotations and the full derivation.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroDiagonal.Defs

/-! # The diagonal obstruction to the per-vertex `q = 0` two-term estimate -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

open PercLib.CriticalLRP

variable (M : SourceModelData)

/-! ## §1. The diagonal value of the per-vertex numerator

`y = 0` is a window vertex (`0 ∈ B_r` for every `r ≥ 1`), and at `y = 0` the Case-3 numerator is
the plain third cutoff moment. -/

/-- **The Case-3 per-vertex numerator at the root is the third cutoff moment**:
`E_{β_c,r}[|K_0|³ 1(0 ∈ K_0)] = E_{β_c,r}|K|³`.  No hypothesis: the cluster of `0` always
contains `0`. -/
theorem connCubeVertexMass_zero (r : ℝ) :
    M.connCubeVertexMass r (0 : M.V) = M.cutMoment 3 r := by
  rw [connCubeVertexMass, cutMoment]
  refine lintegral_congr fun ω => ?_
  rw [Set.indicator_of_mem (cluster_mem_self ω (0 : M.V)), mul_one]

/-! ## §2. The two right-hand-side diagrams at the diagonal

The `ℓ = 3` diagram at the diagonal is the triangle diagram `∇ = M.triSelf` (by the triangle
condition), and the `ℓ = 4` diagram is at most `∇ χ` by diagonal maximality. -/

/-- **`T⁴(0,0) ≤ ∇ · χ`.**  Composition at `n = 1` writes `T⁴(0,0) = ∑_y T³(0,y) T(y,0)`; the
triangle condition bounds `T³(0,y) ≤ ∇` at every `y`, and the column sum of `T` is `χ`. -/
theorem fourDiag_le_triSelf_mul_chi {r : ℝ}
    (H : I418C.PowerInputs (I418C.polyK (M.cutTwoPoint r)) M.triSelf (M.chiReal r)) :
    I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 ≤ M.triSelf * M.chiReal r := by
  have hcomp := H.comp 1
  have hsummable :
      Summable (fun y : M.V => M.triSelf * I418C.polyK (M.cutTwoPoint r) 1 y 0) :=
    (H.colSummable 1).mul_left M.triSelf
  calc I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0
      = ∑' y : M.V, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y *
          I418C.polyK (M.cutTwoPoint r) 1 y 0 := hcomp
    _ ≤ ∑' y : M.V, M.triSelf * I418C.polyK (M.cutTwoPoint r) 1 y 0 :=
        Summable.tsum_le_tsum (fun y => mul_le_mul_of_nonneg_right (H.triSup y) (H.nonneg 1 y 0))
          (H.compSummable 1) hsummable
    _ = M.triSelf * ∑' y : M.V, I418C.polyK (M.cutTwoPoint r) 1 y 0 := tsum_mul_left
    _ = M.triSelf * M.chiReal r := by rw [H.colsum 1, pow_one]

/-! ## §3. The diagonal inequality

Plugging `y = 0` into the target and using §1–§2 gives `c χ^5 ≤ (C₃ + C₄) ∇ χ⁴`, hence
`c χ ≤ (C₃ + C₄) ∇`. -/

/-- **The target implies `c χ ≤ (C₃ + C₄) ∇`.**  This is the exact content of the per-vertex
two-term estimate at `y = 0`. -/
theorem diag_inequality {r c C3 C4 : ℝ} (_hr : 1 ≤ r) (hχ1 : 1 ≤ M.chiReal r)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hdiag : (M.connCubeVertexMass r (0 : M.V)).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * M.chiReal r ^ 3)
    (H : I418C.PowerInputs (I418C.polyK (M.cutTwoPoint r)) M.triSelf (M.chiReal r))
    (hthird : c * M.chiReal r ^ 5 ≤ (M.cutMoment 3 r).toReal) :
    c * M.chiReal r ≤ (C3 + C4) * M.triSelf := by
  set χ := M.chiReal r
  have hχ0 : 0 ≤ χ := le_trans zero_le_one hχ1
  have hχpos : 0 < χ := lt_of_lt_of_le one_pos hχ1
  have hP3 : I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 ≤ M.triSelf := H.triSup 0
  have hP4 : I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 ≤ M.triSelf * χ :=
    fourDiag_le_triSelf_mul_chi M H
  have hstep1 : c * χ ^ 5 ≤ (M.cutMoment 3 r).toReal := hthird
  have hstep2 : (M.connCubeVertexMass r (0 : M.V)).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * χ ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3 := hdiag
  rw [connCubeVertexMass_zero] at hstep2
  have hA : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * χ ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3 ≤
      (C3 + C4) * M.triSelf * χ ^ 4 := by
    have hterm1 : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * χ ^ 4 ≤
        C3 * M.triSelf * χ ^ 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP3 hC3) (pow_nonneg hχ0 4)
    have hfour : I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3 ≤
        M.triSelf * χ ^ 4 := by
      calc I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3
          ≤ (M.triSelf * χ) * χ ^ 3 :=
            mul_le_mul_of_nonneg_right hP4 (pow_nonneg hχ0 3)
        _ = M.triSelf * χ ^ 4 := by ring
    have hterm2 : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3 ≤
        C4 * M.triSelf * χ ^ 4 := by
      calc C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3
          = C4 * (I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3) := by ring
        _ ≤ C4 * (M.triSelf * χ ^ 4) := mul_le_mul_of_nonneg_left hfour hC4
        _ = C4 * M.triSelf * χ ^ 4 := by ring
    linarith [hterm1, hterm2]
  have hchain : c * χ ^ 5 ≤ (C3 + C4) * M.triSelf * χ ^ 4 :=
    le_trans hstep1 (le_trans hstep2 hA)
  have hrew : c * χ ^ 5 = (c * χ) * χ ^ 4 := by ring
  have hpos : 0 < χ ^ 4 := pow_pos hχpos 4
  exact le_of_mul_le_mul_right (hrew ▸ hchain) hpos

/-! ## §4. The no-go -/

/-- **The diagonal contradiction.**  Any bound of the two-term shape *at the single vertex*
`y = 0` is incompatible with the source's Case-3 inputs: the left-hand side is `E|K|³ ⪰ c χ^5`,
the right-hand side is `≤ (C₃ + C₄) ∇ χ⁴`, and `χ → ∞`. -/
theorem diag_contradiction {c R : ℝ} (h : QZeroDiagInputs M c R) {C3 C4 : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hdiag : ∀ r : ℝ, 1 ≤ r →
      (M.connCubeVertexMass r (0 : M.V)).toReal ≤
        C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * (M.cutMassAt r 0).toReal ^ 4 +
          C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 *
            (M.cutMassAt r 0).toReal ^ 3) :
    False := by
  obtain ⟨r₀, hr₀, -⟩ := h.chi_unbounded 0
  have htri0 : 0 ≤ M.triSelf := by
    have H1 := h.powerInputs r₀ hr₀
    exact le_trans (H1.nonneg 3 (0 : M.V) (0 : M.V)) (H1.triSup 0)
  obtain ⟨r, hr, hB⟩ := h.chi_unbounded ((C3 + C4) * M.triSelf / c + 1)
  have hr1 : 1 ≤ r := le_trans (le_max_right R 1) hr
  have hχ1 : 1 ≤ M.chiReal r := h.chi_one_le r hr
  have hmain : c * M.chiReal r ≤ (C3 + C4) * M.triSelf :=
    diag_inequality M hr1 hχ1 hC3 hC4 (hdiag r hr1) (h.powerInputs r hr) (h.third_lower r hr)
  have hcl : (C3 + C4) * M.triSelf + c ≤ c * M.chiReal r := by
    have hmul : c * ((C3 + C4) * M.triSelf / c + 1) ≤ c * M.chiReal r :=
      mul_le_mul_of_nonneg_left hB (le_of_lt h.c_pos)
    have hc : c ≠ 0 := ne_of_gt h.c_pos
    have heq : c * ((C3 + C4) * M.triSelf / c + 1) = (C3 + C4) * M.triSelf + c := by
      field_simp
    rw [heq] at hmul
    exact hmul
  linarith [hmain, hcl, h.c_pos]

/-- **The per-vertex two-term `hgap` of the campaign is unsatisfiable** under the source's
Case-3 inputs, for any choice of the constants `C₃, C₄ ≥ 0`. -/
theorem not_hasPerVertexTwoTermHgap {c R : ℝ} (h : QZeroDiagInputs M c R) {C3 C4 : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) :
    ¬ M.HasPerVertexTwoTermHgap C3 C4 := by
  intro hgap
  exact diag_contradiction M h hC3 hC4 (fun r hr => hgap r hr 0)

/-- **No constants work.**  There is no pair `C₃, C₄ ≥ 0` for which the per-vertex two-term
estimate holds for all `r ≥ 1` and all vertices.  This is the literal negation of the campaign
target. -/
theorem no_perVertex_twoTerm_constants {c R : ℝ} (h : QZeroDiagInputs M c R) :
    ¬ ∃ C3 C4 : ℝ, 0 ≤ C3 ∧ 0 ≤ C4 ∧ M.HasPerVertexTwoTermHgap C3 C4 := by
  rintro ⟨C3, C4, h3, h4, hg⟩
  exact not_hasPerVertexTwoTermHgap M h h3 h4 hg

/-! ## §4b. The landed Case-3 `hgap` hypothesis is uninhabited

`SecondMomentCase3.connCubeMass_le_of_windowGap` consumes

```
hgap : ∀ r ≥ 1, ∀ y ∈ E1Sign.ballF M r,
  (M.connCubeVertexMass r y).toReal
    ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³
```

which is exactly the campaign target restricted to the window.  Since the root `0` is a window
vertex at every `r ≥ 1`, §4 kills this hypothesis too. -/

/-- **The root is a window vertex**: `0 ∈ E1Sign.ballF M r` for every `r ≥ 0`
(`M.ball r = {y | ρ y ≤ r}` and `ρ 0 = 0`). -/
theorem zero_mem_ballF {r : ℝ} (hr : 0 ≤ r) : (0 : M.V) ∈ E1Sign.ballF M r := by
  rw [E1Sign.mem_ballF]
  simp only [ball, Set.mem_ofPred_eq]
  have h0 : toVec (0 : M.V) = 0 := by
    funext i
    simp [toVec]
  rw [h0, M.S.ρ_zero]
  exact hr

/-- **The window `hgap` hypothesis of `connCubeMass_le_of_windowGap` is unsatisfiable** under the
source's Case-3 inputs, for every pair of constants `C₃, C₄ ≥ 0`.  This is the exact shape of the
hypothesis consumed by the landed Case-3 numerator estimate, i.e. the analogue of
`hcase3_unsatisfiable` for the `hgap` bundle. -/
theorem not_windowGap {c R : ℝ} (h : QZeroDiagInputs M c R) {C3 C4 : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) :
    ¬ (∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
        (M.connCubeVertexMass r y).toReal ≤
          C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y *
              (M.cutMassAt r 0).toReal ^ 4 +
            C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y *
              (M.cutMassAt r 0).toReal ^ 3) := by
  intro hg
  exact diag_contradiction M h hC3 hC4
    (fun r hr => hg r hr 0 (zero_mem_ballF M (le_trans zero_le_one hr)))

/-- **The landed window `hgap` holds for no constants.** -/
theorem no_windowGap_constants {c R : ℝ} (h : QZeroDiagInputs M c R) :
    ¬ ∃ C3 C4 : ℝ, 0 ≤ C3 ∧ 0 ≤ C4 ∧
      (∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
        (M.connCubeVertexMass r y).toReal ≤
          C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y *
              (M.cutMassAt r 0).toReal ^ 4 +
            C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y *
              (M.cutMassAt r 0).toReal ^ 3) := by
  rintro ⟨C3, C4, h3, h4, hg⟩
  exact not_windowGap M h h3 h4 hg

/-! ## §4c. The exact repair: isolate the root summand

`HasRepairedPerVertexHgap` is the same two-term estimate with `y ≠ 0`, and the root summand is
handled exactly.  The window sum then satisfies

```
∑_{y ∈ B_r} connCubeVertexMass r y ≤ E_{β_c,r}|K|³
    + |B_r| · (C₃ T³(0,0) χ⁴ + C₄ T⁴(0,0) χ³),
```

and the isolated diagonal summand `E|K|³` is comparable to `|B_r| ∇ χ⁴` in Case 3
(`χ ⪯ r^α ⪯ r^d ⪯ |B_r|` and `∇ ≥ 1`), so it is absorbable.  This is the correct per-vertex
input for the Case-3 numerator: per-vertex *away from the diagonal*, plus the diagonal exactly. -/

/-- **The repaired per-vertex input gives the Case-3 window numerator with the root summand
isolated.**  Uses `connCubeMass_toReal_eq_sum_vertex` (`E1Sign.ballF M r` is the window), the
repaired hypothesis on `y ≠ 0`, and diagonal maximality of the cutoff powers. -/
theorem windowSum_le_of_repaired {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) {r : ℝ}
    (hr : 1 ≤ r) (hχ : M.cutMassAt r 0 ≠ ⊤) (hfin : M.connCubeMass r ≠ ⊤)
    (h : M.HasRepairedPerVertexHgap C3 C4) :
    (M.connCubeMass r).toReal ≤ (M.cutMoment 3 r).toReal +
      ((E1Sign.ballF M r).card : ℝ) *
        (C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * M.chiReal r ^ 4 +
          C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * M.chiReal r ^ 3) := by
  set χ := M.chiReal r
  have hχ0 : 0 ≤ χ := ENNReal.toReal_nonneg
  have hχ4 : 0 ≤ χ ^ 4 := pow_nonneg hχ0 4
  have hχ3 : 0 ≤ χ ^ 3 := pow_nonneg hχ0 3
  rw [M.connCubeMass_toReal_eq_sum_vertex r hfin]
  have hzero : (0 : M.V) ∈ E1Sign.ballF M r :=
    zero_mem_ballF M (le_trans zero_le_one hr)
  rw [← Finset.add_sum_erase (E1Sign.ballF M r)
    (fun y => (M.connCubeVertexMass r y).toReal) hzero]
  have hf0 : (M.connCubeVertexMass r (0 : M.V)).toReal = (M.cutMoment 3 r).toReal := by
    rw [connCubeVertexMass_zero]
  rw [hf0]
  have hstep : ∀ y ∈ (E1Sign.ballF M r).erase (0 : M.V),
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * χ ^ 4 +
          C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3 := by
    intro y hy
    have hy0 : y ≠ 0 := (Finset.mem_erase.mp hy).1
    have h1 := h r hr y hy0
    have hp3 : I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 := M.source_polyK_le_diag r hχ 3 y
    have hp4 : I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y
        ≤ I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 := M.source_polyK_le_diag r hχ 4 y
    have e3 : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * χ ^ 4
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * χ ^ 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp3 hC3) hχ4
    have e4 : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * χ ^ 3
        ≤ C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp4 hC4) hχ3
    linarith [h1, e3, e4]
  have hsum : ∑ y ∈ (E1Sign.ballF M r).erase (0 : M.V), (M.connCubeVertexMass r y).toReal
      ≤ ∑ _y ∈ (E1Sign.ballF M r).erase (0 : M.V),
          (C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * χ ^ 4 +
            C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3) :=
    Finset.sum_le_sum hstep
  have hcard : ∑ _y ∈ (E1Sign.ballF M r).erase (0 : M.V),
        (C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * χ ^ 4 +
          C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3)
      ≤ ((E1Sign.ballF M r).card : ℝ) *
          (C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * χ ^ 4 +
            C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hP3 : 0 ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 :=
      I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 _ _
    have hP4 : 0 ≤ I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 :=
      I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 4 _ _
    have hnn : 0 ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * χ ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * χ ^ 3 := by
      have h1 := mul_nonneg (mul_nonneg hC3 hP3) hχ4
      have h2 := mul_nonneg (mul_nonneg hC4 hP4) hχ3
      linarith
    have hle : (((E1Sign.ballF M r).erase (0 : M.V)).card : ℝ) ≤ ((E1Sign.ballF M r).card : ℝ) := by
      exact_mod_cast Finset.card_erase_le
    exact mul_le_mul_of_nonneg_right hle hnn
  linarith [hsum, hcard]

/-! ## §5. Where the missing power of `χ` lives

The `ℓ = 3` diagram is `∇` *at the diagonal* but `χ³` when summed: the two differ by a factor
`χ³ / ∇`, which is exactly the defect of the per-vertex two-term form and the reason the `ℓ = 1,2`
terms (the `χ^7`, `χ^6` residuals) cannot be deleted from a per-vertex bound. -/

/-- **The `ℓ = 3` diagram sums to `χ³`** — the source's `∑_y T³(0,y) = (E_{β_c,r}|K|)³`. -/
theorem rowSum_polyK_three {r : ℝ}
    (H : I418C.PowerInputs (I418C.polyK (M.cutTwoPoint r)) M.triSelf (M.chiReal r)) :
    ∑' y : M.V, I418C.polyK (M.cutTwoPoint r) 3 y 0 = M.chiReal r ^ 3 :=
  H.colsum 3

/-- The diagonal value of the `ℓ = 3` diagram is a single term of that row sum, hence at most
`χ³`. -/
theorem polyK_three_diag_le_chi_cube {r : ℝ}
    (H : I418C.PowerInputs (I418C.polyK (M.cutTwoPoint r)) M.triSelf (M.chiReal r)) :
    I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 ≤ M.chiReal r ^ 3 := by
  calc I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0
      ≤ ∑' y : M.V, I418C.polyK (M.cutTwoPoint r) 3 y 0 :=
        Summable.le_tsum (H.colSummable 3) (0 : M.V) (fun j _ => H.nonneg 3 j 0)
    _ = M.chiReal r ^ 3 := H.colsum 3

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
