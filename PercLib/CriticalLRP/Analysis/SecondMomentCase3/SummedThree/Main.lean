/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m2`, direction `d1`.

# The ℓ = 3 boundary of the Case-3 numerator, repaired by summation

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1:
Lemma I.4.17 (p. 45), Lemma I.4.18 (p. 46), proof of Proposition I.4.15, Case 3 (p. 47).

## The gap addressed

`SecondMomentCase3.connCubeMass_le_of_windowGap` reduces the Case-3 numerator
`E[|K_0|^3 |K_0 ∩ B_r|]` to the per-vertex Lemma I.4.17 at `p = 3`, `q = 0` (`hgap`) plus two
polygon inputs:

* `hpoly4`, the vertexwise `ℓ = 4` bound `T^4_{β_c,r}(0,x) ≤ Cp (∇_{r^c}+r^{-c}) χ`; this is
  landed as the `ℓ = 4` half of
  `I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii` and is kept
  as a hypothesis here;
* `hT3`, the *vertexwise* `ℓ = 3` bound `T^3_{β_c,r}(0,y) ≤ Cp (∇_{r^c}+r^{-c})`.

`hT3` is not provable.  At every cutoff `T_{β_c,r}(0,0) = 1`, hence `T^3_{β_c,r}(0,0) ≥ 1`,
while `Cp (∇_{r^c}+r^{-c}) → 0`; this is `I418C.one_le_polyK_three` together with
`I418C.LowOrder.not_source_ell_three_bound`.  What the source's argument actually consumes is
the ℓ = 3 term **summed over the window**, and the honest majorant of that sum is not the
sup-tail `∇_{r^c}` but the normalized window average `|B_r|^{-1} Σ_{y∈B_r} ∇_{β_c}(0,y)` of the
*uncut* open triangle — the very quantity the source already uses for the first-moment defect
`𝓔_{1,r}` (Lemma I.4.11 and `TriangleAverage.normalized_ballSum_le_two_scale`).

## What is proved here

* `sum_polyK_three_ballF_le_near_far` — the near/far bound for the actual model window,
  transported from the landed `I420Case3.sum_polyK_three_le_near_far`;
* `sum_polyK_three_ballF_le_card_mul_case3ThreeDriver` — its normalized form, which produces
  the driver `M.case3ThreeDriver s θ r` of `Defs.lean`;
* `sum_perVertex_le_split` — the window summation of Lemma I.4.17's two terms when only the
  *sum* of the ℓ = 3 entries is controlled;
* `connCubeMass_toReal_le_of_splitGap` — the corrected Case-3 numerator with the vertexwise
  `hT3` replaced by the summed bound;
* `connCubeMass_le_of_source_threeDriver` — the same with the summed bound **derived** from
  the triangle condition; `hT3` no longer appears as a hypothesis;
* `ratio_le_of_moment_gap_split`, `p2ExclError_le_of_splitGap` — the corresponding `E_{2,r}`
  estimate with the two drivers `C_3 · (ℓ = 3)` and `C_4 · (ℓ ≥ 4)`.

The remaining hypotheses are the separate, still-open `q = 0` moment gap (Lemma I.4.17 at
`p = 3`, `q = 0`), the landed `ℓ = 4` polygon bound, the triangle condition, and the model's
open-triangle tail `M.nablaTail → 0`.  Lemma I.4.17 at `p = 3`, `q = 0` is *not* proved here.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.SummedThree.Defs
public import PercLib.CriticalLRP.Analysis.Polygon.NearBall

/-! # The summed ℓ = 3 Case-3 numerator and the corrected Case-3 consumer -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal NNReal Topology BigOperators

set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The near/far bound for the summed ℓ = 3 window entries -/

/-- **`Σ_{y ∈ B_r} T^3_{β_c,r}(0,y) ≤ |B_r| ∇_R + |s| ∇_{β_c}`.**

`B_r` is the model's window `E1Sign.ballF M r`, `s` any finite near set whose complement is at
distance `≥ R`, `∇_R` the uncut open-triangle tail `M.nablaTail R` and `∇_{β_c} = M.triSelf`
the triangle diagram.  This is `I420Case3.sum_polyK_three_le_near_far` rewritten at the
`|B_r|` of the Case-3 denominator (`E1Sign.card_ballF`). -/
theorem sum_polyK_three_ballF_le_near_far (r R : ℝ) (s : Finset M.V)
    (hfar : ∀ y ∈ E1Sign.ballF M r, y ∉ s → R ≤ M.S.dist 0 y)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) :
    ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y ≤
      ((M.ball r).ncard : ℝ) * (M.nablaTail R).toReal + (s.card : ℝ) * M.triSelf := by
  have h := I420Case3.sum_polyK_three_le_near_far M r R (E1Sign.ballF M r) s hfar hTri
  rwa [E1Sign.card_ballF M r] at h

/-- **The normalized summed ℓ = 3 bound.**  Dividing by the window count produces exactly the
driver `M.case3ThreeDriver s θ r`; no vertexwise statement is made or used. -/
theorem sum_polyK_three_ballF_le_card_mul_case3ThreeDriver (r : ℝ) (hr : 0 < r) {θ : ℝ}
    (s : ℝ → Finset M.V)
    (hfar : ∀ y ∈ E1Sign.ballF M r, y ∉ s r → r ^ θ ≤ M.S.dist 0 y)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) :
    ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y ≤
      ((M.ball r).ncard : ℝ) * M.case3ThreeDriver s θ r := by
  have hbase := M.sum_polyK_three_ballF_le_near_far r (r ^ θ) (s r) hfar hTri
  have hne : ((M.ball r).ncard : ℝ) ≠ 0 := by
    have hpos := M.ball_ncard_pos r hr.le
    exact_mod_cast ne_of_gt hpos
  have hexp : ((M.ball r).ncard : ℝ) * M.case3ThreeDriver s θ r
      = ((M.ball r).ncard : ℝ) * (M.nablaTail (r ^ θ)).toReal +
        ((s r).card : ℝ) * M.triSelf := by
    simp only [case3ThreeDriver]
    have h1 : ((M.ball r).ncard : ℝ) *
        ((((s r).card : ℝ) / ((M.ball r).ncard : ℝ)) * M.triSelf)
        = ((s r).card : ℝ) * M.triSelf := by
      rw [← mul_assoc, mul_div_cancel₀ _ hne]
    rw [mul_add, h1]
  rw [hexp]
  exact hbase

/-! ## 2. Window summation when only the sum of the ℓ = 3 entries is controlled -/

/-- **The two-term window summation of Lemma I.4.17 with a split ℓ = 3 driver.**

Per window vertex, Lemma I.4.17 at `p = 3`, `q = 0` gives
`F y ≤ C_3 T^3(0,y) χ^4 + C_4 T^4(0,y) χ^3`.  If only the *summed* ℓ = 3 entries are
controlled (`hT3`) while the ℓ = 4 entries are controlled vertexwise (`hT4`), the window sum is
`|s| (C_3 drv3 + C_4 drv4) χ^4`.  This is the exact place where the vertexwise ℓ = 3 input of
`SecondMomentCase3.sum_perVertex_le` is replaced by a summed one. -/
theorem sum_perVertex_le_split {ι : Type*} (s : Finset ι) (F T3 T4 : ι → ℝ)
    {χ drv3 drv4 C3 C4 : ℝ}
    (hF : ∀ y ∈ s, F y ≤ C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3)
    (hT3 : ∑ y ∈ s, T3 y ≤ (s.card : ℝ) * drv3)
    (hT4 : ∀ y ∈ s, T4 y ≤ drv4 * χ)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hχ : 0 ≤ χ) :
    ∑ y ∈ s, F y ≤ (s.card : ℝ) * (C3 * drv3 + C4 * drv4) * χ ^ 4 := by
  have hχ3 : (0 : ℝ) ≤ χ ^ 3 := pow_nonneg hχ 3
  have hχ4 : (0 : ℝ) ≤ χ ^ 4 := pow_nonneg hχ 4
  have e3 : ∑ y ∈ s, C3 * T3 y * χ ^ 4 = C3 * (∑ y ∈ s, T3 y) * χ ^ 4 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have e4 : ∑ y ∈ s, C4 * T4 y * χ ^ 3 = C4 * (∑ y ∈ s, T4 y) * χ ^ 3 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hsum4 : ∑ y ∈ s, T4 y ≤ (s.card : ℝ) * (drv4 * χ) := by
    calc ∑ y ∈ s, T4 y ≤ ∑ _y ∈ s, drv4 * χ := Finset.sum_le_sum hT4
      _ = (s.card : ℝ) * (drv4 * χ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have step3 : C3 * (∑ y ∈ s, T3 y) * χ ^ 4 ≤ C3 * ((s.card : ℝ) * drv3) * χ ^ 4 := by
    have h1 : C3 * (∑ y ∈ s, T3 y) ≤ C3 * ((s.card : ℝ) * drv3) :=
      mul_le_mul_of_nonneg_left hT3 hC3
    exact mul_le_mul_of_nonneg_right h1 hχ4
  have step4 : C4 * (∑ y ∈ s, T4 y) * χ ^ 3 ≤ C4 * ((s.card : ℝ) * (drv4 * χ)) * χ ^ 3 := by
    have h1 : C4 * (∑ y ∈ s, T4 y) ≤ C4 * ((s.card : ℝ) * (drv4 * χ)) :=
      mul_le_mul_of_nonneg_left hsum4 hC4
    exact mul_le_mul_of_nonneg_right h1 hχ3
  calc ∑ y ∈ s, F y
      ≤ ∑ y ∈ s, (C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3) := Finset.sum_le_sum hF
    _ = C3 * (∑ y ∈ s, T3 y) * χ ^ 4 + C4 * (∑ y ∈ s, T4 y) * χ ^ 3 := by
        rw [Finset.sum_add_distrib, e3, e4]
    _ ≤ C3 * ((s.card : ℝ) * drv3) * χ ^ 4 + C4 * ((s.card : ℝ) * (drv4 * χ)) * χ ^ 3 :=
        add_le_add step3 step4
    _ = (s.card : ℝ) * (C3 * drv3 + C4 * drv4) * χ ^ 4 := by ring

/-! ## 3. The corrected Case-3 numerator -/

/-- **Case 3: the numerator estimate from a summed ℓ = 3 input and a vertexwise ℓ = 4 input.**

Same conclusion as `M.connCubeMass_toReal_le_of_perVertex_gap`, with
`hT3 : ∀ y, T^3(0,y) ≤ Cp drv` replaced by
`hT3sum : Σ_{y ∈ B_r} T^3(0,y) ≤ |B_r| Bthree r`.  The `|B_r|` produced by the window sum still
cancels the `|B_r|` of the (I.4.16) denominator, now once per driver. -/
theorem connCubeMass_toReal_le_of_splitGap {C3 C4 Cp c : ℝ} {Bthree : ℝ → ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) {F : ℝ → M.V → ℝ}
    (hF : ∀ r : ℝ, 1 ≤ r → (M.connCubeMass r).toReal = ∑ y ∈ E1Sign.ballF M r, F r y)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      F r y ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hT3sum : ∀ r : ℝ, 1 ≤ r → ∑ y ∈ E1Sign.ballF M r,
      I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ ((E1Sign.ballF M r).card : ℝ) * Bthree r)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤
        Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      (C3 * Bthree r + C4 * Cp * M.case3Driver c r) * ((M.ball r).ncard : ℝ)
        * (M.cutMassAt r 0).toReal ^ 4 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hχ : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
  rw [hF r hr]
  have hmain := sum_perVertex_le_split (s := E1Sign.ballF M r) (F := F r)
    (T3 := fun y => I418C.polyK (M.cutTwoPoint r) 3 0 y)
    (T4 := fun y => I418C.polyK (M.cutTwoPoint r) 4 0 y)
    (χ := (M.cutMassAt r 0).toReal) (drv3 := Bthree r)
    (drv4 := Cp * M.case3Driver c r) (C3 := C3) (C4 := C4)
    (hgap r hr) (hT3sum r hr) (fun y _ => hpoly4 r hr y) hC3 hC4 hχ
  calc ∑ y ∈ E1Sign.ballF M r, F r y
      ≤ ((E1Sign.ballF M r).card : ℝ) * (C3 * Bthree r + C4 * (Cp * M.case3Driver c r))
          * (M.cutMassAt r 0).toReal ^ 4 := hmain
    _ = (C3 * Bthree r + C4 * Cp * M.case3Driver c r) * ((M.ball r).ncard : ℝ)
          * (M.cutMassAt r 0).toReal ^ 4 := by
        rw [E1Sign.card_ballF M r]
        ring

/-! ## 4. Near sets at scale `r ^ θ`, and the derived summed ℓ = 3 input -/

/-- **Near sets at scale `r ^ θ`.**  From the landed `I418C.NearBall.exists_near_ball`: outside a
finite set `s r`, every vertex is at distance `≥ r ^ θ` from the origin, and `|s r|` is at most
`K (r ^ θ)^d = K r^{θ d}`.  The cardinality rate is what makes the near contribution
`(|s r| / |B_r|) ∇_{β_c}` logarithmically integrable, not merely vanishing. -/
theorem exists_nearSets_dist {θ : ℝ} (hθ0 : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧ ∃ s : ℝ → Finset M.V,
      (∀ r : ℝ, 1 ≤ r → ∀ y : M.V, y ∉ s r → r ^ θ ≤ M.S.dist 0 y) ∧
      (∀ r : ℝ, 1 ≤ r → ((s r).card : ℝ) ≤ K * r ^ (θ * (M.d : ℝ))) := by
  classical
  obtain ⟨K, hK, hball⟩ := I418C.NearBall.exists_near_ball M
  have hpow : ∀ r : ℝ, 1 ≤ r → 1 ≤ r ^ θ := fun r hr => Real.one_le_rpow hr hθ0.le
  choose s hs using fun r : ℝ => hball (max (r ^ θ) 1) (le_max_right (r ^ θ) (1 : ℝ))
  refine ⟨K, hK, s, ?_, ?_⟩
  · intro r hr y hy
    have h1 := hpow r hr
    have h := (hs r).1 y hy
    rwa [max_eq_left h1] at h
  · intro r hr
    have h1 := hpow r hr
    have h2 : r ^ (θ * (M.d : ℝ)) = (r ^ θ) ^ (M.d : ℝ) :=
      Real.rpow_mul (le_trans zero_le_one hr) θ (M.d : ℝ)
    calc ((s r).card : ℝ) ≤ K * (max (r ^ θ) 1) ^ (M.d : ℝ) := (hs r).2
      _ = K * (r ^ θ) ^ (M.d : ℝ) := by rw [max_eq_left h1]
      _ = K * r ^ (θ * (M.d : ℝ)) := by rw [← h2]

/-! ## 5. The `E_{2,r}` estimate with the split driver -/

/-- **The real-algebra step of (I.4.16) with a split driver.**

With the numerator bound `C ≤ (drv3 + drv4) |B_r| χ^4` and the moment gap `c_3 χ^3 ≤ E|K|^2`,
the Case-3 error is `C / (|B_r| χ E|K|^2) ≤ (drv3 + drv4)/c_3`.  For a single driver this is
`SecondMomentCase3.ratio_le_of_moment_gap`. -/
theorem ratio_le_of_moment_gap_split {C b A1 A2 χ drv3 drv4 c3 : ℝ}
    (hb : 0 < b) (hA1 : 0 < A1) (hA2 : 0 < A2) (hχ : 0 < χ)
    (hA1χ : A1 = χ) (hc3 : 0 < c3)
    (hgm : c3 * χ ^ 3 ≤ A2) (hdrv : 0 ≤ drv3 + drv4)
    (hC : C ≤ (drv3 + drv4) * b * χ ^ 4) :
    C / (b * A1 * A2) ≤ (drv3 + drv4) / c3 := by
  have hden : (0 : ℝ) < b * A1 * A2 := by positivity
  rw [div_le_iff₀ hden]
  have hfac : (0 : ℝ) ≤ b * χ * (drv3 + drv4) := by
    have := hdrv; positivity
  have hχ3 : χ ^ 3 ≤ A2 / c3 := by
    rw [le_div_iff₀ hc3]; linarith
  have hmul := mul_le_mul_of_nonneg_left hχ3 hfac
  have hkey : (drv3 + drv4) * b * χ ^ 4 ≤ ((drv3 + drv4) / c3) * (b * A1 * A2) := by
    rw [hA1χ]
    calc (drv3 + drv4) * b * χ ^ 4 = b * χ * (drv3 + drv4) * χ ^ 3 := by ring
      _ ≤ b * χ * (drv3 + drv4) * (A2 / c3) := hmul
      _ = ((drv3 + drv4) / c3) * (b * χ * A2) := by field_simp
  exact hC.trans hkey

/-- **Case 3: `E_{2,r} ≤ (C_3 · ℓ=3 driver + C_4 · ℓ≥4 driver)/c_3`.**  The split analogue of
`M.p2ExclError_le_case3Driver`. -/
theorem p2ExclError_le_of_splitGap {C3 C4 Cp c r₀ : ℝ} {Bthree : ℝ → ℝ}
    (_hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hCp : 0 ≤ Cp) {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      (C3 * Bthree r + C4 * Cp * M.case3Driver c r) * ((M.ball r).ncard : ℝ)
        * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hB3 : ∀ᶠ r : ℝ in atTop, 0 ≤ C3 * Bthree r) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r ≤
      (C3 * Bthree r + C4 * Cp * M.case3Driver c r) / c3 := by
  filter_upwards [hnum, hgm, hB3, eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)]
    with r hn hg hb3 hr hr1
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have h2r := h2 r hr
  have h1r : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2r
  have hχeq : (M.cutMoment 1 r).toReal = (M.cutMassAt r 0).toReal := by
    rw [M.cutMassAt_zero_eq_cutMoment r]
  have hχ : (0 : ℝ) < (M.cutMassAt r 0).toReal := by
    have h := M.one_le_cutMoment_one_toReal r h1r
    rw [hχeq] at h
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have h := M.one_le_cutMoment_two_toReal r h2r
    linarith
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr0.le
  have hdrv : (0 : ℝ) ≤ C3 * Bthree r + C4 * Cp * M.case3Driver c r := by
    have h4 : 0 ≤ C4 * Cp * M.case3Driver c r := by
      have := M.case3Driver_nonneg_of_one_le (c := c) hr1
      positivity
    linarith
  refine (M.p2ExclError_le_connCubeMass_div r hr0.le h2r (hc r hr1)).trans ?_
  have hA1 : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    rw [hχeq]; exact hχ
  exact ratio_le_of_moment_gap_split (C := (M.connCubeMass r).toReal)
    (b := ((M.ball r).ncard : ℝ)) (A1 := (M.cutMoment 1 r).toReal)
    (A2 := (M.cutMoment 2 r).toReal) (χ := (M.cutMassAt r 0).toReal)
    (drv3 := C3 * Bthree r) (drv4 := C4 * Cp * M.case3Driver c r) (c3 := c3)
    hb hA1 hA2 hχ hχeq hc3 hg hdrv hn

/-! ## 6. The driver is nonnegative, vanishes, and is polynomially small near its first term -/

/-- The ℓ = 3 driver is nonnegative on the Case-3 range `r ≥ 1`. -/
theorem case3ThreeDriver_nonneg_of_one_le (s : ℝ → Finset M.V) {θ r : ℝ} (_hr : 1 ≤ r) :
    0 ≤ M.case3ThreeDriver s θ r := by
  refine M.case3ThreeDriver_nonneg (θ := θ) (r := r) ?_ ?_
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · unfold triSelf triPoint
    exact ENNReal.toReal_nonneg

/-- **Polynomial decay of the near-set cardinality ratio.**  With near sets of radius `r ^ θ`
supplied at rate `|s r| ≤ K r^{θ d}` and the landed lattice-ball lower bound
`|B_r| ≥ (r/2)^d` (`BallAverage.ball_ncard_ge`), the ratio decays like
`r^{-(1-θ)d}`.  The `d ≥ 1` of `SourceModelData.hd` is what makes the exponent strictly
negative. -/
theorem eventually_card_div_ball_le_rpow {θ K : ℝ} {s : ℝ → Finset M.V}
    (hcard : ∀ r : ℝ, 1 ≤ r → ((s r).card : ℝ) ≤ K * r ^ (θ * (M.d : ℝ)))
    (hK : 0 ≤ K) :
    ∀ᶠ r : ℝ in atTop, ((s r).card : ℝ) / ((M.ball r).ncard : ℝ)
      ≤ K * 2 ^ M.d * r ^ (-((1 - θ) * (M.d : ℝ))) := by
  obtain ⟨C, hC⟩ := BallAverage.exists_cube_bound M
  have hC0 : 0 ≤ C := BallAverage.cube_bound_nonneg M hC
  have h2d : (0 : ℝ) < (2 : ℝ) ^ M.d := by positivity
  filter_upwards [eventually_ge_atTop (max 1 (2 * C + 1)), eventually_gt_atTop (0 : ℝ)]
    with r hr hr0
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr
  have hr2C : 2 * C < r := by
    have := le_max_right (1 : ℝ) (2 * C + 1); linarith
  have hrC : C < r := by linarith
  -- the landed lattice-ball lower bound at the halved radius
  have hge : (r - C) ^ M.d ≤ ((M.ball r).ncard : ℝ) :=
    BallAverage.ball_ncard_ge M hC hC0 hrC
  have hhalf : r / 2 ≤ r - C := by linarith
  have hhalf0 : (0 : ℝ) ≤ r / 2 := by linarith
  have hge' : (r / 2) ^ M.d ≤ ((M.ball r).ncard : ℝ) :=
    le_trans (pow_le_pow_left₀ hhalf0 hhalf M.d) hge
  have hnpos : (0 : ℝ) < ((M.ball r).ncard : ℝ) :=
    lt_of_lt_of_le (by positivity) hge'
  -- `r ^ d ≤ 2 ^ d |B_r|`
  have hrd : r ^ (M.d : ℝ) ≤ (2 : ℝ) ^ M.d * ((M.ball r).ncard : ℝ) := by
    have hsplit : r ^ M.d = (2 : ℝ) ^ M.d * (r / 2) ^ M.d := by
      rw [← mul_pow]
      congr 1
      field_simp
    have hnat : r ^ M.d ≤ (2 : ℝ) ^ M.d * ((M.ball r).ncard : ℝ) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hge' h2d.le
    simpa only [Real.rpow_natCast] using hnat
  have hexp : r ^ (θ * (M.d : ℝ)) = r ^ (-((1 - θ) * (M.d : ℝ))) * r ^ (M.d : ℝ) := by
    nth_rewrite 1 [show θ * (M.d : ℝ) = -((1 - θ) * (M.d : ℝ)) + (M.d : ℝ) from by ring]
    rw [Real.rpow_add hr0]
  rw [div_le_iff₀ hnpos]
  calc ((s r).card : ℝ) ≤ K * r ^ (θ * (M.d : ℝ)) := hcard r hr1
    _ = K * (r ^ (-((1 - θ) * (M.d : ℝ))) * r ^ (M.d : ℝ)) := by rw [hexp]
    _ = (K * r ^ (-((1 - θ) * (M.d : ℝ)))) * r ^ (M.d : ℝ) := by ring
    _ ≤ (K * r ^ (-((1 - θ) * (M.d : ℝ)))) *
          ((2 : ℝ) ^ M.d * ((M.ball r).ncard : ℝ)) := by
        refine mul_le_mul_of_nonneg_left hrd ?_
        exact mul_nonneg hK (Real.rpow_nonneg hr0.le _)
    _ = K * 2 ^ M.d * r ^ (-((1 - θ) * (M.d : ℝ))) * ((M.ball r).ncard : ℝ) := by ring

/-- The first summand of the ℓ = 3 driver vanishes along `r ^ θ` when the open-triangle tail
does (Lemma I.4.18's far-sum conclusion at the rescaled radius). -/
theorem tendsto_nablaTail_comp_rpow {θ : ℝ} (hθ0 : 0 < θ)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.nablaTail (r ^ θ)).toReal) atTop (𝓝 0) :=
  hTail.comp (tendsto_rpow_atTop hθ0)

/-- **The ℓ = 3 Case-3 driver vanishes.**  This is what replaces the refuted vertexwise
`sup_y T^3_{β_c,r}(0,y) ≤ Cp (∇_{r^c} + r^{-c}) → 0`: the *summed* polygon is small with the
window-averaged driver, even though no single entry is. -/
theorem tendsto_case3ThreeDriver {θ K : ℝ} {s : ℝ → Finset M.V}
    (hK : 0 ≤ K) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcard : ∀ r : ℝ, 1 ≤ r → ((s r).card : ℝ) ≤ K * r ^ (θ * (M.d : ℝ)))
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => M.case3ThreeDriver s θ r) atTop (𝓝 0) := by
  have he : (0 : ℝ) < (1 - θ) * (M.d : ℝ) := by
    have hd : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
    have : (0 : ℝ) < 1 - θ := by linarith
    positivity
  have hpow : Tendsto (fun r : ℝ => r ^ (-((1 - θ) * (M.d : ℝ)))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop he
  have hratio : Tendsto (fun r : ℝ => ((s r).card : ℝ) / ((M.ball r).ncard : ℝ))
      atTop (𝓝 0) := by
    have hle := M.eventually_card_div_ball_le_rpow (θ := θ) (K := K) hcard hK
    refine squeeze_zero' ?_ hle ?_
    · filter_upwards with r
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · have h := hpow.const_mul (K * (2 : ℝ) ^ M.d)
      simpa [mul_assoc] using h
  have hsec : Tendsto
      (fun r : ℝ => (((s r).card : ℝ) / ((M.ball r).ncard : ℝ)) * M.triSelf)
      atTop (𝓝 (0 * M.triSelf)) := hratio.mul_const M.triSelf
  have h1 := M.tendsto_nablaTail_comp_rpow hθ0 hTail
  simp only [case3ThreeDriver]
  simpa using h1.add hsec

/-! ## 7. The Case-3 error estimate with the ℓ = 3 slot derived -/

/-- **Case 3: the numerator estimate with a given near family.**

The ℓ = 3 slot is supplied by `sum_polyK_three_ballF_le_card_mul_case3ThreeDriver` from the
triangle condition and the far property of the near family `s`; no vertexwise ℓ = 3 bound is
assumed.  This is the version of `M.connCubeMass_le_of_windowGap` with `hT3` replaced by a
*derived* hypothesis. -/
theorem connCubeMass_toReal_le_of_nearSets {C3 C4 Cp c θ : ℝ} {s : ℝ → Finset M.V}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hfar : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V, y ∉ s r → r ^ θ ≤ M.S.dist 0 y)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      (C3 * M.case3ThreeDriver s θ r + C4 * Cp * M.case3Driver c r)
        * ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 4 := by
  refine M.connCubeMass_toReal_le_of_splitGap (C3 := C3) (C4 := C4) (Cp := Cp) (c := c)
    (Bthree := M.case3ThreeDriver s θ) hC3 hC4
    (F := fun r y => (M.connCubeVertexMass r y).toReal)
    (fun r hr => M.connCubeMass_toReal_eq_sum_vertex r (hc r hr)) hgap ?_ hpoly4
  intro r hr
  rw [E1Sign.card_ballF M r]
  exact M.sum_polyK_three_ballF_le_card_mul_case3ThreeDriver r
    (lt_of_lt_of_le one_pos hr) s (fun y _ hy => hfar r hr y hy) hTri

/-- **Case 3: the numerator estimate, existence form.**  Near sets are produced by
`exists_nearSets_dist`. -/
theorem connCubeMass_le_of_source_threeDriver {C3 C4 Cp c θ : ℝ} (hθ0 : 0 < θ)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :
    ∃ s : ℝ → Finset M.V, (∀ r : ℝ, 1 ≤ r → ∀ y : M.V, y ∉ s r → r ^ θ ≤ M.S.dist 0 y) ∧
      ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
        (C3 * M.case3ThreeDriver s θ r + C4 * Cp * M.case3Driver c r)
          * ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 4 := by
  obtain ⟨K, hK, s, hfar, hcard⟩ := M.exists_nearSets_dist hθ0
  exact ⟨s, hfar, M.connCubeMass_toReal_le_of_nearSets (C3 := C3) (C4 := C4) (Cp := Cp)
    (c := c) hC3 hC4 hc hfar hTri hgap hpoly4⟩

/-- **Case 3: `E_{2,r}` bounded by the split driver**, with the near family given. -/
theorem p2ExclError_le_of_nearSets {C3 C4 Cp c θ r₀ : ℝ} {s : ℝ → Finset M.V}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hCp : 0 ≤ Cp) {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hfar : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V, y ∉ s r → r ^ θ ≤ M.S.dist 0 y)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r ≤
      (C3 * M.case3ThreeDriver s θ r + C4 * Cp * M.case3Driver c r) / c3 := by
  refine M.p2ExclError_le_of_splitGap (C3 := C3) (C4 := C4) (Cp := Cp) (c := c)
    (r₀ := r₀) (Bthree := M.case3ThreeDriver s θ) hC3 hC4 hCp hc3 h2 hc ?_ hgm ?_
  · exact M.connCubeMass_toReal_le_of_nearSets (C3 := C3) (C4 := C4) (Cp := Cp) (c := c)
      hC3 hC4 hc hfar hTri hgap hpoly4
  · exact eventually_ge_atTop (1 : ℝ) |>.mono fun r hr =>
      mul_nonneg hC3 (M.case3ThreeDriver_nonneg_of_one_le s hr)

/-- **Case 3: `E_{2,r}` bounded by the split driver**, existence form. -/
theorem p2ExclError_le_of_source_split {C3 C4 Cp c θ r₀ : ℝ} (hθ0 : 0 < θ)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hCp : 0 ≤ Cp) {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ s : ℝ → Finset M.V, (∀ r : ℝ, 1 ≤ r → ∀ y : M.V, y ∉ s r → r ^ θ ≤ M.S.dist 0 y) ∧
      ∀ᶠ r : ℝ in atTop, M.p2ExclError r ≤
        (C3 * M.case3ThreeDriver s θ r + C4 * Cp * M.case3Driver c r) / c3 := by
  obtain ⟨K, hK, s, hfar, hcard⟩ := M.exists_nearSets_dist hθ0
  exact ⟨s, hfar, M.p2ExclError_le_of_nearSets (C3 := C3) (C4 := C4) (Cp := Cp) (c := c)
    (r₀ := r₀) hC3 hC4 hCp hc3 h2 hc hfar hTri hgap hpoly4 hgm⟩

/-! ## 8. Logarithmic integrability of the derived ℓ = 3 driver -/

/-- **The ℓ = 3 driver inherits logarithmic integrability from the open-triangle tail.**

The driver is `(∇_{β_c}(0, r^θ)).toReal + (|s r| / |B_r|) ∇_{β_c}`.  The first summand is
log-integrable by Lemma I.4.19 (`Analysis.logarithmicallyIntegrable_comp_rpow_const_mul`); the
second is dominated by `K 2^d ∇_{β_c} r^{-(1-θ)d}`, which is a log-integrable error function
because `(1 - θ) d ≥ (1 - θ) > 0` (`SourceModelData.hd`).  So the repaired Case-3 driver is not
merely vanishing: it is an admissible Case-3 driver in exactly the sense the source requires of
`∇_{r^c} + r^{-c}`.

Measurability of the driver in the radius is carried explicitly, exactly as for `𝓔_{1,r}` and
`p2ExclError` elsewhere in the production tree. -/
theorem logarithmicallyIntegrable_case3ThreeDriver {θ K : ℝ} {s : ℝ → Finset M.V}
    (hmeas : Measurable (fun r : ℝ => M.case3ThreeDriver s θ r))
    (hK : 0 ≤ K) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcard : ∀ r : ℝ, 1 ≤ r → ((s r).card : ℝ) ≤ K * r ^ (θ * (M.d : ℝ)))
    (hTail : Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal)) :
    Analysis.LogarithmicallyIntegrable (fun r : ℝ => M.case3ThreeDriver s θ r) := by
  have hd : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
  have he : (0 : ℝ) < (1 - θ) * (M.d : ℝ) := by
    have : (0 : ℝ) < 1 - θ := by linarith
    positivity
  -- first summand: Lemma I.4.19
  have ha : Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail (r ^ θ)).toReal) := by
    refine ⟨?_, ?_⟩
    · have h := Analysis.logarithmicallyIntegrable_comp_rpow_const_mul
        (fun r : ℝ => (M.nablaTail r).toReal) hTail.1 (c := θ) (C := 1) hθ0 one_pos
      simpa using h
    · have h := hTail.2.comp (tendsto_rpow_atTop hθ0)
      exact h
  -- second summand: polynomial decay
  have hb : Analysis.IsLogErrorFunction
      (fun r : ℝ => K * (2 : ℝ) ^ M.d * |M.triSelf| * r ^ (-((1 - θ) * (M.d : ℝ)))) :=
    Analysis.isLogErrorFunction_const_rpow_neg (c := K * (2 : ℝ) ^ M.d * |M.triSelf|) he one_pos
  have hH := Analysis.isLogErrorFunction_add ha hb
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le hmeas hH.1 ?_
  have hT := M.eventually_card_div_ball_le_rpow (θ := θ) (K := K) hcard hK
  filter_upwards [hT, eventually_ge_atTop (1 : ℝ)] with r hTle hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hnn : (0 : ℝ) ≤ r ^ (-((1 - θ) * (M.d : ℝ))) := Real.rpow_nonneg hr0.le _
  have hTnn : (0 : ℝ) ≤ ((s r).card : ℝ) / ((M.ball r).ncard : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsec : (((s r).card : ℝ) / ((M.ball r).ncard : ℝ)) * M.triSelf
      ≤ K * 2 ^ M.d * |M.triSelf| * r ^ (-((1 - θ) * (M.d : ℝ))) := by
    rcases le_or_gt 0 M.triSelf with htri | htri
    · rw [abs_of_nonneg htri]
      calc (((s r).card : ℝ) / ((M.ball r).ncard : ℝ)) * M.triSelf
          ≤ (K * 2 ^ M.d * r ^ (-((1 - θ) * (M.d : ℝ)))) * M.triSelf :=
            mul_le_mul_of_nonneg_right hTle htri
        _ = K * 2 ^ M.d * M.triSelf * r ^ (-((1 - θ) * (M.d : ℝ))) := by ring
    · have h1 : (((s r).card : ℝ) / ((M.ball r).ncard : ℝ)) * M.triSelf ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hTnn htri.le
      have h2 : (0 : ℝ) ≤ K * 2 ^ M.d * |M.triSelf| * r ^ (-((1 - θ) * (M.d : ℝ))) :=
        mul_nonneg (mul_nonneg (mul_nonneg hK (by positivity)) (abs_nonneg _)) hnn
      linarith
  have hle : M.case3ThreeDriver s θ r ≤
      (M.nablaTail (r ^ θ)).toReal +
        K * 2 ^ M.d * |M.triSelf| * r ^ (-((1 - θ) * (M.d : ℝ))) := by
    simp only [case3ThreeDriver]
    linarith
  have hHnn : (0 : ℝ) ≤ (M.nablaTail (r ^ θ)).toReal +
      K * 2 ^ M.d * |M.triSelf| * r ^ (-((1 - θ) * (M.d : ℝ))) :=
    add_nonneg (M.nablaTail_toReal_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hK (by positivity)) (abs_nonneg _)) hnn)
  rw [abs_of_nonneg (M.case3ThreeDriver_nonneg_of_one_le s hr), abs_of_nonneg hHnn]
  exact hle

/-! ## 9. Case 3: logarithmic integrability of `E_{2,r}` with the ℓ = 3 slot derived -/

/-- **Proposition I.4.15, Case 3: `E_{2,r}` is logarithmically integrable.**

This closes the Case-3 *analytic input* of the second-moment argument at the level of `E_{2,r}`:
the conclusion `Analysis.LogarithmicallyIntegrable M.p2ExclError` is exactly what
`M.tendsto_div_two` consumes, together with the moment gap, to produce
`E_{β_c,r}|K|^2 ~ A r^{3α}`.

Nothing vertexwise is assumed about the ℓ = 3 polygon.  The ℓ = 3 slot is derived
(`connCubeMass_toReal_le_of_nearSets`) and the resulting driver is a genuine Case-3 driver:
vanishing (`tendsto_case3ThreeDriver`) and logarithmically integrable
(`logarithmicallyIntegrable_case3ThreeDriver`).  The remaining inputs are the `p = 3`, `q = 0`
moment gap (`hgap`), the landed ℓ = 4 polygon bound (`hpoly4`), the triangle condition, the
moment gap, and the two measurability hypotheses the production tree carries for `𝓔_{1,r}` and
`E_{2,r}` as well. -/
theorem logIntegrable_p2ExclError_of_source_split {C3 C4 Cp c θ K r₀ : ℝ}
    {s : ℝ → Finset M.V}
    (hmeasS : Measurable (fun r : ℝ => M.case3ThreeDriver s θ r))
    (hmeasE : Measurable M.p2ExclError)
    (hK : 0 ≤ K) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hfar : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V, y ∉ s r → r ^ θ ≤ M.S.dist 0 y)
    (hcard : ∀ r : ℝ, 1 ≤ r → ((s r).card : ℝ) ≤ K * r ^ (θ * (M.d : ℝ)))
    (hTail : Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal))
    (hcpos : 0 < c)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hCp : 0 ≤ Cp) {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  have hlog3 := M.logarithmicallyIntegrable_case3ThreeDriver hmeasS hK hθ0 hθ1 hcard hTail
  have htend3 := M.tendsto_case3ThreeDriver (θ := θ) (K := K) hK hθ0 hθ1 hcard hTail.2
  have hlog4 := M.isLogErrorFunction_case3Driver hTail hcpos
  have hsum : Analysis.IsLogErrorFunction
      (fun r : ℝ => (C3 / c3) * M.case3ThreeDriver s θ r
        + (C4 * Cp / c3) * M.case3Driver c r) :=
    Analysis.isLogErrorFunction_add
      (Analysis.isLogErrorFunction_const_mul ⟨hlog3, htend3⟩ (C3 / c3))
      (Analysis.isLogErrorFunction_const_mul hlog4 (C4 * Cp / c3))
  have hEq : (fun r : ℝ => (C3 * M.case3ThreeDriver s θ r + C4 * Cp * M.case3Driver c r)
        / c3)
      = fun r : ℝ => (C3 / c3) * M.case3ThreeDriver s θ r
          + (C4 * Cp / c3) * M.case3Driver c r := by
    funext r
    ring
  have hmaj : Analysis.LogarithmicallyIntegrable
      (fun r : ℝ => (C3 * M.case3ThreeDriver s θ r + C4 * Cp * M.case3Driver c r) / c3) := by
    rw [hEq]
    exact hsum.1
  have hbnd := M.p2ExclError_le_of_nearSets (C3 := C3) (C4 := C4) (Cp := Cp) (c := c)
    (r₀ := r₀) hC3 hC4 hCp hc3 h2 hc hfar hTri hgap hpoly4 hgm
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le hmeasE hmaj ?_
  filter_upwards [hbnd, eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)] with r hb hr hr1
  have hE : (0 : ℝ) ≤ M.p2ExclError r :=
    M.p2ExclError_nonneg r (le_trans zero_le_one hr1) (h2 r hr)
  have hd1 : (0 : ℝ) ≤ C3 * M.case3ThreeDriver s θ r :=
    mul_nonneg hC3 (M.case3ThreeDriver_nonneg_of_one_le s hr1)
  have hd2 : (0 : ℝ) ≤ C4 * Cp * M.case3Driver c r :=
    mul_nonneg (mul_nonneg hC4 hCp) (M.case3Driver_nonneg_of_one_le hr1)
  have hM : (0 : ℝ) ≤
      (C3 * M.case3ThreeDriver s θ r + C4 * Cp * M.case3Driver c r) / c3 :=
    div_nonneg (by linarith) hc3.le
  rw [abs_of_nonneg hE, abs_of_nonneg hM]
  exact hb

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

end
