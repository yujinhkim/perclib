/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Finiteness and majorants for the `p = 2` excluded terms of Lemma I.4.1

Swarm `smwv94uce`, member `m2`, direction `d4`.  Nothing here touches the production tree.

## What is proved

`Defs.lean` names the two excluded expectations of the `p = 2` cut-moment derivative on the
actual translated source cut-off law `M.cutLaw r` of the infinite lattice:

* `M.exclMassQuad r = E_{β_c,r}[|K| ∑_{y∈B_r} 1(y∉K)|K_y|^2]`  (the `ℓ = 0` term),
* `M.exclMassSqLin r = E_{β_c,r}[|K|^2 ∑_{y∈B_r} 1(y∉K)|K_y|]`  (the `ℓ = 1` term),

and `M.p2RHS r = M.exclMassQuad r + 2 * M.exclMassSqLin r` is the `p = 2` RHS of (I.4.1).

This file supplies the analytic half of the `p = 2` statement — the half that does not
depend on the pivotal (Russo/mass-transport) identity:

* `lintegral_clusterVol_pow_vertex` — translation invariance of the cut-off law at a vertex:
  the `p`-th cluster moment at `y` equals `M.cutMoment p r` at the origin.  This is a true
  infinite-volume statement, obtained from `cutLaw_map_shiftConfig` and
  `clusterVol_shiftConfig`, not a finite-window surrogate.
* `lintegral_ballF_clusterVol_pow` — consequently
  `E_{β_c,r}[∑_{y∈B_r} |K_y|^p] = |B_r| · M.cutMoment p r`.
* `p2QuadMass_le`, `p2PairMass_le` — the explicit majorants
  `M.exclMassQuad r ≤ |B_r| (M₂ + M₄)` and `M.exclMassSqLin r ≤ |B_r| (M₂ + M₄)`,
  where `M_p = M.cutMoment p r`, from `x y ≤ x² + y²` inside the integral.
* `p2RhsMass_le` — `M.p2RHS r ≤ 3 |B_r| (M₂ + M₄)`.
* `p2RhsMass_le_first` — with the landed fourth-moment transfer
  `M₄ ≤ 15 (M₁)⁷` (`Orchestration.cutMoment_four_le`) this is `≤ 90 |B_r| (M₁)⁷`, so the
  *only* remaining input is finiteness of the first cut-off moment.
* `p2QuadMass_ne_top`, `p2PairMass_ne_top`, `p2RhsMass_ne_top` — hence both excluded terms
  of the `p = 2` RHS are finite whenever the first moment is, and
* `rhsScalarTwo_eq` — the real-valued RHS `β_c(-K'(r)) (E[ℓ=0] + 2 E[ℓ=1])` is the sum of
  its two finite parts with the source's coefficient `2` intact.
* `p2SourceSum_eq_p2RhsMass` — the litera1 `p = 2` instance of the source's displayed sum
  `∑_{ℓ=0}^{p-1} binom(p,ℓ) …` is exactly `M.exclMassQuad + 2 * M.exclMassSqLin`, i.e. the two
  terms and the coefficient `2` are the binomial's, not a reformulation.

The pivotal identity producing these two terms as the derivative of `E|K|^2` is *not*
proved here, and no attained-radius two-sided statement is made.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffFourthMoments
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffMoments
public import PercLib.CriticalLRP.Analysis.Cutoff.Translation

/-!
# Majorants and finiteness for the `p = 2` excluded terms

Translation invariance of the cut-off law at a single vertex, its consequence for the ball
sum, the `x y ≤ x² + y²` majorants, and the resulting finiteness of both `p = 2` excluded
terms from finiteness of the first cut-off moment.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

/-- `x y ≤ x ^ 2 + y ^ 2` in `ℝ≥0∞`, with no division and no finiteness hypothesis. -/
theorem ennnreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (pow_two b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_left le_rfl
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (pow_two a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_right le_rfl

namespace SourceModelData

variable (M : SourceModelData)

/-! ## Measurability of the `p = 2` integrands -/

/-- The `k`-th power weighted excluded window sum over an arbitrary finite window. -/
theorem measurable_p2WindowSum (s : Finset M.V) (k : ℕ) :
    Measurable fun ω : Config M.V =>
      ∑ y ∈ s,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ k :=
  Finset.measurable_sum s fun y _ =>
    (Measurable.ite (measurableSet_cluster_mem (0 : M.V) y).compl measurable_const
      measurable_const).mul ((measurable_clusterVol y).pow_const k)

/-- The `ℓ = 0` integrand is measurable. -/
theorem measurable_p2QuadFun (r : ℝ) :
    Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) *
      ∑ y ∈ E1Sign.ballF M r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2 :=
  (measurable_clusterVol (0 : M.V)).mul (M.measurable_p2WindowSum _ 2)

/-- The `ℓ = 1` integrand is measurable. -/
theorem measurable_p2PairFun (r : ℝ) :
    Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 2 *
      ∑ y ∈ E1Sign.ballF M r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y :=
  ((measurable_clusterVol (0 : M.V)).pow_const 2).mul
    (by simpa only [pow_one] using M.measurable_p2WindowSum (E1Sign.ballF M r) 1)

/-! ## Translation invariance of the cut-off law at one vertex -/

/-- **The `p`-th cut-off cluster moment does not depend on the vertex.**  The cut-off law is
invariant under lattice translations (`cutLaw_map_shiftConfig`) and translating a
configuration translates its cluster volumes (`clusterVol_shiftConfig`), so the `p`-th moment
at `x` is the `p`-th moment at the origin.  This is an infinite-volume identity on the actual
translated source cut-off law. -/
theorem lintegral_clusterVol_pow_vertex (r : ℝ) (x : M.V) (p : ℕ) :
    ∫⁻ ω, clusterVol ω x ^ p ∂(M.cutLaw r) = M.cutMoment p r := by
  have hlin : ∫⁻ ω, clusterVol ω x ^ p ∂((M.cutLaw r).map (shiftConfig x))
      = ∫⁻ ω, clusterVol (shiftConfig x ω) x ^ p ∂(M.cutLaw r) :=
    lintegral_map ((measurable_clusterVol x).pow_const p) (measurable_shiftConfig x)
  have key : ∫⁻ ω, clusterVol (shiftConfig x ω) x ^ p ∂(M.cutLaw r)
      = ∫⁻ ω, clusterVol ω x ^ p ∂(M.cutLaw r) := by
    rw [← hlin, M.cutLaw_map_shiftConfig r x]
  rw [cutMoment, ← key]
  refine lintegral_congr fun ω => ?_
  have hcv : clusterVol (shiftConfig x ω) x = clusterVol ω (0 : M.V) := by
    have h := M.clusterVol_shiftConfig x ω (0 : M.V)
    simpa using h
  rw [hcv]

/-- **The ball sum of the `p`-th cut-off cluster moments is `|B_r|` times the origin moment.**
Another genuine infinite-volume statement: no finite-volume approximation is involved. -/
theorem lintegral_ballF_clusterVol_pow (r : ℝ) (p : ℕ) :
    ∫⁻ ω, ∑ y ∈ E1Sign.ballF M r, clusterVol ω y ^ p ∂(M.cutLaw r)
      = ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment p r := by
  rw [lintegral_finsetSum _ (fun y _ => (measurable_clusterVol y).pow_const p)]
  rw [Finset.sum_congr rfl (fun y _ => M.lintegral_clusterVol_pow_vertex r y p),
    Finset.sum_const, E1Sign.card_ballF, nsmul_eq_mul]

/-! ## Majorants for the two excluded terms -/

/-- The indicator weight of the excluded window sum is at most one. -/
theorem exclWeight_le_one (ω : Config M.V) (y : M.V) :
    ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y ≤ 1 := by
  by_cases h : y ∈ cluster ω (0 : M.V)
  · rw [Set.indicator_of_notMem (by simpa using h)]
    exact zero_le
  · rw [Set.indicator_of_mem (by simpa using h)]

/-- **The `ℓ = 0` excluded term is dominated by `|B_r| (M₂ + M₄)`.**  Inside the integral the
bound is `|K| 1(y∉K)|K_y|² ≤ |K|² + |K_y|⁴`, summed over the ball and integrated with the
translation invariance of `lintegral_ballF_clusterVol_pow`. -/
theorem p2QuadMass_le (r : ℝ) :
    M.exclMassQuad r ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r) := by
  have hpt : ∀ ω : Config M.V, clusterVol ω (0 : M.V) *
      ∑ y ∈ E1Sign.ballF M r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2
      ≤ ∑ y ∈ E1Sign.ballF M r,
          (clusterVol ω (0 : M.V) ^ 2 + clusterVol ω y ^ 4) := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    calc clusterVol ω (0 : M.V) *
          (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
        ≤ clusterVol ω (0 : M.V) * (1 * clusterVol ω y ^ 2) := by
          gcongr
          exact M.exclWeight_le_one ω y
      _ = clusterVol ω (0 : M.V) * clusterVol ω y ^ 2 := by rw [one_mul]
      _ ≤ clusterVol ω (0 : M.V) ^ 2 + (clusterVol ω y ^ 2) ^ 2 :=
          ennnreal_mul_le_sq_add_sq _ _
      _ = clusterVol ω (0 : M.V) ^ 2 + clusterVol ω y ^ 4 := by
          rw [← pow_mul]
  calc M.exclMassQuad r
      = ∫⁻ ω, clusterVol ω (0 : M.V) *
          ∑ y ∈ E1Sign.ballF M r,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2
          ∂(M.cutLaw r) := rfl
    _ ≤ ∫⁻ ω, ∑ y ∈ E1Sign.ballF M r,
          (clusterVol ω (0 : M.V) ^ 2 + clusterVol ω y ^ 4) ∂(M.cutLaw r) :=
        lintegral_mono hpt
    _ = ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r) := by
        have hsum : ∫⁻ ω, ∑ y ∈ E1Sign.ballF M r,
              (clusterVol ω (0 : M.V) ^ 2 + clusterVol ω y ^ 4) ∂(M.cutLaw r)
            = ∑ y ∈ E1Sign.ballF M r,
              ∫⁻ ω, (clusterVol ω (0 : M.V) ^ 2 + clusterVol ω y ^ 4) ∂(M.cutLaw r) :=
          lintegral_finsetSum (E1Sign.ballF M r) (fun y _ =>
            ((measurable_clusterVol (0 : M.V)).pow_const 2).add
              ((measurable_clusterVol y).pow_const 4))
        rw [hsum]
        have hterm : ∀ y ∈ E1Sign.ballF M r,
            (∫⁻ ω, (clusterVol ω (0 : M.V) ^ 2 + clusterVol ω y ^ 4) ∂(M.cutLaw r))
              = M.cutMoment 2 r + M.cutMoment 4 r := by
          intro y _
          rw [lintegral_add_left ((measurable_clusterVol (0 : M.V)).pow_const 2),
            M.lintegral_clusterVol_pow_vertex r y 4]
          rfl
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, E1Sign.card_ballF, nsmul_eq_mul]

/-- **The `ℓ = 1` excluded term is dominated by `|B_r| (M₂ + M₄)`.**  Inside the integral the
bound is `|K|² 1(y∉K)|K_y| ≤ |K|⁴ + |K_y|²`. -/
theorem p2PairMass_le (r : ℝ) :
    M.exclMassSqLin r ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r) := by
  have hpt : ∀ ω : Config M.V, clusterVol ω (0 : M.V) ^ 2 *
      ∑ y ∈ E1Sign.ballF M r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
      ≤ ∑ y ∈ E1Sign.ballF M r,
          (clusterVol ω y ^ 2 + clusterVol ω (0 : M.V) ^ 4) := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    calc clusterVol ω (0 : M.V) ^ 2 *
          (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
        ≤ clusterVol ω (0 : M.V) ^ 2 * (1 * clusterVol ω y) := by
          gcongr
          exact M.exclWeight_le_one ω y
      _ = clusterVol ω (0 : M.V) ^ 2 * clusterVol ω y := by rw [one_mul]
      _ ≤ (clusterVol ω (0 : M.V) ^ 2) ^ 2 + clusterVol ω y ^ 2 :=
          ennnreal_mul_le_sq_add_sq _ _
      _ = clusterVol ω y ^ 2 + clusterVol ω (0 : M.V) ^ 4 := by
          rw [← pow_mul, add_comm]
  calc M.exclMassSqLin r
      = ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 *
          ∑ y ∈ E1Sign.ballF M r,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
          ∂(M.cutLaw r) := rfl
    _ ≤ ∫⁻ ω, ∑ y ∈ E1Sign.ballF M r,
          (clusterVol ω y ^ 2 + clusterVol ω (0 : M.V) ^ 4) ∂(M.cutLaw r) :=
        lintegral_mono hpt
    _ = ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r) := by
        have hsum : ∫⁻ ω, ∑ y ∈ E1Sign.ballF M r,
              (clusterVol ω y ^ 2 + clusterVol ω (0 : M.V) ^ 4) ∂(M.cutLaw r)
            = ∑ y ∈ E1Sign.ballF M r,
              ∫⁻ ω, (clusterVol ω y ^ 2 + clusterVol ω (0 : M.V) ^ 4) ∂(M.cutLaw r) :=
          lintegral_finsetSum (E1Sign.ballF M r) (fun y _ =>
            ((measurable_clusterVol y).pow_const 2).add
              ((measurable_clusterVol (0 : M.V)).pow_const 4))
        rw [hsum]
        have hterm : ∀ y ∈ E1Sign.ballF M r,
            (∫⁻ ω, (clusterVol ω y ^ 2 + clusterVol ω (0 : M.V) ^ 4) ∂(M.cutLaw r))
              = M.cutMoment 2 r + M.cutMoment 4 r := by
          intro y _
          rw [lintegral_add_left ((measurable_clusterVol y).pow_const 2),
            M.lintegral_clusterVol_pow_vertex r y 2]
          rfl
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, E1Sign.card_ballF, nsmul_eq_mul]

/-- **The `p = 2` RHS functional is dominated by `3 |B_r| (M₂ + M₄)`.** -/
theorem p2RhsMass_le (r : ℝ) :
    M.p2RHS r ≤
      3 * (((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r)) := by
  have hq := M.p2QuadMass_le r
  have hp := M.p2PairMass_le r
  calc M.p2RHS r = M.exclMassQuad r + 2 * M.exclMassSqLin r := rfl
    _ ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r)
          + 2 * (((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r)) := by
        gcongr
    _ = 3 * (((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r)) := by
        ring

/-- The second cut-off moment is at most the fourth one: every cluster contains its root. -/
theorem cutMoment_two_le_four (r : ℝ) : M.cutMoment 2 r ≤ M.cutMoment 4 r := by
  refine lintegral_mono fun ω => ?_
  calc clusterVol ω (0 : M.V) ^ 2 = clusterVol ω (0 : M.V) ^ 2 * 1 := (mul_one _).symm
    _ ≤ clusterVol ω (0 : M.V) ^ 2 * clusterVol ω (0 : M.V) ^ 2 := by
        gcongr
        exact one_le_pow₀ (E1Sign.one_le_clusterVol M ω 0)
    _ = clusterVol ω (0 : M.V) ^ 4 := by ring

/-- **The `p = 2` RHS is dominated by `6 |B_r| M₄`.** -/
theorem p2RhsMass_le_fourth (r : ℝ) :
    M.p2RHS r ≤ 6 * (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 4 r) := by
  refine le_trans (M.p2RhsMass_le r) ?_
  have h24 := M.cutMoment_two_le_four r
  calc 3 * (((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r))
      ≤ 3 * (((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 4 r + M.cutMoment 4 r)) := by
        gcongr
    _ = 6 * (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 4 r) := by ring

/-- **The `p = 2` RHS is dominated by `90 |B_r| (E|K|)⁷`**, using the landed fourth-moment
transfer `cutMoment_four_le`.  The only remaining input is finiteness of the first cut-off
moment at the same radius. -/
theorem p2RhsMass_le_first {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) :
    M.p2RHS r ≤ 90 * ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r) ^ 7 := by
  refine le_trans (M.p2RhsMass_le_fourth r) ?_
  have h4 := cutMoment_four_le M hc hρ hr
  calc 6 * (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 4 r)
      ≤ 6 * (((M.ball r).ncard : ℝ≥0∞) * (15 * (M.cutMoment 1 r) ^ 7)) := by
        gcongr
    _ = 90 * ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r) ^ 7 := by ring

/-! ## Finiteness of the two excluded terms -/

/-- **The `ℓ = 0` excluded term of the `p = 2` RHS is finite** from finiteness of the first
cut-off moment at the same radius (via the landed second and fourth moment transfers). -/
theorem p2QuadMass_ne_top {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) : M.exclMassQuad r ≠ ⊤ := by
  have h2 : M.cutMoment 2 r ≠ ⊤ := cutMoment_two_ne_top_of_one M hc hρ hr h1
  have h4 : M.cutMoment 4 r ≠ ⊤ := cutMoment_four_ne_top_of_one M hc hρ hr h1
  refine ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨h2, h4⟩))
    (M.p2QuadMass_le r)

/-- **The `ℓ = 1` excluded term of the `p = 2` RHS is finite** from finiteness of the first
cut-off moment at the same radius. -/
theorem p2PairMass_ne_top {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) : M.exclMassSqLin r ≠ ⊤ := by
  have h2 : M.cutMoment 2 r ≠ ⊤ := cutMoment_two_ne_top_of_one M hc hρ hr h1
  have h4 : M.cutMoment 4 r ≠ ⊤ := cutMoment_four_ne_top_of_one M hc hρ hr h1
  refine ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨h2, h4⟩))
    (M.p2PairMass_le r)

/-- **Both excluded terms of the `p = 2` RHS are finite, hence so is the whole RHS.** -/
theorem p2RhsMass_ne_top {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) : M.p2RHS r ≠ ⊤ :=
  ENNReal.add_ne_top.mpr
    ⟨M.p2QuadMass_ne_top hc hρ hr h1,
      ENNReal.mul_ne_top (by norm_num) (M.p2PairMass_ne_top hc hρ hr h1)⟩

/-! ## Relation to the landed `p = 1` excluded mass -/

/-- Every cluster volume is at most its square: a cluster contains its root. -/
theorem clusterVol_le_sq (ω : Config M.V) (y : M.V) :
    clusterVol ω y ≤ clusterVol ω y ^ 2 := by
  calc clusterVol ω y = clusterVol ω y ^ 1 := (pow_one _).symm
    _ ≤ clusterVol ω y ^ 2 :=
        pow_le_pow_right₀ (E1Sign.one_le_clusterVol M ω y) (by norm_num)

/-- **The landed `p = 1` excluded mass is dominated by the `ℓ = 1` term of the `p = 2`
RHS.**  Since `|K| ≤ |K|^2` pointwise, the second-moment RHS term carries the whole
first-moment excluded expectation; in particular the `p = 2` RHS contains strictly more
information than the `p = 1` one. -/
theorem exclMass_le_p2PairMass (r : ℝ) : E1Sign.exclMass M r ≤ M.exclMassSqLin r :=
  lintegral_mono fun ω => mul_le_mul' (M.clusterVol_le_sq ω 0) le_rfl

/-- The landed `p = 1` excluded mass inherits the `p = 2` majorant
`|B_r| (M₂ + M₄)`. -/
theorem exclMass_le_ball_mul_moment (r : ℝ) :
    E1Sign.exclMass M r ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 2 r + M.cutMoment 4 r) :=
  le_trans (M.exclMass_le_p2PairMass r) (M.p2PairMass_le r)

/-! ## The source's displayed sum at `p = 2` -/

/-- The `ℓ = 0` source summand is `exclMassQuad`. -/
theorem p2Term_zero (r : ℝ) : M.p2Term r 0 = M.exclMassQuad r := by
  unfold p2Term exclMassQuad exclSumQuad
  refine lintegral_congr fun ω => ?_
  simp

/-- The `ℓ = 1` source summand is `exclMassSqLin`. -/
theorem p2Term_one (r : ℝ) : M.p2Term r 1 = M.exclMassSqLin r := by
  unfold p2Term exclMassSqLin exclSumLin
  refine lintegral_congr fun ω => ?_
  simp

/-- **Fidelity to the source's displayed sum at `p = 2`.**  The `p = 2` instance of
`∑_{ℓ=0}^{p-1} binom(p,ℓ) E[|K|^{ℓ+1} ∑_{y∈B_r} 1(y∉K)|K_y|^{p-ℓ}]` is exactly the two-term
functional `exclMassQuad + 2 * exclMassSqLin`: the coefficient `2` and the powers `|K|`, `|K|²`,
`|K_y|²`, `|K_y|` are the binomial's and the source's. -/
theorem p2SourceSum_eq_p2RhsMass (r : ℝ) : M.p2SourceSum r = M.p2RHS r := by
  rw [p2SourceSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    M.p2Term_zero, M.p2Term_one, p2RHS]
  simp

/-! ## The real-valued `p = 2` RHS -/

/-- **The real-valued `p = 2` RHS is the sum of its two finite parts**, with the source's
coefficient `2` intact. -/
theorem rhsScalarTwo_eq {r : ℝ} (hq : M.exclMassQuad r ≠ ⊤) (hp : M.exclMassSqLin r ≠ ⊤) :
    M.rhsScalarTwo r = M.coeffRHS r *
      ((M.exclMassQuad r).toReal + 2 * (M.exclMassSqLin r).toReal) := by
  rw [rhsScalarTwo, p2RHS,
    ENNReal.toReal_add hq (ENNReal.mul_ne_top (by norm_num) hp), ENNReal.toReal_mul]
  norm_num

/-- **The real `p = 2` RHS is bounded by `β_c(-K'(r))` times the explicit majorant.**  This is
the form the analytic assembly of (I.4.1) needs: a finite real upper bound for the right-hand
side in terms of the first cut-off moment. -/
theorem rhsScalarTwo_le_first {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) (hcoef : 0 ≤ M.coeffRHS r) :
    M.rhsScalarTwo r ≤
      M.coeffRHS r * (90 * ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r) ^ 7).toReal := by
  have htop : 90 * ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r) ^ 7 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp))
      (ENNReal.pow_ne_top h1)
  rw [rhsScalarTwo]
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  exact ENNReal.toReal_mono htop (M.p2RhsMass_le_first hc hρ hr)

/-- The same with the moment hypothesis, no separate finiteness inputs. -/
theorem rhsScalarTwo_eq_of_moment {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) :
    M.rhsScalarTwo r = M.coeffRHS r *
      ((M.exclMassQuad r).toReal + 2 * (M.exclMassSqLin r).toReal) :=
  M.rhsScalarTwo_eq (M.p2QuadMass_ne_top hc hρ hr h1) (M.p2PairMass_ne_top hc hρ hr h1)

end SourceModelData

namespace Witness

open PercLib.CriticalLRP

/-- **`p = 2` at the explicit source witness** (`ρ v = 2 ‖v‖∞`, normalisation `c = 2`): both
excluded terms of the `p = 2` RHS are finite from the first cut-off moment alone. -/
theorem sourceModelWitness_p2RhsMass_ne_top (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) (h1 : (sourceModelWitness d hd α hα).cutMoment 1 r ≠ ⊤) :
    (sourceModelWitness d hd α hα).p2RHS r ≠ ⊤ :=
  SourceModelData.p2RhsMass_ne_top _ (by norm_num)
    (sourceModelWitness_dist_eq d hd α hα) hr h1

/-- The `p = 2` RHS majorant at the source witness. -/
theorem sourceModelWitness_p2RhsMass_le_first (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) :
    (sourceModelWitness d hd α hα).p2RHS r ≤
      90 * (((sourceModelWitness d hd α hα).ball r).ncard : ℝ≥0∞) *
        ((sourceModelWitness d hd α hα).cutMoment 1 r) ^ 7 :=
  SourceModelData.p2RhsMass_le_first _ (by norm_num) (sourceModelWitness_dist_eq d hd α hα) hr

end Witness

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms ennnreal_mul_le_sq_add_sq
#print axioms SourceModelData.measurable_p2WindowSum
#print axioms SourceModelData.lintegral_clusterVol_pow_vertex
#print axioms SourceModelData.lintegral_ballF_clusterVol_pow
#print axioms SourceModelData.p2QuadMass_le
#print axioms SourceModelData.p2PairMass_le
#print axioms SourceModelData.p2RhsMass_le
#print axioms SourceModelData.cutMoment_two_le_four
#print axioms SourceModelData.p2RhsMass_le_fourth
#print axioms SourceModelData.p2RhsMass_le_first
#print axioms SourceModelData.p2QuadMass_ne_top
#print axioms SourceModelData.p2PairMass_ne_top
#print axioms SourceModelData.p2RhsMass_ne_top
#print axioms SourceModelData.clusterVol_le_sq
#print axioms SourceModelData.exclMass_le_p2PairMass
#print axioms SourceModelData.exclMass_le_ball_mul_moment
#print axioms SourceModelData.p2SourceSum_eq_p2RhsMass
#print axioms SourceModelData.rhsScalarTwo_le_first
#print axioms SourceModelData.rhsScalarTwo_eq
#print axioms Witness.sourceModelWitness_p2RhsMass_ne_top
#print axioms Witness.sourceModelWitness_p2RhsMass_le_first

end PercLib.CriticalLRP.Orchestration
