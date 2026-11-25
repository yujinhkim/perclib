/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Row-mass finiteness at small cutoff radii for the source model

Reviewed and integrated from Ultramath `smwtqkdul`, member `m1`,
`SmallCutoff.lean`, based on revision
`9afe8a172733efb434a2944a2ed97cfca4ad9bcf`. This is a small-radius theorem,
not a large-radius finite-susceptibility result.

## What is proved

The source's cutoff law `P_{β_c, r}` of Definition I.1.5 keeps the pairs at `ρ`-distance
at most `r` with intensity `J_r(s) = K s - K r` (`s ≤ r`) and `0` otherwise.  Near the
*attained* minimum `t₀` of the nonzero lattice distances
(`SourceModelData.exists_attained_lattice_min`), the row mass
`∑_{y ≠ x} J_r(ρ(x-y))` is concentrated on the finitely many pairs of `ρ`-length `≤ t₀ + 1`
and every term is at most `K t₀ - K r`, which tends to `0` as `r ↓ t₀`.  Hence for `r`
slightly above `t₀` the *expected degree* `β_c ∑_y (1 - exp(-J_r))` drops below `1`, i.e.
the cutoff law enters the high-temperature region `β M < 1` of `IntensityMoments`, and every
natural cluster moment is finite there.  At and below `t₀` the cutoff has no off-diagonal
pair at all and the same conclusion holds with row mass `0`.

The deliverable is the model-level theorem
`SourceModelData.exists_forall_cutMoment_ne_top_small_radius`: there is a genuine interval
`(0, r₁)` of positive cutoffs on which *every* natural moment of the cluster volume at the
origin, and in particular the first moment `χ(r) = M.cutMassAt r 0`, is finite.  No
hypothesis on `β_c` is used: the smallness is bought by the cutoff, not by the temperature.

## What is *not* claimed

Nothing at large radii: `M.cutMassAt · 0` is monotone in `r`, so this says nothing about
`r ≥ r₁`, and in particular not the eventually-at-`∞` finiteness
`∀ᶠ r in atTop, M.cutMassAt r 0 ≠ ⊤` that `VolumeMoments/FirstMoment/Divergence` consumes.
No mean is inferred from the percolation probability being zero, and `θ = 0` is not used.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.StrictCutoffEpsilon
public import PercLib.CriticalLRP.IntensityMoments
public import PercLib.CriticalLRP.Analysis.BallAverage
public import PercLib.CriticalLRP.Analysis.Cutoff.Defs

/-! # Row-mass finiteness at small cutoff radii for the source model -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.SmallCutoffRowMass

open PercLib.CriticalLRP.Exploration.BFS
open PercLib.Probability PercLib.Probability.ExplorationEnvelope

/-! ## A general high-temperature moment theorem for an arbitrary edge profile

`IntensityMoments.lintegral_clusterVol_intensity_pow_ne_top` is stated for the
`intensityProfile` presentation.  The source cutoff law is the `bernoulliEdgeProb`
presentation, so the row-sum input below is stated for an arbitrary edge profile
`p : Sym2 V → unitInterval`; the two presentations agree at `p = bernoulliEdgeProb J _ β`
and the diagonal (loop) edges are irrelevant to `UniformRowBound`, which quantifies over
`t` with `x ∉ t`. -/

/-- **An admissible envelope constant exists for every `0 ≤ m < 1`.**  This is the
`m = 0` half added to `exists_admissible_lambda`: at `m = 0` the envelope is identically
`1`, so `(lam, C) = (2, 2)` works. -/
theorem exists_lam_envelope_of_nonneg_lt_one {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    ∃ lam C : ℝ, 1 < lam ∧ ∀ n : ℕ, lam * envelope m lam n ≤ C := by
  rcases eq_or_lt_of_le hm0 with h0 | hpos
  · refine ⟨2, 2, by norm_num, fun n => ?_⟩
    have henv : envelope m 2 n = 1 := by
      rw [← h0]
      induction n with
      | zero => exact envelope_zero 0 2
      | succ k ih => rw [envelope_succ, envelopeStep, ih]; norm_num
    rw [henv]; norm_num
  · obtain ⟨lam, hlam, hcond⟩ := exists_admissible_lambda hpos hm1
    refine ⟨lam, 1 / m, hlam, fun n => ?_⟩
    have hmlam : (0 : ℝ) < m * lam := by nlinarith
    have h1 : envelope m lam n ≤ 1 / (m * lam) :=
      envelope_le_inv_mul hpos hm1.le hlam.le hcond n
    have h2 : lam * (1 / (m * lam)) = 1 / m := by field_simp
    calc lam * envelope m lam n ≤ lam * (1 / (m * lam)) := by
          exact mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one hlam.le)
      _ = 1 / m := h2

/-- **Every natural cluster moment is finite under a uniform row bound `m < 1`**, for an
arbitrary edge profile.  This is the `bernoulliEdgeProb` companion of
`IntensityMoments.lintegral_clusterVol_intensity_pow_ne_top`; the proof is the same chain
(`lintegral_epow_cluster_le_of_envelope_bound`, `ae_encard_cluster_ne_top_of_epow_le`,
`lintegral_pow_encard_cluster_le`) and only the envelope parametrisation is new. -/
theorem lintegral_clusterVol_pow_ne_top_of_rowBound {V : Type*} [Countable V]
    (p : Sym2 V → unitInterval) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1)
    (hrow : UniformRowBound p m) (o : V) (k : ℕ) :
    ∫⁻ ω, clusterVol ω o ^ k ∂(prodBernoulli p) ≠ ⊤ := by
  obtain ⟨lam, C, hlam, hC⟩ := exists_lam_envelope_of_nonneg_lt_one hm0 hm1
  have hexp : ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard)
      ∂(prodBernoulli p) ≤ ENNReal.ofReal C :=
    lintegral_epow_cluster_le_of_envelope_bound hrow o hlam.le hC
  have hfin : ∀ᵐ ω ∂(prodBernoulli p), (cluster ω o).encard ≠ ⊤ :=
    ae_encard_cluster_ne_top_of_epow_le hlam hexp
  have hmom := lintegral_pow_encard_cluster_le hrow o hlam hC k
  refine ne_of_lt ?_
  calc ∫⁻ ω, clusterVol ω o ^ k ∂(prodBernoulli p)
      = ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k)
          ∂(prodBernoulli p) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfin] with ω hω
        rw [clusterVol_eq_encard]
        exact (ofReal_encard_toNat_pow (cluster ω o) hω k).symm
    _ ≤ ENNReal.ofReal (C * ((k.factorial : ℝ) / (Real.log lam) ^ k)) := hmom
    _ < ⊤ := ENNReal.ofReal_lt_top

end PercLib.CriticalLRP.SmallCutoffRowMass

namespace PercLib.CriticalLRP.SmallCutoffRowMass

open PercLib.CriticalLRP.Exploration.BFS
open PercLib.CriticalLRP.Orchestration
open PercLib.Probability

variable (M : SourceModelData)

/-! ## Where the cutoff intensity lives -/

/-- The truncated kernel on a pair of *distinct* vertices is the cutoff profile of the
source profile at the `ρ`-distance.  Loops evaluate to `0`, which is why `x ≠ y` is the only
case that matters for `UniformRowBound`. -/
theorem cutKernel_mk {r : ℝ} {x y : M.V} (hxy : x ≠ y) :
    M.cutKernel r s(x, y) = FiniteVolume.cutoffProfile M.K r (M.S.dist x y) := by
  rw [SourceModelData.cutKernel, Orchestration.cutRadialSym, radialSym_mk, ite_eq_right hxy]

/-- The `ρ`-distance only depends on the displacement: `dist x y = dist (y - x) 0`. -/
theorem dist_eq_dist_sub (x y : M.V) : M.S.dist x y = M.S.dist (y - x) 0 := by
  change M.S.ρ (toVec (x - y)) = M.S.ρ (toVec ((y - x) - 0))
  rw [sub_zero, ← M.S.ρ_neg (toVec (y - x))]
  congr 1
  funext i
  simp only [toVec, Pi.sub_apply, Pi.neg_apply, Int.cast_sub]
  ring

/-- Membership of the displacement in the `ρ`-ball is exactly the distance bound. -/
theorem mem_ball_sub_iff {r : ℝ} (x y : M.V) :
    y - x ∈ M.ball r ↔ M.S.dist x y ≤ r := by
  change M.S.ρ (toVec (y - x)) ≤ r ↔ M.S.dist x y ≤ r
  rw [dist_eq_dist_sub M x y]
  simp [SourceNormData.dist]

/-- **The row of the cutoff has at most `|B_{t₀+1}|` non-zero entries.**  For
`r ≤ t₀ + 1` the lattice points at `ρ`-distance at most `r` from `x` inject into the ball
of radius `t₀ + 1` about the origin under `y ↦ y - x`. -/
theorem card_filter_dist_le_ball_ncard {t0 r : ℝ} (hr1 : r ≤ t0 + 1) (x : M.V)
    (t : Finset M.V) :
    (t.filter (fun y => M.S.dist x y ≤ r)).card ≤ (M.ball (t0 + 1)).ncard := by
  classical
  have hinj : Function.Injective (fun y : M.V => y - x) := fun a b h => by
    have := congrArg (fun z => z + x) h
    simpa using this
  have hsub : (t.filter (fun y => M.S.dist x y ≤ r)).image (fun y => y - x)
      ⊆ (BallAverage.ball_finite M (t0 + 1)).toFinset := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_filter] at hy
    exact (BallAverage.ball_finite M (t0 + 1)).mem_toFinset.mpr
      ((mem_ball_sub_iff M x y).mpr (le_trans hy.2 hr1))
  calc (t.filter (fun y => M.S.dist x y ≤ r)).card
      = ((t.filter (fun y => M.S.dist x y ≤ r)).image (fun y => y - x)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (BallAverage.ball_finite M (t0 + 1)).toFinset.card := Finset.card_le_card hsub
    _ = (M.ball (t0 + 1)).ncard :=
        (Set.ncard_eq_toFinset_card _ (BallAverage.ball_finite M (t0 + 1))).symm

/-! ## The two row-mass bounds -/

/-- The truncated open probability of a non-loop pair whose `ρ`-length exceeds `r` is `0`:
the cutoff profile is identically zero there. -/
theorem edgeProb_eq_zero_of_lt {r : ℝ} {x y : M.V} (hxy : x ≠ y)
    (hd : r < M.S.dist x y) :
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit s(x, y) : ℝ) = 0 := by
  rw [bernoulliEdgeProb_coe, cutKernel_mk M (x := x) (y := y) hxy,
    FiniteVolume.cutoffProfile_of_lt hd, mul_zero, neg_zero, Real.exp_zero, sub_self]

/-- **The per-pair intensity bound at a cutoff above `t₀`.**  If `t₀ ≤ r` and `t₀` bounds all
nonzero lattice distances, then every non-loop pair has open probability at most
`β_c (K t₀ - K r)`: the profile is `K s - K r ≤ K t₀ - K r` for `s ≥ t₀`, it is `0` for
`s > r`, and `1 - exp(-u) ≤ u`. -/
theorem edgeProb_le_rowConst {t0 r : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (ht0r : t0 ≤ r) {x y : M.V}
    (hxy : x ≠ y) :
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit s(x, y) : ℝ)
      ≤ (M.betaCrit : ℝ) * (M.K t0 - M.K r) := by
  have hrpos : 0 < r := lt_of_lt_of_le ht0 ht0r
  have hspos : 0 < M.S.dist x y := M.S.dist_pos hxy
  have hst0 : t0 ≤ M.S.dist x y := by
    have h1 : t0 ≤ M.S.dist (y - x) 0 := hlat (y - x) (sub_ne_zero.mpr hxy.symm)
    rwa [dist_eq_dist_sub M x y]
  have hc0 : 0 ≤ (M.betaCrit : ℝ) * (M.K t0 - M.K r) := by
    refine mul_nonneg M.betaCrit.2 ?_
    exact sub_nonneg.mpr (M.K_antitone (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hrpos) ht0r)
  rw [bernoulliEdgeProb_coe, cutKernel_mk M (x := x) (y := y) hxy]
  rcases le_or_gt (M.S.dist x y) r with hd | hd
  · rw [FiniteVolume.cutoffProfile_of_le hd]
    have hKs : M.K (M.S.dist x y) ≤ M.K t0 :=
      M.K_antitone (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hspos) hst0
    set J : ℝ := M.K (M.S.dist x y) - M.K r with hJ
    have hJ0 : 0 ≤ J := by
      have hKr : M.K r ≤ M.K (M.S.dist x y) :=
        M.K_antitone (Set.mem_Ioi.mpr hspos) (Set.mem_Ioi.mpr hrpos) hd
      simp only [hJ]; linarith
    have hstep1 : 1 - Real.exp (-((M.betaCrit : ℝ) * J)) ≤ (M.betaCrit : ℝ) * J := by
      have h := Real.one_sub_le_exp_neg ((M.betaCrit : ℝ) * J)
      linarith
    have hstep2 : (M.betaCrit : ℝ) * J ≤ (M.betaCrit : ℝ) * (M.K t0 - M.K r) := by
      refine mul_le_mul_of_nonneg_left ?_ M.betaCrit.2
      simp only [hJ]; linarith
    linarith
  · rw [FiniteVolume.cutoffProfile_of_lt hd, mul_zero, neg_zero, Real.exp_zero, sub_self]
    exact hc0

/-- **Below the nearest-neighbour distance the cutoff has no pair at all.**  If `r ≤ t₀` then
every nonzero `ρ`-distance is at least `t₀ ≥ r`, and the truncated profile vanishes there
(the endpoint `s = r = t₀` gives `K r - K r = 0`).  The row mass is therefore `0`, uniformly
in the vertex. -/
theorem uniformRowBound_cutKernel_of_le_t0 {t0 r : ℝ}
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (hr : r ≤ t0) :
    UniformRowBound (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit) 0 := by
  classical
  intro x t hx
  have hzero : ∀ y ∈ t,
      (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit s(x, y) : ℝ) = 0 := by
    intro y hy
    have hxy : x ≠ y := by rintro rfl; exact hx hy
    have hst0 : t0 ≤ M.S.dist x y := by
      have h1 : t0 ≤ M.S.dist (y - x) 0 := hlat (y - x) (sub_ne_zero.mpr hxy.symm)
      rwa [dist_eq_dist_sub M x y]
    rcases lt_or_ge r (M.S.dist x y) with hd | hd
    · exact edgeProb_eq_zero_of_lt M hxy hd
    · rw [bernoulliEdgeProb_coe, cutKernel_mk M (x := x) (y := y) hxy,
        FiniteVolume.cutoffProfile_of_le hd]
      have hsr : M.S.dist x y = r := le_antisymm hd (le_trans hr hst0)
      rw [hsr, sub_self, mul_zero, neg_zero, Real.exp_zero, sub_self]
  refine le_of_eq ?_
  rw [Finset.sum_congr rfl hzero]
  simp

/-- **The row mass just above `t₀`.**  For `t₀ ≤ r ≤ t₀ + 1` every non-loop intensity is at
most `β_c (K t₀ - K r)`, and only the at most `|B_{t₀+1}|` pairs of `ρ`-length `≤ r`
contribute, so the whole row sum is at most `β_c |B_{t₀+1}| (K t₀ - K r)`.  The right-hand
side tends to `0` as `r ↓ t₀` — this is the row-mass finiteness mechanism. -/
theorem uniformRowBound_cutKernel_of_near {t0 r : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (ht0r : t0 ≤ r) (hr1 : r ≤ t0 + 1) :
    UniformRowBound (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)
      ((M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r)) := by
  classical
  intro x t hx
  have hrpos : 0 < r := lt_of_lt_of_le ht0 ht0r
  have hc0 : 0 ≤ (M.betaCrit : ℝ) * (M.K t0 - M.K r) := by
    refine mul_nonneg M.betaCrit.2 ?_
    exact sub_nonneg.mpr (M.K_antitone (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hrpos) ht0r)
  have hterm : ∀ y ∈ t,
      (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit s(x, y) : ℝ)
        ≤ (M.betaCrit : ℝ) * (M.K t0 - M.K r) := by
    intro y hy
    have hxy : x ≠ y := by rintro rfl; exact hx hy
    exact edgeProb_le_rowConst M ht0 hlat ht0r hxy
  have hsplit : ∑ y ∈ t,
      (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit s(x, y) : ℝ)
      = ∑ y ∈ t.filter (fun y => M.S.dist x y ≤ r),
          (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit s(x, y) : ℝ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro y hy hnot
    have hxy : x ≠ y := by rintro rfl; exact hx hy
    by_contra hne
    exact hnot (Finset.mem_filter.mpr
      ⟨hy, le_of_not_gt (fun hlt => hne (edgeProb_eq_zero_of_lt M hxy hlt))⟩)
  rw [hsplit]
  calc ∑ y ∈ t.filter (fun y => M.S.dist x y ≤ r),
        (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit s(x, y) : ℝ)
      ≤ ∑ _y ∈ t.filter (fun y => M.S.dist x y ≤ r),
          (M.betaCrit : ℝ) * (M.K t0 - M.K r) :=
        Finset.sum_le_sum fun y hy => hterm y (Finset.mem_filter.mp hy).1
    _ = (M.betaCrit : ℝ) * (M.K t0 - M.K r)
          * ((t.filter (fun y => M.S.dist x y ≤ r)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ (M.betaCrit : ℝ) * (M.K t0 - M.K r) * ((M.ball (t0 + 1)).ncard : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        exact_mod_cast card_filter_dist_le_ball_ncard M hr1 x t
    _ = (M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r) := by ring

/-! ## The row budget is eventually below `1` -/

/-- **The row budget `β_c |B_{t₀+1}| (K t₀ - K r)` is below `1` on a right-neighbourhood of
`t₀`.**  `K` is differentiable on `(0,∞)` hence continuous at `t₀ > 0`, so `K r → K t₀` as
`r ↓ t₀`; the factor `|B_{t₀+1}|` is a fixed finite number and `β_c` is fixed. -/
theorem exists_rowBudget_lt_one :
    ∃ t0 r₁ : ℝ, 0 < t0 ∧ t0 < r₁ ∧ r₁ ≤ t0 + 1 ∧
      (∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) ∧
      ∀ r : ℝ, t0 < r → r < r₁ →
        0 ≤ (M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r) ∧
        (M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r) < 1 := by
  obtain ⟨t0, ht0, -, hlat⟩ := M.exists_attained_lattice_min
  have hcont : ContinuousAt M.K t0 :=
    M.K_diff.continuousOn.continuousAt (Ioi_mem_nhds ht0)
  set B : ℝ := (M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) + 1 with hB
  have hB1 : 1 ≤ B := by
    have h1 : (0 : ℝ) ≤ (M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) :=
      mul_nonneg M.betaCrit.2 (Nat.cast_nonneg _)
    simp only [hB]; linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont (1 / B) (by positivity)
  have hminpos : (0 : ℝ) < min δ 2 := lt_min hδpos (by norm_num)
  have h2le : min δ 2 ≤ 2 := min_le_right _ _
  refine ⟨t0, t0 + min δ 2 / 2, ht0, by linarith, by linarith, hlat, ?_⟩
  intro r ht0r hrlt
  have hδle : min δ 2 ≤ δ := min_le_left _ _
  have hrδ : dist r t0 < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  have hKr : dist (M.K r) (M.K t0) < 1 / B := hδ hrδ
  rw [Real.dist_eq] at hKr
  have hKle : M.K t0 - M.K r ≤ |M.K r - M.K t0| := by
    rw [abs_sub_comm]; exact le_abs_self _
  have hdiff : M.K t0 - M.K r < 1 / B := lt_of_le_of_lt hKle hKr
  have hdiff0 : 0 ≤ M.K t0 - M.K r := by
    rw [sub_nonneg]
    exact M.K_antitone (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr (by linarith)) ht0r.le
  have hN : (0 : ℝ) ≤ ((M.ball (t0 + 1)).ncard : ℝ) := Nat.cast_nonneg _
  have hβ : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.2
  have hβN : (0 : ℝ) ≤ (M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) := mul_nonneg hβ hN
  have hKpos : (0 : ℝ) < 1 / B := by positivity
  have h3 : (M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) < B := by
    simp only [hB]; linarith
  have h2 : ((M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ)) * (1 / B) < 1 := by
    calc ((M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ)) * (1 / B)
        < B * (1 / B) := mul_lt_mul_of_pos_right h3 hKpos
      _ = 1 := by field_simp
  constructor
  · exact mul_nonneg hβN hdiff0
  · rcases eq_or_lt_of_le hβN with h0 | hpos
    · rw [← h0]; norm_num
    · calc (M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r)
          < ((M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ)) * (1 / B) :=
            mul_lt_mul_of_pos_left hdiff hpos
        _ < 1 := h2

/-! ## The small-radius finiteness theorem -/

/-- **Every natural cluster moment of the cutoff law is finite on a genuine interval of
positive cutoffs.**  For the actual `Orchestration.SourceModelData` there are `0 < t₀ < r₁`
with `M.cutMoment k r ≠ ⊤` for every `k` and every `r ∈ (0, r₁)`, and in particular the
first moment `χ(r) = M.cutMassAt r 0` is finite there.

`t₀` is the attained minimum of the nonzero lattice distances, so the cutoff row mass
vanishes below it and is at most `β_c |B_{t₀+1}| (K t₀ - K r) just above it; the latter tends
to `0` because `K` is continuous at `t₀ > 0`.  The high-temperature moment theorem
`lintegral_clusterVol_pow_ne_top_of_rowBound` then applies at the *critical* parameter —
the smallness is in the cutoff radius, not in `β`. -/
theorem exists_forall_cutMoment_ne_top_small_radius :
    ∃ t0 r₁ : ℝ, 0 < t0 ∧ t0 < r₁ ∧
      ∀ r : ℝ, 0 < r → r < r₁ →
        (∀ k : ℕ, M.cutMoment k r ≠ ⊤) ∧ M.cutMassAt r 0 ≠ ⊤ := by
  obtain ⟨t0, r₁, ht0, hr₁, hr₁le, hlat, hbudget⟩ := exists_rowBudget_lt_one M
  refine ⟨t0, r₁, ht0, hr₁, fun r hr hrlt => ?_⟩
  have hp : M.cutLaw r
      = prodBernoulli (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit) :=
    rfl
  have hmom : ∀ k : ℕ,
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ k
        ∂(prodBernoulli (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit))
        ≠ ⊤ := by
    intro k
    rcases le_or_gt r t0 with hle | hgt
    · exact lintegral_clusterVol_pow_ne_top_of_rowBound _ le_rfl (by norm_num)
        (uniformRowBound_cutKernel_of_le_t0 M hlat hle) 0 k
    · obtain ⟨hm0, hm1⟩ := hbudget r hgt (by linarith)
      exact lintegral_clusterVol_pow_ne_top_of_rowBound _ hm0 hm1
        (uniformRowBound_cutKernel_of_near M ht0 hlat hgt.le (by linarith)) 0 k
  refine ⟨fun k => ?_, ?_⟩
  · change M.cutMoment k r ≠ ⊤
    rw [SourceModelData.cutMoment, hp]
    exact hmom k
  · change M.cutMassAt r 0 ≠ ⊤
    rw [SourceModelData.cutMassAt, hp]
    simpa using hmom 1

/-- The headline interface: **there is a positive cutoff at which the source cutoff mass is
finite**, in the exact form `M.cutMassAt r 0 ≠ ⊤` requested (no `ℝ`-valued junk value is
being read). -/
theorem exists_cutMassAt_ne_top :
    ∃ r : ℝ, 0 < r ∧ M.cutMassAt r 0 ≠ ⊤ := by
  obtain ⟨t0, r₁, ht0, hr₁, h⟩ := exists_forall_cutMoment_ne_top_small_radius M
  exact ⟨(t0 + r₁) / 2, by linarith, (h _ (by linarith) (by linarith)).2⟩

end PercLib.CriticalLRP.SmallCutoffRowMass

namespace PercLib.CriticalLRP.SmallCutoffRowMass

open PercLib.CriticalLRP.Orchestration
open PercLib.Probability

/-! ## The filter form, and non-vacuity -/

/-- The interval form as an eventual statement at `0⁺`: **every natural cluster moment of the
cutoff law is finite for all sufficiently small positive cutoffs.**  This is the shape a
continuity or limit argument at `r → 0⁺` consumes. -/
theorem SourceModelData.eventually_cutMoment_ne_top_near_zero (M : SourceModelData) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (∀ k : ℕ, M.cutMoment k r ≠ ⊤) ∧ M.cutMassAt r 0 ≠ ⊤ := by
  obtain ⟨t0, r₁, ht0, hr₁, h⟩ := exists_forall_cutMoment_ne_top_small_radius M
  have hm : Set.Ioo (0 : ℝ) r₁ ∈ 𝓝[>] (0 : ℝ) := by
    refine Filter.inter_mem self_mem_nhdsWithin ?_
    exact nhdsWithin_le_nhds (Iio_mem_nhds (lt_trans ht0 hr₁))
  exact Filter.eventually_of_mem hm fun x hx => h x hx.1 hx.2

/-- **Non-vacuity.**  The witness model has a positive cutoff at which its cutoff mass is
finite, so `exists_cutMassAt_ne_top` is not a statement about an empty class of models. -/
example : ∃ r : ℝ, 0 < r ∧
    (Orchestration.Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).cutMassAt r 0 ≠ ⊤ :=
  exists_cutMassAt_ne_top (Orchestration.Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one)

/-- **Non-vacuity of the interval form** at the witness model. -/
example :
    ∃ t0 r₁ : ℝ, 0 < t0 ∧ t0 < r₁ ∧
      ∀ r : ℝ, 0 < r → r < r₁ →
        (∀ k : ℕ, (Orchestration.Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).cutMoment
            k r ≠ ⊤) ∧
          (Orchestration.Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one).cutMassAt r 0 ≠ ⊤ :=
  exists_forall_cutMoment_ne_top_small_radius
    (Orchestration.Witness.sourceModelWitness 1 le_rfl 1 zero_lt_one)

end PercLib.CriticalLRP.SmallCutoffRowMass

namespace PercLib.CriticalLRP.SmallCutoffRowMass

open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- **The row intensity of the cutoff tends to `0` as `r ↓ t₀`.**  At a fixed attained
minimum `t₀` of the nonzero lattice distances the cutoff row mass is at most
`β_c |B_{t₀+1}| (K t₀ - K r)`, and `K` is continuous at `t₀ > 0`, so this explicit row budget
converges to `0` from the right.  This is the analytic row-mass estimate that the finiteness
theorem consumes; it is *not* a statement about any cluster moment. -/
theorem tendsto_rowBudget_nhdsGT {t0 : ℝ} (ht0 : 0 < t0) :
    Filter.Tendsto
      (fun r : ℝ => (M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r))
      (𝓝[>] t0) (𝓝 0) := by
  have hcont : ContinuousAt M.K t0 :=
    M.K_diff.continuousOn.continuousAt (Ioi_mem_nhds ht0)
  have h1 : Filter.Tendsto (fun r : ℝ => M.K t0 - M.K r) (𝓝[>] t0) (𝓝 0) := by
    have h2 : Filter.Tendsto (fun r : ℝ => M.K r) (𝓝[>] t0) (𝓝 (M.K t0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h3 := h2.const_sub (M.K t0)
    simpa using h3
  have h4 := h1.const_mul ((M.betaCrit : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ))
  simpa [mul_assoc] using h4

end PercLib.CriticalLRP.SmallCutoffRowMass

namespace PercLib.CriticalLRP.SmallCutoffRowMass

open PercLib.CriticalLRP.Exploration.BFS
open PercLib.CriticalLRP.Orchestration
open PercLib.Probability

/-! ## The same statement at an arbitrary parameter `β`

`SourceModelData` has no hypothesis tying `β_c` to the profile, and none of the estimates
above used the value of the parameter: the open probability is only estimated through
`1 - exp(-u) ≤ u`, and the row budget is `β |B_{t₀+1}| (K t₀ - K r)`, which is small at *every*
fixed `β`.  The lemmas below make that explicit, so that a downstream argument
(β-monotonicity at a fixed small cutoff, for instance) can instantiate the finiteness at any
parameter rather than only at `β_c`. -/

variable (M : SourceModelData)

/-- The `β`-general form of `edgeProb_eq_zero_of_lt`. -/
theorem edgeProb_eq_zero_of_lt_of_beta (β : ℝ≥0) {r : ℝ} {x y : M.V} (hxy : x ≠ y)
    (hd : r < M.S.dist x y) :
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β s(x, y) : ℝ) = 0 := by
  rw [bernoulliEdgeProb_coe, cutKernel_mk M (x := x) (y := y) hxy,
    FiniteVolume.cutoffProfile_of_lt hd, mul_zero, neg_zero, Real.exp_zero, sub_self]

/-- The `β`-general form of `edgeProb_le_rowConst`. -/
theorem edgeProb_le_rowConst_of_beta (β : ℝ≥0) {t0 r : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (ht0r : t0 ≤ r) {x y : M.V}
    (hxy : x ≠ y) :
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β s(x, y) : ℝ)
      ≤ (β : ℝ) * (M.K t0 - M.K r) := by
  have hrpos : 0 < r := lt_of_lt_of_le ht0 ht0r
  have hspos : 0 < M.S.dist x y := M.S.dist_pos hxy
  have hst0 : t0 ≤ M.S.dist x y := by
    have h1 : t0 ≤ M.S.dist (y - x) 0 := hlat (y - x) (sub_ne_zero.mpr hxy.symm)
    rwa [dist_eq_dist_sub M x y]
  have hc0 : 0 ≤ (β : ℝ) * (M.K t0 - M.K r) := by
    refine mul_nonneg β.2 ?_
    exact sub_nonneg.mpr (M.K_antitone (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hrpos) ht0r)
  rw [bernoulliEdgeProb_coe, cutKernel_mk M (x := x) (y := y) hxy]
  rcases le_or_gt (M.S.dist x y) r with hd | hd
  · rw [FiniteVolume.cutoffProfile_of_le hd]
    have hKs : M.K (M.S.dist x y) ≤ M.K t0 :=
      M.K_antitone (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hspos) hst0
    set J : ℝ := M.K (M.S.dist x y) - M.K r with hJ
    have hJ0 : 0 ≤ J := by
      have hKr : M.K r ≤ M.K (M.S.dist x y) :=
        M.K_antitone (Set.mem_Ioi.mpr hspos) (Set.mem_Ioi.mpr hrpos) hd
      simp only [hJ]; linarith
    have hstep1 : 1 - Real.exp (-((β : ℝ) * J)) ≤ (β : ℝ) * J := by
      have h := Real.one_sub_le_exp_neg ((β : ℝ) * J)
      linarith
    have hstep2 : (β : ℝ) * J ≤ (β : ℝ) * (M.K t0 - M.K r) := by
      refine mul_le_mul_of_nonneg_left ?_ β.2
      simp only [hJ]; linarith
    linarith
  · rw [FiniteVolume.cutoffProfile_of_lt hd, mul_zero, neg_zero, Real.exp_zero, sub_self]
    exact hc0

/-- The `β`-general form of `uniformRowBound_cutKernel_of_le_t0`. -/
theorem uniformRowBound_cutKernel_of_le_t0_of_beta (β : ℝ≥0) {t0 r : ℝ}
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (hr : r ≤ t0) :
    UniformRowBound (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β) 0 := by
  classical
  intro x t hx
  have hzero : ∀ y ∈ t,
      (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β s(x, y) : ℝ) = 0 := by
    intro y hy
    have hxy : x ≠ y := by rintro rfl; exact hx hy
    have hst0 : t0 ≤ M.S.dist x y := by
      have h1 : t0 ≤ M.S.dist (y - x) 0 := hlat (y - x) (sub_ne_zero.mpr hxy.symm)
      rwa [dist_eq_dist_sub M x y]
    rcases lt_or_ge r (M.S.dist x y) with hd | hd
    · exact edgeProb_eq_zero_of_lt_of_beta M β hxy hd
    · rw [bernoulliEdgeProb_coe, cutKernel_mk M (x := x) (y := y) hxy,
        FiniteVolume.cutoffProfile_of_le hd]
      have hsr : M.S.dist x y = r := le_antisymm hd (le_trans hr hst0)
      rw [hsr, sub_self, mul_zero, neg_zero, Real.exp_zero, sub_self]
  refine le_of_eq ?_
  rw [Finset.sum_congr rfl hzero]
  simp

/-- The `β`-general form of `uniformRowBound_cutKernel_of_near`. -/
theorem uniformRowBound_cutKernel_of_beta_near (β : ℝ≥0) {t0 r : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (ht0r : t0 ≤ r) (hr1 : r ≤ t0 + 1) :
    UniformRowBound (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β)
      ((β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r)) := by
  classical
  intro x t hx
  have hrpos : 0 < r := lt_of_lt_of_le ht0 ht0r
  have hc0 : 0 ≤ (β : ℝ) * (M.K t0 - M.K r) := by
    refine mul_nonneg β.2 ?_
    exact sub_nonneg.mpr (M.K_antitone (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hrpos) ht0r)
  have hterm : ∀ y ∈ t,
      (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β s(x, y) : ℝ)
        ≤ (β : ℝ) * (M.K t0 - M.K r) := by
    intro y hy
    have hxy : x ≠ y := by rintro rfl; exact hx hy
    exact edgeProb_le_rowConst_of_beta M β ht0 hlat ht0r hxy
  have hsplit : ∑ y ∈ t,
      (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β s(x, y) : ℝ)
      = ∑ y ∈ t.filter (fun y => M.S.dist x y ≤ r),
          (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β s(x, y) : ℝ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro y hy hnot
    have hxy : x ≠ y := by rintro rfl; exact hx hy
    by_contra hne
    exact hnot (Finset.mem_filter.mpr
      ⟨hy, le_of_not_gt (fun hlt => hne (edgeProb_eq_zero_of_lt_of_beta M β hxy hlt))⟩)
  rw [hsplit]
  calc ∑ y ∈ t.filter (fun y => M.S.dist x y ≤ r),
        (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β s(x, y) : ℝ)
      ≤ ∑ _y ∈ t.filter (fun y => M.S.dist x y ≤ r), (β : ℝ) * (M.K t0 - M.K r) :=
        Finset.sum_le_sum fun y hy => hterm y (Finset.mem_filter.mp hy).1
    _ = (β : ℝ) * (M.K t0 - M.K r)
          * ((t.filter (fun y => M.S.dist x y ≤ r)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ (β : ℝ) * (M.K t0 - M.K r) * ((M.ball (t0 + 1)).ncard : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        exact_mod_cast card_filter_dist_le_ball_ncard M hr1 x t
    _ = (β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r) := by ring

/-- The `β`-general form of `exists_rowBudget_lt_one`: at every parameter `β`, the row budget
`β |B_{t₀+1}| (K t₀ - K r)` is below `1` on a right-neighbourhood of `t₀`. -/
theorem exists_rowBudget_lt_one_of_beta (β : ℝ≥0) :
    ∃ t0 r₁ : ℝ, 0 < t0 ∧ t0 < r₁ ∧ r₁ ≤ t0 + 1 ∧
      (∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) ∧
      ∀ r : ℝ, t0 < r → r < r₁ →
        0 ≤ (β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r) ∧
        (β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r) < 1 := by
  obtain ⟨t0, ht0, -, hlat⟩ := M.exists_attained_lattice_min
  have hcont : ContinuousAt M.K t0 :=
    M.K_diff.continuousOn.continuousAt (Ioi_mem_nhds ht0)
  set B : ℝ := (β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) + 1 with hB
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont (1 / B) (by
    have hN : (0 : ℝ) ≤ ((M.ball (t0 + 1)).ncard : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) := mul_nonneg β.2 hN
    have : (0 : ℝ) < B := by simp only [hB]; linarith
    positivity)
  have hminpos : (0 : ℝ) < min δ 2 := lt_min hδpos (by norm_num)
  have hδle : min δ 2 ≤ δ := min_le_left _ _
  have h2le : min δ 2 ≤ 2 := min_le_right _ _
  refine ⟨t0, t0 + min δ 2 / 2, ht0, by linarith, by linarith, hlat, ?_⟩
  intro r ht0r hrlt
  have hrδ : dist r t0 < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  have hKr : dist (M.K r) (M.K t0) < 1 / B := hδ hrδ
  rw [Real.dist_eq] at hKr
  have hKle : M.K t0 - M.K r ≤ |M.K r - M.K t0| := by
    rw [abs_sub_comm]; exact le_abs_self _
  have hdiff : M.K t0 - M.K r < 1 / B := lt_of_le_of_lt hKle hKr
  have hdiff0 : 0 ≤ M.K t0 - M.K r := by
    rw [sub_nonneg]
    exact M.K_antitone (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr (by linarith)) ht0r.le
  have hN : (0 : ℝ) ≤ ((M.ball (t0 + 1)).ncard : ℝ) := Nat.cast_nonneg _
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.2
  have hβN : (0 : ℝ) ≤ (β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) := mul_nonneg hβ hN
  have hBpos : (0 : ℝ) < B := by simp only [hB]; linarith
  have hKpos : (0 : ℝ) < 1 / B := by positivity
  have h3 : (β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) < B := by
    simp only [hB]; linarith
  have h2 : ((β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ)) * (1 / B) < 1 := by
    calc ((β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ)) * (1 / B)
        < B * (1 / B) := mul_lt_mul_of_pos_right h3 hKpos
      _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hBpos)]
  constructor
  · exact mul_nonneg hβN hdiff0
  · rcases eq_or_lt_of_le hβN with h0 | hpos
    · rw [← h0]; norm_num
    · calc (β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ) * (M.K t0 - M.K r)
          < ((β : ℝ) * ((M.ball (t0 + 1)).ncard : ℝ)) * (1 / B) :=
            mul_lt_mul_of_pos_left hdiff hpos
        _ < 1 := h2

/-- **Every natural cluster moment of the cutoff law is finite on a genuine interval of
positive cutoffs — at every parameter `β`, not only at `β_c`.**  The interval depends on `β`,
but no expectation or moment of the law at `β` is assumed. -/
theorem exists_forall_cutMoment_longRangeMeasure_ne_top_small_radius (β : ℝ≥0) :
    ∃ t0 r₁ : ℝ, 0 < t0 ∧ t0 < r₁ ∧
      ∀ r : ℝ, 0 < r → r < r₁ →
        (∀ k : ℕ, (∫⁻ ω, clusterVol ω (0 : M.V) ^ k
            ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β)) ≠ ⊤) ∧
          (∫⁻ ω, clusterVol ω (0 : M.V)
            ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β)) ≠ ⊤ := by
  obtain ⟨t0, r₁, ht0, hr₁, hr₁le, hlat, hbudget⟩ := exists_rowBudget_lt_one_of_beta M β
  refine ⟨t0, r₁, ht0, hr₁, fun r hr hrlt => ?_⟩
  have hmom : ∀ k : ℕ,
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ k
        ∂(prodBernoulli (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β)) ≠ ⊤ := by
    intro k
    rcases le_or_gt r t0 with hle | hgt
    · exact lintegral_clusterVol_pow_ne_top_of_rowBound _ le_rfl (by norm_num)
        (uniformRowBound_cutKernel_of_le_t0_of_beta M β hlat hle) 0 k
    · obtain ⟨hm0, hm1⟩ := hbudget r hgt (by linarith)
      exact lintegral_clusterVol_pow_ne_top_of_rowBound _ hm0 hm1
        (uniformRowBound_cutKernel_of_beta_near M β ht0 hlat hgt.le (by linarith)) 0 k
  have hp : longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β
      = prodBernoulli (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) β) := rfl
  refine ⟨fun k => ?_, ?_⟩
  · rw [hp]; exact hmom k
  · rw [hp]; simpa using hmom 1

end PercLib.CriticalLRP.SmallCutoffRowMass
