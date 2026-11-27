/-
Integrated Ultramath work, swarm `smwyop3kc`, member `m2`.
Production worktree: `.scratch/critical-lrp-orchestration` (read only), HEAD
`2e544875fbae83810bd1aa1de1d8faddcdeacc05`.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Endpoint.Model
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.Analysis.Cutoff.IntervalAC.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.RatioInduction.RatioBound

/-!
# Case 3 ⇒ the cubic (I.4.19) moment bound at the actual source model

`I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3` proves, at the genuine
cutoff family `M.cutProb` and the genuine cluster moments
`momOf (fun r => M.cutProb r) 0 ·`, the two normalized limits of (I.4.20):

* `A_0(r) / (|B_r| E|K| · E|K|³) → 1`
* `A_1(r) / (|B_r| E|K|² · E|K|²) → 1`

where `A_ℓ(r) = E[|K|^{ℓ+1} Σ_{y∈B_r} 1(y∉K)|K_y|^{3-ℓ}]` is
`mixedExclR (M.cutProb r) 0 (ℓ+1) (3-ℓ) B_r`.  `moment_upper_bound_three_ratio_of_pos`
consumes exactly those two limits (plus the pointwise mass transport
`A_2 = A_0`) and produces the `p = 3` step (I.4.19).

This file performs the handoff.  What is *discharged* here:

* the two decorrelation bounds `hA0`, `hAmid` of `derivative_bound` — replaced by
  the Case-3 limits;
* the induction hypothesis `hIH` at `p = 3` — vacuous, as in
  `moment_upper_bound_three`;
* the pointwise mass transport `A_2 = A_0` — `mixedExclR_cutProb_swap`, the
  midpoint-reflection transport of `I420Endpoint.mixedExcl_cutKernel_swap`
  transported to `M.cutProb`;
* positivity of `|B_r|` — `ballCard_pos`;
* positivity of the first three moments at *every* radius — at `r ≥ 1` from the
  root moment-finiteness range `hMa` via `momR_pos`, and at `0 < r < 1` from the
  monotonicity `M.cutMoment_monotone` of the cutoff moment in the radius plus
  finiteness at `r = 1`.

What remains an explicit, independent input (see the theorem's hypotheses):

* the Case-3 analytic package: `(HD)(3)`, finite open triangle, the first-moment
  ODE package `hderiv/hpos/hode` with its error bound and vanishing, the lower
  two-point bound `hlow`, the second-moment lower comparison `hgm`, and the
  root moment range `hMa` (orders up to `4` at `p = 3`);
* measurability in the radius of the first two cutoff moments;
* regular variation of `E|K|` of index `α` and of `E|K|²` of index `3α`;
* the exact derivative identity of Lemma I.4.1 at order `3`, for *every* radius
  `r > 0`, with the binomial sum of the actual excluded moments and a tangent
  `cr`.  This is *stronger* than anything the library proves: the shipped
  `Analysis/Cutoff/Deriv.hasDerivAt_cutMassReal_of_summableMajorant` is an
  off-corner statement (`r ∉ M.cornerRadii`), and `M.cornerRadii` contains
  positive radii (`exists_pos_mem_cornerRadii`), at which the admitted bond
  changes the cutoff kernel discontinuously.  So the global form is an honest
  remaining obstruction (inherited from `moment_upper_bound_three` and
  `SecondInduction.*`), not something discharged here;
* the first-moment normalization `cr r · |B_r| · E|K| · r → α` in the
  `(1+o(1))` form used by the induction step.

Nothing here asserts a higher moment finite from the first moment, and no use is
made of an upper moment inequality to obtain the decorrelation input.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Topology

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration
open PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-! ## The two ingredients that the handoff itself supplies -/

/-- **Mass transport at the actual cutoff law**: swapping the two exponents does
not change the excluded mixed moment, for any exponents and any finite window.

This is `I420Endpoint.mixedExcl_cutKernel_swap` transported from the bernoulli
edge law `bernoulliEdgeProb (M.cutKernel r)` to the abbreviation
`M.cutProb r`, and then to the real-valued `mixedExclR`. -/
theorem mixedExclR_cutProb_swap (M : SourceModelData) (r : ℝ) (a b : ℕ)
    (B : Finset M.V) :
    I420Case1.mixedExclR (M.cutProb r) (0 : M.V) a b B =
      I420Case1.mixedExclR (M.cutProb r) (0 : M.V) b a B := by
  unfold I420Case1.mixedExclR
  rw [I420Endpoint.mixedExcl_cutKernel_swap M r a b B]

/-- The source ball `B_r` is nonempty at every positive radius, so its
cardinality is a positive real number.  (`0 ∈ B_r` because `ρ 0 = 0`.) -/
theorem ballCard_pos (M : SourceModelData) {r : ℝ} (hr : 0 < r) :
    0 < I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r := by
  have h0 : toVec (0 : M.V) = 0 := by
    funext i
    simp [toVec]
  have hmem : (0 : M.V) ∈ (BallAverage.ball_finite M r).toFinset := by
    rw [Set.Finite.mem_toFinset]
    simp only [SourceModelData.ball, Set.mem_ofPred_eq]
    rw [h0, M.S.ρ_zero]
    exact hr.le
  have hpos : 0 < ((BallAverage.ball_finite M r).toFinset.card : ℕ) :=
    Finset.card_pos.mpr ⟨0, hmem⟩
  unfold I420Case3.ballCard
  exact_mod_cast hpos

/-- **`M.cornerRadii` contains a positive radius.**

`M.cornerRadii` is `{ρ(x - y) : x ≠ y}`; with `d ≥ 1` the lattice has two
distinct points `0` and `Pi.single 0 1`, so a positive radius is attained.

This is recorded because the shipped differentiation theorem for the cutoff mass
(`Analysis/Cutoff/Deriv.hasDerivAt_cutMassReal_of_summableMajorant`) carries the
off-corner hypothesis `r ∉ M.cornerRadii`: the global derivative identity used
as an input below is *not* what the library proves, and cannot hold at a radius
at which a bond with positive profile is admitted. -/
theorem exists_pos_mem_cornerRadii (M : SourceModelData) :
    ∃ r ∈ M.cornerRadii, 0 < r := by
  let i₀ : Fin M.d := ⟨0, M.hd⟩
  let e : M.V := Pi.single i₀ (1 : ℤ)
  have he : e ≠ 0 := by
    intro h
    have h1 : e i₀ = (0 : M.V) i₀ := congrFun h i₀
    simp only [e, Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have h0e : (0 : M.V) ≠ e := fun h => he (Eq.symm h)
  exact ⟨M.S.dist 0 e, ⟨0, e, h0e, rfl⟩, M.S.dist_pos (x := 0) (y := e) h0e⟩

/-- **The first three cutoff moments are positive at every positive radius**,
from finiteness of the root moments of orders `1, 2, 3, 4` at radii `≥ 1`.

At `r ≥ 1` this is `momR_pos`; at `0 < r < 1` it is the radius monotonicity
`SourceModelData.cutMoment_monotone` together with finiteness at `r = 1`. -/
theorem momOf_cutProb_pos_three (M : SourceModelData)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤) :
    ∀ m, 1 ≤ m → m ≤ 3 → ∀ r : ℝ, 0 < r →
      0 < momOf (fun r => M.cutProb r) (0 : M.V) m r := by
  intro m _ _ r hr
  have hfin1 : I420Case1.powMomentAt (M.cutProb 1) m (0 : M.V) ≠ ⊤ := by
    have h := hMa 1 le_rfl (m - 1) (by omega)
    have hidx : m - 1 + 1 = m := by omega
    rwa [hidx] at h
  rcases le_or_gt 1 r with hge | hlt
  · have hfin : I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤ := by
      have h := hMa r hge (m - 1) (by omega)
      have hidx : m - 1 + 1 = m := by omega
      rwa [hidx] at h
    exact I420Case3.momR_pos hfin
  · have hle : I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≤
        I420Case1.powMomentAt (M.cutProb 1) m (0 : M.V) :=
      M.cutMoment_monotone m (le_of_lt hlt)
    exact I420Case3.momR_pos (ne_top_of_le_ne_top hfin1 hle)

/-! ## The handoff -/

/-- **The cubic (I.4.19) upper moment bound at the actual source cutoff family,
from the Case-3 decorrelation limits.**

The conclusion is the paper's `E|K|³ ≤ (1+o(1))·3·(E|K|²/E|K|)²·E|K|` at the
genuine cutoff law `M.cutProb`, with `E|K|^m = momOf (fun r => M.cutProb r) 0 m r`
and the target written `mixedMoment 3`. -/
theorem case3_moment_three_bound_of_HD_case3 (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
    (hmommeas1 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 1 r))
    (hmommeas2 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 2 r))
    (hRV1 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α)
    (hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α))
    {cr : ℝ → ℝ} (hcr0 : ∀ r, 0 < r → 0 ≤ cr r)
    (hderivId : ∀ r : ℝ, 0 < r → HasDerivAt
      (fun s => momOf (fun s => M.cutProb s) (0 : M.V) 3 s)
      (cr r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset) r)
    (hcnorm : ∀ ε > 0, ∀ᶠ r in atTop,
      cr r * I420Case3.ballCard (fun r =>
          (BallAverage.ball_finite M r).toFinset) r *
        momOf (fun r => M.cutProb r) (0 : M.V) 1 r * r ≤ (1 + ε) * M.α) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      momOf (fun r => M.cutProb r) (0 : M.V) 3 r ≤
        (1 + ε) * mixedMoment 3 (fun m r =>
          momOf (fun r => M.cutProb r) (0 : M.V) m r) r := by
  obtain ⟨hAend, hAmid⟩ :=
    case3_hAend_hAmid_cutPoly_source_of_HD_case3 M hHD3 hTri hc hαd hlow hfin hβ hr₀
      hderiv hpos hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 3 (by norm_num) hθ0 hθ1 hMa hc3 hgm
  have hmom := momOf_cutProb_pos_three M hMa
  -- the pointwise mass transport of the two end terms
  have hmass : ∀ x, 0 < x →
      (fun ℓ r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
        (BallAverage.ball_finite M r).toFinset) 0 x =
      (fun ℓ r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
        (BallAverage.ball_finite M r).toFinset) (3 - 1) x := by
    intro x _
    exact mixedExclR_cutProb_swap M x 1 3 _
  exact moment_upper_bound_three_ratio_of_pos (mom := fun m r =>
      momOf (fun r => M.cutProb r) (0 : M.V) m r) M.hα hmom hmommeas1 hmommeas2
    hRV1 hRV2 (fun x hx => ballCard_pos M hx) hcr0 hderivId hmass hAend hAmid hcnorm

end I420Case3

end PercLib.CriticalLRP
