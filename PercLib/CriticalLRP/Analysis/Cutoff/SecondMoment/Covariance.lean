/-
Integrated and independently rebuilt from accepted Ultramath `smwyspk27`, member `m1`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# (I.4.16) at the actual radial cutoff model: the source second-moment covariance estimate

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of Proposition I.4.15,
display (I.4.16):

```
                          E_{β_c,r}[|K|^3 |K ∩ B_r|]
   0 ≤ E_{2,r} ≤ --------------------------------------- .
                     |B_r| E_{β_c,r}|K| E_{β_c,r}|K|^2
```

Its upper half is precisely the *disconnected* half of the two-cluster covariance inequality
(Lemma I.2.1) at `F = |K_0|`, `G = |K_y|^2`, summed over the finite closed window `B_r`:

    E[ 1(y ∉ K_0) |K_0| |K_y|^2 ] ≤ E|K_0| · E|K_y|^2 ,
    M.exclMassQuad r ≤ |B_r| · M.cutMoment 1 r · M.cutMoment 2 r .

Main results:

* `twoCluster_cardFun_pow_le` : the extended two-cluster BK inequality for powers of the extended
  cluster cardinality, in `ℝ≥0∞` (`|K| = ⊤` on infinite clusters), derived from the general
  `ℝ≥0∞`-valued two-cluster BK `Hrest.twoCluster_ennreal`.
* `SourceModelData.exclSingle_le` : its `(a, b) = (1, 2)` instance at the actual cutoff law.
* `SourceModelData.exclMassQuad_le_ball_mul_moments` : the window bound, over `ℝ≥0∞`, with no
  finiteness hypothesis on any cutoff moment.
* `SourceModelData.ball_mul_moments_le_exclMassQuad_add_window` : the Harris–FKG half, keeping the
  *connected* third moment `E[|K_0|^3 #(K_0 ∩ B_r)]` explicitly, so that the two-sided covariance
  statement is the honest one used by (I.4.14)/(I.4.16).

No `sorry`, `admit`, `native_decide` or custom axiom.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Finiteness
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.ExclusionSwap.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.MomentHom
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Main

/-! # Power-form two-cluster covariance and the excluded second moment -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP
namespace SecondMomentCov

variable {V : Type*} [Countable V]

/-! ## 1. The extended two-cluster BK inequality for powers of `cardFun`

The general `ℝ≥0∞`-valued two-cluster BK (`Hrest.twoCluster_ennreal`, Lemma I.2.1(i) for
non-negative increasing measurable functionals) asks for three things of each functional:
monotonicity under `⊆`, continuity from below along the edge exhaustion — this is where an
infinite cluster is allowed to take the value `⊤`, the truncation being inside the *functional*
and not inside the inequality — and measurability.  We discharge all three for
`S ↦ cardFun S ^ k`, so the result is a genuine product bound in `ℝ≥0∞` with no finiteness
hypothesis and no silent `⊤ ↦ 0` truncation. -/

/-- **Lemma I.2.1(i) for powers of the extended cluster cardinality.**  For the canonical
independent-edge law `edgeMeasure π` and non-negative integers `a`, `b`,

`E[1(x ↮ y) |K_x|^a |K_y|^b] ≤ E|K_x|^a · E|K_y|^b`,

where `|K| = cardFun K`, equal to `⊤` for an infinite cluster. -/
theorem twoCluster_cardFun_pow_le {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (x y : V) (a b : ℕ) :
    ∫⁻ ω, {ω' : Config V | ¬ Connects ω' x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) ^ a * Percolation.cardFun (cluster ω y) ^ b)
        ∂(edgeMeasure π)
      ≤ (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ a ∂(edgeMeasure π)) *
          (∫⁻ ω, Percolation.cardFun (cluster ω y) ^ b ∂(edgeMeasure π)) :=
  Hrest.twoCluster_ennreal (π := π) hπ x y 𝓔 h𝓔mono h𝓔
    (F := fun S => Percolation.cardFun S ^ a)
    (G := fun S => Percolation.cardFun S ^ b)
    (fun _S _T hST => pow_le_pow_left' (Percolation.cardFun_mono hST) a)
    (fun _S _T hST => pow_le_pow_left' (Percolation.cardFun_mono hST) b)
    (I420Case1.pow_cont_of_cont (x := x) 𝓔 Percolation.cardFun_mono
      (Hrest.cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 x) a)
    (I420Case1.pow_cont_of_cont (x := y) 𝓔 Percolation.cardFun_mono
      (Hrest.cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 y) b)
    ((Hrest.measurable_cardFun_cluster_canonical x).pow_const a)
    ((Hrest.measurable_cardFun_cluster_canonical y).pow_const b)

/-- The `(a, b) = (1, 2)` instance in `clusterVol` form: the exact disconnected covariance half of
(I.4.16) at one pair of sites. -/
theorem twoCluster_clusterVol_one_two_le {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (x y : V) :
    ∫⁻ ω, {ω' : Config V | ¬ Connects ω' x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω x * clusterVol ω y ^ 2) ∂(edgeMeasure π)
      ≤ (∫⁻ ω, clusterVol ω x ∂(edgeMeasure π)) *
          (∫⁻ ω, clusterVol ω y ^ 2 ∂(edgeMeasure π)) := by
  have h := twoCluster_cardFun_pow_le (V := V) hπ 𝓔 h𝓔mono h𝓔 x y 1 2
  simpa only [I420Case1.cardFun_cluster_eq_clusterVol, pow_one] using h

end SecondMomentCov
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## 2. The one-point factors at the actual cutoff law -/

/-- `E_{β_c,r}|K_v|^m` is the cutoff moment `M.cutMoment m r`, at every vertex `v`.  This is
`lintegral_clusterVol_pow_vertex`, a genuinely infinite-volume identity: `M.cutLaw r` is invariant
under lattice translations. -/
theorem cutMoment_eq_lintegral_vertex (r : ℝ) (m : ℕ) (v : M.V) :
    M.cutMoment m r
      = ∫⁻ ω, clusterVol ω v ^ m ∂(edgeMeasure (M.cutProb r)) := by
  rw [← M.lintegral_clusterVol_pow_vertex r v m, E1Sign.cutLaw_eq]

/-- The extended-cardinality form of the same one-point factor. -/
theorem cutMoment_eq_lintegral_cardFun (r : ℝ) (m : ℕ) (v : M.V) :
    M.cutMoment m r
      = ∫⁻ ω, Percolation.cardFun (cluster ω v) ^ m ∂(edgeMeasure (M.cutProb r)) :=
  (M.cutMoment_eq_lintegral_vertex r m v).trans
    (by
      refine (lintegral_congr fun ω => ?_).symm
      rw [I420Case1.cardFun_cluster_eq_clusterVol])

/-! ## 3. The single-site covariance bound -/

/-- **The integrand of the excluded quadratic mass, in two-cluster BK form.**  At a fixed window
vertex `y`, the `ℓ = 0` summand of `M.exclMassQuad` is the extended-real
`1(0 ↮ y) |K_0|^1 |K_y|^2`. -/
theorem exclSingle_eq (r : ℝ) (y : M.V) :
    (∫⁻ ω, clusterVol ω (0 : M.V) *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
        ∂(M.cutLaw r))
      = ∫⁻ ω, {ω' : Config M.V | ¬ Connects ω' (0 : M.V) y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω (0 : M.V)) ^ 1 * Percolation.cardFun (cluster ω y) ^ 2)
          ∂(edgeMeasure (M.cutProb r)) := by
  rw [← E1Sign.cutLaw_eq M r]
  refine lintegral_congr fun ω => ?_
  rw [I420Case1.indicator_compl_cluster, I420Case1.cardFun_cluster_eq_clusterVol,
    I420Case1.cardFun_cluster_eq_clusterVol, pow_one]
  ring

/-- **The single-site covariance half of (I.4.16) at the actual cutoff law:**
`E_{β_c,r}[1(y ∉ K_0) |K_0| |K_y|²] ≤ E_{β_c,r}|K_0| · E_{β_c,r}|K_y|²`, in `ℝ≥0∞` and with no
finiteness hypothesis. -/
theorem exclSingle_le (r : ℝ) (y : M.V) :
    (∫⁻ ω, clusterVol ω (0 : M.V) *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
        ∂(M.cutLaw r))
      ≤ M.cutMoment 1 r * M.cutMoment 2 r := by
  classical
  let := Encodable.ofCountable (Sym2 M.V)
  rw [exclSingle_eq M r y]
  have hbk := SecondMomentCov.twoCluster_cardFun_pow_le (V := M.V) (π := M.cutProb r)
    (E1Sign.cutProb_lt_one M r) (Percolation.edgeExhaustion (E := Sym2 M.V))
    Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover (0 : M.V) y 1 2
  refine hbk.trans (le_of_eq ?_)
  rw [M.cutMoment_eq_lintegral_cardFun r 1 (0 : M.V),
    M.cutMoment_eq_lintegral_cardFun r 2 y]

/-! ## 4. Summing over the finite window `B_r` -/

/-- `M.exclMassQuad` is the finite sum over the window of the one-site expectations (finite
Tonelli). -/
theorem exclMassQuad_eq_sum_single (r : ℝ) :
    M.exclMassQuad r = ∑ y ∈ E1Sign.ballF M r,
      ∫⁻ ω, clusterVol ω (0 : M.V) *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
        ∂(M.cutLaw r) := by
  simp only [SourceModelData.exclMassQuad, SourceModelData.exclSumQuad, Finset.mul_sum]
  rw [lintegral_finsetSum]
  exact fun y _ => M.measurable_summandQuad y r

/-- **The source second-moment covariance estimate (I.4.16), disconnected half, at the actual
radial cutoff model:**

`E_{β_c,r}[ |K_0| ∑_{y ∈ B_r} 1(y ∉ K_0)|K_y|² ] ≤ |B_r| · E_{β_c,r}|K_0| · E_{β_c,r}|K_0|²`.

This bounds the negative term of the paper's `E_{2,r}` numerator
`|B_r| E|K| E|K|² − E[|K| ∑_{y∈B_r} 1(y∉K)|K_y|²]`, i.e. it is exactly what (I.4.16) needs on
the disconnected side.  It is an `ℝ≥0∞` inequality with no finiteness hypothesis on any moment,
and it is strictly stronger than the crude `p2QuadMass_le` bound `|B|(M₂ + M₄)`. -/
theorem exclMassQuad_le_ball_mul_moments (r : ℝ) :
    M.exclMassQuad r ≤ ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r := by
  rw [M.exclMassQuad_eq_sum_single r]
  have hsum : (∑ y ∈ E1Sign.ballF M r,
      ∫⁻ ω, clusterVol ω (0 : M.V) *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
        ∂(M.cutLaw r))
      ≤ ∑ _y ∈ E1Sign.ballF M r, (M.cutMoment 1 r * M.cutMoment 2 r) :=
    Finset.sum_le_sum fun y _ => M.exclSingle_le r y
  refine hsum.trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, E1Sign.card_ballF M r, mul_assoc]

end SourceModelData
end PercLib.CriticalLRP.Orchestration

/-! ## 5. The Harris–FKG half, with the connected third moment kept explicit

The full joint moment `E[|K_0| ∑_{y∈B_r}|K_y|²]` is *not* bounded by `|B_r| E|K| E|K|²`: splitting
`∑_{y∈B_r}|K_y|² = ∑_{y∈B_r} 1(y∉K_0)|K_y|² + ∑_{y∈B_r} 1(y∈K_0)|K_y|²` and using
`|K_y| = |K_0|` on `{y ∈ K_0}`, the second group is exactly the connected third moment
`E[|K_0|³ #(K_0 ∩ B_r)]`.  So the honest two-sided covariance statement of (I.4.14)/(I.4.16) is

`|B_r| E|K| E|K|² ≤ E[|K_0| ∑_{y∈B_r} 1(y∉K_0)|K_y|²] + E[|K_0|³ #(K_0 ∩ B_r)]`,

This is the two-sided covariance sandwich underlying (I.4.16). The connected term is retained
below as `M.connCubeMass r` (and, equivalently, as its `cutLaw` integral).
-/

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- `powMomentAt (M.cutProb r)` is the cutoff moment. -/
theorem powMomentAt_cutProb_eq_cutMoment (r : ℝ) (m : ℕ) (v : M.V) :
    I420Case1.powMomentAt (M.cutProb r) m v = M.cutMoment m r := by
  rw [I420Case1.powMomentAt, M.cutMoment_eq_lintegral_cardFun r m v]
  exact lintegral_congr fun ω => by rw [I420Case1.cardFun_cluster_eq_clusterVol]

/-- `M.exclMassQuad` is `I420Case1.mixedExcl` at `(a, b) = (1, 2)`. -/
theorem exclMassQuad_eq_mixedExcl (r : ℝ) :
    M.exclMassQuad r = I420Case1.mixedExcl (M.cutProb r) 0 1 2 (E1Sign.ballF M r) := by
  simp only [SourceModelData.exclMassQuad, SourceModelData.exclSumQuad, I420Case1.mixedExcl,
    E1Sign.cutLaw_eq M r, pow_one]

/-- `M.connCubeMass r = E[|K_0|³ #(K_0 ∩ B_r)]`, written as an integral against the actual
cutoff law.  This is the connected third moment of the `E_{2,r}` numerator of (I.4.16). -/
theorem connCubeMass_eq_lintegral (r : ℝ) :
    M.connCubeMass r = ∫⁻ ω, clusterVol ω (0 : M.V) ^ 3 *
      ∑ y ∈ E1Sign.ballF M r,
        (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(M.cutLaw r) := by
  rw [SourceModelData.connCubeMass]
  rw [show (∫⁻ u : Sym2 M.V → ℝ, M.connCubeFun r u ∂(markMeasure M.V))
      = ∫⁻ u : Sym2 M.V → ℝ, (fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 3 *
          ∑ y ∈ E1Sign.ballF M r,
            (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y)
          (atParameter (M.cutProb r) u) ∂(markMeasure M.V) from
        lintegral_congr fun u => rfl]
  exact lintegral_mark_eq_cutLaw M
    (fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 3 *
      ∑ y ∈ E1Sign.ballF M r,
        (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y)
    ((measurable_clusterVol (0 : M.V)).pow_const 3 |>.mul
      (Finset.measurable_sum _ fun y _ =>
        measurable_const.indicator (measurableSet_cluster_mem (0 : M.V) y))) r

/-- `windowMoment (M.cutProb r) 0 3 (ballF M r)` is the same connected third moment. -/
theorem windowMoment_eq_connCubeLaw (r : ℝ) :
    I420Case1.windowMoment (M.cutProb r) 0 3 (E1Sign.ballF M r)
      = ∫⁻ ω, clusterVol ω (0 : M.V) ^ 3 *
          ∑ y ∈ E1Sign.ballF M r,
            (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(M.cutLaw r) := by
  rw [I420Case1.windowMoment, ← E1Sign.cutLaw_eq M r]
  refine lintegral_congr fun ω => ?_
  rw [clusterVolIn_coe_finset]
  refine congrArg (fun t : ℝ≥0∞ => clusterVol ω (0 : M.V) ^ 3 * t) ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ cluster ω (0 : M.V)
  · rw [Set.indicator_of_mem hy, ite_eq_left hy]
  · rw [Set.indicator_of_notMem hy, ite_eq_right hy]

/-- The connected third moment in the `I420Case1` window notation. -/
theorem windowMoment_eq_connCubeMass (r : ℝ) :
    I420Case1.windowMoment (M.cutProb r) 0 3 (E1Sign.ballF M r) = M.connCubeMass r :=
  (M.windowMoment_eq_connCubeLaw r).trans (M.connCubeMass_eq_lintegral r).symm

/-- **The Harris–FKG half of the two-cluster covariance inequality at the window, with the
connected third moment retained:**

`|B_r| E|K| E|K|² ≤ M.exclMassQuad r + M.connCubeMass r`.

Together with `exclMassQuad_le_ball_mul_moments` this pins the window covariance to the connected
third moment, exactly as in the `E_{2,r}` display of (I.4.14)/(I.4.16). -/
theorem ball_mul_moments_le_exclMassQuad_add_connCubeMass (r : ℝ) :
    ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r
      ≤ M.exclMassQuad r + M.connCubeMass r := by
  classical
  let := Encodable.ofCountable (Sym2 M.V)
  have hterm : ∀ y ∈ E1Sign.ballF M r,
      I420Case1.powMomentAt (M.cutProb r) 1 (0 : M.V) *
          I420Case1.powMomentAt (M.cutProb r) 2 y
        = M.cutMoment 1 r * M.cutMoment 2 r := fun y _ => by
    rw [M.powMomentAt_cutProb_eq_cutMoment r 1 (0 : M.V),
      M.powMomentAt_cutProb_eq_cutMoment r 2 y]
  have hprod : I420Case1.prodFactor (M.cutProb r) 0 1 2 (E1Sign.ballF M r)
      = ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r := by
    rw [I420Case1.prodFactor, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      E1Sign.card_ballF M r, mul_assoc]
  have h := I420Case1.prodFactor_le_mixedExcl_add_window (π := M.cutProb r)
    (E1Sign.cutProb_lt_one M r) (Percolation.edgeExhaustion (E := Sym2 M.V))
    Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover (0 : M.V) 1 2
    (E1Sign.ballF M r)
  rwa [hprod, ← M.exclMassQuad_eq_mixedExcl r, M.windowMoment_eq_connCubeMass r] at h

end SourceModelData
end PercLib.CriticalLRP.Orchestration


/-! ## 6. Consequences for the source's `p = 2` right-hand side (I.4.14) -/

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The source's `p = 2` right-hand side is bounded by three times the mean-field window
product.**  This composes the accepted exclusion swap `p2RHS = 3 · exclMassQuad` with
`exclMassQuad_le_ball_mul_moments`, giving the paper's (I.4.14) final display
`3 β_c |J'(r)| |B_r| E|K| E|K|²` at the source moments; the error estimate remains separate. -/
theorem p2RHS_le_three_mul_ball_mul_moments (r : ℝ) :
    M.p2RHS r ≤ 3 * (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r) := by
  rw [M.p2RHS_eq_three_mul_exclMassQuad r]
  exact mul_le_mul' le_rfl (M.exclMassQuad_le_ball_mul_moments r)

/-- The real-valued form of `p2RHS_le_three_mul_ball_mul_moments`, under the two finiteness
hypotheses that make both displayed moments finite.  No finiteness of any higher moment is used. -/
theorem p2RHS_toReal_le (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (M.p2RHS r).toReal
      ≤ 3 * ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal := by
  have hle := M.p2RHS_le_three_mul_ball_mul_moments r
  have htop : (3 * (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) h1) h2)
  have ht := ENNReal.toReal_mono htop hle
  have hright : (3 * (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r)).toReal
      = 3 * ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal := by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
    ring
  rwa [hright] at ht

end SourceModelData
end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.SecondMomentCov.twoCluster_cardFun_pow_le
#print axioms PercLib.CriticalLRP.SecondMomentCov.twoCluster_clusterVol_one_two_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_eq_lintegral_vertex
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_eq_lintegral_cardFun
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclSingle_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclSingle_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuad_eq_sum_single
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuad_le_ball_mul_moments
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_eq_lintegral
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowMoment_eq_connCubeMass
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.ball_mul_moments_le_exclMassQuad_add_connCubeMass
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_le_three_mul_ball_mul_moments
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_toReal_le
