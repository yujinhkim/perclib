/-
The `p = 2` excluded-term expansion of the Russo integrand of Lemma I.4.1, at the normalized
source model.

Swarm `smwv94uce`, member `m6`, direction D2 (general `p` binomial/pivot algebra, specialised at
`p = 2`).  Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1:

  `d/dr E_{beta,r}|K|^p = beta |J'(r)| sum_{ell=0}^{p-1} binom(p,ell)
      E_{beta,r}[ |K|^{ell+1} sum_{y in B_r} 1(y notin K)|K_y|^{p-ell} ]`.

At `p = 2` the `ell`-sum has exactly two terms, and this file proves that the source's right-hand
side at `p = 2` is, at the actual normalized model and at the actual closed `rho`-ball `B_r`,

  `E[|K| sum_{y in B_r, y notin K} |K_y|^2] + 2 E[|K|^2 sum_{y in B_r, y notin K}|K_y|]`,

i.e. `p2RHS`.  The identification starts from the landed general-`p` mass-transport identity
`PivotFlux.lintegral_paperSumP_eq_rooted` and collapses the binomial summand at `p = 2`; the
coefficient `2` is `binom(2,1)`, and no exponent is changed.

What is *not* claimed here: the analytic step that differentiates `s ↦ (M.cutMoment 2 s).toReal`
in the radius and produces the factor `beta |J'(r)|` is not proved in this file, so nothing here
is a two-sided or one-sided derivative statement, and no corner (`r` an attained radius) is
discussed.  The identity below is exactly the expectation identity that the derivative statement
needs on its right-hand side.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Defs

/-!
# The `p = 2` excluded-term form of (I.4.1) at the source model

The main results are `rootedSumP_two_eq` (pointwise `p = 2` collapse of the binomial increment,
on the almost-sure event that clusters are finite), `lintegral_rootedSumP_two_eq` and
`lintegral_paperSumP_two_eq` (the expectation form for the rooted and the paper double sum), and
`lintegral_paperSumP_two_eq_of_cutMass`, where the almost-sure finiteness of clusters is derived
from finiteness of the first cutoff moment rather than assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.Orchestration.SourceModelData
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace PercLib.CriticalLRP
namespace PivotFlux

variable (M : SourceModelData)

/-! ## The window sums over the closed `rho`-ball -/

/-- Collapsing the rooted `p`-th flux summand to the finite closed ball `B_r = E1Sign.ballF M r`,
for an arbitrary weight `g` of the `y`-th cluster: the ball indicator vanishes off `ballF`, and
on `ballF` the excluded indicator is that of the complement of the cluster of the origin. -/
theorem tsum_ball_indicator_eq_finset (r : ℝ) (ω : Config M.V) (g : M.V → ℝ≥0∞) :
    (∑' c : M.V, (if M.S.ρ (toVec c) ≤ r then 1 else 0) *
        configIndicator {ω' : Config M.V | ¬ Connects ω' (0 : M.V) c} ω * g c)
      = ∑ y ∈ E1Sign.ballF M r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * g y := by
  rw [tsum_eq_sum (s := E1Sign.ballF M r)]
  · refine Finset.sum_congr rfl fun y hy => ?_
    have hyb : M.S.ρ (toVec y) ≤ r := (E1Sign.mem_ballF M).mp hy
    rw [ite_eq_left hyb, one_mul, configIndicator_not_connects_eq_compl_indicator]
  · intro c hc
    have hgt : r < M.S.ρ (toVec c) := by
      by_contra hle
      exact hc ((E1Sign.mem_ballF M).mpr (not_lt.mp hle))
    rw [ite_eq_right (not_le.mpr hgt), zero_mul, zero_mul]

/-- The excluded linear window sum is the landed `p = 1` inner ball sum. -/
theorem exclSumLin_eq_ballSum (r : ℝ) (ω : Config M.V) :
    exclSumLin M r ω = ballSum M r ω := by
  rw [ballSum_eq_finset]
  rfl

/-- The landed `p = 1` excluded mass is the `|K|`-weighted excluded linear window sum.  Thus the
`ell = 1` term of the `p = 2` formula below is built on exactly the `p = 1` window of the landed
excluded-mass package, not on a new object. -/
theorem exclMass_eq_lintegral_exclSumLin (r : ℝ) :
    E1Sign.exclMass M r = ∫⁻ ω, clusterVol ω (0 : M.V) * exclSumLin M r ω ∂(M.cutLaw r) := by
  rw [E1Sign.exclMass]
  refine lintegral_congr fun ω => ?_
  rw [exclSumLin_eq_ballSum, ballSum_eq_finset]

/-! ## The `p = 2` binomial increment -/

/-- The `p = 2` cluster-volume increment: `(|K_b| + |K_c|)^2 - |K_b|^2 = 2|K_b||K_c| + |K_c|^2`
in `ℝ≥0∞`.  This is the pointwise form of the two excluded terms of (I.4.1) at `p = 2`. -/
theorem ofReal_sq_sub_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal ((a + b) ^ 2 - a ^ 2)
      = 2 * ENNReal.ofReal a * ENNReal.ofReal b + ENNReal.ofReal b ^ 2 := by
  have hEq : (a + b) ^ 2 - a ^ 2 = 2 * a * b + b ^ 2 := by ring
  rw [hEq, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow hb,
    show (2 * a * b) = 2 * (a * b) by ring, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul ha]
  rw [← ENNReal.ofReal_ofNat (n := 2)]
  ring

/-- The source's `ell`-sum at `p = 2` has exactly two terms, with the binomial coefficients
`binom(2,0) = 1` and `binom(2,1) = 2`: this is the step that produces the coefficient `2` of the
second excluded term of (I.4.1). -/
theorem sum_range_two_choose (x y : ℝ≥0∞) :
    (∑ ℓ ∈ Finset.range 2, (Nat.choose 2 ℓ : ℝ≥0∞) * x ^ (ℓ + 1) * y ^ (2 - ℓ))
      = x * y ^ 2 + 2 * x ^ 2 * y := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

/-- The landed general-`p` binomial step `BinomialI41.ofReal_mul_pow_sub_pow` at `p = 2`, with
the `ell`-sum evaluated by `sum_range_two_choose`: the source's binomial increment at `p = 2` is
`|K_b| |K_c|^2 + 2 |K_b|^2 |K_c|`, so the coefficient of the second excluded term is exactly
`binom(2,1) = 2` and there are no further terms. -/
theorem ofReal_mul_pow_sub_pow_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a * ENNReal.ofReal ((a + b) ^ 2 - a ^ 2)
      = ENNReal.ofReal a * ENNReal.ofReal b ^ 2
        + 2 * ENNReal.ofReal a ^ 2 * ENNReal.ofReal b := by
  rw [BinomialI41.ofReal_mul_pow_sub_pow a b ha hb 2, sum_range_two_choose]

/-! ## Measurability of the excluded window sums -/

theorem measurable_exclSumQuad (r : ℝ) : Measurable fun ω : Config M.V => exclSumQuad M r ω := by
  refine Finset.measurable_sum _ fun y _ => ?_
  exact (Measurable.indicator measurable_const
    (measurableSet_cluster_mem (0 : M.V) y).compl).mul ((measurable_clusterVol y).pow_const 2)

theorem measurable_exclSumLin (r : ℝ) : Measurable fun ω : Config M.V => exclSumLin M r ω := by
  refine Finset.measurable_sum _ fun y _ => ?_
  exact (Measurable.indicator measurable_const
    (measurableSet_cluster_mem (0 : M.V) y).compl).mul (measurable_clusterVol y)

/-! ## The pointwise `p = 2` collapse -/

/-- **The `p = 2` collapse of the rooted Russo integrand.**  On the event that every cluster is
finite, the rooted `p = 2` flux integrand is exactly the two excluded terms of (I.4.1):

  `|K_0| sum_{y in B_r, y notin K_0}|K_y|^2 + 2 |K_0|^2 sum_{y in B_r, y notin K_0}|K_y|`.

The hypothesis `hfin` is what identifies the `ℝ`-valued cluster volumes `clusterVolR` used by the
landed general-`p` binomial step with the `ℝ≥0∞` volumes `clusterVol`; on an infinite cluster the
landed convention truncates to `0` and the two differ. -/
theorem rootedSumP_two_eq (r : ℝ) (ω : Config M.V)
    (hfin : ∀ v : M.V, clusterVol ω v ≠ ⊤) :
    rootedSumP M 2 r ω
      = clusterVol ω (0 : M.V) * exclSumQuad M r ω
        + 2 * clusterVol ω (0 : M.V) ^ 2 * exclSumLin M r ω := by
  have hof : ∀ y : M.V, ENNReal.ofReal (clusterVolR ω y) = clusterVol ω y := fun y =>
    (BinomialI41.clusterVol_eq_ofReal_clusterVolR (hfin y)).symm
  have hsum : (∑' c : M.V, (if M.S.ρ (toVec c) ≤ r then 1 else 0) *
        configIndicator {ω' : Config M.V | ¬ Connects ω' (0 : M.V) c} ω *
        ENNReal.ofReal ((clusterVolR ω (0 : M.V) + clusterVolR ω c) ^ 2 -
          clusterVolR ω (0 : M.V) ^ 2))
      = ∑ y ∈ E1Sign.ballF M r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y *
            (2 * clusterVol ω (0 : M.V) * clusterVol ω y + clusterVol ω y ^ 2) := by
    rw [tsum_ball_indicator_eq_finset M r ω
      (fun c => ENNReal.ofReal ((clusterVolR ω (0 : M.V) + clusterVolR ω c) ^ 2 -
        clusterVolR ω (0 : M.V) ^ 2))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ofReal_sq_sub_sq _ _ (clusterVolR_nonneg ω (0 : M.V)) (clusterVolR_nonneg ω y),
      hof (0 : M.V), hof y]
  rw [rootedSumP, hsum]
  have hexp : (∑ y ∈ E1Sign.ballF M r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y *
          (2 * clusterVol ω (0 : M.V) * clusterVol ω y + clusterVol ω y ^ 2))
      = 2 * clusterVol ω (0 : M.V) * exclSumLin M r ω + exclSumQuad M r ω := by
    have hstep : ∀ y ∈ E1Sign.ballF M r,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y *
            (2 * clusterVol ω (0 : M.V) * clusterVol ω y + clusterVol ω y ^ 2)
          = 2 * clusterVol ω (0 : M.V) *
              (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
            + ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2 := by
      intro y _
      rw [mul_add]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  rw [hexp, mul_add]
  ring

/-! ## The expectation form -/

/-- **The `p = 2` excluded-term identity, rooted form.**  On the almost-sure event that all
clusters are finite, the expectation of the rooted `p = 2` Russo integrand is the source's `p = 2`
right-hand side `p2RHS r` divided by `beta |J'(r)|`. -/
theorem lintegral_rootedSumP_two_eq (r : ℝ)
    (hfin : ∀ᵐ ω ∂(M.cutLaw r), ∀ v : M.V, clusterVol ω v ≠ ⊤) :
    ∫⁻ ω, rootedSumP M 2 r ω ∂(M.cutLaw r) = p2RHS M r := by
  have hpt : ∀ᵐ ω ∂(M.cutLaw r), rootedSumP M 2 r ω
      = clusterVol ω (0 : M.V) * exclSumQuad M r ω
        + 2 * clusterVol ω (0 : M.V) ^ 2 * exclSumLin M r ω :=
    hfin.mono fun ω h => rootedSumP_two_eq M r ω h
  rw [p2RHS, exclMassQuad, exclMassSqLin]
  rw [lintegral_congr_ae hpt]
  rw [lintegral_add_left (f := fun ω : Config M.V => clusterVol ω (0 : M.V) * exclSumQuad M r ω)
    (g := fun ω : Config M.V => 2 * clusterVol ω (0 : M.V) ^ 2 * exclSumLin M r ω)
    ((measurable_clusterVol (0 : M.V)).mul (measurable_exclSumQuad M r))]
  congr 1
  rw [show (∫⁻ ω : Config M.V, 2 * clusterVol ω (0 : M.V) ^ 2 * exclSumLin M r ω
        ∂(M.cutLaw r))
      = ∫⁻ ω : Config M.V, 2 * (clusterVol ω (0 : M.V) ^ 2 * exclSumLin M r ω)
        ∂(M.cutLaw r) from lintegral_congr fun ω => by ring]
  exact lintegral_const_mul 2
    (((measurable_clusterVol (0 : M.V)).pow_const 2).mul (measurable_exclSumLin M r))

/-- Almost every configuration has every cluster finite, from finiteness of the first cutoff
moment (the cutoff mass does not depend on the vertex). -/
theorem ae_clusterVol_ne_top (r : ℝ) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) :
    ∀ᵐ ω ∂(M.cutLaw r), ∀ v : M.V, clusterVol ω v ≠ ⊤ := by
  rw [ae_all_iff]
  intro v
  refine (ae_lt_top (measurable_clusterVol v) ?_).mono fun ω hω => hω.ne
  rw [show (∫⁻ ω, clusterVol ω v ∂(M.cutLaw r)) = M.cutMassAt r v from rfl,
    M.cutMassAt_eq_zero r v]
  exact h1

/-- **The `p = 2` excluded-term identity for the source's double sum.**  The expectation of
`sum_{x in K} sum_{y in B_r(x)} 1(y notin K)((|K| + |K_y|)^2 - |K|^2)` equals the source's `p = 2`
right-hand side divided by `beta |J'(r)|`: the two excluded terms

  `E[|K| sum_{y in B_r, y notin K}|K_y|^2]`  and  `2 E[|K|^2 sum_{y in B_r, y notin K}|K_y|]`.

This is the general-`p` mass-transport step of the tree (`lintegral_paperSumP_eq_rooted`) composed
with the `p = 2` collapse above; it is unconditional in `ℝ≥0∞` except for the almost-sure
finiteness of clusters. -/
theorem lintegral_paperSumP_two_eq (r : ℝ)
    (hfin : ∀ᵐ ω ∂(M.cutLaw r), ∀ v : M.V, clusterVol ω v ≠ ⊤) :
    ∫⁻ ω, paperSumP M 2 r ω ∂(M.cutLaw r) = p2RHS M r := by
  rw [lintegral_paperSumP_eq_rooted, lintegral_rootedSumP_two_eq M r hfin]

/-- The same identity with the almost-sure finiteness of clusters derived from a finite first
cutoff moment, which is the hypothesis the source carries at `beta <= beta_c`. -/
theorem lintegral_paperSumP_two_eq_of_cutMass (r : ℝ) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) :
    ∫⁻ ω, paperSumP M 2 r ω ∂(M.cutLaw r) = p2RHS M r :=
  lintegral_paperSumP_two_eq M r (ae_clusterVol_ne_top M r h1)

/-! ## The closed/strict/shell split at `p = 2`

The source's `B_r` is closed.  At an attained radius the closed window strictly contains the
strict window `{rho < r}`, and the difference is the sphere `M.shellF r` (the landed `p = 1`
package records the same split as `E1Sign.exclMass = exclMassStrict + exclMassShell`).  The
lemmas here prove that the `p = 2` right-hand side `p2RHS` splits in exactly the same way, so the
identity `lintegral_paperSumP_two_eq` is unambiguously the *closed-window* one and its strict
companion is `p2RHSStrict`.
-/

theorem ballFLt_subset_ballF (r : ℝ) : M.ballFLt r ⊆ E1Sign.ballF M r := by
  intro y hy
  exact (E1Sign.mem_ballF M).mpr ((M.mem_ballFLt).mp hy).le

/-- The closed quadratic excluded window sum is the strict one plus the shell one. -/
theorem exclSumQuad_eq_strict_add_shell (r : ℝ) (ω : Config M.V) :
    exclSumQuad M r ω = exclSumQuadLt M r ω + exclSumQuadShell M r ω := by
  have h := Finset.sum_sdiff
    (f := fun y => ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y *
      clusterVol ω y ^ 2) (ballFLt_subset_ballF M r)
  rw [M.ballFLt_sdiff_shellF r] at h
  rw [exclSumQuad, exclSumQuadLt, exclSumQuadShell, ← h]
  exact add_comm _ _

/-- The closed linear excluded window sum is the strict one plus the shell one. -/
theorem exclSumLin_eq_strict_add_shell (r : ℝ) (ω : Config M.V) :
    exclSumLin M r ω = exclSumLinLt M r ω + exclSumLinShell M r ω := by
  have h := Finset.sum_sdiff
    (f := fun y => ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y *
      clusterVol ω y) (ballFLt_subset_ballF M r)
  rw [M.ballFLt_sdiff_shellF r] at h
  rw [exclSumLin, exclSumLinLt, exclSumLinShell, ← h]
  exact add_comm _ _

theorem measurable_exclSumQuadLt (r : ℝ) : Measurable fun ω : Config M.V => exclSumQuadLt M r ω := by
  refine Finset.measurable_sum _ fun y _ => ?_
  exact (Measurable.indicator measurable_const
    (measurableSet_cluster_mem (0 : M.V) y).compl).mul ((measurable_clusterVol y).pow_const 2)

theorem measurable_exclSumQuadShell (r : ℝ) :
    Measurable fun ω : Config M.V => exclSumQuadShell M r ω := by
  refine Finset.measurable_sum _ fun y _ => ?_
  exact (Measurable.indicator measurable_const
    (measurableSet_cluster_mem (0 : M.V) y).compl).mul ((measurable_clusterVol y).pow_const 2)

theorem measurable_exclSumLinLt (r : ℝ) : Measurable fun ω : Config M.V => exclSumLinLt M r ω := by
  refine Finset.measurable_sum _ fun y _ => ?_
  exact (Measurable.indicator measurable_const
    (measurableSet_cluster_mem (0 : M.V) y).compl).mul (measurable_clusterVol y)

theorem measurable_exclSumLinShell (r : ℝ) :
    Measurable fun ω : Config M.V => exclSumLinShell M r ω := by
  refine Finset.measurable_sum _ fun y _ => ?_
  exact (Measurable.indicator measurable_const
    (measurableSet_cluster_mem (0 : M.V) y).compl).mul (measurable_clusterVol y)

/-- The `p = 2` quadratic excluded mass is the strict-window mass plus the shell mass. -/
theorem exclMassQuad_eq_strict_add_shell (r : ℝ) :
    exclMassQuad M r = exclMassQuadLt M r + exclMassQuadShell M r := by
  rw [exclMassQuad, exclMassQuadLt, exclMassQuadShell,
    ← lintegral_add_left (f := fun ω : Config M.V => clusterVol ω (0 : M.V) * exclSumQuadLt M r ω)
      (g := fun ω : Config M.V => clusterVol ω (0 : M.V) * exclSumQuadShell M r ω)
      ((measurable_clusterVol (0 : M.V)).mul (measurable_exclSumQuadLt M r))]
  exact lintegral_congr fun ω => by rw [exclSumQuad_eq_strict_add_shell M r ω, mul_add]

/-- The `p = 2` squared-root excluded mass is the strict-window mass plus the shell mass. -/
theorem exclMassSqLin_eq_strict_add_shell (r : ℝ) :
    exclMassSqLin M r = exclMassSqLinLt M r + exclMassSqLinShell M r := by
  rw [exclMassSqLin, exclMassSqLinLt, exclMassSqLinShell,
    ← lintegral_add_left
      (f := fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 2 * exclSumLinLt M r ω)
      (g := fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 2 * exclSumLinShell M r ω)
      (((measurable_clusterVol (0 : M.V)).pow_const 2).mul (measurable_exclSumLinLt M r))]
  exact lintegral_congr fun ω => by rw [exclSumLin_eq_strict_add_shell M r ω, mul_add]

/-- **The `p = 2` closed / strict / shell decomposition.**  The source's `p = 2` right-hand side
at the closed ball `B_r` is the strict-window right-hand side plus the exact shell contribution,
mirroring the landed `p = 1` identity `E1Sign.exclMass = exclMassStrict + exclMassShell`.  Off the
attained radii the shell is empty and the two right-hand sides coincide; at an attained radius
they differ by `p2RHSShell r`, which is the `p = 2` counterpart of the corner discrepancy proved
for `p = 1`. -/
theorem p2RHS_eq_strict_add_shell (r : ℝ) :
    p2RHS M r = p2RHSStrict M r + p2RHSShell M r := by
  rw [p2RHS, p2RHSStrict, p2RHSShell, exclMassQuad_eq_strict_add_shell M r,
    exclMassSqLin_eq_strict_add_shell M r]
  ring

/-- The landed strict-window excluded mass is the `|K|`-weighted strict linear window sum, so the
strict companion `p2RHSStrict` extends the same `p = 1` object. -/
theorem exclMassStrict_eq_lintegral (r : ℝ) :
    M.exclMassStrict r = ∫⁻ ω, clusterVol ω (0 : M.V) * exclSumLinLt M r ω ∂(M.cutLaw r) :=
  rfl

/-- The landed shell excluded mass is the `|K|`-weighted shell linear window sum. -/
theorem exclMassShell_eq_lintegral (r : ℝ) :
    M.exclMassShell r = ∫⁻ ω, clusterVol ω (0 : M.V) * exclSumLinShell M r ω ∂(M.cutLaw r) :=
  rfl

end PivotFlux
end PercLib.CriticalLRP

end
