/-
The excluded quadratic window sums of Hutchcroft's Lemma I.4.1 at `p = 2`.

Swarm `smwv94uce`, member `m6`, direction D2: the general-`p` binomial/mass-transport algebra,
specialised at `p = 2`.  The source (Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, Lemma I.4.1) at `p = 2` has exactly two excluded terms

  `E[|K| sum_{y in B_r, y notin K} |K_y|^2]`  and  `2 E[|K|^2 sum_{y in B_r, y notin K} |K_y|]`,

multiplied by `beta |J'(r)|`.  This file only names the two sums and their moments, at the
normalized source model `M` and its closed `rho`-ball `B_r = B_r(0)` (`E1Sign.ballF M r`), with
the unexcluded indicator `1(y notin K_0)` taken from the cluster of the origin.  No proof, no
coefficient and no exponent is assumed: the identification with the `p = 2` binomial expansion of
`rootedSumP` is proved in `Binomial.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.ScalarFactor.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RightExcludedMass.Defs

/-!
# The `p = 2` excluded window sums and their moments

`exclSumQuad`/`exclSumLin` are the two window sums of (I.4.1) at `p = 2`; `exclMassQuad`/
`exclMassSqLin` are their expectations weighted by `|K|` and `|K|^2`; `p2RHS` is the source's
right-hand side at `p = 2` divided by `beta |J'(r)|`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open PercLib.CriticalLRP.Orchestration
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- The excluded quadratic window sum `sum_{y in B_r, y notin K_0} |K_y|^2` of (I.4.1) at
`p = 2` (`ell = 0`).  The sum is over the finite closed `rho`-ball `E1Sign.ballF M r`, and the
indicator is that of the complement of the cluster of the origin, exactly as in
`E1Sign.exclMass`. -/
noncomputable def exclSumQuad (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑ y ∈ E1Sign.ballF M r,
    ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2

/-- The excluded linear window sum `sum_{y in B_r, y notin K_0} |K_y|` of (I.4.1) at `p = 2`
(`ell = 1`).  It is the inner sum of the landed `p = 1` excluded mass `E1Sign.exclMass`. -/
noncomputable def exclSumLin (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑ y ∈ E1Sign.ballF M r,
    ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y

/-- `E_{beta_c,r}[ |K_0| sum_{y in B_r, y notin K_0} |K_y|^2 ]`, the `ell = 0` excluded term of
(I.4.1) at `p = 2`. -/
noncomputable def exclMassQuad (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) * exclSumQuad M r ω ∂(M.cutLaw r)

/-- `E_{beta_c,r}[ |K_0|^2 sum_{y in B_r, y notin K_0} |K_y| ]`, the `ell = 1` excluded term of
(I.4.1) at `p = 2` (without the binomial coefficient `2`, which sits in `p2RHS`). -/
noncomputable def exclMassSqLin (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 * exclSumLin M r ω ∂(M.cutLaw r)

/-- The source's right-hand side of (I.4.1) at `p = 2` divided by `beta |J'(r)|`:
`exclMassQuad r + 2 * exclMassSqLin r`, i.e. the two excluded terms with the exact binomial
coefficient `2` on the second one. -/
noncomputable def p2RHS (r : ℝ) : ℝ≥0∞ :=
  exclMassQuad M r + 2 * exclMassSqLin M r

/-- The `ℓ`-th summand of the source's `p = 2` derivative formula: the excluded window sum
`∑_{y∈B_r} 1(y∉K)|K_y|^{2-ℓ}` weighted by `|K|^{ℓ+1}`, integrated against `cutLaw r`.
Only `ℓ = 0` and `ℓ = 1` occur in the source sum. -/
noncomputable def p2Term (r : ℝ) (ℓ : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ^ (ℓ + 1) *
    ∑ y ∈ E1Sign.ballF M r,
      ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ (2 - ℓ)
    ∂(M.cutLaw r)

/-- The source's displayed sum at `p = 2`, kept literally as a sum over `ℓ ∈ {0,1}` with the
binomial coefficients `binom(2,ℓ)`.  `Finiteness.p2SourceSum_eq_p2RhsMass` shows it is
`exclMassQuad + 2 · exclMassSqLin`. -/
noncomputable def p2SourceSum (r : ℝ) : ℝ≥0∞ :=
  ∑ ℓ ∈ Finset.range 2, (Nat.choose 2 ℓ : ℝ≥0∞) * p2Term M r ℓ


/-! ### The strict-window and shell companions at `p = 2`

The source's `B_r` is the *closed* ball, so at an attained radius (`r` the `rho`-length of some
edge) the closed window `E1Sign.ballF r` is strictly larger than the strict window
`M.ballFLt r`, and the difference is the sphere `M.shellF r`.  The landed `p = 1` package records
this as `E1Sign.exclMass = exclMassStrict + exclMassShell`; the definitions below are the exact
`p = 2` companions of those two objects, so that the same split can be proved for `p2RHS`.
-/

/-- The strict-window (`{rho < r}`) quadratic excluded window sum
`sum_{y in B_{<r}, y notin K_0}|K_y|^2`. -/
noncomputable def exclSumQuadLt (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑ y ∈ M.ballFLt r,
    ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2

/-- The shell (`{rho = r}`) quadratic excluded window sum
`sum_{y in B_r minus B_{<r}, y notin K_0}|K_y|^2`. -/
noncomputable def exclSumQuadShell (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑ y ∈ M.shellF r,
    ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2

/-- The strict-window linear excluded window sum `sum_{y in B_{<r}, y notin K_0}|K_y|`; it is the
inner sum of the landed `exclMassStrict`. -/
noncomputable def exclSumLinLt (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑ y ∈ M.ballFLt r,
    ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y

/-- The shell linear excluded window sum; it is the inner sum of the landed `exclShellFun`. -/
noncomputable def exclSumLinShell (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑ y ∈ M.shellF r,
    ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y

/-- `E[|K_0| sum_{y in B_{<r}, y notin K_0}|K_y|^2]`. -/
noncomputable def exclMassQuadLt (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) * exclSumQuadLt M r ω ∂(M.cutLaw r)

/-- `E[|K_0| sum_{y in shell r, y notin K_0}|K_y|^2]`. -/
noncomputable def exclMassQuadShell (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) * exclSumQuadShell M r ω ∂(M.cutLaw r)

/-- `E[|K_0|^2 sum_{y in B_{<r}, y notin K_0}|K_y|]`. -/
noncomputable def exclMassSqLinLt (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 * exclSumLinLt M r ω ∂(M.cutLaw r)

/-- `E[|K_0|^2 sum_{y in shell r, y notin K_0}|K_y|]`. -/
noncomputable def exclMassSqLinShell (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 * exclSumLinShell M r ω ∂(M.cutLaw r)

/-- The source's `p = 2` right-hand side with the ball replaced by the strict ball
`{rho < r}`, at the same law `cutLaw r`. -/
noncomputable def p2RHSStrict (r : ℝ) : ℝ≥0∞ :=
  exclMassQuadLt M r + 2 * exclMassSqLinLt M r

/-- The shell contribution to the source's `p = 2` right-hand side at radius `r`. -/
noncomputable def p2RHSShell (r : ℝ) : ℝ≥0∞ :=
  exclMassQuadShell M r + 2 * exclMassSqLinShell M r


/-! ## The real-valued second-moment derivative weights -/

/-- The real number `β_c (-K'(r))` times the two excluded masses, with the binomial
coefficient on the squared-root excluded term. -/
noncomputable def rhsScalarTwo (r : ℝ) : ℝ :=
  M.coeffRHS r * (M.p2RHS r).toReal

/-- The strict-window real second-moment derivative weight. -/
noncomputable def rhsScalarTwoStrict (r : ℝ) : ℝ :=
  M.coeffRHS r * (M.p2RHSStrict r).toReal

end SourceModelData
end PercLib.CriticalLRP.Orchestration

end

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2SourceSum
