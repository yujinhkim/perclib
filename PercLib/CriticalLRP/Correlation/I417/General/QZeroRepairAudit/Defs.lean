/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

Ultramath swarm `smwziumdb`, member `m2`, direction `d5` (truth audit of the small-`T` / additive
replacements for the `q = 0`, `p = 3` star estimate).

# Definitions for the audit of the `q = 0` star / product-gap replacements

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Proposition I.4.15, Case 3, printed pp. 46–47 (displays (I.4.16) and
the definition of `E_{2,r}`), and Lemma I.4.17 printed p. 45.

The Case-3 numerator of (I.4.16) is

  `|B_r| E|K| E|K|² − E[|K| ∑_{y∈B_r} 1(y∉K)|K_y|²]`,

i.e. a **product-minus-excluded** window moment.  The one-copy *star* moment
`E[|K_0|³ 1(y ∈ K_0)]` is a different object: it is `starMoment` of the `q = 0` instance and it is
*not* the summand of the numerator.  This file isolates the per-vertex quantities that separate
them, so that the two targets can be compared exactly.

All definitions are the natural `ℝ≥0∞` ones (no `⊤ ↦ 0` conversion anywhere); the real-valued
statements of `Main.lean`/`Sharp.lean` carry the finiteness hypotheses explicitly.

Nothing here assumes a moment, a triangle bound or a diagram bound; the definitions are pure
integrals against the canonical independent-edge law `edgeMeasure π`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroDiagonal.Main
public import PercLib.CriticalLRP.Correlation.I417.Final
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main

/-! # Independently reviewed Case-3 repair-audit module: Defs -/


noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP
namespace QZeroRepairAudit

open Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The four per-vertex objects

Fix a basepoint `o` (the origin) and a window vertex `y`.  The paper's `|K|` is `|K_o|`, and
`1(y ∉ K)` is `1(o ↮ y)` (`connSet` is symmetric; `1(y ∈ K_o) ↔ Connects ω o y`). -/

/-- **The one-copy star moment at a single vertex**,
`E[1(o ↔ y) |K_o|^p] = ∫ 1{y ∈ K_o} · |K_o|^p`.  At `p = 3` this is the `q = 0` instance of
Lemma I.4.17, and it is *not* the summand of the Case-3 numerator. -/
noncomputable def starVert (π : Sym2 V → unitInterval) (o y : V) (p : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω o ^ p * (cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) y
    ∂(edgeMeasure π)

/-- **The excluded per-vertex moment** `E[1(o ↮ y) |K_o|^a |K_y|^b]`.  This is the subtracted
term of Lemma I.4.17 at `(a,b)`, and also exactly the summand of the Case-3 numerator at
`(a,b) = (1,2)`. -/
noncomputable def exclVert (π : Sym2 V → unitInterval) (o y : V) (a b : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω o ^ a *
    ((cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ b)
    ∂(edgeMeasure π)

/-- **The joint per-vertex moment** `E[|K_o|^a |K_y|^b]` (one copy: both clusters live in the same
configuration).  Its excess over the product of the moments is the covariance that separates the
star `E[1(o↔y)|K_o|^3]` from the product-minus-excluded numerator. -/
noncomputable def jointVert (π : Sym2 V → unitInterval) (o y : V) (a b : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω o ^ a * clusterVol ω y ^ b ∂(edgeMeasure π)

/-- **The product factor** `E|K_o|^a · E|K_y|^b` of Lemma I.4.17. -/
noncomputable def prodVert (π : Sym2 V → unitInterval) (o y : V) (a b : ℕ) : ℝ≥0∞ :=
  I420Case1.powMomentAt π a o * I420Case1.powMomentAt π b y

/-- **The `(a,b)` product gap**, i.e. the left-hand side of Lemma I.4.17 with the `ℝ≥0∞`
(truncated) subtraction.  This is *nonnegative* by the nonnegativity half of Lemma I.4.17. -/
noncomputable def gapVert (π : Sym2 V → unitInterval) (o y : V) (a b : ℕ) : ℝ≥0∞ :=
  prodVert π o y a b - exclVert π o y a b

/-- **The covariance of `|K_o|^a` and `|K_y|^b`** (in `ℝ≥0∞`, as a truncated subtraction of the
joint moment by the product factor).  It is `≥ 0` by Harris/FKG. -/
noncomputable def covVert (π : Sym2 V → unitInterval) (o y : V) (a b : ℕ) : ℝ≥0∞ :=
  jointVert π o y a b - prodVert π o y a b

/-! ## The replacement predicates at the source model

The following four predicates are the *targets* under audit.  They are stated at the cutoff law of
the source model `M` (radius `r`, basepoint `0`), with `χ = M.chiReal r = E_{β_c,r}|K|` and
`T^ℓ(0,y) = I418C.polyK (M.cutTwoPoint r) ℓ 0 y` the `ℓ`-fold power of the cutoff two-point
function.  Constants are `r`-independent.  Each is a statement of the source's own shape; none is
assumed to hold anywhere. -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **The per-vertex `q = 0` star target** (`p = 3`): `E[|K_0|³ 1(y∈K_0)] ≤ C₃T³χ⁴ + C₄T⁴χ³`.
Production's `HasPerVertexTwoTermHgap`, restated here only so that this module is self-contained
for the audit; it is *proved false* at `y = 0` (`not_hasPerVertexTwoTermHgap`). -/
def HasStarTwoTerm (C3 C4 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3

/-- **The additive repair** of the star target: the two-term bound plus the extra term
`C₅ · T(0,y) · χ⁵`.  At the diagonal `T(0,0) = 1` this reads `C₅ χ⁵`, which is the size of
`E|K|³` in Case 3; it is the *cheapest* additive power of `χ` that can survive the diagonal
(`Sharp.lean`: every `χ^β` with `β < 5` fails). -/
def HasAdditiveStar (C3 C4 C5 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3 +
        C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5

/-- **The general power additive repair**: the two-term bound plus
`C₅ · (T(0,y))^k · χ^β`.  `HasAdditiveStar` is the case `k = 1`, `β = 5`. -/
def HasPowerAdditiveStar (C3 C4 C5 : ℝ) (k : ℕ) (β : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3 +
        C5 * (M.cutTwoPoint r (0 : M.V) y) ^ k * M.chiReal r ^ β

/-- **The far-region repair**: the two-term bound only outside the `ρ`-ball around the origin.
This is the shape that the Harris obstruction actually permits
(`T(0,y) ≤ (C₃+C₄)∇/(Kχ)` is necessary at every vertex where the two-term bound holds). -/
def HasFarStar (C3 C4 : ℝ) (ρ : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V, ρ < M.S.dist 0 y →
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3

/-- **The product-gap target**: the per-vertex *Case-3 numerator* `N_y` (not the star) bounded by
the two-term diagram shape.  This is the object the paper's Lemma I.4.17 at `(p,q) = (1,2)` — or,
equivalently, at `(2,1)` with the pair `(0,y)` reversed — actually bounds.  It is *not* refuted at
the diagonal: there `N_0 = χ·E|K|²`. -/
def HasProductGap (C3 C4 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    (gapVert (M.cutProb r) (0 : M.V) y 1 2).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3

/-- **The covariance bound** that the additive repair of the star actually needs: a
positive-association upper bound on the joint moment
`E[|K_0| |K_y|²] ≤ E|K_0| E|K_y|² + C₅ T(0,y) χ⁵`, written in the equivalent covariance form
`Cov(|K_0|,|K_y|²) ≤ C₅ T(0,y) χ⁵`.  `Sharp.lean` proves that the product-gap target together
with this covariance bound *implies* the additive star target, and that the constant `C₅` must be
at least the third-moment coefficient `(2·3−3)!! = 3` read off Proposition I.4.20. -/
def HasCovBound (C5 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    (covVert (M.cutProb r) (0 : M.V) y 1 2).toReal ≤
      C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5

end SourceModelData

end QZeroRepairAudit
end PercLib.CriticalLRP
