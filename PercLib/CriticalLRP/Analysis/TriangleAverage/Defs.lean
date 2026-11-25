/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Uncut triangle-average definitions

Reviewed and integrated from Ultramath `smwtqkdul`, member `m2`, `C2.lean`,
based on revision `9afe8a172733efb434a2944a2ed97cfca4ad9bcf`. These definitions
are at the uncut critical law, not the actual finite-cutoff law required for
Case 3. Finite-moment and tail-decay premises remain with the consumer theorems.

Original development note:

Swarm `smwtqkdul`, member `m2`, direction C2 (registered as `d3`).

Source: Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.11, Lemma I.4.12 and the proof of Proposition I.4.2
(pp. 39-41).

The source's `E_{1,r}` is `VolumeMoments.cE1` at `b = |B_r|`:

  `E_{1,r} = (|B_r| (E|K|)^2 - E[|K| Σ_{y∈B_r} 1(y∉K)|K_y|]) / (|B_r| (E|K|)^2)`

(Lemma I.4.11's display).  The landed finite-moment form of Lemma I.4.11
(`I411.lemma_I_4_11_of_finite`) bounds it by

  `E_{1,r} ≤ |B_r|^{-1} Σ_{y ∈ B_r} ∇(0,y)`,  `∇(0,y) = Σ_a Σ_b τ(0,a) τ(a,b) τ(b,y)`.

What is proved here is the **normalized Cesàro average** statement: the ball
average of the triangle diagram vanishes, so `E_{1,r} → 0`.  This is strictly
weaker than the spatial supremum statement `∇_r → 0`, and it is *not* proved from
the stronger (and at `β_c` inapplicable) hypothesis that `∇(0,·)` is summable:
at criticality `Σ_y ∇(0,y) = (Σ_x τ(0,x))^3` carries the divergence of the
susceptibility, so the honest hypotheses are the two the source itself uses:

* **pointwise finiteness** (the triangle condition in sup form)
  `∇_0 = sup_x ∇(0,x) < ∞` — `nablaSup M (nabla M) 0 ≠ ⊤`; and
* **uniform tail decay** `∇_r → 0` — `Tendsto (nablaSup M (nabla M)) atTop (𝓝 0)`.

Main results.

* `tendsto_normalized_ballSum_toReal` (unconditional analysis, no percolation):
  `∇_0 < ∞` and `∇_r → 0` imply `r^{-d} Σ_{x ∈ B_r} f x → 0` for the configured
  lattice balls.  This is the source's two-scale split at `R = √r` — the landed
  `BallAverage.normalized_ballSum_le` — followed by the two limit facts
  `r^{-d/2} → 0` and `∇_{√r} → 0`.  It is the missing *limit* half of
  `Analysis/BallAverage` (which lands only logarithmic integrability and
  explicitly says nothing about `∇_r → 0`).
* `defect_le_normalized_ballSum`: Lemma I.4.11 at the configured model, in the
  exact shape `E_{1,r} ≤ |B_r|^{-1} Σ_{y ∈ B_r} ∇(0,y)`.
* `defect_upper_tendsto_zero_of_tail` gives only an eventual upper bound;
  `defect_posPart_tendsto_zero_of_tail` gives two-sided vanishing of the
  positive part, not a two-sided limit of the signed defect.
* `summable_kernel_cesaro_tendsto_zero`: the unconditional analytic half in the
  *summable-kernel* form (`∇(0,·)` summable `⇒` normalized averages vanish), which
  is the Case 2 mechanism `∇(0,x) ⪯ ‖x‖^{-d+6}` made abstract.  It needs no
  monotonicity, no translation invariance and no rate.

Residual gaps are named in `REPORT.md`; in particular the nonnegativity
`0 ≤ E_{1,r}` is not available at the uncut law from the landed layer (it is the
sign in the coupling identity behind Lemma I.4.12), and the composition inherits
the finiteness `χ(β_c) < ∞` carried by `lemma_I_4_11_of_finite`.
-/
module

public import PercLib.CriticalLRP.Analysis.BallAverage
public import PercLib.CriticalLRP.Analysis.Polygon.Model
public import PercLib.CriticalLRP.Correlation.I411.RealQuotient

/-! # Uncut triangle-average definitions at the configured critical law -/

set_option autoImplicit false

-- The `#print axioms` audit at the end of this file is required by the campaign
-- protocol; it is a command, so the Mathlib hash-command linter is switched off
-- for it here.  Nothing else in the file is excluded from the linter set.
set_option linter.hashCommand false

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal BigOperators Topology

namespace PercLib.CriticalLRP.TriangleAverage

open PercLib.CriticalLRP.I411
open PercLib.CriticalLRP.VolumeMoments
open PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

/-! ## The configured model's window, its triangle weight, and the defect

Only *window* objects are introduced; the percolation law, the two-point
function, the balls and `β_c` are the configured model's own. -/

/-- The lattice ball `B_r = {y : ‖y‖ ≤ r}` of the configured model, as a finset. -/
noncomputable def ballFinset (M : SourceModelData) (r : ℝ) : Finset M.V :=
  (BallAverage.ball_finite M r).toFinset

theorem ballFinset_card (M : SourceModelData) (r : ℝ) :
    (ballFinset M r).card = (M.ball r).ncard :=
  (Set.ncard_eq_toFinset_card (M.ball r) (BallAverage.ball_finite M r)).symm

/-- `Σ_{w} τ_{β_c}(0,w)`, the susceptibility in the source's `ℝ≥0∞` form. -/
noncomputable def suscept (M : SourceModelData) : ℝ≥0∞ :=
  ∑' w : M.V, twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 w

/-- **The open triangle `∇_{β_c}(0,y)`**, as the threefold convolution of the
critical two-point function (`∇(0,y) = Σ_a Σ_b τ(0,a) τ(a,b) τ(b,y)`,
paper, section I.4).  This is the weight whose lattice-ball average is the
source's error term. -/
noncomputable def nabla (M : SourceModelData) (y : M.V) : ℝ≥0∞ :=
  ∑' a : M.V, ∑' b : M.V,
    twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 a *
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit a b *
        twoPointFunction M.kernel M.kernel_nonneg M.betaCrit b y

/-- The total triangle mass `Σ_y ∇(0,y)`.  It is **not** a hypothesis of any limit
theorem below: at `β_c` it carries `χ(β_c)^3` (see `suscept_le_triMass` for the
Lean-checked half of that, and `REPORT.md` gap 5). -/
noncomputable def triMass (M : SourceModelData) : ℝ≥0∞ := ∑' y : M.V, nabla M y

/-- **The total triangle mass dominates the susceptibility**: `χ(β_c) ≤ Σ_y ∇(0,y)`.

The single pair `a = 0`, `b = y` of the double sum is
`τ(0,0)τ(0,y)τ(y,y) = τ(0,y)`, and the two-point function is `1` on the diagonal.
Consequently a finite total triangle mass *forces* `χ(β_c) < ∞`; since the campaign's
expected criticality is `χ(β_c) = ⊤` (`I42C.uncutFirstMoment_eq_top_of_rpow_lower`),
summability of `∇(0,·)` is not a usable hypothesis at `β_c`. -/
theorem suscept_le_triMass (M : SourceModelData) : suscept M ≤ triMass M := by
  refine ENNReal.tsum_le_tsum fun y => ?_
  have h1 : twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 0 = 1 :=
    twoPointFunction_self M.kernel M.kernel_nonneg M.betaCrit 0
  have h2 : twoPointFunction M.kernel M.kernel_nonneg M.betaCrit y y = 1 :=
    twoPointFunction_self M.kernel M.kernel_nonneg M.betaCrit y
  calc twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 y
      = twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 0 *
          twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 y *
            twoPointFunction M.kernel M.kernel_nonneg M.betaCrit y y := by
        rw [h1, h2, one_mul, mul_one]
    _ ≤ ∑' b : M.V, twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 0 *
          twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 b *
            twoPointFunction M.kernel M.kernel_nonneg M.betaCrit b y := by
        simpa using ENNReal.sum_le_tsum (s := ({y} : Finset M.V))
          (f := fun b : M.V => twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 0 *
            twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 b *
              twoPointFunction M.kernel M.kernel_nonneg M.betaCrit b y)
    _ ≤ ∑' a : M.V, ∑' b : M.V,
          twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 a *
            twoPointFunction M.kernel M.kernel_nonneg M.betaCrit a b *
              twoPointFunction M.kernel M.kernel_nonneg M.betaCrit b y := by
        simpa using ENNReal.sum_le_tsum (s := ({(0 : M.V)} : Finset M.V))
          (f := fun a : M.V => ∑' b : M.V,
            twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 a *
              twoPointFunction M.kernel M.kernel_nonneg M.betaCrit a b *
                twoPointFunction M.kernel M.kernel_nonneg M.betaCrit b y)

/-- `E|K|` at the critical law. -/
noncomputable def originMass (M : SourceModelData) : ℝ≥0∞ :=
  ∫⁻ ω : Config M.V, clusterVol ω 0 ∂(M.law M.betaCrit)

/-- `E[|K| Σ_{y ∈ B_r} |K_y|]`, the joint window moment of Lemma I.4.11. -/
noncomputable def winMoment (M : SourceModelData) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω : Config M.V, Percolation.cardFun (cluster ω 0) *
    ∑ y ∈ ballFinset M r, Percolation.cardFun (cluster ω y)
    ∂(M.law M.betaCrit)

/-- `E[|K ∩ B_r| |K|^2]`. -/
noncomputable def sameMoment (M : SourceModelData) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω : Config M.V,
    ((ballFinset M r).filter fun y => y ∈ cluster ω 0).card *
      (Percolation.cardFun (cluster ω 0) * Percolation.cardFun (cluster ω 0))
    ∂(M.law M.betaCrit)

/-- **The source defect `E_{1,r}`** at the configured model: the real quotient
`cE1` of the paper's three moments at the window `B_r`. -/
noncomputable def defect (M : SourceModelData) (r : ℝ) : ℝ :=
  cE1 (originMass M).toReal (winMoment M r).toReal (sameMoment M r).toReal
    (ballFinset M r).card


end PercLib.CriticalLRP.TriangleAverage
