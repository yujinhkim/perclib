/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The quadratic Russo flip calculus at `p = 2`

Swarm `smwv9oxuv`, member `m2`, direction `d2` (native quadratic pivotal-flux API).

The paper's formula (`RussoInf/FluxBase.lean` header, Hutchcroft, *Critical long-range
percolation I*, Lemma I.4.1) is

  `∂/∂r E_{β,r} |K|^p = β|J'(r)| ∑_{x∈K} ∑_{y ∈ B_r(x)} 1(y ∉ K) ((|K| + |K_y|)^p − |K|^p)`.

Every landed piece of the `p = 1` machinery acts on the **linear** flip difference
`flipDiff g e ω = g (forceOn {e} {e} ω) - g (forceOn {e} ∅ ω)`
(`RussoInf/FluxBase`, `RussoInf/SpatialDominated`, `RussoExcluded/Main`), which is additive
(`flipDiff_finsetSum`) but for which production has **no product rule**.  The `p = 2` moment
`|K|²` is not a linear functional of the cluster, so the linear machinery cannot be applied to it
without a second-order calculus.

This file supplies that calculus, in the production API and with no new definitions:

* `flipDiff_mul`, `flipDiff_mul_off` — the **product rule** for `flipDiff`: for arbitrary
  `f g : Config V → ℝ`,
  `flipDiff (f · g) e ω = Δf · g_off + f_off · Δg + Δf · Δg`
  with `Δf = flipDiff f e ω` and `·_off` evaluated at the configuration with `e` closed;
* `flipDiff_sq`, `flipDiff_sq_eq_increment` — the `p = 2` instance,
  `Δ(g²) = 2 g_off Δg + (Δg)² = (g_off + Δg)² − g_off²`, i.e. literally
  `((|K| + |K_y|)² − |K|²)` once `Δg = |K_y|`; the coefficient `2` and the squared term are
  *derived* from the flip calculus, not assumed;
* `flipDiff_sq_nonneg` — the `p = 2` increment of a nonnegative functional that only grows under
  the flip is nonnegative (the sign behind monotonicity of the `p = 2` cutoff moment);
* `abs_flipDiff_mul_le`, `abs_flipDiff_sq_le` — the **quantitative bridge**: a quadratic flip
  difference is dominated by the linear one it is built from,
  `|Δ(g²)| ≤ 4 m |Δg|` whenever `|g| ≤ m`, and `|Δ(f g)| ≤ 4 m_f m_g`;
* `flipDiff_mul_eq_zero_of_notMem_touchSet`, `abs_flipDiff_sq_le_touch`,
  `abs_flipDiff_sq_sMomentTrunc_le` — locality and the truncated `p = 2` pivotal bound
  `|Δ((sMomentTrunc q o A)²)| ≤ 8 (∑_{x∈A}|q x|)² · 1(e ∈ touchSet · o)`, the exact `p = 2`
  companion of the landed linear `abs_flipDiff_sMomentTrunc_singleton_le`;
* `lintegral_abs_flipDiff_sq_le` — the monotone-integral (`ℝ≥0∞`) form of the bridge: the
  quadratic pivotal mass is dominated by the linear pivotal mass, with no integrability input;
* `p2_increment_real_finset_sum`, `p2_increment_card_ennreal` — the `|K|`-edge multiplicity:
  summing the `p = 2` increment over the `|K|` vertices `x ∈ K` multiplies `2|K||K_y| + |K_y|²`
  by `|K|`, producing exactly the two weights `|K|²` and `|K|` of the source's excluded terms
  `exclMassSqLin = E[|K|² ∑_y 1(y∉K)|K_y|]` and `exclMassQuad = E[|K| ∑_y 1(y∉K)|K_y|²]`
  (`PivotFlux.p2RHS = exclMassQuad + 2 · exclMassSqLin`).

## What is *not* claimed

Nothing here differentiates a cutoff moment in the radius, and nothing here asserts or implies the
off-corner identity `∂_r E|K|² = β|J'(r)| · p2RHS`.  Proved is the second-order *flip* calculus and
the domination of the quadratic flux by the linear one; the `r`-derivative still needs the
edge-sum/radius interchange, and an identity for the right-hand side alone never implies a
derivative statement.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.RussoInf.FluxBase
public import PercLib.CriticalLRP.RussoInf.SpatialExchange
public import PercLib.CriticalLRP.RussoInf.Geometry
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Product rule, second-order increment and domination for the Russo flip difference

`flipDiff` is the Russo flip difference of production, the summand of the pivotal flux.  The
results below are the second-order (product/square) part of the calculus it supports.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-! ## 1. The product rule for the flip difference -/

/-- **Product rule for the Russo flip difference.**  The change of a product under flipping one
edge is the two first-order changes plus the second-order cross term.

This is the missing second-order ingredient of the `p = 1` machinery: `flipDiff` is additive
(`flipDiff_finsetSum`) but production has no product rule, which is exactly why a quadratic cluster
functional `|K|²` is not covered by the landed linear flux estimates. -/
theorem flipDiff_mul (f g : Config V → ℝ) (e : Sym2 V) (ω : Config V) :
    flipDiff (fun ω => f ω * g ω) e ω
      = flipDiff f e ω * g (forceOn {e} {e} ω) + f (forceOn {e} ∅ ω) * flipDiff g e ω := by
  unfold flipDiff
  ring

/-- **Product rule, closed form.**  Every factor is evaluated before the flip except the
increments, which makes the second-order structure visible:
`Δ(f g) = Δf · g + f · Δg + Δf · Δg` at the closed configuration. -/
theorem flipDiff_mul_off (f g : Config V → ℝ) (e : Sym2 V) (ω : Config V) :
    flipDiff (fun ω => f ω * g ω) e ω
      = flipDiff f e ω * g (forceOn {e} ∅ ω) + f (forceOn {e} ∅ ω) * flipDiff g e ω
        + flipDiff f e ω * flipDiff g e ω := by
  rw [flipDiff_mul]
  unfold flipDiff
  ring

/-! ## 2. The `p = 2` second-order increment -/

/-- **The `p = 2` flip increment.**  For any `g`, the change of `g²` under a flip is
`2 · g_off · Δg + (Δg)²`.  This is the identity behind the source's
`((|K| + |K_y|)² − |K|²) = 2|K||K_y| + |K_y|²`: both the coefficient `2` and the squared term are
consequences of the flip calculus. -/
theorem flipDiff_sq (g : Config V → ℝ) (e : Sym2 V) (ω : Config V) :
    flipDiff (fun ω => g ω ^ 2) e ω
      = 2 * g (forceOn {e} ∅ ω) * flipDiff g e ω + flipDiff g e ω ^ 2 := by
  unfold flipDiff
  ring

/-- **The `p = 2` increment in the source's shape**: literally `(a + Δ)² − a²` with `a = g` at the
closed configuration and `Δ = flipDiff g e ω`. -/
theorem flipDiff_sq_eq_increment (g : Config V → ℝ) (e : Sym2 V) (ω : Config V) :
    flipDiff (fun ω => g ω ^ 2) e ω
      = (g (forceOn {e} ∅ ω) + flipDiff g e ω) ^ 2 - g (forceOn {e} ∅ ω) ^ 2 := by
  rw [flipDiff_sq]
  ring

/-- The `p = 2` increment is nonnegative for a nonnegative functional that only grows under the
flip.  This is the sign that makes the `p = 2` cutoff moment monotone in the cutoff parameter. -/
theorem flipDiff_sq_nonneg {g : Config V → ℝ} (hg : ∀ ω, 0 ≤ g ω) {e : Sym2 V} {ω : Config V}
    (hmono : 0 ≤ flipDiff g e ω) : 0 ≤ flipDiff (fun ω => g ω ^ 2) e ω := by
  rw [flipDiff_sq]
  have h1 : 0 ≤ 2 * g (forceOn {e} ∅ ω) * flipDiff g e ω :=
    mul_nonneg (mul_nonneg (by norm_num) (hg _)) hmono
  have h2 : 0 ≤ flipDiff g e ω ^ 2 := sq_nonneg _
  linarith

/-! ## 3. Domination of the quadratic flux by the linear flux -/

/-- **The quadratic flip difference is dominated by the linear one.**  If `|g| ≤ m` pointwise then
`|Δ(g²)| ≤ 4 m |Δg|`: the cross term `2 g_off Δg` is bounded by `2 m |Δg|` and the second-order
term `(Δg)²` by `2 m |Δg|` through `|Δg| ≤ 2 m`. -/
theorem abs_flipDiff_sq_le [Countable V] {g : Config V → ℝ} {m : ℝ}
    (hbound : ∀ ω, |g ω| ≤ m) (e : Sym2 V) (ω : Config V) :
    |flipDiff (fun ω => g ω ^ 2) e ω| ≤ 4 * m * |flipDiff g e ω| := by
  rw [flipDiff_sq]
  set a := g (forceOn {e} ∅ ω) with ha
  set Δ := flipDiff g e ω with hΔ
  have ha' : |a| ≤ m := by simpa [ha] using hbound (forceOn {e} ∅ ω)
  have hΔ' : |Δ| ≤ 2 * m := by
    simpa [hΔ] using abs_flipDiff_le_sup hbound e ω
  have hinner : |2 * a + Δ| ≤ 4 * m := by
    have h2 : |2 * a| = 2 * |a| := by rw [abs_mul]; norm_num
    have h3 : |2 * a + Δ| ≤ |2 * a| + |Δ| := abs_add_le _ _
    linarith
  rw [show 2 * a * Δ + Δ ^ 2 = Δ * (2 * a + Δ) by ring, abs_mul]
  have hΔ0 : 0 ≤ |Δ| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hinner hΔ0]

/-- **The product flip difference is bounded by the two sup norms.** -/
theorem abs_flipDiff_mul_le [Countable V] {f g : Config V → ℝ} {mf mg : ℝ} (hmf : 0 ≤ mf)
    (hf : ∀ ω, |f ω| ≤ mf) (hg : ∀ ω, |g ω| ≤ mg) (e : Sym2 V) (ω : Config V) :
    |flipDiff (fun ω => f ω * g ω) e ω| ≤ 4 * mf * mg := by
  have hmg : 0 ≤ mg := (abs_nonneg (g ω)).trans (hg ω)
  rw [flipDiff_mul]
  have h1 : |flipDiff f e ω| ≤ 2 * mf := abs_flipDiff_le_sup hf e ω
  have h2 : |flipDiff g e ω| ≤ 2 * mg := abs_flipDiff_le_sup hg e ω
  have h3 : |g (forceOn {e} {e} ω)| ≤ mg := hg _
  have h4 : |f (forceOn {e} ∅ ω)| ≤ mf := hf _
  calc |flipDiff f e ω * g (forceOn {e} {e} ω) + f (forceOn {e} ∅ ω) * flipDiff g e ω|
      ≤ |flipDiff f e ω * g (forceOn {e} {e} ω)|
          + |f (forceOn {e} ∅ ω) * flipDiff g e ω| := abs_add_le _ _
    _ = |flipDiff f e ω| * |g (forceOn {e} {e} ω)|
          + |f (forceOn {e} ∅ ω)| * |flipDiff g e ω| := by rw [abs_mul, abs_mul]
    _ ≤ 2 * mf * mg + mf * (2 * mg) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul h1 h3 (abs_nonneg _) (by linarith)
        · exact mul_le_mul h4 h2 (abs_nonneg _) (by linarith)
    _ = 4 * mf * mg := by ring

/-! ## 4. Locality: the quadratic flux vanishes off the touching set -/

/-- The `p = 2` flux of a product of cluster functionals is local: it vanishes on edges that do not
touch the cluster of `o`.  This is the second-order companion of `flipDiff_eq_zero` and is what
makes the quadratic pivotal sum an edge sum over the touching set. -/
theorem flipDiff_mul_eq_zero_of_notMem_touchSet [Countable V] {o : V} {f g : Config V → ℝ}
    (hf : ∀ ω η : Config V, cluster ω o = cluster η o → f ω = f η)
    (hg : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    {e : Sym2 V} {ω : Config V} (h : e ∉ touchSet ω o) :
    flipDiff (fun ω => f ω * g ω) e ω = 0 := by
  refine flipDiff_eq_zero (o := o) (fun ω η hc => ?_) h
  rw [hf ω η hc, hg ω η hc]

/-- **The `p = 2` locality-and-bound statement.**  If `|g| ≤ m` and `g` is a functional of the
cluster of `o`, then the quadratic flip difference is bounded by `8 m²` times the indicator of the
touching event — the exact `p = 2` companion of the landed linear `abs_flipDiff_le`. -/
theorem abs_flipDiff_sq_le_touch [Countable V] {o : V} {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hbound : ∀ ω, |g ω| ≤ m)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (e : Sym2 V) (ω : Config V) :
    |flipDiff (fun ω => g ω ^ 2) e ω| ≤ 8 * m ^ 2 * (if e ∈ touchSet ω o then 1 else 0) := by
  have hsq := abs_flipDiff_sq_le hbound e ω
  have hlin : |flipDiff g e ω| ≤ 2 * m * (if e ∈ touchSet ω o then 1 else 0) :=
    abs_flipDiff_le hm hbound hdep e ω
  refine hsq.trans ?_
  set p := (if e ∈ touchSet ω o then (1 : ℝ) else 0) with hp
  have hp0 : 0 ≤ p := by rw [hp]; split <;> norm_num
  have hstep : 4 * m * |flipDiff g e ω| ≤ 4 * m * (2 * m * p) :=
    mul_le_mul (le_refl _) hlin (abs_nonneg _) (by linarith)
  have hfin : 4 * m * (2 * m * p) = 8 * m ^ 2 * p := by ring
  exact hstep.trans hfin.le

/-- **The truncated `p = 2` pivotal bound.**  For the truncated spatial moment
`sMomentTrunc q o A ω = ∑_{x ∈ A} q x · 1(x ∈ K_o ω)` of production, the quadratic flip difference
is bounded by `8 (∑_{x∈A}|q x|)²` on the touching set.  This is the `p = 2` analogue of
`abs_flipDiff_sMomentTrunc_singleton_le`, whose constant is `2 · max m 0` per singleton. -/
theorem abs_flipDiff_sq_sMomentTrunc_le [Countable V] (q : V → ℝ) (o : V) (A : Finset V) (e : Sym2 V)
    (ω : Config V) :
    |flipDiff (fun ω => sMomentTrunc q o A ω ^ 2) e ω|
      ≤ 8 * (∑ x ∈ A, |q x|) ^ 2 * (if e ∈ touchSet ω o then 1 else 0) :=
  abs_flipDiff_sq_le_touch (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (abs_sMomentTrunc_le q o A) (sMomentTrunc_dep q o A) e ω

/-! ## 5. The monotone-integral form of the bridge -/

/-- **The quadratic pivotal mass is dominated by the linear one.**  In `ℝ≥0∞` form this needs no
integrability hypothesis: the `lintegral` of the absolute quadratic flip difference is at most
`4m` times the `lintegral` of the absolute linear one.  This is the form in which the landed
summability/finiteness arguments for the `p = 1` pivotal mass transfer to `p = 2`. -/
theorem lintegral_abs_flipDiff_sq_le [Countable V] (μ : Measure (Config V)) {g : Config V → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hbound : ∀ ω, |g ω| ≤ m) (e : Sym2 V) :
    ∫⁻ ω, ENNReal.ofReal |flipDiff (fun ω => g ω ^ 2) e ω| ∂μ
      ≤ ENNReal.ofReal (4 * m) * ∫⁻ ω, ENNReal.ofReal |flipDiff g e ω| ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * m)]
  exact ENNReal.ofReal_le_ofReal (abs_flipDiff_sq_le hbound e ω)

/-- **The `p = 2` pivot bound.**  The absolute pivotal flux of the *square* of a bounded functional
of the cluster of `o` is at most `8 m²` times the probability that `e` touches the cluster.

This is the exact `p = 2` companion of the landed `abs_pivotalFlux_le`, whose constant is `2 m`.
It has the same shape — a constant times the touching probability — so every landed edge-sum
argument (incident degree bound, touch-set sums, radial envelopes) applies to the quadratic flux
verbatim, with `8 m²` in place of `2 m` and no new analytic input. -/
theorem abs_pivotalFlux_sq_le [Countable V] {o : V} (μ : Measure (Config V))
    [IsProbabilityMeasure μ] {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η) (e : Sym2 V) :
    |pivotalFlux μ (fun ω => g ω ^ 2) e| ≤ 8 * m ^ 2 * μ.real {ω : Config V | e ∈ touchSet ω o} := by
  classical
  set s : Set (Config V) := {ω : Config V | e ∈ touchSet ω o} with hs_def
  have hs : MeasurableSet s := measurableSet_touchSet_mem e
  have hmeas2 : Measurable fun ω => g ω ^ 2 := by fun_prop
  have hmeasf : Measurable (flipDiff (fun ω => g ω ^ 2) e) := by
    unfold flipDiff
    exact (hmeas2.comp (measurable_forceOn _ _)).sub (hmeas2.comp (measurable_forceOn _ _))
  have hpt : ∀ ω, ‖flipDiff (fun ω => g ω ^ 2) e ω‖
      ≤ (8 * m ^ 2) * (s.indicator (fun _ => (1 : ℝ)) ω) := by
    intro ω
    have hif : (if e ∈ touchSet ω o then (1 : ℝ) else 0)
        = s.indicator (fun _ => (1 : ℝ)) ω := by
      by_cases hmem : e ∈ touchSet ω o
      · have hmem' : ω ∈ s := by rw [hs_def]; exact hmem
        rw [ite_eq_left hmem, Set.indicator_of_mem hmem']
      · have hmem' : ω ∉ s := by rw [hs_def]; exact hmem
        rw [ite_eq_right hmem, Set.indicator_of_notMem hmem']
    rw [Real.norm_eq_abs, ← hif]
    exact abs_flipDiff_sq_le_touch hm hbound hdep e ω
  have hind : Integrable (fun ω => (s.indicator (fun _ => (1 : ℝ)) ω)) μ := by
    refine Integrable.of_bound (Measurable.aestronglyMeasurable ?_) 1 ?_
    · fun_prop
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      by_cases hmem : ω ∈ s <;> simp [hmem]
  have hInt : Integrable (fun ω => (8 * m ^ 2) * (s.indicator (fun _ => (1 : ℝ)) ω)) μ :=
    hind.const_mul _
  calc |pivotalFlux μ (fun ω => g ω ^ 2) e|
      = |∫ ω, flipDiff (fun ω => g ω ^ 2) e ω ∂μ| := rfl
    _ ≤ ∫ ω, ‖flipDiff (fun ω => g ω ^ 2) e ω‖ ∂μ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun ω => flipDiff (fun ω => g ω ^ 2) e ω) (μ := μ))
    _ ≤ ∫ ω, (8 * m ^ 2) * (s.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hInt
          (Eventually.of_forall hpt)
    _ = (8 * m ^ 2) * μ.real s := by
        rw [integral_const_mul,
          show ∫ a, s.indicator (fun _ => (1 : ℝ)) a ∂μ = μ.real s from
            integral_indicator_one hs]

/-- **The `p = 2` pivotal bound for the truncated spatial moment**, with no free constant: the
truncation bound `m = ∑_{x∈A}|q x|` of the landed linear theory.  This is the per-edge weight that
the edge-sum of `p = 2` can be summed with. -/
theorem abs_pivotalFlux_sMomentTrunc_sq_le [Countable V] (μ : Measure (Config V))
    [IsProbabilityMeasure μ] (q : V → ℝ) (o : V) (A : Finset V) (e : Sym2 V) :
    |pivotalFlux μ (fun ω => sMomentTrunc q o A ω ^ 2) e|
      ≤ 8 * (∑ x ∈ A, |q x|) ^ 2 * μ.real {ω : Config V | e ∈ touchSet ω o} :=
  abs_pivotalFlux_sq_le μ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (abs_sMomentTrunc_le q o A) (measurable_sMomentTrunc q o A) (sMomentTrunc_dep q o A) e

/-! ## 6. The `|K|`-edge multiplicity: from the increment to the source's two weights -/

/-- The scalar `p = 2` increment `(a + b)² − a² = 2ab + b²`. -/
theorem p2_increment_real (a b : ℝ) : (a + b) ^ 2 - a ^ 2 = 2 * a * b + b ^ 2 := by ring

/-- **The `|K|`-edge multiplicity.**  Each of the `|K|` vertices `x` of the cluster contributes the
same second-order increment `2|K||K_y| + |K_y|²`, so summing over `x ∈ K` multiplies it by `|K|`:
`2|K||K_y| + |K_y|² ↦ 2|K|²|K_y| + |K||K_y|²`, the two weights `|K|²` and `|K|` of the source's
excluded terms. -/
theorem p2_increment_real_finset_sum {ι : Type*} (κ : Finset ι) (a b : ℝ) :
    (∑ _x ∈ κ, ((a + b) ^ 2 - a ^ 2)) = (κ.card : ℝ) * (2 * a * b + b ^ 2) := by
  rw [Finset.sum_const, nsmul_eq_mul, p2_increment_real]

/-- The `p = 2` binomial identity in `ℝ≥0∞`, where the cluster volume `clusterVol` lives. -/
theorem add_sq_ennreal (a b : ℝ≥0∞) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

/-- The `|K|`-edge multiplicity in `ℝ≥0∞` form, for the extended cluster volumes. -/
theorem p2_increment_card_ennreal {ι : Type*} (κ : Finset ι) (a b : ℝ≥0∞) :
    (∑ _x ∈ κ, (a + b) ^ 2) = (κ.card : ℝ≥0∞) * (a ^ 2 + 2 * a * b + b ^ 2) := by
  rw [Finset.sum_const, nsmul_eq_mul, add_sq_ennreal]

/-! ## 7. The flux-level second-order decomposition and its summability

`pivotalFlux` is the `μ`-mean of `flipDiff`, so the product and square rules integrate to the exact
decomposition of the `p = 2` pivotal flux into a first-order (bilinear) part and a diagonal part,
and the per-edge bound of §5 turns into summability of the quadratic pivotal weight series as soon
as the linear one is summable. -/

/-- **Monotonicity of the `p = 2` increment in a monotone pair.**  If `0 ≤ g ≤ h` pointwise and the
increments are ordered (`0 ≤ Δg ≤ Δh`), then the `p = 2` increments are ordered.  This is the
step that lets a monotone exhaustion of the cluster volume (`sMomentTrunc` along `A ↑ univ`) pass
to the quadratic pivotal mass by monotone convergence. -/
theorem flipDiff_sq_mono {g h : Config V → ℝ} (hg : ∀ ω, 0 ≤ g ω) (hh : ∀ ω, 0 ≤ h ω)
    (hgh : ∀ ω, g ω ≤ h ω) {e : Sym2 V} {ω : Config V}
    (hΔgh : flipDiff g e ω ≤ flipDiff h e ω) (hΔg : 0 ≤ flipDiff g e ω) :
    flipDiff (fun ω => g ω ^ 2) e ω ≤ flipDiff (fun ω => h ω ^ 2) e ω := by
  rw [flipDiff_sq, flipDiff_sq]
  have ha : 0 ≤ g (forceOn {e} ∅ ω) := hg _
  have hab : g (forceOn {e} ∅ ω) ≤ h (forceOn {e} ∅ ω) := hgh _
  have hb : 0 ≤ h (forceOn {e} ∅ ω) := hh _
  have h1 : 2 * g (forceOn {e} ∅ ω) * flipDiff g e ω
      ≤ 2 * h (forceOn {e} ∅ ω) * flipDiff h e ω := by
    have hstep : 2 * g (forceOn {e} ∅ ω) * flipDiff g e ω
        ≤ 2 * h (forceOn {e} ∅ ω) * flipDiff g e ω := by
      have : (2 * g (forceOn {e} ∅ ω)) ≤ (2 * h (forceOn {e} ∅ ω)) := by linarith
      exact mul_le_mul_of_nonneg_right this hΔg
    have hstep2 : 2 * h (forceOn {e} ∅ ω) * flipDiff g e ω
        ≤ 2 * h (forceOn {e} ∅ ω) * flipDiff h e ω :=
      mul_le_mul_of_nonneg_left hΔgh (by linarith)
    exact hstep.trans hstep2
  have h2 : flipDiff g e ω ^ 2 ≤ flipDiff h e ω ^ 2 := by
    have := hΔgh
    nlinarith [hΔg, sq_nonneg (flipDiff g e ω), sq_nonneg (flipDiff h e ω)]
  linarith

/-- **Exact bilinear decomposition of the pivotal flux of a product.**  The flux of `f · g` is the
flux of `f` read against the flipped value of `g`, plus the closed value of `f` read against the
flux of `g`. -/
theorem pivotalFlux_mul [Countable V] (μ : Measure (Config V)) (f g : Config V → ℝ) (e : Sym2 V)
    (h1 : Integrable (fun ω => flipDiff f e ω * g (forceOn {e} {e} ω)) μ)
    (h2 : Integrable (fun ω => f (forceOn {e} ∅ ω) * flipDiff g e ω) μ) :
    pivotalFlux μ (fun ω => f ω * g ω) e
      = (∫ ω, flipDiff f e ω * g (forceOn {e} {e} ω) ∂μ)
        + ∫ ω, f (forceOn {e} ∅ ω) * flipDiff g e ω ∂μ := by
  unfold pivotalFlux
  rw [show (fun ω => flipDiff (fun ω => f ω * g ω) e ω)
      = fun ω => flipDiff f e ω * g (forceOn {e} {e} ω)
          + f (forceOn {e} ∅ ω) * flipDiff g e ω from funext fun ω => flipDiff_mul f g e ω]
  rw [integral_add h1 h2]

/-- **The exact `p = 2` pivotal-flux identity**: the flux of `g²` is twice the bilinear flux plus
the flux of the squared increment `(Δg)²`.  This is the second-order structure of the source's
`((|K| + |K_y|)² − |K|²) = 2|K||K_y| + |K_y|²` at the level of the pivotal flux: no linear
functional of the cluster is used, and no bound on `g` is assumed. -/
theorem pivotalFlux_sq [Countable V] (μ : Measure (Config V)) (g : Config V → ℝ) (e : Sym2 V)
    (h1 : Integrable (fun ω => g (forceOn {e} ∅ ω) * flipDiff g e ω) μ)
    (h2 : Integrable (fun ω => flipDiff g e ω ^ 2) μ) :
    pivotalFlux μ (fun ω => g ω ^ 2) e
      = 2 * (∫ ω, g (forceOn {e} ∅ ω) * flipDiff g e ω ∂μ)
        + ∫ ω, flipDiff g e ω ^ 2 ∂μ := by
  unfold pivotalFlux
  rw [show (fun ω => flipDiff (fun ω => g ω ^ 2) e ω)
      = fun ω => 2 * (g (forceOn {e} ∅ ω) * flipDiff g e ω) + flipDiff g e ω ^ 2 from
        funext fun ω => by rw [flipDiff_sq]; ring]
  rw [integral_add (h1.const_mul 2) h2, integral_const_mul]

/-- **The `p = 2` pivotal-flux identity for the cutoff cluster volume.**  The flux of
`|K_o|²` is twice the bilinear term `〈|K_o|, Δ|K_o|〉` plus the diagonal term of the squared
increment.  Once the merge identity `Δ|K_o| = |K_y|` at a pivotal edge `e` is supplied, this reads
exactly as the source's `2|K||K_y| + |K_y|²` — the two terms whose `|K|`-weighted expectations are
`exclMassSqLin` and `exclMassQuad` (`PivotFlux.p2RHS`). -/
theorem pivotalFlux_clusterVol_toReal_sq [Countable V] (μ : Measure (Config V)) (o : V)
    (e : Sym2 V)
    (h1 : Integrable (fun ω => (clusterVol (forceOn {e} ∅ ω) o).toReal
      * flipDiff (fun ω => (clusterVol ω o).toReal) e ω) μ)
    (h2 : Integrable (fun ω => flipDiff (fun ω => (clusterVol ω o).toReal) e ω ^ 2) μ) :
    pivotalFlux μ (fun ω => (clusterVol ω o).toReal ^ 2) e
      = 2 * (∫ ω, (clusterVol (forceOn {e} ∅ ω) o).toReal
          * flipDiff (fun ω => (clusterVol ω o).toReal) e ω ∂μ)
        + ∫ ω, flipDiff (fun ω => (clusterVol ω o).toReal) e ω ^ 2 ∂μ :=
  pivotalFlux_sq μ (fun ω => (clusterVol ω o).toReal) e h1 h2

/-- **Summability of the quadratic pivotal weight series from the linear one.**  If the `p = 1`
weight series `∑_e |c e| · P(e touches K_o)` is summable — the shape produced by the landed
degree/envelope arguments (`sMomentWeight`, `m1_summable_env`, `FiniteVolume.sum_touchSet_le`) —
then so is the `p = 2` pivotal weight series, with the *same* touching-probability series and the
constant `8 m²` coming from the truncation bound.  This is the transfer that makes the `p = 2`
pivotal mass finite without any new analytic input. -/
theorem summable_abs_pivotalFlux_sq [Countable V] {o : V} (μ : Measure (Config V))
    [IsProbabilityMeasure μ] {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (c : Sym2 V → ℝ)
    (hW : Summable fun e : Sym2 V => |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}) :
    Summable fun e : Sym2 V => |c e| * |pivotalFlux μ (fun ω => g ω ^ 2) e| := by
  have hconst : (0 : ℝ) ≤ 8 * m ^ 2 := by positivity
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_) (hW.mul_left (8 * m ^ 2))
  calc |c e| * |pivotalFlux μ (fun ω => g ω ^ 2) e|
      ≤ |c e| * (8 * m ^ 2 * μ.real {ω : Config V | e ∈ touchSet ω o}) :=
        mul_le_mul_of_nonneg_left (abs_pivotalFlux_sq_le μ hm hbound hmeas hdep e) (abs_nonneg _)
    _ = (8 * m ^ 2) * (|c e| * μ.real {ω : Config V | e ∈ touchSet ω o}) := by ring

end PercLib.CriticalLRP
