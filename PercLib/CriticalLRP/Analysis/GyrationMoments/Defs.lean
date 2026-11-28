/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m2.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m2/Defs.lean`.
-/

/-
Member `m2` of swarm `smwzqts7r`, direction `d9`.

Source: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
§I.5.1 (radius of gyration, Proposition I.5.2) and §I.5.2 (full displacement
distribution).  The paper writes spatial moments as `E_{β_c,r}[Σ_{x ∈ K} f(x)]`
(e.g. `F r = E_{β_c,r}[Σ_{x∈K} ‹x,u›²]` in the proof of Lemma I.5.7) and evaluates
them through the two-point function.

Production (`Analysis/GyrationReduction.lean`) keeps the resulting ODE as the
abstract hypothesis `GyrationAsymptotic`; nothing at the model level identifies
that functional with the two-point function.  This file supplies the identity
layer, for every weight and every even displacement power:

* `lintegral_tsum_indicator_cluster` — the general Bernoulli-edge identity
  `∫⁻ Σ_y 1{y ∈ K_o} w y = Σ_y w y · P(o ↔ y)` for an arbitrary weight in `ℝ≥0∞`
  and an arbitrary edge law, with no finiteness assumption;
* `displacementMoment` and `displacementMoment_eq_tsum` — the paper's
  `E_{β_c,r}[Σ_{x∈K} ‹x,u›^{2p}]` at the normalized cutoff law, equal to
  `Σ_y ‹y,u›^{2p} τ_r(0,y)`, plus its `ℝ`-valued form;
* `cutMoment_one_eq_tsum`, `gyrationMoment` and `xi2sq_eq_tsum_ratio` — the
  cutoff first moment and the radius of gyration `ξ₂²(r)` as exact ratios of
  weighted two-point sums.

Nothing here asserts any asymptotics, any two-point estimate, or any part of
Proposition I.5.2 or Lemma I.5.7.  It is the identity layer such a proof has to
start from.

Overlap with production, stated explicitly: `Analysis/Cutoff/Defs.lean` already has
`SourceModelData.cutTwoPointE`, `SourceModelData.cutTwoPoint` (in `ℝ`) and
`SourceModelData.cutMassAt`, and `M.tsum_cutTwoPointE_eq_cutMassAt` is the
*constant-weight* row-sum identity.  The 0-rooted objects below are definitionally the
same (`cutTwoPointE_eq_production`, `cutTwoPoint_eq_production`); what is not in
production is the arbitrary-weight identity of §2 and its consequences in §4-§8.
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.Analysis.Cutoff.Defs
public import PercLib.CriticalLRP.RussoInf.SpatialExchange

/-! Exact displacement and gyration identities and one-sided cutoff bounds. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration.M2

/-! ## §1 The Euclidean pairing on `Fin d → ℝ` -/

/-- The Euclidean inner product of `Fin d → ℝ`, written as a finite sum so that no
inner-product-space structure is needed. -/
def dot {d : ℕ} (x u : Fin d → ℝ) : ℝ := ∑ i, x i * u i

theorem dot_comm {d : ℕ} (x u : Fin d → ℝ) : dot x u = dot u x :=
  Finset.sum_congr rfl fun i _ => mul_comm (x i) (u i)

theorem dot_self_nonneg {d : ℕ} (x : Fin d → ℝ) : 0 ≤ dot x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- Every even power of a real is nonnegative, in the shape `2 * p` used for the
even displacement moments `‹x,u›^{2p}`. -/
theorem pow_two_mul_nonneg {a : ℝ} (p : ℕ) : 0 ≤ a ^ (2 * p) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg a) p

/-! ## §2 The weighted cluster-sum identity for an arbitrary edge law -/

/-- Pointwise form: the indicator of the cluster of `o` is the indicator of the
connection event. -/
theorem indicator_cluster_apply {V : Type*} (ω : PercLib.Percolation.Bond.Config V)
    (o y : V) (w : V → ℝ≥0∞) :
    (PercLib.Percolation.Bond.cluster ω o).indicator w y
      = (PercLib.Percolation.Bond.conn o y).indicator (fun _ => w y) ω := by
  classical
  by_cases h : y ∈ PercLib.Percolation.Bond.cluster ω o
  · have h' : ω ∈ PercLib.Percolation.Bond.conn o y :=
      (PercLib.Percolation.Bond.mem_cluster_iff ω o y).mp h
    simp [h, h']
  · have h' : ω ∉ PercLib.Percolation.Bond.conn o y :=
      fun hc => h ((PercLib.Percolation.Bond.mem_cluster_iff ω o y).mpr hc)
    simp [h, h']

/-- **The weighted cluster-sum identity.**  For any Bernoulli edge law and any
weight `w : V → ℝ≥0∞`, the expectation of the weighted cluster sum is the weight
paired with the two-point function.  No finiteness assumption is used. -/
theorem lintegral_tsum_indicator_cluster {V : Type*} [Countable V]
    (q : Sym2 V → unitInterval) (o : V) (w : V → ℝ≥0∞) :
    ∫⁻ ω, ∑' y : V, (PercLib.Percolation.Bond.cluster ω o).indicator w y
        ∂(edgeMeasure q)
      = ∑' y : V, w y * edgeMeasure q (PercLib.Percolation.Bond.conn o y) := by
  have hterm : ∀ y : V,
      (fun ω => (PercLib.Percolation.Bond.cluster ω o).indicator w y)
        = (PercLib.Percolation.Bond.conn o y).indicator (fun _ => w y) :=
    fun y => funext fun ω => indicator_cluster_apply ω o y w
  have hmeas : ∀ y : V,
      AEMeasurable (fun ω => (PercLib.Percolation.Bond.cluster ω o).indicator w y)
        (edgeMeasure q) := by
    intro y
    rw [hterm y]
    exact (measurable_const.indicator
      (PercLib.Percolation.Bond.measurableSet_conn o y)).aemeasurable
  rw [lintegral_tsum hmeas]
  exact tsum_congr fun y => by
    rw [hterm y,
      lintegral_indicator_const (PercLib.Percolation.Bond.measurableSet_conn o y) (w y)]

/-! ## §3 The cutoff law as a Bernoulli edge law -/

/-- The cutoff law is the Bernoulli edge law of the truncated kernel. -/
theorem cutLaw_eq_edgeMeasure (M : SourceModelData) (r : ℝ) :
    M.cutLaw r
      = edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit) :=
  rfl

instance instIsProbabilityMeasureCutLaw (M : SourceModelData) (r : ℝ) :
    IsProbabilityMeasure (M.cutLaw r) :=
  inferInstanceAs (IsProbabilityMeasure
    (PercLib.Percolation.Bond.law
      (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)))

/-- The cutoff two-point function `τ_r(0,y) = P_{β_c,r}(0 ↔ y)` in `ℝ≥0∞`. -/
def cutTwoPointE (M : SourceModelData) (r : ℝ) (y : M.V) : ℝ≥0∞ :=
  M.cutLaw r (PercLib.Percolation.Bond.conn (0 : M.V) y)

/-- The same quantity in `ℝ`.  (Finiteness is `cutTwoPointE_ne_top`.) -/
def cutTwoPoint (M : SourceModelData) (r : ℝ) (y : M.V) : ℝ :=
  (cutTwoPointE M r y).toReal

theorem cutTwoPointE_ne_top (M : SourceModelData) (r : ℝ) (y : M.V) :
    cutTwoPointE M r y ≠ ⊤ :=
  measure_ne_top _ _

theorem cutTwoPoint_nonneg (M : SourceModelData) (r : ℝ) (y : M.V) :
    0 ≤ cutTwoPoint M r y :=
  ENNReal.toReal_nonneg

theorem cutTwoPoint_le_one (M : SourceModelData) (r : ℝ) (y : M.V) :
    cutTwoPoint M r y ≤ 1 := by
  have hle : cutTwoPointE M r y ≤ M.cutLaw r Set.univ :=
    measure_mono (Set.subset_univ _)
  rw [measure_univ] at hle
  have hm : cutTwoPoint M r y ≤ ((1 : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono (by simp) hle
  simpa using hm

theorem cutTwoPointE_eq_production (M : SourceModelData) (r : ℝ) (y : M.V) :
    cutTwoPointE M r y = M.cutTwoPointE r (0 : M.V) y :=
  rfl

theorem cutTwoPoint_eq_production (M : SourceModelData) (r : ℝ) (y : M.V) :
    cutTwoPoint M r y = M.cutTwoPoint r (0 : M.V) y :=
  rfl

/-! ## §4 The displacement moments at the normalized cutoff law -/

/-- The paper's `E_{β_c,r}[Σ_{x∈K} ‹x,u›^{2p}]`, written as a cluster sum over the
configuration.  This is `F` of the proof of Lemma I.5.7 at `p = 1` and the `2p`-th
displacement moment of §I.5.2 for general `p`. -/
def displacementMoment (M : SourceModelData) (p : ℕ) (r : ℝ) (u : Fin M.d → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' y : M.V, (PercLib.Percolation.Bond.cluster ω (0 : M.V)).indicator
    (fun z => ENNReal.ofReal ((dot (toVec z) u) ^ (2 * p))) y ∂(M.cutLaw r)

/-- **The pair-sum form of the displacement moment.**  The `2p`-th displacement
moment is the `2p`-th power of `‹·,u›` paired with the cutoff two-point function. -/
theorem displacementMoment_eq_tsum (M : SourceModelData) (p : ℕ) (r : ℝ)
    (u : Fin M.d → ℝ) :
    displacementMoment M p r u
      = ∑' y : M.V, ENNReal.ofReal ((dot (toVec y) u) ^ (2 * p)) * cutTwoPointE M r y := by
  have h := lintegral_tsum_indicator_cluster (V := M.V)
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit) (0 : M.V)
    (fun z => ENNReal.ofReal ((dot (toVec z) u) ^ (2 * p)))
  change (∫⁻ ω : PercLib.CriticalLRP.Config M.V, ∑' y : M.V,
      (PercLib.Percolation.Bond.cluster ω (0 : M.V)).indicator
        (fun z => ENNReal.ofReal ((dot (toVec z) u) ^ (2 * p))) y ∂(M.cutLaw r))
    = ∑' y : M.V, ENNReal.ofReal ((dot (toVec y) u) ^ (2 * p)) * cutTwoPointE M r y
  rw [cutLaw_eq_edgeMeasure M]
  simp only [cutTwoPointE]
  exact h

/-- **The displacement moment is production's infinite-volume spatial moment.**
`RussoInf/SpatialExchange` defines `spatialMomentENN q o ω = Σ'_x 1{x ∈ K_o(ω)}·q x` (the object
Lemma I.5.8 differentiates) and proves monotone convergence from its finite truncations, but
never evaluates its expectation.  The identification below is definitional, so item 2 evaluates
that expectation as a weighted two-point sum. -/
theorem displacementMoment_eq_spatialMomentENN (M : SourceModelData) (p : ℕ) (r : ℝ)
    (u : Fin M.d → ℝ) :
    displacementMoment M p r u
      = ∫⁻ ω, PercLib.CriticalLRP.spatialMomentENN
          (fun x : M.V => (dot (toVec x) u) ^ (2 * p)) (0 : M.V) ω ∂(M.cutLaw r) :=
  rfl

/-- The real-valued form: the displacement moment is the `ℝ`-valued weighted sum of
cutoff two-point functions. -/
theorem displacementMoment_toReal_eq_tsum (M : SourceModelData) (p : ℕ) (r : ℝ)
    (u : Fin M.d → ℝ) :
    (displacementMoment M p r u).toReal
      = ∑' y : M.V, (dot (toVec y) u) ^ (2 * p) * cutTwoPoint M r y := by
  rw [displacementMoment_eq_tsum M p r u, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun y => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_two_mul_nonneg p)]
    rfl
  · intro y
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (cutTwoPointE_ne_top M r y)

/-! ## §5 The first cutoff moment and the radius of gyration as two-point sums -/

/-- `E_{β_c,r}|K| = Σ_y P_{β_c,r}(0 ↔ y)`: the cutoff susceptibility is the total
mass of the cutoff two-point function. -/
theorem cutMoment_one_eq_tsum (M : SourceModelData) (r : ℝ) :
    M.cutMoment 1 r = ∑' y : M.V, cutTwoPointE M r y := by
  have h := lintegral_tsum_indicator_cluster (V := M.V)
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit) (0 : M.V)
    (fun _ => (1 : ℝ≥0∞))
  change (∫⁻ ω : PercLib.CriticalLRP.Config M.V, clusterVol ω (0 : M.V) ^ 1
      ∂(M.cutLaw r)) = ∑' y : M.V, cutTwoPointE M r y
  simp only [cutTwoPointE]
  rw [cutLaw_eq_edgeMeasure M]
  rw [show (∫⁻ ω : PercLib.CriticalLRP.Config M.V, clusterVol ω (0 : M.V) ^ 1
        ∂edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit))
      = ∫⁻ ω, ∑' y : M.V, (PercLib.Percolation.Bond.cluster ω (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y
        ∂edgeMeasure (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)
      from lintegral_congr fun ω => ?_]
  · simpa using h
  · rw [pow_one, clusterVol_eq_encard, tsum_indicator_eq_encard]

/-- At `p = 0` the displacement moment is the first cutoff moment: the identity
`E_{β_c,r}[Σ_{x∈K} 1] = E_{β_c,r}|K|`. -/
theorem displacementMoment_zero (M : SourceModelData) (r : ℝ) (u : Fin M.d → ℝ) :
    displacementMoment M 0 r u = M.cutMoment 1 r := by
  rw [displacementMoment_eq_tsum M 0 r u, cutMoment_one_eq_tsum M r]
  exact tsum_congr fun y => by simp

/-- The numerator `E_{β_c,r}[Σ_{x∈K} ‖x‖₂²]` of the radius of gyration. -/
def gyrationMoment (M : SourceModelData) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' y : M.V, (PercLib.Percolation.Bond.cluster ω (0 : M.V)).indicator
    (fun z => ENNReal.ofReal (dot (toVec z) (toVec z))) y ∂(M.cutLaw r)

theorem gyrationMoment_eq_tsum (M : SourceModelData) (r : ℝ) :
    gyrationMoment M r
      = ∑' y : M.V, ENNReal.ofReal (dot (toVec y) (toVec y)) * cutTwoPointE M r y := by
  have h := lintegral_tsum_indicator_cluster (V := M.V)
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit) (0 : M.V)
    (fun z => ENNReal.ofReal (dot (toVec z) (toVec z)))
  change (∫⁻ ω : PercLib.CriticalLRP.Config M.V, ∑' y : M.V,
      (PercLib.Percolation.Bond.cluster ω (0 : M.V)).indicator
        (fun z => ENNReal.ofReal (dot (toVec z) (toVec z))) y ∂(M.cutLaw r))
    = ∑' y : M.V, ENNReal.ofReal (dot (toVec y) (toVec y)) * cutTwoPointE M r y
  rw [cutLaw_eq_edgeMeasure M]
  simp only [cutTwoPointE]
  exact h

theorem gyrationMoment_toReal_eq_tsum (M : SourceModelData) (r : ℝ) :
    (gyrationMoment M r).toReal
      = ∑' y : M.V, dot (toVec y) (toVec y) * cutTwoPoint M r y := by
  rw [gyrationMoment_eq_tsum M r, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun y => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (dot_self_nonneg (toVec y))]
    rfl
  · intro y
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (cutTwoPointE_ne_top M r y)

/-- The paper's radius of gyration `ξ₂²(r)` of §I.5.1, as the ratio of the gyration
numerator to the cutoff first moment. -/
def xi2sq (M : SourceModelData) (r : ℝ) : ℝ≥0∞ :=
  gyrationMoment M r / M.cutMoment 1 r

/-- **`ξ₂²(r)` as an exact ratio of weighted two-point sums.**  This is the model-level
form of `ξ₂²(r) = E_{β_c,r}[Σ_{x∈K}‖x‖₂²] / E_{β_c,r}|K|` with both terms evaluated
by the two-point function. -/
theorem xi2sq_eq_tsum_ratio (M : SourceModelData) (r : ℝ) :
    xi2sq M r
      = (∑' y : M.V, ENNReal.ofReal (dot (toVec y) (toVec y)) * cutTwoPointE M r y)
        / (∑' y : M.V, cutTwoPointE M r y) := by
  rw [xi2sq, gyrationMoment_eq_tsum M r, cutMoment_one_eq_tsum M r]


/-! ## §6 The far part of the two-point mass is controlled by the displacement moment -/

/-- **Far-mass bound.**  For every `R ≥ 0`, the part of the cutoff two-point mass carried at
displacement level at least `R` in the direction `u`, scaled by `R^{2p}`, is at most the
`2p`-th displacement moment.  (The sum is over the vertices with `R ≤ |‹y,u›|`; the `if` is
the indicator of that set, so no summability of the far part is assumed.) -/
theorem ofReal_pow_mul_tsum_indicator_le_displacementMoment
    (M : SourceModelData) (p : ℕ) (r : ℝ) (u : Fin M.d → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ENNReal.ofReal (R ^ (2 * p))
        * (∑' y : M.V, if R ≤ |dot (toVec y) u| then cutTwoPointE M r y else 0)
      ≤ displacementMoment M p r u := by
  rw [displacementMoment_eq_tsum M p r u, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  split_ifs with hy
  · have hle : R ^ (2 * p) ≤ |dot (toVec y) u| ^ (2 * p) :=
      pow_le_pow_left₀ hR hy (2 * p)
    have h1 : ENNReal.ofReal (R ^ (2 * p))
        ≤ ENNReal.ofReal (|dot (toVec y) u| ^ (2 * p)) :=
      ENNReal.ofReal_le_ofReal hle
    calc ENNReal.ofReal (R ^ (2 * p)) * cutTwoPointE M r y
        ≤ ENNReal.ofReal (|dot (toVec y) u| ^ (2 * p)) * cutTwoPointE M r y := by
          gcongr
      _ = ENNReal.ofReal ((dot (toVec y) u) ^ (2 * p)) * cutTwoPointE M r y := by
          have habs : |dot (toVec y) u| ^ (2 * p) = (dot (toVec y) u) ^ (2 * p) := by
            rw [← abs_pow, abs_of_nonneg (pow_two_mul_nonneg p)]
          rw [habs]
  · rw [mul_zero]
    exact zero_le

/-! ## §7 A consistency obstruction for the pointwise `|x|^{-d+α}` profile

The proof of Proposition I.5.2 is an ODE argument.  A tempting shortcut is to insert the
*uncut* critical two-point profile `|x|^{-d+α}` (Corollary II.1.9) into the pair-sum
identity of §4 and read off the displacement moment.  The two constants below show that this
shortcut cannot reproduce the paper's Case-1 constant `α/(2-α)` except on the curve
`α (d+1) = 2`.

* `profileConst α d = α (d+2) / (d (2+α))`: the coefficient of `r² E|K|` obtained from the
  pointwise profile `|x|^{-d+α}` on the unit-volume ball (it uses only
  `∫_B |z|^{-d+α} dz = d/α`, `∫_B ‹z,u›² |z|^{-d+α} dz = (d+2)/(α(2+α)) ∫_B ‹z,u›² dz`
  and `|B| = 1`);
* `gyrationConst α = α/(2-α)`: the coefficient stated in Proposition I.5.2, Case 1.

The lemma is an algebraic comparison of these two heuristic constants.  It is an obstruction
to that route, not a statement about the paper. -/

/-- The coefficient of `r² E|K|` in `E_r[Σ_{x∈K}‹x,u›²]` produced by the pointwise
`|x|^{-d+α}` profile on the unit-volume ball. -/
def profileConst (α d : ℝ) : ℝ := α * (d + 2) / (d * (2 + α))

/-- The coefficient of `r² E|K|` in Proposition I.5.2, Case 1. -/
def gyrationConst (α : ℝ) : ℝ := α / (2 - α)

/-- The pointwise-profile coefficient agrees with the paper's Case-1 coefficient exactly on
`α (d+1) = 2`; in the high-dimensional range `0 < α < 2`, `0 < d`, that is a genuine curve,
so the shortcut is not available in general. -/
theorem profileConst_eq_gyrationConst_iff {α d : ℝ} (hα : 0 < α) (hα2 : α < 2)
    (hd : 0 < d) :
    profileConst α d = gyrationConst α ↔ α * (d + 1) = 2 := by
  have hd2 : d ≠ 0 := ne_of_gt hd
  have hα2' : 2 + α ≠ 0 := ne_of_gt (by linarith)
  have hα2'' : 2 - α ≠ 0 := ne_of_gt (by linarith)
  rw [profileConst, gyrationConst]
  rw [div_eq_div_iff (mul_ne_zero hd2 hα2') hα2'']
  constructor
  · intro h
    nlinarith [h]
  · intro h
    nlinarith [h]

/-- The obstruction in the shape used in the report: under `α (d+1) ≠ 2` the two constants
differ, so no derivation of Proposition I.5.2 Case 1 can pass through the pointwise
`|x|^{-d+α}` profile. -/
theorem profileConst_ne_gyrationConst_of_ne {α d : ℝ} (hα : 0 < α) (hα2 : α < 2)
    (hd : 0 < d) (h : α * (d + 1) ≠ 2) :
    profileConst α d ≠ gyrationConst α := by
  intro hEq
  exact h ((profileConst_eq_gyrationConst_iff hα hα2 hd).mp hEq)


/-! ## §8 Monotonicity in the cutoff radius

The cutoff kernel increases with the radius (`SourceModelData.cutKernel_mono`), so the cutoff
law is stochastically nondecreasing in the radius on increasing events
(`longRangeMeasure_mono_kernel`).  Hence both the cutoff two-point function and the gyration
numerator are nondecreasing in `r`: a radius-uniform bound on the gyration numerator is the
same thing as a bound on its supremum over `r`. -/

/-- The connection event in the native open graph is increasing. -/
theorem isIncreasing_conn {V : Type*} (x y : V) :
    IsIncreasing (PercLib.Percolation.Bond.conn x y) := by
  intro a b hab ha
  exact PercLib.Percolation.Bond.conn_mono hab ha

/-- The cutoff two-point function is nondecreasing in the cutoff radius. -/
theorem cutTwoPointE_mono (M : SourceModelData) {r r' : ℝ} (h : r ≤ r') (y : M.V) :
    cutTwoPointE M r y ≤ cutTwoPointE M r' y :=
  longRangeMeasure_mono_kernel (M.cutKernel_mono h) (M.cutKernel_nonneg r)
    (M.cutKernel_nonneg r') M.betaCrit
    (PercLib.Percolation.Bond.measurableSet_conn (0 : M.V) y)
    (isIncreasing_conn (0 : M.V) y)

/-- The gyration numerator `E_{β_c,r}[Σ_{x∈K}‖x‖₂²]` is nondecreasing in the cutoff radius. -/
theorem gyrationMoment_mono (M : SourceModelData) {r r' : ℝ} (h : r ≤ r') :
    gyrationMoment M r ≤ gyrationMoment M r' := by
  rw [gyrationMoment_eq_tsum M r, gyrationMoment_eq_tsum M r']
  exact ENNReal.tsum_le_tsum fun y => mul_le_mul_right (cutTwoPointE_mono M h y) _

/-- Consequently the gyration numerator is bounded above by its supremum over the radius, and
a bound uniform in `r` is exactly a bound on that supremum. -/
theorem gyrationMoment_le_iSup (M : SourceModelData) (r : ℝ) :
    gyrationMoment M r ≤ ⨆ r' : ℝ, gyrationMoment M r' :=
  le_iSup (fun r' => gyrationMoment M r') r


/-! ## §9 Uniform-in-radius control from the uncut critical spatial moment

The radius-supremum of the cutoff gyration numerators is at most the *uncut* critical
gyration numerator.  This is the uniform-in-`r` statement that a cutoff computation of
Proposition I.5.2 needs: finiteness of the uncut critical second spatial moment bounds every
cutoff numerator at once.  (The converse, i.e. the sup/`tsum` interchange, is not claimed.) -/

/-- The uncut critical two-point function `τ_{β_c}(0,y)` in `ℝ≥0∞`. -/
def uncutTwoPointE (M : SourceModelData) (y : M.V) : ℝ≥0∞ :=
  M.law M.betaCrit {ω : PercLib.CriticalLRP.Config M.V |
    PercLib.CriticalLRP.Connects ω (0 : M.V) y}

/-- The uncut critical gyration numerator `E_{β_c}[Σ_{x∈K}‖x‖₂²]`. -/
def gyrationMomentUncut (M : SourceModelData) : ℝ≥0∞ :=
  ∑' y : M.V, ENNReal.ofReal (dot (toVec y) (toVec y)) * uncutTwoPointE M y

/-- The cutoff two-point function is at most the uncut critical one. -/
theorem cutTwoPointE_le_uncut (M : SourceModelData) (r : ℝ) (y : M.V) :
    cutTwoPointE M r y ≤ uncutTwoPointE M y := by
  have h := M.iSup_connects_eq (0 : M.V) y
  have hr : cutTwoPointE M r y
      ≤ ⨆ r' : ℝ, M.cutLaw r' {ω : PercLib.CriticalLRP.Config M.V |
          PercLib.CriticalLRP.Connects ω (0 : M.V) y} :=
    le_iSup (fun r' : ℝ => M.cutLaw r' {ω : PercLib.CriticalLRP.Config M.V |
      PercLib.CriticalLRP.Connects ω (0 : M.V) y}) r
  exact le_trans hr (le_of_eq h)

/-- **Uniform-in-radius bound.**  Every cutoff gyration numerator is bounded by the uncut
critical one. -/
theorem gyrationMoment_le_uncut (M : SourceModelData) (r : ℝ) :
    gyrationMoment M r ≤ gyrationMomentUncut M := by
  rw [gyrationMoment_eq_tsum M r, gyrationMomentUncut]
  exact ENNReal.tsum_le_tsum fun y => mul_le_mul_right (cutTwoPointE_le_uncut M r y) _

/-- The supremum over the cutoff radius is still bounded by the uncut gyration numerator. -/
theorem iSup_gyrationMoment_le_uncut (M : SourceModelData) :
    (⨆ r : ℝ, gyrationMoment M r) ≤ gyrationMomentUncut M :=
  iSup_le fun r => gyrationMoment_le_uncut M r

end PercLib.CriticalLRP.Orchestration.M2

#print axioms PercLib.CriticalLRP.Orchestration.M2.lintegral_tsum_indicator_cluster
#print axioms PercLib.CriticalLRP.Orchestration.M2.cutLaw_eq_edgeMeasure
#print axioms PercLib.CriticalLRP.Orchestration.M2.cutTwoPoint_le_one
#print axioms PercLib.CriticalLRP.Orchestration.M2.cutTwoPointE_eq_production
#print axioms PercLib.CriticalLRP.Orchestration.M2.cutTwoPoint_eq_production
#print axioms PercLib.CriticalLRP.Orchestration.M2.displacementMoment_eq_tsum
#print axioms PercLib.CriticalLRP.Orchestration.M2.displacementMoment_eq_spatialMomentENN
#print axioms PercLib.CriticalLRP.Orchestration.M2.displacementMoment_toReal_eq_tsum
#print axioms PercLib.CriticalLRP.Orchestration.M2.cutMoment_one_eq_tsum
#print axioms PercLib.CriticalLRP.Orchestration.M2.displacementMoment_zero
#print axioms PercLib.CriticalLRP.Orchestration.M2.gyrationMoment_eq_tsum
#print axioms PercLib.CriticalLRP.Orchestration.M2.gyrationMoment_toReal_eq_tsum
#print axioms PercLib.CriticalLRP.Orchestration.M2.xi2sq_eq_tsum_ratio
#print axioms PercLib.CriticalLRP.Orchestration.M2.ofReal_pow_mul_tsum_indicator_le_displacementMoment
#print axioms PercLib.CriticalLRP.Orchestration.M2.profileConst_eq_gyrationConst_iff
#print axioms PercLib.CriticalLRP.Orchestration.M2.profileConst_ne_gyrationConst_of_ne
#print axioms PercLib.CriticalLRP.Orchestration.M2.isIncreasing_conn
#print axioms PercLib.CriticalLRP.Orchestration.M2.cutTwoPointE_mono
#print axioms PercLib.CriticalLRP.Orchestration.M2.gyrationMoment_mono
#print axioms PercLib.CriticalLRP.Orchestration.M2.gyrationMoment_le_iSup
#print axioms PercLib.CriticalLRP.Orchestration.M2.cutTwoPointE_le_uncut
#print axioms PercLib.CriticalLRP.Orchestration.M2.gyrationMoment_le_uncut
#print axioms PercLib.CriticalLRP.Orchestration.M2.iSup_gyrationMoment_le_uncut
