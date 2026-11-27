/-
Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m5`, direction `d2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwzf17v9`, member `m5`, direction d2.

# The `q = 0` base of Lemma I.4.17: the connected star moment

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.  Lemma I.4.17 (printed p. 45) states, for a transitive weighted graph and
integers `p, q ≥ 0`,

```
0 ≤ E|K|^p E|K|^q − E[|K_x|^p |K_y|^q 1(x ↮ y)]
    ≤ ∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) (E|K|)^{2p+2q+1−ℓ}.
```

The paper's proof of that lemma expands the difference over labelled tuples and then uses the
dichotomy "`y ∈ K_x` or some `y_j ∉ K_y`" to produce a marked vertex `w` on a simple open path
from `y` to `{y_1,…,y_q}`.  **With `q = 0` the target set `{y_1,…,y_q}` is empty and there is no
path to be a sub-event of**, so the printed proof's event cover degenerates.  The formalization
records the covering failure as `I417Gen.prodSet_not_subset_q_zero`; the general marked expansion
`I417Gen.twoCopy_moment_le_marked` therefore carries the hypothesis `1 ≤ q`.

This file proves the *base calculation* that replaces the degenerate step, and isolates exactly
what is missing.

## What is proved

* `I417Gen.rawDiff_add_starMoment` — the exact additive form of the `q = 0` gap:
  `rawDiff + starMoment = momentProd`, i.e.
  `E[1(x ↮ y)|K_x|^p] + E[|K_x|^p 1(x ↔ y)] = E|K_x|^p · 1`.
* `I417Gen.momentProd_sub_rawDiff_right_zero`, `…toReal_right_zero` — the subtractive and
  real-valued forms, with the finiteness boundary explicit (`ℝ≥0∞` truncated subtraction is not
  the source's difference when the deficit is infinite; no `⊤ ↦ 0` conversion is made).
* `I417Gen.starMoment_eq_tsum_labelEvent` — the labelled-vertex expansion
  `E[|K_x|^p 1(x ↔ y)] = ∑_{f : Fin p → V} P(f ⊆ K_x, x ↔ y)`, i.e. the source's
  `∑_{x_1,…,x_p} P(x_1,…,x_p ∈ K_x, y ∈ K_x)`: a **one-copy** `(p+1)`-point star.
* `I417Gen.connSet_measure_le_starMoment`, `I417Gen.starMoment_pos` — the star moment dominates
  `T(x,y)` and is strictly positive; `I417Gen.markedFamily_q_zero_lt_starMoment` — the `q = 0`
  instance of the general marked family is **zero**, while the gap is strictly positive, so the
  `q ≥ 1` template provably cannot be specialised.
* `Orchestration.SourceModelData.connCubeVertexMass_eq_starMoment` and
  `…connCubeVertexMass_eq_momentGap` — the Case-3 per-vertex numerator
  `E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` of `SecondMomentCase3.connCubeMass_le_of_windowGap` **is**
  the `q = 0` moment gap of Lemma I.4.17 at `p = 3`, so the hypothesis `hgap` there is the
  source's Lemma literally, and the remaining obligation is a one-copy tree-diagram bound.
* `…connCubeMass_eq_sum_starMoment` — the window sum, i.e. the Case-3 numerator
  `E_{β_c,r}[|K_0|³ |K_0 ∩ B_r|]` is the window sum of these star moments.  The finiteness
  hypothesis of the subtractive form is derivable at the model
  (`…connCubeVertexMass_eq_momentGap_of_cutMoment`, from `M.cutMoment 3 r ≠ ⊤`).
* `I417Gen.momentPow_eq_starMoment_add_rawDiff`, `I417Gen.starMoment_le_momentPow` — the
  connected/disconnected split of the `p`-th moment and the trivial domination by it;
  `…connCubeVertexMass_le_cutMoment_three` records the resulting per-vertex bound
  `E[|K_0|³1(y ∈ K_0)] ≤ E_{β_c,r}|K|³`, which produces a `|B_r|` that the Case-3 denominator
  cannot absorb, i.e. no decay: the content of the `q = 0` lemma is the `T(0,y)`-weighting.

## Source scope and the recorded difference

At `p = q = 0` the printed display has an empty right-hand sum while the left-hand side is
`P(x ↔ y) > 0`; `I417Gen.momentProd_sub_rawDiff_zero_zero` records the exact value.  Hence the
printed statement needs `p + q ≥ 2` (for `p = 3`, `q = 0` it is `ℓ ∈ {3,4}`, so no issue).  This is
recorded as a hypothesis on the statement, not repaired silently.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.  The definition
`I417Gen.starMoment` is in the sibling `Defs.lean` module.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3

/-! # The `q = 0` connected star moment of Lemma I.4.17 -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Gen

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The two closed-form endpoint values of the moments -/

/-- `E|K_y|^0 = 1` at a probability measure, so the product moment at `q = 0` is the single
`p`-th moment of `|K_x|`. -/
theorem momentProd_right_zero (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    I417A.momentProd π x y p 0 =
      ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π) := by
  have h1 : IsProbabilityMeasure (edgeMeasure π) := inferInstance
  simp only [I417A.momentProd, pow_zero]
  rw [lintegral_one, measure_univ, mul_one]

/-- The raw deficit at `q = 0`. -/
theorem rawDiff_right_zero (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    I417A.rawDiff π x y p 0 =
      ∫⁻ ω, (I417A.notConnSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π) := by
  simp only [I417A.rawDiff, pow_zero, mul_one]

/-- The raw deficit at `p = q = 0` is the probability that `x` and `y` are disconnected. -/
theorem rawDiff_zero_zero (π : Sym2 V → unitInterval) (x y : V) :
    I417A.rawDiff π x y 0 0 = (edgeMeasure π) (I417A.notConnSet x y) := by
  rw [rawDiff_right_zero]
  simp only [pow_zero, mul_one]
  rw [show I417A.notConnSet x y = (connSet x y)ᶜ from rfl]
  exact lintegral_indicator_one (measurableSet_connSet x y).compl

/-! ## Converting an indicator product into a set integral -/

/-- `∫ 1_s · f = ∫_s f`.  Used to identify the `q = 0` deficit with a set integral so that the
complement split `lintegral_add_compl` applies. -/
theorem lintegral_indicator_one_mul {μ : Measure (Config V)} {s : Set (Config V)}
    (hs : MeasurableSet s) (f : Config V → ℝ≥0∞) :
    ∫⁻ ω, s.indicator (fun _ => (1 : ℝ≥0∞)) ω * f ω ∂μ = ∫⁻ ω in s, f ω ∂μ := by
  have hfun : (fun ω => s.indicator (fun _ => (1 : ℝ≥0∞)) ω * f ω) = s.indicator f := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  rw [hfun, lintegral_indicator hs]

/-! ## Positivity of the star moment -/

/-- Every cluster contains its basepoint, so its cardinality is at least one. -/
theorem one_le_cardFun_cluster (ω : Config V) (x : V) :
    1 ≤ Percolation.cardFun (cluster ω x) := by
  rcases (cluster ω x).finite_or_infinite with hfin | hinf
  · rw [Percolation.cardFun_eq_ncard hfin]
    exact_mod_cast (Set.ncard_pos hfin).mpr ⟨x, cluster_mem_self ω x⟩
  · rw [Percolation.cardFun_eq_top hinf]
    exact le_top

theorem one_le_cardFun_pow (ω : Config V) (x : V) (p : ℕ) :
    1 ≤ Percolation.cardFun (cluster ω x) ^ p :=
  one_le_pow₀ (one_le_cardFun_cluster ω x)

/-- At `p = 0` the star moment is the two-point function itself. -/
theorem starMoment_zero (π : Sym2 V → unitInterval) (x y : V) :
    starMoment π x y 0 = (edgeMeasure π) (connSet x y) := by
  simp only [starMoment, pow_zero, mul_one]
  exact lintegral_indicator_one (measurableSet_connSet x y)

/-- **The star moment dominates the two-point function**: `T(x,y) ≤ E[|K_x|^p 1(x ↔ y)]`. -/
theorem connSet_measure_le_starMoment (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    (edgeMeasure π) (connSet x y) ≤ starMoment π x y p := by
  rw [starMoment, lintegral_indicator_one_mul (measurableSet_connSet x y),
    ← lintegral_indicator (measurableSet_connSet x y)
      (fun ω => Percolation.cardFun (cluster ω x) ^ p),
    ← lintegral_indicator_one (μ := edgeMeasure π) (measurableSet_connSet x y)]
  refine lintegral_mono fun ω => ?_
  by_cases h : ω ∈ connSet x y
  · simp only [Set.indicator_of_mem h]
    exact one_le_cardFun_pow ω x p
  · simp only [Set.indicator_of_notMem h]
    exact bot_le

/-- **Strict positivity**, hence the `q = 0` gap is never zero when `x` and `y` connect with
positive probability. -/
theorem starMoment_pos (π : Sym2 V → unitInterval) (x y : V) (p : ℕ)
    (h : 0 < (edgeMeasure π) (connSet x y)) : 0 < starMoment π x y p :=
  lt_of_lt_of_le h (connSet_measure_le_starMoment π x y p)

/-! ## The `q = 0` base calculation -/

/-- **The additive `q = 0` base calculation.**
`E[1(x ↮ y)|K_x|^p] + E[|K_x|^p 1(x ↔ y)] = E|K_x|^p`, exactly, in `ℝ≥0∞` and with no
finiteness hypothesis.  This is the precise content of Lemma I.4.17 at `q = 0`: the "moment gap"
`E|K|^p E|K|^0 − E[1(x ↮ y)|K_x|^p]` is nothing but the connected star moment. -/
theorem rawDiff_add_starMoment (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    I417A.rawDiff π x y p 0 + starMoment π x y p = I417A.momentProd π x y p 0 := by
  simp only [rawDiff_right_zero, momentProd_right_zero, starMoment,
    show I417A.notConnSet x y = (connSet x y)ᶜ from rfl]
  rw [show (∫⁻ ω, (connSet x y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π))
      = ∫⁻ ω in (connSet x y)ᶜ, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)
      from lintegral_indicator_one_mul (measurableSet_connSet x y).compl _]
  rw [show (∫⁻ ω, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π))
      = ∫⁻ ω in connSet x y, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)
      from lintegral_indicator_one_mul (measurableSet_connSet x y) _]
  rw [add_comm]
  exact lintegral_add_compl _ (measurableSet_connSet x y)

/-- **The subtractive `q = 0` base calculation**, under the honest finiteness boundary: `ℝ≥0∞`
subtraction is truncated, so the identification of the difference with the star moment needs the
deficit to be finite (`hfin`).  When it is not, the additive form `rawDiff_add_starMoment` is the
correct statement — see the module notes. -/
theorem momentProd_sub_rawDiff_right_zero (π : Sym2 V → unitInterval) (x y : V) (p : ℕ)
    (hfin : I417A.rawDiff π x y p 0 ≠ ⊤) :
    I417A.momentProd π x y p 0 - I417A.rawDiff π x y p 0 = starMoment π x y p := by
  refine ENNReal.sub_eq_of_eq_add hfin ?_
  rw [add_comm]
  exact (rawDiff_add_starMoment π x y p).symm

/-- The real-valued form of the base calculation: no `⊤ ↦ 0` conversion is made, the finiteness of
the product moment being carried explicitly. -/
theorem momentGap_toReal_right_zero (π : Sym2 V → unitInterval) (x y : V) (p : ℕ)
    (hfin : I417A.momentProd π x y p 0 ≠ ⊤) :
    (I417A.momentProd π x y p 0).toReal - (I417A.rawDiff π x y p 0).toReal
      = (starMoment π x y p).toReal := by
  have hsum : I417A.rawDiff π x y p 0 + starMoment π x y p = I417A.momentProd π x y p 0 :=
    rawDiff_add_starMoment π x y p
  have hr : I417A.rawDiff π x y p 0 ≠ ⊤ := by
    have h2 := hfin
    rw [← hsum] at h2
    exact (ENNReal.add_ne_top.mp h2).1
  have hs : starMoment π x y p ≠ ⊤ := by
    have h2 := hfin
    rw [← hsum] at h2
    exact (ENNReal.add_ne_top.mp h2).2
  have h := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hr hs] at h
  linarith

/-- **The `(p,q) = (0,0)` instance, machine-checked.**  The printed display of Lemma I.4.17 at
`p = q = 0` has an empty right-hand sum, while the left-hand side is `P(x ↔ y)`.  This is the
precise reason the printed statement carries the implicit hypothesis `p + q ≥ 2`; it is recorded
here rather than repaired, and is vacuous for `p = 3`, `q = 0` (`3 ≤ ℓ ≤ 4`). -/
theorem momentProd_sub_rawDiff_zero_zero (π : Sym2 V → unitInterval) (x y : V) :
    I417A.momentProd π x y 0 0 - I417A.rawDiff π x y 0 0 = (edgeMeasure π) (connSet x y) := by
  have hfin : I417A.rawDiff π x y 0 0 ≠ ⊤ := by
    rw [rawDiff_zero_zero]
    exact ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ _))
  rw [momentProd_sub_rawDiff_right_zero π x y 0 hfin, starMoment_zero]

/-- **The `p`-th moment splits into its connected and disconnected parts**:
`E|K_x|^p = E[|K_x|^p 1(x ↔ y)] + E[|K_x|^p 1(x ↮ y)]`.  This is `rawDiff_add_starMoment`
together with `E|K_y|^0 = 1`; it is the exact identity underlying the `q = 0` case of
Lemma I.4.17, with no finiteness hypothesis. -/
theorem momentPow_eq_starMoment_add_rawDiff (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π))
      = starMoment π x y p + I417A.rawDiff π x y p 0 := by
  rw [← momentProd_right_zero, ← rawDiff_add_starMoment, add_comm]

/-- The star moment is dominated by the plain `p`-th moment (the `q = 0` gap is at most `E|K|^p`).
This is the trivial per-vertex inequality; summing it over the window produces a `|B_r|` which
does not cancel against the denominator, which is why a `T(x,y)`-weighted bound is needed. -/
theorem starMoment_le_momentPow (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    starMoment π x y p ≤ ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π) := by
  rw [momentPow_eq_starMoment_add_rawDiff]
  exact le_add_right le_rfl

/-! ## The labelled-vertex expansion: an exact one-copy `(p+1)`-point star

The source writes the `q = 0` gap as `∑_{x_1,…,x_p} P(x_1,…,x_p, y ∈ K_x)`.  The next theorem is
exactly that expansion. -/

theorem indicator_one_inter (A B : Set (Config V)) :
    (fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω * B.indicator (fun _ => (1 : ℝ≥0∞)) ω)
      = (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]

/-- **The `q = 0` gap is the labelled `(p+1)`-point star moment**
`∑_{f : Fin p → V} P(f ⊆ K_x and x ↔ y)`, a sum over labellings of a *single* cluster. -/
theorem starMoment_eq_tsum_labelEvent (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) :
    starMoment π x y p =
      ∑' f : Fin p → V, (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x y) := by
  have hterm : ∀ f : Fin p → V,
      (∫⁻ ω, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i) ∂(edgeMeasure π))
        = (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x y) := by
    intro f
    rw [show (fun ω => (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i))
        = (fun ω => (I417A.labelEvent x f).indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω) from by
      funext ω
      rw [congrFun (I417A.prod_indicator_eq_indicator (x := x) (f := f)) ω]
      ring]
    rw [indicator_one_inter]
    exact lintegral_indicator_one ((I417A.measurableSet_labelEvent x f).inter
      (measurableSet_connSet x y))
  have hmeas : ∀ f : Fin p → V, AEMeasurable (fun ω => (connSet x y).indicator
      (fun _ => (1 : ℝ≥0∞)) ω * ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i))
      (edgeMeasure π) := by
    intro f
    refine AEMeasurable.mul ?_ ?_
    · exact (measurable_const.indicator (measurableSet_connSet x y)).aemeasurable
    · exact (Finset.measurable_prod Finset.univ fun i _ =>
        measurable_const.indicator (measurableSet_cluster_mem x (f i))).aemeasurable
  simp only [starMoment]
  calc ∫⁻ ω, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)
      = ∫⁻ ω, ∑' f : Fin p → V, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i) ∂(edgeMeasure π) := by
        refine lintegral_congr fun ω => ?_
        rw [I417A.cardFun_pow_eq_tsum]
        rw [ENNReal.tsum_mul_left]
    _ = ∑' f : Fin p → V, ∫⁻ ω, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i) ∂(edgeMeasure π) :=
        lintegral_tsum hmeas
    _ = ∑' f : Fin p → V, (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x y) :=
        tsum_congr hterm

/-! ## The obstruction: the general marked family vanishes at `q = 0`

`I417Gen.twoCopy_moment_le_marked` bounds the moment gap by the marked family indexed by
`(terminal, mark) : Fin q × V`.  At `q = 0` that index type is empty, so the bound reads
`gap ≤ 0` while the gap is a strictly positive star moment.  This is the quantitative form of
`I417Gen.prodSet_not_subset_q_zero`: no manipulation of the `q ≥ 1` two-copy machinery can produce
the `q = 0` input, because the family it produces is empty. -/

/-- The `q = 0` instance of the general marked family is empty, hence zero. -/
theorem markedFamily_q_zero_eq_zero (π : Sym2 V → unitInterval) (x : V) (p : ℕ) (y : V) :
    (∑' jw : Fin 0 × V, jointPow π x p jw.2 *
      (∑' g : Fin 0 → V, (edgeMeasure π) (freshMark y g jw.1 jw.2))) = 0 :=
  ENNReal.tsum_eq_zero.mpr fun jw => Fin.elim0 jw.1

/-- **The `q = 0` marked family is strictly smaller than the moment gap** whenever `x` and `y`
connect with positive probability. -/
theorem markedFamily_q_zero_lt_starMoment (π : Sym2 V → unitInterval) (x : V) (p : ℕ) (y : V)
    (h : 0 < (edgeMeasure π) (connSet x y)) :
    (∑' jw : Fin 0 × V, jointPow π x p jw.2 *
        (∑' g : Fin 0 → V, (edgeMeasure π) (freshMark y g jw.1 jw.2)))
      < starMoment π x y p := by
  rw [markedFamily_q_zero_eq_zero π x p y]
  exact starMoment_pos π x y p h

end PercLib.CriticalLRP.I417Gen

/-! ## The bridge to the Case-3 numerator

`SecondMomentCase3.connCubeVertexMass r y` is `E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` under the cutoff law
`M.cutLaw r`, which is definitionally the independent-edge law `edgeMeasure (M.cutProb r)`
(`SourceModelData.cutLaw_eq_edgeMeasure`).  The next two theorems identify it with the `q = 0`
moment gap of Lemma I.4.17 at `p = 3`, so the hypothesis `hgap` of
`SourceModelData.connCubeMass_le_of_windowGap` is the source's lemma itself. -/

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

open PercLib.CriticalLRP.I417Gen

variable (M : SourceModelData)

/-- `E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` is the `q = 0` star moment at `p = 3` of the cutoff law. -/
theorem connCubeVertexMass_eq_starMoment (r : ℝ) (y : M.V) :
    M.connCubeVertexMass r y = starMoment (M.cutProb r) (0 : M.V) y 3 := by
  rw [connCubeVertexMass, starMoment, M.cutLaw_eq_edgeMeasure]
  refine lintegral_congr fun ω => ?_
  rw [clusterVol_eq_encard, Percolation.cardFun_eq_encard, mul_comm]
  congr 1

/-- **The Case-3 per-vertex numerator is the `q = 0` moment gap of Lemma I.4.17 at `p = 3`.**  The
left-hand side is exactly the hypothesis `hgap` of `connCubeMass_le_of_windowGap`. -/
theorem connCubeVertexMass_eq_momentGap (r : ℝ) (y : M.V)
    (hfin : I417A.rawDiff (M.cutProb r) (0 : M.V) y 3 0 ≠ ⊤) :
    M.connCubeVertexMass r y =
      I417A.momentProd (M.cutProb r) (0 : M.V) y 3 0 -
        I417A.rawDiff (M.cutProb r) (0 : M.V) y 3 0 := by
  rw [connCubeVertexMass_eq_starMoment,
    momentProd_sub_rawDiff_right_zero (M.cutProb r) (0 : M.V) y 3 hfin]

/-- The Case-3 numerator is the window sum of the `q = 0` star moments:
`E_{β_c,r}[|K_0|³ |K_0 ∩ B_r|] = ∑_{y ∈ B_r} E[|K_0|³ 1(y ∈ K_0)]`.  (The window decomposition
itself is `SourceModelData.connCubeMass_eq_sum_vertex`; only the identification of each summand is
new here.) -/
theorem connCubeMass_eq_sum_starMoment (r : ℝ) :
    M.connCubeMass r = ∑ y ∈ E1Sign.ballF M r, starMoment (M.cutProb r) (0 : M.V) y 3 := by
  rw [M.connCubeMass_eq_sum_vertex r]
  exact Finset.sum_congr rfl fun y _ => M.connCubeVertexMass_eq_starMoment r y

/-- **The Case-3 per-vertex numerator is the `q = 0` moment gap**, with the finiteness of the
deficit derived from the third cutoff moment rather than assumed. -/
theorem connCubeVertexMass_eq_momentGap_of_cutMoment (r : ℝ) (h3 : M.cutMoment 3 r ≠ ⊤)
    (y : M.V) :
    M.connCubeVertexMass r y =
      I417A.momentProd (M.cutProb r) (0 : M.V) y 3 0 -
        I417A.rawDiff (M.cutProb r) (0 : M.V) y 3 0 := by
  have hM : I417A.momentProd (M.cutProb r) (0 : M.V) y 3 0 ≠ ⊤ := by
    rw [momentProd_right_zero, ← M.cutLaw_eq_edgeMeasure]
    rw [show (∫⁻ ω, Percolation.cardFun (cluster ω (0 : M.V)) ^ 3 ∂(M.cutLaw r))
        = M.cutMoment 3 r from by
      rw [cutMoment]
      simp only [clusterVol_eq_encard, Percolation.cardFun_eq_encard]]
    exact h3
  have hle : I417A.rawDiff (M.cutProb r) (0 : M.V) y 3 0 ≤
      I417A.momentProd (M.cutProb r) (0 : M.V) y 3 0 := by
    rw [← rawDiff_add_starMoment (M.cutProb r) (0 : M.V) y 3]
    exact le_add_right le_rfl
  exact M.connCubeVertexMass_eq_momentGap r y (ne_top_of_le_ne_top hM hle)

/-- The trivial per-vertex bound: each window summand is at most the third cutoff moment.  Summing
it over the window produces a factor `|B_r|` which the denominator cannot absorb, so this is
recorded only to make explicit that the content of Lemma I.4.17 at `p = 3`, `q = 0` is the
`T(0,y)`-weighting, not mere finiteness. -/
theorem connCubeVertexMass_le_cutMoment_three (r : ℝ) (y : M.V) :
    M.connCubeVertexMass r y ≤ M.cutMoment 3 r := by
  rw [connCubeVertexMass_eq_starMoment, cutMoment, M.cutLaw_eq_edgeMeasure]
  simpa only [clusterVol_eq_encard, Percolation.cardFun_eq_encard] using
    starMoment_le_momentPow (M.cutProb r) (0 : M.V) y 3

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
