/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m1/I417A/Main.lean ; module path rewritten only.
-/

/-
# Hutchcroft Lemma I.4.17, direction A: the nonnegativity theorem

Main results.

* `lintegral_negConn_mul_cardFun_pow` : the **exact native event expansion** of the raw
  signed difference as a labelled-vertex sum of two-cluster non-connection probabilities.
* `momentDiff_nonneg` : for every `p q : ℕ` and every pair of vertices, and *without* any
  moment-finiteness hypothesis (all quantities are `ℝ≥0∞`, infinite clusters included),
  `E[1(x ↮ y)|K_x|^p|K_y|^q] ≤ E|K_x|^p · E|K_y|^q`.
* `momentDiff_nonneg'` : the same, from the repository's Lemma I.2.1(i) for increasing
  functionals; an independent check that the nonnegativity half needs no new mathematics.
* `momentDiff_nonneg_basepoint` : the source's shape `E|K|^p E|K|^q − ...`, where
  basepoint independence of `E|K|^n` is supplied by `π`-preserving vertex permutations
  (the canonical model's rendering of "transitive weighted graph").

The proof of `momentDiff_nonneg` uses only BK plus the disjoint-witness inclusion
`labelEvent_disjointOccurrence`; it never uses the restoration coupling, and in particular
never the invalid inclusion `K_y ⊆ K~_y`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Nonnegative.Events
public import PercLib.CriticalLRP.Correlation.I417.Nonnegative.Expansion
public import PercLib.CriticalLRP.Correlation.SecondMomentPermutation

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace I417A

variable {V : Type*} [Countable V]

/-- The moment of a cluster-cardinality power as a labelled-vertex sum of connection
probabilities. -/
theorem lintegral_cardFun_pow_eq_tsum (π : Sym2 V → unitInterval) (x : V) (p : ℕ) :
    ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)
      = ∑' f : Fin p → V, (edgeMeasure π) (labelEvent x f) := by
  classical
  have hpt : ∀ ω : Config V, Percolation.cardFun (cluster ω x) ^ p
      = ∑' f : Fin p → V, (labelEvent x f).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    simp only [cardFun_pow_eq_tsum]
    exact tsum_congr fun f => prod_indicator_apply x f ω
  simp only [hpt]
  rw [lintegral_tsum]
  · exact tsum_congr fun f => lintegral_indicator_one (measurableSet_labelEvent x f)
  · intro f
    exact Measurable.aemeasurable (measurable_const.indicator (measurableSet_labelEvent x f))

/-- **Exact native event expansion of the raw signed moment difference.**
The weighted cluster moments expand into a labelled-vertex sum of two-cluster hit probabilities. -/
theorem lintegral_negConn_mul_cardFun_pow (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) :
    ∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) ^ p * Percolation.cardFun (cluster ω y) ^ q)
        ∂(edgeMeasure π)
      = ∑' r : (Fin p → V) × (Fin q → V),
          (edgeMeasure π) (labelEvent x r.1 ∩ labelEvent y r.2 ∩ {ω | ¬ Connects ω x y}) := by
  classical
  have hpt : ∀ ω : Config V,
      ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) ^ p * Percolation.cardFun (cluster ω y) ^ q)
      = ∑' r : (Fin p → V) × (Fin q → V),
          ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
            ((labelEvent x r.1).indicator (fun _ => (1 : ℝ≥0∞)) ω *
             (labelEvent y r.2).indicator (fun _ => (1 : ℝ≥0∞)) ω) := by
    intro ω
    simp only [cardFun_pow_eq_tsum]
    simp only [prod_indicator_apply]
    rw [tsum_mul_tsum_eq_tsum_prod, ← ENNReal.tsum_mul_left]
  simp only [hpt]
  rw [lintegral_tsum]
  · refine tsum_congr fun r => ?_
    have hind : (fun ω : Config V =>
        ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ((labelEvent x r.1).indicator (fun _ => (1 : ℝ≥0∞)) ω *
           (labelEvent y r.2).indicator (fun _ => (1 : ℝ≥0∞)) ω))
        = (labelEvent x r.1 ∩ labelEvent y r.2 ∩
            {ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      by_cases h1 : ω ∈ labelEvent x r.1 <;> by_cases h2 : ω ∈ labelEvent y r.2 <;>
        by_cases h3 : ω ∈ ({ω : Config V | ¬ Connects ω x y} : Set (Config V)) <;>
        simp [h1, h2, h3]
    rw [hind]
    exact lintegral_indicator_one
      (measurableSet_labelEvent x r.1 |>.inter (measurableSet_labelEvent y r.2)
        |>.inter (measurableSet_connSet x y).compl)
  · intro r
    have h1 : Measurable fun ω : Config V =>
        ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
      measurable_const.indicator (measurableSet_connSet x y).compl
    have h2 : Measurable fun ω : Config V =>
        (labelEvent x r.1).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
      measurable_const.indicator (measurableSet_labelEvent x r.1)
    have h3 : Measurable fun ω : Config V =>
        (labelEvent y r.2).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
      measurable_const.indicator (measurableSet_labelEvent y r.2)
    exact (h1.mul (h2.mul h3)).aemeasurable

/-- **Lemma I.4.17, nonnegativity, general `p q`.**
For percolation on the canonical complete weighted graph,
`E[1(x ↮ y) |K_x|^p |K_y|^q] ≤ E|K_x|^p · E|K_y|^q`
with the extended (`ℝ≥0∞`-valued) cluster cardinality, so that infinite clusters are
included and no moment-finiteness is assumed. -/
theorem momentDiff_nonneg (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p q : ℕ) :
    ∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) ^ p * Percolation.cardFun (cluster ω y) ^ q)
        ∂(edgeMeasure π)
      ≤ (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)) *
          (∫⁻ ω, Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π)) := by
  classical
  rw [lintegral_negConn_mul_cardFun_pow, lintegral_cardFun_pow_eq_tsum,
    lintegral_cardFun_pow_eq_tsum, tsum_mul_tsum_eq_tsum_prod]
  refine ENNReal.tsum_le_tsum fun r => ?_
  refine le_trans (measure_mono ?_) (bk_labelEvent_ennreal π hπ x y r.1 r.2)
  rintro ω ⟨⟨hA, hB⟩, hC⟩
  exact labelEvent_disjointOccurrence r.1 r.2 hA hB hC

/-- **The same nonnegativity from the general two-cluster correlation inequality**
(`Percolation.twoCluster_functional_ennreal`, i.e. Lemma I.2.1(i) for increasing functionals).
This is an independent check of `momentDiff_nonneg`, and shows that the nonnegativity half of
Lemma I.4.17 is a special case of Lemma I.2.1(i). -/
theorem momentDiff_nonneg' (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p q : ℕ) :
    ∫⁻ ω, ({ω : Config V | ¬ Connects ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) ^ p * Percolation.cardFun (cluster ω y) ^ q)
        ∂(edgeMeasure π)
      ≤ (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)) *
          (∫⁻ ω, Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π)) := by
  classical
  let := Encodable.ofCountable (Sym2 V)
  have h := Percolation.twoCluster_functional_ennreal (idBondGraph V) π hπ x y
    (Percolation.edgeExhaustion (E := Sym2 V))
    (Percolation.edgeExhaustion_mono) (Percolation.edgeExhaustion_cover)
    (F := fun S => Percolation.cardFun S ^ p) (H := fun S => Percolation.cardFun S ^ q)
    (fun S T hST => pow_le_pow_left' (Percolation.cardFun_mono hST) p)
    (fun S T hST => pow_le_pow_left' (Percolation.cardFun_mono hST) q)
    (cardFun_pow_cont _ Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover x p)
    (cardFun_pow_cont _ Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover y q)
    ((Percolation.measurable_cardFun_cluster (idBondGraph V) x).pow_const p)
    ((Percolation.measurable_cardFun_cluster (idBondGraph V) y).pow_const q)
  simpa only [cluster_idBondGraph, conn_idBondGraph_iff, edgeMeasure_eq_edgeLaw] using h

/-! ## The exact deficit, and the two slacks that replace the printed argument -/

/-- The raw signed difference is the labelled-vertex sum of the exact deficit events. -/
theorem rawDiff_eq_tsum_deficit (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) :
    rawDiff π x y p q =
      ∑' r : (Fin p → V) × (Fin q → V), (edgeMeasure π) (deficitEvent x y r.1 r.2) :=
  lintegral_negConn_mul_cardFun_pow π x y p q

/-- The product of moments is the labelled-vertex sum of the products of the labelled
connection probabilities. -/
theorem momentProd_eq_tsum_mul (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) :
    momentProd π x y p q =
      ∑' r : (Fin p → V) × (Fin q → V),
        (edgeMeasure π) (labelEvent x r.1) * (edgeMeasure π) (labelEvent y r.2) := by
  rw [momentProd, lintegral_cardFun_pow_eq_tsum, lintegral_cardFun_pow_eq_tsum,
    tsum_mul_tsum_eq_tsum_prod]

/-- First slack: the exact deficit event is contained in the disjoint occurrence of the two
labelled events.  This is the only place where non-connection is used, and it replaces the
printed proof's (false) claim `K_y ⊆ K~_y`. -/
theorem deficitEvent_measure_le_disjointOcc (π : Sym2 V → unitInterval) (x y : V) {p q : ℕ}
    (f : Fin p → V) (g : Fin q → V) :
    (edgeMeasure π) (deficitEvent x y f g)
      ≤ (edgeMeasure π) (Percolation.DisjointOccurrence (labelEvent x f) (labelEvent y g)) := by
  refine measure_mono ?_
  rintro ω ⟨⟨hA, hB⟩, hC⟩
  exact labelEvent_disjointOccurrence f g hA hB hC

/-- Second slack: BK. -/
theorem deficitEvent_measure_le_mul (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) :
    (edgeMeasure π) (deficitEvent x y f g)
      ≤ (edgeMeasure π) (labelEvent x f) * (edgeMeasure π) (labelEvent y g) :=
  le_trans (deficitEvent_measure_le_disjointOcc π x y f g)
    (bk_labelEvent_ennreal π hπ x y f g)

/-! ## The concrete `p = 2, q = 1` instance of Lemma I.4.17 -/

/-- **Nonnegativity for the printed `p = 2, q = 1` example**, in the exact shape of the
lemma's first inequality: `E|K|^2 E|K| − E[|K_x|^2 |K_y| 1(x ↮ y)] ≥ 0`, written additively
as the corresponding `ℝ≥0∞` inequality.  This is a specialization of the general theorem,
not a substitute for it. -/
theorem momentDiff_nonneg_two_one (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V) :
    rawDiff π x y 2 1 ≤ momentProd π x y 2 1 :=
  momentDiff_nonneg π hπ x y 2 1

/-- The labelled-vertex expansion in the concrete case `p = 2`, `q = 1`. -/
theorem rawDiff_two_one_eq_tsum (π : Sym2 V → unitInterval) (x y : V) :
    rawDiff π x y 2 1 =
      ∑' r : (Fin 2 → V) × (Fin 1 → V), (edgeMeasure π) (deficitEvent x y r.1 r.2) :=
  rawDiff_eq_tsum_deficit π x y 2 1

/-! ## The source's `E|K|^p E|K|^q` form -/

/-- **Lemma I.4.17, nonnegativity, in the source's basepoint-free shape.**  If every vertex
is carried to `x` (resp. `y`) by a `π`-preserving vertex permutation, then
`E|K_x|^p = E|K_o|^p` and `E|K_y|^q = E|K_o|^q`, so the moment product is `E|K|^p E|K|^q`.
This is the canonical model's rendering of the source's "transitive weighted graph"
hypothesis; the nonnegativity itself needs neither transitivity nor finiteness of moments. -/
theorem momentDiff_nonneg_basepoint (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (o x y : V) (p q : ℕ)
    (gx : V ≃ V) (hgx : ∀ e : Sym2 V, π (Sym2.map gx e) = π e) (hx : gx o = x)
    (gy : V ≃ V) (hgy : ∀ e : Sym2 V, π (Sym2.map gy e) = π e) (hy : gy o = y) :
    rawDiff π x y p q ≤
      (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ p ∂(edgeMeasure π)) *
        (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ q ∂(edgeMeasure π)) := by
  refine le_trans (momentDiff_nonneg π hπ x y p q) ?_
  rw [← hx, ← hy]
  rw [PercLib.CriticalLRP.TreeExpansion.FivePoint.lintegral_cardFun_pow_permConfig π gx hgx p o,
    PercLib.CriticalLRP.TreeExpansion.FivePoint.lintegral_cardFun_pow_permConfig π gy hgy q o]

/-- **The same, for the paper's law `P_β`** (`β ≥ 0`, `J ≥ 0`); no extra hypothesis. -/
theorem longRange_momentDiff_nonneg {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : V) (p q : ℕ) :
    rawDiff (bernoulliEdgeProb J hJ β) x y p q
      ≤ momentProd (bernoulliEdgeProb J hJ β) x y p q :=
  momentDiff_nonneg _ (bernoulliEdgeProb_lt_one hJ β) x y p q

/-! ## The source's real-valued form, with the finiteness hypothesis explicit -/

/-- **Lemma I.4.17, nonnegativity, in the source's real-valued shape.**
The source's expression `E|K|^p E|K|^q − E[|K_x|^p|K_y|^q 1(x ↮ y)]` is a difference of real
numbers only when the two moments are finite.  This is *the only* place where finiteness is
needed: under `E|K_x|^p < ⊤` and `E|K_y|^q < ⊤` (the `ℝ≥0∞` integrals are not `⊤`) the
difference is nonnegative, with no further hypothesis.  When a moment is infinite the
subtraction is not the source's expression at all, and the `ℝ≥0∞` form
`momentDiff_nonneg` is the correct statement. -/
theorem momentDiff_nonneg_real (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p q : ℕ)
    (hx : (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)) ≠ ⊤)
    (hy : (∫⁻ ω, Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π)) ≠ ⊤) :
    0 ≤ (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)).toReal *
          (∫⁻ ω, Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π)).toReal -
        (rawDiff π x y p q).toReal := by
  have hmain := momentDiff_nonneg π hπ x y p q
  have hfin : (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)) *
      (∫⁻ ω, Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π)) ≠ ⊤ :=
    ENNReal.mul_ne_top hx hy
  have hd : rawDiff π x y p q ≠ ⊤ := ne_top_of_le_ne_top hfin hmain
  have hle : (rawDiff π x y p q).toReal
      ≤ (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)).toReal *
          (∫⁻ ω, Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π)).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono hfin hmain
  exact sub_nonneg.mpr hle

end I417A

end PercLib.CriticalLRP
