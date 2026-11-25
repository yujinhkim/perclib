/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m5/I417Gen/Main.lean; module path rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.General.Cover

/-!
# Lemma I.4.17 for arbitrary finite `p, q`: the marked two-copy moment gap

This file assembles the general-`p,q` version of the proof of Lemma I.4.17.  Write
`τ(u,v) = P(u↔v)`, `μ = edgeMeasure π`, and `χ = E|K|`.  The main results are:

* `tsum_prodSet_eq` : `∑_{f,g} (μ⊗μ)(prodSet f g) = E|K_x|^p · E|K_y|^q`
  (the free sums of the two-copy product event are the product of the two cluster moments).
* `tsum_diagSet` : `∑_{f,g} (μ⊗μ)(diagSet f g) = E[|K_x|^p |K_y|^q 1(x ↮ y)]`
  — the diagonal term of the two-copy expansion **is** the moment in the subtracted term of the
  lemma, with the restored cluster `K̃_y` replaced exactly by the one-copy cluster of `y` through
  the law preservation `map_restoreMap` and the identity `K_x(ω̃) = K_x(ω₁)`.  No inclusion
  `K_y ⊆ K̃_y` and no resampling identity is used.
* `tsum_tsum_markSet` : the marked family factorises over the two copies,
  `∑_{f,g} ∑_{(j,w)} (μ⊗μ)(markSet f g j w) = ∑_{(j,w)} E[|K_x|^p 1(w ∈ K_x)] · ∑_g P(freshMark
  y g j w)`,
  where the first factor is a *base-copy* quantity and the second a *fresh-copy* quantity.
  This is the paper's displayed intermediate inequality
  `∑_w ∑_{x_1…x_p} P(w, x_1,…,x_p ∈ K_x) · P(y_1,…,y_q ∈ K̃_y, w on a simple path y → {y_1,…,y_q})`
  in its repaired, provable form: the `q` arms on the fresh side are read in the fresh cluster
  `K_y(ω₂)` (where the covering puts them), and `w = y` covers the paper's `y ∈ K_x` alternative.
* `twoCopy_moment_le_marked`, `moment_gap_tsub_le_marked`, `moment_gap_le_marked_real` : the exact
  source inequality `E|K|^p E|K|^q − E[|K_x|^p |K_y|^q 1(x ↮ y)] ≤ (marked family)`, additively in
  `ℝ≥0∞` (no hypotheses), in `ℝ≥0∞`-subtraction form, and in real-valued form with the two
  finiteness hypotheses.

What is **not** done here: evaluating `E[|K_x|^p 1(w ∈ K_x)]` by tree diagrams.  That is the step
that produces the paper's `T^ℓ(x,y) (E|K|)^{2p+2q+1−ℓ}` with the universal integer constants
`C_{p,q,ℓ}` (the `(2p−3)!!` rooted-tree count of Lemma I.4.16); it is the diagram side of
Lemma I.4.17 and is deliberately left as the named quantity `jointPow`.

No `sorry`, no custom axioms; no definitions.
-/


open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Gen

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Elementary indicator identities -/

theorem indicator_inter_one_ennreal {α : Type*} (A B : Set α) (a : α) :
    (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) a =
      A.indicator (fun _ => (1 : ℝ≥0∞)) a * B.indicator (fun _ => (1 : ℝ≥0∞)) a := by
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp [hA, hB]

/-- The connection indicator of the base point equals the cluster indicator at the target: this is
the pointwise form of `w ∈ K_x(ω) ↔ ω ∈ {x ↔ w}`. -/
theorem cluster_indicator_apply_ennreal (x w : V) (ω : Config V) :
    (connSet x w).indicator (fun _ => (1 : ℝ≥0∞)) ω =
      (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w := by
  have hiff : ω ∈ connSet x w ↔ w ∈ cluster ω x := mem_cluster_iff.symm
  by_cases h : w ∈ cluster ω x
  · rw [Set.indicator_of_mem (s := connSet x w) (hiff.mpr h),
      Set.indicator_of_mem (s := cluster ω x) h]
  · rw [Set.indicator_of_notMem (s := connSet x w) (fun hh => h (hiff.mp hh)),
      Set.indicator_of_notMem (s := cluster ω x) h]

/-- The complement form used for the diagonal event: `ω ∉ {x ↔ y}` iff `y ∉ K_x(ω)`. -/
theorem compl_connSet_indicator_apply (x y : V) (ω : Config V) :
    (connSet x y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω =
      (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y := by
  have hiff : ω ∈ (connSet x y)ᶜ ↔ y ∈ (cluster ω x)ᶜ :=
    not_congr mem_cluster_iff.symm
  by_cases h : y ∈ (cluster ω x)ᶜ
  · rw [Set.indicator_of_mem (s := (connSet x y)ᶜ) (hiff.mpr h),
      Set.indicator_of_mem (s := (cluster ω x)ᶜ) h]
  · rw [Set.indicator_of_notMem (s := (connSet x y)ᶜ) (fun hh => h (hiff.mp hh)),
      Set.indicator_of_notMem (s := (cluster ω x)ᶜ) h]

/-! ## The product event: free sums give the product of moments -/

theorem measure_prodSet (π : Sym2 V → unitInterval) (x y : V) {p q : ℕ} (f : Fin p → V)
    (g : Fin q → V) :
    ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y f g) =
      (edgeMeasure π) (I417A.labelEvent x f) * (edgeMeasure π) (I417A.labelEvent y g) := by
  have h := Measure.prod_prod (μ := edgeMeasure π) (ν := edgeMeasure π)
    (I417A.labelEvent y g) (I417A.labelEvent x f)
  rw [prodSet, h, mul_comm]

/-- **The free sums of the product event are the product of cluster moments.** -/
theorem tsum_prodSet_eq (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) :
    (∑' r : (Fin p → V) × (Fin q → V),
        ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y r.1 r.2)) =
      I417A.momentProd π x y p q := by
  have hterm : ∀ r : (Fin p → V) × (Fin q → V),
      ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y r.1 r.2) =
        (edgeMeasure π) (I417A.labelEvent x r.1) *
          (edgeMeasure π) (I417A.labelEvent y r.2) :=
    fun r => measure_prodSet π x y r.1 r.2
  simp only [hterm]
  rw [I417A.tsum_prod_mul_eq_tsum_mul
    (P := fun f : Fin p → V => (edgeMeasure π) (I417A.labelEvent x f))
    (Q := fun g : Fin q → V => (edgeMeasure π) (I417A.labelEvent y g))]
  simp only [I417A.momentProd, I417A.lintegral_cardFun_pow_eq_tsum]

/-! ## The diagonal event: free sums give the excluded moment -/

theorem diagSet_eq_inter (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) :
    diagSet x y f g =
      {ρ : TwoCopy V | ρ.2 ∈ I417A.labelEvent x f} ∩
        {ρ : TwoCopy V | ρ.2 ∉ connSet x y} ∩
        {ρ : TwoCopy V | restoreMap x ρ ∈ I417A.labelEvent y g} := by
  ext ρ
  simp only [diagSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- **Pointwise indicator identity for the diagonal event.** -/
theorem diagSet_indicator_apply (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V)
    (ρ : TwoCopy V) :
    (diagSet x y f g).indicator (fun _ => (1 : ℝ≥0∞)) ρ =
      (∏ i, (cluster ρ.2 x).indicator (fun _ => (1 : ℝ≥0∞)) (f i)) *
        (cluster ρ.2 x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        (∏ j, (cluster (restoreMap x ρ) y).indicator (fun _ => (1 : ℝ≥0∞)) (g j)) := by
  have h1 : {ρ : TwoCopy V | ρ.2 ∈ I417A.labelEvent x f}.indicator (fun _ => (1 : ℝ≥0∞)) ρ
      = (I417A.labelEvent x f).indicator (fun _ => (1 : ℝ≥0∞)) ρ.2 := rfl
  have h2 : {ρ : TwoCopy V | ρ.2 ∉ connSet x y}.indicator (fun _ => (1 : ℝ≥0∞)) ρ
      = (connSet x y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ρ.2 := rfl
  have h3 : {ρ : TwoCopy V | restoreMap x ρ ∈ I417A.labelEvent y g}.indicator
        (fun _ => (1 : ℝ≥0∞)) ρ
      = (I417A.labelEvent y g).indicator (fun _ => (1 : ℝ≥0∞)) (restoreMap x ρ) := rfl
  rw [diagSet_eq_inter, indicator_inter_one_ennreal, indicator_inter_one_ennreal, h1, h2, h3,
    I417A.prod_indicator_apply x f ρ.2, I417A.prod_indicator_apply y g (restoreMap x ρ),
    compl_connSet_indicator_apply x y ρ.2]

/-- A multiply-then-sum form used for the two-fold free sum of the diagonal event. -/
theorem tsum_prod_mul_const_mul {A B : Type*} [Countable A] [Countable B]
    (P : A → ℝ≥0∞) (Q : B → ℝ≥0∞) (k : ℝ≥0∞) :
    (∑' r : A × B, P r.1 * k * Q r.2) = (∑' a, P a) * k * (∑' b, Q b) := by
  have h1 : ∀ r : A × B, P r.1 * k * Q r.2 = P r.1 * (k * Q r.2) := fun r => by
    rw [mul_assoc]
  simp only [h1]
  rw [I417A.tsum_prod_mul_eq_tsum_mul (P := P) (Q := fun b => k * Q b), ENNReal.tsum_mul_left,
    mul_assoc]

/-- **The pointwise free sum of the diagonal indicator**: summing over the labelled `p`-tuple and
the labelled `q`-tuple gives the `p`-th moment of `|K_x|` in the base copy, the indicator of
`y ∉ K_x`, and the `q`-th moment of the **restored** cluster `K̃_y`. -/
theorem diagSet_indicator_tsum (x y : V) (p q : ℕ) (ρ : TwoCopy V) :
    (∑' r : (Fin p → V) × (Fin q → V), (diagSet x y r.1 r.2).indicator
        (fun _ => (1 : ℝ≥0∞)) ρ) =
      Percolation.cardFun (cluster ρ.2 x) ^ p *
        (cluster ρ.2 x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q := by
  have hterm : ∀ r : (Fin p → V) × (Fin q → V),
      (diagSet x y r.1 r.2).indicator (fun _ => (1 : ℝ≥0∞)) ρ =
        (∏ i, (cluster ρ.2 x).indicator (fun _ => (1 : ℝ≥0∞)) (r.1 i)) *
          (cluster ρ.2 x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
          (∏ j, (cluster (restoreMap x ρ) y).indicator (fun _ => (1 : ℝ≥0∞)) (r.2 j)) :=
    fun r => diagSet_indicator_apply x y r.1 r.2 ρ
  simp only [hterm]
  rw [tsum_prod_mul_const_mul
    (P := fun f : Fin p → V => ∏ i, (cluster ρ.2 x).indicator (fun _ => (1 : ℝ≥0∞)) (f i))
    (Q := fun g : Fin q → V =>
      ∏ j, (cluster (restoreMap x ρ) y).indicator (fun _ => (1 : ℝ≥0∞)) (g j))
    (k := (cluster ρ.2 x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y)]
  rw [← I417A.cardFun_pow_eq_tsum (cluster ρ.2 x) p,
    ← I417A.cardFun_pow_eq_tsum (cluster (restoreMap x ρ) y) q]

/-- **The diagonal term is the excluded moment**, for arbitrary finite `p, q`:
`∑_{f,g} (μ⊗μ)(diagSet f g) = E[1(x ↮ y) |K_x|^p |K_y|^q]`. -/
theorem tsum_diagSet (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) :
    (∑' r : (Fin p → V) × (Fin q → V),
        ((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y r.1 r.2)) =
      I417A.rawDiff π x y p q := by
  classical
  set μ := edgeMeasure π with hμ
  have hmeasure : ∀ r : (Fin p → V) × (Fin q → V),
      (μ.prod μ) (diagSet x y r.1 r.2) =
        ∫⁻ ρ : TwoCopy V, (diagSet x y r.1 r.2).indicator (fun _ => (1 : ℝ≥0∞)) ρ
          ∂(μ.prod μ) :=
    fun r => (lintegral_indicator_one (measurableSet_diagSet x y r.1 r.2)).symm
  simp only [hmeasure]
  rw [← lintegral_tsum]
  swap
  · intro r
    exact (Measurable.indicator measurable_const (measurableSet_diagSet x y r.1 r.2)).aemeasurable
  trans ∫⁻ ρ : TwoCopy V,
      (fun ω : Config V => Percolation.cardFun (cluster ω x) ^ p *
        (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        Percolation.cardFun (cluster ω y) ^ q) (restoreMap x ρ) ∂(μ.prod μ)
  · refine lintegral_congr fun ρ => ?_
    rw [diagSet_indicator_tsum x y p q ρ]
    simp only [restoreMap, cluster_forceOn_compl_touchSet]
  · have hF : Measurable fun ω : Config V => Percolation.cardFun (cluster ω x) ^ p *
        (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        Percolation.cardFun (cluster ω y) ^ q := by
      have h1 : Measurable fun ω : Config V => Percolation.cardFun (cluster ω x) ^ p := by
        simpa only [cluster_idBondGraph] using
          (Percolation.measurable_cardFun_cluster (idBondGraph V) x).pow_const p
      have h2 : Measurable fun ω : Config V =>
          (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y :=
        Measurable.indicator (f := fun _ => (1 : ℝ≥0∞)) measurable_const
          (measurableSet_cluster_mem x y).compl
      have h3 : Measurable fun ω : Config V => Percolation.cardFun (cluster ω y) ^ q := by
        simpa only [cluster_idBondGraph] using
          (Percolation.measurable_cardFun_cluster (idBondGraph V) y).pow_const q
      have h := Measurable.mul (Measurable.mul h1 h2) h3
      convert h using 1
    rw [(lintegral_map hF (measurable_restoreMap x)).symm, map_restoreMap π x]
    rw [I417A.rawDiff, I417A.notConnSet_eq]
    refine lintegral_congr fun ω => ?_
    by_cases h : y ∈ cluster ω x <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h, mul_comm]

/-! ## The marked family: factorisation over the two copies -/

theorem measure_markSet (π : Sym2 V → unitInterval) (x y : V) {p q : ℕ} (f : Fin p → V)
    (g : Fin q → V) (j : Fin q) (w : V) :
    ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y f g j w) =
      (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x w) *
        (edgeMeasure π) (freshMark y g j w) := by
  have h := Measure.prod_prod (μ := edgeMeasure π) (ν := edgeMeasure π)
    (freshMark y g j w) (I417A.labelEvent x f ∩ connSet x w)
  simp only [markSet, h, mul_comm]

/-- **The marked moment through a marked vertex**: `∑_f P(w, f ⊆ K_x) = E[|K_x|^p 1(w ∈ K_x)]`. -/
theorem tsum_labelEvent_inter (π : Sym2 V → unitInterval) (x : V) (p : ℕ) (w : V) :
    (∑' f : Fin p → V,
        (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x w)) = jointPow π x p w := by
  classical
  have hpt : ∀ ω : Config V,
      (∑' f : Fin p → V, (I417A.labelEvent x f ∩ connSet x w).indicator
        (fun _ => (1 : ℝ≥0∞)) ω) =
        Percolation.cardFun (cluster ω x) ^ p *
          (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w := by
    intro ω
    have hind : ∀ f : Fin p → V,
        (I417A.labelEvent x f ∩ connSet x w).indicator (fun _ => (1 : ℝ≥0∞)) ω =
          (∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i)) *
            (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w := by
      intro f
      rw [indicator_inter_one_ennreal, I417A.prod_indicator_apply x f ω,
        cluster_indicator_apply_ennreal x w ω]
    simp only [hind]
    rw [ENNReal.tsum_mul_right, I417A.cardFun_pow_eq_tsum]
  have hmeasure : ∀ f : Fin p → V,
      (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x w) =
        ∫⁻ ω, (I417A.labelEvent x f ∩ connSet x w).indicator (fun _ => (1 : ℝ≥0∞)) ω
          ∂(edgeMeasure π) :=
    fun f => (lintegral_indicator_one ((I417A.measurableSet_labelEvent x f).inter
      (measurableSet_connSet x w))).symm
  simp only [hmeasure]
  rw [← lintegral_tsum]
  · exact lintegral_congr fun ω => hpt ω
  · intro f
    exact (Measurable.indicator measurable_const ((I417A.measurableSet_labelEvent x f).inter
      (measurableSet_connSet x w))).aemeasurable

/-- **The marked family, summed and factorised over the two copies.**  For each `(j,w)` the
`(f,g)`-sum splits into a base-copy factor `E[|K_x|^p 1(w ∈ K_x)]` and a fresh-copy factor
`∑_g P(freshMark y g j w)`. -/
theorem tsum_tsum_markSet (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) :
    (∑' r : (Fin p → V) × (Fin q → V), ∑' jw : Fin q × V,
        ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y r.1 r.2 jw.1 jw.2)) =
      ∑' jw : Fin q × V, jointPow π x p jw.2 *
        (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g jw.1 jw.2)) := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun jw => ?_
  refine Eq.trans (tsum_congr fun r => measure_markSet π x y r.1 r.2 jw.1 jw.2) ?_
  rw [I417A.tsum_prod_mul_eq_tsum_mul
    (P := fun f : Fin p → V => (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x jw.2))
    (Q := fun g : Fin q → V => (edgeMeasure π) (freshMark y g jw.1 jw.2)),
    tsum_labelEvent_inter]

/-! ## The general-`p,q` moment gap -/

/-- **Lemma I.4.17, general `p, q`: the two-copy marked expansion.**  For every `1 ≤ q`, the product
of the cluster moments is bounded by the excluded moment plus the marked family:
`E|K_x|^p E|K_y|^q ≤ E[1(x↮y)|K_x|^p|K_y|^q] + ∑_{(j,w)} E[|K_x|^p 1(w∈K_x)] ∑_g P(freshMark y g
j w)`.
No moment finiteness, no transitivity, no hypothesis other than `1 ≤ q`. -/
theorem twoCopy_moment_le_marked (π : Sym2 V → unitInterval) (x y : V) {p q : ℕ} (hq : 1 ≤ q) :
    I417A.momentProd π x y p q ≤
      I417A.rawDiff π x y p q +
        ∑' jw : Fin q × V, jointPow π x p jw.2 *
          (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g jw.1 jw.2)) := by
  rw [← tsum_prodSet_eq π x y p q]
  refine le_trans (ENNReal.tsum_le_tsum fun r => measure_prodSet_le π x y hq r.1 r.2) ?_
  rw [ENNReal.tsum_add, tsum_diagSet, tsum_tsum_markSet]

/-- **The exact source inequality, subtractive `ℝ≥0∞` form**, valid for every `1 ≤ q`:
`E|K|^p E|K|^q − E[|K_x|^p|K_y|^q 1(x ↮ y)] ≤ (marked family)`.  The `ℝ≥0∞` subtraction is the
paper's difference whenever the two moments are finite; when the subtracted term is larger the left
side is `0` by the `ℝ≥0∞` convention. -/
theorem moment_gap_tsub_le_marked (π : Sym2 V → unitInterval) (x y : V) {p q : ℕ} (hq : 1 ≤ q) :
    I417A.momentProd π x y p q - I417A.rawDiff π x y p q ≤
      ∑' jw : Fin q × V, jointPow π x p jw.2 *
        (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g jw.1 jw.2)) := by
  refine tsub_le_iff_right.mpr ?_
  rw [add_comm]
  exact twoCopy_moment_le_marked π x y hq

/-- **The source statement in real-valued form**, for finite moments: if the product of moments and
the marked family are finite, then the difference of the two real moments is at most the real marked
family.  `E[1(x↮y)|K_x|^p|K_y|^q] ≤ E|K_x|^p E|K_y|^q` is the nonnegativity half of Lemma I.4.17
(`I417A.momentDiff_nonneg`), used here so that the `ℝ≥0∞` difference is the real difference. -/
theorem moment_gap_le_marked_real (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    {p q : ℕ} (hq : 1 ≤ q) (hprod : I417A.momentProd π x y p q ≠ ⊤)
    (hmark : (∑' jw : Fin q × V, jointPow π x p jw.2 *
        (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g jw.1 jw.2))) ≠ ⊤) :
    (I417A.momentProd π x y p q).toReal - (I417A.rawDiff π x y p q).toReal ≤
      (∑' jw : Fin q × V, jointPow π x p jw.2 *
        (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g jw.1 jw.2))).toReal := by
  have hle : I417A.rawDiff π x y p q ≤ I417A.momentProd π x y p q :=
    I417A.momentDiff_nonneg π hπ x y p q
  have hfin : I417A.rawDiff π x y p q ≠ ⊤ := ne_top_of_le_ne_top hprod hle
  have h := moment_gap_tsub_le_marked (p := p) π x y hq
  have hto : (I417A.momentProd π x y p q - I417A.rawDiff π x y p q).toReal ≤
      (∑' jw : Fin q × V, jointPow π x p jw.2 *
        (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g jw.1 jw.2))).toReal :=
    ENNReal.toReal_mono hmark h
  rwa [ENNReal.toReal_sub_of_le hle hprod] at hto

end PercLib.CriticalLRP.I417Gen
