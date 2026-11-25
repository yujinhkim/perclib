/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
# Lemma I.4.11, part (A): the excluded-expectation decomposition and the true gap event

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.11 and its proof (p. 39-40), read from
`.scratch/formalization-next/paper.txt` lines 2102-2173.

The paper's display reads

  `|B_r| (E_{β,r}|K|)^2 − E_{β,r}[ |K| ∑_{y∈B_r} 1(y∉K) |K_y| ]`
      `= ∑_{y∈B_r} ∑_{x,z} [ P(0↔x) P(y↔z) − P_{β,r}(0↔x ↮ y↔z) ]`

and Lemma I.4.12 bounds each bracket by `∑_{a,b} τ(0,a) τ(a,x) τ(a,b) τ(y,b) τ(b,z)`.

## The `↮` in the source is *not* disjoint occurrence

In the source, `0 ↔ x ↮ y ↔ z` means "`0↔x`, `y↔z`, and `x` is **not connected** to `y`"
(the paper's own next display confirms this: it rewrites the same event as
`{x ∈ K_0, y ∉ K_0, z ∈ K_y}`).  The canonical model already carries that event under the
name `apartSet` (`BK/CanonicalBridge.lean`, docstring "`x ↔ y ↮ z ↔ w`"), and Lemma I.2.2 for
it is `longRangeMeasure_threePoint`.

`Correlation/TwoClusterGap.lean` instead defines `disjSet a b c d` as
`Percolation.DisjointOccurrence (connSet a b) (connSet c d)`, i.e. the BK *disjoint
occurrence* event `a↔b ∘ c↔d`.  This file proves that the two are different objects:

* `apartSet o x y z ⊆ disjSet o x y z` (`apartSet_subset_disjSet`) — different clusters give
  vertex-disjoint, hence edge-disjoint, witnesses;
* the inclusion is strict as an event (`exists_disjSet_not_apartSet`) and strictly smaller in
  measure for the fair-coin law on four sites (`measure_apartSet_lt_disjSet`).

Hence `longRange_twoCluster_gap` (which is stated with `disjSet`) is *weaker* than Lemma I.4.12
in the form the proof of Lemma I.4.11 consumes: it bounds `τ(0,x)τ(y,z)` by
`P(disjSet 0 x y z) + diagram`, and `P(apartSet 0 x y z) < P(disjSet 0 x y z)`, while I.4.11
needs the subtraction of `P(apartSet 0 x y z)`.

## The exact `ℝ≥0∞` decomposition (no `∞ − ∞`)

`exclMoment_eq_tsum_apartSet` proves, with no hypotheses at all,

  `∫⁻ ω, |K_0| ∑_{y∈B} 1(y∉K_0) |K_y| = ∑_{y∈B} ∑_x ∑_z P(apartSet 0 x y z)`,

i.e. the excluded expectation *is* a finite `y`-sum of double `x,z` sums of the gap-event
probabilities.  This is the paper's `E_{β,r}[|K| ∑_y 1(y∉K)|K_y|] = ∑_y ∑_{x,z} P(0↔x ↮ y↔z)`,
and it is the exact `ℝ≥0∞` statement with no finite-moment hypotheses; every step is finite
Fubini over the finite set `B` plus `clusterVol_eq_tsum`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.TreeGraphCanonical

set_option autoImplicit true

set_option linter.unusedSectionVars false

set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.I411

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. Semantics of the two candidate gap events -/

/-- **Meaning of the source's `0↔x ↮ y↔z`.**  `apartSet o x y z` is exactly
`{x ∈ K_0} ∩ {y ∉ K_0} ∩ {z ∈ K_y}`; this is the event whose probability the source writes
`P_{β,r}(0↔x ↮ y↔z)`. -/
theorem apartSet_eq_cluster (o x y z : V) :
    apartSet o x y z =
      {ω : Config V | x ∈ cluster ω o ∧ y ∉ cluster ω o ∧ z ∈ cluster ω y} := by
  ext ω
  simp only [apartSet, Set.mem_ofPred_eq, mem_cluster_iff]
  tauto

theorem measurableSet_apartSet (o x y z : V) : MeasurableSet (apartSet o x y z) := by
  have h : apartSet o x y z =
      {ω : Config V | ¬ Connects ω o y} ∩ connSet o x ∩ connSet y z := by
    ext ω
    simp [apartSet, connSet, and_assoc, and_comm]
  rw [h]
  exact (((measurableSet_connSet o y).compl.inter (measurableSet_connSet o x)).inter
    (measurableSet_connSet y z))

/-- **Meaning of `disjSet`**: unfolding `Correlation.TwoClusterGap.disjSet`, it is the BK
disjoint-occurrence event.  This is *not* the source's `↮` event. -/
theorem mem_disjSet_iff (o x y z : V) (ω : Config V) :
    ω ∈ disjSet o x y z ↔
      ∃ s t : Finset (Sym2 V), (s : Set (Sym2 V)) ⊆ ω ∧ (t : Set (Sym2 V)) ⊆ ω ∧
        Disjoint s t ∧ Connects (s : Set (Sym2 V)) o x ∧
          Connects (t : Set (Sym2 V)) y z :=
  Iff.rfl

/-- **`apartSet ⊆ disjSet`.**  If the two connections occur in different clusters then their
witness paths share no vertex, hence no edge, so the disjoint occurrence holds. -/
theorem apartSet_subset_disjSet (o x y z : V) : apartSet o x y z ⊆ disjSet o x y z := by
  intro ω hω
  obtain ⟨hox, hyz, hoy⟩ : Connects ω o x ∧ Connects ω y z ∧ ¬ Connects ω o y := hω
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr hox
  obtain ⟨q, hq⟩ := pathConnects_iff.mpr hyz
  refine ⟨p.edges.toFinset, q.edges.toFinset, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact hp e (by simpa using he)
  · intro e he
    exact hq e (by simpa using he)
  · refine Finset.disjoint_left.mpr fun e he he' => ?_
    rw [List.mem_toFinset] at he he'
    induction e using Sym2.ind with
    | _ u v =>
        have hu_supp_p : u ∈ p.support :=
          SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
            (Or.inr ⟨s(u, v), he, Sym2.mem_mk_left u v⟩)
        have hu_supp_q : u ∈ q.support :=
          SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
            (Or.inr ⟨s(u, v), he', Sym2.mem_mk_left u v⟩)
        have hu₁ : Connects ω o u := mem_cluster_iff.mp
          (mem_cluster_of_mem_support p hp u hu_supp_p)
        have hu₂ : Connects ω y u := mem_cluster_iff.mp
          (mem_cluster_of_mem_support q hq u hu_supp_q)
        exact hoy (hu₁.trans hu₂.symm)
  · exact pathConnects_iff.mp ⟨p, fun e he => by simpa using he⟩
  · exact pathConnects_iff.mp ⟨q, fun e he => by simpa using he⟩

/-! ## 2. The excluded expectation as a double `x,z` sum of gap probabilities

The paper's `E_{β,r}[ |K| ∑_{y∈B} 1(y∉K) |K_y| ]` is exactly `exclMoment` below.  Its
decomposition into `∑_{y∈B} ∑_{x,z} P(0↔x ↮ y↔z)` needs nothing beyond
`clusterVol_eq_tsum` (twice), Fubini for finite `B` and the countable `x`, `z` sums, and the
pointwise indicator identity `indicator_apartSet`.  No finiteness of any moment is assumed:
everything lives in `ℝ≥0∞`, so infinite clusters cause no subtraction. -/

/-- The **excluded expectation** `E[ |K_0| ∑_{y∈B} 1(y ∉ K_0) |K_y| ]` of the proof of
Lemma I.4.11, in `ℝ≥0∞` so that infinite cluster volumes are harmless. -/
noncomputable def exclMoment (π : Sym2 V → unitInterval) (o : V) (B : Finset V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω o *
    ∑ y ∈ B, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
      ∂(edgeMeasure π)

/-- `|K_v| |K_w| = ∑_x ∑_z 1(x ∈ K_v) 1(z ∈ K_w)`. -/
theorem clusterVol_mul_clusterVol (ω : Config V) (v w : V) :
    clusterVol ω v * clusterVol ω w =
      ∑' x : V, ∑' z : V,
        ((cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) x *
          (cluster ω w).indicator (fun _ => (1 : ℝ≥0∞)) z) := by
  rw [clusterVol_eq_tsum ω v, clusterVol_eq_tsum ω w, ← ENNReal.tsum_mul_right]
  exact tsum_congr fun x => by rw [← ENNReal.tsum_mul_left]

/-- The pointwise indicator identity behind the decomposition: the three indicators select
exactly the event `{x ∈ K_0, y ∉ K_0, z ∈ K_y}`. -/
theorem indicator_apartSet (o x y z : V) (ω : Config V) :
    (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        ((cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) x *
          (cluster ω y).indicator (fun _ => (1 : ℝ≥0∞)) z)
      = (apartSet o x y z).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [apartSet_eq_cluster]
  by_cases hx : x ∈ cluster ω o <;> by_cases hy : y ∈ cluster ω o <;>
    by_cases hz : z ∈ cluster ω y <;>
    simp [hx, hy, hz, Set.mem_compl_iff, Set.mem_ofPred_eq]

theorem measurable_weighted (o x y z : V) :
    Measurable fun ω : Config V =>
      (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        ((cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) x *
          (cluster ω y).indicator (fun _ => (1 : ℝ≥0∞)) z) :=
  (measurable_const.indicator (measurableSet_cluster_mem o y).compl).mul
    ((measurable_const.indicator (measurableSet_cluster_mem o x)).mul
      (measurable_const.indicator (measurableSet_cluster_mem y z)))

/-- **One `y`-slice of the decomposition**: the weighted expectation at a fixed `y` is the
double `x,z` sum of the gap-event probabilities. -/
theorem lintegral_weighted_eq_tsum_apartSet (π : Sym2 V → unitInterval) (o y : V) :
    (∫⁻ ω, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        (clusterVol ω o * clusterVol ω y) ∂(edgeMeasure π))
      = ∑' x : V, ∑' z : V, edgeMeasure π (apartSet o x y z) := by
  have hpt : ∀ ω : Config V,
      (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
          (clusterVol ω o * clusterVol ω y)
        = ∑' x : V, ∑' z : V,
            ((cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
              ((cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) x *
                (cluster ω y).indicator (fun _ => (1 : ℝ≥0∞)) z)) := by
    intro ω
    rw [clusterVol_mul_clusterVol, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun x => by rw [← ENNReal.tsum_mul_left]
  calc (∫⁻ ω, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        (clusterVol ω o * clusterVol ω y) ∂(edgeMeasure π))
      = ∫⁻ ω, ∑' x : V, ∑' z : V,
            ((cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
              ((cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) x *
                (cluster ω y).indicator (fun _ => (1 : ℝ≥0∞)) z))
          ∂(edgeMeasure π) := by simp only [hpt]
    _ = ∑' x : V, ∫⁻ ω, ∑' z : V,
            ((cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
              ((cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) x *
                (cluster ω y).indicator (fun _ => (1 : ℝ≥0∞)) z))
          ∂(edgeMeasure π) := by
        refine lintegral_tsum fun x => ?_
        exact (Measurable.tsum fun z => measurable_weighted o x y z).aemeasurable
    _ = ∑' x : V, ∑' z : V, ∫⁻ ω,
            ((cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
              ((cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) x *
                (cluster ω y).indicator (fun _ => (1 : ℝ≥0∞)) z))
          ∂(edgeMeasure π) := by
        refine tsum_congr fun x => ?_
        exact lintegral_tsum fun z => (measurable_weighted o x y z).aemeasurable
    _ = ∑' x : V, ∑' z : V, edgeMeasure π (apartSet o x y z) := by
        refine tsum_congr fun x => tsum_congr fun z => ?_
        exact (lintegral_congr fun ω => indicator_apartSet o x y z ω).trans
          (lintegral_indicator_one (measurableSet_apartSet o x y z))

/-- **The decomposition of the excluded expectation** (paper: `E_{β,r}[|K| ∑_{y∈B} 1(y∉K)|K_y|]
= ∑_{y∈B} ∑_{x,z} P_{β,r}(0↔x ↮ y↔z)`), exactly and with no hypotheses, in `ℝ≥0∞`. -/
theorem exclMoment_eq_tsum_apartSet (π : Sym2 V → unitInterval) (o : V) (B : Finset V) :
    exclMoment π o B = ∑ y ∈ B, ∑' x : V, ∑' z : V, edgeMeasure π (apartSet o x y z) := by
  have hpt : ∀ ω : Config V,
      clusterVol ω o * ∑ y ∈ B,
          (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
        = ∑ y ∈ B, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
            (clusterVol ω o * clusterVol ω y) := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [exclMoment]
  simp only [hpt]
  calc (∫⁻ ω, ∑ y ∈ B, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
        (clusterVol ω o * clusterVol ω y) ∂(edgeMeasure π))
      = ∑ y ∈ B, ∫⁻ ω, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
          (clusterVol ω o * clusterVol ω y) ∂(edgeMeasure π) :=
        lintegral_finsetSum B (fun y _ =>
          (measurable_const.indicator (measurableSet_cluster_mem o y).compl).mul
            ((measurable_clusterVol o).mul (measurable_clusterVol y)))
    _ = ∑ y ∈ B, ∑' x : V, ∑' z : V, edgeMeasure π (apartSet o x y z) :=
        Finset.sum_congr rfl fun y _ => lintegral_weighted_eq_tsum_apartSet π o y


/-! ## 3. `apartSet` and `disjSet` are genuinely different events

`apartSet o x y z ⊆ disjSet o x y z` is `apartSet_subset_disjSet`.  The reverse inclusion fails:
on four sites, the configuration with only the edges `{0,1}`, `{2,3}`, `{0,2}` open has
edge-disjoint witnesses for `0↔1` and `2↔3` (namely those edges themselves) but also has
`0↔2`, so it is not in `apartSet`.  The next three lemmas record this, and then upgrade it to a
strict *measure* inequality for any law putting positive mass on those three edges. -/

section Strictness

/-- The configuration on `Fin 4` carrying exactly the edges `{0,1}`, `{2,3}`, `{0,2}`. -/
def threeEdgeConfig : Config (Fin 4) :=
  fun e => e = s(0, 1) ∨ e = s(2, 3) ∨ e = s(0, 2)

theorem threeEdge_mem₁ : s(0, 1) ∈ threeEdgeConfig := Or.inl rfl

theorem threeEdge_mem₂ : s(2, 3) ∈ threeEdgeConfig := Or.inr (Or.inl rfl)

theorem threeEdge_mem₃ : s(0, 2) ∈ threeEdgeConfig := Or.inr (Or.inr rfl)

/-- Two open edges give two disjoint connecting witnesses. -/
theorem disjSet_of_two_edges {ω : Config (Fin 4)} (h₁ : s(0, 1) ∈ ω) (h₂ : s(2, 3) ∈ ω) :
    ω ∈ disjSet 0 1 2 3 := by
  have hconn₁ : Connects (↑({s(0, 1)} : Finset (Sym2 (Fin 4))) : Set (Sym2 (Fin 4))) 0 1 :=
    SimpleGraph.Adj.reachable (by
      rw [openGraph_adj]
      exact ⟨by decide, by simp⟩)
  have hconn₂ : Connects (↑({s(2, 3)} : Finset (Sym2 (Fin 4))) : Set (Sym2 (Fin 4))) 2 3 :=
    SimpleGraph.Adj.reachable (by
      rw [openGraph_adj]
      exact ⟨by decide, by simp⟩)
  refine ⟨{s(0, 1)}, {s(2, 3)}, ?_, ?_, ?_, hconn₁, hconn₂⟩
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_singleton] at he
    rw [he]; exact h₁
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_singleton] at he
    rw [he]; exact h₂
  · rw [Finset.disjoint_singleton_right]
    simp

/-- A single open edge `{0,2}` already destroys the `apartSet` event. -/
theorem not_apartSet_of_edge {ω : Config (Fin 4)} (h : s(0, 2) ∈ ω) :
    ω ∉ apartSet 0 1 2 3 := by
  intro hω
  obtain ⟨-, -, hoy⟩ : Connects ω 0 1 ∧ Connects ω 2 3 ∧ ¬ Connects ω 0 2 := hω
  exact hoy (SimpleGraph.Adj.reachable (by
    rw [openGraph_adj]
    exact ⟨by decide, h⟩))

/-- **The inclusion is strict as an event.** -/
theorem exists_disjSet_not_apartSet :
    ∃ ω : Config (Fin 4), ω ∈ disjSet 0 1 2 3 ∧ ω ∉ apartSet 0 1 2 3 :=
  ⟨threeEdgeConfig, disjSet_of_two_edges threeEdge_mem₁ threeEdge_mem₂,
    not_apartSet_of_edge threeEdge_mem₃⟩

/-- **The inclusion is strict in measure**, for any law giving positive probability to the three
edges `{0,1}`, `{2,3}`, `{0,2}`. -/
theorem measure_apartSet_lt_disjSet {π : Sym2 (Fin 4) → unitInterval}
    (hπ0 : ∀ e ∈ ({s(0, 1), s(2, 3), s(0, 2)} : Finset (Sym2 (Fin 4))), toNNReal (π e) ≠ 0) :
    (edgeMeasure π) (apartSet 0 1 2 3) < (edgeMeasure π) (disjSet 0 1 2 3) := by
  classical
  have hcyl : (edgeMeasure π) {ω : Config (Fin 4) |
      ∀ e ∈ ({s(0, 1), s(2, 3), s(0, 2)} : Finset (Sym2 (Fin 4))), e ∈ ω} ≠ 0 := by
    rw [edgeMeasure_cylinder]
    exact Finset.prod_ne_zero_iff.mpr fun e he => by
      have := hπ0 e he
      exact_mod_cast this
  have hsub : {ω : Config (Fin 4) |
      ∀ e ∈ ({s(0, 1), s(2, 3), s(0, 2)} : Finset (Sym2 (Fin 4))), e ∈ ω}
      ⊆ disjSet 0 1 2 3 \ apartSet 0 1 2 3 := by
    intro ω hω
    refine ⟨disjSet_of_two_edges (hω _ (by simp)) (hω _ (by simp)), ?_⟩
    exact not_apartSet_of_edge (hω _ (by simp))
  have hmeas : MeasurableSet
      (disjSet (0 : Fin 4) 1 2 3 \ apartSet (0 : Fin 4) 1 2 3) :=
    (measurableSet_disjSet (0 : Fin 4) 1 2 3).diff
      (measurableSet_apartSet (0 : Fin 4) 1 2 3)
  have hpos : 0 < (edgeMeasure π) (disjSet 0 1 2 3 \ apartSet 0 1 2 3) :=
    lt_of_lt_of_le (pos_iff_ne_zero.mpr hcyl) (measure_mono hsub)
  have hunion : apartSet (0 : Fin 4) 1 2 3 ∪
      (disjSet (0 : Fin 4) 1 2 3 \ apartSet (0 : Fin 4) 1 2 3) =
      disjSet (0 : Fin 4) 1 2 3 :=
    Set.union_sdiff_cancel (apartSet_subset_disjSet (0 : Fin 4) 1 2 3)
  have hsplit : (edgeMeasure π) (disjSet 0 1 2 3)
      = (edgeMeasure π) (apartSet 0 1 2 3) +
        (edgeMeasure π) (disjSet 0 1 2 3 \ apartSet 0 1 2 3) := by
    have h := measure_union (μ := edgeMeasure π) (s₁ := apartSet 0 1 2 3)
      (s₂ := disjSet 0 1 2 3 \ apartSet 0 1 2 3) disjoint_sdiff_self_right hmeas
    rw [hunion] at h
    exact h
  rw [hsplit]
  exact ENNReal.lt_add_right (measure_ne_top _ _) (ne_of_gt hpos)

end Strictness

/-! ## 4. From the gap inequality to the Lemma I.4.11 step

`TwoClusterGapApart` is Lemma I.4.12 *in the form the proof of I.4.11 uses*: the subtracted
event is the source's `↮` event `apartSet`, not the disjoint-occurrence event `disjSet`.
`I411_step_of_twoClusterGapApart` then performs the finite `y`-sum / countable `x,z`-sum
combination, giving exactly the paper's

  `|B| (E|K|)^2 − E[|K| ∑_{y∈B} 1(y∉K)|K_y|] ≤ ∑_{y∈B} ∑_{x,z} [diagram]`

in additive `ℝ≥0∞` form.  `apartSet_gap_of_disjSet_gap` records precisely what the existing
`disjSet`-based `longRange_twoCluster_gap` does give: the same inequality plus the extra,
strictly positive error term `P(disjSet) − P(apartSet)`. -/

section Reduction

/-- The five-factor diagram term of Lemma I.4.12,
`∑_a ∑_b τ(0,a) τ(a,x) τ(a,b) τ(y,b) τ(b,z)`. -/
noncomputable def gapDiagram (μ : Measure (Config V)) (o y x z : V) : ℝ≥0∞ :=
  ∑' a : V, ∑' b : V, μ (connSet o a) * μ (connSet a x) * μ (connSet a b)
    * μ (connSet y b) * μ (connSet b z)

/-- **Lemma I.4.12 with the source's event**: `τ(0,x) τ(y,z) ≤ P(0↔x ↮ y↔z) + diagram`,
where `0↔x ↮ y↔z` is `apartSet 0 x y z` (not `disjSet`). -/
def TwoClusterGapApart (μ : Measure (Config V)) (o : V) : Prop :=
  ∀ x y z : V, μ (connSet o x) * μ (connSet y z) ≤
    μ (apartSet o x y z) + gapDiagram μ o y x z

/-- **The Lemma I.4.11 step**, obtained by summing one application of the gap inequality over
the finite set `B` and over `x, z`, using `exclMoment_eq_tsum_apartSet`:

  `∑_{y∈B} ∑_{x,z} τ(0,x) τ(y,z) ≤ E[|K_0| ∑_{y∈B} 1(y∉K_0)|K_y|]
      + ∑_{y∈B} ∑_{x,z} [diagram]`.

No `∞ − ∞` occurs: the identity `exclMoment = ∑_y ∑_x ∑_z P(apartSet)` replaces the
subtraction, and the two sides are compared additively. -/
theorem I411_step_of_twoClusterGapApart {π : Sym2 V → unitInterval} {o : V}
    (h : TwoClusterGapApart (edgeMeasure π) o) (B : Finset V) :
    (∑ y ∈ B, ∑' x : V, ∑' z : V,
        (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z))
      ≤ exclMoment π o B +
        ∑ y ∈ B, ∑' x : V, ∑' z : V, gapDiagram (edgeMeasure π) o y x z := by
  have hle : ∀ y ∈ B,
      (∑' x : V, ∑' z : V,
          (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z))
        ≤ (∑' x : V, ∑' z : V, (edgeMeasure π) (apartSet o x y z)) +
          ∑' x : V, ∑' z : V, gapDiagram (edgeMeasure π) o y x z := by
    intro y _
    calc (∑' x : V, ∑' z : V,
          (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z))
        ≤ ∑' x : V, ∑' z : V,
            ((edgeMeasure π) (apartSet o x y z) + gapDiagram (edgeMeasure π) o y x z) :=
          ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun z => h x y z
      _ = (∑' x : V, ∑' z : V, (edgeMeasure π) (apartSet o x y z)) +
            ∑' x : V, ∑' z : V, gapDiagram (edgeMeasure π) o y x z := by
          simp only [ENNReal.tsum_add]
  calc (∑ y ∈ B, ∑' x : V, ∑' z : V,
        (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z))
      ≤ ∑ y ∈ B, ((∑' x : V, ∑' z : V, (edgeMeasure π) (apartSet o x y z)) +
          ∑' x : V, ∑' z : V, gapDiagram (edgeMeasure π) o y x z) :=
        Finset.sum_le_sum hle
    _ = (∑ y ∈ B, ∑' x : V, ∑' z : V, (edgeMeasure π) (apartSet o x y z)) +
          ∑ y ∈ B, ∑' x : V, ∑' z : V, gapDiagram (edgeMeasure π) o y x z :=
        Finset.sum_add_distrib
    _ = exclMoment π o B +
          ∑ y ∈ B, ∑' x : V, ∑' z : V, gapDiagram (edgeMeasure π) o y x z := by
        rw [exclMoment_eq_tsum_apartSet]

/-- **What the existing `disjSet`-based `longRange_twoCluster_gap` actually yields.**  It gives
the source's inequality only with the extra error term `P(disjSet) − P(apartSet)`, which is
strictly positive as soon as the three edges `{0,1}`, `{2,3}`, `{0,2}` have positive
probability (`measure_apartSet_lt_disjSet`). -/
theorem apartSet_gap_of_disjSet_gap {μ : Measure (Config V)} {o x y z : V} {D : ℝ≥0∞}
    (h : μ (connSet o x) * μ (connSet y z) ≤ μ (disjSet o x y z) + D) :
    μ (connSet o x) * μ (connSet y z) ≤
      μ (apartSet o x y z) + (D + μ (disjSet o x y z \ apartSet o x y z)) := by
  have hunion : apartSet o x y z ∪ (disjSet o x y z \ apartSet o x y z) = disjSet o x y z :=
    Set.union_sdiff_cancel (apartSet_subset_disjSet o x y z)
  have hsplit : μ (disjSet o x y z) = μ (apartSet o x y z) +
      μ (disjSet o x y z \ apartSet o x y z) := by
    have h := measure_union (μ := μ) (s₁ := apartSet o x y z)
      (s₂ := disjSet o x y z \ apartSet o x y z) disjoint_sdiff_self_right
      ((measurableSet_disjSet o x y z).diff (measurableSet_apartSet o x y z))
    rw [hunion] at h
    exact h
  calc μ (connSet o x) * μ (connSet y z)
      ≤ μ (apartSet o x y z) + μ (disjSet o x y z \ apartSet o x y z) + D := by
        rw [hsplit] at h; exact h
    _ = μ (apartSet o x y z) + (D + μ (disjSet o x y z \ apartSet o x y z)) := by ac_rfl

end Reduction

end PercLib.CriticalLRP.I411

/-! ## Axiom audit -/
