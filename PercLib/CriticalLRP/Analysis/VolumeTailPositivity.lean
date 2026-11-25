/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Positive cluster-volume tails from finite open paths

For Proposition I.3.1, the finite initial-range correction needs positivity of
full-law tails at every positive natural level. This module proves that input
from simple paths of every finite length whose edges all have positive opening
probability. Independence makes the event that a fixed path is open have
positive probability, and its support supplies the required distinct vertices.

The real volume map sends infinite clusters to zero. Consequently the path
event is first included in the tail-or-infinite event of `VolumeTailModel`;
almost-sure finiteness is then used to remove the infinite-cluster part. The
path existence property is stated explicitly and is not inferred merely from
connectedness of an arbitrary graph. Repeated nonperiodic steps supply the
property under translation invariance; `VolumeTailLatticePositivity` specializes
that construction to the positive-intensity power-law lattice kernel.
-/

module

public import PercLib.CriticalLRP.Analysis.VolumeTailModel

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped ENNReal Topology BigOperators

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- A finite set of cluster vertices gives the corresponding lower bound on
finite real cluster volume. -/
theorem card_le_clusterVol_toReal {ω : Config V} {o : V} {t : Finset V}
    (hfin : (cluster ω o).Finite) (ht : (t : Set V) ⊆ cluster ω o) :
    (t.card : ℝ) ≤ (clusterVol ω o).toReal := by
  have hcard : t.card ≤ hfin.toFinset.card :=
    Finset.card_le_card (fun x hx => hfin.mem_toFinset.mpr (ht (by simpa using hx)))
  have hvol : clusterVol ω o = (hfin.toFinset.card : ℝ≥0∞) := by
    rw [clusterVol_eq_encard]
    norm_cast
    exact hfin.encard_eq_coe_toFinset_card
  rw [hvol, ENNReal.toReal_natCast]
  exact_mod_cast hcard

/-- Opening every edge of a simple path of length `n - 1` puts either at least
`n` vertices in the origin's finite cluster or the origin in an infinite cluster. -/
theorem allOpen_path_subset_tailOrInfinite
    {o v : V} (p : (⊤ : SimpleGraph V).Walk o v) (hp : p.IsPath)
    {n : ℕ} (hn : n = p.length + 1) (s : Finset (Sym2 V))
    (hs : ∀ e ∈ p.edges, e ∈ s) :
    {ω : Config V | ∀ e ∈ s, e ∈ ω} ⊆ tailOrInfinite (n := (n : ℝ)) o := by
  classical
  intro ω hω
  change (n : ℝ) ≤ (clusterVol ω o).toReal ∨ InInfiniteCluster ω o
  by_cases hi : InInfiniteCluster ω o
  · exact Or.inr hi
  · refine Or.inl ?_
    have hfin : (cluster ω o).Finite :=
      Set.not_infinite.mp (fun h => hi ((inInfiniteCluster_iff_infinite ω o).mpr h))
    have hconn : ∀ x ∈ p.support, Connects ω o x := by
      intro x hx
      rw [← pathConnects_iff]
      refine ⟨p.takeUntil x hx, ?_⟩
      intro e he
      exact hω e (hs e (p.edges_takeUntil_subset_edges hx he))
    have htsub : (p.support.toFinset : Set V) ⊆ cluster ω o := by
      intro x hx
      rw [mem_cluster_iff]
      exact hconn x (by simpa using hx)
    have hsuppc : p.support.toFinset.card = p.length + 1 := by
      rw [List.toFinset_card_of_nodup (p.isPath_def.mp hp), p.length_support]
    have hcard : n ≤ p.support.toFinset.card := hn.le.trans_eq hsuppc.symm
    have hcardR : (n : ℝ) ≤ (p.support.toFinset.card : ℝ) := by exact_mod_cast hcard
    exact hcardR.trans (card_le_clusterVol_toReal hfin htsub)

/-- A simple path of length `n - 1` with positive edge-opening probabilities
forces the level-`n` real volume tail to have positive probability. Almost-sure
finiteness removes the infinite part of the enlarged event without changing
its measure. -/
theorem volumeLaw_tail_pos_of_path (π : Sym2 V → unitInterval)
    {o v : V} (p : (⊤ : SimpleGraph V).Walk o v) (hp : p.IsPath)
    {n : ℕ} (hn : n = p.length + 1)
    (hπ : ∀ e ∈ p.edges, 0 < (π e : ℝ))
    (hfin : ∀ᵐ ω ∂edgeMeasure π, clusterVol ω o ≠ ⊤) :
    0 < (volumeLaw π o (Ici (n : ℝ))).toReal := by
  classical
  rw [volumeLaw_tail_eq_tailEvent]
  apply ENNReal.toReal_pos
  · have hopen : 0 < edgeMeasure π {ω : Config V | ∀ e ∈ p.edges.toFinset, e ∈ ω} := by
      rw [edgeMeasure_cylinder]
      apply pos_iff_ne_zero.mpr
      rw [Finset.prod_ne_zero_iff]
      intro e he
      have hπe : 0 < (π e : ℝ) := hπ e (List.mem_toFinset.mp he)
      have hpos : 0 < ((unitInterval.toNNReal (π e)) : ℝ≥0∞) := by
        rw [ENNReal.coe_pos]
        exact_mod_cast hπe
      exact hpos.ne'
    have htail : 0 < edgeMeasure π (tailOrInfinite (n := (n : ℝ)) o) :=
      hopen.trans_le (measure_mono (allOpen_path_subset_tailOrInfinite p hp hn _
        (fun e he => List.mem_toFinset.mpr he)))
    have heq : tailOrInfinite (n := (n : ℝ)) o =ᵐ[edgeMeasure π]
        tailEvent (n := (n : ℝ)) o := by
      filter_upwards [hfin] with ω hω
      by_cases h : (n : ℝ) ≤ (clusterVol ω o).toReal
      · simp [tailOrInfinite, tailEvent, h]
      · have hi : ¬ InInfiniteCluster ω o := hω
        simp [tailOrInfinite, tailEvent, h, hi]
    rw [measure_congr heq] at htail
    exact htail.ne'
  · exact measure_ne_top _ _

/-- The graph-theoretic input sufficient for positive volume tails at every
positive natural level: for each `n ≥ 1`, there is a simple path with `n`
support vertices and positive opening probability on every edge. -/
def ArbitrarilyLongPositivePaths (π : Sym2 V → unitInterval) (o : V) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ (v : V) (p : (⊤ : SimpleGraph V).Walk o v),
    p.IsPath ∧ n = p.length + 1 ∧ ∀ e ∈ p.edges, 0 < (π e : ℝ)

/-- Discharge the all-natural tail-positivity premise from finite open paths. -/
theorem volumeLaw_nat_tail_pos (π : Sym2 V → unitInterval) (o : V)
    (hpaths : ArbitrarilyLongPositivePaths π o)
    (hfin : ∀ᵐ ω ∂edgeMeasure π, clusterVol ω o ≠ ⊤) :
    ∀ n : ℕ, 1 ≤ n → 0 < (volumeLaw π o (Ici (n : ℝ))).toReal := by
  intro n hn
  obtain ⟨v, p, hp, hlen, hπ⟩ := hpaths n hn
  exact volumeLaw_tail_pos_of_path π p hp hlen hπ hfin

namespace PositivePaths

variable {V : Type*} [Countable V] [AddCommGroup V]

/-- Repeated unit steps in a fixed nonzero direction. -/
def repeatedStepWalk (o d : V) (hd : d ≠ 0) : ∀ n : ℕ,
    (⊤ : SimpleGraph V).Walk o (o + n • d)
  | 0 => (SimpleGraph.Walk.nil : (⊤ : SimpleGraph V).Walk o o).copy rfl (by simp)
  | n + 1 => by
      have hstep : (⊤ : SimpleGraph V).Adj (o + n • d) (o + n • d + d) := by
        rw [SimpleGraph.top_adj]
        intro heq
        apply hd
        apply add_left_cancel (a := o + n • d)
        simpa [add_assoc] using heq.symm
      exact ((repeatedStepWalk o d hd n).concat hstep).copy rfl
        (by simp only [add_nsmul, one_nsmul, add_assoc])

omit [Countable V] in
theorem repeatedStepWalk_length (o d : V) (hd : d ≠ 0) (n : ℕ) :
    (repeatedStepWalk o d hd n).length = n := by
  induction n with
  | zero => simp [repeatedStepWalk]
  | succ n ih =>
      rw [repeatedStepWalk, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_concat, ih]

omit [Countable V] in
theorem repeatedStepWalk_support (o d : V) (hd : d ≠ 0) (n : ℕ) :
    (repeatedStepWalk o d hd n).support =
      (List.range (n + 1)).map (fun k => o + k • d) := by
  induction n with
  | zero => simp [repeatedStepWalk]
  | succ n ih =>
      have hlast : o + n • d + d = o + (n + 1) • d := by
        simp only [add_nsmul, one_nsmul, add_assoc]
      simp only [repeatedStepWalk, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_concat, ih, List.range_succ, List.map_append,
        List.map_singleton, hlast]

omit [Countable V] in
theorem repeatedStepWalk_edges (o d : V) (hd : d ≠ 0) (n : ℕ) :
    (repeatedStepWalk o d hd n).edges =
      (List.range n).map (fun k => s(o + k • d, o + (k + 1) • d)) := by
  induction n with
  | zero => simp [repeatedStepWalk]
  | succ n ih =>
      have hlast : o + n • d + d = o + (n + 1) • d := by
        simp only [add_nsmul, one_nsmul, add_assoc]
      simp only [repeatedStepWalk, SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_concat, ih, List.range_succ, List.map_append,
        List.map_singleton, hlast, List.concat_eq_append]

theorem repeatedStepWalk_isPath (o d : V) (hd : d ≠ 0)
    (hinj : Function.Injective (fun k : ℕ => o + k • d)) (n : ℕ) :
    (repeatedStepWalk o d hd n).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, repeatedStepWalk_support]
  exact List.nodup_range.map hinj

theorem arbitrarilyLongPositivePaths_of_step (π : Sym2 V → unitInterval)
    (o d : V) (hd : d ≠ 0)
    (hinj : Function.Injective (fun k : ℕ => o + k • d))
    (hpos : ∀ k : ℕ, 0 < (π s(o + k • d, o + (k + 1) • d) : ℝ)) :
    ArbitrarilyLongPositivePaths π o := by
  intro n hn
  refine ⟨o + (n - 1) • d, repeatedStepWalk o d hd (n - 1),
    repeatedStepWalk_isPath o d hd hinj (n - 1), ?_, ?_⟩
  · rw [repeatedStepWalk_length]
    omega
  · intro e he
    rw [repeatedStepWalk_edges] at he
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp he
    exact hpos k

theorem arbitrarilyLongPositivePaths_of_translationInvariant
    (π : Sym2 V → unitInterval) (o d : V) (hd : d ≠ 0)
    (hinj : Function.Injective (fun k : ℕ => o + k • d))
    (hpos : 0 < (π s(0, d) : ℝ))
    (htrans : ∀ a x y : V, π s(a + x, a + y) = π s(x, y)) :
    ArbitrarilyLongPositivePaths π o := by
  apply arbitrarilyLongPositivePaths_of_step π o d hd hinj
  intro k
  have heq : s(o + k • d, o + (k + 1) • d) =
      s((o + k • d) + 0, (o + k • d) + d) := by
    simp only [add_zero, add_nsmul, one_nsmul, add_assoc]
  rw [heq, htrans]
  exact hpos

end PositivePaths

end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.card_le_clusterVol_toReal
#print axioms PercLib.CriticalLRP.allOpen_path_subset_tailOrInfinite
#print axioms PercLib.CriticalLRP.volumeLaw_tail_pos_of_path
#print axioms PercLib.CriticalLRP.ArbitrarilyLongPositivePaths
#print axioms PercLib.CriticalLRP.volumeLaw_nat_tail_pos
#print axioms PercLib.CriticalLRP.PositivePaths.repeatedStepWalk
#print axioms PercLib.CriticalLRP.PositivePaths.repeatedStepWalk_length
#print axioms PercLib.CriticalLRP.PositivePaths.repeatedStepWalk_support
#print axioms PercLib.CriticalLRP.PositivePaths.repeatedStepWalk_edges
#print axioms PercLib.CriticalLRP.PositivePaths.repeatedStepWalk_isPath
#print axioms PercLib.CriticalLRP.PositivePaths.arbitrarilyLongPositivePaths_of_step
#print axioms PercLib.CriticalLRP.PositivePaths.arbitrarilyLongPositivePaths_of_translationInvariant
