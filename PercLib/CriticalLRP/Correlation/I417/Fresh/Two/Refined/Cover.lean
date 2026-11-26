/-
Independently rebuilt and integrated from the accepted `smwx5p94b/m1` artifact
`.ultramath/smwx5p94b/m1/M1Fresh`. Production integration revision:
`9c345df8dcb6d4027a2e61d7a7785abf4df111cf`. The coordinator assigns the production
namespace and fully qualified imports; the mathematical statements are unchanged.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Refined.Defs

/-!
Independently built for swarm `smwx5p94b`, member `m1`, direction Q2-FRESH-NORMALIZATION.

# The `q = 2` fresh-side four-edge cover

Source: T. Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.17 (supplied PDF p. 45): "Expanding each of these
probabilities out as in the proof of the tree-graph inequality yields the claim: we obtain a bound
in terms of tree diagrams with two pinned vertices at `x` and `y`, with `2p + 2q + 1` edges in
total, some number `3 ≤ ℓ ≤ p + q + 1` of which belong to the path connecting `x` and `y`."

The fresh copy contributes `2q` of those edges.  At `q = 2` that is four: the rooted binary tree
with the two labelled arms as leaves has three edges, and the mark `w` *subdivides* one of them
because the event places `w` on the open path from `y` to the arm `g j`.  The replacement of the
mark-as-last-leaf reading (`hubStar`, five edges at `q = 2`) by this subdivision is a saving of
exactly one two-point factor, hence of one power of `T` or of `χ`.

Deterministic content (`exists_refined_branch`): on `freshMark y g j w` with `j = 0`, take the
edge-disjoint open halves `A : y → w` and `R : w → g 0` supplied by the disjoint occurrence, put
`S = supp A ∪ supp R`, and first-hit a walk `g 1 → y` against `S` at a vertex `p`.  Then

* if `p ∈ supp A`: the four walks `A↑p`, `A↓p`, `R`, `Q` are `y→p`, `p→w`, `w→g 0`, `p→g 1`,
  pairwise edge-disjoint (`ShapeA`), where `A↑p`, `A↓p` split `A` at `p`;
* if `p ∈ supp R`: the four walks `A`, `R↑p`, `R↓p`, `Q` are `y→w`, `w→p`, `p→g 0`, `p→g 1`,
  pairwise edge-disjoint (`ShapeB`).

The `j = 1` case is the same statement with the two arm labels exchanged (the `labelEvent` is
symmetric).  Fourfold BK then bounds each shape by four two-point factors.
-/
open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshTwo.Refined

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Example

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## Assembling a four-edge diagram from four walks -/

/-- Four walks made of open edges whose edge sets are pairwise disjoint realise the fourfold
disjoint occurrence of the four connection events. -/
theorem tree4_mem_of_walks {ω : Config V} {a b c d e f g h : V}
    {p₁ : (⊤ : SimpleGraph V).Walk a b} {p₂ : (⊤ : SimpleGraph V).Walk c d}
    {p₃ : (⊤ : SimpleGraph V).Walk e f} {p₄ : (⊤ : SimpleGraph V).Walk g h}
    (m₁ : ∀ x ∈ p₁.edges, x ∈ ω) (m₂ : ∀ x ∈ p₂.edges, x ∈ ω)
    (m₃ : ∀ x ∈ p₃.edges, x ∈ ω) (m₄ : ∀ x ∈ p₄.edges, x ∈ ω)
    (d₁₂ : Disjoint (edgeFinset p₁.edges) (edgeFinset p₂.edges))
    (d₁₃ : Disjoint (edgeFinset p₁.edges) (edgeFinset p₃.edges))
    (d₁₄ : Disjoint (edgeFinset p₁.edges) (edgeFinset p₄.edges))
    (d₂₃ : Disjoint (edgeFinset p₂.edges) (edgeFinset p₃.edges))
    (d₂₄ : Disjoint (edgeFinset p₂.edges) (edgeFinset p₄.edges))
    (d₃₄ : Disjoint (edgeFinset p₃.edges) (edgeFinset p₄.edges)) :
    Tree4 (connSet a b) (connSet c d) (connSet e f) (connSet g h) ω := by
  classical
  refine ⟨![edgeFinset p₁.edges, edgeFinset p₂.edges, edgeFinset p₃.edges,
    edgeFinset p₄.edges], ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · intro x hx; exact m₁ x (mem_edgeFinset.mp hx)
    · intro x hx; exact m₂ x (mem_edgeFinset.mp hx)
    · intro x hx; exact m₃ x (mem_edgeFinset.mp hx)
    · intro x hx; exact m₄ x (mem_edgeFinset.mp hx)
  · intro k
    fin_cases k
    · exact pathConnects_iff.mp ⟨p₁, fun x hx => mem_edgeFinset.mpr hx⟩
    · exact pathConnects_iff.mp ⟨p₂, fun x hx => mem_edgeFinset.mpr hx⟩
    · exact pathConnects_iff.mp ⟨p₃, fun x hx => mem_edgeFinset.mpr hx⟩
    · exact pathConnects_iff.mp ⟨p₄, fun x hx => mem_edgeFinset.mpr hx⟩
  · intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all [disjoint_comm]

/-! ## The deterministic four-edge branch -/

/-- Splitting one walk in two: the two halves have disjoint edge sets. -/
theorem edgeFinset_takeUntil_disjoint_dropUntil {u v : V} (P : (⊤ : SimpleGraph V).Walk u v)
    (hP : P.IsPath) {z : V} (hz : z ∈ P.support) :
    Disjoint (edgeFinset (P.takeUntil z hz).edges) (edgeFinset (P.dropUntil z hz).edges) := by
  classical
  have hconcat : (P.takeUntil z hz).edges ++ (P.dropUntil z hz).edges = P.edges := by
    rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
  have hd : ((P.takeUntil z hz).edges ++ (P.dropUntil z hz).edges).Nodup := by
    rw [hconcat]; exact hP.isTrail.edges_nodup
  exact edgeFinset_disjoint_of_list_disjoint (List.nodup_append'.mp hd).2.2

/-- **The four-edge fresh branch.**  If the mark `w` and the arm `g 0` are connected by an open
path whose two halves at `w` are edge-disjoint, and the other arm `g 1` is connected to `y`, then
one of the two four-edge shapes holds: the spine `y → p → w` with the arms at `w` and `p`
(`ShapeA`), or the spine `y → w → p` with both arms at `p` (`ShapeB`). -/
theorem exists_refined_branch {ω : Config V} {y w g0 g1 : V}
    (hDO : ω ∈ Percolation.DisjointOccurrence (connSet y w) (connSet w g0))
    (h1 : Connects ω y g1) :
    (∃ p : V, ShapeA y w g0 g1 p ω) ∨ (∃ p : V, ShapeB y w g0 g1 p ω) := by
  classical
  obtain ⟨s, t, hs, ht, hst, hAs, hBt⟩ := hDO
  -- the two edge-disjoint open halves of the fresh path
  obtain ⟨p0, hp0⟩ := pathConnects_iff.mpr hAs
  obtain ⟨r0, hr0⟩ := pathConnects_iff.mpr hBt
  set P : (⊤ : SimpleGraph V).Walk y w := p0.bypass with hPdef
  set R : (⊤ : SimpleGraph V).Walk w g0 := r0.bypass with hRdef
  have hPpath : P.IsPath := SimpleGraph.Walk.bypass_isPath p0
  have hRpath : R.IsPath := SimpleGraph.Walk.bypass_isPath r0
  have hPsub : ∀ e ∈ P.edges, e ∈ s :=
    fun e he => hp0 e (SimpleGraph.Walk.edges_bypass_subset_edges p0 he)
  have hRsub : ∀ e ∈ R.edges, e ∈ t :=
    fun e he => hr0 e (SimpleGraph.Walk.edges_bypass_subset_edges r0 he)
  have hPedges : ∀ e ∈ P.edges, e ∈ ω := fun e he => hs (hPsub e he)
  have hRedges : ∀ e ∈ R.edges, e ∈ ω := fun e he => ht (hRsub e he)
  -- the first hit of the other arm against the two halves
  set S : Set V := {v | v ∈ P.support ∨ v ∈ R.support} with hSdef
  have hyS : y ∈ S := Or.inl (SimpleGraph.Walk.start_mem_support P)
  obtain ⟨r1, hr1⟩ := pathConnects_iff.mpr (connects_symm h1)
  obtain ⟨p, Q0, hpS, hQ0edges, hQ0supp⟩ := exists_first_hit r1 hr1 S hyS
  set Q : (⊤ : SimpleGraph V).Walk p g1 := Q0.bypass with hQdef
  have hQpath : Q.IsPath := SimpleGraph.Walk.bypass_isPath Q0
  have hQedges : ∀ e ∈ Q.edges, e ∈ ω :=
    fun e he => hQ0edges e (SimpleGraph.Walk.edges_bypass_subset_edges Q0 he)
  have hQsupp : ∀ v ∈ Q.support, v = p ∨ v ∉ S :=
    fun v hv => hQ0supp v (SimpleGraph.Walk.support_bypass_subset_support Q0 hv)
  -- region membership of the two halves
  have hPinS : ∀ e ∈ P.edges, ∀ v ∈ e, v ∈ S :=
    fun e he v hv =>
      Or.inl (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩))
  have hRinS : ∀ e ∈ R.edges, ∀ v ∈ e, v ∈ S :=
    fun e he v hv =>
      Or.inr (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩))
  -- region membership of the arm
  have hQinU : ∀ e ∈ Q.edges, ∀ v ∈ e, v ∈ ({p} : Set V) ∪ Sᶜ := by
    intro e he v hv
    rcases hQsupp v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e, he, hv⟩)) with h | h
    · subst h; exact Or.inl (by simp)
    · exact Or.inr h
  have hSU : ∀ v ∈ S, v ∈ ({p} : Set V) ∪ Sᶜ → v = p := by
    rintro v _ (h | h)
    · simpa using h
    · exact absurd ‹v ∈ S› h
  have hQinS : ∀ v ∈ ({p} : Set V) ∪ Sᶜ, v ∈ S → v = p := by
    rintro v (h | h) hS
    · simpa using h
    · exact absurd hS h
  rcases hpS with hpP | hpR
  · -- ===== case A: the arm meets the `y → w` half at `p` =====
    have hAinS : ∀ e ∈ (P.takeUntil p hpP).edges, ∀ v ∈ e, v ∈ S :=
      fun e he v hv =>
        hPinS e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hpP he) v hv
    have hBinS : ∀ e ∈ (P.dropUntil p hpP).edges, ∀ v ∈ e, v ∈ S :=
      fun e he v hv =>
        hPinS e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hpP he) v hv
    have hAsub : ∀ e ∈ (P.takeUntil p hpP).edges, e ∈ s :=
      fun e he => hPsub e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hpP he)
    have hBsub : ∀ e ∈ (P.dropUntil p hpP).edges, e ∈ s :=
      fun e he => hPsub e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hpP he)
    have hAB : Disjoint (edgeFinset (P.takeUntil p hpP).edges)
        (edgeFinset (P.dropUntil p hpP).edges) :=
      edgeFinset_takeUntil_disjoint_dropUntil P hPpath hpP
    have hA_R : Disjoint (edgeFinset (P.takeUntil p hpP).edges) (edgeFinset R.edges) := by
      rw [Finset.disjoint_left]
      intro e he he'
      exact Finset.disjoint_left.mp hst (hAsub e (mem_edgeFinset.mp he))
        (hRsub e (mem_edgeFinset.mp he'))
    have hB_R : Disjoint (edgeFinset (P.dropUntil p hpP).edges) (edgeFinset R.edges) := by
      rw [Finset.disjoint_left]
      intro e he he'
      exact Finset.disjoint_left.mp hst (hBsub e (mem_edgeFinset.mp he))
        (hRsub e (mem_edgeFinset.mp he'))
    refine Or.inl ⟨p, ?_⟩
    exact tree4_mem_of_walks
      (p₁ := P.takeUntil p hpP) (p₂ := P.dropUntil p hpP) (p₃ := R) (p₄ := Q)
      (fun e he => hPedges e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hpP he))
      (fun e he => hPedges e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hpP he))
      hRedges hQedges
      hAB hA_R
      (edges_disjoint_of_regions hAinS hQinU hSU)
      hB_R
      (edges_disjoint_of_regions hBinS hQinU hSU)
      (edges_disjoint_of_regions hRinS hQinU hSU)
  · -- ===== case B: the arm meets the `w → g 0` half at `p` =====
    have hEinS : ∀ e ∈ (R.takeUntil p hpR).edges, ∀ v ∈ e, v ∈ S :=
      fun e he v hv =>
        hRinS e (SimpleGraph.Walk.edges_takeUntil_subset_edges R hpR he) v hv
    have hFinS : ∀ e ∈ (R.dropUntil p hpR).edges, ∀ v ∈ e, v ∈ S :=
      fun e he v hv =>
        hRinS e (SimpleGraph.Walk.edges_dropUntil_subset_edges R hpR he) v hv
    have hEsub : ∀ e ∈ (R.takeUntil p hpR).edges, e ∈ t :=
      fun e he => hRsub e (SimpleGraph.Walk.edges_takeUntil_subset_edges R hpR he)
    have hFsub : ∀ e ∈ (R.dropUntil p hpR).edges, e ∈ t :=
      fun e he => hRsub e (SimpleGraph.Walk.edges_dropUntil_subset_edges R hpR he)
    have hEF : Disjoint (edgeFinset (R.takeUntil p hpR).edges)
        (edgeFinset (R.dropUntil p hpR).edges) :=
      edgeFinset_takeUntil_disjoint_dropUntil R hRpath hpR
    have hP_E : Disjoint (edgeFinset P.edges) (edgeFinset (R.takeUntil p hpR).edges) := by
      rw [Finset.disjoint_left]
      intro e he he'
      exact Finset.disjoint_left.mp hst (hPsub e (mem_edgeFinset.mp he))
        (hEsub e (mem_edgeFinset.mp he'))
    have hP_F : Disjoint (edgeFinset P.edges) (edgeFinset (R.dropUntil p hpR).edges) := by
      rw [Finset.disjoint_left]
      intro e he he'
      exact Finset.disjoint_left.mp hst (hPsub e (mem_edgeFinset.mp he))
        (hFsub e (mem_edgeFinset.mp he'))
    refine Or.inr ⟨p, ?_⟩
    exact tree4_mem_of_walks
      (p₁ := P) (p₂ := R.takeUntil p hpR) (p₃ := R.dropUntil p hpR) (p₄ := Q)
      hPedges
      (fun e he => hRedges e (SimpleGraph.Walk.edges_takeUntil_subset_edges R hpR he))
      (fun e he => hRedges e (SimpleGraph.Walk.edges_dropUntil_subset_edges R hpR he))
      hQedges
      hP_E hP_F
      (edges_disjoint_of_regions hPinS hQinU hSU)
      hEF
      (edges_disjoint_of_regions hEinS hQinU hSU)
      (edges_disjoint_of_regions hFinS hQinU hSU)

/-! ## Fourfold BK and the per-arm probability bound -/

/-- Fourfold BK for four-edge tree diagrams. -/
theorem tree4_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (A B C D : Set (Config V)) (hA : IsUpperSet A) (hB : IsUpperSet B) (hC : IsUpperSet C)
    (hD : IsUpperSet D) (fA : Percolation.FiniteWitness A) (fB : Percolation.FiniteWitness B)
    (fC : Percolation.FiniteWitness C) (fD : Percolation.FiniteWitness D) :
    (edgeMeasure π) (Tree4 A B C D) ≤
      (edgeMeasure π) A * (edgeMeasure π) B * (edgeMeasure π) C * (edgeMeasure π) D := by
  have hU : ∀ i : Fin 4, IsUpperSet (![A, B, C, D] i) := by
    intro i
    fin_cases i <;> simpa using ‹_›
  have hF : ∀ i : Fin 4, Percolation.FiniteWitness (![A, B, C, D] i) := by
    intro i
    fin_cases i <;> simpa using ‹_›
  have h := bk_fin_ennreal π hπ (fun i : Fin 4 => ![A, B, C, D] i) hU hF
  have hprod : (∏ i : Fin 4, (edgeMeasure π) (![A, B, C, D] i)) =
      (edgeMeasure π) A * (edgeMeasure π) B * (edgeMeasure π) C * (edgeMeasure π) D := by
    simp [Fin.prod_univ_four]
  rw [hprod] at h
  exact h

end PercLib.CriticalLRP.I417FreshTwo.Refined
