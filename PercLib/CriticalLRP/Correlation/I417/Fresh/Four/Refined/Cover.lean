/-
Independently rebuilt and integrated from the accepted `smwx8o5tv/m2` artifact
`.ultramath/smwx8o5tv/m2/Q4`. Production integration revision:
`89f3b5eed8eb492ac975beb090e1d5e2fd9685ba`. Definitions, including `Diag`
and `baseDiag`, are confined to `Defs.lean`; the remaining files prove their
properties and the q=4 cover/BK bound, not its weighted moment evaluation.
-/
/-
Independently built for swarm `smwx8o5tv`, member `m2`, direction Q4-FINITE-COVER.
No production files are modified; this module is read-only against production.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Four.Refined.Attach

/-!
# Lemma I.4.17 at `q = 4`: the cover, assembled

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (supplied paper text lines 2444--2464).

The three attachment rounds, one per remaining labelled arm, starting from the two halves of the
selected path.  Each round first-hits the new arm's path against the whole of the diagram built so
far (`PercLib.CriticalLRP.exists_first_hit`) and then applies `step`.  The legs carry the invariant
that their leftmost leg still starts at the pin `y`, which is what keeps `y` a vertex of the diagram
(and hence a legitimate target for the next first hit) at every stage.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFour.Refined

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- The leftmost leg keeps its source when a leg is split: the slot of the split leg is reused for
the half that keeps its source.  This is what carries the pin `y` through the attachment rounds. -/
theorem splitAt_left {ι : Type*} [DecidableEq ι] {L : ι → V × V} {y : V} {l : ι}
    (hl : (L l).1 = y) (k : ι) (z d : V) :
    ((splitAt L k z d) (Sum.inl l)).1 = y := by
  by_cases h : l = k
  · rw [h] at hl ⊢
    rw [splitAt_inl_self]
    exact hl
  · rw [splitAt_inl_of_ne h]
    exact hl

/-- **The `q = 4` mark-on-the-path fresh cover.**  For every configuration of the fresh marked
event with four labelled arms, every choice of the selected arm `j : Fin 4` and every ordering
`i₁, i₂, i₃` of the three remaining labels, one of the eight-leg diagrams of `q4Shape` occurs with
all eight witnesses pairwise edge-disjoint.

No distinctness of the labels is needed, and the attachment vertices `z1, z2, z3` may coincide with
any vertex of the diagram or with the arms: coincident arms, `w = y`, `w = g j` and trivial legs are
all absorbed. -/
theorem freshMark_subset_q4Shape (y w : V) (g : Fin 4 → V) (j i1 i2 i3 : Fin 4) :
    I417Gen.freshMark y g j w ⊆ q4Shape y w (g j) (g i1) (g i2) (g i3) := by
  classical
  rintro ω ⟨hDO, hlab⟩
  obtain ⟨s, t, hs, ht, hst, hys, hwt⟩ := hDO
  obtain ⟨p0, hp0⟩ := pathConnects_iff.mpr hys
  obtain ⟨r0, hr0⟩ := pathConnects_iff.mpr hwt
  -- the two halves of the selected path, as paths
  set P : (⊤ : SimpleGraph V).Walk y w := p0.bypass with hP
  set R : (⊤ : SimpleGraph V).Walk w (g j) := r0.bypass with hR
  have hPsub : ∀ e ∈ P.edges, e ∈ (s : Set (Sym2 V)) :=
    fun e he => hp0 e (SimpleGraph.Walk.edges_bypass_subset_edges p0 he)
  have hRsub : ∀ e ∈ R.edges, e ∈ (t : Set (Sym2 V)) :=
    fun e he => hr0 e (SimpleGraph.Walk.edges_bypass_subset_edges r0 he)
  have hPop : ∀ e ∈ P.edges, e ∈ ω := fun e he => hs (hPsub e he)
  have hRop : ∀ e ∈ R.edges, e ∈ ω := fun e he => ht (hRsub e he)
  have hPR : Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset R.edges) := by
    rw [Finset.disjoint_left]
    intro e he he'
    exact Finset.disjoint_left.mp hst (hPsub e (I417Example.mem_edgeFinset.mp he))
      (hRsub e (I417Example.mem_edgeFinset.mp he'))
  have hD0 : Diag (Fin 2) ω (baseLegs y w (g j)) :=
    baseDiag (SimpleGraph.Walk.bypass_isPath p0) (SimpleGraph.Walk.bypass_isPath r0)
      hPop hRop hPR
  -- the arms lie in the cluster of `y`
  rw [I417A.labelEvent_eq_iInter] at hlab
  have harm1 : Connects ω y (g i1) := Set.mem_iInter.mp hlab i1
  have harm2 : Connects ω y (g i2) := Set.mem_iInter.mp hlab i2
  have harm3 : Connects ω y (g i3) := Set.mem_iInter.mp hlab i3
  -- the leftmost leg starts at `y`, so `y` is a vertex of the diagram
  have hl0 : ((baseLegs y w (g j)) 0).1 = y := rfl
  have hyU0 : y ∈ ⋃ i, {v : V | v ∈ (hD0.W i).2.support} := by
    refine Set.mem_iUnion.mpr ⟨(0 : Fin 2), ?_⟩
    have h1 : (hD0.W 0).1.1 = y := by rw [hD0.legs_eq 0]; exact hl0
    exact mem_support_start (hD0.W 0).2 h1
  -- ===== first arm =====
  obtain ⟨r1, hr1⟩ := pathConnects_iff.mpr (connects_symm harm1)
  obtain ⟨z1, Q1, hz1, hQ1op, hQ1supp⟩ :=
    exists_first_hit r1 hr1 (⋃ i, {v : V | v ∈ (hD0.W i).2.support}) hyU0
  have hQ1reg : ∀ e ∈ Q1.edges, ∀ v ∈ e,
      v ∈ ({z1} ∪ (⋃ i, {v : V | v ∈ (hD0.W i).2.support})ᶜ) := by
    intro e he v hv
    rcases hQ1supp v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e, he, hv⟩)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨k1, ⟨D1⟩⟩ := step hD0 hz1 Q1 hQ1op hQ1reg
  have hl1 : ((splitAt (baseLegs y w (g j)) k1 z1 (g i1)) (Sum.inl (0 : Fin 2))).1 = y :=
    splitAt_left hl0 k1 z1 (g i1)
  have hyU1 : y ∈ ⋃ i, {v : V | v ∈ (D1.W i).2.support} := by
    refine Set.mem_iUnion.mpr ⟨(Sum.inl (0 : Fin 2)), ?_⟩
    have h1 : (D1.W (Sum.inl (0 : Fin 2))).1.1 = y := by rw [D1.legs_eq]; exact hl1
    exact mem_support_start (D1.W (Sum.inl (0 : Fin 2))).2 h1
  -- ===== second arm =====
  obtain ⟨r2, hr2⟩ := pathConnects_iff.mpr (connects_symm harm2)
  obtain ⟨z2, Q2, hz2, hQ2op, hQ2supp⟩ :=
    exists_first_hit r2 hr2 (⋃ i, {v : V | v ∈ (D1.W i).2.support}) hyU1
  have hQ2reg : ∀ e ∈ Q2.edges, ∀ v ∈ e,
      v ∈ ({z2} ∪ (⋃ i, {v : V | v ∈ (D1.W i).2.support})ᶜ) := by
    intro e he v hv
    rcases hQ2supp v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e, he, hv⟩)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨k2, ⟨D2⟩⟩ := step D1 hz2 Q2 hQ2op hQ2reg
  have hl2 : ((splitAt (splitAt (baseLegs y w (g j)) k1 z1 (g i1)) k2 z2 (g i2))
      (Sum.inl (Sum.inl (0 : Fin 2)))).1 = y :=
    splitAt_left hl1 k2 z2 (g i2)
  have hyU2 : y ∈ ⋃ i, {v : V | v ∈ (D2.W i).2.support} := by
    refine Set.mem_iUnion.mpr ⟨(Sum.inl (Sum.inl (0 : Fin 2))), ?_⟩
    have h1 : (D2.W (Sum.inl (Sum.inl (0 : Fin 2)))).1.1 = y := by rw [D2.legs_eq]; exact hl2
    exact mem_support_start (D2.W (Sum.inl (Sum.inl (0 : Fin 2)))).2 h1
  -- ===== third arm =====
  obtain ⟨r3, hr3⟩ := pathConnects_iff.mpr (connects_symm harm3)
  obtain ⟨z3, Q3, hz3, hQ3op, hQ3supp⟩ :=
    exists_first_hit r3 hr3 (⋃ i, {v : V | v ∈ (D2.W i).2.support}) hyU2
  have hQ3reg : ∀ e ∈ Q3.edges, ∀ v ∈ e,
      v ∈ ({z3} ∪ (⋃ i, {v : V | v ∈ (D2.W i).2.support})ᶜ) := by
    intro e he v hv
    rcases hQ3supp v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e, he, hv⟩)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨k3, ⟨D3⟩⟩ := step D2 hz3 Q3 hQ3op hQ3reg
  -- ===== membership in the `q = 4` family =====
  refine Set.mem_iUnion.mpr ⟨k1, Set.mem_iUnion.mpr ⟨k2, Set.mem_iUnion.mpr ⟨k3,
    Set.mem_iUnion.mpr ⟨z1, Set.mem_iUnion.mpr ⟨z2, Set.mem_iUnion.mpr ⟨z3, ?_⟩⟩⟩⟩⟩⟩
  have hL : (fun i => (D3.W i).1) =
      q4Legs k1 k2 k3 z1 z2 z3 y w (g j) (g i1) (g i2) (g i3) :=
    funext D3.legs_eq
  rw [← hL]
  exact shapeOfI_of_diag D3

end PercLib.CriticalLRP.I417FreshFour.Refined
