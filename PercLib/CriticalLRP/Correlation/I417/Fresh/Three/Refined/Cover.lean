/-
Independently reviewed and integrated from the completed artifact `smwx6p0op/m1`
at `.ultramath/smwx6p0op/m1/M3Q`. Production integration revision:
`3cd318e5a37d0dc889f23bd3baf1b8884e651a27`. The coordinator uses the production
namespace and fully qualified imports; the proof covers `q = 3`, not arbitrary `q`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Three.Refined.Defs

/-!
Independently built for swarm `smwx6p0op`, member `m1`, direction Q3-MARK-ON-PATH-COVER.

# The `q = 3` mark-on-the-path fresh cover

Source: T. Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.17 (paper text lines 2444--2464): the fresh-copy
probability expands into rooted binary trees with the pin `y` at the root and the `q` labelled arms
as leaves, with the mark `w` subdividing one edge of the path from `y` to the selected arm, and
`2p + 2q + 1` edges in total.

This file proves the deterministic content at `q = 3`, for **all three arm labels and every choice
of the selected arm** `j`, with **arbitrary coincident positions**: from a configuration of
`freshMark y g j w` (the disjoint occurrence of the two halves `y → w`, `w → g j`, together with all
three arms in the fresh cluster) one of the eight six-edge subdivided binary trees of
`legsA0`--`legsB3` occurs, with all six witnesses pairwise edge-disjoint.

Method (the `q = 2` first-hit method of swarm `smwx5p94b` iterated once more, preserving *both*
halves of the selected path and all three labelled arms):

1. `A : y → w` and `R : w → g j` are the edge-disjoint open halves, `S = supp A ∪ supp R`;
2. first-hit a walk `g i₁ → y` against `S` at `p`, splitting `A` or `R` at `p` (this is the whole
   `q = 2` cover, four segments);
3. first-hit a walk `g i₂ → y` against `S₂ = S ∪ supp (p → g i₁)` at `q`; the hit point `q` lies on
   one of the four segments, and splitting *that* segment at `q` produces the two extra legs plus
   the third arm's leg: six legs in all.

Splitting a segment at a point of its support costs nothing (trivial walks allowed), so the
argument is uniform in all degeneracies: `w = y`, `w = g j`, coincident arms, `p` or `q` at an
endpoint, and the third arm attaching at an already existing vertex.

No definitions, no `sorry`, no custom axioms.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshThree.Refined

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## Assembling a six-leg diagram from six walks -/

/-- Six open walks with pairwise disjoint edge sets realise the six-fold disjoint occurrence of
their six connection events. -/
theorem shapeOf_mem_of_walks {L : Fin 6 → V × V} {ω : Config V}
    (p : (i : Fin 6) → (⊤ : SimpleGraph V).Walk (L i).1 (L i).2)
    (hopen : ∀ i, ∀ e ∈ (p i).edges, e ∈ ω)
    (hdisj : ∀ i j : Fin 6, i ≠ j →
      Disjoint (I417Example.edgeFinset (p i).edges) (I417Example.edgeFinset (p j).edges)) :
    ShapeOf L ω := by
  classical
  refine ⟨fun i => I417Example.edgeFinset (p i).edges, ?_, ?_, hdisj⟩
  · intro i
    rw [I417Example.edgeFinset_coe]
    exact hopen i
  · intro i
    exact pathConnects_iff.mp ⟨p i, fun x hx => I417Example.mem_edgeFinset.mpr hx⟩

/-- Edge finsets are monotone under edge-list inclusion. -/
theorem edgeFinset_subset_of_subset {l₁ l₂ : List (Sym2 V)} (h : l₁ ⊆ l₂) :
    I417Example.edgeFinset l₁ ⊆ I417Example.edgeFinset l₂ := by
  intro a ha
  rw [I417Example.mem_edgeFinset] at *
  exact h ha

/-- Splitting a path at a vertex of it gives two walks with disjoint edge sets. -/
theorem edgeFinset_takeUntil_disjoint_dropUntil {u v : V} (P : (⊤ : SimpleGraph V).Walk u v)
    (hP : P.IsPath) {z : V} (hz : z ∈ P.support) :
    Disjoint (I417Example.edgeFinset (P.takeUntil z hz).edges)
      (I417Example.edgeFinset (P.dropUntil z hz).edges) := by
  classical
  have hconcat : (P.takeUntil z hz).edges ++ (P.dropUntil z hz).edges = P.edges := by
    rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
  have hd : ((P.takeUntil z hz).edges ++ (P.dropUntil z hz).edges).Nodup := by
    rw [hconcat]; exact hP.isTrail.edges_nodup
  exact I417Example.edgeFinset_disjoint_of_list_disjoint (List.nodup_append'.mp hd).2.2

/-! ## Splitting one segment of a four-segment diagram and attaching the third arm -/

set_option maxHeartbeats 1000000 in
-- the fifteen pairwise disjointness cases of the six-walk assembly exceed the default budget
/-- **The `q = 3` attachment step.**  Suppose four open walks `P`, `W₂`, `W₃`, `W₄` have pairwise
disjoint edge sets, `z` is a vertex of `P`, and a fifth open walk `Q : z → d` has edges disjoint
from all four.  Then the six walks obtained by splitting `P` at `z` and appending `Q` realise the
six-leg shape `(a₁,z) (z,b₁) (a₂,b₂) (a₃,b₃) (a₄,b₄) (z,d)` with pairwise disjoint edge sets. -/
theorem shapeOf_split {a1 b1 a2 b2 a3 b3 a4 b4 d : V} {ω : Config V}
    {P : (⊤ : SimpleGraph V).Walk a1 b1} (hP : P.IsPath) {z : V} (hz : z ∈ P.support)
    (W2 : (⊤ : SimpleGraph V).Walk a2 b2) (W3 : (⊤ : SimpleGraph V).Walk a3 b3)
    (W4 : (⊤ : SimpleGraph V).Walk a4 b4) (Q : (⊤ : SimpleGraph V).Walk z d)
    (hPω : ∀ e ∈ P.edges, e ∈ ω) (h2ω : ∀ e ∈ W2.edges, e ∈ ω)
    (h3ω : ∀ e ∈ W3.edges, e ∈ ω) (h4ω : ∀ e ∈ W4.edges, e ∈ ω)
    (hQω : ∀ e ∈ Q.edges, e ∈ ω)
    (dP2 : Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset W2.edges))
    (dP3 : Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset W3.edges))
    (dP4 : Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset W4.edges))
    (d23 : Disjoint (I417Example.edgeFinset W2.edges) (I417Example.edgeFinset W3.edges))
    (d24 : Disjoint (I417Example.edgeFinset W2.edges) (I417Example.edgeFinset W4.edges))
    (d34 : Disjoint (I417Example.edgeFinset W3.edges) (I417Example.edgeFinset W4.edges))
    (dQP : Disjoint (I417Example.edgeFinset Q.edges) (I417Example.edgeFinset P.edges))
    (dQ2 : Disjoint (I417Example.edgeFinset Q.edges) (I417Example.edgeFinset W2.edges))
    (dQ3 : Disjoint (I417Example.edgeFinset Q.edges) (I417Example.edgeFinset W3.edges))
    (dQ4 : Disjoint (I417Example.edgeFinset Q.edges) (I417Example.edgeFinset W4.edges)) :
    ShapeOf (legs6 a1 z z b1 a2 b2 a3 b3 a4 b4 z d) ω := by
  classical
  have hup : ∀ e ∈ (P.takeUntil z hz).edges, e ∈ ω :=
    fun e he => hPω e (SimpleGraph.Walk.edges_takeUntil_subset_edges P hz he)
  have hdown : ∀ e ∈ (P.dropUntil z hz).edges, e ∈ ω :=
    fun e he => hPω e (SimpleGraph.Walk.edges_dropUntil_subset_edges P hz he)
  have hsubUp : I417Example.edgeFinset (P.takeUntil z hz).edges ⊆
      I417Example.edgeFinset P.edges :=
    edgeFinset_subset_of_subset (SimpleGraph.Walk.edges_takeUntil_subset_edges P hz)
  have hsubDown : I417Example.edgeFinset (P.dropUntil z hz).edges ⊆
      I417Example.edgeFinset P.edges :=
    edgeFinset_subset_of_subset (SimpleGraph.Walk.edges_dropUntil_subset_edges P hz)
  have h01 : Disjoint (I417Example.edgeFinset (P.takeUntil z hz).edges)
      (I417Example.edgeFinset (P.dropUntil z hz).edges) :=
    edgeFinset_takeUntil_disjoint_dropUntil P hP hz
  have h02 : Disjoint (I417Example.edgeFinset (P.takeUntil z hz).edges)
      (I417Example.edgeFinset W2.edges) := dP2.mono hsubUp le_rfl
  have h03 : Disjoint (I417Example.edgeFinset (P.takeUntil z hz).edges)
      (I417Example.edgeFinset W3.edges) := dP3.mono hsubUp le_rfl
  have h04 : Disjoint (I417Example.edgeFinset (P.takeUntil z hz).edges)
      (I417Example.edgeFinset W4.edges) := dP4.mono hsubUp le_rfl
  have h05 : Disjoint (I417Example.edgeFinset (P.takeUntil z hz).edges)
      (I417Example.edgeFinset Q.edges) := dQP.symm.mono hsubUp le_rfl
  have h12 : Disjoint (I417Example.edgeFinset (P.dropUntil z hz).edges)
      (I417Example.edgeFinset W2.edges) := dP2.mono hsubDown le_rfl
  have h13 : Disjoint (I417Example.edgeFinset (P.dropUntil z hz).edges)
      (I417Example.edgeFinset W3.edges) := dP3.mono hsubDown le_rfl
  have h14 : Disjoint (I417Example.edgeFinset (P.dropUntil z hz).edges)
      (I417Example.edgeFinset W4.edges) := dP4.mono hsubDown le_rfl
  have h15 : Disjoint (I417Example.edgeFinset (P.dropUntil z hz).edges)
      (I417Example.edgeFinset Q.edges) := dQP.symm.mono hsubDown le_rfl
  refine shapeOf_mem_of_walks (walks6 (P.takeUntil z hz) (P.dropUntil z hz) W2 W3 W4 Q)
    ?_ ?_
  · intro i
    fin_cases i
    · exact hup
    · exact hdown
    · exact h2ω
    · exact h3ω
    · exact h4ω
    · exact hQω
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact h01
        | exact h01.symm
        | exact h02
        | exact h02.symm
        | exact h03
        | exact h03.symm
        | exact h04
        | exact h04.symm
        | exact h05
        | exact h05.symm
        | exact h12
        | exact h12.symm
        | exact h13
        | exact h13.symm
        | exact h14
        | exact h14.symm
        | exact h15
        | exact h15.symm
        | exact d23
        | exact d23.symm
        | exact d24
        | exact d24.symm
        | exact d34
        | exact d34.symm
        | exact dQ2
        | exact dQ2.symm
        | exact dQ3
        | exact dQ3.symm
        | exact dQ4
        | exact dQ4.symm

/-! ## The eight families are inside `ShapeQ3` -/

theorem shapeA0_subset (y w ga gb gc p q : V) :
    ShapeOf (legsA0 y w ga gb gc p q) ⊆ ShapeQ3 y w ga gb gc := by
  intro ω h
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  simp only [Set.mem_union]
  tauto

theorem shapeA1_subset (y w ga gb gc p q : V) :
    ShapeOf (legsA1 y w ga gb gc p q) ⊆ ShapeQ3 y w ga gb gc := by
  intro ω h
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  simp only [Set.mem_union]
  tauto

theorem shapeA2_subset (y w ga gb gc p q : V) :
    ShapeOf (legsA2 y w ga gb gc p q) ⊆ ShapeQ3 y w ga gb gc := by
  intro ω h
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  simp only [Set.mem_union]
  tauto

theorem shapeA3_subset (y w ga gb gc p q : V) :
    ShapeOf (legsA3 y w ga gb gc p q) ⊆ ShapeQ3 y w ga gb gc := by
  intro ω h
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  simp only [Set.mem_union]
  tauto

theorem shapeB0_subset (y w ga gb gc p q : V) :
    ShapeOf (legsB0 y w ga gb gc p q) ⊆ ShapeQ3 y w ga gb gc := by
  intro ω h
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  simp only [Set.mem_union]
  tauto

theorem shapeB1_subset (y w ga gb gc p q : V) :
    ShapeOf (legsB1 y w ga gb gc p q) ⊆ ShapeQ3 y w ga gb gc := by
  intro ω h
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  simp only [Set.mem_union]
  tauto

theorem shapeB2_subset (y w ga gb gc p q : V) :
    ShapeOf (legsB2 y w ga gb gc p q) ⊆ ShapeQ3 y w ga gb gc := by
  intro ω h
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  simp only [Set.mem_union]
  tauto

theorem shapeB3_subset (y w ga gb gc p q : V) :
    ShapeOf (legsB3 y w ga gb gc p q) ⊆ ShapeQ3 y w ga gb gc := by
  intro ω h
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  simp only [Set.mem_union]
  tauto

/-! ## The cover -/

/-- **The `q = 3` mark-on-the-path fresh cover.**  For every configuration of the fresh marked
event at the selected arm `j` and every choice of the two other arms `i₁, i₂`, one of the eight
six-edge subdivided binary trees occurs with pairwise disjoint witnesses.  No distinctness of the
three labels is needed: the argument allows coincident arms and coincident branch points. -/
theorem freshMark_subset_shapeQ3 (y w : V) (g : Fin 3 → V) (j i1 i2 : Fin 3) :
    I417Gen.freshMark y g j w ⊆ ShapeQ3 y w (g j) (g i1) (g i2) := by
  classical
  rintro ω ⟨hDO, hlab⟩
  have harm1 : Connects ω y (g i1) := by
    rw [I417A.labelEvent_eq_iInter] at hlab
    exact Set.mem_iInter.mp hlab i1
  have harm2 : Connects ω y (g i2) := by
    rw [I417A.labelEvent_eq_iInter] at hlab
    exact Set.mem_iInter.mp hlab i2
  -- the two edge-disjoint open halves of the fresh path
  obtain ⟨s, t, hs, ht, hst, hAs, hBt⟩ := hDO
  obtain ⟨p0, hp0⟩ := pathConnects_iff.mpr hAs
  obtain ⟨r0, hr0⟩ := pathConnects_iff.mpr hBt
  set P : (⊤ : SimpleGraph V).Walk y w := p0.bypass with hPdef
  set R : (⊤ : SimpleGraph V).Walk w (g j) := r0.bypass with hRdef
  have hPpath : P.IsPath := SimpleGraph.Walk.bypass_isPath p0
  have hRpath : R.IsPath := SimpleGraph.Walk.bypass_isPath r0
  have hPsub : ∀ e ∈ P.edges, e ∈ s :=
    fun e he => hp0 e (SimpleGraph.Walk.edges_bypass_subset_edges p0 he)
  have hRsub : ∀ e ∈ R.edges, e ∈ t :=
    fun e he => hr0 e (SimpleGraph.Walk.edges_bypass_subset_edges r0 he)
  have hPedges : ∀ e ∈ P.edges, e ∈ ω := fun e he => hs (hPsub e he)
  have hRedges : ∀ e ∈ R.edges, e ∈ ω := fun e he => ht (hRsub e he)
  have hPR : Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset R.edges) := by
    rw [Finset.disjoint_left]
    intro e he he'
    exact Finset.disjoint_left.mp hst (hPsub e (I417Example.mem_edgeFinset.mp he))
      (hRsub e (I417Example.mem_edgeFinset.mp he'))
  -- the first hit of the arm `g i₁` against the two halves
  set S : Set V := {v | v ∈ P.support ∨ v ∈ R.support} with hSdef
  have hyS : y ∈ S := Or.inl (SimpleGraph.Walk.start_mem_support P)
  obtain ⟨r1, hr1⟩ := pathConnects_iff.mpr (connects_symm harm1)
  obtain ⟨p, Q0, hpS, hQ0edges, hQ0supp⟩ := exists_first_hit r1 hr1 S hyS
  set Q : (⊤ : SimpleGraph V).Walk p (g i1) := Q0.bypass with hQdef
  have hQpath : Q.IsPath := SimpleGraph.Walk.bypass_isPath Q0
  have hQedges : ∀ e ∈ Q.edges, e ∈ ω :=
    fun e he => hQ0edges e (SimpleGraph.Walk.edges_bypass_subset_edges Q0 he)
  have hQsupp : ∀ v ∈ Q.support, v = p ∨ v ∉ S :=
    fun v hv => hQ0supp v (SimpleGraph.Walk.support_bypass_subset_support Q0 hv)
  have hPinS : ∀ e ∈ P.edges, ∀ v ∈ e, v ∈ S :=
    fun e he v hv =>
      Or.inl (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩))
  have hRinS : ∀ e ∈ R.edges, ∀ v ∈ e, v ∈ S :=
    fun e he v hv =>
      Or.inr (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩))
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
  have hPQ : Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset Q.edges) :=
    I417Example.edges_disjoint_of_regions hPinS hQinU hSU
  have hRQ : Disjoint (I417Example.edgeFinset R.edges) (I417Example.edgeFinset Q.edges) :=
    I417Example.edges_disjoint_of_regions hRinS hQinU hSU
  -- the first hit of the arm `g i₂` against the two halves and the first arm
  set S2 : Set V := {v | v ∈ S ∨ v ∈ Q.support} with hS2def
  have hyS2 : y ∈ S2 := Or.inl hyS
  have hS2P : ∀ e ∈ P.edges, ∀ v ∈ e, v ∈ S2 :=
    fun e he v hv => Or.inl (hPinS e he v hv)
  have hS2R : ∀ e ∈ R.edges, ∀ v ∈ e, v ∈ S2 :=
    fun e he v hv => Or.inl (hRinS e he v hv)
  have hS2Q : ∀ e ∈ Q.edges, ∀ v ∈ e, v ∈ S2 :=
    fun e he v hv =>
      Or.inr (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩))
  obtain ⟨r2, hr2⟩ := pathConnects_iff.mpr (connects_symm harm2)
  obtain ⟨q, Q2₀, hqS2, hQ2₀edges, hQ2₀supp⟩ := exists_first_hit r2 hr2 S2 hyS2
  set Q2 : (⊤ : SimpleGraph V).Walk q (g i2) := Q2₀.bypass with hQ2def
  have hQ2edges : ∀ e ∈ Q2.edges, e ∈ ω :=
    fun e he => hQ2₀edges e (SimpleGraph.Walk.edges_bypass_subset_edges Q2₀ he)
  have hQ2supp : ∀ v ∈ Q2.support, v = q ∨ v ∉ S2 :=
    fun v hv => hQ2₀supp v (SimpleGraph.Walk.support_bypass_subset_support Q2₀ hv)
  have hQ2inU : ∀ e ∈ Q2.edges, ∀ v ∈ e, v ∈ ({q} : Set V) ∪ S2ᶜ := by
    intro e he v hv
    rcases hQ2supp v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e, he, hv⟩)) with h | h
    · subst h; exact Or.inl (by simp)
    · exact Or.inr h
  have hQ2SU : ∀ v ∈ S2, v ∈ ({q} : Set V) ∪ S2ᶜ → v = q := by
    rintro v _ (h | h)
    · simpa using h
    · exact absurd ‹v ∈ S2› h
  have hPQ2 : Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset Q2.edges) :=
    I417Example.edges_disjoint_of_regions hS2P hQ2inU hQ2SU
  have hRQ2 : Disjoint (I417Example.edgeFinset R.edges) (I417Example.edgeFinset Q2.edges) :=
    I417Example.edges_disjoint_of_regions hS2R hQ2inU hQ2SU
  have hQQ2 : Disjoint (I417Example.edgeFinset Q.edges) (I417Example.edgeFinset Q2.edges) :=
    I417Example.edges_disjoint_of_regions hS2Q hQ2inU hQ2SU
  -- case analysis: where the first hit `p` landed
  rcases hpS with hpP | hpR
  · -- ===== `p` on the `y → w` half =====
    set Aup : (⊤ : SimpleGraph V).Walk y p := P.takeUntil p hpP with hAupdef
    set Adown : (⊤ : SimpleGraph V).Walk p w := P.dropUntil p hpP with hAdowndef
    have hAupPath : Aup.IsPath := hPpath.takeUntil hpP
    have hAdownPath : Adown.IsPath := hPpath.dropUntil hpP
    have hAupSub : ∀ e ∈ Aup.edges, e ∈ P.edges :=
      fun e he => SimpleGraph.Walk.edges_takeUntil_subset_edges P hpP he
    have hAdownSub : ∀ e ∈ Adown.edges, e ∈ P.edges :=
      fun e he => SimpleGraph.Walk.edges_dropUntil_subset_edges P hpP he
    have hAupω : ∀ e ∈ Aup.edges, e ∈ ω := fun e he => hPedges e (hAupSub e he)
    have hAdownω : ∀ e ∈ Adown.edges, e ∈ ω := fun e he => hPedges e (hAdownSub e he)
    have hAupAdown : Disjoint (I417Example.edgeFinset Aup.edges)
        (I417Example.edgeFinset Adown.edges) :=
      edgeFinset_takeUntil_disjoint_dropUntil P hPpath hpP
    have hAupR : Disjoint (I417Example.edgeFinset Aup.edges)
        (I417Example.edgeFinset R.edges) :=
      hPR.mono (edgeFinset_subset_of_subset hAupSub) le_rfl
    have hAdownR : Disjoint (I417Example.edgeFinset Adown.edges)
        (I417Example.edgeFinset R.edges) :=
      hPR.mono (edgeFinset_subset_of_subset hAdownSub) le_rfl
    have hAupQ : Disjoint (I417Example.edgeFinset Aup.edges)
        (I417Example.edgeFinset Q.edges) :=
      hPQ.mono (edgeFinset_subset_of_subset hAupSub) le_rfl
    have hAdownQ : Disjoint (I417Example.edgeFinset Adown.edges)
        (I417Example.edgeFinset Q.edges) :=
      hPQ.mono (edgeFinset_subset_of_subset hAdownSub) le_rfl
    have hAupQ2 : Disjoint (I417Example.edgeFinset Aup.edges)
        (I417Example.edgeFinset Q2.edges) :=
      hPQ2.mono (edgeFinset_subset_of_subset hAupSub) le_rfl
    have hAdownQ2 : Disjoint (I417Example.edgeFinset Adown.edges)
        (I417Example.edgeFinset Q2.edges) :=
      hPQ2.mono (edgeFinset_subset_of_subset hAdownSub) le_rfl
    rcases hqS2 with hqS | hqQ
    · rcases hqS with hqP | hqR
      · -- `q` on the `y → w` half: split `Aup` or `Adown`
        by_cases hqAup : q ∈ Aup.support
        · refine shapeA0_subset y w (g j) (g i1) (g i2) p q ?_
          exact shapeOf_split hAupPath hqAup Adown R Q Q2 hAupω hAdownω hRedges hQedges hQ2edges
            hAupAdown hAupR hAupQ hAdownR hAdownQ hRQ hAupQ2.symm hAdownQ2.symm hRQ2.symm
            hQQ2.symm
        · have hqAdown : q ∈ Adown.support :=
            I417Example.mem_dropUntil_of_notMem_takeUntil hpP hqP hqAup
          refine shapeA1_subset y w (g j) (g i1) (g i2) p q ?_
          exact shapeOf_split hAdownPath hqAdown Aup R Q Q2 hAdownω hAupω hRedges hQedges
            hQ2edges hAupAdown.symm hAdownR hAdownQ hAupR hAupQ hRQ hAdownQ2.symm hAupQ2.symm
            hRQ2.symm hQQ2.symm
      · -- `q` on the `w → g j` half: split `R`
        refine shapeA2_subset y w (g j) (g i1) (g i2) p q ?_
        exact shapeOf_split hRpath hqR Aup Adown Q Q2 hRedges hAupω hAdownω hQedges hQ2edges
          hAupR.symm hAdownR.symm hRQ hAupAdown hAupQ hAdownQ hRQ2.symm hAupQ2.symm hAdownQ2.symm
          hQQ2.symm
    · -- `q` on the first arm: split `Q`
      refine shapeA3_subset y w (g j) (g i1) (g i2) p q ?_
      exact shapeOf_split (Q := Q2) hQpath hqQ Aup Adown R hQedges hAupω hAdownω hRedges
        hQ2edges hAupQ.symm hAdownQ.symm hRQ.symm hAupAdown hAupR hAdownR hQQ2.symm hAupQ2.symm
        hAdownQ2.symm hRQ2.symm
  · -- ===== `p` on the `w → g j` half =====
    set Rup : (⊤ : SimpleGraph V).Walk w p := R.takeUntil p hpR with hRupdef
    set Rdown : (⊤ : SimpleGraph V).Walk p (g j) := R.dropUntil p hpR with hRowndef
    have hRupPath : Rup.IsPath := hRpath.takeUntil hpR
    have hRdownPath : Rdown.IsPath := hRpath.dropUntil hpR
    have hRupSub : ∀ e ∈ Rup.edges, e ∈ R.edges :=
      fun e he => SimpleGraph.Walk.edges_takeUntil_subset_edges R hpR he
    have hRdownSub : ∀ e ∈ Rdown.edges, e ∈ R.edges :=
      fun e he => SimpleGraph.Walk.edges_dropUntil_subset_edges R hpR he
    have hRupω : ∀ e ∈ Rup.edges, e ∈ ω := fun e he => hRedges e (hRupSub e he)
    have hRdownω : ∀ e ∈ Rdown.edges, e ∈ ω := fun e he => hRedges e (hRdownSub e he)
    have hRupRdown : Disjoint (I417Example.edgeFinset Rup.edges)
        (I417Example.edgeFinset Rdown.edges) :=
      edgeFinset_takeUntil_disjoint_dropUntil R hRpath hpR
    have hPRup : Disjoint (I417Example.edgeFinset P.edges)
        (I417Example.edgeFinset Rup.edges) :=
      hPR.mono le_rfl (edgeFinset_subset_of_subset hRupSub)
    have hPRdown : Disjoint (I417Example.edgeFinset P.edges)
        (I417Example.edgeFinset Rdown.edges) :=
      hPR.mono le_rfl (edgeFinset_subset_of_subset hRdownSub)
    have hRupQ : Disjoint (I417Example.edgeFinset Rup.edges)
        (I417Example.edgeFinset Q.edges) :=
      hRQ.mono (edgeFinset_subset_of_subset hRupSub) le_rfl
    have hRdownQ : Disjoint (I417Example.edgeFinset Rdown.edges)
        (I417Example.edgeFinset Q.edges) :=
      hRQ.mono (edgeFinset_subset_of_subset hRdownSub) le_rfl
    have hQ2Rup : Disjoint (I417Example.edgeFinset Q2.edges)
        (I417Example.edgeFinset Rup.edges) :=
      hRQ2.symm.mono le_rfl (edgeFinset_subset_of_subset hRupSub)
    have hQ2Rdown : Disjoint (I417Example.edgeFinset Q2.edges)
        (I417Example.edgeFinset Rdown.edges) :=
      hRQ2.symm.mono le_rfl (edgeFinset_subset_of_subset hRdownSub)
    rcases hqS2 with hqS | hqQ
    · rcases hqS with hqP | hqR
      · -- `q` on the whole `y → w` half: split `P`
        refine shapeB0_subset y w (g j) (g i1) (g i2) p q ?_
        exact shapeOf_split hPpath hqP Rup Rdown Q Q2 hPedges hRupω hRdownω hQedges hQ2edges
          hPRup hPRdown hPQ hRupRdown hRupQ hRdownQ hPQ2.symm hQ2Rup hQ2Rdown hQQ2.symm
      · -- `q` on the `w → g j` half: split `Rup` or `Rdown`
        by_cases hqRup : q ∈ Rup.support
        · refine shapeB1_subset y w (g j) (g i1) (g i2) p q ?_
          exact shapeOf_split hRupPath hqRup P Rdown Q Q2 hRupω hPedges hRdownω hQedges hQ2edges
            hPRup.symm hRupRdown hRupQ hPRdown hPQ hRdownQ hQ2Rup hPQ2.symm hQ2Rdown hQQ2.symm
        · have hqRdown : q ∈ Rdown.support :=
            I417Example.mem_dropUntil_of_notMem_takeUntil hpR hqR hqRup
          refine shapeB2_subset y w (g j) (g i1) (g i2) p q ?_
          exact shapeOf_split hRdownPath hqRdown P Rup Q Q2 hRdownω hPedges hRupω hQedges
            hQ2edges hPRdown.symm hRupRdown.symm hRdownQ hPRup hPQ hRupQ hQ2Rdown hPQ2.symm
            hQ2Rup hQQ2.symm
    · -- `q` on the first arm: split `Q`
      refine shapeB3_subset y w (g j) (g i1) (g i2) p q ?_
      exact shapeOf_split (Q := Q2) hQpath hqQ P Rup Rdown hQedges hPedges hRupω hRdownω
        hQ2edges hPQ.symm hRupQ.symm hRdownQ.symm hPRup hPRdown hRupRdown hQQ2.symm hPQ2.symm
        hQ2Rup hQ2Rdown

end PercLib.CriticalLRP.I417FreshThree.Refined
