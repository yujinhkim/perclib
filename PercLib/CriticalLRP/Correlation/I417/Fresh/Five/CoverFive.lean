/-
Coordinator-integrated from the independently rebuilt `smwxb4a1l/m1` Q5 artifact.
Original production base `8d1c9eb3738a26cc63afc07f525ba4af357bd905`; review revisions
are confined to strict module lints and explicit branch-lemma aggregation.
-/
/-
Independently built for swarm `smwxb4a1l`, member `m1`, direction Q5-FINITE-EVALUATION.
Read-only against production (`d9a001b7f0a33cf6395158f7621ad4de1fe3c7c8`).
Proofs only in this file; no new definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Five.Branch

/-!
# The explicit `q = 5` first-hit cover

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (pp. 43--46).

The fresh side of the `q = 5` two-copy expansion is `2q = 10` edge-disjoint legs: the two halves
`y → w`, `w → g j` of the selected arm's path, plus one attachment round for each of the four
remaining arms.  Each round takes an open walk from the next arm to the pin `y`, first-hits the
diagram built so far (`exists_first_hit`), and splits the hit leg (`step`).  This file runs the four
rounds **explicitly**, so that the cover produced is a `384`-branch family of ten-leg diagrams whose
branch index is the split-leg choice in each round:

* `exists_diag_q5` — the four rounds, starting from the two-leg base `baseDiag`; the result is a
  witnessed diagram (`Diag`) on the ten-slot index type with exactly the legs of `q5Legs`;
* `freshMark_subset_q5Shape` — the fresh marked event is contained in the explicit family
  `q5Shape`;
* `freshMark_measure_le_q5` — union bound over the eight-fold family plus `q`-fold BK.

Every use of the cover keeps the *actual path witnesses*: no measure-level insertion or moment
assumption enters.  The only inputs are the two edge-disjoint open halves of the marked path and
the connections of the five arms to `y`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFive

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshFour.Refined
open PercLib.CriticalLRP.I417FreshFour.Eval
open PercLib.CriticalLRP.I417GenIter
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## One attachment round, with the pin invariant -/

/-- **One attachment round.**  Given a witnessed diagram `D` whose leg in slot `l` starts at the pin
`y`, and the connection of the next arm `d` to `y`, some leg `k` can be split at a first-hit vertex
`z` and the arm attached, producing a witnessed diagram with legs `splitAt L k z d` whose slot
`Sum.inl l` still starts at `y`. -/
theorem round_q5 {ι : Type*} [DecidableEq ι] {ω : Config V} {L : ι → V × V} {y : V}
    (D : Diag ι ω L) (l : ι) (hl : (L l).1 = y) (d : V) (hd : Connects ω y d) :
    ∃ (k : ι) (z : V), Nonempty (Diag (ι ⊕ Bool) ω (splitAt L k z d)) ∧
      ((splitAt L k z d) (Sum.inl l)).1 = y := by
  classical
  obtain ⟨r, hr⟩ := pathConnects_iff.mpr (connects_symm hd)
  have hyS : y ∈ ⋃ i, {v : V | v ∈ (D.W i).2.support} := by
    refine Set.mem_iUnion.mpr ⟨l, ?_⟩
    have h1 : (D.W l).1.1 = y := by rw [D.legs_eq l]; exact hl
    exact I417GenIter.mem_support_start (D.W l).2 h1
  obtain ⟨z, Q, _hzS, hQop, hQsupp⟩ :=
    exists_first_hit r hr (⋃ i, {v : V | v ∈ (D.W i).2.support}) hyS
  have hQreg : ∀ e ∈ Q.edges, ∀ v ∈ e,
      v ∈ ({z} ∪ (⋃ i, {v : V | v ∈ (D.W i).2.support})ᶜ) := by
    intro e he v hv
    rcases hQsupp v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e, he, hv⟩)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨k, ⟨D'⟩⟩ := I417GenIter.step D _hzS Q hQop hQreg
  exact ⟨k, z, ⟨D'⟩, I417GenIter.splitAt_left hl k z d⟩

/-! ## The four rounds -/

/-- **The explicit `q = 5` first-hit cover, branch by branch.**  From the two halves of the selected
arm's path and the five connections to `y`, the four remaining arms are attached one at a time by
first-hitting the diagram; the result is a witnessed ten-leg diagram with exactly the legs of
`q5Legs` for some branch `(k1,k2,k3,k4)` and hit vertices `(z1,z2,z3,z4)`. -/
theorem exists_diag_q5 {ω : Config V} {y w : V} {g : Fin 5 → V} {j i1 i2 i3 i4 : Fin 5}
    (hcon : ∀ t : Fin 5, Connects ω y (g t))
    {P : (⊤ : SimpleGraph V).Walk y w} {R : (⊤ : SimpleGraph V).Walk w (g j)}
    (hPpath : P.IsPath) (hRpath : R.IsPath) (hPop : ∀ e ∈ P.edges, e ∈ ω)
    (hRop : ∀ e ∈ R.edges, e ∈ ω)
    (hPR : Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset R.edges)) :
    ∃ (k1 : Fin 2) (k2 : Fin 2 ⊕ Bool) (k3 : (Fin 2 ⊕ Bool) ⊕ Bool)
      (k4 : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool) (z1 z2 z3 z4 : V),
      Nonempty (Diag ((((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool) ⊕ Bool) ω
        (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w (g j) (g i1) (g i2) (g i3) (g i4))) := by
  classical
  -- the two-leg base
  have hbase : (baseLegs y w (g j) (0 : Fin 2)).1 = y := rfl
  obtain ⟨k1, z1, ⟨D1⟩, hpin1⟩ :=
    round_q5 (baseDiag hPpath hRpath hPop hRop hPR) (0 : Fin 2) hbase (g i1) (hcon i1)
  -- the second round: the pin slot is `Sum.inl 0`
  obtain ⟨k2, z2, ⟨D2⟩, hpin2⟩ :=
    round_q5 D1 (Sum.inl (0 : Fin 2)) hpin1 (g i2) (hcon i2)
  -- the third round
  obtain ⟨k3, z3, ⟨D3⟩, hpin3⟩ :=
    round_q5 D2 (Sum.inl (Sum.inl (0 : Fin 2))) hpin2 (g i3) (hcon i3)
  -- the fourth round
  obtain ⟨k4, z4, ⟨D4⟩, _hpin4⟩ :=
    round_q5 D3 (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))) hpin3 (g i4) (hcon i4)
  exact ⟨k1, k2, k3, k4, z1, z2, z3, z4, ⟨D4⟩⟩

end PercLib.CriticalLRP.I417FreshFive

namespace PercLib.CriticalLRP.I417FreshFive

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshFour.Refined
open PercLib.CriticalLRP.I417FreshFour.Eval
open PercLib.CriticalLRP.I417GenIter
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **The `q = 5` cover.**  The fresh marked event is contained in the explicit `384`-branch
ten-leg family, keeping the actual path witnesses of the disjoint occurrence and of the five arm
connections.  No distinctness of the arm labels is needed: whether or not the labels coincide, the
four first-hit rounds attach exactly the four prescribed arms. -/
theorem freshMark_subset_q5Shape (y w : V) (g : Fin 5 → V) (j i1 i2 i3 i4 : Fin 5) :
    I417Gen.freshMark y g j w ⊆ q5Shape y w (g j) (g i1) (g i2) (g i3) (g i4) := by
  classical
  rintro ω ⟨hDO, hlab⟩
  obtain ⟨s, t, hs, ht, hst, hys, hwt⟩ := hDO
  obtain ⟨p0, hp0⟩ := pathConnects_iff.mpr hys
  obtain ⟨r0, hr0⟩ := pathConnects_iff.mpr hwt
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
  rw [I417A.labelEvent_eq_iInter] at hlab
  have hcon : ∀ i : Fin 5, Connects ω y (g i) := fun i => Set.mem_iInter.mp hlab i
  obtain ⟨k1, k2, k3, k4, z1, z2, z3, z4, ⟨D⟩⟩ :=
    exists_diag_q5 (ω := ω) (y := y) (w := w) (g := g) (j := j) (i1 := i1) (i2 := i2)
      (i3 := i3) (i4 := i4) hcon
      (SimpleGraph.Walk.bypass_isPath p0) (SimpleGraph.Walk.bypass_isPath r0)
      hPop hRop hPR
  refine Set.mem_iUnion.mpr ⟨k1, ?_⟩
  refine Set.mem_iUnion.mpr ⟨k2, ?_⟩
  refine Set.mem_iUnion.mpr ⟨k3, ?_⟩
  refine Set.mem_iUnion.mpr ⟨k4, ?_⟩
  refine Set.mem_iUnion.mpr ⟨z1, ?_⟩
  refine Set.mem_iUnion.mpr ⟨z2, ?_⟩
  refine Set.mem_iUnion.mpr ⟨z3, ?_⟩
  exact Set.mem_iUnion.mpr ⟨z4, shapeOfI_of_diag_legs D⟩

/-- **The `q = 5` fresh-side BK bound.**  For every arm tuple, selected arm and ordering of the other
four labels, the fresh marked event costs at most the sum over the `2 · 4 · 6 · 8 = 384` ten-leg
diagrams of the products of their ten two-point factors. -/
theorem freshMark_measure_le_q5 (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (g : Fin 5 → V) (j i1 i2 i3 i4 : Fin 5) :
    (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
      ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
        ∑' (k4 : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool), ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
        ∑' (z4 : V),
          ∏ i, tau π
            (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w (g j) (g i1) (g i2) (g i3) (g i4) i).1
            (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w (g j) (g i1) (g i2) (g i3) (g i4) i).2 := by
  classical
  refine le_trans (measure_mono (freshMark_subset_q5Shape y w g j i1 i2 i3 i4)) ?_
  rw [q5Shape]
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun k1 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun k2 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun k3 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun k4 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun z1 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun z2 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun z3 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun z4 => ?_)
  exact shapeOfI_measure_le π hπ _

end PercLib.CriticalLRP.I417FreshFive
