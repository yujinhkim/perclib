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

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Four.Refined.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Three.Refined.Cover

/-!
# Lemma I.4.17 at `q = 4`: the eight-edge fresh cover

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied paper text lines 2444--2464): the fresh
side of the two-copy expansion carries `2q` edges, arranged as a rooted binary tree whose leaves are
the `q` *labelled* arms with the mark `w` subdividing one edge of the path from the pin `y` to the
selected arm.

This file proves the deterministic event-level content at `q = 4`:

  `freshMark y g j w ⊆ q4Shape y w (g j) (g i₁) (g i₂) (g i₃)`

for **every** choice of the selected arm `j : Fin 4` and every ordering `i₁, i₂, i₃` of the three
remaining labels, and with **arbitrary coincident positions** (`w = y`, `w = g j`, coincident arms,
attachment points at existing vertices, trivial legs).

## Method: inside-segment attachment, iterated

The `q = 2` fresh event is exactly a two-leg diagram: `Percolation.DisjointOccurrence` supplies the
two edge-disjoint open halves `P : y → w` and `R : w → g j`, so `baseDiag` packages them as a
`Diag (Fin 2)` — two legs, two open path witnesses, pairwise disjoint.

`step` is the **generic attachment step**, the `q → q + 1` induction step of the first-hit method:
given a diagram `D` (legs plus open path witnesses, pairwise edge-disjoint) and an open walk
`Q : z → d` from a vertex `z` of the diagram to a new labelled arm, whose edges have both endpoints
in `{z} ∪ Uᶜ` where `U = ⋃ i, supp (W i)` is the diagram's vertex set, there is a **leg `k`** of `D`
containing `z`, and splitting that leg at `z` and attaching `Q` gives a diagram with two more legs,
realising `splitAt L k z d`.

Because `D`'s witnesses are pairwise edge-disjoint and the two endpoints of every leg edge lie in
`U` while both endpoints of every `Q`-edge lie in `{z} ∪ Uᶜ`, `Q`'s edges are disjoint from every
leg's edges (`I417Example.edges_disjoint_of_regions`); the two halves of the split leg are disjoint
because the split is taken on a *path*.

Iterating `step` three times from `baseDiag` gives the eight-leg family.  At each stage the first
hit is taken against the *union of the leg supports of the current diagram*
(`PercLib.CriticalLRP.exists_first_hit`), which is what makes the attachment land inside the
diagram; it is the iterated first-hit construction of `Fresh/Two/Refined/Cover.lean` and
`Fresh/Three/Refined/Cover.lean`, carried out once in index-generic form.
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

/-! ## Walking from a named vertex

A walk's endpoint is a *term*, so `v ∈ p.support` at a propositionally equal vertex needs the cast of
the walk, not a rewrite inside its type.  These two elementary lemmas do that once. -/

theorem support_cast {u v y : V} (p : (⊤ : SimpleGraph V).Walk u v) (h : u = y) :
    (h ▸ p).support = p.support := by
  cases h
  rfl

/-- A named start vertex of a walk lies in its support. -/
theorem mem_support_start {u v : V} (p : (⊤ : SimpleGraph V).Walk u v) {y : V} (h : u = y) :
    y ∈ p.support := by
  have key : (h ▸ p).support = p.support := support_cast p h
  rw [← key]
  exact SimpleGraph.Walk.start_mem_support _

/-! ## The attachment step -/

/-- **Inside-segment attachment.**  Let `D` be a `2q`-leg diagram in `ω` and let `Q : z → d` be an
open walk from a vertex `z` of the diagram to a new arm `d`, whose edges have both endpoints in
`{z} ∪ Uᶜ`, where `U = ⋃ i, supp (W i)` is the vertex set of the diagram.  Then **some** leg `k` of
`D` contains `z`, and splitting that leg at `z` and attaching `Q` gives a `2q + 2`-leg diagram
realising `splitAt L k z d`.

No non-degeneracy is assumed: `z` may be either endpoint of a leg (the corresponding half is then a
trivial walk), a leg may be trivial, and `d` may coincide with any vertex (including `z` and the
arms). -/
theorem step {ι : Type*} [DecidableEq ι] {ω : Config V} {L : ι → V × V} (D : Diag ι ω L)
    {z d : V} (hz : z ∈ ⋃ i, {v : V | v ∈ (D.W i).2.support})
    (Q : (⊤ : SimpleGraph V).Walk z d) (hQop : ∀ e ∈ Q.edges, e ∈ ω)
    (hQreg : ∀ e ∈ Q.edges, ∀ v ∈ e, v ∈ ({z} ∪ (⋃ i, {v : V | v ∈ (D.W i).2.support})ᶜ)) :
    ∃ k : ι, Nonempty (Diag (ι ⊕ Bool) ω (splitAt L k z d)) := by
  classical
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  -- the two halves of the split leg
  set Pup : (⊤ : SimpleGraph V).Walk (D.W k).1.1 z :=
    (D.W k).2.takeUntil z hk with hPup
  set Pdn : (⊤ : SimpleGraph V).Walk z (D.W k).1.2 :=
    (D.W k).2.dropUntil z hk with hPdn
  have hPupPath : Pup.IsPath := (D.isPath k).takeUntil hk
  have hPdnPath : Pdn.IsPath := (D.isPath k).dropUntil hk
  have hPupSub : ∀ e ∈ Pup.edges, e ∈ (D.W k).2.edges :=
    fun e he => SimpleGraph.Walk.edges_takeUntil_subset_edges (D.W k).2 hk he
  have hPdnSub : ∀ e ∈ Pdn.edges, e ∈ (D.W k).2.edges :=
    fun e he => SimpleGraph.Walk.edges_dropUntil_subset_edges (D.W k).2 hk he
  have hPupDn : Disjoint (I417Example.edgeFinset Pup.edges) (I417Example.edgeFinset Pdn.edges) :=
    I417FreshThree.Refined.edgeFinset_takeUntil_disjoint_dropUntil (D.W k).2 (D.isPath k) hk
  have hPupSubF : I417Example.edgeFinset Pup.edges ⊆ I417Example.edgeFinset (D.W k).2.edges :=
    fun x hx => I417Example.mem_edgeFinset.mpr (hPupSub x (I417Example.mem_edgeFinset.mp hx))
  have hPdnSubF : I417Example.edgeFinset Pdn.edges ⊆ I417Example.edgeFinset (D.W k).2.edges :=
    fun x hx => I417Example.mem_edgeFinset.mpr (hPdnSub x (I417Example.mem_edgeFinset.mp hx))
  -- the new arm is attached through the bypassed walk, so that it is again a path
  have hQbP : (∀ e ∈ Q.bypass.edges, e ∈ ω) ∧
      (∀ e ∈ Q.bypass.edges, ∀ v ∈ e, v ∈ ({z} ∪ (⋃ i, {v : V | v ∈ (D.W i).2.support})ᶜ)) := by
    refine ⟨fun e he => hQop e (SimpleGraph.Walk.edges_bypass_subset_edges Q he), ?_⟩
    intro e he v hv
    exact hQreg e (SimpleGraph.Walk.edges_bypass_subset_edges Q he) v hv
  -- the new family
  set W' : ι ⊕ Bool → LegWalk V := fun i =>
    match i with
    | Sum.inl j => if j = k then ⟨((D.W k).1.1, z), Pup⟩ else ⟨(D.W j).1, (D.W j).2⟩
    | Sum.inr false => ⟨(z, (D.W k).1.2), Pdn⟩
    | Sum.inr true => ⟨(z, d), Q.bypass⟩ with hW'
  have hW'_self : W' (Sum.inl k) = ⟨((D.W k).1.1, z), Pup⟩ := by
    rw [hW']
    simp
  have hW'_ne : ∀ j : ι, j ≠ k → W' (Sum.inl j) = ⟨(D.W j).1, (D.W j).2⟩ := by
    intro j hj
    rw [hW']
    simp [hj]
  have hW'_false : W' (Sum.inr false) = ⟨(z, (D.W k).1.2), Pdn⟩ := by
    rw [hW']
  have hW'_true : W' (Sum.inr true) = ⟨(z, d), Q.bypass⟩ := by
    rw [hW']
  -- every leg edge has both endpoints in the diagram vertex set `U`
  have hEdgeInU : ∀ (i : ι) (e : Sym2 V), e ∈ (D.W i).2.edges → ∀ v ∈ e,
      v ∈ (⋃ i, {v : V | v ∈ (D.W i).2.support}) := by
    intro i e he v hv
    exact Set.mem_iUnion.mpr ⟨i, SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
      (Or.inr ⟨e, he, hv⟩)⟩
  have hZone : ∀ v ∈ (⋃ i, {v : V | v ∈ (D.W i).2.support}),
      v ∈ ({z} ∪ (⋃ i, {v : V | v ∈ (D.W i).2.support})ᶜ : Set V) → v = z := by
    intro v hv hv'
    rcases hv' with h | h
    · simpa using h
    · exact absurd hv h
  -- the edge finsets of the new family, at the level of `Finset`s (no dependent transport)
  have hEs : I417Example.edgeFinset (W' (Sum.inl k)).2.edges = I417Example.edgeFinset Pup.edges := by
    rw [hW'_self]
  have hEn : ∀ j : ι, j ≠ k →
      I417Example.edgeFinset (W' (Sum.inl j)).2.edges =
        I417Example.edgeFinset (D.W j).2.edges := by
    intro j hj
    rw [hW'_ne j hj]
  have hEf : I417Example.edgeFinset (W' (Sum.inr false)).2.edges =
      I417Example.edgeFinset Pdn.edges := by
    rw [hW'_false]
  have hEt : I417Example.edgeFinset (W' (Sum.inr true)).2.edges =
      I417Example.edgeFinset Q.bypass.edges := by
    rw [hW'_true]
  refine ⟨k, ⟨⟨W', ?_, ?_, ?_, ?_⟩⟩⟩
  · -- the legs of the new family
    intro i
    rcases i with (a | b)
    · by_cases ha : a = k
      · rw [ha, hW'_self, splitAt_inl_self]
        change ((D.W k).1.1, z) = ((L k).1, z)
        rw [D.legs_eq k]
      · rw [hW'_ne a ha, splitAt_inl_of_ne ha]
        exact D.legs_eq a
    · cases b
      · rw [hW'_false, splitAt_inr_false]
        change (z, (D.W k).1.2) = (z, (L k).2)
        rw [D.legs_eq k]
      · rw [hW'_true, splitAt_inr_true]
  · -- openness
    intro i
    rcases i with (a | b)
    · by_cases ha : a = k
      · rw [ha, hW'_self]
        intro e he
        exact D.isOpen k e (hPupSub e he)
      · rw [hW'_ne a ha]
        exact D.isOpen a
    · cases b
      · rw [hW'_false]
        intro e he
        exact D.isOpen k e (hPdnSub e he)
      · rw [hW'_true]
        exact hQbP.1
  · -- path witnesses
    intro i
    rcases i with (a | b)
    · by_cases ha : a = k
      · rw [ha, hW'_self]
        exact hPupPath
      · rw [hW'_ne a ha]
        exact D.isPath a
    · cases b
      · rw [hW'_false]
        exact hPdnPath
      · rw [hW'_true]
        exact SimpleGraph.Walk.bypass_isPath Q
  · -- pairwise disjointness
    intro i j hij
    rcases i with (a | bi) <;> rcases j with (b | bj)
    · -- leg vs leg
      by_cases ha : a = k
      · rw [ha, hEs]
        by_cases hb : b = k
        · exact absurd (by rw [ha, hb]) hij
        · rw [hEn b hb]
          exact (D.disj k b (fun h => hij (by rw [ha, h]))).mono hPupSubF le_rfl
      · rw [hEn a ha]
        by_cases hb : b = k
        · rw [hb, hEs]
          exact (D.disj a k ha).mono le_rfl hPupSubF
        · rw [hEn b hb]
          exact D.disj a b (fun h => hij (by rw [h]))
    · cases bj
      · -- leg vs the second half
        by_cases ha : a = k
        · rw [ha, hEs, hEf]
          exact hPupDn
        · rw [hEn a ha, hEf]
          exact (D.disj a k ha).mono le_rfl hPdnSubF
      · -- leg vs the new arm
        by_cases ha : a = k
        · rw [ha, hEs, hEt]
          exact I417Example.edges_disjoint_of_regions
            (fun e he => hEdgeInU k e (hPupSub e he)) hQbP.2 hZone
        · rw [hEn a ha, hEt]
          exact I417Example.edges_disjoint_of_regions
            (fun e he => hEdgeInU a e he) hQbP.2 hZone
    · cases bi
      · -- the second half vs a leg
        by_cases hb : b = k
        · rw [hb, hEs, hEf]
          exact hPupDn.symm
        · rw [hEf, hEn b hb]
          exact ((D.disj b k hb).mono le_rfl hPdnSubF).symm
      · -- the new arm vs a leg
        by_cases hb : b = k
        · rw [hb, hEs, hEt]
          exact (I417Example.edges_disjoint_of_regions
            (fun e he => hEdgeInU k e (hPupSub e he)) hQbP.2 hZone).symm
        · rw [hEt, hEn b hb]
          exact (I417Example.edges_disjoint_of_regions
            (fun e he => hEdgeInU b e he) hQbP.2 hZone).symm
    · -- the two new legs
      cases bi <;> cases bj
      · exact absurd rfl hij
      · rw [hEf, hEt]
        exact I417Example.edges_disjoint_of_regions
          (fun e he => hEdgeInU k e (hPdnSub e he)) hQbP.2 hZone
      · rw [hEt, hEf]
        exact (I417Example.edges_disjoint_of_regions
          (fun e he => hEdgeInU k e (hPdnSub e he)) hQbP.2 hZone).symm
      · exact absurd rfl hij

end PercLib.CriticalLRP.I417FreshFour.Refined
