/-
Independently rebuilt and integrated from the accepted `smwx9itnu/m2` artifact
`.ultramath/smwx9itnu/m2/Gen`. Production integration revision:
`8ae938fa49a73456688d438f25ef2441c282b2f4`.
The base split/diagram API is shared with `I417FreshFour.Refined` instead of
being duplicated.
-/
/-
Independently built for swarm `smwx9itnu`, member `m2`, direction GENERAL-Q-VECTOR-COVER.
No production files are modified; this module is read-only against production.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Iter.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Three.Refined.Cover

/-!
# Lemma I.4.17 for arbitrary `q`: the attachment step and the pin invariant

This file proves the deterministic step that turns one diagram (legs plus pairwise edge-disjoint
open path witnesses) into the next one by first-hitting the next arm against the diagram and
splitting the hit leg at the hit vertex.  It is the index-generic attachment step already used by
the accepted `q = 4` artifact, restated in this development's namespace so that the general-`q`
induction can iterate it.

* `shapeOfI_of_diag` : a witnessed diagram realises the index-generic shape.
* `baseDiag` : the two halves of `freshMark`'s disjoint occurrence form the `Fin 2` base diagram.
* `step` : given a diagram `D`, a vertex `z` of its support, and an open walk `Q : z → d` whose
  edges meet the diagram only at `z`, some leg `k` can be split at `z` and the arm `z → d`
  attached, producing a diagram on the index type `ι ⊕ Bool` with legs `splitAt L k z d`.
* `splitAt_left` : splitting any leg keeps the source of every other leg's slot, in particular the
  leftmost slot `first n` still starts at the pin `y`.
* `Hist.first_leg_start` : consequently every stage of the history has its first leg starting at
  `y`, so `y` is available as the endpoint of every subsequent first hit.

No definitions are introduced here; every definition is in `Gen/Defs.lean`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417GenIter

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## From a witnessed diagram to the index-generic shape -/

/-- A diagram with witnesses realises the index-generic shape of the legs it witnesses. -/
theorem shapeOfI_of_diag {ι : Type*} {ω : Config V} {L : ι → V × V} (D : Diag ι ω L) :
    ShapeOfI (fun i => (D.W i).1) ω := by
  refine ⟨fun i => I417Example.edgeFinset (D.W i).2.edges, ?_, ?_, ?_⟩
  · intro i e he
    exact D.isOpen i e (I417Example.mem_edgeFinset.mp he)
  · intro i
    exact pathConnects_iff.mp ⟨(D.W i).2, fun x hx => I417Example.mem_edgeFinset.mpr hx⟩
  · intro i j hij
    exact D.disj i j hij

/-- A diagram with witnesses realises the index-generic shape of its declared legs. -/
theorem shapeOfI_of_diag_legs {ι : Type*} {ω : Config V} {L : ι → V × V} (D : Diag ι ω L) :
    ShapeOfI L ω := by
  have h : (fun i => (D.W i).1) = L := funext D.legs_eq
  rw [← h]
  exact shapeOfI_of_diag D

/-! ## The two-leg base -/

/-! ## Walking from a named vertex -/

/-- A walk's endpoint is a *term*, so `v ∈ p.support` at a propositionally equal vertex needs the
cast of the walk, not a rewrite inside its type. -/
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

/-! ## Splitting keeps the source slot -/

/-- The leftmost leg keeps its source when a leg is split: the slot of the split leg is reused for
the half that keeps its source. -/
theorem splitAt_left {ι : Type*} [DecidableEq ι] {L : ι → V × V} {y : V} {l : ι}
    (hl : (L l).1 = y) (k : ι) (z d : V) :
    ((splitAt L k z d) (Sum.inl l)).1 = y := by
  by_cases h : l = k
  · rw [h] at hl ⊢
    rw [splitAt_inl_self]
    exact hl
  · rw [splitAt_inl_of_ne h]
    exact hl

/-- **The pin invariant.**  Every stage of an attachment history has its first leg starting at
the pin `y`: `(Hist.legs H y w ga (first n)).1 = y`.  Hence `y` lies in the diagram support at
every stage and can serve as the endpoint of the next first hit. -/
theorem Hist.first_leg_start {n : ℕ} (H : Hist V n) (y w ga : V) :
    (H.legs y w ga (first n)).1 = y := by
  induction H with
  | nil => rfl
  | @snoc m H k z d ih =>
    change ((splitAt (H.legs y w ga) k z d) (Sum.inl (first m))).1 = y
    exact splitAt_left ih k z d

/-! ## The attachment step -/

/-- **Inside-segment attachment.**  Let `D` be a diagram in `ω` and let `Q : z → d` be an open
walk from a vertex `z` of the diagram to a new arm `d`, whose edges have both endpoints in
`{z} ∪ Uᶜ`, where `U = ⋃ i, supp (W i)` is the vertex set of the diagram.  Then **some** leg `k`
of `D` contains `z`, and splitting that leg at `z` and attaching `Q` gives a diagram with two more
legs, realising `splitAt L k z d`.

No non-degeneracy is assumed: `z` may be either endpoint of a leg (the corresponding half is then
a trivial walk), a leg may be trivial, and `d` may coincide with any vertex. -/
theorem step {ι : Type*} [DecidableEq ι] {ω : Config V} {L : ι → V × V} (D : Diag ι ω L)
    {z d : V} (hz : z ∈ ⋃ i, {v : V | v ∈ (D.W i).2.support})
    (Q : (⊤ : SimpleGraph V).Walk z d) (hQop : ∀ e ∈ Q.edges, e ∈ ω)
    (hQreg : ∀ e ∈ Q.edges, ∀ v ∈ e, v ∈ ({z} ∪ (⋃ i, {v : V | v ∈ (D.W i).2.support})ᶜ)) :
    ∃ k : ι, Nonempty (Diag (ι ⊕ Bool) ω (splitAt L k z d)) := by
  classical
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
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
  have hQbP : (∀ e ∈ Q.bypass.edges, e ∈ ω) ∧
      (∀ e ∈ Q.bypass.edges, ∀ v ∈ e, v ∈ ({z} ∪ (⋃ i, {v : V | v ∈ (D.W i).2.support})ᶜ)) := by
    refine ⟨fun e he => hQop e (SimpleGraph.Walk.edges_bypass_subset_edges Q he), ?_⟩
    intro e he v hv
    exact hQreg e (SimpleGraph.Walk.edges_bypass_subset_edges Q he) v hv
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
  · intro i
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
  · intro i
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
  · intro i
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
  · intro i j hij
    rcases i with (a | bi) <;> rcases j with (b | bj)
    · by_cases ha : a = k
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
      · by_cases ha : a = k
        · rw [ha, hEs, hEf]
          exact hPupDn
        · rw [hEn a ha, hEf]
          exact (D.disj a k ha).mono le_rfl hPdnSubF
      · by_cases ha : a = k
        · rw [ha, hEs, hEt]
          exact I417Example.edges_disjoint_of_regions
            (fun e he => hEdgeInU k e (hPupSub e he)) hQbP.2 hZone
        · rw [hEn a ha, hEt]
          exact I417Example.edges_disjoint_of_regions
            (fun e he => hEdgeInU a e he) hQbP.2 hZone
    · cases bi
      · by_cases hb : b = k
        · rw [hb, hEs, hEf]
          exact hPupDn.symm
        · rw [hEf, hEn b hb]
          exact ((D.disj b k hb).mono le_rfl hPdnSubF).symm
      · by_cases hb : b = k
        · rw [hb, hEs, hEt]
          exact (I417Example.edges_disjoint_of_regions
            (fun e he => hEdgeInU k e (hPupSub e he)) hQbP.2 hZone).symm
        · rw [hEt, hEn b hb]
          exact (I417Example.edges_disjoint_of_regions
            (fun e he => hEdgeInU b e he) hQbP.2 hZone).symm
    · cases bi <;> cases bj
      · exact absurd rfl hij
      · rw [hEf, hEt]
        exact I417Example.edges_disjoint_of_regions
          (fun e he => hEdgeInU k e (hPdnSub e he)) hQbP.2 hZone
      · rw [hEt, hEf]
        exact (I417Example.edges_disjoint_of_regions
          (fun e he => hEdgeInU k e (hPdnSub e he)) hQbP.2 hZone).symm
      · exact absurd rfl hij

end PercLib.CriticalLRP.I417GenIter
