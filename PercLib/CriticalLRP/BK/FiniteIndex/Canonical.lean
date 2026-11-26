/-
Independently built canonical instantiation of the finite-index BK bridge.
Swarm smwwtd5t5, member m2 (direction B).
Production read only, at HEAD 4c53bb5a8e76a4358a426adf71169b916b90f51f.
-/

/-
# BK at the canonical connection events, and the atlas instantiation

`FiniteBK.lean` proves `P(DisjFam A) ≤ ∏ P(A i)` for a finite index `ι` and arbitrary increasing
finitely witnessed `A i` on `Config V = Set (Sym2 V)`, with `V` only countable.  This file
instantiates it at the canonical connection events `connSet u v` of §I.2.1, which is the form in
which the atlas union bound of Lemma I.4.16 (pp. 43--45) uses BK, and reconciles the result with
the atlas layer `TreeExpansion.AtlasRealization`.

Contents:

* `edgeMeasure_bk_connSet_fam` — for any finite `ι` and endpoints `u v : ι → V`,
  `P(all {uᵢ ↔ vᵢ} with pairwise disjoint open witnesses) ≤ ∏ᵢ P(uᵢ ↔ vᵢ)`.
  No finiteness of `V` is used, so this applies to the canonical countable model directly.
* `edgeMeasure_bk_atlas` — the same bound with the index the atlas edge type `Real.AEdge t` of one
  fully labelled shape `t : RTree α` with vertices `φ : t.IPos → V`; the number of factors is
  `2 * t.numLeaves - 1` (production `Real.card_aedge`).
* `mem_diagEvent_iff_disjFam` — the diagram event `Real.DiagEvent` of that atlas layer is exactly
  `DisjFam` of its edge connection events, so the bound above is *the* bound on the realised atlas,
  not on some surrogate.
* `connSet_self`, `edgeMeasure_connSet_self`, `disjFam_connSet_self_option`,
  `edgeMeasure_bk_connSet_fam_diag` — the diagonal `u = v`: `{u ↔ u}` is certain, is witnessed by
  `∅`, and contributes the factor `1`.  No fictitious edge has to be introduced for a degenerate
  atlas edge.
* `edgeMeasure_iUnion_le_tsum`, `edgeMeasure_iUnion_bk_le_tsum` — the union bound over an
  arbitrary *countable* family of diagrams (the sum over shapes and internal positions), with no
  measurability hypothesis needed, by subadditivity of the outer measure.
-/

module

public import PercLib.CriticalLRP.BK.FiniteIndex.BK
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Cover

/-!
# Canonical connection events and the atlas index
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-! ## BK for a finite family of canonical connection events -/

/-- **BK at canonical connection events, `ℝ≥0∞` form.**  For a finite index type `ι` and arbitrary
endpoints `uᵢ, vᵢ`, the probability that all the connections `uᵢ ↔ vᵢ` hold simultaneously with
pairwise edge-disjoint open witnesses is at most the product of the individual connection
probabilities.

Only the *index* is finite; `V` is an arbitrary countable vertex set and the edge set `Sym2 V` is
infinite, so this is not a finite-box statement. -/
theorem edgeMeasure_bk_connSet_fam (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {ι : Type*} [Fintype ι] (u v : ι → V) :
    edgeMeasure π (Percolation.DisjFam fun i => connSet (u i) (v i))
      ≤ ∏ i, edgeMeasure π (connSet (u i) (v i)) :=
  Percolation.bk_disjFam π hπ (fun _ => isUpper_connSet _ _) (fun _ => finiteWitness_connSet _ _)

/-- **BK at canonical connection events, real form.** -/
theorem edgeMeasure_bk_connSet_fam_real (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {ι : Type*} [Fintype ι] (u v : ι → V) :
    (edgeMeasure π).real (Percolation.DisjFam fun i => connSet (u i) (v i))
      ≤ ∏ i, (edgeMeasure π).real (connSet (u i) (v i)) :=
  Percolation.bk_disjFam_real π hπ (fun _ => isUpper_connSet _ _)
    (fun _ => finiteWitness_connSet _ _)

/-! ## The diagonal: `u ↔ u` is certain and costs no edge -/

/-- `{u ↔ u}` is the whole space: the empty path is an honest path, so no open edge is needed. -/
theorem connSet_self (u : V) : connSet u u = Set.univ := by
  ext ω
  exact ⟨fun _ => Set.mem_univ ω, fun _ => connects_refl ω u⟩

/-- The diagonal connection event has probability `1`, so a degenerate atlas edge contributes the
factor `P(u ↔ u) = 1` to the product of connection probabilities. -/
theorem edgeMeasure_connSet_self (π : Sym2 V → unitInterval) (u : V) :
    edgeMeasure π (connSet u u) = 1 := by
  rw [connSet_self, measure_univ]

/-- Real form of `edgeMeasure_connSet_self`. -/
theorem edgeMeasure_connSet_self_real (π : Sym2 V → unitInterval) (u : V) :
    (edgeMeasure π).real (connSet u u) = 1 := by
  rw [measureReal_def, edgeMeasure_connSet_self, ENNReal.toReal_one]

/-- **A degenerate atlas edge is a free index.**  Adding an index whose two ends coincide does not
change the disjoint-occurrence event: such an index is witnessed by `∅`, which is disjoint from
every other witness and consumes no open edge. -/
theorem disjFam_connSet_self_option {ι : Type*} (u v : ι → V) (w : V) :
    Percolation.DisjFam
        (fun o : Option ι => connSet (match o with | none => w | some i => u i)
          (match o with | none => w | some i => v i))
      = Percolation.DisjFam (fun i => connSet (u i) (v i)) := by
  have hfun : (fun o : Option ι => connSet (match o with | none => w | some i => u i)
        (match o with | none => w | some i => v i))
      = fun o : Option ι => match o with
        | none => Set.univ
        | some i => connSet (u i) (v i) := by
    funext o
    rcases o with _ | i
    · exact connSet_self w
    · rfl
  rw [hfun]
  exact Percolation.disjFam_option_univ (fun i => connSet (u i) (v i))

/-- **The BK bound with one degenerate index.**  The degenerate index contributes the factor
`P(w ↔ w) = 1`, and the bound is the product over the remaining indices: no fictitious edge. -/
theorem edgeMeasure_bk_connSet_fam_diag (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {ι : Type*} [Fintype ι] (u v : ι → V) (w : V) :
    edgeMeasure π (Percolation.DisjFam
        (fun o : Option ι => connSet (match o with | none => w | some i => u i)
          (match o with | none => w | some i => v i)))
      ≤ ∏ i, edgeMeasure π (connSet (u i) (v i)) := by
  rw [disjFam_connSet_self_option]
  exact edgeMeasure_bk_connSet_fam π hπ u v

/-! ## The atlas of one fully labelled shape -/

/-- **BK for one atlas diagram.**  For a rooted binary shape `t` with labels `α`, a terminal map
`y : α → V`, a root leaf at `c` and internal vertices at `φ`, the probability that all
`2 * t.numLeaves - 1` atlas edges (production `Real.AEdge t`, `Real.card_aedge`) are realised by
pairwise edge-disjoint open paths is at most the product, over the atlas edges, of the connection
probabilities of their two ends `srcPos` and `dstPos`.

This is the canonical countable version of `Real.prob_diagEvent_le`: it needs no finite edge type
and no finite vertex type. -/
theorem edgeMeasure_bk_atlas (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {α : Type*} (y : α → V) (c : V) (t : TreeExpansion.RTree α) (φ : t.IPos → V) :
    edgeMeasure π (Percolation.DisjFam fun e : TreeExpansion.Real.AEdge t =>
        connSet (TreeExpansion.Real.srcPos t φ c e) (TreeExpansion.Real.dstPos t φ y e))
      ≤ ∏ e : TreeExpansion.Real.AEdge t,
          edgeMeasure π (connSet (TreeExpansion.Real.srcPos t φ c e)
            (TreeExpansion.Real.dstPos t φ y e)) :=
  edgeMeasure_bk_connSet_fam π hπ _ _

/-- **The open graph of a finite edge index is the canonical open graph of the configuration it
carries.**  `TreeGraph.openGraph` and the canonical `openGraph` are both
`SimpleGraph.fromEdgeSet`, so the finite-index picture embeds in the canonical model with no
transport of paths at all. -/
theorem openGraph_edgeSetOf {E : Type*} (ends : E → Sym2 V) (s : Finset E) :
    TreeGraph.openGraph ends s = openGraph (TreeGraph.edgeSetOf ends s) := rfl

/-- **`TreeGraph.Conn` is canonical `Connects`** at the configuration `edgeSetOf ends s`. -/
theorem conn_iff_connects {E : Type*} (ends : E → Sym2 V) (s : Finset E) (x y : V) :
    TreeGraph.Conn ends s x y ↔ Connects (TreeGraph.edgeSetOf ends s) x y := Iff.rfl

/-- **A realized atlas is a canonical disjoint occurrence.**  If a diagram of the atlas layer is
realized inside the finite edge index `E` (production `Real.DiagEvent`), then the canonical
configuration it carries, `TreeGraph.edgeSetOf ends ω`, lies in `DisjFam` of the canonical
connection events at the atlas edges.  So the canonical BK bound `edgeMeasure_bk_atlas` applies to
realized atlases.

Injectivity of `ends` is needed and used: the atlas application takes `E := ↥W` the finite set of
edge witnesses and `ends` its inclusion into `Sym2 V`, which is injective.  (For a non-injective
`ends` two disjoint witnesses of `E` could share a value in `Sym2 V`, so their images need not be
disjoint.) -/
theorem diagEvent_subset_disjFam {E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    {α : Type*} [Fintype α] [DecidableEq α] {ends : E → Sym2 V} (hinj : Function.Injective ends)
    (y : α → V) (c : V) (t : TreeExpansion.RTree α) (φ : t.IPos → V) {ω : Finset E}
    (hω : ω ∈ TreeExpansion.Real.DiagEvent ends y c t φ) :
    TreeGraph.edgeSetOf ends ω ∈ Percolation.DisjFam (fun e : TreeExpansion.Real.AEdge t =>
      connSet (TreeExpansion.Real.srcPos t φ c e) (TreeExpansion.Real.dstPos t φ y e)) := by
  classical
  obtain ⟨wit, hsub, hdisj, hconn⟩ := hω
  refine ⟨fun e => Finset.image ends (wit e), ?_, ?_, ?_⟩
  · intro e x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨a, hsub e ha, rfl⟩
  · intro e
    have hset : ((Finset.image ends (wit e) : Finset (Sym2 V)) : Set (Sym2 V))
        = TreeGraph.edgeSetOf ends (wit e) := by
      ext x
      simp only [Finset.coe_image, TreeGraph.edgeSetOf, Set.mem_image, Set.mem_ofPred_eq,
        Finset.mem_coe]
    rw [hset]
    exact (conn_iff_connects ends (wit e) _ _).mp (hconn e)
  · intro e e' hee'
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hx'
    have hba : b = a := hinj hab
    subst hba
    exact (Finset.disjoint_left.mp (hdisj e e' hee') ha) hb

/-! ## Union bound over a countable family of diagrams

The source proof takes a union bound over the combinatorial structures of the tree, i.e. over a
*countable* set of shapes and internal positions, and then bounds each term by BK.  Subadditivity
of the outer measure is all that the union step needs: no measurability of the individual
diagrams, and no finiteness of the index, is required. -/

/-- **Countable union bound.** -/
theorem edgeMeasure_iUnion_le_tsum (π : Sym2 V → unitInterval) {κ : Type*} [Countable κ]
    (D : κ → Set (Config V)) (b : κ → ℝ≥0∞) (h : ∀ k, edgeMeasure π (D k) ≤ b k) :
    edgeMeasure π (⋃ k, D k) ≤ ∑' k, b k :=
  (measure_iUnion_le D).trans (ENNReal.tsum_le_tsum h)

/-- **Union bound over a countable family of atlas diagrams, then BK.**  This is the shape of the
union step of Lemma I.4.16: sum over the countable set of diagrams of the product of the
connection probabilities of the atlas edges of each diagram. -/
theorem edgeMeasure_iUnion_bk_le_tsum (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {κ ι : Type*} [Countable κ] [Fintype ι] (u v : κ → ι → V) :
    edgeMeasure π (⋃ k, Percolation.DisjFam fun i => connSet (u k i) (v k i))
      ≤ ∑' k, ∏ i, edgeMeasure π (connSet (u k i) (v k i)) :=
  edgeMeasure_iUnion_le_tsum π
    (fun k => Percolation.DisjFam fun i => connSet (u k i) (v k i))
    (fun k => ∏ i, edgeMeasure π (connSet (u k i) (v k i)))
    (fun k => edgeMeasure_bk_connSet_fam π hπ (u k) (v k))

/-- **Union bound over all fully labelled shapes with a fixed leaf set and all internal
positions.**  This is the canonical countable form of the union step of Lemma I.4.16: the shapes
with leaf set `Z` form the finite type `TreeExpansion.LTon α Z`, the positions `φ : t.IPos → V`
are countable, and each single diagram is bounded by BK (`edgeMeasure_bk_atlas`).

The resulting right-hand side is the sum over `(t, φ)` of the product of the connection
probabilities of the `2 * #Z - 1` atlas edges of `t` — the quantity that the source then regroups
into three-point and two-point functions.  No measurability of the individual diagrams and no
finite vertex set is used. -/
theorem edgeMeasure_iUnion_atlas_le_tsum (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {α : Type*} [Fintype α] [DecidableEq α] (y : α → V) (c : V) (Z : Finset α) :
    edgeMeasure π (⋃ p : (Σ t : TreeExpansion.LTon α Z,
          ((t : TreeExpansion.RTree α)).IPos → V),
        Percolation.DisjFam fun e : TreeExpansion.Real.AEdge (p.1 : TreeExpansion.RTree α) =>
          connSet (TreeExpansion.Real.srcPos (p.1 : TreeExpansion.RTree α) p.2 c e)
            (TreeExpansion.Real.dstPos (p.1 : TreeExpansion.RTree α) p.2 y e))
      ≤ ∑' p : (Σ t : TreeExpansion.LTon α Z, ((t : TreeExpansion.RTree α)).IPos → V),
          ∏ e : TreeExpansion.Real.AEdge (p.1 : TreeExpansion.RTree α),
            edgeMeasure π
              (connSet (TreeExpansion.Real.srcPos (p.1 : TreeExpansion.RTree α) p.2 c e)
                (TreeExpansion.Real.dstPos (p.1 : TreeExpansion.RTree α) p.2 y e)) :=
  edgeMeasure_iUnion_le_tsum π _ _
    (fun p => edgeMeasure_bk_atlas π hπ y c (p.1 : TreeExpansion.RTree α) p.2)

/-! ## Measurability of the disjoint-occurrence family

The event is a countable union over the possible finite witness families, and each term fixes the
finite set of edges that must be open; so it is measurable with no hypothesis on the events `A i`
beyond the finiteness of the index.  (The union bound above does not need this, since it only uses
subadditivity of the outer measure; it is recorded for consumers that want to apply
measure-theoretic operations to the diagrams themselves.) -/

/-- **Measurability of the disjoint-occurrence family** in the canonical model. -/
theorem measurableSet_disjFam {ι : Type*} [Fintype ι] (A : ι → Set (Config V)) :
    MeasurableSet (Percolation.DisjFam A) := by
  classical
  have h : Percolation.DisjFam A = ⋃ U : {W : ι → Finset (Sym2 V) //
      (∀ i, (W i : Set (Sym2 V)) ∈ A i) ∧ (∀ i j, i ≠ j → Disjoint (W i) (W j))},
      {ω : Config V | ∀ i, ((U : ι → Finset (Sym2 V)) i : Set (Sym2 V)) ⊆ ω} := by
    ext ω
    constructor
    · rintro ⟨W, hsub, hmem, hdisj⟩
      exact Set.mem_iUnion.mpr ⟨⟨W, hmem, hdisj⟩, hsub⟩
    · intro hω
      rw [Set.mem_iUnion] at hω
      obtain ⟨U, hU⟩ := hω
      exact ⟨U.1, hU, U.2.1, U.2.2⟩
  rw [h]
  refine MeasurableSet.iUnion fun U => ?_
  have hset : {ω : Config V | ∀ i, ((U : ι → Finset (Sym2 V)) i : Set (Sym2 V)) ⊆ ω}
      = {ω : Config V | ∀ e ∈ Finset.univ.biUnion (U : ι → Finset (Sym2 V)), e ∈ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    exact ⟨fun h e ⟨i, hi⟩ => h i e hi, fun h i e he => h e ⟨i, he⟩⟩
  rw [hset]
  exact measurableSet_allOpen _

end PercLib.CriticalLRP
