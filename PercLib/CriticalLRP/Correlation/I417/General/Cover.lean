/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m5/I417Gen/Cover.lean; module path rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.General.Defs

/-!
# The marked covering of Lemma I.4.17 for arbitrary finite `p, q`

This is the deterministic heart of the general-`p,q` two-copy expansion: every pair of
configurations `ρ = (ω₂, ω₁)` whose base copy carries the `p` arms `f ⊆ K_x(ω₁)` and whose fresh
copy carries the `q` arms `g ⊆ K_y(ω₂)` satisfies at least one of

* the **diagonal** condition: `y ∉ K_x(ω₁)` and `g ⊆ K̃_y`, where `K̃_y` is the cluster of `y`
in the
  restored configuration `restoreMap x ρ` (`diagSet`);
* or the pair lies in the **marked family** `markSet … j w` for some terminal `j : Fin q` and some
  mark `w ∈ K_x(ω₁)`: in the fresh copy all arms `g` are in `K_y(ω₂)` and the two halves
  `y↔w`, `w↔g j` occur disjointly.

The paper's proof of Lemma I.4.17 assumes `Ky ⊆ K̃y` on `{y ∉ Kx}`; that inclusion is false for the
base cluster (`Correlation/PrintedEventFails.lean`, `not_cluster_subset_forceOn_compl`).  The
provable replacement, already used for `p = 2, q = 1` (`Correlation/I417/Cover.lean`), is the exact
characterisation `mem_cluster_forceOn_compl_iff`: on `{y ∉ Kx}`, `z ∈ K̃y` iff there is an
`ω₂`-open walk `y → z` whose edges avoid `K_x(ω₁)`.  If some arm `g j` is **not** in `K̃y`, no such
walk exists; since `y ↔ g j` holds in the fresh copy, a shortest fresh walk must meet `K_x(ω₁)`,
and splitting it at the first vertex `w` of `K_x(ω₁)` gives two edge-disjoint fresh walks
`y → w` and `w → g j` — exactly `freshMark y g j w`.

The paper's separate alternative `y ∈ K_x` is *not* a separate family: it is the marked family at
the mark `w = y` (`mem_markSet_of_yInKx`, using the empty witness for `y ↔ y`).  So the covering is
the paper's single sum over `w`, with the terminal `j` carried along.

`q ≥ 1` is needed: with `q = 0` there is no arm to terminate the marked walk on, and the marked
family is empty while `prodSet` is not.

No `sorry`, no custom axioms; no definitions.
-/


open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Gen

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **The marked covering for arbitrary finite `p, q`.**  On the two-copy product event, either the
diagonal alternative holds (base `y ∉ K_x` and restored `g ⊆ K̃_y`), or the pair lies in the marked
family at some terminal `j : Fin q` and some mark `w : V`. -/
theorem prodSet_subset (x y : V) {p q : ℕ} (hq : 1 ≤ q) (f : Fin p → V) (g : Fin q → V) :
    prodSet x y f g ⊆ diagSet x y f g ∪ ⋃ jw : Fin q × V, markSet x y f g jw.1 jw.2 := by
  rintro ρ ⟨hg, hf⟩
  by_cases hy : ρ.2 ∈ connSet x y
  · -- the paper's `y ∈ K_x` alternative: mark `w = y`, any terminal `j`
    refine Or.inr (Set.mem_iUnion.mpr ⟨(⟨0, hq⟩, y), ?_⟩)
    exact mem_markSet_of_yInKx ⟨0, hq⟩ hf hy hg
  · by_cases hdiag : restoreMap x ρ ∈ I417A.labelEvent y g
    · exact Or.inl ⟨hf, hy, hdiag⟩
    · -- some arm is missing from the restored cluster: split a shortest fresh walk at `K_x(ω₁)`
      obtain ⟨j, hj⟩ := not_forall.mp hdiag
      have hyK : y ∉ cluster ρ.2 x := fun hc => hy (mem_cluster_iff.mpr hc)
      have hno : ¬ ∃ p : (⊤ : SimpleGraph V).Walk y (g j),
          (∀ e ∈ p.edges, e ∈ ρ.1) ∧ (∀ v ∈ p.support, v ∉ cluster ρ.2 x) := by
        rintro ⟨p, hp, hav⟩
        exact hj ((mem_cluster_forceOn_compl_iff (ω := ρ.2) (ω' := ρ.1) (o := x) (y := y)
          (z := g j) hyK).mpr ⟨p, hp, fun e he v hv => hav v
            (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩))⟩)
      obtain ⟨b, hbK, hdisj⟩ := exists_fresh_disjOcc_of_no_avoid (ω₁ := ρ.2) (ω₂ := ρ.1)
        (o := x) (y := y) (z := g j) (mem_cluster_iff.mp (hg j)) hno
      exact Or.inr (Set.mem_iUnion.mpr ⟨(j, b), ⟨⟨hdisj, hg⟩, hf, mem_cluster_iff.mp hbK⟩⟩)

/-- **The per-tuple measure inequality** (`ℝ≥0∞`, no hypothesis beyond `1 ≤ q`): the probability of
the two-copy product event is at most the diagonal probability plus the sum of the marked
probabilities. -/
theorem measure_prodSet_le (π : Sym2 V → unitInterval) (x y : V) {p q : ℕ} (hq : 1 ≤ q)
    (f : Fin p → V) (g : Fin q → V) :
    ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y f g) ≤
      ((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y f g) +
        ∑' jw : Fin q × V,
          ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y f g jw.1 jw.2) := by
  refine le_trans (measure_mono (prodSet_subset x y hq f g)) ?_
  refine le_trans (measure_union_le (μ := (edgeMeasure π).prod (edgeMeasure π)) _ _)
    (add_le_add le_rfl (measure_iUnion_le _))

end PercLib.CriticalLRP.I417Gen
