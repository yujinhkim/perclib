/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Cover.lean ; module path rewritten only.
-/

/-
# The repaired two-copy covering for Lemma I.4.17 at `p = 2`, `q = 1`

This is the deterministic half of direction B: the correct replacement for the printed step

  "on the event that `y ∉ Kx`, we have `Ky ⊆ K̃y` and a point `z ∈ K̃y` belongs to `Ky` iff there is
   an open path connecting `y` to `z` in `K̃y` that does not visit `Kx`"

of the proof of Lemma I.4.17.  The first half of that sentence is false for the printed coupling
(`not_cluster_subset_forceOn_compl`), so instead of comparing `Ky` with `K̃y` we use the second half
— which *is* true (`mem_cluster_forceOn_compl_iff`, a restatement of
`cluster_forceOn_compl_disjoint`) — to read `y₁ ∈ K̃y` as "there is a fresh walk from `y` to `y₁`
avoiding the base cluster `Kx(ω₁)`", and the failure of that avoidance gives the mark.

Main result: `prodSet_subset`.  On the two-copy event

  `x₁, x₂ ∈ Kx(ω₁)`  and  `y₁ ∈ Ky(ω₂)`

either the restored configuration already satisfies the diagonal condition
`y ∉ Kx(ω₁) ∧ y₁ ∈ K̃y` (so that the pair contributes to the excluded moment), or `y ∈ Kx(ω₁)`,
or the fresh copy contains a disjoint occurrence `{y↔w} ∘ {w↔y₁}` with the mark `w ∈ Kx(ω₁)`.

No `sorry`, no custom axioms; no definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Defs

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Measurability -/

theorem measurableSet_prodSet (x y x₁ x₂ y₁ : V) : MeasurableSet (prodSet x y x₁ x₂ y₁) :=
  (measurableSet_connSet y y₁).prod
    ((measurableSet_connSet x x₁).inter (measurableSet_connSet x x₂))

theorem measurableSet_diagSet (x y x₁ x₂ y₁ : V) : MeasurableSet (diagSet x y x₁ x₂ y₁) := by
  have h : diagSet x y x₁ x₂ y₁ =
      {p : TwoCopy V | p.2 ∈ connSet x x₁} ∩ {p : TwoCopy V | p.2 ∈ connSet x x₂} ∩
        {p : TwoCopy V | p.2 ∉ connSet x y} ∩
        {p : TwoCopy V | restoreMap x p ∈ connSet y y₁} := by
    ext p
    simp only [diagSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [h]
  refine ((MeasurableSet.inter ?_ ?_).inter ?_).inter ?_
  · exact measurable_snd (measurableSet_connSet x x₁)
  · exact measurable_snd (measurableSet_connSet x x₂)
  · exact (measurable_snd (measurableSet_connSet x y)).compl
  · exact (measurable_restoreMap x) (measurableSet_connSet y y₁)

theorem measurableSet_yInSet (x y x₁ x₂ y₁ : V) : MeasurableSet (yInSet x y x₁ x₂ y₁) :=
  (measurableSet_connSet y y₁).prod
    (((measurableSet_connSet x x₁).inter (measurableSet_connSet x x₂)).inter
      (measurableSet_connSet x y))

theorem measurableSet_markSet (x y x₁ x₂ y₁ w : V) : MeasurableSet (markSet x y x₁ x₂ y₁ w) :=
  (measurableSet_disjSet y w w y₁).prod
    (((measurableSet_connSet x x₁).inter (measurableSet_connSet x x₂)).inter
      (measurableSet_connSet x w))

/-! ## The covering -/

/-- **The repaired two-copy covering.**  Every pair `(ω₂, ω₁)` with `x₁, x₂ ∈ Kx(ω₁)` and
`y₁ ∈ Ky(ω₂)` lies in one of the three alternatives: the diagonal event `diagSet`, the
`y ∈ Kx(ω₁)` event `yInSet`, or a marked crossing `markSet … w`.

The proof is the paper's case analysis made correct: if `y ∉ Kx(ω₁)` and `y₁ ∉ K̃y` then *no*
`ω₂`-open walk from `y` to `y₁` avoids `Kx(ω₁)` (otherwise `mem_cluster_forceOn_compl_iff` would
put `y₁` in `K̃y`), which is exactly the hypothesis of `exists_fresh_disjOcc_of_no_avoid`. -/
theorem prodSet_subset (x y x₁ x₂ y₁ : V) :
    prodSet x y x₁ x₂ y₁ ⊆
      diagSet x y x₁ x₂ y₁ ∪ yInSet x y x₁ x₂ y₁ ∪ ⋃ w : V, markSet x y x₁ x₂ y₁ w := by
  rintro ⟨ω₂, ω₁⟩ ⟨h1, h2⟩
  by_cases hy : ω₁ ∈ connSet x y
  · -- `y ∈ Kx(ω₁)`: the `yInSet` alternative
    exact Or.inl (Or.inr ⟨h1, ⟨⟨h2.1, h2.2⟩, hy⟩⟩)
  · by_cases hy₁ : restoreMap x (ω₂, ω₁) ∈ connSet y y₁
    · -- the diagonal case
      exact Or.inl (Or.inl ⟨h2, hy, hy₁⟩)
    · -- `y ∉ Kx`, `y₁ ∉ K̃y`: the fresh walk must meet `Kx`, giving the mark
      have hyK : y ∉ cluster ω₁ x := fun hc => hy (mem_cluster_iff.mpr hc)
      have hno : ¬ ∃ p : (⊤ : SimpleGraph V).Walk y y₁,
          (∀ e ∈ p.edges, e ∈ ω₂) ∧ (∀ v ∈ p.support, v ∉ cluster ω₁ x) := by
        rintro ⟨p, hp, hav⟩
        refine hy₁ (mem_cluster_iff.mp ?_)
        refine (mem_cluster_forceOn_compl_iff (ω := ω₁) (ω' := ω₂) (o := x) (y := y) (z := y₁)
          hyK).mpr ⟨p, hp, ?_⟩
        intro e he v hv
        exact hav v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩))
      obtain ⟨w, hwK, hw⟩ := exists_fresh_disjOcc_of_no_avoid (ω₁ := ω₁) (ω₂ := ω₂)
        (o := x) (y := y) (z := y₁) h1 hno
      refine Or.inr (Set.mem_iUnion.mpr ⟨w, ?_⟩)
      exact ⟨hw, ⟨⟨h2.1, h2.2⟩, mem_cluster_iff.mp hwK⟩⟩

end PercLib.CriticalLRP.I417
