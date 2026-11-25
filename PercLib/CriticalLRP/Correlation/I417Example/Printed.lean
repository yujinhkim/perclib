/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/Printed.lean ; module path rewritten only.
-/

/-
# The printed `p = 2`, `q = 1` display of Lemma I.4.17, unconditionally

The covering of direction B (`I417B/Cover.prodSet_subset`) has three alternatives:
`diagSet`, `yInSet` and the marked crossings `⋃_w markSet w`.  The `y ∈ Kx` alternative
`yInSet x y x₁ x₂ y₁` is *literally* the marked-crossing alternative at the mark `w = y`:

  `yInSet x y x₁ x₂ y₁ = markSet x y x₁ x₂ y₁ y`,

because the fresh condition of `markSet … y` is `{y↔y} ∘ {y↔y₁}`, and `{y↔y}` is trivially
satisfied with the empty witness.  Hence the two-copy product event is already covered by

  `prodSet ⊆ diagSet ∪ ⋃_w markSet w`   (`prodSet_subset_tight`),

and the excess of the printed expansion is only the marked family, which `I417Example/Excess.markSet_le`
evaluates as `T³(x,y) χ⁴ + 2 T⁴(x,y) χ³`.  This gives the printed display with the printed
constants for the *true* difference `E|K|²E|K| − E[|Kx|²|Ky|1(x↮y)]`:

  `volSq π x · E|Ky| − exclMomentSq π x y ≤ T³(x,y) χ⁴ + 2 T⁴(x,y) χ³`.

(For the larger quantity `I417.excess`, which keeps the redundant `yInSet` family as a separate
summand, the tree-graph bound gives `2 T³χ⁴ + 4 T⁴χ³`; see `I417Example/Excess.excess_le_two_four`.)

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.Excess

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

open PercLib.CriticalLRP.I417

variable {V : Type*} [Countable V]

/-! ## The `y ∈ Kx` alternative is the marked alternative at `w = y` -/

/-- `{y↔y₁}` alone implies the disjoint occurrence `{y↔y} ∘ {y↔y₁}`. -/
theorem connSet_subset_disjOcc_self (y y₁ : V) :
    connSet y y₁ ⊆ Percolation.DisjointOccurrence (connSet y y) (connSet y y₁) := by
  intro ω hω
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr (show Connects ω y y₁ from hω)
  refine ⟨∅, edgeFinset p.edges, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro e he
    exact hp e (mem_edgeFinset.mp he)
  · simp
  · exact connects_refl (∅ : Finset (Sym2 V)) y
  · exact pathConnects_iff.mp ⟨p, fun e he => mem_edgeFinset.mpr he⟩

/-- **`yInSet` is the marked alternative at the mark `y`.** -/
theorem yInSet_subset_markSet (x y x₁ x₂ y₁ : V) :
    yInSet x y x₁ x₂ y₁ ⊆ markSet x y x₁ x₂ y₁ y := by
  rintro ⟨ω₂, ω₁⟩ ⟨hy₁, hbase⟩
  exact ⟨connSet_subset_disjOcc_self y y₁ hy₁, hbase⟩

/-- **The tight covering**: the diagonal alternative together with the marked crossings only. -/
theorem prodSet_subset_tight (x y x₁ x₂ y₁ : V) :
    prodSet x y x₁ x₂ y₁ ⊆ diagSet x y x₁ x₂ y₁ ∪ ⋃ w : V, markSet x y x₁ x₂ y₁ w := by
  intro p hp
  rcases prodSet_subset x y x₁ x₂ y₁ hp with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_iUnion.mpr ⟨y, yInSet_subset_markSet x y x₁ x₂ y₁ h⟩)
  · exact Or.inr h

/-! ## The tight probability inequalities -/

/-- Per-triple form of the tight covering. -/
theorem measure_prodSet_le_tight (π : Sym2 V → unitInterval) (x y x₁ x₂ y₁ : V) :
    ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y x₁ x₂ y₁) ≤
      ((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y x₁ x₂ y₁) +
        ∑' w : V, ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w) := by
  refine le_trans (measure_mono (prodSet_subset_tight x y x₁ x₂ y₁)) ?_
  exact le_trans (measure_union_le _ _) (add_le_add le_rfl (measure_iUnion_le _))

/-- **The two-copy inequality with the tight covering.** -/
theorem twoCopy_moment_le_tight (π : Sym2 V → unitInterval) (x y : V) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) ≤
      (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y x₁ x₂ y₁)) +
        (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V, ∑' w : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w)) := by
  rw [← tsum_prodSet_eq]
  calc (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
        ((edgeMeasure π).prod (edgeMeasure π)) (prodSet x y x₁ x₂ y₁))
      ≤ ∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
          (((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y x₁ x₂ y₁) +
            ∑' w : V, ((edgeMeasure π).prod (edgeMeasure π)) (markSet x y x₁ x₂ y₁ w)) :=
        ENNReal.tsum_le_tsum fun x₁ => ENNReal.tsum_le_tsum fun x₂ =>
          ENNReal.tsum_le_tsum fun y₁ => measure_prodSet_le_tight π x y x₁ x₂ y₁
    _ = _ := by simp only [ENNReal.tsum_add]

/-! ## The printed display -/

/-- **The printed `p = 2`, `q = 1` display of Lemma I.4.17**, unconditionally (for any `π` with
`π e < 1`, on a transitive weighted graph):

  `E|K|² E|K| − E[|Kx|²|Ky|1(x↮y)] ≤ T³(x,y) (E|K|)⁴ + 2 T⁴(x,y) (E|K|)³`.

`hχ` is the transitivity hypothesis (`E|K|` does not depend on the root). -/
theorem printed_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    volSq π x * meanVol π y - exclMomentSq π x y ≤
      T3 π x y * (meanVol π x) ^ 4 + 2 * T4 π x y * (meanVol π x) ^ 3 := by
  classical
  have hME : meanVol π y = ∫⁻ ω, clusterVol ω y ∂(edgeMeasure π) :=
    tsum_connSet_eq_lintegral π y
  have hkey : volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) ≤
      (∑' x₁ : V, ∑' x₂ : V, ∑' y₁ : V,
          ((edgeMeasure π).prod (edgeMeasure π)) (diagSet x y x₁ x₂ y₁)) +
        (∑' w : V, jointSq π x w *
          ((edgeMeasure π) (connSet y w) * meanVol π w)) := by
    refine le_trans (twoCopy_moment_le_tight π x y) (add_le_add le_rfl ?_)
    exact tsum_markSet_le π hπ x y
  rw [tsub_le_iff_right, hME]
  refine le_trans hkey ?_
  rw [tsum_diagSet]
  refine le_trans (add_le_add le_rfl (markSet_le π hπ x y hχ)) (le_of_eq ?_)
  ring

end PercLib.CriticalLRP.I417Example
