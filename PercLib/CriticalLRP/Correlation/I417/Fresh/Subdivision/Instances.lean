/-
Independently rebuilt and integrated from the accepted `smwx6p0op/m2` artifact
`.ultramath/smwx6p0op/m2/GQDepth`. Production integration revision:
`c83993396c566d21a0abe4051ed84dd6dab6093e`. The coordinator uses the production
namespace and fully qualified imports; this package is diagram infrastructure,
not an event-cover theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Poly
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Compose

/-!
Independently built for swarm `smwx6p0op`, member `m2`, direction DEPTH-RANGE-I417.

# Checked instances of the subdivided-edge fresh diagram

The value theorem `subW_eq` is shape-independent, so a `q`-arm fresh diagram is worth
`χ^(2q-ℓ) T^ℓ` for every `1 ≤ ℓ ≤ q`.  This file checks that the family is non-vacuous and that its
depth range is *attained*, at `q = 1, 2, 3` and in general:

* `comb_subW_max` — for every `q ≥ 1` the comb `combTree (q-1)` has a leaf at depth `q`, so the
  fresh diagram with the mark on the edge above that leaf is worth `χ^q · T^q`.  The printed upper
  end `p+q+1` of the composed range is therefore attained, not merely an upper bound;
* `subW_two_leaf_depth_one/_two` — the `q = 2` family: `χ^3 T` and `χ^2 T^2`.  These are exactly the
  two monomials of the accepted `q = 2` cover `smwx5p94b/m1` (`M1Fresh.freshTwoRefined`:
  `χ^2·T^2(w,y) + χ^3·T(w,y)`), the `ℓ = 1` term being `ShapeB` and the `ℓ = 2` term `ShapeA`;
* `subW_two_leaf_shapeB/_shapeA` — the *unfolded* forms: the `ℓ = 1` diagram is the subdivision of
  the top edge `y → p` (both arms below `p`), the `ℓ = 2` diagram is the subdivision of the edge
  above the arm (`y → p → w → g 0`, the other arm below `p`).  So the definition is literally the
  four-edge shapes, not a shape-abstract stand-in;
* `subW_three_leaf_*` — the `q = 3` family: `χ^5 T`, `χ^4 T^2`, `χ^3 T^3` on one three-leaf shape,
  the first compiled instance beyond the accepted `q = 2` case.
-/

open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh.Subdivision

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.I417Base

universe u

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The comb: leaf count and deepest leaf -/

/-- The comb with `n` nested nodes has `n + 1` leaves. -/
theorem combTree_numLeaves : ∀ n : ℕ, (combTree n).numLeaves = n + 1
  | 0 => rfl
  | n + 1 => by
      change (RTree.node (RTree.leaf ()) (combTree n)).numLeaves = n + 1 + 1
      rw [RTree.numLeaves_node, combTree_numLeaves n, RTree.numLeaves_leaf]
      omega

/-- The comb's deep leaf sits at depth `n + 1`: the maximum allowed by the leaf count. -/
theorem combTree_depth_deep : ∀ n : ℕ, RTree.depth (combTree n) (combDeepPos n) = n + 1
  | 0 => rfl
  | n + 1 => by
      change RTree.depth (combTree n) (combDeepPos n) + 1 = n + 1 + 1
      rw [combTree_depth_deep n]

/-! ## The deepest fresh diagram: `χ^q T^q` is attained -/

/-- **The upper end of the fresh depth range is attained.**  For every `q ≥ 1` the comb gives a
fresh diagram with `q` arms and mark depth exactly `q`, so its value is `χ^q · T^q`: the fresh side
can carry `T^q`, and composed with the marked base of depth `p+1` it reaches the printed
`T^(p+q+1)`.  The printed range `3 ≤ ℓ ≤ p+q+1` is therefore tight at its top. -/
theorem comb_subW_max (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (hχ : ∀ v, ∑' y, k v y = χ) (n : ℕ)
    (v w : V) :
    subW k (combTree n) (combDeepPos n) (n + 1) v w = χ ^ (n + 1) * iterPow k (n + 1) v w := by
  have h1 : 1 ≤ n + 1 := by omega
  have h2 : n + 1 ≤ RTree.depth (combTree n) (combDeepPos n) := by
    rw [combTree_depth_deep]
  have h3 : (combTree n).numLeaves = n + 1 := combTree_numLeaves n
  rw [subW_eq k χ hχ (combTree n) (combDeepPos n) (n + 1) v w h1 h2, h3]
  rw [show 2 * (n + 1) - (n + 1) = n + 1 from by omega]

/-! ## The `q = 2` family: the two accepted `smwx5p94b/m1` monomials -/

/-- Its left leaf sits at depth two. -/
theorem twoLeaf_depth_fst : RTree.depth twoLeaf (Sum.inl ⟨⟩) = 2 := rfl

/-- **`q = 2`, `ℓ = 2`**: the subdivision of the edge above the arm `g 0`, worth `χ^2 T^2`
(accepted `q = 2` cover: shape A). -/
theorem subW_two_leaf_depth_two (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (v w : V) :
    subW k twoLeaf (Sum.inl ⟨⟩) 2 v w = χ ^ 2 * iterPow k 2 v w := by
  have h1 : 1 ≤ 2 := by omega
  have h2 : 2 ≤ RTree.depth twoLeaf (Sum.inl ⟨⟩) := by rw [twoLeaf_depth_fst]
  rw [subW_eq k χ hχ twoLeaf (Sum.inl ⟨⟩) 2 v w h1 h2]
  have hnum : 2 * twoLeaf.numLeaves - 2 = 2 := by decide
  rw [hnum]

/-- **`q = 2`, `ℓ = 1`**: the subdivision of the edge above the whole tree, worth `χ^3 T`
(accepted `q = 2` cover: shape B). -/
theorem subW_two_leaf_depth_one (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (v w : V) :
    subW k twoLeaf (Sum.inl ⟨⟩) 1 v w = χ ^ 3 * iterPow k 1 v w := by
  have h1 : 1 ≤ 1 := le_refl 1
  have h2 : 1 ≤ RTree.depth twoLeaf (Sum.inl ⟨⟩) := by rw [twoLeaf_depth_fst]; omega
  rw [subW_eq k χ hχ twoLeaf (Sum.inl ⟨⟩) 1 v w h1 h2]
  have hnum : 2 * twoLeaf.numLeaves - 1 = 3 := by decide
  rw [hnum]

/-- **The `ℓ = 2` diagram unfolded**: it is literally the four-edge shape
`{y↔u} ∘ {u↔w} ∘ {w↔g 0} ∘ {u↔g 1}` of the accepted `q = 2` cover — spine `y → u → w`, arm
`g 0` below the mark, arm `g 1` below `u`. -/
theorem subW_two_leaf_shapeA (k : V → V → ℝ≥0∞) (v w : V) :
    subW k twoLeaf (Sum.inl ⟨⟩) 2 v w
      = ∑' u, k v u * (k u w * treeTot k (RTree.leaf true) w) * treeTot k (RTree.leaf false) u :=
  rfl

/-- **The `ℓ = 1` diagram unfolded**: spine `y → w → u` with both arms below `u` — shape B of the
accepted `q = 2` cover. -/
theorem subW_two_leaf_shapeB (k : V → V → ℝ≥0∞) (v w : V) :
    subW k twoLeaf (Sum.inl ⟨⟩) 1 v w = k v w * treeTot k twoLeaf w :=
  rfl

/-! ## The `q = 3` family: `χ^5 T`, `χ^4 T^2`, `χ^3 T^3` -/

/-- Its deep leaf sits at depth three. -/
theorem threeLeaf_depth_deep : RTree.depth threeLeaf (Sum.inr (Sum.inl ⟨⟩)) = 3 := rfl

/-- **`q = 3`, `ℓ = 3`**: `χ^3 T^3` — the deepest fresh diagram on this shape, six edges. -/
theorem subW_three_leaf_depth_three (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (v w : V) :
    subW k threeLeaf (Sum.inr (Sum.inl ⟨⟩)) 3 v w = χ ^ 3 * iterPow k 3 v w := by
  have h1 : 1 ≤ 3 := by omega
  have h2 : 3 ≤ RTree.depth threeLeaf (Sum.inr (Sum.inl ⟨⟩)) := by rw [threeLeaf_depth_deep]
  rw [subW_eq k χ hχ threeLeaf (Sum.inr (Sum.inl ⟨⟩)) 3 v w h1 h2]
  have hnum : 2 * threeLeaf.numLeaves - 3 = 3 := by decide
  rw [hnum]

/-- **`q = 3`, `ℓ = 2`**: `χ^4 T^2`. -/
theorem subW_three_leaf_depth_two (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (v w : V) :
    subW k threeLeaf (Sum.inr (Sum.inl ⟨⟩)) 2 v w = χ ^ 4 * iterPow k 2 v w := by
  have h1 : 1 ≤ 2 := by omega
  have h2 : 2 ≤ RTree.depth threeLeaf (Sum.inr (Sum.inl ⟨⟩)) := by
    rw [threeLeaf_depth_deep]
    omega
  rw [subW_eq k χ hχ threeLeaf (Sum.inr (Sum.inl ⟨⟩)) 2 v w h1 h2]
  have hnum : 2 * threeLeaf.numLeaves - 2 = 4 := by decide
  rw [hnum]

/-- **`q = 3`, `ℓ = 1`**: `χ^5 T`. -/
theorem subW_three_leaf_depth_one (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (v w : V) :
    subW k threeLeaf (Sum.inr (Sum.inl ⟨⟩)) 1 v w = χ ^ 5 * iterPow k 1 v w := by
  have h1 : 1 ≤ 1 := le_refl 1
  have h2 : 1 ≤ RTree.depth threeLeaf (Sum.inr (Sum.inl ⟨⟩)) := by
    rw [threeLeaf_depth_deep]; omega
  rw [subW_eq k χ hχ threeLeaf (Sum.inr (Sum.inl ⟨⟩)) 1 v w h1 h2]
  have hnum : 2 * threeLeaf.numLeaves - 1 = 5 := by decide
  rw [hnum]

end PercLib.CriticalLRP.I417Fresh.Subdivision
