/-
Independently rebuilt and integrated from the accepted `smwx6p0op/m2` artifact
`.ultramath/smwx6p0op/m2/GQDepth`. Production integration revision:
`c83993396c566d21a0abe4051ed84dd6dab6093e`. The coordinator uses the production
namespace and fully qualified imports; this package is diagram infrastructure,
not an event-cover theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Value
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.PerDepth.Main

/-!
Independently built for swarm `smwx6p0op`, member `m2`, direction DEPTH-RANGE-I417.

# The path-depth range of Lemma I.4.17, at arbitrary `p, q`

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (supplied PDF pp. 45--46):

> "We obtain a bound in terms of tree diagrams with two pinned vertices at `x` and `y`, with
> `2p+2q+1` edges in total, some number `3 ≤ ℓ ≤ p+q+1` of them belong to the path connecting `x`
> and `y`."

Production records that range as a **hypothesis** (`I417Base.marked_diagram_by_depth` takes
`a ≤ depth ≤ b` on the family).  This file derives the two ends from the two sides of the
expansion, at arbitrary `p` and `q`:

* **lower end `ℓ ≥ 3`.**  The marked (base) side has `2p+1` edges and its depth-`1` coefficient
  vanishes: `I417MarkedPerDepth.nonplaneMarkedCount_eq_zero_of_lt` kills depths `< 1` and
  `nonplaneMarkedCount_one_eq_zero` (production) kills depth `1` for `p ≥ 1`, while
  `nonplaneMarkedCount_eq_zero_of_gt` kills depths `> p+1`.  Hence a base diagram with a *nonzero*
  coefficient has marked depth in `[2, p+1]`.  The fresh side has fresh depth `ℓ₂ ≥ 1`
  (`RTree.depth_pos`).  So the composed `x`--`y` path has `ℓ = ℓ₁ + ℓ₂ ≥ 3`.
* **upper end `ℓ ≤ p+q+1`.**  `ℓ₁ ≤ p+1` (same production bound) and `ℓ₂ ≤ q`
  (`subW_depth_le`, from `RTree.depth_le_numLeaves` on the `q`-leaf fresh tree).
* **edge count.**  `(2p+1) + 2q = 2p+2q+1`, and the non-path edges count
  `(2p+1-ℓ₁) + (2q-ℓ₂) = 2p+2q+1-ℓ` — the printed monomial `T^ℓ χ^(2p+2q+1-ℓ)` exactly.

Nothing here is an event-level statement: the *cover* of the fresh event by this diagram family is
a separate question (member `m1`'s direction).  This file is the depth/exponent bookkeeping that
any such cover must land in, and it is where the printed numbers `2q` and `3 ≤ ℓ ≤ p+q+1` come
from.
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

/-! ## The fresh-side depth range `1 ≤ ℓ ≤ q` -/

/-- **The mark depth of the fresh diagram is at most the number of arms.**  A `q`-leaf binary tree
has all its leaves at RTree-depth at most `q`, and `ℓ` is such a depth. -/
theorem subW_depth_le_numLeaves {α : Type u} (t : RTree α) (q : t.LeafPos) :
    RTree.depth t q ≤ t.numLeaves :=
  RTree.depth_le_numLeaves t q

/-- **Fresh-side monomial range.**  For `q` arms and mark depth `ℓ ∈ [1, q]` the source monomial
`χ^(2q-ℓ)·T^ℓ` has `2q` edges, `T`-power in `[1,q]` and `χ`-exponent in `[q, 2q-1]`:
the fresh side never produces more than the printed `2q` edges. -/
theorem subMono_range (q ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ q) :
    q ≤ 2 * q - ℓ ∧ 2 * q - ℓ ≤ 2 * q - 1 ∧ 1 ≤ ℓ ∧ ℓ ≤ q ∧ (2 * q - ℓ) + ℓ = 2 * q := by
  refine ⟨by omega, by omega, h1, h2, by omega⟩

/-- **The green and the black edges of one fresh diagram.**  Every subdivided-edge diagram with
`q` arms and mark depth `ℓ ∈ [1, RTree.depth t q]` evaluates to `χ^e · T^ℓ` with
`1 ≤ ℓ ≤ q`, `q ≤ e ≤ 2q-1` and `e + ℓ = 2q`; in particular the total number of fresh edges is
exactly `2q`, not `2q+1`. -/
theorem subW_level_range {α : Type u} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (t : RTree α) (q : t.LeafPos) (ℓ : ℕ)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ RTree.depth t q) (v w : V) :
    subW k t q ℓ v w = χ ^ (2 * t.numLeaves - ℓ) * iterPow k ℓ v w ∧
      1 ≤ ℓ ∧ ℓ ≤ t.numLeaves ∧
        t.numLeaves ≤ 2 * t.numLeaves - ℓ ∧ 2 * t.numLeaves - ℓ ≤ 2 * t.numLeaves - 1 ∧
          (2 * t.numLeaves - ℓ) + ℓ = 2 * t.numLeaves := by
  have hq : ℓ ≤ t.numLeaves := le_trans h2 (subW_depth_le_numLeaves t q)
  refine ⟨subW_eq k χ hχ t q ℓ v w h1 h2, h1, hq, ?_, ?_, ?_⟩ <;>
    omega

/-! ## The marked-side range `2 ≤ ℓ ≤ p+1` -/

/-- **Only depths `2, …, p+1` carry a nonzero marked coefficient.**  This is production's
`I417MarkedPerDepth` vanishing: nothing below depth `1`, nothing at depth `1` when `p ≥ 1`, nothing
above `p+1`.  It is the reason the source's printed lower end of the `x`--`y` path is `3`. -/
theorem base_marked_depth_range (p ℓ : ℕ) (hp : 1 ≤ p)
    (hne : PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount p ℓ ≠ 0) :
    2 ≤ ℓ ∧ ℓ ≤ p + 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hcon
    rcases Nat.lt_or_ge ℓ 2 with h | h
    · rcases Nat.lt_or_ge ℓ 1 with h0 | h0
      · exact hne (PercLib.CriticalLRP.I417MarkedPerDepth.nonplaneMarkedCount_eq_zero_of_lt p ℓ h0)
      · have h1 : ℓ = 1 := by omega
        subst h1
        exact hne (PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount_one_eq_zero hp)
    · omega
  · by_contra hcon
    exact hne (PercLib.CriticalLRP.I417MarkedPerDepth.nonplaneMarkedCount_eq_zero_of_gt p ℓ
      (by omega))

/-! ## The composed source range `3 ≤ ℓ ≤ p+q+1` -/

/-- **The printed path-depth range of Lemma I.4.17.**  A base diagram with marked depth `ℓ₁ ≥ 2`
(which is what a nonzero coefficient forces) composed with a fresh diagram of mark depth
`ℓ₂ ∈ [1,q]` produces an `x`--`y` path of length `ℓ = ℓ₁ + ℓ₂`, and that length lies in the printed
range `3 ≤ ℓ ≤ p+q+1` — with `ℓ = p+q+1` attained exactly when `ℓ₁ = p+1` and `ℓ₂ = q`. -/
theorem source_path_range (p q ℓ₁ ℓ₂ : ℕ) (h1a : 2 ≤ ℓ₁) (h1b : ℓ₁ ≤ p + 1)
    (h2a : 1 ≤ ℓ₂) (h2b : ℓ₂ ≤ q) :
    3 ≤ ℓ₁ + ℓ₂ ∧ ℓ₁ + ℓ₂ ≤ p + q + 1 ∧
      (2 * p + 1 - ℓ₁) + (2 * q - ℓ₂) = 2 * p + 2 * q + 1 - (ℓ₁ + ℓ₂) := by
  refine ⟨by omega, by omega, by omega⟩

/-- **The printed edge count.**  `(2p+1) + 2q = 2p+2q+1` edges, of which `ℓ` are on the `x`--`y`
path; the `χ`-exponent and the `T`-power add up to that total.  This is the monomial identity
`χ^(2p+1-ℓ₁) T^ℓ₁ · χ^(2q-ℓ₂) T^ℓ₂ = χ^(2p+2q+1-ℓ) T^(ℓ₁+ℓ₂) · (1)` at the level of exponents,
together with the statement that the total is `2p+2q+1` for every admissible `ℓ₁, ℓ₂`. -/
theorem source_edge_count (p q ℓ₁ ℓ₂ : ℕ) (h1b : ℓ₁ ≤ p + 1) (h2b : ℓ₂ ≤ q)
    (h1a : 2 ≤ ℓ₁) (h2a : 1 ≤ ℓ₂) :
    2 * p + 1 + 2 * q = 2 * p + 2 * q + 1 ∧
      (2 * p + 1 - ℓ₁) + (2 * q - ℓ₂) = 2 * p + 2 * q + 1 - (ℓ₁ + ℓ₂) ∧
        2 * p + 1 - ℓ₁ + ℓ₁ = 2 * p + 1 ∧ 2 * q - ℓ₂ + ℓ₂ = 2 * q := by
  refine ⟨by ring, by omega, by omega, by omega⟩

end PercLib.CriticalLRP.I417Fresh.Subdivision
