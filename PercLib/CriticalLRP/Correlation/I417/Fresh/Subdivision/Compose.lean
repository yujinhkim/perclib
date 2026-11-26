/-
Independently rebuilt and integrated from the accepted `smwx6p0op/m2` artifact
`.ultramath/smwx6p0op/m2/GQDepth`. Production integration revision:
`c83993396c566d21a0abe4051ed84dd6dab6093e`. The coordinator uses the production
namespace and fully qualified imports; this package is diagram infrastructure,
not an event-cover theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Range
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly.Main

/-!
Independently built for swarm `smwx6p0op`, member `m2`, direction DEPTH-RANGE-I417.

# Composing a marked base diagram with a subdivided fresh diagram

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied PDF pp. 45--46).  The proof multiplies a
**marked** (base) diagram — pinned at `x`, with the mark `w` one of its leaves and `ℓ₁` its depth —
by a **fresh** diagram — pinned at `y`, with the mark `w` *subdividing* an edge and `ℓ₂` the depth
of the arm — and sums over `w`.

On one diagram the composition is three ordinary identities:

* base: `I417Base.tsum_wtE_marked` + `I417Base.pathW_eq_iterPow` give `χ^(2p+1-ℓ₁)·T^ℓ₁(x,w)`;
* fresh: `subW_eq` gives `χ^(2q-ℓ₂)·T^ℓ₂(w,y)`;
* the polygon step: `∑_w T^ℓ₁(x,w) T^ℓ₂(w,y) = T^(ℓ₁+ℓ₂)(x,y)`
  (production's `I417FreshTwo.iterPow_add_right`), so the *single* summand at the actual `w` obeys
  `T^ℓ₁(x,w) T^ℓ₂(w,y) ≤ T^(ℓ₁+ℓ₂)(x,y)`.

The result `marked_fresh_le` is the composed diagram bound with the printed normalisation: the
right-hand side is `χ^(2p+2q+1-ℓ)·T^ℓ(x,y)` with `ℓ = ℓ₁+ℓ₂ ∈ [3, p+q+1]`, i.e. the source's
`T^ℓ χ^(2p+2q+1-ℓ)` term with `C_{p,q,ℓ}`-style coefficients still to be counted by the consumer.
It is a *bound*, not an evaluation of the summed family: on a summed family the polygon step
`≤` is where the `C_{p,q,ℓ}` counting enters, and no converse is claimed.

Nothing here assumes probability, BK, moments or transitivity: the only hypothesis is the constant
row sum `χ` (the abstract form of transitivity of `E|K|`).
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

/-- **One subdivided step is bounded by the polygon power.**  The product of the two path weights
through an actual vertex `w` is at most the `(a+b)`-fold power, because the `(a+b)`-fold power is
the sum over *all* intermediate vertices. -/
theorem iterPow_mul_le (k : V → V → ℝ≥0∞) (a b : ℕ) (x w y : V) :
    iterPow k a x w * iterPow k b w y ≤ iterPow k (a + b) x y := by
  rw [← PercLib.CriticalLRP.I417FreshTwo.iterPow_add_right k a b x y]
  exact ENNReal.le_tsum (f := fun u => iterPow k a x u * iterPow k b u y) w

/-- **The composed marked-times-fresh diagram is bounded by the printed monomial.**

`t` is a marked base diagram with `p+1` leaves and marked leaf `qm` at depth `ℓ₁ ≥ 2`, its leaf
values summed and the mark pinned at `w` (`I417Base.tsum_wtE_marked`); `tb` is a fresh diagram with
`q` arm leaves, the edge above the arm `qb` subdivided, the subdivision point pinned at `w`
(`subW`), at depth `ℓ₂ ∈ [1, RTree.depth tb qb]`.  Their product — the value of the
composed diagram with two pinned vertices `x` and `w` and the summed arm leaves — is at most

  `χ ^ (2p + 2q + 1 - (ℓ₁ + ℓ₂)) · T ^ (ℓ₁ + ℓ₂) (x, y)`,

with `3 ≤ ℓ₁+ℓ₂ ≤ p+q+1` and exponent plus power `2p+2q+1`, exactly the printed form. -/
theorem marked_fresh_le {α β : Type u} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (p q : ℕ) (t : RTree α) (qm : t.LeafPos)
    (tb : RTree β) (qb : tb.LeafPos) (ℓ₂ : ℕ) (hbase : t.numLeaves = p + 1)
    (hfresh : tb.numLeaves = q) (h1a : 2 ≤ RTree.depth t qm) (h2a : 1 ≤ ℓ₂)
    (h2b : ℓ₂ ≤ RTree.depth tb qb) (x w y : V) :
    (∑' z : t.LeafPos → V, (if z qm = w then 1 else 0) * wtE k t z x) *
        subW k tb qb ℓ₂ w y
      ≤ χ ^ (2 * p + 2 * q + 1 - (RTree.depth t qm + ℓ₂)) *
          iterPow k (RTree.depth t qm + ℓ₂) x y := by
  have hb_le : RTree.depth t qm ≤ p + 1 := by
    have h := RTree.depth_le_numLeaves t qm
    omega
  have hf_le : ℓ₂ ≤ q := by
    have h := RTree.depth_le_numLeaves tb qb
    omega
  -- the marked base value
  have hbaseval : (∑' z : t.LeafPos → V, (if z qm = w then 1 else 0) * wtE k t z x)
      = χ ^ (2 * p + 1 - RTree.depth t qm) * iterPow k (RTree.depth t qm) x w := by
    rw [tsum_wtE_marked k χ hχ t qm x w, pathW_eq_iterPow k t qm x w, hbase]
    have hexp : 2 * (p + 1) - 1 - RTree.depth t qm = 2 * p + 1 - RTree.depth t qm := by omega
    rw [hexp]
  -- the fresh value
  have hfreshval : subW k tb qb ℓ₂ w y = χ ^ (2 * q - ℓ₂) * iterPow k ℓ₂ w y := by
    rw [subW_eq k χ hχ tb qb ℓ₂ w y h2a h2b, hfresh]
  rw [hbaseval, hfreshval]
  have hpath : iterPow k (RTree.depth t qm) x w * iterPow k ℓ₂ w y
      ≤ iterPow k (RTree.depth t qm + ℓ₂) x y :=
    iterPow_mul_le k (RTree.depth t qm) ℓ₂ x w y
  have hexp : (2 * p + 1 - RTree.depth t qm) + (2 * q - ℓ₂)
      = 2 * p + 2 * q + 1 - (RTree.depth t qm + ℓ₂) := by omega
  calc (χ ^ (2 * p + 1 - RTree.depth t qm) * iterPow k (RTree.depth t qm) x w) *
        (χ ^ (2 * q - ℓ₂) * iterPow k ℓ₂ w y)
      = (χ ^ (2 * p + 1 - RTree.depth t qm) * χ ^ (2 * q - ℓ₂)) *
          (iterPow k (RTree.depth t qm) x w * iterPow k ℓ₂ w y) := by ring
    _ = χ ^ ((2 * p + 1 - RTree.depth t qm) + (2 * q - ℓ₂)) *
          (iterPow k (RTree.depth t qm) x w * iterPow k ℓ₂ w y) := by rw [← pow_add]
    _ ≤ χ ^ (2 * p + 2 * q + 1 - (RTree.depth t qm + ℓ₂)) *
          iterPow k (RTree.depth t qm + ℓ₂) x y := by
        rw [hexp]
        gcongr

/-- **The composed depth lies in the printed range.**  Directly from `marked_fresh_le`'s side
conditions: the composed path length `ℓ₁ + ℓ₂` is at least `3` and at most `p + q + 1`, and the
`χ`-exponent plus the `T`-power is `2p + 2q + 1`. -/
theorem composed_depth_range {p q ℓ₁ ℓ₂ : ℕ} (h1a : 2 ≤ ℓ₁) (h1b : ℓ₁ ≤ p + 1)
    (h2a : 1 ≤ ℓ₂) (h2b : ℓ₂ ≤ q) :
    3 ≤ ℓ₁ + ℓ₂ ∧ ℓ₁ + ℓ₂ ≤ p + q + 1 ∧
      (2 * p + 2 * q + 1 - (ℓ₁ + ℓ₂)) + (ℓ₁ + ℓ₂) = 2 * p + 2 * q + 1 :=
  ⟨by omega, by omega, by omega⟩

end PercLib.CriticalLRP.I417Fresh.Subdivision
