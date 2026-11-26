/-
Independently rebuilt and integrated from the accepted `smwx6p0op/m2` artifact
`.ultramath/smwx6p0op/m2/GQDepth`. Production integration revision:
`c83993396c566d21a0abe4051ed84dd6dab6093e`. The coordinator uses the production
namespace and fully qualified imports; this package is diagram infrastructure,
not an event-cover theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Compose

/-!
Independently built for swarm `smwx6p0op`, member `m2`, direction DEPTH-RANGE-I417.

# The mark-summed composed diagram evaluates, it does not merely majorise

`marked_fresh_le` bounds one composed diagram at a *fixed* mark `w` by the polynomial
monomial; a per-position majorant of that kind is not yet the source's step, which **sums over the
mark** `w` and uses the polygon identity

  `∑_w T^ℓ₁(x,w) · T^ℓ₂(w,y) = T^(ℓ₁+ℓ₂)(x,y)`

(production's `I417FreshTwo.iterPow_add_right`).  This file performs that summation for the
subdivided-edge fresh family and records that the result is an **equality**:

  `tsum_marked_fresh_eq` — for a marked base diagram of `p+1` leaves with marked depth `ℓ₁` and
  a subdivided fresh diagram of `q` arms with mark depth `ℓ₂ ∈ [1, q]`,

    `∑_w (base_w · fresh_w) = χ^(2p+2q+1-ℓ) · T^ℓ(x,y)`,  `ℓ = ℓ₁ + ℓ₂ ∈ [3, p+q+1]`.

So for this diagram family no coefficient is lost at the `w`-summation: the `C_{p,q,ℓ}` of the
source count diagrams, not mark positions.  The distinction matters: a per-position majorant alone
cannot be summed over `w` (its right-hand side is `w`-independent, so the sum diverges); the
equality here is what makes the summation legitimate.

`tsum_marked_fresh_eq_two` specialises to `q = 2` and reproduces, exactly, the two monomials of the
accepted `q = 2` cover `smwx5p94b/m1` (`χ^(2p+3-ℓ) T^(ℓ+2)` at fresh depth `2` and
`χ^(2p+4-ℓ) T^(ℓ+1)` at fresh depth `1`), now *summed over the mark*.

No probability, BK, moment or transitivity input: only the constant row sum `χ`.
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

/-- The marked base diagram value, with its leaf count `p+1` and marked depth `ℓ₁`:
`χ^(2p+1-ℓ₁)·T^ℓ₁(x,w)`. -/
theorem marked_value_eq {α : Type u} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (p : ℕ) (t : RTree α) (qm : t.LeafPos)
    (hbase : t.numLeaves = p + 1) (x w : V) :
    (∑' z : t.LeafPos → V, (if z qm = w then 1 else 0) * wtE k t z x)
      = χ ^ (2 * p + 1 - RTree.depth t qm) * iterPow k (RTree.depth t qm) x w := by
  rw [tsum_wtE_marked k χ hχ t qm x w, pathW_eq_iterPow k t qm x w, hbase]
  have hexp : 2 * (p + 1) - 1 - RTree.depth t qm = 2 * p + 1 - RTree.depth t qm := by omega
  rw [hexp]

/-- **The mark-summed composed diagram is exactly the printed monomial.**  Summing the product of a
marked base diagram (depth `ℓ₁`, `p+1` leaves) and a subdivided-edge fresh diagram (depth
`ℓ₂ ∈ [1,q]`, `q` arms) over the mark `w` gives `χ^(2p+2q+1-ℓ)·T^ℓ(x,y)` with `ℓ = ℓ₁+ℓ₂`; no
coefficient is lost, and the exponents total `2p+2q+1`. -/
theorem tsum_marked_fresh_eq {α β : Type u} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (p q : ℕ) (t : RTree α) (qm : t.LeafPos)
    (tb : RTree β) (qb : tb.LeafPos) (ℓ₂ : ℕ) (hbase : t.numLeaves = p + 1)
    (hfresh : tb.numLeaves = q) (h2a : 1 ≤ ℓ₂) (h2b : ℓ₂ ≤ RTree.depth tb qb) (x y : V) :
    (∑' w : V, (∑' z : t.LeafPos → V, (if z qm = w then 1 else 0) * wtE k t z x) *
        subW k tb qb ℓ₂ w y)
      = χ ^ (2 * p + 2 * q + 1 - (RTree.depth t qm + ℓ₂)) *
          iterPow k (RTree.depth t qm + ℓ₂) x y := by
  have hf_le : ℓ₂ ≤ q := by
    have h := RTree.depth_le_numLeaves tb qb
    omega
  have hb_le : RTree.depth t qm ≤ p + 1 := by
    have h := RTree.depth_le_numLeaves t qm
    omega
  have hfreshval : ∀ w : V, subW k tb qb ℓ₂ w y = χ ^ (2 * q - ℓ₂) * iterPow k ℓ₂ w y :=
    fun w => by rw [subW_eq k χ hχ tb qb ℓ₂ w y h2a h2b, hfresh]
  -- rewrite every summand in the form that the polygon identity applies to
  have hstep : (∑' w : V, (∑' z : t.LeafPos → V, (if z qm = w then 1 else 0) * wtE k t z x) *
        subW k tb qb ℓ₂ w y)
      = ∑' w : V, (χ ^ (2 * p + 1 - RTree.depth t qm) * χ ^ (2 * q - ℓ₂)) *
          (iterPow k (RTree.depth t qm) x w * iterPow k ℓ₂ w y) := by
    refine tsum_congr fun w => ?_
    rw [marked_value_eq k χ hχ p t qm hbase x w, hfreshval w]
    ring
  rw [hstep, ENNReal.tsum_mul_left,
    PercLib.CriticalLRP.I417FreshTwo.iterPow_add_right k (RTree.depth t qm) ℓ₂ x y,
    ← pow_add]
  have hexp : 2 * p + 1 - RTree.depth t qm + (2 * q - ℓ₂)
      = 2 * p + 2 * q + 1 - (RTree.depth t qm + ℓ₂) := by omega
  rw [hexp]

/-- **The `q = 2` specialisation over the mark**: fresh depth `2` gives `χ^(2p+3-ℓ) T^(ℓ+2)` and
fresh depth `1` gives `χ^(2p+4-ℓ) T^(ℓ+1)`, `ℓ` the marked base depth — exactly the two monomials of
the accepted `q = 2` cover, now summed over `w` and with `ℓ ∈ [2,p+1]` the source range. -/
theorem tsum_marked_fresh_eq_two {α β : Type u} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (p : ℕ) (t : RTree α) (qm : t.LeafPos)
    (tb : RTree β) (qb : tb.LeafPos) (hbase : t.numLeaves = p + 1) (hfresh : tb.numLeaves = 2)
    (h2b : 2 ≤ RTree.depth tb qb) (x y : V) :
    (∑' w : V, (∑' z : t.LeafPos → V, (if z qm = w then 1 else 0) * wtE k t z x) *
          subW k tb qb 2 w y
        = χ ^ (2 * p + 3 - RTree.depth t qm) *
            iterPow k (RTree.depth t qm + 2) x y) ∧
      (∑' w : V, (∑' z : t.LeafPos → V, (if z qm = w then 1 else 0) * wtE k t z x) *
          subW k tb qb 1 w y
        = χ ^ (2 * p + 4 - RTree.depth t qm) *
            iterPow k (RTree.depth t qm + 1) x y) := by
  have h2a : 1 ≤ (2 : ℕ) := by omega
  have h1a : 1 ≤ (1 : ℕ) := le_refl 1
  have h1b : 1 ≤ RTree.depth tb qb := one_le_two.trans h2b
  constructor
  · have h := tsum_marked_fresh_eq k χ hχ p 2 t qm tb qb 2 hbase hfresh h2a h2b x y
    rw [show 2 * p + 2 * 2 + 1 - (RTree.depth t qm + 2)
          = 2 * p + 3 - RTree.depth t qm from by omega] at h
    exact h
  · have h := tsum_marked_fresh_eq k χ hχ p 2 t qm tb qb 1 hbase hfresh h1a h1b x y
    rw [show 2 * p + 2 * 2 + 1 - (RTree.depth t qm + 1)
          = 2 * p + 4 - RTree.depth t qm from by omega] at h
    exact h

end PercLib.CriticalLRP.I417Fresh.Subdivision
