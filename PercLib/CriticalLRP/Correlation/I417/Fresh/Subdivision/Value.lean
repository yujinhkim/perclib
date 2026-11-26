/-
Independently rebuilt and integrated from the accepted `smwx6p0op/m2` artifact
`.ultramath/smwx6p0op/m2/GQDepth`. Production integration revision:
`c83993396c566d21a0abe4051ed84dd6dab6093e`. The coordinator uses the production
namespace and fully qualified imports; this package is diagram infrastructure,
not an event-cover theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Defs
public import PercLib.CriticalLRP.Correlation.I417.Base.Marked

/-!
Independently built for swarm `smwx6p0op`, member `m2`, direction DEPTH-RANGE-I417.

# A subdivided-edge diagram is worth `χ^(2q-ℓ) T^ℓ`, whatever its shape

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied PDF p. 45), the sentence

> "In each case, `C_{p,q,ℓ}` counts the number of diagrams in the bound in which the path
> connecting `x` and `y` has length `ℓ`."

The main result here is the **fresh-side** analogue of production's `I417Base.tsum_wtE_marked`:

  `subW_eq : subW k t q ℓ v w = χ ^ (2 * t.numLeaves - ℓ) * iterPow k ℓ v w`

for `1 ≤ ℓ ≤ RTree.depth t q`.  The diagram has `2 * t.numLeaves` edges — the printed `2q` fresh
edges — of which the `ℓ` on the `v`--`w` path contribute `T` and the remaining `2q - ℓ` contribute
the constant row sum `χ`.  **The value does not depend on the shape of `t`, only on `q` and `ℓ`**,
which is exactly what makes the fresh family collapse to the coefficient-weighted polynomial
`freshPoly`.

Two features that the printed count needs and that the single-hub/extra-leaf reading loses:

* `w` is *not* a leaf.  Reading `w` as an extra leaf (the hub-star `{y↔w} ∩ ⋂_j {w↔g j}`) gives a
  tree with `2q+1` edges and the value `χ^(2q+1-ℓ)T^ℓ` — one `χ` too many.  The subdivision keeps
  `2q`: the edge above the arm `q` is replaced by two edges, one of which is the last path edge;
* the two degeneracies `ℓ = 1` (`w` directly below `y`) and `ℓ = RTree.depth t q` (`w` on the edge
  above the arm, so `w` may coincide with the arm value) are both *inside* the family, because the
  arm values are summed.  No case split on coincident positions is needed.

The only hypothesis is a **constant row sum** of the kernel (`∀ v, ∑' y, k v y = χ`), the abstract
form of transitivity `E|K_v| = E|K|`.  No probability, no BK, no moment or transitivity input, no
finiteness of `χ`, and no assumption on the shape/index type `α`.
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

/-! ## The fully summed tree weight is `χ^(2n-1)` -/

/-- `treeTot` is production's `tsum_wtE`: an `n`-leaf tree below a pinned vertex is worth
`χ^(2n-1)`, independently of its shape. -/
theorem treeTot_eq {α : Type u} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (t : RTree α) (v : V) :
    treeTot k t v = χ ^ (2 * t.numLeaves - 1) :=
  PercLib.CriticalLRP.I417Base.tsum_wtE k χ hχ t v

/-! ## The one-step power of a kernel -/

/-- `iterPow k 1 = k`. -/
theorem iterPow_one (k : V → V → ℝ≥0∞) (v w : V) : iterPow k 1 v w = k v w := by
  rw [show iterPow k 1 v w = ∑' u, k v u * (if u = w then (1 : ℝ≥0∞) else 0) from rfl]
  rw [tsum_eq_single w]
  · simp
  · intro b hb
    simp [hb]

/-- The defining recursion of `iterPow` at a successor. -/
theorem iterPow_succ (k : V → V → ℝ≥0∞) (n : ℕ) (v w : V) :
    iterPow k (n + 1) v w = ∑' u, k v u * iterPow k n u w := rfl

/-- The two-fold power, in the form the `q = 2` shapes use. -/
theorem iterPow_two (k : V → V → ℝ≥0∞) (v w : V) :
    iterPow k 2 v w = ∑' u, k v u * k u w := by
  rw [iterPow_succ]
  exact tsum_congr fun u => by rw [iterPow_one]

/-! ## The value of a subdivided-edge diagram -/

/-- **The fresh diagram value depends only on the arm count and the mark depth.**  For a kernel `k`
with constant row sum `χ`, a rooted binary tree `t` with `q = t.numLeaves` arm leaves, whose
edge above the leaf position `q` is subdivided and the subdivision point pinned at `w`, is worth

  `χ ^ (2 * q - ℓ) * T ^ ℓ (v,w)`

with `ℓ = RTree.depth t q` the path length from `v` to `w`, i.e. `2q` edges in total, `2q - ℓ` of
them carrying `χ` and `ℓ` of them carrying `T`.  Independent of the shape of `t`. -/
theorem subW_eq {α : Type u} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (t : RTree α) :
    ∀ (q : t.LeafPos) (ℓ : ℕ) (v w : V), 1 ≤ ℓ → ℓ ≤ RTree.depth t q →
      subW k t q ℓ v w = χ ^ (2 * t.numLeaves - ℓ) * iterPow k ℓ v w := by
  induction t with
  | leaf a =>
      intro q ℓ v w h1 h2
      have hℓ : ℓ = 1 := by
        have hd : RTree.depth (RTree.leaf a) q = 1 := rfl
        omega
      subst hℓ
      rw [show subW k (RTree.leaf a) q 1 v w
            = k v w * treeTot k (RTree.leaf a) w from rfl]
      rw [treeTot_eq k χ hχ (RTree.leaf a) w, iterPow_one]
      rw [show 2 * (RTree.leaf a).numLeaves - 1 = 1 from rfl]
      rw [pow_one, mul_comm]
  | node l r ihl ihr =>
      intro q ℓ v w h1 h2
      rcases q with q' | q'
      · -- the marked leaf is in the left child
        rcases ℓ with _ | _ | n
        · omega
        · -- `ℓ = 1`: the subdivided edge is the one above the whole tree
          rw [show subW k (RTree.node l r) (Sum.inl q') 1 v w
                = k v w * treeTot k (RTree.node l r) w from rfl]
          rw [treeTot_eq k χ hχ (RTree.node l r) w, iterPow_one, mul_comm]
        · -- `ℓ = n + 2`: the subdivided edge is inside the left child
          have hdep : RTree.depth (RTree.node l r) (Sum.inl q') = RTree.depth l q' + 1 := rfl
          have h2' : n + 1 ≤ RTree.depth l q' := by rw [hdep] at h2; omega
          have h1' : 1 ≤ n + 1 := by omega
          rw [show subW k (RTree.node l r) (Sum.inl q') (n + 2) v w
                = ∑' u, k v u * subW k l q' (n + 1) u w * treeTot k r u from rfl]
          rw [show (∑' u, k v u * subW k l q' (n + 1) u w * treeTot k r u)
                = ∑' u, k v u *
                    (χ ^ (2 * l.numLeaves - (n + 1)) * iterPow k (n + 1) u w) *
                    χ ^ (2 * r.numLeaves - 1) from
            tsum_congr fun u => by
              rw [ihl q' (n + 1) u w h1' h2', treeTot_eq k χ hχ r u]]
          rw [show (∑' u, k v u *
                (χ ^ (2 * l.numLeaves - (n + 1)) * iterPow k (n + 1) u w) *
                χ ^ (2 * r.numLeaves - 1))
              = (χ ^ (2 * l.numLeaves - (n + 1)) * χ ^ (2 * r.numLeaves - 1)) *
                  ∑' u, k v u * iterPow k (n + 1) u w from by
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun u => by ring]
          have hexp : 2 * l.numLeaves - (n + 1) + (2 * r.numLeaves - 1)
              = 2 * (RTree.node l r).numLeaves - (n + 2) := by
            have h1l : 1 ≤ l.numLeaves := RTree.numLeaves_pos l
            have h1r : 1 ≤ r.numLeaves := RTree.numLeaves_pos r
            have hdl : RTree.depth l q' ≤ l.numLeaves := RTree.depth_le_numLeaves l q'
            rw [RTree.numLeaves_node]
            omega
          rw [← pow_add, hexp, show iterPow k (n + 2) v w
                = ∑' u, k v u * iterPow k (n + 1) u w from rfl]
      · -- the marked leaf is in the right child
        rcases ℓ with _ | _ | n
        · omega
        · rw [show subW k (RTree.node l r) (Sum.inr q') 1 v w
                = k v w * treeTot k (RTree.node l r) w from rfl]
          rw [treeTot_eq k χ hχ (RTree.node l r) w, iterPow_one, mul_comm]
        · have hdep : RTree.depth (RTree.node l r) (Sum.inr q') = RTree.depth r q' + 1 := rfl
          have h2' : n + 1 ≤ RTree.depth r q' := by rw [hdep] at h2; omega
          have h1' : 1 ≤ n + 1 := by omega
          rw [show subW k (RTree.node l r) (Sum.inr q') (n + 2) v w
                = ∑' u, k v u * treeTot k l u * subW k r q' (n + 1) u w from rfl]
          rw [show (∑' u, k v u * treeTot k l u * subW k r q' (n + 1) u w)
                = ∑' u, k v u * χ ^ (2 * l.numLeaves - 1) *
                    (χ ^ (2 * r.numLeaves - (n + 1)) * iterPow k (n + 1) u w) from
            tsum_congr fun u => by
              rw [ihr q' (n + 1) u w h1' h2', treeTot_eq k χ hχ l u]]
          rw [show (∑' u, k v u * χ ^ (2 * l.numLeaves - 1) *
                (χ ^ (2 * r.numLeaves - (n + 1)) * iterPow k (n + 1) u w))
              = (χ ^ (2 * l.numLeaves - 1) * χ ^ (2 * r.numLeaves - (n + 1))) *
                  ∑' u, k v u * iterPow k (n + 1) u w from by
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun u => by ring]
          have hexp : 2 * l.numLeaves - 1 + (2 * r.numLeaves - (n + 1))
              = 2 * (RTree.node l r).numLeaves - (n + 2) := by
            have h1l : 1 ≤ l.numLeaves := RTree.numLeaves_pos l
            have h1r : 1 ≤ r.numLeaves := RTree.numLeaves_pos r
            have hdr : RTree.depth r q' ≤ r.numLeaves := RTree.depth_le_numLeaves r q'
            rw [RTree.numLeaves_node]
            omega
          rw [← pow_add, hexp, show iterPow k (n + 2) v w
                = ∑' u, k v u * iterPow k (n + 1) u w from rfl]

/-- The fresh diagram value written with the source monomial `subMono`. -/
theorem subW_eq_subMono {α : Type u} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (t : RTree α) (q : t.LeafPos) (ℓ : ℕ) (v w : V)
    (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ RTree.depth t q) :
    subW k t q ℓ v w = subMono k χ t.numLeaves ℓ v w :=
  subW_eq k χ hχ t q ℓ v w h1 h2

end PercLib.CriticalLRP.I417Fresh.Subdivision
