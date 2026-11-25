/- Integrated from independently rebuilt Ultramath work.
Production base 38371c8354fd1b28220794b007003710ea155dea.
Scratch source: ../../.ultramath/smwvlmbqa/m6/Defs.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Basic
public import PercLib.CriticalLRP.TreeExpansion.Weight
public import PercLib.CriticalLRP.TreeExpansion.PathWeightedTreeSum

/-!
# Marked-leaf diagram layers of Lemma I.4.17 for arbitrary `p`

Source: Tom Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied PDF p. 45), and Lemma I.4.16
(p. 44):

> "Expanding each of these probabilities out as in the proof of the tree-graph inequality
> yields the claim: We obtain a bound in terms of tree diagrams with two pinned vertices at
> `x` and `y`, with `2p+2q+1` edges in total, some number `3 ≤ ℓ ≤ p+q+1` of which belong to
> the path connecting `x` and `y`. [...] In each case, `C_{p,q,ℓ}` counts the number of
> diagrams in the bound in which the path connecting `x` and `y` has length `ℓ`."

The whole content of that last sentence — that a diagram *only* contributes
`T^ℓ(x,y) (E|K|)^{2p+2q+1-ℓ}`, i.e. that the value of a diagram depends on the marked path
**only through its length** — is what this file and `Marked.lean` make precise and prove at
arbitrary `p`.  The base side of Lemma I.4.17 is `jointPow π x p w = E[|K_x|^p 1(w ∈ K_x)]`;
expanding it produces rooted binary trees on `p+1` labelled leaves (the `p` arms of `x` and
the single mark `w`), and each of them has exactly one leaf whose value is *pinned* at `w`.
The paper's claim is then that such a marked diagram with marked leaf at depth `ℓ` is worth

  `χ^(2p+1-ℓ) · T^ℓ(x,w)`,   `χ = E|K|`,

independently of the shape of the tree.  `Marked.lean` proves exactly this
(`tsum_wtE_marked`), and consequently that the whole marked family collapses to the finite
polygon/two-point matrix sum `∑_ℓ C_{p,ℓ} χ^(2p+1-ℓ) T^ℓ(x,w)` with integer `C_{p,ℓ}`.

## What is in this file

* `wtE k t y v` — the tree-graph weight of a rooted binary tree `t` with root pinned at `v`,
  leaf values `y : t.LeafPos → V`, and the value at every **internal** vertex summed over.
  This is the `ℝ≥0∞`/countable analogue of `RTree.wt` (`TreeExpansion/Weight.lean`), which
  is stated for `[Fintype V]` and `ℝ`: the canonical model `I417A` lives on a countable
  vertex set and its two-point function is an `ℝ≥0∞`-valued kernel whose mass may be `⊤`.
* `pathW k t q v w` — the weight of the root-to-leaf path ending at the leaf position `q`,
  with that leaf's value pinned at `w` and the intermediate vertices summed over: the
  `RTree.depth t q`-fold composition of `k` from `v` to `w`.
* `iterPow k n v w` — the `n`-fold power of a kernel `k` (`iterPow k 0` is the diagonal
  indicator, `iterPow k (n+1) v w = ∑_u k v u * iterPow k n u w`).

## Source discrepancies

None in this file: it is the diagram (combinatorial-analytic) layer only, and it uses no
probability.  The only hypothesis needed is that the kernel has a **constant** row sum `χ`,
which is the abstract form of transitivity `E|K_v| = E|K|` used throughout the source
(`meanVol π v = meanVol π x`).
-/

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Base

open PercLib.CriticalLRP.TreeExpansion

universe u

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The infinite-degree tree-graph weight -/

/-- `wtE k t y v`: the sum over all assignments of values in `V` to the **internal** vertices
of `t` of the product of `k` over the edges of `t`, where the root is assigned `v` (so the
edge from the parent of the root contributes `k (parent) v`) and the leaf position `p` is
assigned `y p`.

This is `RTree.wt` transported to `ℝ≥0∞` and to a countable vertex set, so that it can be
applied to `edgeMeasure π` on the countable canonical model. -/
noncomputable def wtE {α : Type u} (k : V → V → ℝ≥0∞) :
    (t : RTree α) → (t.LeafPos → V) → V → ℝ≥0∞
  | .leaf _, y, v => k v (y ⟨⟩)
  | .node l r, y, v =>
      ∑' u, k v u * wtE k l (fun p => y (Sum.inl p)) u * wtE k r (fun p => y (Sum.inr p)) u

/-! ## The marked path -/

/-- `pathW k t q v w`: the `RTree.depth t q`-fold composition of `k` along the tree path from
the root to the leaf position `q`, with the value at `q` pinned to `w` and the values at the
intermediate vertices of the path summed over.

For a leaf this is `k v w`; at a node it routes through the child that contains `q`.  The
point of this definition is that it does *not* depend on the shape of `t` at all, only on
the length `RTree.depth t q` of the path. -/
noncomputable def pathW {α : Type u} (k : V → V → ℝ≥0∞) :
    (t : RTree α) → (q : t.LeafPos) → V → V → ℝ≥0∞
  | .leaf _, _, v, w => k v w
  | .node l _r, Sum.inl q, v, w => ∑' u, k v u * pathW k l q u w
  | .node _l r, Sum.inr q, v, w => ∑' u, k v u * pathW k r q u w

/-! ## Powers of a kernel -/

/-- One step of the kernel composition: `step k F v w = ∑_u k v u * F u w`. -/
noncomputable def step (k : V → V → ℝ≥0∞) (F : V → V → ℝ≥0∞) : V → V → ℝ≥0∞ :=
  fun v w => ∑' u, k v u * F u w

/-- `iterPow k n`: the `n`-fold power of the kernel `k`, with `iterPow k 0` the diagonal
indicator `1[v = w]` and `iterPow k (n+1) v w = ∑_u k v u * iterPow k n u w`.  For
`k = τ` the two-point function of the canonical model this is the `n`-th matrix power
`T^n(x,w)` of Lemma I.4.17. -/
noncomputable def iterPow (k : V → V → ℝ≥0∞) : ℕ → (V → V → ℝ≥0∞)
  | 0 => fun v w => if v = w then 1 else 0
  | n + 1 => step k (iterPow k n)

end PercLib.CriticalLRP.I417Base
