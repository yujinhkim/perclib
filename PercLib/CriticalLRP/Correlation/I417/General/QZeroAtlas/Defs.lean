/-
Accepted from Ultramath `smwzg77c3`, member `m1`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d1`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `q = 0`, `p = 3` tree-diagram atlas of Lemma I.4.17

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof (pp. 45-46), together with the
tree-graph inequality (I.2.2) of Section I.2.1, p. 22.

At `q = 0` the moment gap of Lemma I.4.17 at `p = 3` is exactly the one-copy star moment
`E[|K_x|³ 1(x ↔ y)]` (`I417Gen.starMoment`), and the labelled expansion
(`I417Gen.starMoment_eq_tsum_labelEvent`) writes it as

  `∑_{x1 x2 x3} P(x1, x2, x3, y ∈ K_x)`,

i.e. as the probability that the **four** labels `x1, x2, x3, y` all lie in `K_x`.  Applying the
tree-graph inequality (I.2.2) to that four-label event produces a tree sum over the full binary
trees with four labelled leaves; the trees are the fifteen elements of the list
`atlasDiagrams` below (this file records them as explicit edge lists on eight nodes:
`0 = x` the root, `1,2,3` the three internal vertices, `4 = y`, `5,6,7 = x1,x2,x3`).

The fifteen trees group into four shapes, by the length `ℓ` of the tree path from the root to the
leaf `y`:

* `shapeTwo`  (`ℓ = 2`, three trees): the branch point adjacent to the root is adjacent to `y`;
* `shapeThreeA` (`ℓ = 3`, three trees, balanced); `shapeThreeB` (`ℓ = 3`, three trees, chain);
* `shapeFour` (`ℓ = 4`, six trees, chain with `y` in the deep cherry).

The total number of edges is `2p + 2q + 1 = 7` in every case, so a tree whose pinned path has
length `ℓ` carries `7 - ℓ` off-path edges.  The evaluation lemmas in `Main.lean` show that each
shape sums to exactly `χ ^ (7 - ℓ) * (ℓ-fold kernel power)(x, y)` under the kernel data below,
where `χ = ∑_z P(x ↔ z) = E|K|`.

**This differs from the printed ℓ-range `3 ≤ ℓ ≤ p + q + 1` of Lemma I.4.17**: at `q = 0` the
atlas carries an extra `ℓ = 2` shape with total weight `3 χ ^ 5 k ^ 2(x,y)`, which is *not*
implied by the `ℓ = 3, 4` terms at the level of the kernel hypotheses (`Main.lean`,
`no_uniform_ell_two_absorption`).  The `ℓ = 2` shape is exactly the class in which the `y`-arm of
the source's marked path (the edge `w ↔ y_j` of the printed proof, pp. 45-46) is *absent*: with
`q = 0` the target set `{y_1, …, y_q}` is empty, so the printed marked-path mechanism, which is
what forces `ℓ ≥ 3` for `q ≥ 1`, does not apply.  Recording the `ℓ = 2` shape is therefore a
source-level correction at `q = 0`, not a weakening of the target: `Main.lean` proves the honest
three-term bound and derives the printed two-term form from an explicit extra input.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main
public import PercLib.CriticalLRP.Analysis.KernelPower.Defs
public import Mathlib

/-! # The `q = 0` four-label tree-diagram atlas -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.QZeroAtlas

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Iterated kernel powers -/

/-- The `ℓ`-fold power of an `ℝ≥0∞`-valued kernel, in the *chain-nested* form
`kpow k (n+1) u v = ∑' z, k u z * kpow k n z v`, with `kpow k 0` the identity kernel.

For a symmetric kernel this is the `ℓ`-fold matrix power `T^ℓ` of Lemma I.4.17; the chain nesting is
chosen so that the tree-diagram sums of the atlas (which read off a chain of kernel factors from the
root to the target) match it definitionally. -/
def kpow (k : V → V → ℝ≥0∞) : ℕ → V → V → ℝ≥0∞
  | 0 => fun u v => if u = v then 1 else 0
  | (n + 1) => fun u v => ∑' z, k u z * kpow k n z v

@[simp] theorem kpow_zero (k : V → V → ℝ≥0∞) (u v : V) :
    kpow k 0 u v = if u = v then 1 else 0 := rfl

theorem kpow_succ (k : V → V → ℝ≥0∞) (n : ℕ) (u v : V) :
    kpow k (n + 1) u v = ∑' z, k u z * kpow k n z v := rfl

/-- The one-step power is the kernel itself. -/
theorem kpow_one (k : V → V → ℝ≥0∞) (u v : V) : kpow k 1 u v = k u v := by
  rw [kpow_succ]
  have : ∀ z : V, k u z * kpow k 0 z v = if z = v then k u v else 0 := by
    intro z
    rw [kpow_zero]
    by_cases h : z = v
    · subst h; simp
    · simp [h]
  calc ∑' z, k u z * kpow k 0 z v = ∑' z, (if z = v then k u v else 0) := tsum_congr this
    _ = k u v := tsum_ite_eq v (fun _ => k u v)

/-- The two-step power. -/
theorem kpow_two (k : V → V → ℝ≥0∞) (u v : V) :
    kpow k 2 u v = ∑' z, k u z * k z v := by
  rw [kpow_succ]
  exact tsum_congr fun z => by rw [kpow_one]

/-- The three-step power. -/
theorem kpow_three (k : V → V → ℝ≥0∞) (u v : V) :
    kpow k 3 u v = ∑' z, k u z * kpow k 2 z v := kpow_succ _ _ _ _

/-- The four-step power. -/
theorem kpow_four (k : V → V → ℝ≥0∞) (u v : V) :
    kpow k 4 u v = ∑' z, k u z * kpow k 3 z v := kpow_succ _ _ _ _

/-- The kernel commutes with its own `n`-th `kpow`: the two orderings of the `(n+1)`-fold sum
agree.  No symmetry hypothesis is needed. -/
theorem kpow_comm_k {k : V → V → ℝ≥0∞} (n : ℕ) (x y : V) :
    (∑' u, kpow k n x u * k u y) = ∑' u, k x u * kpow k n u y := by
  induction n generalizing x y with
  | zero =>
      have h1 : (∑' u, kpow k 0 x u * k u y) = k x y := by
        rw [tsum_eq_single x]
        · simp
        · intro b hb
          simp [kpow_zero, Ne.symm hb]
      have h2 : (∑' u, k x u * kpow k 0 u y) = k x y := by
        rw [tsum_eq_single y]
        · simp
        · intro b hb
          simp [kpow_zero, hb]
      rw [h1, h2]
  | succ n ih =>
      simp only [kpow_succ]
      calc (∑' u, (∑' z, k x z * kpow k n z u) * k u y)
          = ∑' u, ∑' z, (k x z * kpow k n z u) * k u y := by
            refine tsum_congr fun u => ?_
            exact ENNReal.tsum_mul_right.symm
        _ = ∑' z, ∑' u, (k x z * kpow k n z u) * k u y := ENNReal.tsum_comm
        _ = ∑' z, ∑' u, k x z * (kpow k n z u * k u y) := by
            refine tsum_congr fun z => tsum_congr fun u => ?_
            ring
        _ = ∑' z, k x z * (∑' u, kpow k n z u * k u y) := by
            refine tsum_congr fun z => ?_
            exact ENNReal.tsum_mul_left
        _ = ∑' z, k x z * (∑' u, k z u * kpow k n u y) := by
            refine tsum_congr fun z => ?_
            rw [ih z y]
        _ = ∑' z, ∑' u, k x z * (k z u * kpow k n u y) := by
            refine tsum_congr fun z => ?_
            exact (ENNReal.tsum_mul_left).symm
        _ = ∑' z, ∑' u, (k x z * k z u) * kpow k n u y := by
            refine tsum_congr fun z => tsum_congr fun u => ?_
            ring
        _ = ∑' u, ∑' z, (k x u * k u z) * kpow k n z y := rfl
        _ = ∑' u, ∑' z, k x u * (k u z * kpow k n z y) := by
            refine tsum_congr fun u => tsum_congr fun z => ?_
            ring
        _ = ∑' u, k x u * (∑' z, k u z * kpow k n z y) := by
            refine tsum_congr fun u => ?_
            exact ENNReal.tsum_mul_left

/-- **`kpow` is the production matrix power** `KernelPower.Kpow` (the paper's `T^ℓ`), for every
`n`.  In particular `kpow D.k ℓ v y = T^ℓ(v,y)` for `ℓ = 2, 3, 4`, the powers appearing in
Lemma I.4.17. -/
theorem kpow_eq_Kpow {k : V → V → ℝ≥0∞} (n : ℕ) (x y : V) :
    kpow k n x y = PercLib.CriticalLRP.KernelPower.Kpow k n x y := by
  induction n generalizing x y with
  | zero =>
      simp only [kpow_zero, PercLib.CriticalLRP.KernelPower.Kpow_zero,
        PercLib.CriticalLRP.KernelPower.deltaE]
  | succ n ih =>
      have hcomm : ∀ a b : V,
          (∑' z, PercLib.CriticalLRP.KernelPower.Kpow k n a z * k z b)
            = ∑' z, k a z * PercLib.CriticalLRP.KernelPower.Kpow k n z b := by
        intro a b
        have e1 : (∑' z, PercLib.CriticalLRP.KernelPower.Kpow k n a z * k z b)
            = ∑' z, kpow k n a z * k z b := by
          refine tsum_congr fun z => ?_
          rw [show PercLib.CriticalLRP.KernelPower.Kpow k n a z = kpow k n a z
            from (ih a z).symm]
        rw [e1, kpow_comm_k n a b]
        refine tsum_congr fun z => ?_
        rw [show kpow k n z b = PercLib.CriticalLRP.KernelPower.Kpow k n z b from ih z b]
      calc kpow k (n + 1) x y = ∑' z, k x z * kpow k n z y := kpow_succ k n x y
        _ = ∑' z, k x z * PercLib.CriticalLRP.KernelPower.Kpow k n z y := by
            refine tsum_congr fun z => ?_
            rw [ih]
        _ = ∑' z, PercLib.CriticalLRP.KernelPower.Kpow k n x z * k z y :=
            (hcomm x y).symm
        _ = PercLib.CriticalLRP.KernelPower.Kpow k (n + 1) x y :=
            (PercLib.CriticalLRP.KernelPower.Kpow_succ k n x y).symm


/-- Data of a symmetric sub-probability kernel with unit diagonal and total mass `χ`.  For the
two-point function `T` of a transitive weighted graph one takes `k = T` and
`χ = ∑_z T(x,z) = E|K|` (the row sum is independent of `x` by transitivity). -/
structure KernelData (V : Type*) [Countable V] where
  /-- the kernel (the two-point function `T`) -/
  k : V → V → ℝ≥0∞
  /-- the susceptibility `χ = E|K|` -/
  χ : ℝ≥0∞
  /-- symmetry of the two-point function -/
  symm : ∀ a b, k a b = k b a
  /-- the two-point function is at most one -/
  le_one : ∀ a b, k a b ≤ 1
  /-- the diagonal of the two-point function is one -/
  diag : ∀ a, k a a = 1
  /-- the row sums of the two-point function are the first moment -/
  row : ∀ a, (∑' z, k a z) ≤ χ

namespace KernelData

variable (D : KernelData V)

/-- Monotonicity of the row sum: `∑_z k a z ≤ χ`. -/
theorem row_le (a : V) : (∑' z, D.k a z) ≤ D.χ := D.row a

end KernelData

/-! ## The four shapes of the atlas

Every shape is the sum, over the three internal vertices `w1, w2, w3` and the three labels
`x1, x2, x3`, of a product of seven kernel factors — one for each of the `2p + 2q + 1 = 7`
edges of the tree diagram.  The summation order is irrelevant (`ENNReal.tsum_comm`); it is
chosen so that the label sums are innermost. -/

/-- **Shape `ℓ = 2`** (three trees): `x - w1 - w2 - w3` is the chain and `y` hangs off `w1`, so the
`y`-path is the single edge `w1 - y` followed by... nothing: the tree path from the root to `y` is
`x - w1 - y`, of length two.  Diagram (node names as in `atlasDiagrams`):
`x-w1, w1-w2, w1-y, w2-w3, w2-x1, w3-x2, w3-x3`. -/
def shapeTwo (D : KernelData V) (v y : V) : ℝ≥0∞ :=
  ∑' w1, ∑' w2, ∑' w3, ∑' x1, ∑' x2, ∑' x3,
    D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3 * D.k w2 x1 * D.k w3 x2 * D.k w3 x3

/-- **Shape `ℓ = 3`, balanced** (three trees): the two children of `w1` are `w2` carrying `x1, x2`
and `w3` carrying `x3, y`.  Diagram: `x-w1, w1-w2, w1-w3, w2-x1, w2-x2, w3-x3, w3-y`. -/
def shapeThreeA (D : KernelData V) (v y : V) : ℝ≥0∞ :=
  ∑' w1, ∑' w2, ∑' w3, ∑' x1, ∑' x2, ∑' x3,
    D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w2 x1 * D.k w2 x2 * D.k w3 x3 * D.k w3 y

/-- **Shape `ℓ = 3`, chain** (three trees): `x - w1 - w2 - w3` is the chain, `y` hangs off `w2` and
`x1` off `w1`.  Diagram: `x-w1, w1-w2, w1-x1, w2-w3, w2-y, w3-x2, w3-x3`. -/
def shapeThreeB (D : KernelData V) (v y : V) : ℝ≥0∞ :=
  ∑' w1, ∑' w2, ∑' w3, ∑' x1, ∑' x2, ∑' x3,
    D.k v w1 * D.k w1 w2 * D.k w1 x1 * D.k w2 w3 * D.k w2 y * D.k w3 x2 * D.k w3 x3

/-- **Shape `ℓ = 4`, chain** (six trees): `x - w1 - w2 - w3 - y` is the pinned path, and the three
labels hang off `w1, w2, w3` respectively.  Diagram:
`x-w1, w1-w2, w1-x1, w2-w3, w2-x2, w3-x3, w3-y`. -/
def shapeFour (D : KernelData V) (v y : V) : ℝ≥0∞ :=
  ∑' w1, ∑' w2, ∑' w3, ∑' x1, ∑' x2, ∑' x3,
    D.k v w1 * D.k w1 w2 * D.k w1 x1 * D.k w2 w3 * D.k w2 x2 * D.k w3 x3 * D.k w3 y

/-- The `q = 0`, `p = 3` diagram atlas: the three `ℓ = 2` trees, the six `ℓ = 3` trees and the six
`ℓ = 4` trees, with the multiplicities `3, 3, 3, 6` of the four shapes (machine-checked in
`Main.lean`, `atlasDiagrams_classification`). -/
def atlas (D : KernelData V) (v y : V) : ℝ≥0∞ :=
  3 * shapeTwo D v y + 3 * shapeThreeA D v y + 3 * shapeThreeB D v y + 6 * shapeFour D v y

/-! ## The fifteen trees, explicitly

The list of the fifteen full binary trees with four labelled leaves `y, x1, x2, x3` and root `x`,
as edge lists on the node set `0 = x`, `1, 2, 3` = the internal vertices, `4 = y`,
`5 = x1`, `6 = x2`, `7 = x3`.  Obtained from the tree-sum recursion of (I.2.2) (each unordered
split counted once at a fixed basepoint), which has fifteen terms at four labels. -/

/-- Node coding: `0 = x` (root), `1,2,3 = w1,w2,w3` (internal), `4 = y`, `5 = x1`, `6 = x2`,
`7 = x3`. -/
abbrev Node := ℕ

/-- The fifteen tree diagrams of the `q = 0`, `p = 3` atlas. -/
def atlasDiagrams : List (List (Node × Node)) :=
  [ -- ℓ = 2 (3 trees): x-w1-w2-w3, y at w1
    [(0, 1), (1, 2), (1, 4), (2, 3), (2, 5), (3, 6), (3, 7)],
    [(0, 1), (1, 2), (1, 4), (2, 3), (2, 6), (3, 5), (3, 7)],
    [(0, 1), (1, 2), (1, 4), (2, 3), (2, 7), (3, 5), (3, 6)],
    -- ℓ = 3 balanced (3 trees): cherries {y, xi} and {the other two}
    [(0, 1), (1, 2), (1, 3), (2, 6), (2, 7), (3, 5), (3, 4)],
    [(0, 1), (1, 2), (1, 3), (2, 6), (2, 4), (3, 5), (3, 7)],
    [(0, 1), (1, 2), (1, 3), (2, 7), (2, 4), (3, 5), (3, 6)],
    -- ℓ = 3 chain (3 trees): y at w2, xi at w1
    [(0, 1), (1, 2), (1, 7), (2, 3), (2, 4), (3, 5), (3, 6)],
    [(0, 1), (1, 2), (1, 6), (2, 3), (2, 4), (3, 5), (3, 7)],
    [(0, 1), (1, 2), (1, 5), (2, 3), (2, 4), (3, 6), (3, 7)],
    -- ℓ = 4 chain (6 trees): x-w1-w2-w3-y with one label at each internal node
    [(0, 1), (1, 2), (1, 7), (2, 3), (2, 6), (3, 5), (3, 4)],
    [(0, 1), (1, 2), (1, 7), (2, 3), (2, 5), (3, 6), (3, 4)],
    [(0, 1), (1, 2), (1, 6), (2, 3), (2, 7), (3, 5), (3, 4)],
    [(0, 1), (1, 2), (1, 6), (2, 3), (2, 5), (3, 7), (3, 4)],
    [(0, 1), (1, 2), (1, 5), (2, 3), (2, 7), (3, 6), (3, 4)],
    [(0, 1), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7), (3, 4)]]

/-- The neighbours of a node in an edge list. -/
def nbrs (E : List (Node × Node)) (a : Node) : List Node :=
  E.filterMap fun p => if p.1 = a then some p.2 else if p.2 = a then some p.1 else none

/-- The set of nodes reachable from `0` in at most `n` steps. -/
def reachN (E : List (Node × Node)) : ℕ → List Node
  | 0 => [0]
  | (n + 1) => reachN E n ++ (reachN E n).flatMap (nbrs E)

/-- The tree distance from the root `0 = x` to the target leaf `4 = y`. -/
def pathLen (E : List (Node × Node)) : ℕ :=
  ((List.range 12).find? fun n => decide (4 ∈ reachN E n)).getD 0


end PercLib.CriticalLRP.QZeroAtlas
