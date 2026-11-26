/-
Classification of the seven split positions of the six-terminal `p = 5` arm system,
and the scalar normal form of the `p = 5`, `k = 2` target.

Swarm `smwxenel0`, member `m2`, direction `I417-TARGET-NORMAL-FORM`.

This file is *definitions and finite combinatorics only*.  The object is the abstract
nine-edge, six-leaf binary tree of `SixPoint.CombSystem`: leaves `b₀..b₄, t`, internal
vertices `u, v, w` and the landing point `c` of the sixth arm.  Attaching `t` at a point
`c` of arm `j` replaces arm `j` by the two edges `armSrc j — c` and `c — armTgt j`, so the
tree always has `2 * 6 - 3 = 9` edges and four internal vertices.

For every split position `j : Fin 7` we compute
* the two-colouring of the tree (the bipartition the paper's `k`-step of the tree-graph
  inequality uses) and the size of its two classes on the internal vertices,
* the admissible star sets `S : {u,v,w,c}` of size `2 = k`: the independent pairs whose
  three-stars are edge-disjoint and whose complement is three residual edges,
* the resulting *position pattern*: the leaf triple of each three-star and the three
  residual pairs.

The main point is that at every split position the two-star-three-single regrouping exists,
and that the source's bipartition argument alone produces only two of the three admissible
patterns at six of the seven positions.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointThree.Defs
/-!
# Split-position classification and the `p = 5`, `k = 2` normal form

This covers the finite star patterns and three of the four partial certificate cases.
The remaining certificates and moment/slot evaluations are separate work.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern

variable {V : Type*}

/-! ## Vertex indexing and the bridge to `armSrc`/`armTgt` -/

/-- The ten vertices of the split tree.  `0..4` are `b₀..b₄`, `5` is `t`, `6,7,8` are
`u, v, w` and `9` is the landing point `c` of the sixth arm. -/
def vert (b0 b1 b2 b3 b4 t u v w c : V) : ℕ → V
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => t
  | 6 => u
  | 7 => v
  | 8 => w
  | _ => c

/-- Vertex index of the source of comb arm `i`. -/
def srcIdx : Fin 7 → ℕ := ![0, 1, 2, 3, 4, 6, 7]

/-- Vertex index of the target of comb arm `i`. -/
def tgtIdx : Fin 7 → ℕ := ![6, 6, 7, 8, 8, 7, 8]

/-- The index of the landing point. -/
def cIdx : ℕ := 9

/-- The index of the sixth terminal. -/
def tIdx : ℕ := 5

/-- The four internal vertices of the split tree. -/
def internals : List ℕ := [6, 7, 8, 9]

/-- `armSrc` is the vertex function `vert` at the tabulated source index. -/
theorem armSrc_eq_vert (b0 b1 b2 b3 b4 t u v w c : V) (i : Fin 7) :
    armSrc b0 b1 b2 b3 b4 u v i = vert b0 b1 b2 b3 b4 t u v w c (srcIdx i) := by
  fin_cases i <;> rfl

/-- `armTgt` is the vertex function `vert` at the tabulated target index. -/
theorem armTgt_eq_vert (b0 b1 b2 b3 b4 t u v w c : V) (i : Fin 7) :
    armTgt u v w i = vert b0 b1 b2 b3 b4 t u v w c (tgtIdx i) := by
  fin_cases i <;> rfl

/-! ## The nine edges of a split position -/

/-- **The nine macro-edges of the split tree at position `j`.**  The seven comb arms are
`(srcIdx i, tgtIdx i)`; arm `j` is replaced by `(srcIdx j, c)` and `(c, tgtIdx j)`, and
`(t, c)` is the sixth arm.  Every pair is listed with its smaller coordinate first. -/
def splitEdges : Fin 7 → List (ℕ × ℕ)
  | 0 => [(1, 6), (2, 7), (3, 8), (4, 8), (5, 9), (6, 7), (7, 8), (0, 9), (6, 9)]
  | 1 => [(0, 6), (2, 7), (3, 8), (4, 8), (5, 9), (6, 7), (7, 8), (1, 9), (6, 9)]
  | 2 => [(0, 6), (1, 6), (3, 8), (4, 8), (5, 9), (6, 7), (7, 8), (2, 9), (7, 9)]
  | 3 => [(0, 6), (1, 6), (2, 7), (4, 8), (5, 9), (6, 7), (7, 8), (3, 9), (8, 9)]
  | 4 => [(0, 6), (1, 6), (2, 7), (3, 8), (5, 9), (6, 7), (7, 8), (4, 9), (8, 9)]
  | 5 => [(0, 6), (1, 6), (2, 7), (3, 8), (4, 8), (5, 9), (7, 8), (6, 9), (7, 9)]
  | 6 => [(0, 6), (1, 6), (2, 7), (3, 8), (4, 8), (5, 9), (6, 7), (7, 9), (8, 9)]

/-- The neighbours of `a` in the split-`j` tree, in edge-list order. -/
def nbrs (j : Fin 7) (a : ℕ) : List ℕ :=
  (splitEdges j).filterMap (fun p =>
    if p.1 = a then some p.2 else if p.2 = a then some p.1 else none)

/-- The edges of `splitEdges j` incident to `a`. -/
def edgesAt (j : Fin 7) (a : ℕ) : List (ℕ × ℕ) :=
  (splitEdges j).filter (fun p => p.1 = a || p.2 = a)

/-- The edges of `splitEdges j` incident to neither `a` nor `b`. -/
def residual (j : Fin 7) (a b : ℕ) : List (ℕ × ℕ) :=
  (splitEdges j).filter (fun p =>
    !(p.1 = a) && !(p.1 = b) && !(p.2 = a) && !(p.2 = b))

/-- The tree is always a nine-edge graph. -/
theorem edge_count : ∀ j : Fin 7, (splitEdges j).length = 9 := by decide

/-- The nine edges of a split position are distinct. -/
theorem edge_nodup : ∀ j : Fin 7, (splitEdges j).Nodup := by decide

/-- Each of the four internal vertices has degree three. -/
theorem internal_degree : ∀ j : Fin 7, ∀ x ∈ internals, (nbrs j x).length = 3 := by decide

/-- Each of the six terminals is a leaf. -/
theorem leaf_degree : ∀ j : Fin 7, ∀ x ∈ [0, 1, 2, 3, 4, 5], (nbrs j x).length = 1 := by
  decide

/-- Every edge of the split tree joins an internal vertex to a leaf or two internal vertices;
in particular the ten vertices are exactly the six leaves and the four internals. -/
theorem edge_support : ∀ j : Fin 7, ∀ p ∈ splitEdges j,
    p.1 ∈ [0, 1, 2, 3, 4, 5] ∨ p.1 ∈ internals := by decide

/-! ## The bridge: the abstract edges are the production arms -/

/-- At split position `j` the abstract tree contains the macro-edge of every comb arm
`i ≠ j`, the two halves of arm `j`, and the sixth arm `t — c`. -/
theorem arms_in_splitEdges : ∀ j i : Fin 7, i ≠ j →
    (srcIdx i, tgtIdx i) ∈ splitEdges j := by decide

/-- The two halves of the split arm `j`. -/
theorem split_arm_halves : ∀ j : Fin 7,
    (min (srcIdx j) cIdx, max (srcIdx j) cIdx) ∈ splitEdges j ∧
      (min cIdx (tgtIdx j), max cIdx (tgtIdx j)) ∈ splitEdges j := by decide

/-- The sixth arm `t — c` is a single edge of the abstract tree. -/
theorem sixth_arm_in_splitEdges : ∀ j : Fin 7, (tIdx, cIdx) ∈ splitEdges j := by decide

/-! ## The independent pairs of internal vertices -/

/-- `a` and `b` are an admissible star set: both internal, distinct, written in increasing
order, and not adjacent in the split-`j` tree.  Two three-stars at non-adjacent internal
vertices are edge-disjoint and their complement is three residual edges. -/
def indep (j : Fin 7) (a b : ℕ) : Bool :=
  internals.contains a && internals.contains b && decide (a < b) &&
    !((nbrs j a).contains b)

/-- The admissible star sets at split position `j`, in lexicographic order. -/
def indepPairs (j : Fin 7) : List (ℕ × ℕ) :=
  ((internals.product internals).filter (fun p => indep j p.1 p.2))

/-- The classification table of admissible star sets, one line per split position. -/
def indepTable : Fin 7 → List (ℕ × ℕ)
  | 0 => [(6, 8), (7, 9), (8, 9)]
  | 1 => [(6, 8), (7, 9), (8, 9)]
  | 2 => [(6, 8), (6, 9), (8, 9)]
  | 3 => [(6, 8), (6, 9), (7, 9)]
  | 4 => [(6, 8), (6, 9), (7, 9)]
  | 5 => [(6, 7), (6, 8), (8, 9)]
  | 6 => [(6, 8), (6, 9), (7, 8)]

/-- **Classification of the admissible star sets.**  At every split position there are
exactly three admissible star sets, and they are the tabulated ones. -/
theorem indepPairs_eq_table : ∀ j : Fin 7, indepPairs j = indepTable j := by decide

/-- Every split position admits exactly three `k = 2` star sets. -/
theorem indepPairs_length : ∀ j : Fin 7, (indepPairs j).length = 3 := by decide

/-- The star sets listed for `j = 2` are exactly the three `2`-subsets of the large
bipartition class `{u, w, c}`; the one used by production (`{u, w}`) is the first. -/
theorem indepPairs_two : indepPairs 2 = [(6, 8), (6, 9), (8, 9)] := by decide

/-! ## The bipartition used by the paper's `k`-step -/

/-- The bipartition class of `u` at split position `j` (the tree is bipartite; this is the
class of the internal vertex `u`). -/
def classU : Fin 7 → List ℕ
  | 0 => [0, 2, 5, 6, 8]
  | 1 => [1, 2, 5, 6, 8]
  | 2 => [6, 8, 9]
  | 3 => [2, 3, 5, 6, 8]
  | 4 => [2, 4, 5, 6, 8]
  | 5 => [3, 4, 5, 6, 7]
  | 6 => [2, 3, 4, 6, 9]

/-- The class of `u` is a proper side of the bipartition: no edge joins two of its
vertices. -/
theorem classU_proper : ∀ j : Fin 7, ∀ p ∈ splitEdges j,
    ¬((p.1 ∈ classU j) ↔ (p.2 ∈ classU j)) := by decide

/-- The size of the class of `u`.  It is `3` at `j = 2` and `5` at every other position. -/
theorem classU_card : ∀ j : Fin 7, (classU j).length = (if j = 2 then 3 else 5) := by decide

/-- The number of internal vertices in the class of `u`. -/
def internalClassSize (s : List ℕ) : ℕ :=
  (internals.filter (fun x => s.contains x)).length

/-- **Class sizes.**  At `j = 2` the class of `u` contains three internal vertices;
at every other split position both classes contain two. -/
theorem internal_class_sizes : ∀ j : Fin 7,
    internalClassSize (classU j) = (if j = 2 then 3 else 2) := by decide

/-- **`k = 2` admissibility at every split position.**  The larger internal class has at
least `k = 2` vertices, so the paper's `k`-step of Lemma I.4.16 can be applied at every
split position (here `ceil ((5 - 1)/2) = 2`). -/
theorem larger_class_at_least_two : ∀ j : Fin 7,
    2 ≤ max (internalClassSize (classU j)) (4 - internalClassSize (classU j)) := by
  decide

/-- The `2`-element subsets of a single bipartition class: the pairs the paper's argument
produces directly. -/
def classPairs (j : Fin 7) : List (ℕ × ℕ) :=
  ((internals.product internals).filter (fun p =>
    decide (p.1 < p.2) && ((classU j).contains p.1 == (classU j).contains p.2)))

/-- **The source-class pairs are admissible.**  Every pair inside one class is an
independent pair, hence a valid two-star set. -/
theorem classPairs_subset_indep : ∀ j : Fin 7, ∀ p ∈ classPairs j, p ∈ indepPairs j := by
  decide

/-- The number of pairs the paper's bipartition argument alone produces at each split
position: two at six positions, three at `j = 2`. -/
theorem classPairs_length : ∀ j : Fin 7, (classPairs j).length = (if j = 2 then 3 else 2) := by
  decide

/-- The production split position `j = 2` is the only one where the bipartition class not
containing `v` has three internal vertices, hence the only one where the source's `k`-step
produces all three admissible star sets. -/
theorem classPairs_two : classPairs 2 = [(6, 8), (6, 9), (8, 9)] := by decide

/-! ## The position pattern of a star set -/

/-- **The partition behind a star set.**  The nine edges split as the three edges at `a`,
the three edges at `b`, and the three residual edges; the three groups are pairwise
disjoint and cover the tree. -/
theorem star_partition : ∀ j : Fin 7, ∀ p ∈ indepPairs j,
    (edgesAt j p.1).length = 3 ∧ (residual j p.1 p.2).length = 3 ∧
      (∀ e ∈ residual j p.1 p.2, e ∉ edgesAt j p.1 ∧ e ∉ edgesAt j p.2) ∧
      (∀ e ∈ splitEdges j, e ∈ residual j p.1 p.2 ∨ e ∈ edgesAt j p.1 ∨
        e ∈ edgesAt j p.2) := by decide

/-- The three-star at an internal vertex has that vertex's three neighbours as leaves. -/
theorem star_leaves : ∀ j : Fin 7, ∀ x ∈ internals, (nbrs j x).length = 3 :=
  fun j x hx => internal_degree j x hx

/-- **The production pattern at `j = 2`, `S = {u, w}`.**  The two stars are
`{b₀, b₁, v}` at `u` and `{b₃, b₄, v}` at `w`, and the residual edges are `t — c`,
`b₂ — c`, `c — v`. -/
theorem production_pattern :
    nbrs 2 6 = [0, 1, 7] ∧ nbrs 2 8 = [3, 4, 7] ∧
      residual 2 6 8 = [(5, 9), (2, 9), (7, 9)] := by decide

/-- The five position events read off the pattern at `j = 2`, `S = {u, w}`: they are
exactly the two joint pairs and the three two-point factors of
`SixPoint.combSystem_twoJointThree`. -/
theorem production_pattern_events (b0 b1 b2 b3 b4 t u v w c : V) :
    (conn (vert b0 b1 b2 b3 b4 t u v w c 0) (vert b0 b1 b2 b3 b4 t u v w c 7) ∩
        conn (vert b0 b1 b2 b3 b4 t u v w c 1) (vert b0 b1 b2 b3 b4 t u v w c 7)) =
      (conn b0 v ∩ conn b1 v) ∧
    (conn (vert b0 b1 b2 b3 b4 t u v w c 3) (vert b0 b1 b2 b3 b4 t u v w c 7) ∩
        conn (vert b0 b1 b2 b3 b4 t u v w c 4) (vert b0 b1 b2 b3 b4 t u v w c 7)) =
      (conn b3 v ∩ conn b4 v) ∧
    conn (vert b0 b1 b2 b3 b4 t u v w c 5) (vert b0 b1 b2 b3 b4 t u v w c 9) = conn t c ∧
    conn (vert b0 b1 b2 b3 b4 t u v w c 2) (vert b0 b1 b2 b3 b4 t u v w c 9) = conn b2 c ∧
    conn (vert b0 b1 b2 b3 b4 t u v w c 9) (vert b0 b1 b2 b3 b4 t u v w c 7) = conn c v := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [vert]

/-! ## The scalar normal form of the `p = 5`, `k = 2` target -/

/-- The edge budget of the tree-graph inequality: the `k` three-stars use `3 * k` edges and
the remaining factors `2 * p - 1 - 3 * k` two-point edges, adding up to the `2 * p - 1`
edges of the binary tree on `p + 1` leaves. -/
theorem edge_budget (p k : ℕ) (hk : 3 * k ≤ 2 * p - 1) :
    3 * k + (2 * p - 1 - 3 * k) = 2 * p - 1 := by omega

/-- At `p = 5`, `k = 2` the nine edges are two three-stars and three residual edges. -/
theorem budget_five_two : 3 * 2 + (2 * 5 - 1 - 3 * 2) = 9 := by omega

/-- The `k = 2` instance is admissible at `p = 5`, i.e. `k ≤ ceil ((p - 1) / 2)`. -/
theorem two_admissible_five : 2 * 2 ≤ 5 - 1 := by omega

/-- The tree-graph coefficient at `p = 5` is `(2 * 5 - 3)!! = 105`. -/
theorem double_factorial_five : Nat.doubleFactorial (2 * 5 - 3) = 105 := by decide

/-- The residual edge count at `p = 5`, `k = 2`, which is the exponent of the first moment
in the target. -/
theorem residual_exponent_five_two : 2 * 5 - 1 - 3 * 2 = 3 := by omega

/-- The nested product of `k` three-point factors and `r` two-point factors, in the nesting
order the fivefold BK product produces. -/
noncomputable def nestProd (a b : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞
  | 0, r => b ^ r
  | (k + 1), r => a * nestProd a b k r

/-- **Target normal form.**  The nested product of the `k` three-point factors and the
`2 * p - 1 - 3 * k` two-point factors is `a ^ k * b ^ (2 * p - 1 - 3 * k)`. -/
theorem nestProd_eq (a b : ℝ≥0∞) (k r : ℕ) :
    nestProd a b k r = a ^ k * b ^ r := by
  induction k with
  | zero => simp [nestProd]
  | succ k ih =>
    rw [nestProd, ih, pow_succ]
    ring

/-- **The `p = 5`, `k = 2` target in normal form**: the five-factor certificate product is
`(∫ |K|²) ^ 2 * (∫ |K|) ^ 3`, with the second-moment factor twice and the first-moment
factor three times. -/
theorem target_five_two (M2 M1 : ℝ≥0∞) :
    nestProd M2 M1 2 3 = M2 ^ 2 * M1 ^ 3 := by
  rw [nestProd_eq]

/-- The same normal form with the paper's factor count: at `p = 5`, `k = 2` the exponent of
the first moment is `2 * p - 1 - 3 * k = 3`. -/
theorem target_five_two_exponent :
    nestProd (1 : ℝ≥0∞) 1 2 (2 * 5 - 1 - 3 * 2) = 1 := by
  rw [nestProd_eq, residual_exponent_five_two]
  simp

/-- A three-star: three edge-disjoint-or-not walks at a common centre `x`, two legs `a`, `b`
and one spine to `y`.  The certificate is the union of the two paths through the spine. -/
structure StarCert [Countable V] (ω : Config V) where
  /-- the centre -/
  x : V
  /-- first leg endpoint -/
  a : V
  /-- second leg endpoint -/
  b : V
  /-- spine target -/
  y : V
  /-- leg to the first endpoint -/
  legA : (openGraph ω).Walk a x
  /-- leg to the second endpoint -/
  legB : (openGraph ω).Walk b x
  /-- spine from the centre -/
  spine : (openGraph ω).Walk x y

namespace StarCert

variable [Countable V] {ω : Config V}

/-- The union of the three walks of the star. -/
def cover (S : StarCert ω) : Set (Sym2 V) :=
  walkEdges S.legA ∪ walkEdges S.legB ∪ walkEdges S.spine

/-- The certificate of the joint pair `a — y`, `b — y`. -/
def cert (S : StarCert ω) : Set (Sym2 V) :=
  walkEdges (S.legA.append S.spine) ∪ walkEdges (S.legB.append S.spine)

end StarCert

end PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern
