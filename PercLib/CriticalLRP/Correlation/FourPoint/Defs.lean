/- Integrated from independently rebuilt Ultramath work.
Production base 3b6ff818cd3ac1a9cee99dcfff154a2ff4f85095.
Scratch source: ../../.ultramath/smwvp122a/m3/Defs.lean.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Finset.Basic

/-!
Deterministic four-point pairing cover for the proof of Lemma I.4.16 of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.4 (proof of the generalized tree-graph inequality).

The paper's step (p. 44) asserts that for three points `x, y, z` joined to the origin there is a
point `w` such that one of the three events

  `{0 ↔ x, w} ∘ {w ↔ y} ∘ {w ↔ z}`,
  `{0 ↔ y, w} ∘ {w ↔ x} ∘ {w ↔ z}`,
  `{0 ↔ z, w} ∘ {w ↔ x} ∘ {w ↔ y}`

holds, where `∘` denotes edge-disjoint occurrence and `{0 ↔ x, w}` is the event that `0`, `x` and
`w` lie in a common cluster.  Each printed alternative fixes one pairing of the three terminals.
The present development isolates the deterministic content in the form that is actually true and
that the union bound over the three pairings uses: there are a vertex `w`, a partition
`{t, u, v} = {x, y, z}` and four walks

* `P : o → w` and `Q : t → w`, whose union is the connected witness for `{o ↔ t, w}`
  (`o`, `t` and `w` all lie on the concatenated walk `o → w → t`),
* `R : u → w` and `S : v → w`,

such that `R` and `S` are edge-disjoint from each other and from both `P` and `Q`.  This is
exactly the hypothesis consumed by the three-fold BK inequality in the paper's sum: the first
factor is the three-point function `P(o ↔ t, w)`, the other two are the two-point functions
`P(w ↔ u)`, `P(w ↔ v)`.

The configurations that the printed formulation hides are represented uniformly: the "joint"
terminal `t` is not fixed in advance (any of the three terminals may play its role), one of the
two two-point arms may be empty (`u = w` or `v = w`, giving the empty walk and the factor
`P(w ↔ w) = 1`), and the joint cluster `P ∪ Q` may share edges internally, as it must when the
four points are collinear.
-/

@[expose] public section

namespace PercLib.CriticalLRP.FourPoint

variable {V : Type*} [DecidableEq V]

/-- **The deterministic four-point pairing cover.**  For vertices `o, x, y, z` of a graph `G`
there are a centre `w`, a partition `{t, u, v} = {x, y, z}` of the three terminals and walks
`P : o → w`, `Q : t → w`, `R : u → w`, `S : v → w` such that the edge lists of `R` and `S` are
pairwise disjoint from each other and from the edge lists of both `P` and `Q`.

The pair `(P, Q)` is the joint cluster witnessing that `o`, `t` and `w` are connected; `R` and `S`
are the two arms.  Nothing is required of the edge lists of `P` and `Q` relative to each other,
which is what allows the collinear configuration to be covered. -/
def HasCover (G : SimpleGraph V) (o x y z : V) : Prop :=
  ∃ (w t u v : V) (P : G.Walk o w) (Q : G.Walk t w) (R : G.Walk u w) (S : G.Walk v w),
    ({t, u, v} : Finset V) = {x, y, z} ∧
      (P.edges ++ Q.edges).Disjoint R.edges ∧
      (P.edges ++ Q.edges).Disjoint S.edges ∧ R.edges.Disjoint S.edges

/-- `ThreeArmData G x y z` : there is a vertex `w` and three pairwise edge-disjoint geodesics
from `x`, `y`, `z` to `w`.  This is the branch-point decomposition underlying the first
tree-graph inequality (I.2.1), in the form needed by the four-point cover: the arms are also
required to be shortest paths, so that they can be fed to the metric edge-disjointness criterion
of `disjoint_of_dist_add`. -/
def ThreeArmData (G : SimpleGraph V) (x y z : V) : Prop :=
  ∃ (w : V) (p : G.Walk x w) (q : G.Walk y w) (r : G.Walk z w),
    p.IsPath ∧ q.IsPath ∧ r.IsPath ∧
      p.length = G.dist x w ∧ q.length = G.dist y w ∧ r.length = G.dist z w ∧
      p.edges.Disjoint q.edges ∧ p.edges.Disjoint r.edges ∧ q.edges.Disjoint r.edges

/-- `ArmsGood G x y z n` : there are walks from `x`, `y`, `z` to a common vertex whose total
length is `n`.  Used to run the minimality argument that produces `ThreeArmData`. -/
def ArmsGood (G : SimpleGraph V) (x y z : V) (n : ℕ) : Prop :=
  ∃ (w : V) (p : G.Walk x w) (q : G.Walk y w) (r : G.Walk z w),
    p.length + q.length + r.length = n

end PercLib.CriticalLRP.FourPoint
