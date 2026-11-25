/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# `hgap` in cluster coordinates: what is unconditional, and what restoration buys

`VolumeMoments/I58Cross.lean` carries the per-pair hypothesis

  `hgap : |pairDisj x y z − pairProd x z| ≤ pairAll x y z`,

where, in the paper's notation (§I.5.2, the third display of `lem:disjoint_connections`),

* `pairDisj x y z = E_r[ 1(y∉K) 1(x∈K) 1(z∈K_y) ]`,
* `pairAll  x y z = E_r[ 1(x∈K) 1(y∈K) 1(z∈K) ]`,
* `pairProd  x   z = P_r(0↔x) P_r(y↔z)`.

The canonical model instantiates `K = K_0` (the cluster of the origin) and `K_y` (the cluster of
`y`), so the three quantities read

* `pairDisjSet o x y z = {o↔x} ∩ {o↮y} ∩ {y↔z}`,
* `pairAllSet  o x y z = {o↔x} ∩ {o↔y} ∩ {o↔z}`  (`= {o↔x↔y↔z}`, the four-point event),
* `connSet o x` and `connSet y z` for the two-point functions.

This file proves, unconditionally in the canonical countable product model:

* `pairDisjSet_subset_disjSet` — `{o↔x, y∉K_0, z∈K_y} ⊆ {o↔x ↮ y↔z}`.  The isolated hypothesis
  `y ∉ K_0` is exactly what makes the two witnesses edge-disjoint: a shared edge between an
  `o`–`x` path and a `y`–`z` path would join `o` to `y`.
* `pairDisjSet_eq_disjSet_inter` — the exact identification
  `{x∈K_0, y∉K_0, z∈K_y} = {o↔x ↮ y↔z} ∩ {y ∉ K_0}`, so
  `P(pairDisj) = P(o↔x ↮ y↔z, y ∉ K_0)`.
* `disjSet_inter_connSet_subset_pairAllSet` — `{o↔x} ∩ {y↔z} ∩ {o↔y} ⊆ {x,y,z ∈ K_0}`:
  if the two connections are disjointly witnessed **and** `y ∈ K_0`, then `o`, `x`, `y`, `z` are
  all in one cluster, so the four-point event (`= pairAllSet`) holds.
* `edgeMeasure_gap_cluster_two` — the **unconditional two-sided bound with constant 2**,

  `|P(x∈K_0, y∉K_0, z∈K_y) − P(o↔x)P(y↔z)| ≤ 2 P(x,y,z ∈ K_0)`.
* `edgeMeasure_gap_cluster_sharp` — the paper's constant-1 form, from the extra hypothesis
  `hrest : P(o↔x ↮ y↔z) ≤ P(x∈K_0, y∉K_0, z∈K_y)`.

**Accounting of hypotheses.**  The constant in the two-sided bound is the only thing at stake.
The chain is
`P(x,y,z∈K_0) ≥ P(o↔x↔y↔z) ≥ P(o↔x)P(y↔z) − P(o↔x ↮ y↔z)` (the previous file) together with
`P(o↔x ↮ y↔z) ≤ P(x,y,z∈K_0) + P(x∈K_0, y∉K_0, z∈K_y)` (here); the sum of the two gives the
constant `2`.  The constant `1` of the paper is exactly the statement
`P(o↔x ↮ y↔z) ≤ P(x∈K_0, y∉K_0, z∈K_y)`, i.e. that the disjoint-occurrence event carries
`y ∉ K_0` — the restoration statement of §I.2.1 (`Correlation/SelfRestoration.lean`,
`Correlation/TwoClusterGap.lean`).  It is *not* an identity of events: if `o—x`, `x—y`, `y—z`
and `o—z` are all open then `o↔x ↮ y↔z` holds with `y ∈ K_0`, so the unconditioned inclusion
`disjSet ⊆ pairDisjSet` fails; only the *probabilistic* form `hrest` would suffice, and it is the
content of restoration, not of BK/FKG.  Only `π e < 1` is assumed below; nothing else.
-/
module

public import PercLib.CriticalLRP.Correlation.TwoClusterGap
public import PercLib.CriticalLRP.VolumeMoments.I58Cross
public import PercLib.CriticalLRP.Correlation.HgapDisjointConnections

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. The model's per-pair events in cluster coordinates -/

/-- `E_r[1(y∉K) 1(x∈K) 1(z∈K_y)]` for `K = K_0`, `K_y` the cluster of `y`. -/
def pairDisjSet (o x y z : V) : Set (Config V) :=
  connSet o x ∩ (connSet o y)ᶜ ∩ connSet y z

/-- `E_r[1(x∈K) 1(y∈K) 1(z∈K)]` for `K = K_0`; equivalently the four-point event
`{o↔x↔y↔z}`. -/
def pairAllSet (o x y z : V) : Set (Config V) :=
  connSet o x ∩ connSet o y ∩ connSet o z

theorem measurableSet_pairDisjSet (o x y z : V) : MeasurableSet (pairDisjSet o x y z) :=
  ((measurableSet_connSet o x).inter (measurableSet_connSet o y).compl).inter
    (measurableSet_connSet y z)

theorem measurableSet_pairAllSet (o x y z : V) : MeasurableSet (pairAllSet o x y z) :=
  ((measurableSet_connSet o x).inter (measurableSet_connSet o y)).inter
    (measurableSet_connSet o z)

/-- The left connection of a disjointly-witnessed pair holds in the configuration. -/
theorem connects_left_of_mem_disjSet {ω : Config V} {a b c d : V}
    (h : ω ∈ disjSet a b c d) : Connects ω a b := by
  obtain ⟨s, t, hs, ht, -, hsa, -⟩ := h
  exact connects_mono (fun e he => hs he) hsa

/-- The right connection of a disjointly-witnessed pair holds in the configuration. -/
theorem connects_right_of_mem_disjSet {ω : Config V} {a b c d : V}
    (h : ω ∈ disjSet a b c d) : Connects ω c d := by
  obtain ⟨s, t, hs, ht, -, -, htb⟩ := h
  exact connects_mono (fun e he => ht he) htb

/-! ## 2. The two inclusions -/

/-- `{o↔x, y ∉ K_0, z ∈ K_y} ⊆ {o↔x ↮ y↔z}`.  With `y ∉ K_0`, a common edge of an `o`–`x`
path and a `y`–`z` path would join `o` to `y`; hence the connections are disjoint. -/
theorem pairDisjSet_subset_disjSet (o x y z : V) :
    pairDisjSet o x y z ⊆ disjSet o x y z := by
  rintro ω ⟨⟨hox, hoy⟩, hyz⟩
  by_contra hnot
  exact hoy (connects_trans hox (allConn_of_not_disjOcc hox hyz hnot))

/-- `{o↔x} ∩ {y↔z} ∩ {o↔y} ⊆ {x,y,z ∈ K_0}`: disjoint witnesses plus `y ∈ K_0` force the
four-point event. -/
theorem disjSet_inter_connSet_subset_pairAllSet (o x y z : V) :
    disjSet o x y z ∩ connSet o y ⊆ pairAllSet o x y z := by
  rintro ω ⟨hω, hoy⟩
  exact ⟨⟨connects_left_of_mem_disjSet hω, hoy⟩,
    connects_trans hoy (connects_right_of_mem_disjSet hω)⟩

/-- `{o↔x↔y↔z} ⊆ {x,y,z ∈ K_0}`. -/
theorem allConnSet_subset_pairAllSet (o x y z : V) :
    allConnSet o x y z ⊆ pairAllSet o x y z := by
  rintro ω ⟨hox, hxy, hyz⟩
  exact ⟨⟨hox, connects_trans hox hxy⟩, connects_trans hox (connects_trans hxy hyz)⟩

/-- `{x,y,z ∈ K_0}` **is** the four-point event `{o↔x↔y↔z}` (both inclusions), which is the
identification the paper makes when it replaces `P(0↔x↔y↔z)` by `P(x,y,z ∈ K)`. -/
theorem pairAllSet_eq_allConnSet (o x y z : V) : pairAllSet o x y z = allConnSet o x y z := by
  refine Set.Subset.antisymm ?_ (allConnSet_subset_pairAllSet o x y z)
  rintro ω ⟨⟨hox, hoy⟩, hoz⟩
  exact ⟨hox, connects_trans (connects_symm hox) hoy,
    connects_trans (connects_symm hoy) hoz⟩

/-- `{o↔x ↮ y↔z} ∩ {y ∉ K_0} ⊆ {x∈K_0, y∉K_0, z∈K_y}`: the missing half of the
identification.  On the disjoint-occurrence event with `y ∉ K_0` the connection of `z` to `y` is
off the cluster of the origin, so `x ∈ K_0` and `z ∈ K_y`. -/
theorem disjSet_inter_compl_subset_pairDisjSet (o x y z : V) :
    disjSet o x y z ∩ (connSet o y)ᶜ ⊆ pairDisjSet o x y z := by
  rintro ω ⟨hω, hy⟩
  exact ⟨⟨connects_left_of_mem_disjSet hω, hy⟩, connects_right_of_mem_disjSet hω⟩

/-- **The exact identification of the model's disjoint weight**: the event carrying
`1(y∉K) 1(x∈K) 1(z∈K_y)` is the disjoint occurrence event *with `y ∉ K_0` imposed*,

`{x∈K_0, y∉K_0, z∈K_y} = {o↔x ↮ y↔z} ∩ {y ∉ K_0}`.

So `P(pairDisj) = P(o↔x ↮ y↔z, y ∉ K_0)`, and the difference from the paper's
`P(o↔x ↮ y↔z)` is carried by `{o↔x ↮ y↔z, y ∈ K_0}`, which lies in the four-point event
(`disjSet_inter_connSet_subset_pairAllSet`).  That difference is exactly the loss of a factor `2`
in `edgeMeasure_gap_cluster_two`. -/
theorem pairDisjSet_eq_disjSet_inter (o x y z : V) :
    pairDisjSet o x y z = disjSet o x y z ∩ (connSet o y)ᶜ := by
  refine Set.Subset.antisymm ?_ (disjSet_inter_compl_subset_pairDisjSet o x y z)
  rintro ω ⟨⟨hox, hy⟩, hyz⟩
  exact ⟨pairDisjSet_subset_disjSet o x y z ⟨⟨hox, hy⟩, hyz⟩, hy⟩

/-- `{o↔x ↮ y↔z} ⊆ {x,y,z ∈ K_0} ∪ {x∈K_0, y∉K_0, z∈K_y}`: split according to whether
`y ∈ K_0`. -/
theorem disjSet_subset_pairDisjSet_union_pairAllSet (o x y z : V) :
    disjSet o x y z ⊆ pairDisjSet o x y z ∪ pairAllSet o x y z := by
  intro ω hω
  by_cases hy : ω ∈ connSet o y
  · exact Or.inr (disjSet_inter_connSet_subset_pairAllSet o x y z ⟨hω, hy⟩)
  · exact Or.inl ⟨⟨connects_left_of_mem_disjSet hω, hy⟩,
      connects_right_of_mem_disjSet hω⟩

/-! ## 3. Monotonicity of the real-valued measure -/

theorem real_measure_mono (π : Sym2 V → unitInterval) {A B : Set (Config V)} (h : A ⊆ B) :
    (edgeMeasure π).real A ≤ (edgeMeasure π).real B :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h)

theorem real_measure_union_le (π : Sym2 V → unitInterval) (A B : Set (Config V)) :
    (edgeMeasure π).real (A ∪ B) ≤ (edgeMeasure π).real A + (edgeMeasure π).real B := by
  have hfin : (edgeMeasure π) A + (edgeMeasure π) B ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  calc (edgeMeasure π).real (A ∪ B) ≤ ((edgeMeasure π) A + (edgeMeasure π) B).toReal :=
        (ENNReal.toReal_le_toReal (measure_ne_top _ _) hfin).mpr (measure_union_le A B)
    _ = (edgeMeasure π).real A + (edgeMeasure π).real B := by
        rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]; rfl

/-! ## 4. The two-sided bounds in cluster coordinates -/

/-- **`hgap` in cluster coordinates, unconditionally, with constant `2`.** -/
theorem edgeMeasure_gap_cluster_two (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (o x y z : V) :
    |(edgeMeasure π).real (pairDisjSet o x y z) -
        (edgeMeasure π).real (connSet o x) * (edgeMeasure π).real (connSet y z)| ≤
      2 * (edgeMeasure π).real (pairAllSet o x y z) := by
  have hupper := edgeMeasure_gap_upper_real π hπ o x y z
  have hlower := edgeMeasure_gap_lower_real π hπ o x y z
  have hUD : (edgeMeasure π).real (pairDisjSet o x y z) ≤
      (edgeMeasure π).real (disjSet o x y z) :=
    real_measure_mono π (pairDisjSet_subset_disjSet o x y z)
  have hall : (edgeMeasure π).real (allConnSet o x y z) ≤
      (edgeMeasure π).real (pairAllSet o x y z) :=
    real_measure_mono π (allConnSet_subset_pairAllSet o x y z)
  have hDF : (edgeMeasure π).real (disjSet o x y z) ≤
      (edgeMeasure π).real (pairDisjSet o x y z) + (edgeMeasure π).real (pairAllSet o x y z) :=
    (real_measure_mono π (disjSet_subset_pairDisjSet_union_pairAllSet o x y z)).trans
      (real_measure_union_le π _ _)
  rw [abs_le]
  constructor <;> linarith

/-- **The paper's constant-`1` form, from the restoration inequality.**

`hrest : P(o↔x ↮ y↔z) ≤ P(x∈K_0, y∉K_0, z∈K_y)` is the restoration statement of §I.2.1 in
probabilistic form (the event of the left-hand side is *not* contained in the right-hand side;
only its probability is dominated, and that is exactly what restoration supplies). -/
theorem edgeMeasure_gap_cluster_sharp (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (o x y z : V)
    (hrest : (edgeMeasure π).real (disjSet o x y z) ≤
      (edgeMeasure π).real (pairDisjSet o x y z)) :
    |(edgeMeasure π).real (pairDisjSet o x y z) -
        (edgeMeasure π).real (connSet o x) * (edgeMeasure π).real (connSet y z)| ≤
      (edgeMeasure π).real (pairAllSet o x y z) := by
  have hupper := edgeMeasure_gap_upper_real π hπ o x y z
  have hlower := edgeMeasure_gap_lower_real π hπ o x y z
  have hUD : (edgeMeasure π).real (pairDisjSet o x y z) ≤
      (edgeMeasure π).real (disjSet o x y z) :=
    real_measure_mono π (pairDisjSet_subset_disjSet o x y z)
  have hall : (edgeMeasure π).real (allConnSet o x y z) ≤
      (edgeMeasure π).real (pairAllSet o x y z) :=
    real_measure_mono π (allConnSet_subset_pairAllSet o x y z)
  rw [abs_le]
  constructor <;> linarith

end PercLib.CriticalLRP
