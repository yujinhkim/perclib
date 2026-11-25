/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The simple two-cluster covariance-gap bound (`lem:disjoint_connections`), unconditionally

Source: `.scratch/i52/source/Zd_renormalizationHD.tex`, Lemma `lem:disjoint_connections`
(lines 952-960): for Bernoulli bond percolation on a weighted graph `G = (V,E,J)` with
`β ≥ 0`,

  `0 ≤ P_β(x↔y) P_β(z↔w) − P_β(x↔y ↮ z↔w) ≤ P_β(x↔y↔z↔w)`   for all `x,y,z,w ∈ V`,

where `x↔y ↮ z↔w` is the **disjoint occurrence** of the two connection events (§I.2.1) and
`x↔y↔z↔w` is the event that all four points lie in one cluster.  The paper derives it from
the second display of `lem:BK_disjoint_clusters_covariance`:

*
  `E[F G] − E F · E G ≤ E[F G 1(x↔y)]`,

with `F = 1{x↔y}`, `G = 1{z↔w}`, and `1 = 1(x↔z) + 1(x↮z)`: Harris–FKG bounds the covariance
from below by `0`, and BK bounds `E[F G 1(x↮z)]` from above by `E F · E G`.

**What is proved here, and in which model.**  Everything below is about the *canonical*
countable product bond model of `CountableProduct/Base.lean`: `V` is a countable vertex type,
`Config V = Set (Sym2 V)`, `edgeMeasure π` is the independent bond measure with edge open
probability `π e` (`edgeMeasure_eq_edgeLaw`), and `connSet`/`disjSet`/`allConnSet` are the
canonical events of `BK/CanonicalBridge.lean`.  No abstract weighted model is used, and no
hypothesis is assumed other than `π e < 1` (the standing hypothesis of BK in this repository;
it holds for the paper's law `P_β` because `π e = 1 − e^{−β J e} < 1`).

Main results:

* `allConn_of_not_disjOcc` — the deterministic core, which is where the paper's prose
  "`1 = 1(x↔z) + 1(x↮z)`" is paid for: if `x ↔ y` and `z ↔ w` hold but **not** disjointly,
  then the two open paths must share an edge, and consequently all four points are in one
  cluster.  This is the only place where an argument (rather than an inequality) is needed.
* `connSet_inter_subset_disjSet_union` — the set inclusion
  `{x↔y} ∩ {z↔w} ⊆ {x↔y ↮ z↔w} ∪ {x↔y↔z↔w}`, the exact deterministic input of the
  covariance step.
* `edgeMeasure_gap_ennreal`, `edgeMeasure_gap_upper_real` — the upper half of the gap bound
  `P(x↔y)P(z↔w) − P(x↔y ↮ z↔w) ≤ P(x↔y↔z↔w)` (Harris–FKG + the inclusion).
* `edgeMeasure_gap_lower_real` — the lower half `0 ≤ P(x↔y)P(z↔w) − P(x↔y ↮ z↔w)`, which is
  BK and is already available as `bk_connSet_ennreal`; it is restated in real form here so
  that the two-sided statement is self-contained.
* `edgeMeasure_gap` — the paper's display verbatim, as a two-sided absolute-value bound.
* `longRangeMeasure_gap` — the same for the paper's law `P_β`.

Relation to `VolumeMoments/I58Cross.lean`.  The per-pair hypothesis `hgap` there is stated for
the *abstract* finite weighted model: `pairDisj` is `E[1(y∉K) 1(x∈K) 1(z∈K_y)]` with `K_y` the
restored cluster, `pairAll` is `E[1(x∈K)1(y∈K)1(z∈K)]` and `pairProd` is the product of the two
two-point functions.  The inequality proved here is the paper's own disjoint-occurrence form of
the bound.  Passing from this statement to `I58Cross`'s `pairDisj` additionally needs the
restoration identification `P(x∈K_0, y∉K_0, z∈K_y) = P(0↔x ↮ y↔z)` of §I.2.1, whose repaired
chain is `Correlation/TwoClusterGap.lean` + `Correlation/SelfRestoration.lean`; that
identification is **not** proved here.  See `HgapReport.md` for the exact accounting.
-/
module

public import PercLib.CriticalLRP.Correlation.TwoClusterGap

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. The deterministic two-path overlap lemma -/

/-- **If two connections are not disjoint, the four points are connected.**

Let `ω` be a bond configuration in which `x ↔ y` and `z ↔ w`.  If the two connection events do
not occur on edge-disjoint sets of open edges, then some open `x`–`y` path and some open `z`–`w`
path share an edge `e = {u,v}`; both `u` and `v` lie on both paths, so `x`, `y`, `z`, `w` all lie
in the cluster of `u`.  In particular `y ↔ z`.

This is the deterministic content behind `1(x↮z) = 1 − 1(x↔z)` in the paper's proof of
`lem:disjoint_connections`; it is *not* an instance of monotonicity, and it is where the
hypothesis that the two connections are taken disjointly is used. -/
theorem allConn_of_not_disjOcc {ω : Config V} {x y z w : V}
    (hxy : Connects ω x y) (hzw : Connects ω z w) (hnd : ω ∉ disjSet x y z w) :
    Connects ω y z := by
  classical
  -- open walks witnessing the two connections
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr hxy
  obtain ⟨q, hq⟩ := pathConnects_iff.mpr hzw
  -- the two walks must share an open edge, otherwise they would witness `disjSet`
  have hshare : ∃ e : Sym2 V, e ∈ p.edges ∧ e ∈ q.edges := by
    by_contra hcon
    apply hnd
    refine ⟨p.edges.toFinset, q.edges.toFinset, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      exact hp e (List.mem_toFinset.mp he)
    · intro e he
      exact hq e (List.mem_toFinset.mp he)
    · refine Finset.disjoint_left.mpr ?_
      intro e hep heq
      exact hcon ⟨e, List.mem_toFinset.mp hep, List.mem_toFinset.mp heq⟩
    · show Connects (p.edges.toFinset : Set (Sym2 V)) x y
      exact pathConnects_iff.mp ⟨p, fun e he => List.mem_toFinset.mpr he⟩
    · show Connects (q.edges.toFinset : Set (Sym2 V)) z w
      exact pathConnects_iff.mp ⟨q, fun e he => List.mem_toFinset.mpr he⟩
  obtain ⟨e, hep, heq⟩ := hshare
  obtain ⟨u, v, huv⟩ : ∃ u v : V, e = s(u, v) := by
    induction e using Sym2.ind with
    | h u v => exact ⟨u, v, rfl⟩
  subst huv
  -- a common endpoint `u` of the shared edge lies on both walks
  have hu_p : u ∈ p.support := p.mem_support_of_mem_edges hep (Sym2.mem_mk_left u v)
  have hu_q : u ∈ q.support := q.mem_support_of_mem_edges heq (Sym2.mem_mk_left u v)
  have hxu : Connects ω x u := mem_cluster_iff.mp (mem_cluster_of_mem_support p hp u hu_p)
  have hzu : Connects ω z u := mem_cluster_iff.mp (mem_cluster_of_mem_support q hq u hu_q)
  exact connects_trans (connects_symm hxy) (connects_trans hxu (connects_symm hzu))

/-- The deterministic input of the covariance step, as a set inclusion:

`{x↔y} ∩ {z↔w} ⊆ {x↔y ↮ z↔w} ∪ {x↔y↔z↔w}`.

Consequence: `P(x↔y, z↔w) ≤ P(x↔y ↮ z↔w) + P(x↔y↔z↔w)` with no measurability input, and
hence, together with Harris–FKG, the upper half of `lem:disjoint_connections`. -/
theorem connSet_inter_subset_disjSet_union (x y z w : V) :
    connSet x y ∩ connSet z w ⊆ disjSet x y z w ∪ allConnSet x y z w := by
  intro ω hω
  by_cases hd : ω ∈ disjSet x y z w
  · exact Or.inl hd
  · exact Or.inr ⟨hω.1, allConn_of_not_disjOcc hω.1 hω.2 hd, hω.2⟩

/-- The four-point event `x↔y↔z↔w` is measurable (so that it is a genuine event with a
probability). -/
theorem measurableSet_allConnSet (x y z w : V) : MeasurableSet (allConnSet x y z w) :=
  (measurableSet_connSet x y).inter
    ((measurableSet_connSet y z).inter (measurableSet_connSet z w))

/-- The disjoint-occurrence event is contained in both connection events. -/
theorem disjSet_subset_connSet_inter (x y z w : V) :
    disjSet x y z w ⊆ connSet x y ∩ connSet z w := by
  rintro ω ⟨s, t, hs, ht, -, hsa, htb⟩
  exact ⟨connects_mono (fun e he => hs he) hsa, connects_mono (fun e he => ht he) htb⟩

/-! ## 2. The gap bound in the canonical product model -/

/-- **The upper half of `lem:disjoint_connections`, `ℝ≥0∞` form**:

`P(x↔y) P(z↔w) ≤ P(x↔y ↮ z↔w) + P(x↔y↔z↔w)`.

Harris–FKG gives `P(x↔y)P(z↔w) ≤ P(x↔y, z↔w)`; the deterministic inclusion
`connSet_inter_subset_disjSet_union` splits the right-hand side.  No measurability of the
inclusion step is used (`measure_mono` and `measure_union_le` are valid for arbitrary sets). -/
theorem edgeMeasure_gap_ennreal (π : Sym2 V → unitInterval) (_hπ : ∀ e, π e < 1)
    (x y z w : V) :
    (edgeMeasure π) (connSet x y) * (edgeMeasure π) (connSet z w) ≤
      (edgeMeasure π) (disjSet x y z w) + (edgeMeasure π) (allConnSet x y z w) := by
  -- Harris--FKG, transported to `ℝ≥0∞`
  have hfkg := edgeMeasure_fkg π (connSet x y) (connSet z w) (isUpper_connSet x y)
    (isUpper_connSet z w) (finiteWitness_connSet x y) (finiteWitness_connSet z w)
  have hfinA : (edgeMeasure π) (connSet x y) * (edgeMeasure π) (connSet z w) ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hfkg' : (edgeMeasure π) (connSet x y) * (edgeMeasure π) (connSet z w) ≤
      (edgeMeasure π) (connSet x y ∩ connSet z w) := by
    refine (ENNReal.toReal_le_toReal hfinA (measure_ne_top _ _)).mp ?_
    rw [ENNReal.toReal_mul]
    exact hfkg
  exact hfkg'.trans ((measure_mono (connSet_inter_subset_disjSet_union x y z w)).trans
    (measure_union_le _ _))

/-- **The upper half of `lem:disjoint_connections`, real form**:

`P(x↔y) P(z↔w) − P(x↔y ↮ z↔w) ≤ P(x↔y↔z↔w)`. -/
theorem edgeMeasure_gap_upper_real (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y z w : V) :
    (edgeMeasure π).real (connSet x y) * (edgeMeasure π).real (connSet z w) ≤
      (edgeMeasure π).real (disjSet x y z w) + (edgeMeasure π).real (allConnSet x y z w) := by
  have h := edgeMeasure_gap_ennreal π hπ x y z w
  have hfin : (edgeMeasure π) (connSet x y) * (edgeMeasure π) (connSet z w) ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hfin2 : (edgeMeasure π) (disjSet x y z w) + (edgeMeasure π) (allConnSet x y z w) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  calc (edgeMeasure π).real (connSet x y) * (edgeMeasure π).real (connSet z w)
      = ((edgeMeasure π) (connSet x y) * (edgeMeasure π) (connSet z w)).toReal := by
        rw [ENNReal.toReal_mul]; rfl
    _ ≤ ((edgeMeasure π) (disjSet x y z w) + (edgeMeasure π) (allConnSet x y z w)).toReal :=
        (ENNReal.toReal_le_toReal hfin hfin2).mpr h
    _ = (edgeMeasure π).real (disjSet x y z w) + (edgeMeasure π).real (allConnSet x y z w) := by
        rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]; rfl

/-- **The lower half of `lem:disjoint_connections`, real form**:
`P(x↔y ↮ z↔w) ≤ P(x↔y) P(z↔w)`.  This is BK (`bk_connSet_ennreal`). -/
theorem edgeMeasure_gap_lower_real (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y z w : V) :
    (edgeMeasure π).real (disjSet x y z w) ≤
      (edgeMeasure π).real (connSet x y) * (edgeMeasure π).real (connSet z w) := by
  have h := bk_connSet_ennreal π hπ x y z w
  have hfin : (edgeMeasure π) (connSet x y) * (edgeMeasure π) (connSet z w) ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  calc (edgeMeasure π).real (disjSet x y z w)
      ≤ ((edgeMeasure π) (connSet x y) * (edgeMeasure π) (connSet z w)).toReal :=
        (ENNReal.toReal_le_toReal (measure_ne_top _ _) hfin).mpr h
    _ = (edgeMeasure π).real (connSet x y) * (edgeMeasure π).real (connSet z w) := by
        rw [ENNReal.toReal_mul]; rfl

/-- **`lem:disjoint_connections`, the paper's display, verbatim.**

`|P(x↔y ↮ z↔w) − P(x↔y) P(z↔w)| ≤ P(x↔y↔z↔w)`.

Both halves are unconditional in the canonical model (only `π e < 1`, the BK hypothesis, is
assumed): the lower half is BK, the upper half is Harris–FKG together with the deterministic
two-path overlap lemma.  Compare `twoCluster_gap_le` (`Correlation/TwoClusterGap.lean`), which is
the *different*, tree-graph-refined additive form of Lemma I.4.12 and still carries the two-leaf
tree-graph inequality as a hypothesis; the bound here needs no tree-graph input. -/
theorem edgeMeasure_gap (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y z w : V) :
    |(edgeMeasure π).real (disjSet x y z w) -
        (edgeMeasure π).real (connSet x y) * (edgeMeasure π).real (connSet z w)| ≤
      (edgeMeasure π).real (allConnSet x y z w) := by
  have hupper := edgeMeasure_gap_upper_real π hπ x y z w
  have hlower := edgeMeasure_gap_lower_real π hπ x y z w
  have hnonneg : (0 : ℝ) ≤ (edgeMeasure π).real (allConnSet x y z w) :=
    ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-! ## 3. The paper's law `P_β` -/

/-- **`lem:disjoint_connections` for the law `P_β` of §I.1.2** (`β ≥ 0`, `J ≥ 0`). -/
theorem longRangeMeasure_gap (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y z w : V) :
    |(longRangeMeasure J hJ β).real (disjSet x y z w) -
        (longRangeMeasure J hJ β).real (connSet x y) *
          (longRangeMeasure J hJ β).real (connSet z w)| ≤
      (longRangeMeasure J hJ β).real (allConnSet x y z w) :=
  edgeMeasure_gap (bernoulliEdgeProb J hJ β) (fun e => bernoulliEdgeProb_lt_one hJ β e) x y z w

end PercLib.CriticalLRP
