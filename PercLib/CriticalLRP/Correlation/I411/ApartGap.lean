/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
# Lemma I.4.12 with the source's gap event `apartSet` (the missing pointwise input of I.4.11)

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.12 and its proof (p. 39), and the display in the proof of
Lemma I.4.11 (p. 40).

## What was missing

`Correlation/TwoClusterGap.lean` proves Lemma I.4.12 with the *BK disjoint-occurrence* event
`disjSet o x y z = {0↔x} ∘ {y↔z}`.  The proof of Lemma I.4.11 subtracts instead the *source*
event `0↔x ↮ y↔z = apartSet o x y z = {x ∈ K_0} ∩ {y ∉ K_0} ∩ {z ∈ K_y}`, which is strictly
smaller (`I411.apartSet_subset_disjSet`, `I411.exists_disjSet_not_apartSet`).  A bound with
`disjSet` therefore does not give the bound with `apartSet`
(`I411.apartSet_gap_of_disjSet_gap` makes the resulting extra error term explicit), and
`I411.I411_step_of_twoClusterGapApart` has so far been conditional on the named hypothesis
`I411.TwoClusterGapApart`.

The printed proof of Lemma I.4.12 replaces the pair probability by a two-copy event and computes
`P(x ∈ K_0, z ∈ K̃_y \ K_y)`.  That computation is not literally correct (`K̃_y` is the cluster of
`y` in the *restored* configuration; the printed identity `P(x∈K_0, z∈K̃_y) = P(0↔x)P(y↔z)` fails,
see `Correlation/PrintedEventFails.lean` and the `not_cluster_subset_forceOn_compl` remark in
`Correlation/TwoClusterGap.lean`), but the *inequality* is nevertheless true and the coupling
argument can be repaired by one observation that the existing chain did not use.

## The repair

Keep the printed coupling: `ω̃ = restoreMap o (ω₂, ω₁) = forceOn (touchSet ω₁ o)ᶜ ω₂ ω₁`, i.e. the
base configuration `ω₁` is kept on every edge touching its cluster `K_0(ω₁)`, and the independent
copy `ω₂` is used off it.  The observation is

* `cluster_forceOn_compl_touchSet` (already in `CountableProduct/RestorationCompl.lean`):
  `K_0(ω̃) = K_0(ω₁)` *exactly* — the cluster of the origin is not enlarged by the resampling.

Now let `ω₂ ∈ {y↔z}` and `ω₁ ∈ {0↔x}`.  Either there is a walk `y → z` in `ω₂` avoiding
`K_0(ω₁)`, in which case

* `x ∈ K_0(ω̃) = K_0(ω₁)`,
* `y ∉ K_0(ω̃)` (the walk starts at `y` and avoids `K_0(ω₁)`),
* `z ∈ K_y(ω̃)` (the walk consists of edges off `touchSet ω₁ o`, hence of fresh `ω₂`-edges that
  survive into `ω̃`),

i.e. `ω̃ ∈ apartSet o x y z`; this is `apartSet_restoreMap`.  Or no such walk exists, and the
existing deterministic lemma `exists_fresh_disjOcc_of_no_avoid` produces `b ∈ K_0(ω₁)` with the
disjoint occurrence `y↔b ∘ b↔z` in `ω₂`.  Hence the exact covering

* `pairSet_subset_apart`:
  `{y↔z} × {0↔x} ⊆ restoreMap o ⁻¹' apartSet o x y z ∪ ⋃ b, disjSet y b b z × (0↔x ∩ 0↔b)`.

This is the only change with respect to the proof of `twoCluster_gap_le`; the rest of the chain
(product measure of the preimage = measure of `apartSet` via law preservation, BK, and the
two-leaf tree-graph inequality `twoLeaf_treeGraph`) is reused verbatim.

## Results

* `twoCluster_gap_apart` : Lemma I.4.12 *with the source's event*, with no remaining hypothesis
  for the canonical law `edgeMeasure π`, `π e < 1`:

  `P(0↔x) P(y↔z) ≤ P(0↔x ↮ y↔z) + ∑_a ∑_b P(0↔a) P(a↔x) P(a↔b) P(y↔b) P(b↔z)`.

* `twoClusterGapApart_edgeMeasure` : the named hypothesis `I411.TwoClusterGapApart
  (edgeMeasure π) o` is discharged.
* `longRange_twoClusterGapApart` : the same for the paper's law `P_β` (`β ≥ 0`, `J ≥ 0`).
* `I411_step_edgeMeasure` / `I411_step_longRange` : the display in the proof of Lemma I.4.11,
  with no remaining hypothesis, by feeding the above into
  `I411.I411_step_of_twoClusterGapApart`.

No `sorry`, no custom axioms, no hypothesis on the survival probability or on moment finiteness.
-/
module

public import PercLib.CriticalLRP.Correlation.I411.Basic
public import PercLib.CriticalLRP.Correlation.I411.DiagramAssembly

set_option autoImplicit true

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.I411

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. The deterministic half: the repaired coupling lands in `apartSet` -/

/-- **The restoration lands in the source's gap event.**  If the base configuration joins `o` to
`x` and the fresh configuration joins `y` to `z` by a walk avoiding the *base* cluster of `o`,
then the restored configuration `forceOn (touchSet ω₁ o)ᶜ ω₂ ω₁` satisfies
`x ∈ K_0`, `y ∉ K_0`, `z ∈ K_y` — i.e. it lies in `apartSet o x y z = {0↔x ↮ y↔z}`.

The proof uses `cluster_forceOn_compl_touchSet`: the restored configuration has exactly the base
cluster of `o`, so `y ∉ K_0` and `x ∈ K_0` are inherited from the avoidance hypothesis and `hx`,
while `z ∈ K_y` is witnessed by the walk, whose edges all lie off `touchSet ω₁ o` and hence are
fresh `ω₂`-edges. -/
theorem apartSet_restoreMap {ω₁ ω₂ : Config V} {o x y z : V}
    (hx : x ∈ cluster ω₁ o)
    (p : (⊤ : SimpleGraph V).Walk y z) (hp : ∀ e ∈ p.edges, e ∈ ω₂)
    (hav : ∀ v ∈ p.support, v ∉ cluster ω₁ o) :
    restoreMap o (ω₂, ω₁) ∈ apartSet o x y z := by
  have hy : y ∉ cluster ω₁ o := hav y (SimpleGraph.Walk.start_mem_support p)
  show forceOn (touchSet ω₁ o)ᶜ ω₂ ω₁ ∈ apartSet o x y z
  rw [apartSet_eq_cluster]
  refine ⟨?_, ?_, ?_⟩
  · rw [cluster_forceOn_compl_touchSet ω₂ ω₁ o]; exact hx
  · rw [cluster_forceOn_compl_touchSet ω₂ ω₁ o]; exact hy
  · refine (mem_cluster_forceOn_compl_iff (ω := ω₁) (ω' := ω₂) (o := o) (y := y) (z := z)
      hy).mpr ⟨p, hp, ?_⟩
    intro e he v hv
    exact hav v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩))

/-- **The exact covering of the two-copy event.**  For every pair `(ω₂, ω₁)` with `y↔z` in the
fresh copy `ω₂` and `0↔x` in the base copy `ω₁`, either the restored configuration lies in
`apartSet o x y z`, or the fresh copy already contains a disjoint occurrence `y↔b ∘ b↔z` with
`b ∈ K_0(ω₁)`.

This is the repaired replacement for the printed identity of Lemma I.4.12; the second alternative
is the existing `exists_fresh_disjOcc_of_no_avoid`. -/
theorem pairSet_subset_apart {o x y z : V} :
    pairSet o x y z ⊆ restoreMap o ⁻¹' apartSet o x y z ∪
      ⋃ b : V, (disjSet y b b z ×ˢ (connSet o x ∩ connSet o b)) := by
  rintro ⟨ω₂, ω₁⟩ ⟨h1, h2⟩
  by_cases hex : ∃ p : (⊤ : SimpleGraph V).Walk y z,
      (∀ e ∈ p.edges, e ∈ ω₂) ∧ (∀ v ∈ p.support, v ∉ cluster ω₁ o)
  · exact Or.inl (apartSet_restoreMap (mem_cluster_iff.mpr h2) hex.choose
      hex.choose_spec.1 hex.choose_spec.2)
  · obtain ⟨b, hbK, hb⟩ := exists_fresh_disjOcc_of_no_avoid h1 hex
    exact Or.inr (Set.mem_iUnion.mpr ⟨b, hb, h2, mem_cluster_iff.mp hbK⟩)

/-! ## 2. The measure-theoretic half (the same chain as `twoCluster_gap_le`, first term
replaced by `apartSet`) -/

/-- **Lemma I.4.12 with the source's event**, conditionally on BK in the fresh copy and the
two-leaf tree-graph inequality for the two connections from `o`:

  `τ(o,x) τ(y,z) ≤ P(o↔x ↮ y↔z) + ∑_a ∑_b τ(o,a) τ(a,x) τ(a,b) τ(y,b) τ(b,z)`.

Nothing else is used: the coupling, its law preservation, and the covering
`pairSet_subset_apart` are handled here. -/
theorem twoCluster_gap_le_apart (π : Sym2 V → unitInterval) (o x y z : V)
    (hTG : ∀ b : V, (edgeMeasure π) (connSet o x ∩ connSet o b)
      ≤ ∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b))
    (hBK : ∀ b : V, (edgeMeasure π) (disjSet y b b z)
      ≤ (edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z)) :
    (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z) ≤
      (edgeMeasure π) (apartSet o x y z) +
        ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
          * (edgeMeasure π) (connSet b z) := by
  classical
  -- the deterministic covering
  have hcover := pairSet_subset_apart (o := o) (x := x) (y := y) (z := z)
  -- (1) the two-copy probability is bounded by the two pieces
  have hmap : ((edgeMeasure π).prod (edgeMeasure π)) (restoreMap o ⁻¹' apartSet o x y z)
      = (edgeMeasure π) (apartSet o x y z) := by
    rw [← Measure.map_apply (measurable_restoreMap o) (measurableSet_apartSet o x y z)]
    exact congrArg (fun ν => ν (apartSet o x y z)) (map_restoreMap π o)
  have hstep1 : ((edgeMeasure π).prod (edgeMeasure π)) (pairSet o x y z) ≤
      (edgeMeasure π) (apartSet o x y z) +
        ∑' b : V, (edgeMeasure π) (disjSet y b b z)
          * (edgeMeasure π) (connSet o x ∩ connSet o b) := by
    refine le_trans (measure_mono hcover) ?_
    refine le_trans (measure_union_le _ _) (add_le_add (le_of_eq hmap) ?_)
    refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun b => ?_)
    exact le_of_eq (Measure.prod_prod _ _)
  -- (2) combine with BK and the tree-graph inequality
  have hstep2 : (∑' b : V, (edgeMeasure π) (disjSet y b b z)
        * (edgeMeasure π) (connSet o x ∩ connSet o b)) ≤
      ∑' b : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
        * (∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
            * (edgeMeasure π) (connSet a b)) :=
    ENNReal.tsum_le_tsum fun b => mul_le_mul' (hBK b) (hTG b)
  -- (3) reassociate into the paper's double sum
  have hstep3 : (∑' b : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
        * (∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
            * (edgeMeasure π) (connSet a b))) =
      ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
        * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
        * (edgeMeasure π) (connSet b z) := by
    have h1 : (∑' b : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
          * (∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
              * (edgeMeasure π) (connSet a b))) =
        ∑' b : V, ∑' a : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
          * ((edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
              * (edgeMeasure π) (connSet a b)) := by
      refine tsum_congr fun b => ?_
      rw [← ENNReal.tsum_mul_left]
    rw [h1, ENNReal.tsum_comm]
    exact tsum_congr fun a => tsum_congr fun b => mul_five_rearrange _ _ _ _ _
  calc (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z)
      = ((edgeMeasure π).prod (edgeMeasure π)) (pairSet o x y z) := by
        rw [measure_pairSet, mul_comm]
    _ ≤ (edgeMeasure π) (apartSet o x y z) +
          ∑' b : V, (edgeMeasure π) (disjSet y b b z)
            * (edgeMeasure π) (connSet o x ∩ connSet o b) := hstep1
    _ ≤ (edgeMeasure π) (apartSet o x y z) +
          ∑' b : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
            * (∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
                * (edgeMeasure π) (connSet a b)) := add_le_add le_rfl hstep2
    _ = (edgeMeasure π) (apartSet o x y z) +
          ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
            * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
            * (edgeMeasure π) (connSet b z) := by rw [hstep3]

/-! ## 3. Discharging BK and the tree-graph inequality -/

/-- **Lemma I.4.12 with the source's event, unconditionally** on the canonical law.  BK
(`bk_connSet_ennreal`) and the two-leaf tree-graph inequality (`twoLeaf_treeGraph`) are both
available for `edgeMeasure π` when `π e < 1` for every edge. -/
theorem twoCluster_gap_apart (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o x y z : V) :
    (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z) ≤
      (edgeMeasure π) (apartSet o x y z) +
        ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
          * (edgeMeasure π) (connSet b z) :=
  twoCluster_gap_le_apart π o x y z (fun b => twoLeaf_treeGraph π hπ o x b)
    (fun b => bk_connSet_ennreal π hπ y b b z)

/-- **Consistency with the existing `disjSet` form**: since `apartSet ⊆ disjSet`, the source-event
bound proved above implies the bound of `Correlation.TwoClusterGap.twoCluster_gap` (Lemma I.4.12
with the BK disjoint-occurrence event), which is therefore not lost. -/
theorem twoCluster_gap_of_apart (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o x y z : V) :
    (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z) ≤
      (edgeMeasure π) (disjSet o x y z) +
        ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
          * (edgeMeasure π) (connSet b z) := by
  refine le_trans (twoCluster_gap_apart π hπ o x y z) (add_le_add ?_ le_rfl)
  exact measure_mono (apartSet_subset_disjSet o x y z)

/-- **The named hypothesis `TwoClusterGapApart` is discharged** for the canonical law, for every
`π` with `π e < 1`.  Equivalently, Lemma I.4.12 holds in the exact form the proof of Lemma I.4.11
consumes. -/
theorem twoClusterGapApart_edgeMeasure (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (o : V) : TwoClusterGapApart (edgeMeasure π) o :=
  fun x y z => twoCluster_gap_apart π hπ o x y z

/-- **The named hypothesis `TwoClusterGapApart` is discharged for the paper's law `P_β`**
(`β ≥ 0`, `J ≥ 0`), via `π = 1 − exp(−β J)`. -/
theorem longRange_twoClusterGapApart (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (o : V) : TwoClusterGapApart (longRangeMeasure J hJ β) o :=
  twoClusterGapApart_edgeMeasure (bernoulliEdgeProb J hJ β)
    (fun e => bernoulliEdgeProb_lt_one hJ β e) o

/-! ## 4. The display in the proof of Lemma I.4.11, with no remaining hypothesis -/

/-- **The Lemma I.4.11 display**, unconditional on the canonical law: summing the gap inequality
over `y ∈ B` and over `x, z` gives

  `∑_{y∈B} ∑_{x,z} τ(0,x) τ(y,z) ≤ E[|K_0| ∑_{y∈B} 1(y∉K_0)|K_y|]
      + ∑_{y∈B} ∑_{x,z} ∑_{a,b} τ(0,a)τ(a,x)τ(a,b)τ(y,b)τ(b,z)`.

This is `I411_step_of_twoClusterGapApart` fed with the discharged hypothesis. -/
theorem I411_step_edgeMeasure (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o : V)
    (B : Finset V) :
    (∑ y ∈ B, ∑' x : V, ∑' z : V,
        (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z))
      ≤ exclMoment π o B +
        ∑ y ∈ B, ∑' x : V, ∑' z : V, gapDiagram (edgeMeasure π) o y x z :=
  I411_step_of_twoClusterGapApart (twoClusterGapApart_edgeMeasure π hπ o) B

/-- **The Lemma I.4.11 display for the paper's law `P_β`**, with no remaining hypothesis. -/
theorem I411_step_longRange (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (o : V)
    (B : Finset V) :
    (∑ y ∈ B, ∑' x : V, ∑' z : V,
        (longRangeMeasure J hJ β) (connSet o x) * (longRangeMeasure J hJ β) (connSet y z))
      ≤ exclMoment (bernoulliEdgeProb J hJ β) o B +
        ∑ y ∈ B, ∑' x : V, ∑' z : V,
          gapDiagram (longRangeMeasure J hJ β) o y x z :=
  I411_step_of_twoClusterGapApart (longRange_twoClusterGapApart J hJ β o) B

/-! ## 5. The paper's display in the proof of Lemma I.4.11, unconditionally on the lattice -/

/-- **The display in the proof of Lemma I.4.11** (paper p. 40, after Lemma I.4.12), with the
source's gap event and with *no* remaining hypothesis, for translation-invariant `J ≥ 0`:

  `∑_{y∈B} ∑_{x,z} τ(0,x) τ(y,z)`
  `  ≤ ∑_{y∈B} ∑_{x,z} P(0↔x ↮ y↔z) + (E|K_0|)² ∑_{y∈B} ∇(0,y)`,

where `∇(0,y) = ∑_{a,b} τ(0,a) τ(a,b) τ(b,y)`.

This composes the pointwise gap bound `twoCluster_gap_apart` with the five-factor assembly
`I411.sum_twoCluster_le_of_pointwise`; the only inputs are translation invariance and `J ≥ 0`.
Nothing is assumed about finiteness of `E|K_0|`: both sides are in `ℝ≥0∞`. -/
theorem I411_paper_display {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (B : Finset (Fin d → ℤ)) :
    (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 x * twoPointFunction J hJ β y z)
      ≤ (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
          (longRangeMeasure J hJ β) (apartSet 0 x y z))
        + (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
          * (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
          * (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
              twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
                * twoPointFunction J hJ β b y) :=
  sum_twoCluster_le_of_pointwise hJinv hJ β B
    (fun y x z => (longRangeMeasure J hJ β) (apartSet 0 x y z))
    (fun y _ x z => by
      simpa only [longRangeMeasure, twoPointFunction, connSet] using
        twoCluster_gap_apart (bernoulliEdgeProb J hJ β)
          (fun e => bernoulliEdgeProb_lt_one hJ β e) 0 x y z)

/-- **The paper's subtracted display in the proof of Lemma I.4.11**, with no remaining hypothesis:

  `|B| (E|K_0|)² − E[|K_0| ∑_{y∈B} 1(y∉K_0) |K_y|] ≤ (E|K_0|)² ∑_{y∈B} ∇(0,y)`,

where `E|K_0| = ∑_w τ(0,w) = ∫⁻ |K_0|` and `∇(0,y) = ∑_{a,b} τ(0,a)τ(a,b)τ(b,y)`.

The subtraction is `ENNReal.tsub`; when `E|K_0| = ⊤` the left side is `0` (no meaning is attached
to `⊤ - ⊤` beyond the `ℝ≥0∞` convention), and the inequality remains valid.  The two
identifications used are `I411.exclMoment_eq_tsum_apartSet` (the excluded moment is the `x,z`-sum
of the gap-event probabilities) and `sum_tsum_tsum_twoPoint_eq_card` (`|B| (E|K_0|)²` is the
`x,z`-sum of `τ(0,x)τ(y,z)`). -/
theorem I411_subtracted_display {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (B : Finset (Fin d → ℤ)) :
    (B.card : ℝ≥0∞)
        * ((∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
          * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w))
      - exclMoment (bernoulliEdgeProb J hJ β) 0 B
    ≤ ((∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
        * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w))
        * (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
            twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
              * twoPointFunction J hJ β b y) := by
  have hG : (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
      (longRangeMeasure J hJ β) (apartSet 0 x y z))
      = exclMoment (bernoulliEdgeProb J hJ β) 0 B := by
    simp only [longRangeMeasure]
    exact (exclMoment_eq_tsum_apartSet (bernoulliEdgeProb J hJ β) 0 B).symm
  rw [← sum_tsum_tsum_twoPoint_eq_card hJinv hJ β B]
  refine (tsub_le_iff_right).mpr ?_
  rw [add_comm]
  have h := I411_paper_display hJinv hJ β B
  rw [hG, lintegral_clusterVol_eq_tsum_twoPoint hJ β 0] at h
  exact h

end PercLib.CriticalLRP.I411
