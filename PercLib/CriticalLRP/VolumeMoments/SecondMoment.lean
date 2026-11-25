/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
# The second cluster moment: the tree-graph factorisation and the cubic mean-field bound

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.2.1 (the two-leaf tree-graph inequality, equation (I.2.1)) and,
within §I.4.2, **only** the `p = 2`, `k = 0` instance of Lemma I.4.16 (equivalently,
equation (I.2.3) at `p = 2`).  This module does not prove the full Lemma I.4.16,
the higher-moment instances used in §I.4.2, or the surrounding ODE estimates.

## What is proved here

For the native countable product law `edgeMeasure π` on `Config V = Sym2 V → Prop`
(`V` an arbitrary countable type) this file proves, in `ℝ≥0∞` and with no finiteness
hypothesis anywhere:

* `lintegral_clusterVol_mul_clusterVol` — `∫⁻ |K_v| |K_w| = ∑_x ∑_y P(v↔x, w↔y)`;
* `tsum_tsum_measure_inter_le` — the tree-graph (I.2.1) factorisation
  `∑_x ∑_y P(o↔x, o↔y) ≤ ∑_a τ(o,a) (∑_x τ(a,x))²`, from `twoLeaf_treeGraph`;
* `lintegral_clusterVol_sq_le_tsum` — the resulting unconditional bound
  `∫⁻ |K_o|² ≤ ∑_a τ(o,a) (∫⁻ |K_a|)²`;

and then, **under the homogeneity hypothesis that the expected cluster volume does not
increase when the root is moved**, `∀ a, ∫⁻ |K_a| ≤ ∫⁻ |K_o|`,

* `lintegral_clusterVol_sq_le_cube` — the cubic mean-field bound
  `∫⁻ |K_o|² ≤ (∫⁻ |K_o|)² · (∫⁻ |K_o|) = (∫⁻ |K_o|)³`
  (and `..._pow`, literally `∫⁻ |K_o|^2 ≤ (∫⁻ |K_o|)^3`);
* `lintegral_clusterVol_sq_ne_top` — a finite first moment forces a finite second moment.

The homogeneity hypothesis is *not* a paper hypothesis: it is supplied by translation
invariance on the lattice.  Accordingly the last section proves it for `V = Fin d → ℤ` and
shift-invariant `π` (`lintegral_clusterVol_shift_invariant`, from the repository's
`edgeMeasure_shift_invariant`) and concludes

* `lintegral_clusterVol_sq_le_cube_lattice` — `∫⁻ |K_o|² ≤ (∫⁻ |K_o|)³` for every
  vertex `o` and every shift-invariant `π` with `π e < 1` on `Z^d`;
* `longRange_lintegral_clusterVol_sq_le_cube` — the same for the paper's law `P_β`, i.e.
  `π e = 1 - exp(-β J e)` with a translation-invariant kernel `J`.

## What is *not* true, and why the hypothesis is needed

The literal statement on an arbitrary countable vertex set, without homogeneity, is **false**:
the tree-graph route gives only `∑_a τ(o,a) S(a)²` with `S(a) = ∫⁻ |K_a|`, and on an
inhomogeneous graph a leaf of a hub can have a much larger expected cluster volume than the
root.  A concrete counterexample (a two-level star: `0—1` open with probability `1/10`, vertex
`1` joined to ten leaves with probability `1/2`, all other edges closed and all edges
independent) has
`E|K_0| = 8/5` and `E|K_0|² = 121/20 > 512/125 = (8/5)³`.  Indeed, if `X` is the
indicator of the root edge and `N ~ Bin(10, 1/2)` is independent of `X`, then
`|K_0| = 1 + X(1+N)`, `E N = 5`, `E N² = 55/2`, so
`E|K_0| = 1 + (1/10)(1+E N) = 8/5` and
`E|K_0|² = 1 + 2·(1/10)(1+E N) + (1/10)(1+2E N+E N²) = 121/20`.
The paper never needs the inhomogeneous case: its law is translation invariant.

No `sorry`, no custom axioms; every step is `ℝ≥0∞`-valued so infinite clusters and infinite
moments never require a subtraction.
-/
module

public import PercLib.CriticalLRP.Correlation.I411.Basic
public import PercLib.CriticalLRP.Correlation.Susceptibility
public import PercLib.CriticalLRP.CountableProduct.Lattice
public import PercLib.CriticalLRP.VolumeMoments.ErrorBounds

set_option autoImplicit true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Product of cluster volumes as a double sum.**  `|K_v| |K_w|` integrated against the
native product law is the double sum of the probabilities of the intersections
`{v ↔ x} ∩ {w ↔ y}`.  No finiteness is assumed: everything is `ℝ≥0∞`. -/
theorem lintegral_clusterVol_mul_clusterVol (π : Sym2 V → unitInterval) (v w : V) :
    ∫⁻ ω, clusterVol ω v * clusterVol ω w ∂(edgeMeasure π)
      = ∑' x : V, ∑' y : V, (edgeMeasure π) (connSet v x ∩ connSet w y) := by
  have key : ∀ (ω : Config V) (s : V) (x : V),
      (cluster ω s).indicator (fun _ => (1 : ℝ≥0∞)) x
        = (connSet s x).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω s x
    by_cases hx : x ∈ cluster ω s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem
        (by simpa [connSet, mem_cluster_iff] using hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem
        (by simpa [connSet, mem_cluster_iff] using hx)]
  have hpt : ∀ ω : Config V, clusterVol ω v * clusterVol ω w
      = ∑' x : V, ∑' y : V,
          (connSet v x ∩ connSet w y).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [I411.clusterVol_mul_clusterVol]
    refine tsum_congr fun x => tsum_congr fun y => ?_
    rw [key ω v x, key ω w y]
    by_cases h1 : ω ∈ connSet v x <;> by_cases h2 : ω ∈ connSet w y <;>
      simp [Set.indicator, h1, h2]
  simp only [hpt]
  rw [lintegral_tsum]
  · refine tsum_congr fun x => ?_
    rw [lintegral_tsum]
    · exact tsum_congr fun y =>
        lintegral_indicator_one ((measurableSet_connSet v x).inter (measurableSet_connSet w y))
    · intro y
      exact (measurable_const.indicator
        ((measurableSet_connSet v x).inter (measurableSet_connSet w y))).aemeasurable
  · intro x
    exact (Measurable.tsum fun y => measurable_const.indicator
      ((measurableSet_connSet v x).inter (measurableSet_connSet w y))).aemeasurable

/-- **Tree-graph factorisation of the double intersection sum.** -/
theorem tsum_tsum_measure_inter_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o : V) :
    ∑' x : V, ∑' y : V, (edgeMeasure π) (connSet o x ∩ connSet o y)
      ≤ ∑' a : V, (edgeMeasure π) (connSet o a) *
          (∑' x : V, (edgeMeasure π) (connSet a x)) *
          (∑' y : V, (edgeMeasure π) (connSet a y)) := by
  calc ∑' x : V, ∑' y : V, (edgeMeasure π) (connSet o x ∩ connSet o y)
      ≤ ∑' x : V, ∑' y : V, ∑' a : V,
          (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
            * (edgeMeasure π) (connSet a y) :=
        ENNReal.tsum_le_tsum fun x =>
          ENNReal.tsum_le_tsum fun y => twoLeaf_treeGraph π hπ o x y
    _ = ∑' a : V, ∑' x : V, ∑' y : V,
          (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
            * (edgeMeasure π) (connSet a y) := by
        rw [show (∑' x : V, ∑' y : V, ∑' a : V,
              (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
                * (edgeMeasure π) (connSet a y))
            = ∑' x : V, ∑' a : V, ∑' y : V,
              (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
                * (edgeMeasure π) (connSet a y) from
          tsum_congr fun x => ENNReal.tsum_comm]
        exact ENNReal.tsum_comm
    _ = ∑' a : V, (edgeMeasure π) (connSet o a) *
          (∑' x : V, (edgeMeasure π) (connSet a x)) *
          (∑' y : V, (edgeMeasure π) (connSet a y)) := by
        refine tsum_congr fun a => ?_
        rw [show (∑' x : V, ∑' y : V,
              (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
                * (edgeMeasure π) (connSet a y))
            = ∑' x : V, ((edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x))
                * (∑' y : V, (edgeMeasure π) (connSet a y)) from
          tsum_congr fun x => ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

/-- **Unconditional tree-graph bound on the second cluster moment.** -/
theorem lintegral_clusterVol_sq_le_tsum (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (o : V) :
    ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π)
      ≤ ∑' a : V, (edgeMeasure π) (connSet o a) *
          (∫⁻ ω, clusterVol ω a ∂(edgeMeasure π)) *
          (∫⁻ ω, clusterVol ω a ∂(edgeMeasure π)) := by
  rw [lintegral_clusterVol_mul_clusterVol]
  refine le_trans (tsum_tsum_measure_inter_le π hπ o) ?_
  exact ENNReal.tsum_le_tsum fun a => by
    rw [lintegral_clusterVol_eq_tsum_connSet π a]

/-- A product of cluster volumes is bounded pointwise by the sum of the two
squares, also in expectation. -/

theorem lintegral_clusterVol_mul_le_add_sq (π : Sym2 V → unitInterval) (v w : V) :
    ∫⁻ ω, clusterVol ω v * clusterVol ω w ∂(edgeMeasure π) ≤
      (∫⁻ ω, clusterVol ω v * clusterVol ω v ∂(edgeMeasure π)) +
        ∫⁻ ω, clusterVol ω w * clusterVol ω w ∂(edgeMeasure π) := by
  calc
    _ ≤ ∫⁻ ω, clusterVol ω v * clusterVol ω v +
          clusterVol ω w * clusterVol ω w ∂(edgeMeasure π) := by
      refine lintegral_mono fun ω => ?_
      rcases le_total (clusterVol ω v) (clusterVol ω w) with h | h
      · calc
          clusterVol ω v * clusterVol ω w ≤ clusterVol ω w * clusterVol ω w := by gcongr
          _ ≤ _ := self_le_add_left _ _
      · calc
          clusterVol ω v * clusterVol ω w ≤ clusterVol ω v * clusterVol ω v := by gcongr
          _ ≤ _ := self_le_add_right _ _
    _ = _ := lintegral_add_left ((measurable_clusterVol v).mul (measurable_clusterVol v)) _

/-- A finite joint window moment is dominated by the finite family of second
moments at the root and at the sites of the window. -/

theorem joint_windowMoment_le_sum_second_moments (π : Sym2 V → unitInterval)
    (o : V) (B : Finset V) :
    (∫⁻ ω, Percolation.cardFun (cluster ω o) *
        ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) ≤
      ∑ y ∈ B, ((∫⁻ ω, Percolation.cardFun (cluster ω o) *
          Percolation.cardFun (cluster ω o) ∂(edgeMeasure π)) +
        ∫⁻ ω, Percolation.cardFun (cluster ω y) *
          Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) := by
  rw [Hrest.lintegral_joint_cardFun_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  simpa only [Percolation.cardFun_eq_encard] using
    lintegral_clusterVol_mul_le_add_sq π o y

/-- **Cubic second-moment bound under homogeneity of the expected volume.** -/
theorem lintegral_clusterVol_sq_le_cube (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (o : V)
    (hS : ∀ a : V, (∫⁻ ω, clusterVol ω a ∂(edgeMeasure π))
      ≤ (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π))) :
    ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π)
      ≤ (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π))
          * (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π))
          * (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) := by
  set S : ℝ≥0∞ := ∫⁻ ω, clusterVol ω o ∂(edgeMeasure π) with hSdef
  refine le_trans (lintegral_clusterVol_sq_le_tsum π hπ o) ?_
  calc ∑' a : V, (edgeMeasure π) (connSet o a) *
        (∫⁻ ω, clusterVol ω a ∂(edgeMeasure π)) *
        (∫⁻ ω, clusterVol ω a ∂(edgeMeasure π))
      ≤ ∑' a : V, (edgeMeasure π) (connSet o a) * S * S :=
        ENNReal.tsum_le_tsum fun a => by gcongr <;> exact hS a
    _ = (∑' a : V, (edgeMeasure π) (connSet o a)) * S * S := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    _ = S * S * S := by
        rw [← lintegral_clusterVol_eq_tsum_connSet π o, hSdef]

/-- Finiteness of the second moment as a *conclusion* of a finite first moment. -/
theorem lintegral_clusterVol_sq_ne_top (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (o : V)
    (hS : ∀ a : V, (∫⁻ ω, clusterVol ω a ∂(edgeMeasure π))
      ≤ (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)))
    (hfin : (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ≠ ⊤) :
    ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_clusterVol_sq_le_cube π hπ o hS)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hfin hfin) hfin

/-- The cubic bound in the literal power notation `∫⁻ |K_o|² ≤ (∫⁻ |K_o|)³`. -/
theorem lintegral_clusterVol_sq_le_cube_pow (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (o : V)
    (hS : ∀ a : V, (∫⁻ ω, clusterVol ω a ∂(edgeMeasure π))
      ≤ (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π))) :
    ∫⁻ ω, clusterVol ω o ^ 2 ∂(edgeMeasure π)
      ≤ (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ^ 3 := by
  simpa only [pow_two, pow_three, mul_assoc] using lintegral_clusterVol_sq_le_cube π hπ o hS

/-! ## The lattice case: translation invariance supplies the homogeneity -/

section Lattice

variable {d : ℕ}

/-- Translating the configuration moves the cluster volume accordingly. -/
theorem clusterVol_shiftConfig (a : Fin d → ℤ) (ω : Config (Fin d → ℤ)) (v : Fin d → ℤ) :
    clusterVol (shiftConfig a ω) (v + a) = clusterVol ω v := by
  rw [clusterVol_eq_encard, clusterVol_eq_encard, cluster_shiftConfig]
  congr 1
  exact Function.Injective.encard_image (fun x y h => add_right_cancel h) (cluster ω v)

/-- **The expected cluster volume is translation invariant** for a translation-invariant edge
probability. -/
theorem lintegral_clusterVol_shift_invariant (π : Sym2 (Fin d → ℤ) → unitInterval)
    (hπinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (v : Fin d → ℤ) :
    (∫⁻ ω, clusterVol ω v ∂(edgeMeasure π))
      = (∫⁻ ω, clusterVol ω 0 ∂(edgeMeasure π)) := by
  have hinv : (edgeMeasure π).map (shiftConfig (-v)) = edgeMeasure π :=
    edgeMeasure_shift_invariant π hπinv (-v)
  calc (∫⁻ ω, clusterVol ω v ∂(edgeMeasure π))
      = ∫⁻ ω, clusterVol (shiftConfig (-v) ω) (v + -v) ∂(edgeMeasure π) :=
        lintegral_congr fun ω => (clusterVol_shiftConfig (-v) ω v).symm
    _ = ∫⁻ ω, clusterVol (shiftConfig (-v) ω) 0 ∂(edgeMeasure π) := by simp
    _ = ∫⁻ ω, clusterVol ω 0 ∂((edgeMeasure π).map (shiftConfig (-v))) :=
        (lintegral_map (measurable_clusterVol 0) (measurable_shiftConfig (-v))).symm
    _ = ∫⁻ ω, clusterVol ω 0 ∂(edgeMeasure π) := by rw [hinv]

/-- **Second-moment bound on the lattice.** -/
theorem lintegral_clusterVol_sq_le_cube_lattice (π : Sym2 (Fin d → ℤ) → unitInterval)
    (hπ : ∀ e, π e < 1)
    (hπinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (o : Fin d → ℤ) :
    ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π)
      ≤ (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π))
          * (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π))
          * (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) := by
  refine lintegral_clusterVol_sq_le_cube π hπ o fun a => ?_
  rw [lintegral_clusterVol_shift_invariant π hπinv a,
    lintegral_clusterVol_shift_invariant π hπinv o]

/-- The lattice bound in the literal power notation. -/
theorem lintegral_clusterVol_sq_le_cube_lattice_pow (π : Sym2 (Fin d → ℤ) → unitInterval)
    (hπ : ∀ e, π e < 1)
    (hπinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (o : Fin d → ℤ) :
    ∫⁻ ω, clusterVol ω o ^ 2 ∂(edgeMeasure π)
      ≤ (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ^ 3 :=
  lintegral_clusterVol_sq_le_cube_pow π hπ o fun a => by
    rw [lintegral_clusterVol_shift_invariant π hπinv a,
      lintegral_clusterVol_shift_invariant π hπinv o]

/-- **The paper's law `P_β`**: second-moment bound for a translation-invariant kernel. -/
theorem longRange_lintegral_clusterVol_sq_le_cube {d : ℕ} (J : Sym2 (Fin d → ℤ) → ℝ)
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (o : Fin d → ℤ) :
    ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(longRangeMeasure J hJ β)
      ≤ (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ β))
          * (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ β))
          * (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ β)) := by
  have h := lintegral_clusterVol_sq_le_cube_lattice (bernoulliEdgeProb J hJ β)
    (bernoulliEdgeProb_lt_one hJ β) (bernoulliEdgeProb_shift hJinv hJ β) o
  simpa only [longRangeMeasure] using h

/-- The paper's law, in the literal power notation. -/
theorem longRange_lintegral_clusterVol_sq_le_cube_pow {d : ℕ} (J : Sym2 (Fin d → ℤ) → ℝ)
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (o : Fin d → ℤ) :
    ∫⁻ ω, clusterVol ω o ^ 2 ∂(longRangeMeasure J hJ β)
      ≤ (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ β)) ^ 3 := by
  have h := lintegral_clusterVol_sq_le_cube_lattice_pow (bernoulliEdgeProb J hJ β)
    (bernoulliEdgeProb_lt_one hJ β) (bernoulliEdgeProb_shift hJinv hJ β) o
  simpa only [longRangeMeasure] using h

/-- A finite first cluster-volume moment at a lattice vertex forces a finite second
moment.  The cubic bound makes the upper tail finite without any additional premise
beyond finiteness of the first moment.  This is not an all-higher-moments statement. -/
theorem latticeLongRange_lintegral_clusterVol_sq_ne_top {d : ℕ} (α : ℝ) (β : NNReal)
    (o : Fin d → ℤ)
    (hfirst : (∫⁻ ω, clusterVol ω o ∂(latticeLongRangeMeasure d α β)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(latticeLongRangeMeasure d α β)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (longRange_lintegral_clusterVol_sq_le_cube
    (lrKernel d α) (lrKernel_shift_invariant d α) (lrKernel_nonneg d α) β o)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hfirst hfirst) hfirst

/-- The finite-second-moment corollary in the standard `|K|^2` notation. -/
theorem latticeLongRange_lintegral_clusterVol_pow_two_ne_top {d : ℕ} (α : ℝ) (β : NNReal)
    (o : Fin d → ℤ)
    (hfirst : (∫⁻ ω, clusterVol ω o ∂(latticeLongRangeMeasure d α β)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o ^ 2 ∂(latticeLongRangeMeasure d α β)) ≠ ⊤ := by
  simpa only [pow_two] using latticeLongRange_lintegral_clusterVol_sq_ne_top α β o hfirst

#print axioms latticeLongRange_lintegral_clusterVol_sq_ne_top
#print axioms latticeLongRange_lintegral_clusterVol_pow_two_ne_top

/-- **The paper's law on `Z^d`**, `J(x,y) = ‖x - y‖^{-d-α}` (Definition I.1.3): the second
cluster moment is at most the cube of the first. -/
theorem latticeLongRange_lintegral_clusterVol_sq_le_cube_pow {d : ℕ} (α : ℝ) (β : NNReal)
    (o : Fin d → ℤ) :
    ∫⁻ ω, clusterVol ω o ^ 2 ∂(latticeLongRangeMeasure d α β)
      ≤ (∫⁻ ω, clusterVol ω o ∂(latticeLongRangeMeasure d α β)) ^ 3 :=
  longRange_lintegral_clusterVol_sq_le_cube_pow (lrKernel d α) (lrKernel_shift_invariant d α)
    (lrKernel_nonneg d α) β o

end Lattice

end PercLib.CriticalLRP
