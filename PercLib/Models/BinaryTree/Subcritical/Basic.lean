/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

/-
Concrete-model witness for the subcritical finite-susceptibility statement of
Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, §I.1.2, in the
paper's own interface `longRangeMeasure J hJ β` / `criticalBeta J hJ`.

Setting: the rooted binary tree on words over `Fin 2`, with the nonzero kernel
`J = 1` on tree edges and `J = 0` on every other unordered pair (so `J` vanishes on
the diagonal automatically, matching Definition I.1.3's factor `1(x ≠ y)`).

Results (all with standard axioms only):

* `binaryTreeKernel` is a nonzero kernel of the paper's interface;
* `lintegral_clusterVol_binaryTreeKernel_eq` : the root first moment
  `∫⁻ |K_[]| ∂P_β = (1 - 2(1 - e^{-β}))⁻¹` exactly, in `ℝ≥0∞`;
* `..._lt_top` / `..._eq_top` : this is finite for `β < log 2` and `⊤` for `β ≥ log 2`;
* `criticalBeta_binaryTreeKernel_le_logTwo` : the code's `β_c` is at most `log 2`;
* `lintegral_clusterVol_binaryTreeKernel_lt_top_iff` : the finite-mean set is **exactly**
  `[0, log 2)`, so the mean's threshold and the code's `β_c` are not identified (only
  `β_c ≤ log 2` is proved; `β_c = log 2` is one structural step away, see `analysis.md` §5);
* `lintegral_clusterVol_lt_top_of_lt_criticalBeta` : **finite first moment at every
  parameter below the code's critical parameter**, for this nonzero kernel;
* `exists_theta_zero_and_lintegral_eq_top` : at `β = log 2` (and thus at a parameter at or
  above `β_c`) the root percolation probability is `0` while the root first moment is `⊤`
  (`percolationFunction_binaryTreeKernel_eq_zero`,
  `lintegral_clusterVol_binaryTreeKernel_eq_top`).  Hence `θ = 0` alone does not give a
  finite first moment: a general proof of subcritical finiteness for the paper's kernels
  needs input beyond "no infinite cluster below `β_c`".

General, kernel-independent lemmas in this file:
`percolationFunction_eq_law_cluster_infinite`, `percolationFunction_le_infiniteClusterProb`,
`percolationFunction_eq_zero_of_lt_criticalBeta` (`β < β_c → θ_β(v) = 0`),
`infiniteClusterProb_eq_zero_of_forall_lintegral_lt_top` (a finite first moment at *every*
vertex precludes an infinite cluster) and its contrapositive
`exists_lintegral_eq_top_of_infiniteClusterProb_pos`.

Not claimed: any statement about the power-law kernel `‖x-y‖^{-d-α}` on `Z^d`.  This is a
model witness (non-vacuity of the target conclusion, and sharpness of its boundary), not a
proof of subcritical finiteness for the paper's lattice kernels.
-/
public import PercLib.Models.BinaryTree
public import PercLib.CriticalLRP.CountableProduct.FiniteFirstMoment
public import PercLib.Percolation.Bond.RootIndependence

open MeasureTheory Set PercLib.Percolation.Bond
open scoped ENNReal

@[expose] public section

namespace PercLib.CriticalLRP

noncomputable section

/-! ## The binary-tree kernel -/

/-- The edge set of the rooted binary tree on words over `Fin 2` (`PercLib.Models`' tree). -/
abbrev binaryTreeEdges : Set (Sym2 (List (Fin 2))) :=
  (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet

/-- The nonzero kernel `J = 1` on tree edges, `J = 0` elsewhere. -/
def binaryTreeKernel : Sym2 (List (Fin 2)) → ℝ :=
  fun e => if e ∈ binaryTreeEdges then 1 else 0

theorem binaryTreeKernel_nonneg (e : Sym2 (List (Fin 2))) : 0 ≤ binaryTreeKernel e := by
  unfold binaryTreeKernel; split <;> norm_num

theorem binaryTreeKernel_of_mem {e : Sym2 (List (Fin 2))} (he : e ∈ binaryTreeEdges) :
    binaryTreeKernel e = 1 := by
  simp [binaryTreeKernel, he]

theorem binaryTreeKernel_of_not_mem {e : Sym2 (List (Fin 2))} (he : e ∉ binaryTreeEdges) :
    binaryTreeKernel e = 0 := by
  simp [binaryTreeKernel, he]

/-- The kernel vanishes on the diagonal, as in Definition I.1.3. -/
theorem binaryTreeKernel_diag (v : List (Fin 2)) : binaryTreeKernel s(v, v) = 0 := by
  refine binaryTreeKernel_of_not_mem ?_
  rw [SimpleGraph.mem_edgeSet]
  simp

/-- The root edge `{[], [0]}` is a tree edge. -/
theorem rootEdge_mem : s(([] : List (Fin 2)), (0 : Fin 2) :: []) ∈ binaryTreeEdges := by
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
  refine ⟨by simp, Or.inl ⟨0, rfl⟩⟩

/-- The kernel is nonzero. -/
theorem binaryTreeKernel_ne_zero : binaryTreeKernel ≠ 0 := by
  intro h
  have h1 : binaryTreeKernel s(([] : List (Fin 2)), (0 : Fin 2) :: []) = 0 := by
    rw [h]; rfl
  rw [binaryTreeKernel_of_mem rootEdge_mem] at h1
  exact one_ne_zero h1

/-! ## The edge-open probability `1 - e^{-β}` and the paper's law -/

/-- The edge-open probability of a tree edge: `p(β) = 1 - e^{-β}`. -/
def treeProb (β : NNReal) : unitInterval :=
  ⟨1 - Real.exp (-(β : ℝ)), by
    have h1 : Real.exp (-(β : ℝ)) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.2 (by linarith [β.2])
    have h2 : 0 < Real.exp (-(β : ℝ)) := Real.exp_pos _
    constructor <;> linarith⟩

@[simp] theorem treeProb_coe (β : NNReal) :
    ((treeProb β : unitInterval) : ℝ) = 1 - Real.exp (-(β : ℝ)) := rfl

theorem treeProb_nonneg (β : NNReal) : 0 ≤ ((treeProb β : unitInterval) : ℝ) := (treeProb β).2.1

theorem treeProb_lt_one (β : NNReal) : ((treeProb β : unitInterval) : ℝ) < 1 := by
  rw [treeProb_coe]
  have := Real.exp_pos (-(β : ℝ))
  linarith

/-- **The paper's edge probability is the tree probability** on tree edges, and `0` off the
tree: `1 - e^{-β J e}` with `J = 1` on tree edges and `J = 0` elsewhere. -/
theorem bernoulliEdgeProb_binaryTreeKernel (β : NNReal) (e : Sym2 (List (Fin 2))) :
    bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β e
      = if e ∈ binaryTreeEdges then treeProb β else 0 := by
  by_cases he : e ∈ binaryTreeEdges
  · rw [ite_eq_left he]
    refine Subtype.ext ?_
    rw [bernoulliEdgeProb_coe]
    simp only [treeProb_coe, binaryTreeKernel_of_mem he, mul_one]
  · rw [ite_eq_right he]
    refine Subtype.ext ?_
    rw [bernoulliEdgeProb_coe]
    simp only [binaryTreeKernel_of_not_mem he, mul_zero, neg_zero, Real.exp_zero]
    norm_num

theorem binaryTree_offDiag_eq (β : NNReal) :
    ∀ e : Sym2 (List (Fin 2)), ¬ e.IsDiag →
      bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β e
        = if e ∈ binaryTreeEdges then treeProb β else 0 :=
  fun e _ => bernoulliEdgeProb_binaryTreeKernel β e

/-- The paper's law `P_β` for the tree kernel is the bond law with the tree profile. -/
theorem longRangeMeasure_binaryTreeKernel (β : NNReal) :
    longRangeMeasure binaryTreeKernel binaryTreeKernel_nonneg β
      = law (bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β) := rfl

end

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

noncomputable section

open PercLib.Models

/-- The tree threshold parameter `log 2`, as an element of `ℝ≥0`. -/
def logTwo : NNReal :=
  ⟨Real.log 2, Real.log_nonneg one_le_two⟩

@[simp] theorem logTwo_coe : ((logTwo : NNReal) : ℝ) = Real.log 2 := rfl

theorem exp_neg_logTwo : Real.exp (-(Real.log 2)) = 1 / 2 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- `p(β) < 1/2` is `β < log 2`. -/
theorem treeProb_coe_lt_half_iff (β : NNReal) :
    ((treeProb β : unitInterval) : ℝ) < 1 / 2 ↔ β < logTwo := by
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  constructor
  · intro h
    rw [treeProb_coe] at h
    have h1 : (1 : ℝ) / 2 < Real.exp (-(β : ℝ)) := by linarith
    have h2 : Real.exp (Real.log (1 / 2)) < Real.exp (-(β : ℝ)) := by
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
    have h3 : Real.log (1 / 2) < -(β : ℝ) := Real.exp_lt_exp.1 h2
    rw [hlog] at h3
    have h4 : (β : ℝ) < Real.log 2 := by linarith
    exact_mod_cast h4
  · intro h
    have hc : (β : ℝ) < Real.log 2 := by exact_mod_cast h
    have h2 : Real.exp (-(Real.log 2)) < Real.exp (-(β : ℝ)) := Real.exp_lt_exp.2 (by linarith)
    rw [exp_neg_logTwo] at h2
    rw [treeProb_coe]
    linarith

/-- `1/2 < p(β)` is `log 2 < β`. -/
theorem half_lt_treeProb_coe_iff (β : NNReal) :
    1 / 2 < ((treeProb β : unitInterval) : ℝ) ↔ logTwo < β := by
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  constructor
  · intro h
    rw [treeProb_coe] at h
    have h1 : Real.exp (-(β : ℝ)) < 1 / 2 := by linarith
    have h2 : Real.exp (-(β : ℝ)) < Real.exp (Real.log (1 / 2)) := by
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
    have h3 : -(β : ℝ) < Real.log (1 / 2) := Real.exp_lt_exp.1 h2
    rw [hlog] at h3
    have h4 : Real.log 2 < (β : ℝ) := by linarith
    exact_mod_cast h4
  · intro h
    have hc : Real.log 2 < (β : ℝ) := by exact_mod_cast h
    have h2 : Real.exp (-(β : ℝ)) < Real.exp (-(Real.log 2)) := Real.exp_lt_exp.2 (by linarith)
    rw [exp_neg_logTwo] at h2
    rw [treeProb_coe]
    linarith

/-- The tree probability at the threshold is exactly `1/2`. -/
theorem treeProb_coe_logTwo : ((treeProb logTwo : unitInterval) : ℝ) = 1 / 2 := by
  rw [treeProb_coe, logTwo_coe, exp_neg_logTwo]
  norm_num

/-! ## The root first moment, exactly -/

/-- **Exact root susceptibility for the tree kernel**:
`∫⁻ |K_[]| ∂P_β = (1 - 2p(β))⁻¹`, finite exactly when `p(β) < 1/2`. -/
theorem lintegral_clusterVol_binaryTreeKernel_eq (β : NNReal)
    (hβ : ((treeProb β : unitInterval) : ℝ) < 1 / 2) :
    ∫⁻ ω, clusterVol ω ([] : List (Fin 2))
        ∂longRangeMeasure binaryTreeKernel binaryTreeKernel_nonneg β
      = ENNReal.ofReal (1 - 2 * ((treeProb β : unitInterval) : ℝ))⁻¹ := by
  have h := binaryTree_chi_of_lt (p := treeProb β)
    (q := bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β)
    (binaryTree_offDiag_eq β) hβ
  simpa [chi, longRangeMeasure, edgeMeasure, clusterVol] using h

theorem lintegral_clusterVol_binaryTreeKernel_lt_top (β : NNReal)
    (hβ : ((treeProb β : unitInterval) : ℝ) < 1 / 2) :
    ∫⁻ ω, clusterVol ω ([] : List (Fin 2))
        ∂longRangeMeasure binaryTreeKernel binaryTreeKernel_nonneg β < ⊤ := by
  rw [lintegral_clusterVol_binaryTreeKernel_eq β hβ]
  exact ENNReal.ofReal_lt_top

/-- At and above `p = 1/2` the root first moment is infinite. -/
theorem lintegral_clusterVol_binaryTreeKernel_eq_top (β : NNReal)
    (hβ : 1 / 2 ≤ ((treeProb β : unitInterval) : ℝ)) :
    ∫⁻ ω, clusterVol ω ([] : List (Fin 2))
        ∂longRangeMeasure binaryTreeKernel binaryTreeKernel_nonneg β = ⊤ := by
  have h := binaryTree_chi_of_le (p := treeProb β)
    (q := bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β)
    (binaryTree_offDiag_eq β) hβ
  simpa [chi, longRangeMeasure, edgeMeasure, clusterVol] using h

end

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

noncomputable section

open PercLib.Models

/-! ## General bridges between the paper's interface and the bond interface -/

/-- The root percolation function is the probability that the root's cluster is an infinite
set (the `PercLib.Models` form of `θ`). -/
theorem percolationFunction_eq_law_cluster_infinite {V : Type*} [Countable V]
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (v : V) :
    percolationFunction J hJ β v
      = law (bernoulliEdgeProb J hJ β) {ω : Config V | (cluster ω v).Infinite} := by
  rw [percolationFunction, longRangeMeasure, edgeMeasure]
  congr 1
  ext ω
  exact inInfiniteCluster_iff_infinite ω v

/-- The root percolation function is bounded by the probability that an infinite cluster
exists somewhere. -/
theorem percolationFunction_le_infiniteClusterProb {V : Type*} [Countable V]
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (v : V) :
    percolationFunction J hJ β v ≤ infiniteClusterProb J hJ β := by
  rw [percolationFunction, infiniteClusterProb, existsInfiniteClusterEvent]
  exact measure_mono fun ω hω => ⟨v, hω⟩

/-- Below the critical parameter the root does not percolate. -/
theorem percolationFunction_eq_zero_of_lt_criticalBeta {V : Type*} [Countable V]
    {J : Sym2 V → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal} {v : V}
    (h : β < criticalBeta J hJ) :
    percolationFunction J hJ β v = 0 := by
  have hz : infiniteClusterProb J hJ β = 0 := infiniteClusterProb_eq_zero_of_lt_criticalBeta h
  have hle := percolationFunction_le_infiniteClusterProb J hJ β v
  rw [hz] at hle
  exact le_antisymm hle bot_le

/-! ## The tree kernel: percolation probability and critical parameter -/

/-- Below `p = 1/2` the root does not percolate. -/
theorem percolationFunction_binaryTreeKernel_eq_zero (β : NNReal)
    (hβ : ((treeProb β : unitInterval) : ℝ) ≤ 1 / 2) :
    percolationFunction binaryTreeKernel binaryTreeKernel_nonneg β ([] : List (Fin 2)) = 0 := by
  rw [percolationFunction_eq_law_cluster_infinite]
  exact binaryTree_theta_of_le (treeProb β)
    (bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β)
    (binaryTree_offDiag_eq β) hβ

/-- Above `p = 1/2` the root percolates with positive probability. -/
theorem percolationFunction_binaryTreeKernel_pos (β : NNReal)
    (hβ : 1 / 2 < ((treeProb β : unitInterval) : ℝ)) :
    0 < percolationFunction binaryTreeKernel binaryTreeKernel_nonneg β ([] : List (Fin 2)) := by
  rw [percolationFunction_eq_law_cluster_infinite,
    binaryTree_theta_of_lt (treeProb β)
      (bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β)
      (binaryTree_offDiag_eq β) hβ]
  refine ENNReal.ofReal_pos.2 ?_
  have hp0 : (0 : ℝ) < ((treeProb β : unitInterval) : ℝ) := by linarith
  have hp1 : ((treeProb β : unitInterval) : ℝ) ≤ 1 := (treeProb β).2.2
  have hq : (1 - ((treeProb β : unitInterval) : ℝ)) / ((treeProb β : unitInterval) : ℝ) < 1 := by
    rw [div_lt_one hp0]; linarith
  have hq0 : 0 ≤ (1 - ((treeProb β : unitInterval) : ℝ)) / ((treeProb β : unitInterval) : ℝ) :=
    div_nonneg (by linarith) (le_of_lt hp0)
  nlinarith

/-- Above `p = 1/2` some infinite cluster exists with positive probability. -/
theorem infiniteClusterProb_binaryTreeKernel_pos (β : NNReal)
    (hβ : 1 / 2 < ((treeProb β : unitInterval) : ℝ)) :
    0 < infiniteClusterProb binaryTreeKernel binaryTreeKernel_nonneg β :=
  lt_of_lt_of_le (percolationFunction_binaryTreeKernel_pos β hβ)
    (percolationFunction_le_infiniteClusterProb _ _ β ([] : List (Fin 2)))

/-- Above `p = 1/2` the tree kernel percolates almost surely (zero–one law). -/
theorem mem_criticalBetaSet_binaryTreeKernel (β : NNReal)
    (hβ : 1 / 2 < ((treeProb β : unitInterval) : ℝ)) :
    β ∈ criticalBetaSet binaryTreeKernel binaryTreeKernel_nonneg := by
  rw [mem_criticalBetaSet_iff]
  rcases percolationEventProb_zero_or_one binaryTreeKernel binaryTreeKernel_nonneg β with h | h
  · exact absurd h (ne_of_gt (infiniteClusterProb_binaryTreeKernel_pos β hβ))
  · exact h

/-- **The code's critical parameter for the tree kernel is at most `log 2`.** -/
theorem criticalBeta_binaryTreeKernel_le_logTwo :
    criticalBeta binaryTreeKernel binaryTreeKernel_nonneg ≤ logTwo := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  refine criticalBeta_le_of_mem ?_
  refine mem_criticalBetaSet_binaryTreeKernel _ ?_
  rw [half_lt_treeProb_coe_iff]
  exact lt_add_of_pos_right _ hε

/-- At a positive parameter the support of the tree kernel is preconnected.  All tree
edges have positive probability, so paths through the root are enough. -/
theorem binaryTree_support_preconnected (β : NNReal) (hβ : 0 < β) :
    (SimpleGraph.fromEdgeSet
      {e | 0 < bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β e}).Preconnected := by
  have hβr : (0 : ℝ) < β := by exact_mod_cast hβ
  have hprob : 0 < ((treeProb β : unitInterval) : ℝ) := by
    rw [treeProb_coe, sub_pos, Real.exp_lt_one_iff]
    exact neg_neg_of_pos hβr
  have hroot : ∀ v : List (Fin 2),
      (SimpleGraph.fromEdgeSet
        {e | 0 < bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β e}).Reachable [] v := by
    intro v
    apply PercLib.Models.reachable_nil_of_forall_drop _ v
    intro m hm
    have hedge : s(v.drop (m + 1), v.drop m) ∈ binaryTreeEdges := by
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
      have hcons : v.drop m = v.get ⟨m, hm⟩ :: v.drop (m + 1) := List.drop_eq_getElem_cons hm
      have hne : v.drop m ≠ v.drop (m + 1) := by
        intro heq
        have hlen := congrArg List.length hcons
        simp only [heq, List.length_cons] at hlen
        omega
      exact ⟨hne.symm, Or.inl ⟨_, hcons⟩⟩
    change 0 < bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β
      s(v.drop (m + 1), v.drop m)
    rw [bernoulliEdgeProb_binaryTreeKernel, ite_eq_left hedge]
    exact hprob
  intro x y
  exact (hroot x).symm.trans (hroot y)

/-- **The binary tree has a positive literal critical parameter**.  A positive
subcritical parameter below `log 2` has zero global percolation probability, and its
upper-set continues above the critical point.  This is the non-vacuity witness for the
`of_nonempty` threshold transports; it makes no claim about the lattice kernel. -/
theorem criticalBeta_binaryTreeKernel_pos :
    0 < criticalBeta binaryTreeKernel binaryTreeKernel_nonneg := by
  have hlog : 0 < logTwo := by
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hne : (criticalBetaSet binaryTreeKernel binaryTreeKernel_nonneg).Nonempty := by
    refine ⟨logTwo + 1, ?_⟩
    refine mem_criticalBetaSet_binaryTreeKernel _ ?_
    rw [half_lt_treeProb_coe_iff]
    exact lt_add_of_pos_right _ zero_lt_one
  have hquarter : logTwo / 4 < logTwo := div_lt_self hlog (by norm_num)
  have hroot_zero := percolationFunction_binaryTreeKernel_eq_zero (logTwo / 4)
    ((treeProb_coe_lt_half_iff _).2 hquarter).le
  have hzeros : ∀ v : List (Fin 2),
      percolationFunction binaryTreeKernel binaryTreeKernel_nonneg (logTwo / 4) v = 0 := by
    intro v
    by_contra hv
    have hvpos : 0 < law (bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg (logTwo / 4))
        {ω | (PercLib.Percolation.Bond.cluster ω v).Infinite} := by
      rw [← percolationFunction_eq_law_cluster_infinite]
      exact pos_iff_ne_zero.mpr hv
    have hroot_pos := (PercLib.Percolation.Bond.law_cluster_infinite_pos_iff_of_preconnected _
      (binaryTree_support_preconnected _ (div_pos hlog (by norm_num))) v []).1 hvpos
    rw [← percolationFunction_eq_law_cluster_infinite, hroot_zero] at hroot_pos
    exact lt_irrefl 0 hroot_pos
  have hb : infiniteClusterProb binaryTreeKernel binaryTreeKernel_nonneg (logTwo / 4) = 0 := by
    rw [infiniteClusterProb_eq_zero_iff_forall binaryTreeKernel_nonneg]
    exact hzeros
  have hle := le_criticalBeta_of_infiniteClusterProb_eq_zero_of_nonempty hne hb
  exact lt_of_lt_of_le (show 0 < logTwo / 4 by exact div_pos hlog (by norm_num)) hle

/-- **Finite root first moment at every parameter below the code's critical parameter**,
for the nonzero tree kernel. -/
theorem lintegral_clusterVol_lt_top_of_lt_criticalBeta (β : NNReal)
    (hβ : β < criticalBeta binaryTreeKernel binaryTreeKernel_nonneg) :
    ∫⁻ ω, clusterVol ω ([] : List (Fin 2))
        ∂longRangeMeasure binaryTreeKernel binaryTreeKernel_nonneg β < ⊤ := by
  have hlt : β < logTwo := lt_of_lt_of_le hβ criticalBeta_binaryTreeKernel_le_logTwo
  exact lintegral_clusterVol_binaryTreeKernel_lt_top β ((treeProb_coe_lt_half_iff β).2 hlt)

/-- **The finite-mean set is exactly the interval below `log 2`** for the tree kernel. -/
theorem lintegral_clusterVol_binaryTreeKernel_lt_top_iff (β : NNReal) :
    ∫⁻ ω, clusterVol ω ([] : List (Fin 2))
        ∂longRangeMeasure binaryTreeKernel binaryTreeKernel_nonneg β < ⊤ ↔ β < logTwo := by
  rw [← treeProb_coe_lt_half_iff β]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [lintegral_clusterVol_binaryTreeKernel_eq_top β hc] at h
    exact absurd h (lt_irrefl ⊤)
  · exact lintegral_clusterVol_binaryTreeKernel_lt_top β

/-! ## General: a finite first moment at every vertex precludes percolation -/

/-- If the first moment is finite at **every** vertex then there is no infinite cluster almost
surely.  (This is the general form of "finite susceptibility excludes percolation"; it needs
the mean at every vertex, not only at one, because `∃ v` is a countable union.) -/
theorem infiniteClusterProb_eq_zero_of_forall_lintegral_lt_top {V : Type*} [Countable V]
    {J : Sym2 V → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (h : ∀ v : V, ∫⁻ ω, clusterVol ω v ∂longRangeMeasure J hJ β < ⊤) :
    infiniteClusterProb J hJ β = 0 := by
  exact infiniteClusterProb_eq_zero_of_forall_clusterVol_lintegral_lt_top h

/-- Contrapositive form: percolation at `β` forces the first moment to be infinite at some
vertex. -/
theorem exists_lintegral_eq_top_of_infiniteClusterProb_pos {V : Type*} [Countable V]
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (h : 0 < infiniteClusterProb J hJ β) :
    ∃ v : V, ∫⁻ ω, clusterVol ω v ∂longRangeMeasure J hJ β = ⊤ := by
  by_contra hcon
  push Not at hcon
  exact absurd (infiniteClusterProb_eq_zero_of_forall_lintegral_lt_top
    (fun v => lt_top_iff_ne_top.mpr (hcon v))) (ne_of_gt h)

/-! ## The packaged witness -/

/-- **Non-vacuity of subcritical finite susceptibility**: a nonzero kernel of the paper's
interface (`Sym2 V → ℝ`, `V` countable, `P_β` with edge probabilities `1 - e^{-β J e}`) whose
root first moment is finite at *every* parameter below the code's critical parameter. -/
theorem exists_nonzero_kernel_finite_first_moment_below_criticalBeta :
    ∃ (J : Sym2 (List (Fin 2)) → ℝ) (hJ : ∀ e, 0 ≤ J e),
      J ≠ 0 ∧ ∀ β : NNReal, β < criticalBeta J hJ →
        ∫⁻ ω, clusterVol ω ([] : List (Fin 2)) ∂longRangeMeasure J hJ β < ⊤ :=
  ⟨binaryTreeKernel, binaryTreeKernel_nonneg, binaryTreeKernel_ne_zero,
    fun β hβ => lintegral_clusterVol_lt_top_of_lt_criticalBeta β hβ⟩

/-- **`θ = 0` does not give a finite first moment.**  For the tree kernel at `β = log 2` the
root percolation probability vanishes while the root first moment is `⊤`; so no argument can
deduce subcritical finiteness from "no infinite cluster" alone. -/
theorem exists_theta_zero_and_lintegral_eq_top :
    ∃ (J : Sym2 (List (Fin 2)) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal),
      percolationFunction J hJ β [] = 0 ∧
        (∫⁻ ω, clusterVol ω ([] : List (Fin 2)) ∂longRangeMeasure J hJ β) = ⊤ :=
  ⟨binaryTreeKernel, binaryTreeKernel_nonneg, logTwo,
    percolationFunction_binaryTreeKernel_eq_zero logTwo (le_of_eq treeProb_coe_logTwo),
    lintegral_clusterVol_binaryTreeKernel_eq_top logTwo (le_of_eq treeProb_coe_logTwo.symm)⟩

/-- **The naive inference "`θ_β(v) = 0` implies a finite first moment at `v`" is false**, even
for nonzero kernels of the paper's interface: the tree kernel at `β = log 2` has `θ = 0` and
first moment `⊤`.  This is the formal refutation of the only shortcut that the current
`criticalBeta` interface offers. -/
theorem not_forall_theta_zero_imp_lintegral_lt_top :
    ¬ ∀ (J : Sym2 (List (Fin 2)) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal),
        percolationFunction J hJ β ([] : List (Fin 2)) = 0 →
        ∫⁻ ω, clusterVol ω ([] : List (Fin 2)) ∂longRangeMeasure J hJ β < ⊤ := by
  intro h
  obtain ⟨J, hJ, β, hθ, htop⟩ := exists_theta_zero_and_lintegral_eq_top
  exact absurd (h J hJ β hθ) (by rw [htop]; exact lt_irrefl ⊤)

end

end PercLib.CriticalLRP

/-! ## Axiom audit -/

section Audit

#print axioms PercLib.CriticalLRP.binaryTreeKernel_ne_zero
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_binaryTreeKernel_eq
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_binaryTreeKernel_lt_top
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_binaryTreeKernel_eq_top
#print axioms PercLib.CriticalLRP.percolationFunction_binaryTreeKernel_eq_zero
#print axioms PercLib.CriticalLRP.percolationFunction_binaryTreeKernel_pos
#print axioms PercLib.CriticalLRP.mem_criticalBetaSet_binaryTreeKernel
#print axioms PercLib.CriticalLRP.binaryTree_support_preconnected
#print axioms PercLib.CriticalLRP.criticalBeta_binaryTreeKernel_le_logTwo
#print axioms PercLib.CriticalLRP.criticalBeta_binaryTreeKernel_pos
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_lt_top_of_lt_criticalBeta
#print axioms PercLib.CriticalLRP.percolationFunction_eq_zero_of_lt_criticalBeta
#print axioms PercLib.CriticalLRP.exists_nonzero_kernel_finite_first_moment_below_criticalBeta
#print axioms PercLib.CriticalLRP.exists_theta_zero_and_lintegral_eq_top
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_binaryTreeKernel_lt_top_iff
#print axioms PercLib.CriticalLRP.infiniteClusterProb_eq_zero_of_forall_lintegral_lt_top
#print axioms PercLib.CriticalLRP.exists_lintegral_eq_top_of_infiniteClusterProb_pos
#print axioms PercLib.CriticalLRP.not_forall_theta_zero_imp_lintegral_lt_top

end Audit
