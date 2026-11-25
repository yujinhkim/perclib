/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Rebuilt from Ultramath `smwv4hzkh`, member `m3`, for `smwv576pz` direction A4, and validated
independently against the production tree at commit 8351546.  The block display, the attainment
statement and the elementary size bounds are new; the optimality of the `|W| + 1` edian bound is
added here (the earlier packet only recorded the loose bound).
-/
module

public import PercLib.CriticalLRP.Tightness.Universal

/-!
# The block display `|K_max(Λ)| = max{|K_x ∩ Λ| : x ∈ V} = max{|K_x ∩ Λ| : x ∈ Λ}`

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.2.1 (source locator `paper-tex.txt` line 442):

> Let `Λ ⊆ V` be finite and non-empty … Let `|K_max(Λ)|` be the random variable defined by
> `|K_max(Λ)| = max{|K_x ∩ Λ| : x ∈ V} = max{|K_x ∩ Λ| : x ∈ Λ}`.

The development defines the *right-hand* side, `clusterMaxVol ω W = W.sup (fun w => |K_w ∩ W|)`
(`Tightness/MaxCluster.lean`), and records the displayed equality only in a module comment.
This file supplies that step:

* `clusterVolIn_le_clusterMaxVol_all`: `|K_v ∩ W| ≤ |K_max(W)|` for **every** `v : V`, with no
  membership hypothesis — a cluster disjoint from `W` contributes `0`, and otherwise it is the
  cluster of a window point (`clusterVolIn_le_clusterMaxVol_of_mem_cluster`);
* `iSup_clusterVolIn_eq_clusterMaxVol`: the displayed identity itself, as an equality of the
  supremum over *all* of `V` and the finite supremum over the window;
* `exists_mem_clusterVolIn_eq_clusterMaxVol`: for non-empty `W` the supremum is *attained* at a
  vertex of the window, so both sides of the display really are maxima (not merely suprema).

The file also records the boundary case `W = ∅` (`clusterVolIn_empty`, `clusterMaxVol_empty`),
where the paper's hypothesis "`Λ` non-empty" is needed for attainment but not for the identity.

Finally it proves the elementary cardinality bounds `|K_v ∩ W| ≤ |W|`, `|K_max(W)| ≤ |W|` and
`M_β(W) ≤ |W| + 1`, and — this is the part that is not in the earlier packet — that the last
bound is **attained**, by the configuration in which every edge is open, so no sharper universal
bound `M_β(W) ≤ |W|` can hold.  The paper's edian `M_β(W)` is the existing production definition
`edianMaxVol` (`Nat.find` of the tail condition); nothing here changes that definition, and no
statement in this file is a claim about `M_r`, the critical-window edian of §I.2.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

namespace Percolation

variable {V : Type*} [Countable V]

/-! ## The empty window -/

omit [Countable V] in
/-- `|K_v ∩ ∅| = 0`. -/
theorem clusterVolIn_empty (ω : Config V) (v : V) :
    clusterVolIn ω v (∅ : Set V) = 0 := by
  simp [clusterVolIn]

omit [Countable V] in
/-- `|K_max(∅)| = 0`: the supremum over an empty window. -/
theorem clusterMaxVol_empty (ω : Config V) :
    clusterMaxVol ω (∅ : Finset V) = 0 := by
  simp [clusterMaxVol]

/-! ## The block display `max_{x ∈ V} |K_x ∩ Λ| = max_{x ∈ Λ} |K_x ∩ Λ|` -/

omit [Countable V] in
/-- Equal clusters have equal truncated volumes. -/
theorem clusterVolIn_eq_of_cluster_eq {ω : Config V} {v w : V}
    (h : PercLib.CriticalLRP.cluster ω v = PercLib.CriticalLRP.cluster ω w) (W : Set V) :
    clusterVolIn ω v W = clusterVolIn ω w W := by
  simp only [clusterVolIn, h]

/-- If `w` is a window point of the cluster of `v`, then `|K_v ∩ W| ≤ |K_max(W)|`: the cluster of
`v` is the cluster of the window point `w`, whose truncated volume occurs in the supremum. -/
theorem clusterVolIn_le_clusterMaxVol_of_mem_cluster {ω : Config V} {W : Finset V} {v w : V}
    (hw : w ∈ W) (hvw : w ∈ PercLib.CriticalLRP.cluster ω v) :
    clusterVolIn ω v (W : Set V) ≤ clusterMaxVol ω W := by
  have hcl : PercLib.CriticalLRP.cluster ω v = PercLib.CriticalLRP.cluster ω w :=
    cluster_eq_iff.mpr (mem_cluster_iff.mp hvw)
  rw [clusterVolIn_eq_of_cluster_eq hcl]
  exact clusterVolIn_le_clusterMaxVol ω hw

/-- **The paper's block inequality, for every base point**: for every vertex `v : V` —
in particular for every `v ∉ W` — `|K_v ∩ W| ≤ |K_max(W)|`.  A cluster disjoint from `W`
contributes `0`; otherwise it is the cluster of a window point. -/
theorem clusterVolIn_le_clusterMaxVol_all (ω : Config V) (W : Finset V)
    (v : V) : clusterVolIn ω v (W : Set V) ≤ clusterMaxVol ω W := by
  by_cases hne : (PercLib.CriticalLRP.cluster ω v ∩ (W : Set V)).Nonempty
  · obtain ⟨w, hwv, hwW⟩ := hne
    exact clusterVolIn_le_clusterMaxVol_of_mem_cluster hwW hwv
  · have hempty : PercLib.CriticalLRP.cluster ω v ∩ (W : Set V) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    have h0 : clusterVolIn ω v (W : Set V) = 0 := by
      simp only [clusterVolIn, hempty]
      simp
    rw [h0]
    exact zero_le

/-- The same inequality in the shape consumed by `tail_single_of_max`, which asks for a
pointwise domination `∀ ω, X ω ≤ Kmax ω` of two random variables. -/
theorem clusterVolIn_le_clusterMaxVol_fun (W : Finset V) (v : V) :
    ∀ ω : Config V, clusterVolIn ω v (W : Set V) ≤ clusterMaxVol ω W :=
  fun ω => clusterVolIn_le_clusterMaxVol_all ω W v

/-- **The displayed identity of §I.2.1**: the supremum of `|K_x ∩ Λ|` over *all* vertices of the
graph equals the supremum over the window.  (For infinite `V` this is an equality of suprema; the
next theorem shows the right-hand side is attained when `W ≠ ∅`.) -/
theorem iSup_clusterVolIn_eq_clusterMaxVol (ω : Config V) (W : Finset V) :
    (⨆ v : V, clusterVolIn ω v (W : Set V)) = clusterMaxVol ω W := by
  refine le_antisymm (iSup_le fun v => clusterVolIn_le_clusterMaxVol_all ω W v) ?_
  refine Finset.sup_le fun w hw => ?_
  exact le_iSup (fun v : V => clusterVolIn ω v (W : Set V)) w

omit [Countable V] in
/-- **The maximum block is attained in the window**: some `w ∈ W` realises `|K_max(W)|`.  This is
where the paper's hypothesis that `Λ` is non-empty is used. -/
theorem exists_mem_clusterVolIn_eq_clusterMaxVol {W : Finset V} (hW : W.Nonempty)
    (ω : Config V) : ∃ w ∈ W, clusterVolIn ω w (W : Set V) = clusterMaxVol ω W := by
  obtain ⟨w, hw, hsup⟩ :=
    Finset.exists_mem_eq_sup W hW (fun w => clusterVolIn ω w (W : Set V))
  exact ⟨w, hw, hsup.symm⟩

omit [Countable V] in
/-- For a non-empty window the supremum over *all* of `V` is attained: the paper's `max` over
`V` is a maximum, and — by the previous theorem — it is attained at a vertex of the window. -/
theorem exists_clusterVolIn_eq_clusterMaxVol {W : Finset V} (hW : W.Nonempty)
    (ω : Config V) : ∃ v : V, clusterVolIn ω v (W : Set V) = clusterMaxVol ω W := by
  obtain ⟨w, _, h⟩ := exists_mem_clusterVolIn_eq_clusterMaxVol hW ω
  exact ⟨w, h⟩

/-! ## The elementary size bounds -/

omit [Countable V] in
/-- A truncated cluster volume is at most the window: `|K_v ∩ W| ≤ |W|`. -/
theorem clusterVolIn_le_card (ω : Config V) (v : V) (W : Finset V) :
    clusterVolIn ω v (W : Set V) ≤ (W.card : ℝ≥0∞) := by
  have hsub : PercLib.CriticalLRP.cluster ω v ∩ (W : Set V) ⊆ (W : Set V) :=
    Set.inter_subset_right
  have henc : (PercLib.CriticalLRP.cluster ω v ∩ (W : Set V)).encard ≤ (W.card : ℕ∞) := by
    rw [← Set.encard_coe_eq_coe_finsetCard W]
    exact Set.encard_le_encard hsub
  have hcast :
      (((PercLib.CriticalLRP.cluster ω v ∩ (W : Set V)).encard : ℕ∞) : ℝ≥0∞) ≤
        ((W.card : ℕ∞) : ℝ≥0∞) := by
    exact_mod_cast henc
  simpa [clusterVolIn] using hcast

omit [Countable V] in
/-- `|K_max(W)| ≤ |W|`: a cluster intersection with the window has at most `|W|` points. -/
theorem clusterMaxVol_le_card (ω : Config V) (W : Finset V) :
    clusterMaxVol ω W ≤ (W.card : ℝ≥0∞) := by
  refine Finset.sup_le fun w _ => ?_
  exact clusterVolIn_le_card ω w W

omit [Countable V] in
/-- `M_β(W) ≤ |W| + 1`: the size `|W| + 1` is always admissible for the edian, because
`|K_max(W)| ≤ |W|`.  Hence the paper's edian is a genuine finite natural number, with no
subcriticality or moment-finiteness input. -/
theorem edianMaxVol_le_card_succ {μ : Measure (Config V)} [IsFiniteMeasure μ] (W : Finset V)
    (hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ clusterMaxVol ω W} ≤
      ENNReal.ofReal (Real.exp (-1))) :
    edianMaxVol μ W hex ≤ W.card + 1 := by
  refine Nat.find_min' hex ?_
  have hempty : {ω : Config V | ((W.card + 1 : ℕ) : ℝ≥0∞) ≤ clusterMaxVol ω W} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    have hcast : ((W.card : ℕ) : ℝ≥0∞) < ((W.card + 1 : ℕ) : ℝ≥0∞) := by
      rw [Nat.cast_lt]
      omega
    exact absurd (le_trans hω (clusterMaxVol_le_card ω W)) (not_le.mpr hcast)
  rw [hempty, measure_empty]
  exact zero_le

/-! ## Sharpness: `|W| + 1` is attained, so no better universal bound holds -/

omit [Countable V] in
/-- If the window is contained in the cluster of `w`, the truncated volume at `w` is `|W|`. -/
theorem clusterVolIn_eq_card_of_subset_cluster {ω : Config V} {w : V} {W : Finset V}
    (h : (W : Set V) ⊆ PercLib.CriticalLRP.cluster ω w) :
    clusterVolIn ω w (W : Set V) = (W.card : ℝ≥0∞) := by
  rw [clusterVolIn, Set.inter_eq_right.mpr h, Set.encard_coe_eq_coe_finsetCard]
  simp

/-- If the window is contained in a single cluster, `|K_max(W)| = |W|`. -/
theorem clusterMaxVol_eq_card_of_subset_cluster {ω : Config V} {w : V} {W : Finset V}
    (hw : w ∈ W) (h : (W : Set V) ⊆ PercLib.CriticalLRP.cluster ω w) :
    clusterMaxVol ω W = (W.card : ℝ≥0∞) := by
  refine le_antisymm (clusterMaxVol_le_card ω W) ?_
  rw [← clusterVolIn_eq_card_of_subset_cluster h]
  exact clusterVolIn_le_clusterMaxVol ω hw

/-- In the configuration in which every edge is open, the open graph is complete. -/
theorem cluster_top (w : V) :
    PercLib.CriticalLRP.cluster (⊤ : Config V) w = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  rw [mem_cluster_iff]
  by_cases hy : y = w
  · subst hy
    exact SimpleGraph.Reachable.refl y
  · exact SimpleGraph.Adj.reachable (openGraph_adj.mpr ⟨fun h => hy h.symm, trivial⟩)

/-- **The maximum cluster size saturates its trivial bound** on the everywhere-open
configuration: `|K_max(W)| = |W|`. -/
theorem clusterMaxVol_top (W : Finset V) :
    clusterMaxVol (⊤ : Config V) W = (W.card : ℝ≥0∞) := by
  rcases W.eq_empty_or_nonempty with h | hne
  · subst h
    rw [clusterMaxVol_empty]
    simp
  · obtain ⟨w, hw⟩ := hne
    exact clusterMaxVol_eq_card_of_subset_cluster hw (by rw [cluster_top]; exact subset_univ _)

/-- **Sharpness of `M_β(W) ≤ |W| + 1`.**  Under the Dirac measure on the everywhere-open
configuration, `|K_max(W)| = |W|` identically, so the tail probability is `1` for every `n ≤ |W|`
and `0` for `n = |W| + 1`; hence the edian is exactly `|W| + 1`.  Consequently no bound
`M_β(W) ≤ |W|` can hold for all probability measures, and `edianMaxVol_le_card_succ` is optimal in
this generality. -/
theorem edianMaxVol_dirac_top (W : Finset V)
    (hex : ∃ n : ℕ, Measure.dirac (⊤ : Config V) {ω | (n : ℝ≥0∞) ≤ clusterMaxVol ω W} ≤
      ENNReal.ofReal (Real.exp (-1))) :
    edianMaxVol (Measure.dirac (⊤ : Config V)) W hex = W.card + 1 := by
  classical
  refine le_antisymm (edianMaxVol_le_card_succ W hex) ?_
  change W.card + 1 ≤ Nat.find hex
  rw [Nat.le_find_iff]
  intro m hm hle
  have hmem : (⊤ : Config V) ∈ {ω : Config V | (m : ℝ≥0∞) ≤ clusterMaxVol ω W} := by
    simp only [Set.mem_ofPred_eq]
    rw [clusterMaxVol_top]
    exact_mod_cast Nat.lt_succ_iff.mp hm
  rw [Measure.dirac_apply_of_mem hmem] at hle
  have hone : ENNReal.ofReal (Real.exp (-1)) < 1 := by
    rw [ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
    norm_num
  exact absurd hle (not_le.mpr hone)

/-- The canonical form of the sharpness statement, at the production existence proof. -/
theorem edianMaxVol_dirac_top_card_succ (W : Finset V) :
    edianMaxVol (Measure.dirac (⊤ : Config V)) W (exists_edianMaxVol W) = W.card + 1 :=
  edianMaxVol_dirac_top W (exists_edianMaxVol W)

/-! ## Consequence: the single-cluster tail `(I.2.6)` at an arbitrary base point -/

/-- The block inequality transfers the maximum-cluster tail `(I.2.4)` to the truncated cluster
volume of an **arbitrary** vertex `v : V`, with no hypothesis `v ∈ W`.  This is the form of
`(I.2.6)` that the paper states for every `u ∈ V`. -/
theorem tail_single_of_tailMax_anyV {μ : Measure (Config V)} (W : Finset V) (v : V) {M : ℕ}
    (h24 : TailMaxI24 μ (fun ω => clusterMaxVol ω W) M) :
    ∀ t : ℝ, (M : ℝ) ≤ t →
      μ {ω | ENNReal.ofReal t ≤ clusterVolIn ω v (W : Set V)} ≤
        ENNReal.ofReal (Real.exp (-(t / (9 * M)))) :=
  tail_single_of_max (clusterVolIn_le_clusterMaxVol_fun W v) h24

end Percolation

end PercLib.CriticalLRP

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Percolation.clusterVolIn_empty
#print axioms PercLib.CriticalLRP.Percolation.clusterMaxVol_empty
#print axioms PercLib.CriticalLRP.Percolation.clusterVolIn_eq_of_cluster_eq
#print axioms PercLib.CriticalLRP.Percolation.clusterVolIn_le_clusterMaxVol_of_mem_cluster
#print axioms PercLib.CriticalLRP.Percolation.clusterVolIn_le_clusterMaxVol_all
#print axioms PercLib.CriticalLRP.Percolation.iSup_clusterVolIn_eq_clusterMaxVol
#print axioms PercLib.CriticalLRP.Percolation.exists_mem_clusterVolIn_eq_clusterMaxVol
#print axioms PercLib.CriticalLRP.Percolation.exists_clusterVolIn_eq_clusterMaxVol
#print axioms PercLib.CriticalLRP.Percolation.clusterVolIn_le_card
#print axioms PercLib.CriticalLRP.Percolation.clusterMaxVol_le_card
#print axioms PercLib.CriticalLRP.Percolation.edianMaxVol_le_card_succ
#print axioms PercLib.CriticalLRP.Percolation.clusterVolIn_eq_card_of_subset_cluster
#print axioms PercLib.CriticalLRP.Percolation.clusterMaxVol_eq_card_of_subset_cluster
#print axioms PercLib.CriticalLRP.Percolation.cluster_top
#print axioms PercLib.CriticalLRP.Percolation.clusterMaxVol_top
#print axioms PercLib.CriticalLRP.Percolation.edianMaxVol_dirac_top
#print axioms PercLib.CriticalLRP.Percolation.edianMaxVol_dirac_top_card_succ
#print axioms PercLib.CriticalLRP.Percolation.tail_single_of_tailMax_anyV
