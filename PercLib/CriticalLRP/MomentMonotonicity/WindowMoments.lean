/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Finite support versus finite moments: the exact content of
  `hutchcroft.i.1.5.step.cutoffmoments`

The cut-off kernel `J_r` of Definition I.1.5 has **finite support at every vertex**: the
only `y` with `J_r(x,y) ≠ 0` are those with `‖y − x‖_∞ ≤ r`
(`cutoffSymKernel_support_finite` below).  That is a bound on the *degree* of the
configuration graph, not on the *cluster*: the cluster of `x` is the set of endpoints of
finite paths of unbounded length inside the range-`r` graph, so it can be infinite.  For
`1 < r ≤ 2` the only pairs with `J_r(x,y) ≠ 0` are nearest neighbours (weight
`K 1 − K r > 0`), i.e. the range-`r` law contains nearest-neighbour percolation, which
percolates at large `β` (standard, not formalized in this repository).  Consequently
finite support of the kernel does **not** bound any cluster moment, and the finite-volume
(box) law cannot be passed off as the lattice law.

What the finite support *does* give is precisely delimited here, in the general
Bernoulli bond setting, and then at the cut-off law:

* `powMoment_eq_iSup_window` — the `p`-th cluster moment is the supremum of its
  *windowed* values `∫⁻ |K ∩ B_n|^p` over any cofinal family of windows (this is
  `secondMoment_eq_iSup_box` for arbitrary `p`);
* `window_powMoment_ne_top` — every windowed `p`-th moment is finite, with the explicit
  bound `|B_n|^p` (this is the only "finite-universe" bound available);
* `powMoment_ne_top_iff_uniform_window` — hence the full `p`-th moment is finite **iff**
  the windowed moments are *uniformly* bounded in `n`;
* `powMoment_le_of_ae_cluster_subset_finset` — the abstract finite-support escape hatch:
  if the cluster is a.s. contained in a fixed finite set, all moments are bounded by
  `|S|^p`.  The windowed moments of the cut-off law are of exactly this shape, which is
  why they are finite and why the hypothesis cannot be upgraded to the lattice.

So no finiteness of a support set can discharge `hutchcroft.i.1.5.step.cutoffmoments`:
the obligation is *uniformity* of the windowed moments, i.e. a percolation-theoretic
statement (subcritical first moment plus a tree-graph/tail input), not a support
statement.  The transfer that consumes such a bound at *every* order is
`MomentTransfer.cutoff_lintegral_clusterVol_pow_ne_top`.

No new definitions, no `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CutoffDominated
public import PercLib.CriticalLRP.VolumeMoments.SecondMomentWindow
public import PercLib.CriticalLRP.CountableProduct.Compatibility

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-! ## The windowed cluster volume as a finite sum over the window -/

/-- `|K_v ∩ F|` for a finite `F` is the sum of the indicators of `K_v` over `F`. -/
theorem clusterVolIn_coe_finset (ω : Config V) (v : V) (F : Finset V) :
    clusterVolIn ω v (F : Set V) = ∑ w ∈ F, (if w ∈ cluster ω v then (1 : ℝ≥0∞) else 0) := by
  have hset : cluster ω v ∩ (F : Set V) = ((F.filter fun w => w ∈ cluster ω v : Finset V) : Set V) := by
    ext w
    simp [and_comm]
  rw [clusterVolIn, Finset.sum_boole, hset, Set.encard_coe_eq_coe_finsetCard]
  push_cast
  ring

/-- The windowed cluster volume is monotone in the window. -/
theorem clusterVolIn_mono {ω : Config V} {v : V} {W W' : Set V} (h : W ⊆ W') :
    clusterVolIn ω v W ≤ clusterVolIn ω v W' := by
  have h' : cluster ω v ∩ W ⊆ cluster ω v ∩ W' := Set.inter_subset_inter_right _ h
  show ((cluster ω v ∩ W).encard : ℝ≥0∞) ≤ ((cluster ω v ∩ W').encard : ℝ≥0∞)
  exact_mod_cast Set.encard_mono h'

/-! ## The cluster volume as the supremum of its windowed values -/

/-- **The cluster volume is exhausted by any cofinal family of windows.** -/
theorem clusterVol_eq_iSup_window (ω : Config V) (v : V) (F : ℕ → Finset V)
    (hF : ∀ s : Finset V, ∃ n, s ⊆ F n) :
    clusterVol ω v = ⨆ n, clusterVolIn ω v (F n) := by
  rw [clusterVol_eq_tsum, ENNReal.tsum_eq_iSup_sum]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun s => ?_
    obtain ⟨n, hn⟩ := hF s
    refine le_iSup_of_le n ?_
    rw [clusterVolIn_coe_finset]
    exact Finset.sum_le_sum_of_subset_of_nonneg hn fun w _ _ => zero_le
  · refine iSup_le fun n => ?_
    rw [clusterVolIn_coe_finset]
    exact le_iSup (fun s : Finset V => ∑ w ∈ s, if w ∈ cluster ω v then (1 : ℝ≥0∞) else 0) (F n)

/-- **Every cluster moment is the supremum of its windowed values.**  No finiteness
assumption and no percolation input: this is the monotone convergence of
`|K_v ∩ B_n|^p ↑ |K_v|^p`. -/
theorem lintegral_clusterVol_pow_eq_iSup_window (q : Sym2 V → unitInterval) (v : V)
    (F : ℕ → Finset V) (hF : ∀ s : Finset V, ∃ n, s ⊆ F n) (hmono : Monotone F) (p : ℕ) :
    (∫⁻ ω, clusterVol ω v ^ p ∂(edgeMeasure q))
      = ⨆ n, ∫⁻ ω, clusterVolIn ω v (F n) ^ p ∂(edgeMeasure q) := by
  have hpt : ∀ ω : Config V, clusterVol ω v ^ p = ⨆ n, clusterVolIn ω v (F n) ^ p := by
    intro ω
    rw [clusterVol_eq_iSup_window ω v F hF, ENNReal.iSup_pow]
  simp only [hpt]
  rw [lintegral_iSup]
  · intro n
    exact (measurable_clusterVolIn v (F n)).pow_const p
  · intro m n hmn ω
    exact pow_le_pow_left' (clusterVolIn_mono (by simpa using hmono hmn : (F m : Set V) ⊆ (F n : Set V))) p

/-- **Finite universe bound**: each windowed `p`-th moment is finite, with the explicit
bound `|F|^p`.  This is the only place where the finite size of a window is used. -/
theorem window_powMoment_ne_top (q : Sym2 V → unitInterval) (v : V) (F : Finset V) (p : ℕ) :
    (∫⁻ ω, clusterVolIn ω v (F : Set V) ^ p ∂(edgeMeasure q)) ≠ ⊤ := by
  have hb : ∀ ω : Config V, clusterVolIn ω v (F : Set V) ≤ (F.card : ℝ≥0∞) := by
    intro ω
    have h1 : clusterVolIn ω v (F : Set V) ≤ ((F : Set V).encard : ℝ≥0∞) := by
      show ((cluster ω v ∩ (F : Set V)).encard : ℝ≥0∞) ≤ _
      exact_mod_cast Set.encard_mono
        (Set.inter_subset_right : cluster ω v ∩ (F : Set V) ⊆ (F : Set V))
    calc clusterVolIn ω v (F : Set V) ≤ ((F : Set V).encard : ℝ≥0∞) := h1
      _ = (F.card : ℝ≥0∞) := by rw [Set.encard_coe_eq_coe_finsetCard]; simp
  have hmono : (∫⁻ ω, clusterVolIn ω v (F : Set V) ^ p ∂(edgeMeasure q))
      ≤ ∫⁻ _ω : Config V, (F.card : ℝ≥0∞) ^ p ∂(edgeMeasure q) :=
    lintegral_mono fun ω => pow_le_pow_left' (hb ω) p
  have htop : (∫⁻ _ω : Config V, (F.card : ℝ≥0∞) ^ p ∂(edgeMeasure q))
      = (F.card : ℝ≥0∞) ^ p := by
    rw [lintegral_const]
    simp
  rw [htop] at hmono
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)) hmono

/-- **The exact content of a full cluster moment**: it is finite iff the windowed moments
admit a bound independent of the window.  Finite support of the kernel gives the
finiteness of each term, never the uniformity. -/
theorem powMoment_ne_top_iff_uniform_window (q : Sym2 V → unitInterval) (v : V)
    (F : ℕ → Finset V) (hF : ∀ s : Finset V, ∃ n, s ⊆ F n) (hmono : Monotone F) (p : ℕ) :
    (∫⁻ ω, clusterVol ω v ^ p ∂(edgeMeasure q)) ≠ ⊤ ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n,
        (∫⁻ ω, clusterVolIn ω v (F n) ^ p ∂(edgeMeasure q)) ≤ C := by
  rw [lintegral_clusterVol_pow_eq_iSup_window q v F hF hmono p]
  constructor
  · intro h
    exact ⟨_, h, fun n => le_iSup
      (fun n => ∫⁻ ω, clusterVolIn ω v (F n) ^ p ∂(edgeMeasure q)) n⟩
  · rintro ⟨C, hC, hle⟩
    exact ne_top_of_le_ne_top hC (ciSup_le hle)

/-! ## The abstract finite-support escape hatch -/

/-- If the cluster of `v` is almost surely contained in a fixed finite set `S`, then every
moment is finite and bounded by `|S|^p`.  This is the *only* shape in which a
finite-support hypothesis produces a moment bound.  It does not apply to the cut-off law
of Definition I.1.5: there `J_r` bounds edge *lengths*, and the cluster is the set of
endpoints of paths of unbounded length in the range-`r` graph (for `1 < r ≤ 2` that graph
contains nearest-neighbour percolation), so no finite `S` contains it a.s. -/

theorem powMoment_le_of_ae_cluster_subset_finset (q : Sym2 V → unitInterval) (v : V)
    (S : Finset V) (h : ∀ᵐ ω ∂(edgeMeasure q), cluster ω v ⊆ (S : Set V)) (p : ℕ) :
    (∫⁻ ω, clusterVol ω v ^ p ∂(edgeMeasure q)) ≤ (S.card : ℝ≥0∞) ^ p := by
  have hbound : ∀ᵐ ω ∂(edgeMeasure q), clusterVol ω v ^ p ≤ (S.card : ℝ≥0∞) ^ p := by
    filter_upwards [h] with ω hω
    have h1 : clusterVol ω v ≤ (S.card : ℝ≥0∞) := by
      rw [clusterVol_eq_encard]
      have h2 : (cluster ω v).encard ≤ (S : Set V).encard := Set.encard_mono hω
      have h3 : ((S : Set V).encard : ℝ≥0∞) = (S.card : ℝ≥0∞) := by
        rw [Set.encard_coe_eq_coe_finsetCard]
        simp
      calc ((cluster ω v).encard : ℝ≥0∞) ≤ ((S : Set V).encard : ℝ≥0∞) := by
            exact_mod_cast h2
        _ = (S.card : ℝ≥0∞) := h3
    exact pow_le_pow_left' h1 p
  calc (∫⁻ ω, clusterVol ω v ^ p ∂(edgeMeasure q))
      ≤ ∫⁻ _ω : Config V, (S.card : ℝ≥0∞) ^ p ∂(edgeMeasure q) :=
        lintegral_mono_ae hbound
    _ = (S.card : ℝ≥0∞) ^ p := by rw [lintegral_const]; simp

/-! ## Finite support of the Definition I.1.5 cut-off kernel -/

namespace CutoffSupport

open FiniteVolume CutoffKernel

variable {d : ℕ}

/-- **The cut-off kernel of Definition I.1.5 has finite support at every vertex.**  For
every profile `K`, radius `r` and base point `x`, only finitely many `y` satisfy
`J_r(x,y) ≠ 0`, namely those with `‖y − x‖_∞ ≤ ⌈r⌉₊`. -/
theorem cutoffSymKernel_support_finite (K : ℝ → ℝ) (r : ℝ) (x : Fin d → ℤ) :
    {y : Fin d → ℤ | cutoffSymKernel K d r s(x, y) ≠ 0}.Finite := by
  refine Set.Finite.subset (Finset.finite_toSet ((box d ⌈r⌉₊).image (· + x))) ?_
  intro y hy
  by_contra hmem
  have hlt : ⌈r⌉₊ < linfNorm (y - x) := by
    by_contra hle
    exact hmem (Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨y - x, mem_box_iff.mpr (not_lt.mp hle), by abel⟩))
  have hxne : x ≠ y := by
    rintro rfl
    rw [sub_self, show linfNorm (0 : Fin d → ℤ) = 0 from linfNorm_eq_zero_iff.mpr rfl] at hlt
    exact absurd hlt (not_lt.mpr (Nat.zero_le _))
  have hdist : r < ((linfNorm (x - y) : ℕ) : ℝ) := by
    have h1 : ((linfNorm (x - y) : ℕ) : ℝ) = ((linfNorm (y - x) : ℕ) : ℝ) := by
      rw [show x - y = -(y - x) by abel, linfNorm_neg]
    have h2 : (⌈r⌉₊ : ℝ) < ((linfNorm (y - x) : ℕ) : ℝ) := by exact_mod_cast hlt
    have h3 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    rw [h1]; linarith
  have hzero : cutoffSymKernel K d r s(x, y) = 0 := by
    rw [cutoffSymKernel_mk, ite_eq_right hxne, cutoffProfile_of_lt hdist]
  exact hy hzero

end CutoffSupport

end PercLib.CriticalLRP

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.clusterVolIn_coe_finset
#print axioms PercLib.CriticalLRP.clusterVolIn_mono
#print axioms PercLib.CriticalLRP.clusterVol_eq_iSup_window
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_pow_eq_iSup_window
#print axioms PercLib.CriticalLRP.window_powMoment_ne_top
#print axioms PercLib.CriticalLRP.powMoment_ne_top_iff_uniform_window
#print axioms PercLib.CriticalLRP.powMoment_le_of_ae_cluster_subset_finset
#print axioms PercLib.CriticalLRP.CutoffSupport.cutoffSymKernel_support_finite
