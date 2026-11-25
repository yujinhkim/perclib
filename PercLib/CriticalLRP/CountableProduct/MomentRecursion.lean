/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Renewal first moments and independence for the row-sum programme

Accepted from independent submission `smwp81k72` direction D2.  This proves the
order-one renewal and the finite-coordinate factorisation, with the binomial
expansion, not the unproved higher-moment contraction.  The latter requires the
first-hit or branching-process input not constructed here.
-/

/-
Swarm `smwp81k72`, member `m2`, direction d2 (all-order moments from uniform row sums).

Prepared as an isolated proof-only module and now checked in the production import
closure.  It builds on the accepted renewal module of swarm `smwp7ai5u`
(`Renewal.lean`, namespace
`PercLib.CriticalLRP.Renewal`) and supplies the pieces of that run's residual
premise (R4) that are actually correct:

* measurability of the pruned cluster of `y` after every edge at `o` is closed -- the
  "measurability of `ω ↦ ω ∩ blockT o` and of the coordinate map" gap named in (R4.2);
* the *finite-set* multi-coordinate independence lemma, i.e. the weighted tuple sum
  `∫⁻ ∏_{e ∈ F} 1{e ∈ ω} · G = (∏_{e ∈ F} π e) · ∫⁻ G` for `G` blind to `F`,
  obtained by iterating the accepted single-coordinate lemma;
* the exact first-moment identity for the *offspring sum* `Y = ∑_y B_y a_y` of the
  renewal, its bound by the uniform row sum times `(1 - m)⁻¹`, and hence `∫⁻ Y ≠ ⊤`:
  the order-`1` input the moment recursion needs;
* the binomial split of the `k`-th cluster moment against the offspring sum, with the
  `j = k` term exposed -- i.e. (R4.3) minus the recursion, which cannot close
  (see `offspring_second_moment_exceeds_row_sum` and `REPORT.md`).

No new axioms, no `sorry`, no `admit`, no `native_decide`, no heartbeat changes.
-/
module

public import PercLib.CriticalLRP.CountableProduct.MomentRecursion.Defs
public import PercLib.Percolation.Bond.RowSum
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

attribute [local instance] Classical.propDecidable

@[expose] public section

open MeasureTheory Set
open PercLib.Percolation.Bond PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.MomentRecursion

open PercLib.CriticalLRP.Renewal

variable {V : Type*} [Countable V]

/-! ## Monotonicity of the cluster in the configuration -/

theorem cluster_mono {ω ω' : Config V} (h : ω ⊆ ω') (x : V) :
    cluster ω x ⊆ cluster ω' x := by
  intro y hy
  exact SimpleGraph.Reachable.mono (openGraph_mono h) hy

/-! ## Measurability of the pruning -/

/-- Intersecting with a fixed set of pairs is measurable for the cylinder σ-algebra. -/
theorem measurable_inter_const (S : Set (Sym2 V)) :
    Measurable fun ω : Config V => ω ∩ S := by
  refine Measurable.of_mem fun i => ?_
  by_cases hi : i ∈ S
  · have h : (fun ω : Config V => i ∈ ω ∩ S) = fun ω => i ∈ ω := by
      funext ω
      simp only [Set.mem_inter_iff, hi, and_true]
    rw [h]
    exact measurable_set_mem i
  · have h : (fun ω : Config V => i ∈ ω ∩ S) = fun _ => False := by
      funext ω
      simp only [Set.mem_inter_iff, hi, and_false]
    rw [h]
    exact measurable_const

/-- Membership of a single pair is a measurable event. -/
theorem measurableSet_mem_pair (e : Sym2 V) : MeasurableSet {ω : Config V | e ∈ ω} := by
  have heq : {ω : Config V | e ∈ ω}
      = {ω : Config V | ((({e} : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω)} := by
    ext ω
    simp
  rw [heq]
  exact measurableSet_setOf_finset_subset' {e}

/-- **Measurability of the pruned cluster volume** (the (R4.2) gap): the `blockT`
deletion `ω ↦ ω ∩ blockT o` is measurable (`measurable_inter_const`) and the cluster
volume is measurable in the configuration (`measurable_encard_cluster`). -/
theorem measurable_prunedVol (o y : V) : Measurable (prunedVol o y) :=
  ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
      (measurable_encard_cluster y)).comp
    (measurable_inter_const (blockT o))

/-- The pruned cluster sits inside the full cluster, so its volume is no larger. -/
theorem prunedVol_le_clusterVol (o y : V) (ω : Config V) :
    prunedVol o y ω ≤ ((cluster ω y).encard : ℝ≥0∞) :=
  ENat.toENNReal_le.mpr (Set.encard_le_encard (cluster_mono Set.inter_subset_left y))

/-- The edge at the root is not an internal edge of the pruned graph. -/
theorem sdiff_singleton_inter_blockT (o y : V) (ω : Config V) :
    (ω \ {s(o, y)}) ∩ blockT o = ω ∩ blockT o := by
  have h : s(o, y) ∉ blockT o := fun hc => hc (Sym2.mem_mk_left o y)
  ext z
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
  exact ⟨fun hz => ⟨hz.1.1, hz.2⟩, fun hz => ⟨⟨hz.1, fun hze => h (hze ▸ hz.2)⟩, hz.2⟩⟩

/-- The pruned cluster of `y` does not see the edge `{o,y}`: it is determined by the
coordinates other than that edge.  This is the hypothesis the accepted single-coordinate
factorisation lemma consumes. -/
theorem prunedVol_sdiff_determined (o y : V) (ω : Config V) :
    prunedVol o y ω = prunedVol o y (ω \ {s(o, y)}) := by
  simp only [prunedVol, sdiff_singleton_inter_blockT]

/-! ## The offspring sum of the renewal -/

theorem measurable_offspringTerm (o y : V) : Measurable (offspringTerm o y) := by
  classical
  by_cases hy : y = o
  · have hzero : offspringTerm o y = fun _ => (0 : ℝ≥0∞) := by
      funext ω
      simp only [offspringTerm, hy, ne_eq, not_true_eq_false, false_and, if_false]
    rw [hzero]
    exact measurable_const
  · have hfun : offspringTerm o y
        = fun ω : Config V => if s(o, y) ∈ ω then prunedVol o y ω else 0 := by
      funext ω
      simp only [offspringTerm, hy, ne_eq, not_false_eq_true, true_and]
    rw [hfun]
    exact Measurable.ite (measurableSet_mem_pair (s(o, y))) (measurable_prunedVol o y)
      measurable_const

theorem measurable_offspring (o : V) : Measurable (offspring o) :=
  Measurable.ennreal_tsum fun y => measurable_offspringTerm o y

/-- The renewal decomposition in the shape the moment recursion consumes. -/
theorem cluster_vol_le_one_add_offspring (o : V) (ω : Config V) :
    ((cluster ω o).encard : ℝ≥0∞) ≤ 1 + offspring o ω :=
  encard_cluster_le_offspring ω o

theorem pow_le_pow_offspring (o : V) (k : ℕ) (ω : Config V) :
    (((cluster ω o).encard : ℝ≥0∞)) ^ k ≤ (1 + offspring o ω) ^ k :=
  pow_le_pow_left' (cluster_vol_le_one_add_offspring o ω) k

/-! ## The multi-coordinate independence lemma (weighted tuple sums) -/

theorem sdiff_singleton_sdiff_insert_coe (a : Sym2 V) (s : Finset (Sym2 V))
    (ω : Config V) :
    (ω \ {a}) \ (((insert a s : Finset (Sym2 V)) : Set (Sym2 V)))
      = ω \ (((insert a s : Finset (Sym2 V)) : Set (Sym2 V))) := by
  have ha : a ∈ (((insert a s : Finset (Sym2 V)) : Set (Sym2 V))) := by
    simp
  ext z
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  exact ⟨fun hz => ⟨hz.1.1, hz.2⟩,
    fun hz => ⟨⟨hz.1, fun hze => hz.2 (by rw [hze]; exact ha)⟩, hz.2⟩⟩

theorem sdiff_coe_sdiff_insert_coe (a : Sym2 V) (s : Finset (Sym2 V))
    (ω : Config V) :
    (ω \ (s : Set (Sym2 V))) \ (((insert a s : Finset (Sym2 V)) : Set (Sym2 V)))
      = ω \ (((insert a s : Finset (Sym2 V)) : Set (Sym2 V))) := by
  have hsub : (s : Set (Sym2 V)) ⊆ (((insert a s : Finset (Sym2 V)) : Set (Sym2 V))) := by
    intro z hz
    exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hz))
  ext z
  simp only [Set.mem_sdiff]
  exact ⟨fun hz => ⟨hz.1.1, hz.2⟩,
    fun hz => ⟨⟨hz.1, fun hzs => hz.2 (hsub hzs)⟩, hz.2⟩⟩

/-- **Finite-set factorisation of a cluster-moment tuple sum.**  Averaging the
indicator that every edge of a finite set `F` is open against a function `G` that does
not see those edges costs exactly the product of the intensities.  Proved by induction
on `F` from the accepted single-coordinate lemma
`lintegral_indicator_mul_of_sdiff_determined`. -/
theorem lintegral_prod_indicator_mul_of_sdiff_determined
    (π : Sym2 V → unitInterval) (F : Finset (Sym2 V)) {G : Config V → ℝ≥0∞}
    (hG : Measurable G) (hdet : ∀ ω : Config V, G ω = G (ω \ (F : Set (Sym2 V)))) :
    ∫⁻ ω, (∏ e ∈ F, edgeInd e ω) * G ω ∂(law π)
      = ((∏ e ∈ F, unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞)
          * ∫⁻ ω, G ω ∂(law π) := by
  classical
  revert hG hdet
  refine Finset.induction_on F ?_ ?_
  · intro hG hdet
    simp
  · intro a s ha ih hG hdet
    have hdet_a : ∀ ω : Config V, G ω = G (ω \ {a}) := by
      intro ω
      rw [hdet ω, hdet (ω \ {a}), sdiff_singleton_sdiff_insert_coe]
    have hdet_s : ∀ ω : Config V, G ω = G (ω \ (s : Set (Sym2 V))) := by
      intro ω
      rw [hdet ω, hdet (ω \ (s : Set (Sym2 V))), sdiff_coe_sdiff_insert_coe]
    have hprod_gen : ∀ (ω η : Config V), (∀ e : Sym2 V, e ≠ a → (e ∈ ω ↔ e ∈ η)) →
        (∏ e ∈ s, edgeInd e ω) = (∏ e ∈ s, edgeInd e η) := by
      intro ω η hagree
      refine Finset.prod_congr rfl fun e he => ?_
      have hne : e ≠ a := fun h => ha (h ▸ he)
      have hiff : (e ∈ ω) ↔ (e ∈ η) := hagree e hne
      have h := if_congr hiff (rfl : (1 : ℝ≥0∞) = 1) (rfl : (0 : ℝ≥0∞) = 0)
      exact h
    have hdet_H : ∀ ω : Config V,
        (∏ e ∈ s, edgeInd e ω) * G ω
          = (∏ e ∈ s, edgeInd e (ω \ {a})) * G (ω \ {a}) := by
      intro ω
      rw [hprod_gen ω (ω \ {a}) (fun e hne => ?_), hdet_a ω]
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨h, hne⟩, fun h => h.1⟩
    have hmeas_ind : ∀ e : Sym2 V, Measurable (edgeInd e) := by
      intro e
      have hfun : edgeInd e = fun ω : Config V => if e ∈ ω then (1 : ℝ≥0∞) else 0 := rfl
      rw [hfun]
      exact Measurable.ite (measurableSet_mem_pair e) measurable_const measurable_const
    have hH : Measurable fun ω : Config V => (∏ e ∈ s, edgeInd e ω) * G ω :=
      (Finset.measurable_prod s fun e _ => hmeas_ind e).mul hG
    have hkey : ∀ ω : Config V,
        (∏ e ∈ insert a s, edgeInd e ω) * G ω
          = (if a ∈ ω then (∏ e ∈ s, edgeInd e ω) * G ω else 0) := by
      intro ω
      rw [Finset.prod_insert ha]
      by_cases h : a ∈ ω
      · simp only [h, edgeInd, if_true, one_mul]
      · simp only [h, edgeInd, if_false, zero_mul]
    calc ∫⁻ ω, (∏ e ∈ insert a s, edgeInd e ω) * G ω ∂(law π)
        = ∫⁻ ω, (if a ∈ ω then (∏ e ∈ s, edgeInd e ω) * G ω else 0) ∂(law π) :=
          lintegral_congr hkey
      _ = ((unitInterval.toNNReal (π a) : ℝ≥0) : ℝ≥0∞)
            * ∫⁻ ω, (∏ e ∈ s, edgeInd e ω) * G ω ∂(law π) :=
          lintegral_indicator_mul_of_sdiff_determined π a hH hdet_H
      _ = ((unitInterval.toNNReal (π a) : ℝ≥0) : ℝ≥0∞)
            * (((∏ e ∈ s, unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞)
              * ∫⁻ ω, G ω ∂(law π)) := by rw [ih hG hdet_s]
      _ = ((∏ e ∈ insert a s, unitInterval.toNNReal (π e) : ℝ≥0) : ℝ≥0∞)
            * ∫⁻ ω, G ω ∂(law π) := by
          rw [Finset.prod_insert ha, ENNReal.coe_mul, mul_assoc]

/-! ## The uniform row sum -/

/-! ## The exact first moment of the offspring sum -/

/-- **Exact first moment of the offspring sum.**  The single-coordinate lemma turns each
open-edge indicator into its intensity, leaving the pruned first moment. -/
theorem lintegral_offspring_eq (π : Sym2 V → unitInterval) (o : V) :
    ∫⁻ ω, offspring o ω ∂(law π)
      = ∑' y : V,
          (if y = o then 0 else (unitInterval.toNNReal (π s(o, y)) : ℝ≥0∞))
            * ∫⁻ ω, prunedVol o y ω ∂(law π) := by
  classical
  unfold offspring
  rw [lintegral_tsum fun y => (measurable_offspringTerm o y).aemeasurable]
  refine tsum_congr fun y => ?_
  by_cases hy : y = o
  · have hzero : offspringTerm o y = fun _ => (0 : ℝ≥0∞) := by
      funext ω
      simp only [offspringTerm, hy, ne_eq, not_true_eq_false, false_and, if_false]
    rw [hzero, lintegral_zero]
    simp [hy]
  · have hstep : offspringTerm o y
        = fun ω => (if s(o, y) ∈ ω then prunedVol o y ω else 0) := by
      funext ω
      simp only [offspringTerm, hy, ne_eq, not_false_eq_true, true_and]
    rw [hstep, lintegral_indicator_mul_of_sdiff_determined π (s(o, y))
      (measurable_prunedVol o y) (prunedVol_sdiff_determined o y)]
    simp only [hy, if_false]

/-- **The order-`1` input of the moment recursion**: the offspring sum has finite first
moment, bounded by `m (1 - m)⁻¹` from the uniform row sum alone. -/
theorem lintegral_offspring_le (π : Sym2 V → unitInterval) (o : V) (m : ℝ≥0∞)
    (hrow : ∀ v, rowSum π v ≤ m) (hm : m < 1) :
    ∫⁻ ω, offspring o ω ∂(law π) ≤ m * (1 - m)⁻¹ := by
  classical
  rw [lintegral_offspring_eq]
  have hI : ∀ y : V, ∫⁻ ω, prunedVol o y ω ∂(law π) ≤ (1 - m)⁻¹ := fun y =>
    (lintegral_mono fun ω => prunedVol_le_clusterVol o y ω).trans
      (chi_le_inv_one_sub_of_rowSum π m hrow hm y)
  calc ∑' y : V, (if y = o then 0 else (unitInterval.toNNReal (π s(o, y)) : ℝ≥0∞))
        * ∫⁻ ω, prunedVol o y ω ∂(law π)
      ≤ ∑' y : V, (if y = o then 0 else (unitInterval.toNNReal (π s(o, y)) : ℝ≥0∞))
          * (1 - m)⁻¹ :=
        ENNReal.tsum_le_tsum fun y => mul_le_mul_of_nonneg_left (hI y) zero_le
    _ = (∑' y : V, (if y = o then 0
          else (unitInterval.toNNReal (π s(o, y)) : ℝ≥0∞))) * (1 - m)⁻¹ :=
        ENNReal.tsum_mul_right
    _ = rowSum π o * (1 - m)⁻¹ := by simp [rowSum]
    _ ≤ m * (1 - m)⁻¹ := mul_le_mul_of_nonneg_right (hrow o) zero_le

/-- Hence the offspring sum has finite expectation, uniformly in the root. -/
theorem lintegral_offspring_ne_top (π : Sym2 V → unitInterval) (o : V) (m : ℝ≥0∞)
    (hrow : ∀ v, rowSum π v ≤ m) (hm : m < 1) :
    ∫⁻ ω, offspring o ω ∂(law π) ≠ ⊤ := by
  have h1m : (1 : ℝ≥0∞) - m ≠ 0 := by
    rw [Ne, tsub_eq_zero_iff_le]
    exact not_le.mpr hm
  have hm_top : m ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hm le_top)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hm_top (ENNReal.inv_ne_top.mpr h1m))
    (lintegral_offspring_le π o m hrow hm)

/-! ## The binomial split of the `k`-th cluster moment -/

theorem one_add_pow_eq_sum (Y : ℝ≥0∞) (k : ℕ) :
    (1 + Y) ^ k = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) * Y ^ j := by
  rw [add_comm 1 Y, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, mul_comm]

/-- **The binomial step of the moment recursion.**  The `k`-th cluster moment is at most
the binomial average of the offspring moments, with the `j = k` term present: this is
(R4.3) without the recursion, which cannot close (see
`offspring_second_moment_exceeds_row_sum`). -/
theorem lintegral_cluster_pow_le_sum (π : Sym2 V → unitInterval) (o : V) (k : ℕ) :
    ∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞)) ^ k ∂(law π)
      ≤ ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ≥0∞) * ∫⁻ ω, (offspring o ω) ^ j ∂(law π) := by
  have hstep : ∫⁻ ω, (((cluster ω o).encard : ℝ≥0∞)) ^ k ∂(law π)
      ≤ ∫⁻ ω, (1 + offspring o ω) ^ k ∂(law π) :=
    lintegral_mono fun ω => pow_le_pow_offspring o k ω
  refine hstep.trans (le_of_eq ?_)
  have hcongr : ∀ ω : Config V, (1 + offspring o ω) ^ k
      = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) * (offspring o ω) ^ j :=
    fun ω => one_add_pow_eq_sum (offspring o ω) k
  rw [lintegral_congr hcongr]
  have hmeas : ∀ j ∈ Finset.range (k + 1), Measurable
      (fun ω : Config V => (k.choose j : ℝ≥0∞) * (offspring o ω) ^ j) := by
    intro j _
    exact Measurable.const_mul (Measurable.pow_const (measurable_offspring o) j) _
  rw [MeasureTheory.lintegral_finsetSum _ hmeas]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact lintegral_const_mul _ (Measurable.pow_const (measurable_offspring o) j)

/-! ## The obstruction to the reported recursion coefficients -/

/-- **Arithmetic core of the obstruction.**  Take two independent open edges at the root
with intensities `p₁ = p₂ = 2/5`, hence row sum `m = 4/5 < 1`, and unit offspring sizes
`a_y ≡ A`.  Then `N = B₁ + B₂` has `E[N] = m` and
`E[N²] = m + m² - p₁² - p₂² = 28/25 > 1`, so `E[Y²] = A² E[N²] > A² m`.  Hence the
coefficients `m`, `m^k` and `m/(k - (k-1) m)` claimed for the offspring moment recursion
in the accepted report are unattainable from the row sum alone: the reported bounds are
false already at `k = 2`. -/
theorem offspring_second_moment_exceeds_row_sum :
    (4 / 5 : ℝ) < 1
      ∧ 1 < (4 / 5 + (4 / 5) ^ 2 - 2 * (2 / 5) ^ 2 : ℝ)
      ∧ (4 / 5 : ℝ) < 4 / 5 + (4 / 5) ^ 2 - 2 * (2 / 5) ^ 2
      ∧ (4 / 5 : ℝ) / (2 - 4 / 5) < 4 / 5 + (4 / 5) ^ 2 - 2 * (2 / 5) ^ 2 := by
  norm_num

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.MomentRecursion.cluster_mono
#print axioms PercLib.CriticalLRP.MomentRecursion.measurable_inter_const
#print axioms PercLib.CriticalLRP.MomentRecursion.measurable_prunedVol
#print axioms PercLib.CriticalLRP.MomentRecursion.prunedVol_sdiff_determined
#print axioms PercLib.CriticalLRP.MomentRecursion.measurable_offspring
#print axioms PercLib.CriticalLRP.MomentRecursion.cluster_vol_le_one_add_offspring
#print axioms PercLib.CriticalLRP.MomentRecursion.lintegral_prod_indicator_mul_of_sdiff_determined
#print axioms PercLib.CriticalLRP.MomentRecursion.lintegral_offspring_eq
#print axioms PercLib.CriticalLRP.MomentRecursion.lintegral_offspring_le
#print axioms PercLib.CriticalLRP.MomentRecursion.lintegral_offspring_ne_top
#print axioms PercLib.CriticalLRP.MomentRecursion.one_add_pow_eq_sum
#print axioms PercLib.CriticalLRP.MomentRecursion.lintegral_cluster_pow_le_sum
#print axioms PercLib.CriticalLRP.MomentRecursion.offspring_second_moment_exceeds_row_sum
