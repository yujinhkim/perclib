/-
Exact nearest-neighbour bond percolation on the integer line. New specialization of
PercLib's forest path formula and pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
The canonical law on unordered pairs is retained, with arbitrary diagonal marginals.
-/
module

public import PercLib.Percolation.Bond.Forest
public import PercLib.Percolation.Bond.Intensity
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section
noncomputable section

open MeasureTheory PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal Classical

namespace PercLib.Models.Line

/-- Translate a finite segment of the natural ray into the integer line. -/
theorem exists_hasse_int_path (a : ℤ) (n : ℕ) :
    ∃ p : (SimpleGraph.hasse ℤ).Path a (a + n), p.1.length = n := by
  obtain ⟨p, hlen, _⟩ := exists_hasse_nat_path (Nat.zero_le n)
  let f : SimpleGraph.hasse ℕ →g SimpleGraph.hasse ℤ :=
    { toFun := fun m => a + m
      map_rel' := by
        intro m n h
        simp only [SimpleGraph.hasse_adj, Nat.covBy_iff_add_one_eq] at h
        simp only [SimpleGraph.hasse_adj, Order.covBy_iff_add_one_eq]
        rcases h with h | h <;> omega }
  have hf : Function.Injective f := by intro m n h; dsimp [f] at h; omega
  have hp := p.2.map hf
  refine ⟨⟨(p.1.map f).copy (by simp [f]) rfl, ?_⟩, ?_⟩
  · exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr hp
  · simpa using hlen

/-- A line profile is supported almost surely on the integer Hasse graph, regardless of loops. -/
theorem ae_openGraph_le_hasse_int (p : unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0) :
    ∀ᵐ ω ∂law q, openGraph ω ≤ SimpleGraph.hasse ℤ := by
  filter_upwards [ae_config_subset_positive q] with ω hω
  intro a b hab
  obtain ⟨he, hne⟩ := (openGraph_adj_iff ω a b).mp hab
  have hp : 0 < q s(a, b) := hω he
  rw [hq a b hne] at hp
  have hd : |b - a| = 1 := by by_contra h; simp [h] at hp
  simp only [SimpleGraph.hasse_adj, Order.covBy_iff_add_one_eq]
  rcases abs_eq (show (0 : ℤ) ≤ 1 by decide) |>.mp hd with h | h <;> omega

/-- The two-point function on the integer line, for increasing endpoints. -/
theorem tau_eq_pow_of_le (p : unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0)
    {a b : ℤ} (hab : a ≤ b) :
    tau q a b = (unitInterval.toNNReal p : ℝ≥0∞) ^ (b - a).natAbs := by
  obtain ⟨r₀, hlen₀⟩ := exists_hasse_int_path a (b - a).natAbs
  have habs : a + ((b - a).natAbs : ℤ) = b := by
    rw [Int.natCast_natAbs, abs_of_nonneg (sub_nonneg.mpr hab)]
    omega
  let r : (SimpleGraph.hasse ℤ).Path a b :=
    ⟨r₀.1.copy rfl habs, (SimpleGraph.Walk.isPath_copy _ _ _).mpr r₀.2⟩
  have hlen : r.1.length = (b - a).natAbs := by simpa [r] using hlen₀
  have hprob : ∀ e ∈ r.1.edges.toFinset, q e = p := by
    intro e he
    induction e using Sym2.ind with | _ x y =>
    have ha := r.1.adj_of_mem_edges (List.mem_toFinset.mp he)
    have hne := ha.ne
    simp only [SimpleGraph.hasse_adj, Order.covBy_iff_add_one_eq] at ha
    rw [hq x y hne, ite_eq_left]
    rcases ha with h | h
    · have : y - x = 1 := by omega
      simp [this]
    · have : y - x = -1 := by omega
      simp [this]
  calc
    _ = ∏ e ∈ r.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) := by
      convert tau_eq_prod_of_ae_le_acyclic q (SimpleGraph.isAcyclic_hasse_of_linearOrder ℤ)
        (ae_openGraph_le_hasse_int p q hq) r using 1
      congr 1
      ext e
      simp only [List.mem_toFinset]
    _ = ∏ _e ∈ r.1.edges.toFinset, (unitInterval.toNNReal p : ℝ≥0∞) :=
      Finset.prod_congr rfl (fun e he => congrArg
        (fun u : unitInterval => (unitInterval.toNNReal u : ℝ≥0∞)) (hprob e he))
    _ = _ := by
      rw [Finset.prod_const, List.toFinset_card_of_nodup r.2.isTrail.edges_nodup,
        SimpleGraph.Walk.length_edges, hlen]

/-- Exact two-point function, including coincident roots and both parameter endpoints. -/
theorem tau_eq_pow (p : unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0) (a b : ℤ) :
    tau q a b = (unitInterval.toNNReal p : ℝ≥0∞) ^ (b - a).natAbs := by
  rcases le_total a b with h | h
  · exact tau_eq_pow_of_le p q hq h
  · rw [tau_comm, tau_eq_pow_of_le p q hq h, ← Int.natAbs_neg (a - b), neg_sub]

/-- The exact susceptibility. At p = 1 this expression is infinity. -/
theorem chi_eq (p : unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0) (a : ℤ) :
    chi q a = (1 + (unitInterval.toNNReal p : ℝ≥0∞)) /
      (1 - (unitInterval.toNNReal p : ℝ≥0∞)) := by
  rw [chi_eq_tsum_tau]
  simp_rw [tau_eq_pow p q hq]
  rw [← (Equiv.addLeft a).tsum_eq]
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have hn (n : ℕ) : (-(↑n + 1) : ℤ).natAbs = n + 1 := by omega
  simp only [Int.natAbs_natCast, hn, pow_succ, ENNReal.tsum_mul_right,
    ENNReal.tsum_geometric]
  rw [div_eq_mul_inv]
  ring

/-- Susceptibility is finite at every subunit nearest-neighbour probability. -/
theorem chi_lt_top (p : unitInterval) (hp : p < 1) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0) (a : ℤ) :
    chi q a < ⊤ := by
  rw [chi_eq p q hq]
  apply ENNReal.div_lt_top (by finiteness)
  exact ne_of_gt (tsub_pos_of_lt (by exact_mod_cast hp))

/-- Every cluster is finite almost surely below p = 1. -/
theorem ae_all_clusters_finite (p : unitInterval) (hp : p < 1) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0) :
    ∀ᵐ ω ∂law q, ∀ a, (cluster ω a).Finite := by
  rw [ae_all_iff]
  intro a
  have hm : Measurable (fun ω : Config ℤ => ((cluster ω a).encard : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster a)
  have h := ae_lt_top hm (chi_lt_top p hp q hq a).ne
  filter_upwards [h] with ω hω
  exact Set.encard_lt_top_iff.mp (ENat.toENNReal_lt_top.mp hω)

/-- No root percolates below p = 1. -/
theorem law_cluster_infinite_eq_zero (p : unitInterval) (hp : p < 1) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0) (a : ℤ) :
    law q {ω | (cluster ω a).Infinite} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_all_clusters_finite p hp q hq] with ω hω
  exact fun h => h (hω a)

/-- No infinite cluster exists anywhere below p = 1. -/
theorem law_exists_infinite_eq_zero (p : unitInterval) (hp : p < 1) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0) :
    law q {ω | ∃ a, (cluster ω a).Infinite} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_all_clusters_finite p hp q hq] with ω hω
  rintro ⟨a, ha⟩
  exact ha (hω a)

/-- At p = 1, every vertex lies in the root cluster almost surely. -/
theorem ae_cluster_eq_univ (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then 1 else 0) (a : ℤ) :
    ∀ᵐ ω ∂law q, cluster ω a = Set.univ := by
  have hconn (b : ℤ) : ∀ᵐ ω ∂law q, ω ∈ conn a b := by
    apply (mem_ae_iff_prob_eq_one (measurableSet_conn a b)).mpr
    change tau q a b = 1
    simp [tau_eq_pow 1 q hq]
  filter_upwards [ae_all_iff.mpr hconn] with ω hω
  exact Set.eq_univ_of_forall (fun b => hω b)

/-- At p = 1 the root percolates with probability one. -/
theorem law_cluster_infinite_eq_one (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then 1 else 0) (a : ℤ) :
    law q {ω | (cluster ω a).Infinite} = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_cluster_infinite a)).mp
  filter_upwards [ae_cluster_eq_univ q hq a] with ω hω
  simpa only [hω] using Set.infinite_univ

/-- At p = 1 the susceptibility is infinite. -/
theorem chi_eq_top (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then 1 else 0) (a : ℤ) :
    chi q a = ⊤ := by
  norm_num [chi_eq 1 q hq, ENNReal.div_eq_top]

/-- Every finite intensity of the unit-rate nearest-neighbour kernel is subcritical. -/
theorem law_exists_infinite_intensity_eq_zero (J : Sym2 ℤ → ℝ≥0)
    (hJ : ∀ a b, a ≠ b → J s(a, b) = if |b - a| = 1 then 1 else 0) (β : ℝ≥0) :
    law (intensityProfile J β) {ω | ∃ a, (cluster ω a).Infinite} = 0 := by
  let p : unitInterval := intensityProfile (fun _ : Sym2 ℤ => 1) β s(0, 1)
  have hp : p < 1 := by
    change 1 - Real.exp (-(β : ℝ) * 1) < 1
    linarith [Real.exp_pos (-(β : ℝ) * 1)]
  apply law_exists_infinite_eq_zero p hp
  intro a b hab
  apply Subtype.ext
  change 1 - Real.exp (-(β : ℝ) * (J s(a, b) : ℝ)) = _
  rw [hJ a b hab]
  split_ifs with h
  · rfl
  · simp

/-- No finite intensity percolates, so the root critical intensity is infinity. -/
theorem rootCriticalIntensity_eq_top (J : Sym2 ℤ → ℝ≥0)
    (hJ : ∀ a b, a ≠ b → J s(a, b) = if |b - a| = 1 then 1 else 0) (a : ℤ) :
    rootCriticalIntensity J a = ⊤ := by
  apply top_le_iff.mp
  apply le_sInf
  rintro b ⟨β, rfl, hpos⟩
  have hz : law (intensityProfile J β) {ω | (cluster ω a).Infinite} = 0 :=
    measure_mono_null (show {ω | (cluster ω a).Infinite} ⊆ {ω | ∃ x, (cluster ω x).Infinite}
      from fun ω h => ⟨a, h⟩) (law_exists_infinite_intensity_eq_zero J hJ β)
  exact (hpos.ne' hz).elim

/-- The global critical intensity is also infinity. -/
theorem globalCriticalIntensity_eq_top (J : Sym2 ℤ → ℝ≥0)
    (hJ : ∀ a b, a ≠ b → J s(a, b) = if |b - a| = 1 then 1 else 0) :
    globalCriticalIntensity J = ⊤ := by
  apply top_le_iff.mp
  apply le_sInf
  rintro b ⟨β, rfl, hpos⟩
  exact (hpos.ne' (law_exists_infinite_intensity_eq_zero J hJ β)).elim

-- Every parameter and every diagonal profile inhabit the model assumptions.
example (p : unitInterval) (d : ℤ → unitInterval) :
    ∃ q : Sym2 ℤ → unitInterval,
      (∀ a, q s(a, a) = d a) ∧
      (∀ a b, tau q a b = (unitInterval.toNNReal p : ℝ≥0∞) ^ (b - a).natAbs) ∧
      (∀ a, chi q a = (1 + (unitInterval.toNNReal p : ℝ≥0∞)) /
        (1 - (unitInterval.toNNReal p : ℝ≥0∞))) := by
  let q : Sym2 ℤ → unitInterval := Sym2.lift ⟨fun a b =>
    if a = b then d a else if |b - a| = 1 then p else 0, by
      intro a b
      dsimp
      by_cases h : a = b
      · subst b; rfl
      · simp [h, Ne.symm h, abs_sub_comm]⟩
  have hq (a b : ℤ) (h : a ≠ b) : q s(a, b) = if |b - a| = 1 then p else 0 := by
    simp [q, h]
  exact ⟨q, (by intro a; simp [q]), tau_eq_pow p q hq, chi_eq p q hq⟩

-- The root term survives at p = 0.
example (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = 0) (a : ℤ) : chi q a = 1 := by
  have h : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then (0 : unitInterval) else 0 := by
    simpa using hq
  simp [chi_eq 0 q h]

-- A nonzero unit-rate kernel has infinite critical intensity, not just the zero kernel.
example : ∃ J : Sym2 ℤ → ℝ≥0, J s(0, 1) = 1 ∧
    globalCriticalIntensity J = ⊤ ∧ ∀ a, rootCriticalIntensity J a = ⊤ := by
  let J : Sym2 ℤ → ℝ≥0 := Sym2.lift ⟨fun a b => if |b - a| = 1 then 1 else 0,
    fun a b => by dsimp; rw [abs_sub_comm]⟩
  have hJ (a b : ℤ) (_ : a ≠ b) : J s(a, b) = if |b - a| = 1 then 1 else 0 := rfl
  exact ⟨J, by norm_num [J], globalCriticalIntensity_eq_top J hJ,
    rootCriticalIntensity_eq_top J hJ⟩

end PercLib.Models.Line
