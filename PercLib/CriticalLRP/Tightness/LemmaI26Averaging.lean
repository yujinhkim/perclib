/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.2.6: the lattice-averaging step and the full chain

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.2.6 (p. 24) and its proof:

  `E_{β,r}|K|^p ≥ E_{β,r}|K ∩ B_{2r}|^p ≥ (M_{β,r}-1)^p P_{β,r}(|K ∩ B_{2r}| ≥ M_{β,r}-1)
      ≥ (M_{β,r}-1)^{p+1}/(e |B_r|)`   for every `β, r ≥ 0`, `p ≥ 1`,

where `K` is the cluster of the origin and `M_{β,r}` is the edian of `|K_max(B_r)|`.

The first two inequalities are trivial/markovian.  The third is the paper's
"transitivity" step, which is *translation averaging* and not transitivity of `Z^d` on
`B_r` (the latter is false).  The deterministic input is:

  if some cluster `C` has `|C ∩ B_r| ≥ m`, then every `x ∈ C ∩ B_r` satisfies
  `|K_x ∩ B_{2r}(x)| ≥ m`,

because `C ∩ B_r ⊆ K_x` (clusters are equal or disjoint) and `B_r ⊆ B_{2r}(x)` for `x ∈ B_r`
(triangle inequality `‖y - x‖ ≤ ‖y‖ + ‖x‖ ≤ 2r`).  Averaging over the `|B_r|` translates of
the event and using translation invariance of the law gives
`P(|K ∩ B_{2r}| ≥ m) ≥ (m/e)/|B_r|`.

Geometry: we work with the sup-norm lattice balls `B_n(x) = {y : ‖y - x‖_∞ ≤ n}` for natural
`n`, matching the existing `ℕ`-indexed `FiniteVolume.box d n` API.  For real `r ≥ 0` the lattice
ball `{y : ‖y - x‖_∞ ≤ r}` is exactly `B_{⌊r⌋}(x)` since `‖·‖_∞` is integer-valued on `Z^d`;
see `latticeBallR_eq_latticeBall` and `card_latticeBallR` (`|B_r| = (2⌊r⌋+1)^d`).

Everything below is *unconditional* for a translation-invariant probability law: no tail
hypothesis (I.2.6), no subcriticality and no a.e. finiteness of clusters is needed, because the
window is finite and the moments are the `ℝ≥0∞`-valued lintegral.  The only hypothesis on the
law is translation invariance `μ.map (shiftConfig a) = μ`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Tightness.RealExponent
public import PercLib.CriticalLRP.CountableProduct.Lattice
public import PercLib.CriticalLRP.LatticeGeometry

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-! ## The sup norm on `ℤ^d` is a norm: triangle inequality and lattice balls -/

/-- The triangle inequality for the sup norm `‖y‖_∞ = max_i |y_i|` of `LatticeGeometry`. -/
theorem linfNorm_add_le (y z : Fin d → ℤ) :
    FiniteVolume.linfNorm (y + z) ≤ FiniteVolume.linfNorm y + FiniteVolume.linfNorm z := by
  rw [FiniteVolume.linfNorm_le_iff]
  intro i
  have hy : (y i).natAbs ≤ FiniteVolume.linfNorm y :=
    FiniteVolume.linfNorm_le_iff.mp le_rfl i
  have hz : (z i).natAbs ≤ FiniteVolume.linfNorm z :=
    FiniteVolume.linfNorm_le_iff.mp le_rfl i
  calc ((y + z) i).natAbs = (y i + z i).natAbs := rfl
    _ ≤ (y i).natAbs + (z i).natAbs := Int.natAbs_add_le _ _
    _ ≤ FiniteVolume.linfNorm y + FiniteVolume.linfNorm z := add_le_add hy hz

/-- `‖y - x‖_∞ ≤ ‖y‖_∞ + ‖x‖_∞`. -/
theorem linfNorm_sub_le (y x : Fin d → ℤ) :
    FiniteVolume.linfNorm (y - x) ≤ FiniteVolume.linfNorm y + FiniteVolume.linfNorm x := by
  have h : y - x = y + -x := by abel
  rw [h]
  calc FiniteVolume.linfNorm (y + -x)
      ≤ FiniteVolume.linfNorm y + FiniteVolume.linfNorm (-x) := linfNorm_add_le y (-x)
    _ = FiniteVolume.linfNorm y + FiniteVolume.linfNorm x := by rw [FiniteVolume.linfNorm_neg]

/-- The closed lattice ball `B_n(x) = {y ∈ ℤ^d : ‖y - x‖_∞ ≤ n}`. -/
noncomputable def latticeBall (n : ℕ) (x : Fin d → ℤ) : Set (Fin d → ℤ) :=
  {y | FiniteVolume.linfNorm (y - x) ≤ n}

theorem mem_latticeBall_iff {n : ℕ} {x y : Fin d → ℤ} :
    y ∈ latticeBall n x ↔ FiniteVolume.linfNorm (y - x) ≤ n := Iff.rfl

/-- `B_n(0)` is the box `B_n` of `LatticeGeometry`. -/
theorem latticeBall_zero (n : ℕ) :
    latticeBall (d := d) n 0 = ↑(FiniteVolume.box d n) := by
  ext y
  rw [mem_latticeBall_iff, sub_zero]
  exact FiniteVolume.mem_box_iff.symm

/-- Translating a ball of radius `n` by `a` translates the ball of radius `n` at `x`. -/
theorem latticeBall_shift (n : ℕ) (x a : Fin d → ℤ) :
    latticeBall n (x + a) = (fun y => y + a) '' latticeBall n x := by
  ext y
  rw [mem_latticeBall_iff, mem_image]
  constructor
  · intro h
    refine ⟨y - a, ?_, by abel⟩
    have hy : (y - a) - x = y - (x + a) := by abel
    rw [mem_latticeBall_iff, hy]
    exact h
  · rintro ⟨u, hu, rfl⟩
    have hy : (u + a) - (x + a) = u - x := by abel
    show FiniteVolume.linfNorm ((u + a) - (x + a)) ≤ n
    rw [hy]
    exact hu

/-- **`B_n ⊆ B_{2n}(x)` for `x ∈ B_n`**, by the triangle inequality. -/
theorem box_subset_latticeBall {n : ℕ} {x : Fin d → ℤ} (hx : x ∈ FiniteVolume.box d n) :
    (↑(FiniteVolume.box d n) : Set (Fin d → ℤ)) ⊆ latticeBall (2 * n) x := by
  intro y hy
  rw [mem_latticeBall_iff]
  have h1 : FiniteVolume.linfNorm (y - x) ≤
      FiniteVolume.linfNorm y + FiniteVolume.linfNorm x := linfNorm_sub_le y x
  have h2 : FiniteVolume.linfNorm y ≤ n := FiniteVolume.mem_box_iff.mp hy
  have h3 : FiniteVolume.linfNorm x ≤ n := FiniteVolume.mem_box_iff.mp hx
  omega

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-! ## The deterministic counting step

If a single cluster `C` occupies at least `m` points of `B_n`, then *at least* `m` points `x` of
`B_n` see `m` points of their own cluster inside `B_{2n}(x)`: namely all the points of `C ∩ B_n`.
-/

/-- The number of `x ∈ B_n` with `|K_x ∩ B_{2n}(x)| ≥ m`, as an `ℝ≥0∞`-valued sum of indicators. -/
noncomputable def ballClusterCount (m n : ℕ) (ω : Config (Fin d → ℤ)) : ℝ≥0∞ :=
  ∑ x ∈ FiniteVolume.box d n,
    if (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall (2 * n) x) then 1 else 0

theorem measurableSet_clusterVolIn_ge (m n : ℕ) (x : Fin d → ℤ) :
    MeasurableSet {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall n x)} :=
  measurableSet_le measurable_const (measurable_clusterVolIn x _)

theorem measurable_ballClusterCount (m n : ℕ) :
    Measurable (ballClusterCount (d := d) m n) := by
  refine Finset.measurable_sum _ fun x _ => ?_
  exact Measurable.ite (measurableSet_clusterVolIn_ge m (2 * n) x)
    measurable_const measurable_const

/-- **The geometric core of Lemma I.2.6.**  If `x` belongs to the cluster of `w` and `x ∈ B_n`,
then every point of `K_w ∩ B_n` lies in `K_x ∩ B_{2n}(x)`: the clusters are equal, and
`B_n ⊆ B_{2n}(x)` by the triangle inequality.  Hence

  `|K_x ∩ B_{2n}(x)| ≥ |K_w ∩ B_n|`. -/
theorem clusterVolIn_ball_two_mul_ge {ω : Config (Fin d → ℤ)} {w x : Fin d → ℤ} {n : ℕ}
    (hxw : x ∈ cluster ω w) (hx : x ∈ FiniteVolume.box d n) :
    clusterVolIn ω w ↑(FiniteVolume.box d n) ≤ clusterVolIn ω x (latticeBall (2 * n) x) := by
  have hcl : cluster ω x = cluster ω w := by
    rw [cluster_eq_iff]
    exact connects_symm (mem_cluster_iff.mp hxw)
  have hsub : cluster ω w ∩ ↑(FiniteVolume.box d n) ⊆ cluster ω x ∩ latticeBall (2 * n) x := by
    intro y hy
    exact ⟨by rw [hcl]; exact hy.1, box_subset_latticeBall hx hy.2⟩
  rw [clusterVolIn, clusterVolIn]
  exact_mod_cast Set.encard_mono hsub

/-- **Deterministic counting**: if some cluster has at least `m` points in `B_n`, then at least `m`
points `x` of `B_n` have `|K_x ∩ B_{2n}(x)| ≥ m`. -/
theorem le_ballClusterCount {m n : ℕ} {ω : Config (Fin d → ℤ)}
    (h : ∃ w ∈ FiniteVolume.box d n, (m : ℝ≥0∞) ≤ clusterVolIn ω w ↑(FiniteVolume.box d n)) :
    (m : ℝ≥0∞) ≤ ballClusterCount m n ω := by
  classical
  obtain ⟨w, hw, hle⟩ := h
  set S : Set (Fin d → ℤ) := cluster ω w ∩ ↑(FiniteVolume.box d n) with hS
  set T : Finset (Fin d → ℤ) := (FiniteVolume.box d n).filter
    (fun x => (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall (2 * n) x)) with hT
  have hSfin : S.Finite := (FiniteVolume.box d n).finite_toSet.subset Set.inter_subset_right
  have hle' : (m : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) := by
    rw [clusterVolIn] at hle
    rw [hS]
    exact hle
  -- every point of `S` lies in `B_n` and sees at least `m` points of its cluster in `B_{2n}`
  have hmem : ∀ x ∈ S, x ∈ FiniteVolume.box d n ∧
      (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall (2 * n) x) := by
    intro x hx
    obtain ⟨hxc, hxb⟩ := hx
    refine ⟨hxb, le_trans hle' ?_⟩
    have hS_eq : clusterVolIn ω w ↑(FiniteVolume.box d n) = (S.encard : ℝ≥0∞) := by
      rw [clusterVolIn, hS]
    have hmain := clusterVolIn_ball_two_mul_ge (ω := ω) (w := w) hxc hxb
    rwa [hS_eq] at hmain
  have hfilter : S ⊆ (T : Set (Fin d → ℤ)) := by
    intro x hx
    obtain ⟨hxb, hxm⟩ := hmem x hx
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hxb, hxm⟩)
  have hcard : S.ncard ≤ T.card := by
    have h1 : S.ncard ≤ (T : Set (Fin d → ℤ)).ncard :=
      Set.ncard_le_ncard hfilter T.finite_toSet
    rwa [Set.ncard_coe_finset] at h1
  simp only [ballClusterCount]
  rw [Finset.sum_boole]
  change (m : ℝ≥0∞) ≤ (T.card : ℝ≥0∞)
  calc (m : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) := hle'
    _ = (S.ncard : ℝ≥0∞) := encard_coe_eq_ncard_coe hSfin
    _ ≤ (T.card : ℝ≥0∞) := by exact_mod_cast hcard

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-! ## Translation invariance of the shifted events -/

/-- Translating the configuration by `a` shifts both the base point and the window of
`|K_x ∩ B_n(x)|`. -/
theorem clusterVolIn_shift (a : Fin d → ℤ) (ω : Config (Fin d → ℤ)) (x : Fin d → ℤ) (n : ℕ) :
    clusterVolIn (shiftConfig a ω) (x + a) (latticeBall n (x + a)) =
      clusterVolIn ω x (latticeBall n x) := by
  rw [clusterVolIn, clusterVolIn, cluster_shiftConfig, latticeBall_shift]
  congr 1
  rw [← Set.image_inter (f := fun u : Fin d → ℤ => u + a) (fun u v huv => by simpa using huv)]
  exact Set.InjOn.encard_image fun u _ v _ huv => by simpa using huv

/-- **Translation invariance of the probability of `{|K_x ∩ B_n(x)| ≥ m}`** for a
translation-invariant law. -/
theorem measure_clusterVolIn_ge_shift (μ : Measure (Config (Fin d → ℤ)))
    (hμ : ∀ a, μ.map (shiftConfig a) = μ) (m n : ℕ) (x : Fin d → ℤ) :
    μ {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall n x)} =
      μ {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (latticeBall n 0)} := by
  have hbase : MeasurableSet
      {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (latticeBall n 0)} :=
    measurableSet_clusterVolIn_ge m n 0
  have hgoal : MeasurableSet
      {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall n x)} :=
    measurableSet_clusterVolIn_ge m n x
  have hpre : shiftConfig x ⁻¹'
      {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall n x)} =
      {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (latticeBall n 0)} := by
    ext ω
    have hshift := clusterVolIn_shift (a := x) ω 0 n
    simp only [zero_add] at hshift
    show ((m : ℝ≥0∞) ≤ clusterVolIn (shiftConfig x ω) x (latticeBall n x)) ↔ _
    rw [hshift]
    exact Iff.rfl
  calc μ {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall n x)}
      = (μ.map (shiftConfig x)) {ω | (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall n x)} := by
        rw [hμ x]
    _ = μ (shiftConfig x ⁻¹' {ω | (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall n x)}) :=
        Measure.map_apply (measurable_shiftConfig x) hgoal
    _ = μ {ω | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (latticeBall n 0)} := by rw [hpre]

/-! ## The averaging bound -/

/-- **The translation-averaging step of Lemma I.2.6.**  If, with probability at least `e^{-1}`,
some cluster occupies at least `m` points of `B_n`, then

  `P(|K ∩ B_{2n}| ≥ m) ≥ (m/e)/|B_n|`.

Note `|K ∩ B_{2n}|` is the cluster of the origin, and `B_{2n} = B_{2n}(0)`. -/
theorem averaging_bound (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ.map (shiftConfig a) = μ) {m n : ℕ}
    (h : ENNReal.ofReal (Real.exp (-1)) ≤
      μ {ω : Config (Fin d → ℤ) |
        ∃ w ∈ FiniteVolume.box d n, (m : ℝ≥0∞) ≤ clusterVolIn ω w ↑(FiniteVolume.box d n)}) :
    ENNReal.ofReal (Real.exp (-1) * (m : ℝ) / ((FiniteVolume.box d n).card : ℝ)) ≤
      μ {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (latticeBall (2 * n) 0)} := by
  classical
  set A : Set (Config (Fin d → ℤ)) :=
    {ω | ∃ w ∈ FiniteVolume.box d n, (m : ℝ≥0∞) ≤ clusterVolIn ω w ↑(FiniteVolume.box d n)}
    with hA
  set B : Set (Config (Fin d → ℤ)) :=
    {ω | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (latticeBall (2 * n) 0)} with hB
  have hAmeas : MeasurableSet A := by
    have hset : A = ⋃ w ∈ FiniteVolume.box d n,
        {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω w ↑(FiniteVolume.box d n)} := by
      rw [hA]
      ext ω
      simp
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun w _ =>
      measurableSet_le measurable_const (measurable_clusterVolIn w _)
  -- pointwise: on `A` the count is at least `m`
  have hpoint : ∀ ω, (m : ℝ≥0∞) * (if ω ∈ A then (1 : ℝ≥0∞) else 0) ≤ ballClusterCount m n ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hω, ite_true, mul_one]
      exact le_ballClusterCount (by rwa [hA] at hω)
    · simp only [hω, ite_false, mul_zero]
      exact zero_le
  have hii : ∫⁻ ω, (if ω ∈ A then (1 : ℝ≥0∞) else 0) ∂μ = μ A := by
    have hbase := lintegral_indicator_one (μ := μ) hAmeas
    rw [← hbase]
    refine lintegral_congr fun ω => ?_
    rw [Set.indicator_apply]
    simp only [Pi.one_apply]
  have hconst : ∫⁻ ω, (m : ℝ≥0∞) * (if ω ∈ A then (1 : ℝ≥0∞) else 0) ∂μ = (m : ℝ≥0∞) * μ A := by
    rw [lintegral_const_mul' (m : ℝ≥0∞) (fun ω => if ω ∈ A then (1 : ℝ≥0∞) else 0)
      (ENNReal.natCast_ne_top m), hii]
  have h1 : (m : ℝ≥0∞) * μ A ≤ ∫⁻ ω, ballClusterCount m n ω ∂μ := by
    rw [← hconst]
    exact lintegral_mono hpoint
  -- evaluate the integral as a sum of shifted probabilities
  have h2 : ∫⁻ ω, ballClusterCount m n ω ∂μ =
      ∑ x ∈ FiniteVolume.box d n,
        μ {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall (2 * n) x)} := by
    have hfun : ballClusterCount m n = fun ω => ∑ x ∈ FiniteVolume.box d n,
        (if (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall (2 * n) x) then (1 : ℝ≥0∞) else 0) := rfl
    rw [hfun]
    rw [lintegral_finsetSum (FiniteVolume.box d n) (fun x _ => Measurable.ite
      (measurableSet_clusterVolIn_ge m (2 * n) x) measurable_const measurable_const)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h0 := lintegral_indicator_one (μ := μ) (measurableSet_clusterVolIn_ge m (2 * n) x)
    rw [← h0]
    refine lintegral_congr fun ω => ?_
    rw [Set.indicator_apply]
    simp only [Pi.one_apply, Set.mem_ofPred_eq]
  have h3 : (∑ x ∈ FiniteVolume.box d n,
        μ {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω x (latticeBall (2 * n) x)}) =
      ((FiniteVolume.box d n).card : ℝ≥0∞) *
        μ {ω : Config (Fin d → ℤ) |
          (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (latticeBall (2 * n) 0)} := by
    rw [Finset.sum_congr rfl fun x _ => measure_clusterVolIn_ge_shift μ hμ m (2 * n) x,
      Finset.sum_const, nsmul_eq_mul]
  have h4 : ENNReal.ofReal (Real.exp (-1)) * (m : ℝ≥0∞) ≤
      ((FiniteVolume.box d n).card : ℝ≥0∞) * μ B := by
    rw [← h3, ← h2]
    calc ENNReal.ofReal (Real.exp (-1)) * (m : ℝ≥0∞)
        = (m : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-1)) := mul_comm _ _
      _ ≤ (m : ℝ≥0∞) * μ A := by
          exact mul_le_mul_of_nonneg_left h (zero_le : (0 : ℝ≥0∞) ≤ (m : ℝ≥0∞))
      _ ≤ _ := h1
  -- transfer to `ℝ` and divide by `|B_n|`
  have hne_top : μ B ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono (subset_univ _))
  have hcard_pos : 0 < (FiniteVolume.box d n).card := by
    refine Finset.card_pos.mpr ⟨0, ?_⟩
    have h0 : FiniteVolume.linfNorm (0 : Fin d → ℤ) = 0 :=
      FiniteVolume.linfNorm_eq_zero_iff.mpr rfl
    rw [FiniteVolume.mem_box_iff, h0]
    exact Nat.zero_le n
  have hcard_ne : ((FiniteVolume.box d n).card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hrhs_top : ((FiniteVolume.box d n).card : ℝ≥0∞) * μ B ≠ ⊤ :=
    ENNReal.mul_ne_top hcard_ne hne_top
  have hreal : Real.exp (-1) * (m : ℝ) ≤
      ((FiniteVolume.box d n).card : ℝ) * (μ B).toReal := by
    have h5 := ENNReal.toReal_mono hrhs_top h4
    have h6 : (ENNReal.ofReal (Real.exp (-1)) * (m : ℝ≥0∞)).toReal
        = Real.exp (-1) * (m : ℝ) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos (-1)).le,
        ENNReal.toReal_natCast]
    have h7 : ((((FiniteVolume.box d n).card : ℝ≥0∞)) * μ B).toReal
        = ((FiniteVolume.box d n).card : ℝ) * (μ B).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    rw [h6, h7] at h5
    exact h5
  have hdiv : Real.exp (-1) * (m : ℝ) / ((FiniteVolume.box d n).card : ℝ) ≤ (μ B).toReal := by
    rw [div_le_iff₀ (by exact_mod_cast hcard_pos)]
    calc Real.exp (-1) * (m : ℝ)
        ≤ ((FiniteVolume.box d n).card : ℝ) * (μ B).toReal := hreal
      _ = (μ B).toReal * ((FiniteVolume.box d n).card : ℝ) := mul_comm _ _
  rw [ENNReal.ofReal_le_iff_le_toReal hne_top]
  exact hdiv

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-! ## From the edian to the hypothesis of the averaging bound -/

/-- `{|K_x ∩ W| ≥ m}` for `m ≥ 1`. -/
theorem le_clusterMaxVol_iff {V : Type*} [Countable V] {m : ℕ} (hm : 1 ≤ m) (W : Finset V)
    (ω : Config V) :
    ((m : ℝ≥0∞) ≤ clusterMaxVol ω W) ↔ ∃ w ∈ W, (m : ℝ≥0∞) ≤ clusterVolIn ω w ↑W := by
  constructor
  · intro h
    by_contra hcon
    have hall : ∀ w ∈ W, clusterVolIn ω w ↑W < (m : ℝ≥0∞) := by
      intro w hw
      exact lt_of_not_ge fun hle => hcon ⟨w, hw, hle⟩
    have hlt : clusterMaxVol ω W < (m : ℝ≥0∞) := by
      rw [clusterMaxVol]
      refine Finset.sup_lt_iff ?_ |>.mpr hall
      have : (0 : ℝ≥0∞) < (m : ℝ≥0∞) := by exact_mod_cast hm
      exact this
    exact absurd h (not_le.mpr hlt)
  · rintro ⟨w, hw, hle⟩
    exact le_trans hle (clusterVolIn_le_clusterMaxVol ω hw)

/-- **The edian gives the averaging hypothesis**: with probability at least `e^{-1}` some cluster
occupies `M_β(B_n) - 1` points of `B_n`.  This is the paper's "since such a cluster exists with
probability at least `1/e` by definition of `M_{β,r}`". -/
theorem edian_measure_exists (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    (n : ℕ) :
    ENNReal.ofReal (Real.exp (-1)) ≤
      μ {ω : Config (Fin d → ℤ) | ∃ w ∈ FiniteVolume.box d n,
        (((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _)) - 1 : ℕ) : ℝ≥0∞) ≤
          clusterVolIn ω w ↑(FiniteVolume.box d n)} := by
  classical
  set M : ℕ := edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) with hM
  have hMge : 1 ≤ M := hM ▸ one_le_edianMaxVol (FiniteVolume.box d n) (exists_edianMaxVol _)
  rcases Nat.lt_or_ge M 2 with hcase | hcase
  · -- `M = 1`: the event is everything, because `m = 0`
    have hM1 : M = 1 := by omega
    have hmem0 : (0 : Fin d → ℤ) ∈ FiniteVolume.box d n := by
      have h0 : FiniteVolume.linfNorm (0 : Fin d → ℤ) = 0 :=
        FiniteVolume.linfNorm_eq_zero_iff.mpr rfl
      rw [FiniteVolume.mem_box_iff, h0]
      exact Nat.zero_le n
    have huniv : {ω : Config (Fin d → ℤ) | ∃ w ∈ FiniteVolume.box d n,
        ((M - 1 : ℕ) : ℝ≥0∞) ≤ clusterVolIn ω w ↑(FiniteVolume.box d n)} = univ := by
      ext ω
      refine iff_true_intro ⟨0, hmem0, ?_⟩
      rw [hM1]
      simp
    rw [huniv, measure_univ]
    refine le_of_lt (ENNReal.ofReal_lt_one.mpr ?_)
    rw [Real.exp_lt_one_iff]
    norm_num
  · -- `M ≥ 2`, so `m = M - 1 ≥ 1` and minimality of the edian applies
    have hm : 1 ≤ M - 1 := by omega
    have hlt : M - 1 < edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) := by omega
    have hmin : ENNReal.ofReal (Real.exp (-1)) <
        μ {ω : Config (Fin d → ℤ) |
          ((M - 1 : ℕ) : ℝ≥0∞) ≤ clusterMaxVol ω (FiniteVolume.box d n)} :=
      edianOf_min (μ := μ) (X := fun ω => clusterMaxVol ω (FiniteVolume.box d n))
        (hex := exists_edianMaxVol (FiniteVolume.box d n)) hlt
    refine le_trans (le_of_lt hmin) (measure_mono ?_)
    intro ω hω
    exact (le_clusterMaxVol_iff hm _ ω).mp hω

/-- **Lemma I.2.6, probability form**: `P(|K ∩ B_{2r}| ≥ M_{β,r}-1) ≥ (M_{β,r}-1)/(e|B_r|)`. -/
theorem lemma_I_2_6_prob (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ.map (shiftConfig a) = μ) (n : ℕ) :
    ENNReal.ofReal ((((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1)) /
        (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))) ≤
      μ {ω : Config (Fin d → ℤ) |
        (((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _)) - 1 : ℕ) : ℝ≥0∞) ≤
          clusterVolIn ω 0 (latticeBall (2 * n) 0)} := by
  classical
  have hMge : 1 ≤ edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) :=
    one_le_edianMaxVol (FiniteVolume.box d n) (exists_edianMaxVol _)
  have havg := averaging_bound μ hμ
    (m := edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) - 1) (n := n)
    (edian_measure_exists (d := d) μ n)
  have heq : Real.exp (-1) *
        (((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) - 1 : ℕ)) : ℝ) /
        ((FiniteVolume.box d n).card : ℝ)
      = ((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1) /
        (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ)) := by
    rw [Nat.cast_sub hMge, Nat.cast_one, Real.exp_neg]
    field_simp
  rw [heq] at havg
  exact havg

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-- `|K_v ∩ W| ≤ |K_v|`. -/
theorem clusterVolIn_le_clusterVol {V : Type*} [Countable V] (ω : Config V) (v : V) (W : Set V) :
    clusterVolIn ω v W ≤ clusterVol ω v := by
  rw [clusterVolIn, clusterVol_eq_encard]
  exact_mod_cast Set.encard_mono Set.inter_subset_left

/-- **The first inequality of Lemma I.2.6**: `E|K ∩ B_{2r}|^p ≤ E|K|^p`. -/
theorem lemma_I_2_6_mono (μ : Measure (Config (Fin d → ℤ))) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ ω, clusterVolIn ω 0 (latticeBall (2 * n) 0) ^ p ∂μ ≤
      ∫⁻ ω, clusterVol ω 0 ^ p ∂μ := by
  refine lintegral_mono fun ω => ?_
  exact ENNReal.rpow_le_rpow (clusterVolIn_le_clusterVol ω 0 _) hp.le

/-- The finite ball is a.e. finite, so the ball-truncated cluster cardinality has no `⊤` mass:
this is the a.e. finiteness hypothesis of Markov's inequality. -/
theorem ae_ne_top_clusterVolIn_ball (μ : Measure (Config (Fin d → ℤ))) (n : ℕ) :
    μ {ω : Config (Fin d → ℤ) | clusterVolIn ω 0 (latticeBall n 0) = ⊤} = 0 := by
  have hempty : {ω : Config (Fin d → ℤ) | clusterVolIn ω 0 (latticeBall n 0) = ⊤} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω
    rw [latticeBall_zero]
    exact clusterVolIn_ne_top_of_finite ω 0 (FiniteVolume.box d n).finite_toSet
  rw [hempty, measure_empty]

/-- **Lemma I.2.6, ball form**: the second and third inequalities, combined through Markov's
inequality:
`E|K ∩ B_{2r}|^p ≥ (M_{β,r}-1)^p P(|K ∩ B_{2r}| ≥ M_{β,r}-1) ≥ (M_{β,r}-1)^{p+1}/(e|B_r|)`. -/
theorem lemma_I_2_6_mid (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ.map (shiftConfig a) = μ) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal ((((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1) ^ p *
        (((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1) /
          (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))))) ≤
      ∫⁻ ω, clusterVolIn ω 0 (latticeBall (2 * n) 0) ^ p ∂μ := by
  classical
  set E : ℕ := edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) with hE
  have hEge : 1 ≤ E := hE ▸ one_le_edianMaxVol (FiniteVolume.box d n) (exists_edianMaxVol _)
  set m : ℕ := E - 1 with hmdef
  have hcard_pos : 0 < (FiniteVolume.box d n).card := by
    refine Finset.card_pos.mpr ⟨0, ?_⟩
    have h0 : FiniteVolume.linfNorm (0 : Fin d → ℤ) = 0 :=
      FiniteVolume.linfNorm_eq_zero_iff.mpr rfl
    rw [FiniteVolume.mem_box_iff, h0]
    exact Nat.zero_le n
  rcases Nat.lt_or_ge E 2 with hcase | hcase
  · -- `E = 1`, hence `m = 0` and both sides record the trivial bound `0 ≤ ...`
    have hE1 : E = 1 := by omega
    have hzero : (E : ℝ) - 1 = 0 := by rw [hE1]; norm_num
    rw [hzero]
    simp
  · have hm : 1 ≤ m := by omega
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmE : (m : ℝ) = (E : ℝ) - 1 := by
      rw [hmdef, Nat.cast_sub hEge, Nat.cast_one]
    -- the averaged probability bound
    have hprob : ENNReal.ofReal (Real.exp (-1) * (m : ℝ) / ((FiniteVolume.box d n).card : ℝ)) ≤
        μ {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (latticeBall (2 * n) 0)} := by
      have h := averaging_bound μ hμ (m := m) (n := n) ?_
      · exact h
      · have := edian_measure_exists (d := d) μ n
        rw [← hE] at this
        rw [← hmdef] at this
        exact this
    -- Markov
    have hmarkov := ofReal_rpow_mul_meas_le_lintegral_ennreal (μ := μ)
      (X := fun ω => clusterVolIn ω 0 (latticeBall (2 * n) 0))
      (measurable_clusterVolIn 0 _) (ae_ne_top_clusterVolIn_ball μ (2 * n))
      (M := (m : ℝ)) hmR.le (p := p) hp
    have hBset : {ω : Config (Fin d → ℤ) | ENNReal.ofReal (m : ℝ) ≤
        clusterVolIn ω 0 (latticeBall (2 * n) 0)}
        = {ω : Config (Fin d → ℤ) | (m : ℝ≥0∞) ≤ clusterVolIn ω 0 (latticeBall (2 * n) 0)} := by
      ext ω
      rw [ENNReal.ofReal_natCast]
    rw [hBset] at hmarkov
    refine le_trans ?_ hmarkov
    -- assemble
    have hsec : Real.exp (-1) * (m : ℝ) / ((FiniteVolume.box d n).card : ℝ)
        = (m : ℝ) / (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ)) := by
      rw [Real.exp_neg]
      field_simp
    have hkey : (m : ℝ) ^ p * (Real.exp (-1) * (m : ℝ) / ((FiniteVolume.box d n).card : ℝ))
        = ((E : ℝ) - 1) ^ p * (((E : ℝ) - 1) /
            (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))) := by
      rw [← hmE, hsec]
    rw [← hkey, ENNReal.ofReal_mul (Real.rpow_nonneg hmR.le p)]
    exact mul_le_mul_of_nonneg_left hprob (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal ((m : ℝ) ^ p))

/-- **Lemma I.2.6** (Hutchcroft, arXiv:2508.18807v1, p. 24), for every real `p > 0` (the paper
states `p ≥ 1`):
`E|K|^p ≥ E|K ∩ B_{2r}|^p ≥ (M_{β,r}-1)^{p+1}/(e|B_r|)`.

Here `M_{β,r}` is the edian of `|K_max(B_r)|`, computed for the natural radius `n` with `B_n` the
lattice ball of `LatticeGeometry.linfNorm`; `|B_n| = (2n+1)^d` by `card_box`. -/
theorem lemma_I_2_6 (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ.map (shiftConfig a) = μ) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal ((((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1) ^
          (p + 1)) /
        (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))) ≤
      ∫⁻ ω, clusterVol ω 0 ^ p ∂μ := by
  classical
  set E : ℕ := edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) with hE
  have hEge : 1 ≤ E := hE ▸ one_le_edianMaxVol (FiniteVolume.box d n) (exists_edianMaxVol _)
  rcases Nat.lt_or_ge E 2 with hcase | hcase
  · have hE1 : E = 1 := by omega
    have hzero : (E : ℝ) - 1 = 0 := by rw [hE1]; norm_num
    rw [hzero, Real.zero_rpow (by linarith : p + 1 ≠ 0), zero_div, ENNReal.ofReal_zero]
    exact zero_le
  · have hE2 : 1 ≤ E - 1 := by omega
    have hpos : (0 : ℝ) < (E : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (E : ℝ) - 1 := by
        have : ((1 : ℕ) : ℝ) ≤ ((E - 1 : ℕ) : ℝ) := by exact_mod_cast hE2
        rwa [Nat.cast_sub hEge, Nat.cast_one] at this
      linarith
    have hcard_pos : 0 < (FiniteVolume.box d n).card := by
      refine Finset.card_pos.mpr ⟨0, ?_⟩
      have h0 : FiniteVolume.linfNorm (0 : Fin d → ℤ) = 0 :=
        FiniteVolume.linfNorm_eq_zero_iff.mpr rfl
      rw [FiniteVolume.mem_box_iff, h0]
      exact Nat.zero_le n
    have hkey : ((E : ℝ) - 1) ^ (p + 1) /
          (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))
        = ((E : ℝ) - 1) ^ p * (((E : ℝ) - 1) /
            (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))) := by
      rw [Real.rpow_add hpos, Real.rpow_one]
      field_simp
    rw [hkey]
    exact le_trans (lemma_I_2_6_mid μ hμ n hp) (lemma_I_2_6_mono μ n hp)

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-! ## Closed balls of real radius

The paper's `B_r(x) = {y ∈ Z^d : ‖x - y‖ ≤ r}` is indexed by a real radius `r ≥ 0`.  Since the
sup norm of a lattice vector is a natural number, the closed ball of real radius `r` is exactly
the ball of natural radius `⌊r⌋`: nothing is lost by working with the `Finset`-valued `box`.
-/

/-- The closed lattice ball of real radius `r` about `x`. -/
noncomputable def latticeBallR (r : ℝ) (x : Fin d → ℤ) : Set (Fin d → ℤ) :=
  {y | FiniteVolume.latticeDist x y ≤ r}

theorem mem_latticeBallR_iff {r : ℝ} {x y : Fin d → ℤ} :
    y ∈ latticeBallR r x ↔ FiniteVolume.latticeDist x y ≤ r := Iff.rfl

/-- The sup norm of a lattice vector, as a real number: `latticeDist x y = ‖y - x‖_∞`. -/
theorem latticeDist_eq_linfNorm (x y : Fin d → ℤ) :
    FiniteVolume.latticeDist x y = (FiniteVolume.linfNorm (y - x) : ℝ) := by
  unfold FiniteVolume.latticeDist
  rw [← neg_sub y x, FiniteVolume.linfNorm_neg]

/-- **`B_r(x) = B_{⌊r⌋}(x)`** for a real radius `r ≥ 0`. -/
theorem latticeBallR_eq_latticeBall {r : ℝ} (hr : 0 ≤ r) (x : Fin d → ℤ) :
    latticeBallR r x = latticeBall ⌊r⌋₊ x := by
  ext y
  rw [mem_latticeBallR_iff, latticeDist_eq_linfNorm, mem_latticeBall_iff]
  exact (Nat.le_floor_iff hr).symm

/-- **Lemma I.2.6 at a real radius** `r ≥ 0`, in the paper's exact form: the window is the closed
ball `B_r = {y : ‖y‖_∞ ≤ r}`, whose cardinality is `(2⌊r⌋+1)^d`. -/
theorem lemma_I_2_6_real (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ.map (shiftConfig a) = μ) {r : ℝ} (_hr : 0 ≤ r) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal ((((edianMaxVol μ (FiniteVolume.box d ⌊r⌋₊) (exists_edianMaxVol _) : ℝ) - 1) ^
          (p + 1)) / (Real.exp 1 * ((FiniteVolume.box d ⌊r⌋₊).card : ℝ))) ≤
      ∫⁻ ω, clusterVol ω 0 ^ p ∂μ :=
  lemma_I_2_6 μ hμ ⌊r⌋₊ hp

/-- **`|B_r| = (2⌊r⌋+1)^d`** for a real radius `r ≥ 0` (the cardinality of the closed lattice ball
in the sup norm): the paper's `|B_r| ≍ r^d`. -/
theorem card_latticeBallR {r : ℝ} (hr : 0 ≤ r) :
    (latticeBallR (d := d) r 0).encard = ((2 * ⌊r⌋₊ + 1) ^ d : ℕ) := by
  rw [latticeBallR_eq_latticeBall hr, latticeBall_zero, Set.encard_coe_eq_coe_finsetCard,
    FiniteVolume.card_box]

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-! ## Instantiation at the paper's laws `P_β` and `P_{β,r}`

`P_β` is `longRangeMeasure J hJ β = edgeMeasure (bernoulliEdgeProb J hJ β)`.  For a
translation-invariant kernel `J` the law is translation invariant
(`edgeMeasure_shift_invariant`), which is the only hypothesis of `lemma_I_2_6`.  The cut-off
kernel `J_r` of Definition I.1.5 is `CutoffKernel.cutoffSymKernel K d r`, and it is translation
invariant by `cutoffSymKernel_shift` (see `LemmaI26Cutoff.lean`).
-/

/-- **Lemma I.2.6 for an arbitrary translation-invariant edge law** `edgeMeasure π`. -/
theorem lemma_I_2_6_edgeMeasure (π : Sym2 (Fin d → ℤ) → unitInterval)
    (hπ : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), π (Sym2.map (fun x => x + a) e) = π e)
    (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal ((((edianMaxVol (edgeMeasure π) (FiniteVolume.box d n)
            (exists_edianMaxVol _) : ℝ) - 1) ^ (p + 1)) /
        (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))) ≤
      ∫⁻ ω, clusterVol ω 0 ^ p ∂(edgeMeasure π) :=
  lemma_I_2_6 (edgeMeasure π) (fun a => edgeMeasure_shift_invariant π hπ a) n hp

/-- **Lemma I.2.6 for the long-range model `P_β`** with a translation-invariant kernel. -/
theorem lemma_I_2_6_longRange (J : Sym2 (Fin d → ℤ) → ℝ)
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal ((((edianMaxVol (longRangeMeasure J hJ β) (FiniteVolume.box d n)
            (exists_edianMaxVol _) : ℝ) - 1) ^ (p + 1)) /
        (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))) ≤
      ∫⁻ ω, clusterVol ω 0 ^ p ∂(longRangeMeasure J hJ β) :=
  lemma_I_2_6_edgeMeasure (bernoulliEdgeProb J hJ β)
    (bernoulliEdgeProb_shift hJinv hJ β) n hp

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-! ## The real-valued expectation form

The paper writes `E_{β,r}|K|^p` for a real expectation.  The `ℝ≥0∞`-valued inequality
`lemma_I_2_6` implies the real form as soon as `E|K|^p` is finite, which is the situation in the
paper's application (the law `P_{β,r}` is subcritical at `β_c` for finite `r`).  We record the
transfer; the finiteness hypothesis is exactly what is needed to identify the Bochner integral
`∫ ω, (|K|)^p` with `(∫⁻ ω, |K|^p).toReal`.
-/

/-- **Lemma I.2.6 with real expectations**: if `E|K|^p < ∞` then
`(M_{β,r}-1)^{p+1}/(e|B_r|) ≤ E|K|^p` in `ℝ`. -/
theorem lemma_I_2_6_real_integral (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ.map (shiftConfig a) = μ) (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hfin : ∫⁻ ω, clusterVol ω 0 ^ p ∂μ ≠ ⊤) :
    ((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1) ^ (p + 1) /
        (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ)) ≤
      ∫ ω, (clusterVol ω 0).toReal ^ p ∂μ := by
  classical
  have hmain := lemma_I_2_6 μ hμ n hp
  have hEge : 1 ≤ edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) :=
    one_le_edianMaxVol (FiniteVolume.box d n) (exists_edianMaxVol _)
  -- a.e. finiteness of the cluster volume, from finiteness of the moment
  have haefin : μ {ω : Config (Fin d → ℤ) | clusterVol ω 0 = ⊤} = 0 := by
    have h := measure_eq_top_of_lintegral_ne_top
      ((measurable_clusterVol 0).pow_const p).aemeasurable hfin
    convert h using 2
    ext ω
    show clusterVol ω 0 = ⊤ ↔ clusterVol ω 0 ^ p = ⊤
    rw [ENNReal.rpow_eq_top_iff]
    constructor
    · intro hω; exact Or.inr ⟨hω, hp⟩
    · rintro (⟨_, hpneg⟩ | ⟨htop, _⟩)
      · exact absurd hp (not_lt.mpr hpneg.le)
      · exact htop
  -- the Bochner integral is the `toReal` of the lintegral
  have hnn : 0 ≤ᵐ[μ] fun ω => (clusterVol ω 0).toReal ^ p :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg ENNReal.toReal_nonneg p
  have hmeas : AEStronglyMeasurable (fun ω : Config (Fin d → ℤ) => (clusterVol ω 0).toReal ^ p) μ :=
    (Measurable.aestronglyMeasurable ((measurable_clusterVol 0).ennreal_toReal.pow_const p))
  have hconv : (∫⁻ ω, clusterVol ω 0 ^ p ∂μ).toReal =
      ∫ ω, (clusterVol ω 0).toReal ^ p ∂μ := by
    rw [lintegral_rpow_toReal haefin hp.le]
    exact (integral_eq_lintegral_of_nonneg_ae hnn hmeas).symm
  have hbase_nn : 0 ≤ (edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) := by
      exact_mod_cast hEge
    linarith
  have hbound_nn : 0 ≤ ((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1) ^
      (p + 1) / (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ)) :=
    div_nonneg (Real.rpow_nonneg hbase_nn _) (by positivity)
  calc ((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1) ^ (p + 1) /
        (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))
      = (ENNReal.ofReal (((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1) ^
          (p + 1) / (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ)))).toReal :=
        (ENNReal.toReal_ofReal hbound_nn).symm
    _ ≤ (∫⁻ ω, clusterVol ω 0 ^ p ∂μ).toReal := ENNReal.toReal_mono hfin hmain
    _ = ∫ ω, (clusterVol ω 0).toReal ^ p ∂μ := hconv

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-- **Lemma I.2.6 with `|B_r|` evaluated**, `|B_n| = (2n+1)^d` (`FiniteVolume.card_box`):
`E|K|^p ≥ (M_{β,r}-1)^{p+1}/(e(2n+1)^d)`. -/
theorem lemma_I_2_6_card (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ.map (shiftConfig a) = μ) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal ((((edianMaxVol μ (FiniteVolume.box d n) (exists_edianMaxVol _) : ℝ) - 1) ^
          (p + 1)) / (Real.exp 1 * (((2 * n + 1) ^ d : ℕ) : ℝ))) ≤
      ∫⁻ ω, clusterVol ω 0 ^ p ∂μ := by
  rw [← FiniteVolume.card_box (d := d) n]
  exact lemma_I_2_6 μ hμ n hp

/-- **Lemma I.2.6 at a real radius with `|B_r| = (2⌊r⌋+1)^d`**: the paper's displayed form for
`r ≥ 0`. -/
theorem lemma_I_2_6_real_card (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    (hμ : ∀ a, μ.map (shiftConfig a) = μ) {r : ℝ} (hr : 0 ≤ r) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal ((((edianMaxVol μ (FiniteVolume.box d ⌊r⌋₊) (exists_edianMaxVol _) : ℝ) - 1) ^
          (p + 1)) / (Real.exp 1 * (((2 * ⌊r⌋₊ + 1) ^ d : ℕ) : ℝ))) ≤
      ∫⁻ ω, clusterVol ω 0 ^ p ∂μ := by
  rw [← FiniteVolume.card_box (d := d) ⌊r⌋₊]
  exact lemma_I_2_6_real μ hμ hr hp

end Percolation

end PercLib.CriticalLRP
