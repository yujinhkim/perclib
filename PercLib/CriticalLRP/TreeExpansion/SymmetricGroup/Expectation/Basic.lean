/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
# Finite expectation alignment: `expectReal` versus `∫⁻ ∂edgeMeasure`

On a finite vertex set `V`, the tree-expansion development
(`PercLib/CriticalLRP/TreeExpansion/`) computes expectations of cluster functionals with the
finite sums `expectReal p X = ∑_s configurationLaw p s * X s`, while the paper's consumers use the
native law `edgeMeasure π` on `Config V := Sym2 V → Prop` and Lebesgue integrals `∫⁻` / `∫`.

The atom identities of `TreeExpansion/SymmetricGroup/Alignment.lean` identify the mass of a single
native configuration with the finite product law.  This file sums those identities over the
(finitely many) configurations, which turns them into integral identities, and then uses them to
move the tree model's cluster moment bounds (I.2.3) to the native law.

## Alignment

* `toFsEquiv` : the bijection `Config V ≃ Finset (Sym2 V)`;
* `integral_toFs` : for **any** `X : Finset (Sym2 V) → ℝ`, the real Lebesgue integral of
  `ω ↦ X (toFs ω)` is `expectReal (fun e => π e) X` (no positivity needed: the space is finite);
* `lintegral_ofReal_toFs` : the `ℝ≥0∞` version for nonnegative `X`, via `lintegral_fintype`;
* `clusterVol_eq_ofReal` : the native `clusterVol` (an `encard`) is `ofReal` of the
  tree-expansion `clusterVol` (a `Finset.card`);
* `lintegral_clusterVol`, `lintegral_clusterVol_sq` : the native (`ℝ≥0∞`) first and second
  cluster moments as `ofReal` of the finite real moments `clusterVolume`, `clusterVolSq`;
* `integral_clusterVol_toReal`, `integral_clusterVol_sq_toReal` : the same as real integrals;
* `clusterVolumeE_eq_ofReal`, `clusterVolSqE_eq_ofReal` : the `ℝ≥0∞` extended sums
  `∑'`/`∑'∑'` of `TreeGraph/Extended.lean` coincide with `ofReal` of the real moments on finite
  `V`;
* `cardFun_cluster_eq_clusterVol` and `lintegral_cardFun_cluster`, `lintegral_cardFun_cluster_cube`:
  the same identities in the `Percolation.cardFun` vocabulary of `VolumeMoments/ErrorBounds.lean`.

## Moment bounds for the native law

* `second_moment_le_native` : transfer of the proved tree-model bound
  `clusterVolSqE ≤ clusterVolumeE ^ 3` to the native law, giving `∫⁻ (|K_o|)² ≤ (∫⁻ |K_o|)³`
  on a finite `V`, with the tree model's translation-invariance premise `hinv` explicit;
* `configurationLaw_image_eshift`, `prob_image_eshift'`,
  `twoPoint_translation_of_invariant`, `twoPointE_translation_of_invariant` : `hinv` derived from
  translation invariance of the edge weights (not just for constant weights);
* `second_moment_le_native_of_translation_invariant`,
  `third_moment_le_native_of_translation_invariant`, `third_moment_le_native`,
  `third_moment_le_native_const` : (I.2.3) at `q = 2` and `q = 3` for the native law of every
  translation-invariant finite model, with no residual translation hypothesis;
* `kernelJ`, `longRangeWeight`, `second_moment_le_native_kernel`,
  `third_moment_le_native_kernel` : the paper's kernel `π⟨x,y⟩ = 1 - exp (-(β J(y - x)))` on a
  finite abelian group as an instance, `J` even and nonnegative, `β ≥ 0`.

Everything here is a finite-`V` statement.  Nothing in this file asserts an identity or inequality
on a countably infinite vertex set.  The only infinite-`V` results used are imported:
`TreeGraph.second_moment_le_infinite` and `moment_bound_of_bk_expectation`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.SymmetricGroup.Alignment
public import PercLib.CriticalLRP.TreeExpansion.SymmetricGroup.ThirdMoment

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The configuration / finite-edge-set bijection -/

/-- On a finite edge type, configurations (subsets) and finite edge sets are the same thing. -/
def toFsEquiv (E : Type*) [Fintype E] [DecidableEq E] : Set E ≃ Finset E where
  toFun := TreeGraph.toFs
  invFun := fun s => (s : Set E)
  left_inv := TreeGraph.coe_toFs
  right_inv := TreeGraph.toFs_coe

@[simp] theorem toFsEquiv_apply (E : Type*) [Fintype E] [DecidableEq E] (ω : Set E) :
    toFsEquiv E ω = TreeGraph.toFs ω := rfl

/-- The finite product law `configurationLaw` with probability vector `fun e => π e`. -/
theorem integral_toFs (π : Sym2 V → unitInterval) (X : Finset (Sym2 V) → ℝ) :
    ∫ ω : Config V, X (TreeGraph.toFs ω) ∂(edgeMeasure π)
      = TreeGraph.expectReal (fun e => (π e : ℝ)) X := by
  classical
  have hprob : IsProbabilityMeasure (edgeMeasure π) := by
    rw [edgeMeasure_eq_edgeLaw']
    infer_instance
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  calc ∑ ω : Config V, (edgeMeasure π).real {ω} * X (TreeGraph.toFs ω)
      = ∑ ω : Config V,
          PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) (TreeGraph.toFs ω)
            * X (TreeGraph.toFs ω) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [edgeMeasure_atom' π ω]
    _ = ∑ s : Finset (Sym2 V),
          PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) s * X s := by
        rw [← Equiv.sum_comp (toFsEquiv (Sym2 V))
          (fun s => PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) s * X s)]
        rfl
    _ = TreeGraph.expectReal (fun e => (π e : ℝ)) X := rfl

/-! ### The `ℝ≥0∞` form -/

/-- **Alignment of the `ℝ≥0∞` integral with the finite expectation**, for nonnegative `X`. -/
theorem lintegral_ofReal_toFs (π : Sym2 V → unitInterval) (X : Finset (Sym2 V) → ℝ)
    (hX : ∀ s, 0 ≤ X s) :
    ∫⁻ ω : Config V, ENNReal.ofReal (X (TreeGraph.toFs ω)) ∂(edgeMeasure π)
      = ENNReal.ofReal (TreeGraph.expectReal (fun e => (π e : ℝ)) X) := by
  classical
  have hp0 : ∀ e : Sym2 V, 0 ≤ (π e : ℝ) := fun e => unitInterval.nonneg (π e)
  have hp1 : ∀ e : Sym2 V, (π e : ℝ) ≤ 1 := fun e => unitInterval.le_one (π e)
  have hprob : IsProbabilityMeasure (edgeMeasure π) := by
    rw [edgeMeasure_eq_edgeLaw']
    infer_instance
  have hne : ∀ ω : Config V, (edgeMeasure π) {ω} ≠ ⊤ := by
    intro ω
    have h1 : (edgeMeasure π) {ω} ≤ (edgeMeasure π) Set.univ := measure_mono (Set.subset_univ _)
    rw [measure_univ] at h1
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h1
  rw [lintegral_fintype]
  have hsum : ∀ ω : Config V,
      ENNReal.ofReal (X (TreeGraph.toFs ω)) * (edgeMeasure π) {ω}
        = ENNReal.ofReal (X (TreeGraph.toFs ω)
            * PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) (TreeGraph.toFs ω)) := by
    intro ω
    have hatom : ((edgeMeasure π) {ω}).toReal
        = PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) (TreeGraph.toFs ω) :=
      edgeMeasure_atom' π ω
    rw [← ENNReal.ofReal_toReal (hne ω), hatom, ENNReal.ofReal_mul (hX _)]
  have hsum2 : (∑ s : Finset (Sym2 V), ENNReal.ofReal
        (X s * PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) s))
      = ENNReal.ofReal (TreeGraph.expectReal (fun e => (π e : ℝ)) X) := by
    have hnonneg : ∀ s ∈ (Finset.univ : Finset (Finset (Sym2 V))),
        0 ≤ X s * PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) s :=
      fun s _ => mul_nonneg (hX s) (PercLib.CriticalLRP.configurationLaw_nonneg _ hp0 hp1 s)
    have h1 : (∑ s : Finset (Sym2 V), ENNReal.ofReal
          (X s * PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) s))
        = ∑ s ∈ (Finset.univ : Finset (Finset (Sym2 V))), ENNReal.ofReal
          (X s * PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) s) := by
      simp
    rw [h1, ← ENNReal.ofReal_sum_of_nonneg hnonneg]
    congr 1
    rw [Finset.sum_congr rfl (fun s _ => mul_comm (X s)
      (PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) s))]
    rfl
  calc ∑ ω : Config V, ENNReal.ofReal (X (TreeGraph.toFs ω)) * (edgeMeasure π) {ω}
      = ∑ ω : Config V, ENNReal.ofReal (X (TreeGraph.toFs ω)
          * PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) (TreeGraph.toFs ω)) :=
        Finset.sum_congr rfl fun ω _ => hsum ω
    _ = ∑ s : Finset (Sym2 V), ENNReal.ofReal
          (X s * PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) s) := by
        rw [← Equiv.sum_comp (toFsEquiv (Sym2 V)) (fun s => ENNReal.ofReal
          (X s * PercLib.CriticalLRP.configurationLaw (fun e => (π e : ℝ)) s))]
        rfl
    _ = ENNReal.ofReal (TreeGraph.expectReal (fun e => (π e : ℝ)) X) := hsum2


/-! ### The native cluster volume -/

/-- The native cluster volume (an `encard` of a set of vertices) is `ofReal` of the finite
tree-expansion cluster volume (a `Finset.card`). -/
theorem clusterVol_eq_ofReal (ω : Config V) (x : V) :
    PercLib.CriticalLRP.clusterVol ω x
      = ENNReal.ofReal (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V)
          (TreeGraph.toFs ω) x : ℝ) := by
  rw [PercLib.CriticalLRP.clusterVol]
  rw [show PercLib.Percolation.Bond.cluster ω x
      = ((TreeGraph.clusterF (PercLib.CriticalLRP.idBondGraph V) (TreeGraph.toFs ω) x
          : Finset V) : Set V) from cluster_toFs' ω x]
  rw [Set.encard_coe_eq_coe_finsetCard, TreeGraph.clusterVol, ENNReal.ofReal_natCast]
  norm_cast

/-- Squared form of `clusterVol_eq_ofReal`. -/
theorem clusterVol_sq_eq_ofReal (ω : Config V) (x : V) :
    (PercLib.CriticalLRP.clusterVol ω x) ^ 2
      = ENNReal.ofReal ((TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V)
          (TreeGraph.toFs ω) x : ℝ) ^ 2) := by
  rw [clusterVol_eq_ofReal, ENNReal.ofReal_pow (by positivity)]

/-- **Native first cluster moment.**  `∫⁻ |K_x| ∂edgeMeasure π` is `ofReal` of the finite
susceptibility `clusterVolume`. -/
theorem lintegral_clusterVol (π : Sym2 V → unitInterval) (x : V) :
    ∫⁻ ω : Config V, PercLib.CriticalLRP.clusterVol ω x ∂(edgeMeasure π)
      = ENNReal.ofReal (TreeGraph.clusterVolume (fun e => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) x) := by
  calc ∫⁻ ω : Config V, PercLib.CriticalLRP.clusterVol ω x ∂(edgeMeasure π)
      = ∫⁻ ω : Config V, ENNReal.ofReal (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V)
          (TreeGraph.toFs ω) x : ℝ) ∂(edgeMeasure π) :=
        lintegral_congr fun ω => clusterVol_eq_ofReal ω x
    _ = ENNReal.ofReal (TreeGraph.expectReal (fun e => (π e : ℝ))
          (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ))) :=
        lintegral_ofReal_toFs π
          (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ))
          (fun s => by positivity)
    _ = ENNReal.ofReal (TreeGraph.clusterVolume (fun e => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) x) := by
        rw [TreeGraph.expectation_clusterVol]

/-- **Native second cluster moment.**  `∫⁻ |K_x|² ∂edgeMeasure π` is `ofReal` of `clusterVolSq`. -/
theorem lintegral_clusterVol_sq (π : Sym2 V → unitInterval) (x : V) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.clusterVol ω x) ^ 2 ∂(edgeMeasure π)
      = ENNReal.ofReal (TreeGraph.clusterVolSq (fun e => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) x) := by
  calc ∫⁻ ω : Config V, (PercLib.CriticalLRP.clusterVol ω x) ^ 2 ∂(edgeMeasure π)
      = ∫⁻ ω : Config V, ENNReal.ofReal ((TreeGraph.clusterVol
          (PercLib.CriticalLRP.idBondGraph V) (TreeGraph.toFs ω) x : ℝ) ^ 2) ∂(edgeMeasure π) :=
        lintegral_congr fun ω => clusterVol_sq_eq_ofReal ω x
    _ = ENNReal.ofReal (TreeGraph.expectReal (fun e => (π e : ℝ))
          (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ) ^ 2)) :=
        lintegral_ofReal_toFs π
          (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ) ^ 2)
          (fun s => by positivity)
    _ = ENNReal.ofReal (TreeGraph.clusterVolSq (fun e => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) x) := by
        rw [TreeGraph.expectation_clusterVol_sq]

/-! ### The real-integral forms -/

/-- **Native first cluster moment, real form.** -/
theorem integral_clusterVol_toReal (π : Sym2 V → unitInterval) (x : V) :
    ∫ ω : Config V, (PercLib.CriticalLRP.clusterVol ω x).toReal ∂(edgeMeasure π)
      = TreeGraph.clusterVolume (fun e => (π e : ℝ)) (PercLib.CriticalLRP.idBondGraph V) x := by
  have h : (fun ω : Config V => (PercLib.CriticalLRP.clusterVol ω x).toReal)
      = fun ω => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V)
          (TreeGraph.toFs ω) x : ℝ) := by
    funext ω
    rw [clusterVol_eq_ofReal, ENNReal.toReal_ofReal (by positivity)]
  calc ∫ ω : Config V, (PercLib.CriticalLRP.clusterVol ω x).toReal ∂(edgeMeasure π)
      = ∫ ω : Config V, (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V)
          (TreeGraph.toFs ω) x : ℝ) ∂(edgeMeasure π) := by rw [h]
    _ = TreeGraph.expectReal (fun e => (π e : ℝ))
          (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ)) :=
        integral_toFs π (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ))
    _ = TreeGraph.clusterVolume (fun e => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) x := by
        rw [TreeGraph.expectation_clusterVol]

/-- **Native second cluster moment, real form.** -/
theorem integral_clusterVol_sq_toReal (π : Sym2 V → unitInterval) (x : V) :
    ∫ ω : Config V, ((PercLib.CriticalLRP.clusterVol ω x).toReal) ^ 2 ∂(edgeMeasure π)
      = TreeGraph.clusterVolSq (fun e => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) x := by
  have h : (fun ω : Config V => ((PercLib.CriticalLRP.clusterVol ω x).toReal) ^ 2)
      = fun ω => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V)
          (TreeGraph.toFs ω) x : ℝ) ^ 2 := by
    funext ω
    rw [clusterVol_eq_ofReal, ENNReal.toReal_ofReal (by positivity)]
  calc ∫ ω : Config V, ((PercLib.CriticalLRP.clusterVol ω x).toReal) ^ 2 ∂(edgeMeasure π)
      = ∫ ω : Config V, (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V)
          (TreeGraph.toFs ω) x : ℝ) ^ 2 ∂(edgeMeasure π) := by rw [h]
    _ = TreeGraph.expectReal (fun e => (π e : ℝ))
          (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ) ^ 2) :=
        integral_toFs π (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ) ^ 2)
    _ = TreeGraph.clusterVolSq (fun e => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) x := by
        rw [TreeGraph.expectation_clusterVol_sq]

/-! ### The extended sums of `TreeGraph/Extended.lean` on a finite vertex set -/

/-- On a finite vertex set the extended first moment `∑'` of the tree model is `ofReal` of the
real moment `clusterVolume`. -/
theorem clusterVolumeE_eq_ofReal {E : Type*} [Fintype E] [DecidableEq E]
    (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (ends : E → Sym2 V) (x : V) :
    TreeGraph.clusterVolumeE p ends x = ENNReal.ofReal (TreeGraph.clusterVolume p ends x) := by
  rw [TreeGraph.clusterVolumeE, TreeGraph.clusterVolume]
  simp only [TreeGraph.twoPointE, TreeGraph.twoPoint, tsum_fintype]
  exact (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun y => TreeGraph.prob p {s | TreeGraph.Conn ends s x y})
    (fun y _ => TreeGraph.prob_nonneg hp0 hp1 _)).symm

/-- On a finite vertex set the extended second moment `∑'∑'` of the tree model is `ofReal` of the
real moment `clusterVolSq`. -/
theorem clusterVolSqE_eq_ofReal {E : Type*} [Fintype E] [DecidableEq E]
    (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (ends : E → Sym2 V) (x : V) :
    TreeGraph.clusterVolSqE p ends x = ENNReal.ofReal (TreeGraph.clusterVolSq p ends x) := by
  rw [TreeGraph.clusterVolSqE, TreeGraph.clusterVolSq]
  simp only [tsum_fintype]
  have hinner : ∀ y : V,
      (∑ z : V, ENNReal.ofReal (TreeGraph.prob p
        {s | TreeGraph.Conn ends s x y ∧ TreeGraph.Conn ends s x z}))
      = ENNReal.ofReal (∑ z : V, TreeGraph.prob p
        {s | TreeGraph.Conn ends s x y ∧ TreeGraph.Conn ends s x z}) := fun y =>
    (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := fun z =>
      TreeGraph.prob p {s | TreeGraph.Conn ends s x y ∧ TreeGraph.Conn ends s x z})
      (fun z _ => TreeGraph.prob_nonneg hp0 hp1 _)).symm
  rw [Finset.sum_congr rfl (fun y _ => hinner y)]
  exact (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := fun y =>
    ∑ z : V, TreeGraph.prob p {s | TreeGraph.Conn ends s x y ∧ TreeGraph.Conn ends s x z})
    (fun y _ => Finset.sum_nonneg fun z _ => TreeGraph.prob_nonneg hp0 hp1 _)).symm

/-! ### Transfer of the tree-model second-moment bound to the native law -/

/-- **Cluster second-moment bound (I.2.3) for the native law on a finite vertex set.**
`∫⁻ |K_o|² ≤ (∫⁻ |K_o|)³` for `edgeMeasure π` on a finite `V` with `∀ e, π e < 1`.

The two inputs are explicit: the tree model's translation-invariance hypothesis `hinv` on the
two-point function (the paper's transitivity, an input of `second_moment_le_infinite`), and
`∀ e, π e < 1` (non-degeneracy, used to obtain BK).  No finiteness of a moment is assumed; the
statement holds in `ℝ≥0∞`. -/
theorem second_moment_le_native [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hπ : ∀ e : Sym2 V, (π e : ℝ) < 1) (o : V)
    (hinv : ∀ a b : V, TreeGraph.twoPointE (fun e => (π e : ℝ))
        (PercLib.CriticalLRP.idBondGraph V) a b
      = TreeGraph.twoPointE (fun e => (π e : ℝ)) (PercLib.CriticalLRP.idBondGraph V) o (b - a)) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.clusterVol ω o) ^ 2 ∂(edgeMeasure π)
      ≤ (∫⁻ ω : Config V, PercLib.CriticalLRP.clusterVol ω o ∂(edgeMeasure π)) ^ 3 := by
  have hp0 : ∀ e : Sym2 V, 0 ≤ (π e : ℝ) := fun e => unitInterval.nonneg (π e)
  have hp1 : ∀ e : Sym2 V, (π e : ℝ) ≤ 1 := fun e => unitInterval.le_one (π e)
  have hbk : TreeGraph.BKIncreasing (fun e : Sym2 V => (π e : ℝ)) :=
    TreeGraph.BKIncreasing_of_bkFin _ hp0 (fun e => hπ e)
  have hmain := TreeGraph.second_moment_le_infinite (fun e : Sym2 V => (π e : ℝ)) hp0 hp1 hbk
    (PercLib.CriticalLRP.idBondGraph V) o hinv
  rw [clusterVolSqE_eq_ofReal _ hp0 hp1, clusterVolumeE_eq_ofReal _ hp0 hp1] at hmain
  rw [lintegral_clusterVol_sq, lintegral_clusterVol]
  exact hmain

/-! ### The measurable structure on `Config V` and the constant-weight instance -/

/-- On a finite vertex set the native configuration space carries a discrete measurable space, so
that a singleton configuration is measurable.  This is the σ-algebra hypothesis under which
`lintegral_fintype` computes the native integral as the finite sum of atomic contributions. -/
theorem measurableSet_config_singleton (ω : Config V) :
    MeasurableSet ({ω} : Set (Config V)) :=
  MeasurableSet.of_discrete

/-- Translation invariance of the two-point function of `TreeGraph/Extended.lean` for constant edge
weight `p` on a finite abelian group, i.e. the hypothesis `hinv` of `second_moment_le_native`
derived from the invariance of the model (`twoPoint_const_translation`). -/
theorem twoPointE_const_translation [AddCommGroup V] (p : ℝ) (a b : V) :
    TreeGraph.twoPointE (fun _ => p) (PercLib.CriticalLRP.idBondGraph V) a b
      = TreeGraph.twoPointE (fun _ => p) (PercLib.CriticalLRP.idBondGraph V) 0 (b - a) := by
  have h : ENNReal.ofReal (TreeGraph.prob (fun _ => p) {s |
        TreeGraph.Conn (PercLib.CriticalLRP.idBondGraph V) s a b})
      = ENNReal.ofReal (TreeGraph.prob (fun _ => p) {s |
        TreeGraph.Conn (PercLib.CriticalLRP.idBondGraph V) s 0 (b - a)}) :=
    congrArg ENNReal.ofReal (twoPoint_const_translation (V := V) p a b)
  simpa only [TreeGraph.twoPointE, TreeGraph.twoPoint] using h

/-- **Cluster second-moment bound for the native law, constant edge weight, no residual
hypothesis.**  For Bernoulli bond percolation on the complete graph of a finite abelian group with
constant edge probability `p < 1`, `∫⁻ |K_0|² ≤ (∫⁻ |K_0|)³` — the `q = 2` case of (I.2.3) for
the native law `edgeMeasure (fun _ => p)`. -/
theorem second_moment_le_native_const [AddCommGroup V] (p : unitInterval)
    (hp : (p : ℝ) < 1) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.clusterVol ω 0) ^ 2 ∂(edgeMeasure (fun _ => p))
      ≤ (∫⁻ ω : Config V, PercLib.CriticalLRP.clusterVol ω 0 ∂(edgeMeasure (fun _ => p))) ^ 3 :=
  second_moment_le_native (fun _ => p) (fun _ => hp) 0
    (fun a b => twoPointE_const_translation (p : ℝ) a b)

/-! ### The same alignment in the `cardFun` vocabulary of the I.4.7/I.4.8 consumers -/

/-- `Percolation.cardFun` of the native cluster is the native cluster volume. -/
theorem cardFun_cluster_eq_clusterVol (ω : Config V) (x : V) :
    PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω x)
      = PercLib.CriticalLRP.clusterVol ω x := by
  rw [PercLib.CriticalLRP.Percolation.cardFun_eq_encard]

/-- The native first moment in the `cardFun` vocabulary of `VolumeMoments/ErrorBounds.lean`. -/
theorem lintegral_cardFun_cluster (π : Sym2 V → unitInterval) (x : V) :
    ∫⁻ ω : Config V, PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω x)
        ∂(edgeMeasure π)
      = ENNReal.ofReal (TreeGraph.clusterVolume (fun e => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) x) := by
  rw [show (fun ω => PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω x))
      = fun ω => PercLib.CriticalLRP.clusterVol ω x from
      funext fun ω => cardFun_cluster_eq_clusterVol ω x]
  exact lintegral_clusterVol π x

/-- Cubed form of `cardFun_cluster_eq_clusterVol`. -/
theorem cardFun_cluster_cube_eq_ofReal (ω : Config V) (x : V) :
    (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω x)) ^ 3
      = ENNReal.ofReal ((TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V)
          (TreeGraph.toFs ω) x : ℝ) ^ 3) := by
  rw [cardFun_cluster_eq_clusterVol, clusterVol_eq_ofReal, ENNReal.ofReal_pow (by positivity)]

/-- The native third moment in the `cardFun` vocabulary of `VolumeMoments/ErrorBounds.lean`. -/
theorem lintegral_cardFun_cluster_cube (π : Sym2 V → unitInterval) (x : V) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω x)) ^ 3 ∂(edgeMeasure π)
      = ENNReal.ofReal (TreeGraph.expectReal (fun e => (π e : ℝ))
          (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ) ^ 3)) := by
  calc ∫⁻ ω : Config V, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω x)) ^ 3 ∂(edgeMeasure π)
      = ∫⁻ ω : Config V, ENNReal.ofReal ((TreeGraph.clusterVol
          (PercLib.CriticalLRP.idBondGraph V) (TreeGraph.toFs ω) x : ℝ) ^ 3) ∂(edgeMeasure π) :=
        lintegral_congr fun ω => cardFun_cluster_cube_eq_ofReal ω x
    _ = ENNReal.ofReal (TreeGraph.expectReal (fun e => (π e : ℝ))
          (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ) ^ 3)) :=
        lintegral_ofReal_toFs π
          (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s x : ℝ) ^ 3)
          (fun s => by positivity)

/-- **Third cluster moment bound for the native law, constant edge weight, no residual
hypothesis.**  This is the hypothesis `hthird` of
`VolumeMoments.cE1_le_three_mul_cube_div_of_finite` (there written for arbitrary `π`), proved here
for the constant-weight complete graph on a finite abelian group:

`∫⁻ |K_0|³ ∂edgeMeasure (fun _ => p) ≤ 3 * (∫⁻ |K_0| ∂edgeMeasure (fun _ => p)) ^ 5`. -/
theorem third_moment_le_native [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hπ1 : ∀ e : Sym2 V, (π e : ℝ) < 1)
    (hinv : ∀ a b : V, TreeGraph.twoPoint (fun e => (π e : ℝ))
        (PercLib.CriticalLRP.idBondGraph V) a b
      = TreeGraph.twoPoint (fun e => (π e : ℝ)) (PercLib.CriticalLRP.idBondGraph V) 0 (b - a)) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 3 ∂(edgeMeasure π)
      ≤ 3 * (∫⁻ ω : Config V, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0) ∂(edgeMeasure π)) ^ 5 := by
  have hp0 : ∀ e : Sym2 V, 0 ≤ (π e : ℝ) := fun e => unitInterval.nonneg (π e)
  have hp1 : ∀ e : Sym2 V, (π e : ℝ) ≤ 1 := fun e => unitInterval.le_one (π e)
  have hbk : TreeGraph.BKIncreasing (fun e : Sym2 V => (π e : ℝ)) :=
    TreeGraph.BKIncreasing_of_bkFin _ hp0 (fun e => hπ1 e)
  have hmom := moment_bound_of_bk_expectation (fun e : Sym2 V => (π e : ℝ)) hp0 hp1
    (PercLib.CriticalLRP.idBondGraph V) 0 hinv hbk 3 (by norm_num)
  have hM : ((PercLib.CriticalLRP.VolumeMoments.M (3 - 1) : ℕ) : ℝ) = 3 := by
    norm_num [PercLib.CriticalLRP.VolumeMoments.M]
  rw [hM] at hmom
  have hvol : 0 ≤ TreeGraph.clusterVolume (fun e : Sym2 V => (π e : ℝ))
      (PercLib.CriticalLRP.idBondGraph V) 0 :=
    Finset.sum_nonneg fun y _ => TreeGraph.twoPoint_nonneg hp0 hp1 _ _ _
  rw [lintegral_cardFun_cluster_cube, lintegral_cardFun_cluster]
  calc ENNReal.ofReal (TreeGraph.expectReal (fun e : Sym2 V => (π e : ℝ))
        (fun s => (TreeGraph.clusterVol (PercLib.CriticalLRP.idBondGraph V) s 0 : ℝ) ^ 3))
      ≤ ENNReal.ofReal (3 * TreeGraph.clusterVolume (fun e : Sym2 V => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) 0 ^ 5) := ENNReal.ofReal_le_ofReal hmom
    _ = 3 * (ENNReal.ofReal (TreeGraph.clusterVolume (fun e : Sym2 V => (π e : ℝ))
          (PercLib.CriticalLRP.idBondGraph V) 0)) ^ 5 := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hvol]
        norm_num

/-! ### Translation invariance of the finite model for equivariant edge weights -/

/-- The finite product law is invariant under a vertex translation whenever the edge weights are. -/
theorem configurationLaw_image_eshift [AddCommGroup V] (p : Sym2 V → ℝ)
    (hp : ∀ (c : V) (e : Sym2 V), p (eshift c e) = p e) (c : V) (s : Finset (Sym2 V)) :
    PercLib.CriticalLRP.configurationLaw p (s.image (eshift c)) =
      PercLib.CriticalLRP.configurationLaw p s := by
  rw [PercLib.CriticalLRP.configurationLaw, PercLib.CriticalLRP.configurationLaw]
  refine Fintype.prod_equiv (eshiftEquiv (-c))
    (fun e => if e ∈ s.image (eshift c) then p e else 1 - p e)
    (fun e => if e ∈ s then p e else 1 - p e) ?_
  intro e
  have h := mem_image_eshift_iff c s e
  show (if e ∈ s.image (eshift c) then p e else 1 - p e)
      = (if eshift (-c) e ∈ s then p (eshift (-c) e) else 1 - p (eshift (-c) e))
  rw [hp (-c) e]
  by_cases he : e ∈ s.image (eshift c)
  · rw [ite_eq_left he, ite_eq_left (h.mp he)]
  · rw [ite_eq_right he, ite_eq_right (fun hc => he (h.mpr hc))]

/-- Probabilities are invariant under a vertex translation for equivariant edge weights. -/
theorem prob_image_eshift' [AddCommGroup V] (p : Sym2 V → ℝ)
    (hp : ∀ (c : V) (e : Sym2 V), p (eshift c e) = p e) (c : V)
    (B : Set (Finset (Sym2 V))) :
    TreeGraph.prob p {s | s.image (eshift c) ∈ B} = TreeGraph.prob p B := by
  classical
  simp only [TreeGraph.prob, PercLib.CriticalLRP.probability,
    PercLib.CriticalLRP.expectation]
  refine Fintype.sum_equiv (confShift c)
    (fun s => PercLib.CriticalLRP.configurationLaw p s *
      (if s.image (eshift c) ∈ B then (1 : ℝ) else 0))
    (fun t => PercLib.CriticalLRP.configurationLaw p t *
      (if t ∈ B then (1 : ℝ) else 0)) ?_
  intro s
  have hφ : (confShift c) s = s.image (eshift c) := rfl
  rw [hφ, configurationLaw_image_eshift p hp c s]

/-- **Translation invariance of the two-point function** for equivariant edge weights: the
hypothesis `hinv` of `moment_bound_of_bk`/`second_moment_le_infinite`, derived from the invariance
of the finite model. -/
theorem twoPoint_translation_of_invariant [AddCommGroup V] (p : Sym2 V → ℝ)
    (hp : ∀ (c : V) (e : Sym2 V), p (eshift c e) = p e) (a b : V) :
    TreeGraph.twoPoint p cfgEnds a b = TreeGraph.twoPoint p cfgEnds 0 (b - a) := by
  classical
  unfold TreeGraph.twoPoint
  have hset : {s : Finset (Sym2 V) | TreeGraph.Conn cfgEnds s a b}
      = {s | s.image (eshift (-a)) ∈ {t : Finset (Sym2 V) | TreeGraph.Conn cfgEnds t 0 (b - a)}} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    rw [conn_image_eshift_iff (-a) s a b]
    simp [sub_eq_add_neg]
  rw [hset]
  exact prob_image_eshift' p hp (-a) _

/-- `twoPointE` version of `twoPoint_translation_of_invariant` for `π : Sym2 V → unitInterval`. -/
theorem twoPointE_translation_of_invariant [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hπ : ∀ (c : V) (e : Sym2 V), π (eshift c e) = π e) (a b : V) :
    TreeGraph.twoPointE (fun e => (π e : ℝ)) (PercLib.CriticalLRP.idBondGraph V) a b
      = TreeGraph.twoPointE (fun e => (π e : ℝ)) (PercLib.CriticalLRP.idBondGraph V) 0 (b - a) := by
  have hp : ∀ (c : V) (e : Sym2 V), (fun e : Sym2 V => (π e : ℝ)) (eshift c e)
      = (fun e : Sym2 V => (π e : ℝ)) e := by
    intro c e
    show ((π (eshift c e) : unitInterval) : ℝ) = ((π e : unitInterval) : ℝ)
    rw [hπ c e]
  have h := congrArg ENNReal.ofReal (twoPoint_translation_of_invariant
    (fun e => (π e : ℝ)) hp a b)
  simpa only [TreeGraph.twoPointE, TreeGraph.twoPoint] using h

/-- **Third cluster moment bound for the native law, constant edge weight.**  The hypothesis
`hthird` of `VolumeMoments.cE1_le_three_mul_cube_div_of_finite`, proved for the constant-weight
complete graph on a finite abelian group. -/
theorem third_moment_le_native_const [AddCommGroup V] (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 3 ∂(edgeMeasure (fun _ => p))
      ≤ 3 * (∫⁻ ω : Config V, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0) ∂(edgeMeasure (fun _ => p))) ^ 5 :=
  third_moment_le_native (fun _ => p) (fun _ => hp)
    (fun a b => twoPoint_const_translation (V := V) (p : ℝ) a b)

/-- **Second cluster moment bound for the native law, translation-invariant edge weights.**
`∫⁻ |K_0|² ≤ (∫⁻ |K_0|)³` with **no** residual translation hypothesis: the input `hinv` of
`second_moment_le_native` is derived from the invariance of the finite model. -/
theorem second_moment_le_native_of_translation_invariant [AddCommGroup V]
    (π : Sym2 V → unitInterval) (hπ1 : ∀ e : Sym2 V, (π e : ℝ) < 1)
    (hπinv : ∀ (c : V) (e : Sym2 V), π (eshift c e) = π e) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.clusterVol ω 0) ^ 2 ∂(edgeMeasure π)
      ≤ (∫⁻ ω : Config V, PercLib.CriticalLRP.clusterVol ω 0 ∂(edgeMeasure π)) ^ 3 :=
  second_moment_le_native π hπ1 0 (fun a b => twoPointE_translation_of_invariant π hπinv a b)

/-- **Third cluster moment bound for the native law, translation-invariant edge weights.**
`∫⁻ |K_0|³ ≤ 3 (∫⁻ |K_0|)^5` — the hypothesis `hthird` of
`VolumeMoments.cE1_le_three_mul_cube_div_of_finite` — for any translation-invariant edge weight
with `π e < 1`.  This covers, on a finite abelian group, the paper's cut-off kernels
`π ⟨x,y⟩ = 1 - exp(-(β J_r(y - x)))`. -/
theorem third_moment_le_native_of_translation_invariant [AddCommGroup V]
    (π : Sym2 V → unitInterval) (hπ1 : ∀ e : Sym2 V, (π e : ℝ) < 1)
    (hπinv : ∀ (c : V) (e : Sym2 V), π (eshift c e) = π e) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 3 ∂(edgeMeasure π)
      ≤ 3 * (∫⁻ ω : Config V, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0) ∂(edgeMeasure π)) ^ 5 := by
  have hp : ∀ (c : V) (e : Sym2 V), (fun e : Sym2 V => (π e : ℝ)) (eshift c e)
      = (fun e : Sym2 V => (π e : ℝ)) e := by
    intro c e
    show ((π (eshift c e) : unitInterval) : ℝ) = ((π e : unitInterval) : ℝ)
    rw [hπinv c e]
  exact third_moment_le_native π hπ1 (fun a b => twoPoint_translation_of_invariant _ hp a b)

section Kernel

variable [AddCommGroup V]

/-! ### The paper's kernel form as an instance on a finite abelian group -/

/-- An even kernel `J` on a finite abelian group defines a symmetric edge function
`⟨x,y⟩ ↦ J (y - x)` on unordered pairs.  (The paper's `J(x,y) = J(y,x) = J(0, y - x)` is exactly
an even function of the difference.) -/
noncomputable def kernelJ (J : V → ℝ) (hJ : ∀ x : V, J (-x) = J x) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => J (b - a), by
    intro a b
    show J (b - a) = J (a - b)
    rw [← neg_sub, hJ]⟩

theorem kernelJ_mk (J : V → ℝ) (hJ : ∀ x : V, J (-x) = J x) (a b : V) :
    kernelJ J hJ s(a, b) = J (b - a) :=
  Sym2.lift_mk _ a b

/-- The edge function of an even kernel is translation invariant. -/
theorem kernelJ_eshift (J : V → ℝ) (hJ : ∀ x : V, J (-x) = J x) (c : V) (e : Sym2 V) :
    kernelJ J hJ (eshift c e) = kernelJ J hJ e := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [eshift_mk, kernelJ_mk, kernelJ_mk]
    have h : (b + c) - (a + c) = b - a := by abel
    rw [h]

/-- Nonnegativity of the edge function of a nonnegative even kernel. -/
theorem kernelJ_nonneg (J : V → ℝ) (hJ : ∀ x : V, J (-x) = J x) (hJ0 : ∀ x : V, 0 ≤ J x)
    (e : Sym2 V) : 0 ≤ kernelJ J hJ e := by
  induction e using Sym2.ind with
  | _ a b => rw [kernelJ_mk]; exact hJ0 (b - a)

/-- The cut-off kernel edge probability `π e = 1 - exp (-(β * J e))` of §I.1.2, as an element of
`unitInterval` (so that `edgeMeasure` applies). -/
noncomputable def longRangeWeight (β : ℝ) (hβ : 0 ≤ β) (J : V → ℝ)
    (hJ : ∀ x : V, J (-x) = J x) (hJ0 : ∀ x : V, 0 ≤ J x) : Sym2 V → unitInterval :=
  fun e => ⟨PercLib.CriticalLRP.longRangeEdgeProbability β (kernelJ J hJ e),
    PercLib.CriticalLRP.longRangeEdgeProbability_mem_Icc hβ (kernelJ_nonneg J hJ hJ0 e)⟩

/-- The long-range edge weight of an even kernel is translation invariant. -/
theorem longRangeWeight_invariant (β : ℝ) (hβ : 0 ≤ β) (J : V → ℝ)
    (hJ : ∀ x : V, J (-x) = J x) (hJ0 : ∀ x : V, 0 ≤ J x) (c : V) (e : Sym2 V) :
    longRangeWeight β hβ J hJ hJ0 (eshift c e) = longRangeWeight β hβ J hJ hJ0 e := by
  refine Subtype.ext ?_
  show PercLib.CriticalLRP.longRangeEdgeProbability β (kernelJ J hJ (eshift c e))
      = PercLib.CriticalLRP.longRangeEdgeProbability β (kernelJ J hJ e)
  rw [kernelJ_eshift]

/-- Non-degeneracy is automatic for the long-range edge weight: `1 - exp (-x) < 1` for every real
`x`.  (This is why the paper's cut-off models satisfy `π e < 1` without extra assumptions.) -/
theorem longRangeWeight_lt_one (β : ℝ) (hβ : 0 ≤ β) (J : V → ℝ)
    (hJ : ∀ x : V, J (-x) = J x) (hJ0 : ∀ x : V, 0 ≤ J x) (e : Sym2 V) :
    ((longRangeWeight β hβ J hJ hJ0 e : unitInterval) : ℝ) < 1 := by
  show PercLib.CriticalLRP.longRangeEdgeProbability β (kernelJ J hJ e) < 1
  rw [PercLib.CriticalLRP.longRangeEdgeProbability]
  have h := Real.exp_pos (-(β * kernelJ J hJ e))
  linarith

/-- **(I.2.3) at `q = 2` for the paper's kernel on a finite abelian group**, with no residual
hypothesis: `∫⁻ |K_0|² ≤ (∫⁻ |K_0|)³` for `edgeMeasure` with
`π ⟨x,y⟩ = 1 - exp (-(β J (y - x)))`, `J` even and nonnegative, `β ≥ 0`.  Taking
`V = Fin d → ZMod n` gives the cut-off model in a periodic box. -/
theorem second_moment_le_native_kernel (β : ℝ) (hβ : 0 ≤ β) (J : V → ℝ)
    (hJ : ∀ x : V, J (-x) = J x) (hJ0 : ∀ x : V, 0 ≤ J x) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.clusterVol ω 0) ^ 2
        ∂(edgeMeasure (longRangeWeight β hβ J hJ hJ0))
      ≤ (∫⁻ ω : Config V, PercLib.CriticalLRP.clusterVol ω 0
          ∂(edgeMeasure (longRangeWeight β hβ J hJ hJ0))) ^ 3 :=
  second_moment_le_native_of_translation_invariant _
    (fun e => longRangeWeight_lt_one β hβ J hJ hJ0 e)
    (fun c e => longRangeWeight_invariant β hβ J hJ hJ0 c e)

/-- **(I.2.3) at `q = 3` for the paper's kernel on a finite abelian group**, with no residual
hypothesis: `∫⁻ |K_0|³ ≤ 3 (∫⁻ |K_0|)^5` for `edgeMeasure` with
`π ⟨x,y⟩ = 1 - exp (-(β J (y - x)))`.  This is the hypothesis `hthird` of
`VolumeMoments.cE1_le_three_mul_cube_div_of_finite` for this model. -/
theorem third_moment_le_native_kernel (β : ℝ) (hβ : 0 ≤ β) (J : V → ℝ)
    (hJ : ∀ x : V, J (-x) = J x) (hJ0 : ∀ x : V, 0 ≤ J x) :
    ∫⁻ ω : Config V, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 3 ∂(edgeMeasure (longRangeWeight β hβ J hJ hJ0))
      ≤ 3 * (∫⁻ ω : Config V, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0) ∂(edgeMeasure (longRangeWeight β hβ J hJ hJ0))) ^ 5 :=
  third_moment_le_native_of_translation_invariant _
    (fun e => longRangeWeight_lt_one β hβ J hJ hJ0 e)
    (fun c e => longRangeWeight_invariant β hβ J hJ hJ0 c e)

end Kernel
end
end PercLib.CriticalLRP.TreeExpansion
