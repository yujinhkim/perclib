/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Cutoff cluster moments for the source model, from the first moment

The paper's Theorem I.1.6 asserts `E_{β_c,r} |K|^p < ∞` for every `p ≥ 1` at every
finite `r`.  The tree-graph third-moment bound
(`TreeExpansion.Native.cutoff_thirdMoment_ne_top_of_firstMoment`) reduces `p = 3` to
`p = 1` for the native Definition I.1.5 kernel `CutoffKernel.cutoffSymKernel`, which
uses the `ℓ∞` lattice norm directly.

This file builds the missing bridge for the source-model vocabulary: if the source
norm `M.S.ρ` is `c` times the `ℓ∞` norm on lattice differences, then the source
cut-off kernel `M.cutKernel r` is *literally* the native kernel with profile
`t ↦ M.K (c * t)` at the rescaled radius `r / c`.  The scale is not cosmetic: the
source witness uses `ρ v = 2‖v‖∞`, so its nearest-neighbour cutoff radius is `2`,
not `1`.

Consequently, for such `M`, finiteness of `M.cutMoment 1 r` implies finiteness of
`M.cutMoment 3 r` (and then `M.cutMoment 2 r`, since every cluster contains its
root).  The first moment is *not* discharged here: it is the subcritical mean
finiteness input of Theorem I.1.6, kept as an explicit hypothesis.

No new definitions, no `sorry`, no `admit`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.CutoffThirdMomentFinite
public import PercLib.CriticalLRP.Orchestration.ModelWitness.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect

/-!
# Moment transfer from native cutoff kernels to source models

For source norms that are a positive multiple of the lattice sup norm, the source cutoff
law is identified exactly with the native cutoff law after rescaling the profile and
radius. The translation-invariant third-moment bound then turns a finite first cutoff
moment into finite second and third cutoff moments. The finite first moment remains a
hypothesis, including at the explicit power-law model.
-/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

/-! ## Rescaling the Definition I.1.5 cut-off profile -/

/-- The cut-off profile of Definition I.1.5 rescales: cutting the profile
`t ↦ K (c t)` at `r / c` is the same as cutting `K` at `r` and evaluating at `c s`. -/
theorem cutoffProfile_scale {K : ℝ → ℝ} {c r s : ℝ} (hc : 0 < c) :
    FiniteVolume.cutoffProfile (fun t => K (c * t)) (r / c) s
      = FiniteVolume.cutoffProfile K r (c * s) := by
  have key : s ≤ r / c ↔ c * s ≤ r := by
    rw [le_div_iff₀ hc]
    constructor <;> intro h <;> linarith
  unfold FiniteVolume.cutoffProfile
  by_cases h : c * s ≤ r
  · rw [ite_eq_left (key.mpr h), ite_eq_left h]
    have hcr : c * (r / c) = r := by
      rw [mul_comm, div_mul_cancel₀ _ hc.ne']
    change K (c * s) - K (c * (r / c)) = K (c * s) - K r
    rw [hcr]
  · rw [ite_eq_right (fun hs => h (key.mp hs)), ite_eq_right h]

/-! ## The source cut-off kernel is the native kernel after rescaling the norm -/

/-- **The kernel bridge.**  If the source norm of a lattice difference is `c` times the
`ℓ∞` norm, then the source cut-off kernel at radius `r` is the native Definition I.1.5
cut-off kernel, with profile `t ↦ M.K (c t)` and radius `r / c`.  Both kernels vanish
on loops and both use the profile-difference form of `J_r`. -/
theorem cutKernel_eq_cutoffSymKernel (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) (r : ℝ) :
    M.cutKernel r =
      CutoffKernel.cutoffSymKernel (fun t => M.K (c * t)) M.d (r / c) := by
  funext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [SourceModelData.cutKernel, cutRadialSym, radialSym_mk, CutoffKernel.cutoffSymKernel_mk]
    by_cases hxy : x = y
    · simp only [hxy, ite_true]
    · rw [ite_eq_right hxy, ite_eq_right hxy, SourceNormData.dist, hρ, cutoffProfile_scale hc]

/-- The native cluster cardinality is the source-model cluster volume.  (The committed
`TreeExpansion.cardFun_cluster_eq_clusterVol` requires `[Fintype V]`, unavailable on the
infinite lattice; `cardFun_eq_encard` gives the statement in general.) -/
theorem cardFun_cluster_eq_clusterVol' (M : SourceModelData) (ω : Config M.V) (x : M.V) :
    Percolation.cardFun (cluster ω x) = clusterVol ω x := by
  rw [Percolation.cardFun_eq_encard]

/-- **The law bridge**: the source cut-off law is the native cut-off law at the
rescaled profile and radius. -/
theorem cutLaw_eq_native (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) :
    M.cutLaw r =
      longRangeMeasure (CutoffKernel.cutoffSymKernel (fun t => M.K (c * t)) M.d (r / c))
        (CutoffKernel.cutoffSymKernel_nonneg (r := r / c) (by
          intro s hs t ht hst
          exact M.K_antitone (mul_pos hc hs) (mul_pos hc ht)
            (mul_le_mul_of_nonneg_left hst hc.le)) (by positivity))
        M.betaCrit := by
  rw [SourceModelData.cutLaw]
  simp only [cutKernel_eq_cutoffSymKernel M hc hρ r]

/-- **The moment bridge**: in the rescaled coordinates the source `p`-th cut-off moment
is the native `p`-th moment of the cluster volume. -/
theorem cutMoment_eq_native (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (p : ℕ) :
    M.cutMoment p r =
      ∫⁻ ω, (Percolation.cardFun (cluster ω (0 : M.V))) ^ p
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel (fun t => M.K (c * t)) M.d (r / c))
          (CutoffKernel.cutoffSymKernel_nonneg (r := r / c) (by
            intro s hs t ht hst
            exact M.K_antitone (mul_pos hc hs) (mul_pos hc ht)
              (mul_le_mul_of_nonneg_left hst hc.le)) (by positivity))
          M.betaCrit) := by
  rw [SourceModelData.cutMoment, cutLaw_eq_native M hc hρ hr]
  refine lintegral_congr fun ω => ?_
  rw [cardFun_cluster_eq_clusterVol']

/-! ## Finiteness of the second and third cut-off moments -/

/-- **Third cut-off moment finite from the first**, for a source model whose norm is a
positive multiple of the `ℓ∞` norm.  This is the `p = 3` case of Theorem I.1.6 in the
source-model vocabulary, with the first moment kept as the only input. -/
theorem cutMoment_three_ne_top_of_one (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) :
    M.cutMoment 3 r ≠ ⊤ := by
  have hKanti : AntitoneOn (fun t => M.K (c * t)) (Set.Ioi 0) := by
    intro s hs t ht hst
    exact M.K_antitone (mul_pos hc hs) (mul_pos hc ht)
      (mul_le_mul_of_nonneg_left hst hc.le)
  have hr' : 0 < r / c := by positivity
  have h1' : (∫⁻ ω, Percolation.cardFun (cluster ω (0 : M.V))
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel (fun t => M.K (c * t)) M.d (r / c))
        (CutoffKernel.cutoffSymKernel_nonneg hKanti hr') M.betaCrit)) ≠ ⊤ := by
    rw [cutMoment_eq_native M hc hρ hr 1] at h1
    simpa only [pow_one] using h1
  have h3' := TreeExpansion.Native.cutoff_thirdMoment_ne_top_of_firstMoment
    hKanti hr' M.betaCrit h1'
  rwa [cutMoment_eq_native M hc hρ hr 3]

/-- **Second cut-off moment finite from the third** (every cluster contains its root, so
`|K|² ≤ |K|³`).  Combined with `cutMoment_three_ne_top_of_one` this gives the `p = 2`
case of Theorem I.1.6 from the first moment. -/
theorem cutMoment_two_ne_top_of_three (M : SourceModelData) {r : ℝ}
    (h3 : M.cutMoment 3 r ≠ ⊤) : M.cutMoment 2 r ≠ ⊤ := by
  refine ne_top_of_le_ne_top h3 ?_
  refine lintegral_mono fun ω => ?_
  calc (clusterVol ω (0 : M.V)) ^ 2
      ≤ (clusterVol ω (0 : M.V)) ^ 3 :=
        pow_le_pow_right₀ (E1Sign.one_le_clusterVol M ω 0) (by norm_num)
    _ = _ := rfl

/-- **Second cut-off moment finite from the first.** -/
theorem cutMoment_two_ne_top_of_one (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ}
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) :
    M.cutMoment 2 r ≠ ⊤ :=
  cutMoment_two_ne_top_of_three M (cutMoment_three_ne_top_of_one M hc hρ hr h1)

/-! ## The source witness: `ρ v = 2 ‖v‖∞` -/

namespace Witness

/-- The `ℓ∞` norm of `ℤ^d` is the operator norm of its real embedding. -/
theorem norm_toVec_eq_linfNorm {d : ℕ} (hd : 1 ≤ d) (z : Fin d → ℤ) :
    ‖toVec z‖ = (FiniteVolume.linfNorm z : ℝ) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun i => (z i).natAbs)
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    intro j
    have hji : ‖toVec z j‖ = ((z j).natAbs : ℝ) := by simp [toVec]
    rw [hji]
    have hle : (z j).natAbs ≤ FiniteVolume.linfNorm z := by
      rw [FiniteVolume.linfNorm]
      exact Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ j)
    exact_mod_cast hle
  · have hsup : FiniteVolume.linfNorm z = (z i).natAbs := by
      rw [FiniteVolume.linfNorm]; exact hi
    rw [hsup]
    have hcast : ((z i).natAbs : ℝ) = ‖toVec z i‖ := by simp [toVec]
    rw [hcast]
    exact norm_le_pi_norm (toVec z) i

/-- The witness norm is twice the `ℓ∞` norm, so its normalization constant is `c = 2`. -/
theorem sourceModelWitness_dist_eq (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    ∀ z : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec z) = 2 * (FiniteVolume.linfNorm z : ℝ) := by
  intro z
  simp only [sourceModelWitness, sourceNormWitness]
  rw [norm_toVec_eq_linfNorm hd z]

/-- **`p = 3` at the source witness, from the first moment.** -/
theorem sourceModelWitness_cutMoment_three_ne_top (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : 0 < r)
    (h1 : (sourceModelWitness d hd α hα).cutMoment 1 r ≠ ⊤) :
    (sourceModelWitness d hd α hα).cutMoment 3 r ≠ ⊤ :=
  cutMoment_three_ne_top_of_one _ (by norm_num) (sourceModelWitness_dist_eq d hd α hα) hr h1

/-- **`p = 2` at the source witness, from the first moment.** -/
theorem sourceModelWitness_cutMoment_two_ne_top (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : 0 < r)
    (h1 : (sourceModelWitness d hd α hα).cutMoment 1 r ≠ ⊤) :
    (sourceModelWitness d hd α hα).cutMoment 2 r ≠ ⊤ :=
  cutMoment_two_ne_top_of_one _ (by norm_num) (sourceModelWitness_dist_eq d hd α hα) hr h1

end Witness

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.cutoffProfile_scale
#print axioms PercLib.CriticalLRP.Orchestration.cutKernel_eq_cutoffSymKernel
#print axioms PercLib.CriticalLRP.Orchestration.cardFun_cluster_eq_clusterVol'
#print axioms PercLib.CriticalLRP.Orchestration.cutLaw_eq_native
#print axioms PercLib.CriticalLRP.Orchestration.cutMoment_eq_native
#print axioms PercLib.CriticalLRP.Orchestration.cutMoment_three_ne_top_of_one
#print axioms PercLib.CriticalLRP.Orchestration.cutMoment_two_ne_top_of_three
#print axioms PercLib.CriticalLRP.Orchestration.Witness.norm_toVec_eq_linfNorm
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_cutMoment_three_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_cutMoment_two_ne_top
