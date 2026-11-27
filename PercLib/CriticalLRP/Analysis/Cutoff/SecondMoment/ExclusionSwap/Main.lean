/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwyrvajs`, member `m2`,
direction (B), at production base `f6643492ceecda8b5282ee0d6f3eebafb44ee6f5`.
The reflection equivalence is in `ExclusionSwap.Defs`.

# The `p = 2` exclusion-swap identity of (I.4.14): the coefficient `3` is a theorem

Hutchcroft, *Critical long-range percolation I*, (I.4.14), second equality:

  `d/dr E|K|² = β|J'(r)| E[Σ_{y∈B_r}1(y∉K)|K||K_y|²] + 2β|J'(r)| E[Σ_{y∈B_r}1(y∉K)|K|²|K_y|]`
  `           = 3β|J'(r)| E[Σ_{y∈B_r}1(y∉K)|K||K_y|²]`.

The second equality is *not* an inequality: the two excluded window sums have the same
expectation.  The proof is the vertex reflection `x ↦ y - x`, which swaps `0` and `y`, preserves
the radial cut kernel (`S.ρ` is even, so `dist (y-a) (y-b) = dist a b`) and therefore preserves
`M.cutLaw r`.  Under it `|K_0| ↔ |K_y|`, while `1(y ∉ K_0) ↔ 1(0 ∉ K_y) = 1(y ∉ K_0)` by
symmetry of connectivity.

Consequence: `M.p2RHS r = 3 * M.exclMassQuad r`, i.e. the accepted `p = 2` right-hand side
`exclMassQuad + 2 exclMassSqLin` is exactly three times the *single* excluded quadratic window
mass of the source display, with no bounded comparison and no use of the first-moment defect.

No `sorry`, `admit`, `native_decide` or custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.AlmostEverywhere
public import PercLib.CriticalLRP.Correlation.HvolPermutation
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.ExclusionSwap.Defs

/-! # Exact excluded second-moment swap -/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The reflection `x ↦ y - x` of the vertex set -/


@[simp] theorem reflEquiv_apply (y x : M.V) : M.reflEquiv y x = y - x := rfl

theorem reflEquiv_zero (y : M.V) : M.reflEquiv y 0 = y := by
  funext i; simp [reflEquiv]

theorem reflEquiv_self (y : M.V) : M.reflEquiv y y = 0 := by
  funext i; simp [reflEquiv]

/-! ## 2. The cut kernel is invariant under the reflection -/

theorem toVec_neg (x : M.V) : toVec (-x) = -toVec x := by
  funext i; simp [toVec]

theorem cutKernel_reflEquiv (r : ℝ) (y : M.V) (e : Sym2 M.V) :
    M.cutKernel r (Sym2.map (M.reflEquiv y) e) = M.cutKernel r e := by
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.map_mk]
    change radialSym M.S (FiniteVolume.cutoffProfile M.K r)
        (s(M.reflEquiv y a, M.reflEquiv y b))
      = radialSym M.S (FiniteVolume.cutoffProfile M.K r) (s(a, b))
    rw [radialSym_mk, radialSym_mk]
    by_cases hab : a = b
    · subst hab
      simp [reflEquiv]
    · have hne : M.reflEquiv y a ≠ M.reflEquiv y b :=
        fun h => hab ((M.reflEquiv y).injective h)
      rw [ite_eq_right hne, ite_eq_right hab]
      have hvec : ((y - a) - (y - b) : Fin M.d → ℤ) = -(a - b) := by
        funext i; simp [Pi.sub_apply]
      have : SourceNormData.dist M.S (M.reflEquiv y a) (M.reflEquiv y b)
          = SourceNormData.dist M.S a b := by
        change M.S.ρ (toVec ((y - a) - (y - b))) = M.S.ρ (toVec (a - b))
        rw [hvec, toVec_neg, M.S.ρ_neg]
      rw [this]

/-! ## 3. The cutoff law is invariant under the reflection -/

theorem cutLaw_map_reflEquiv (r : ℝ) (y : M.V) :
    (M.cutLaw r).map (Hvol.permConfig (M.reflEquiv y)) = M.cutLaw r := by
  have hπ : ∀ e : Sym2 M.V,
      bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit
          (Sym2.map (M.reflEquiv y) e)
        = bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e := by
    intro e
    refine Subtype.ext ?_
    rw [bernoulliEdgeProb_coe, bernoulliEdgeProb_coe, M.cutKernel_reflEquiv r y e]
  have := Hvol.edgeMeasure_permConfig_invariant
    (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit) (M.reflEquiv y) hπ
  simpa only [SourceModelData.cutLaw, longRangeMeasure] using this

/-- **Substitution along the reflection.**  For every measurable `ℝ≥0∞`-valued `F`,
`∫ F ∂cutLaw r = ∫ F ∘ permConfig (refl y) ∂cutLaw r`. -/
theorem lintegral_reflEquiv (r : ℝ) (y : M.V) {F : Config M.V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, F ω ∂(M.cutLaw r))
      = ∫⁻ ω, F (Hvol.permConfig (M.reflEquiv y) ω) ∂(M.cutLaw r) := by
  have hmap := M.cutLaw_map_reflEquiv r y
  calc (∫⁻ ω, F ω ∂(M.cutLaw r))
      = ∫⁻ ω, F ω ∂((M.cutLaw r).map (Hvol.permConfig (M.reflEquiv y))) := by rw [hmap]
    _ = ∫⁻ ω, F (Hvol.permConfig (M.reflEquiv y) ω) ∂(M.cutLaw r) :=
        lintegral_map hF (Hvol.measurable_permConfig (M.reflEquiv y))

/-! ## 4. Cluster volumes and the exclusion indicator under the reflection -/

theorem clusterVol_reflEquiv (y : M.V) (ω : Config M.V) (v : M.V) :
    clusterVol (Hvol.permConfig (M.reflEquiv y) ω) (M.reflEquiv y v) = clusterVol ω v := by
  change ((cluster (Hvol.permConfig (M.reflEquiv y) ω) (M.reflEquiv y v)).encard : ℝ≥0∞)
    = ((cluster ω v).encard : ℝ≥0∞)
  rw [Hvol.cluster_permConfig, (M.reflEquiv y).injective.encard_image]

/-- Under the reflection, `y ∈ K_0` becomes `0 ∈ K_y`, which is the same statement by symmetry
of connectivity. -/
theorem mem_image_refl_iff (y : M.V) (ω : Config M.V) :
    y ∈ M.reflEquiv y '' cluster ω y ↔ y ∈ cluster ω (0 : M.V) := by
  rw [Set.mem_image]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have h2 : M.reflEquiv y (M.reflEquiv y z) = (0 : M.V) := by
      rw [hzy, M.reflEquiv_self y]
    have hz0 : z = (0 : M.V) := by
      rw [← (M.reflEquiv y).left_inv z]; exact h2
    exact connects_symm (hz0 ▸ hz)
  · intro h
    exact ⟨(0 : M.V), connects_symm h, M.reflEquiv_zero y⟩

theorem indicator_reflEquiv (y : M.V) (ω : Config M.V) :
    (((cluster (Hvol.permConfig (M.reflEquiv y) ω) (0 : M.V))ᶜ).indicator
        (fun _ => (1 : ℝ≥0∞)) y)
      = (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) := by
  have hcl : cluster (Hvol.permConfig (M.reflEquiv y) ω) (0 : M.V)
      = M.reflEquiv y '' cluster ω y := by
    simpa only [M.reflEquiv_self y] using Hvol.cluster_permConfig (M.reflEquiv y) ω y
  by_cases h : y ∈ cluster ω (0 : M.V)
  · have h' : y ∈ M.reflEquiv y '' cluster ω y := (M.mem_image_refl_iff y ω).mpr h
    rw [hcl, Set.indicator_of_notMem (by simpa using h'),
      Set.indicator_of_notMem (by simpa using h)]
  · have h' : y ∉ M.reflEquiv y '' cluster ω y :=
      fun hh => h ((M.mem_image_refl_iff y ω).mp hh)
    rw [hcl, Set.indicator_of_mem (by simpa using h'),
      Set.indicator_of_mem (by simpa using h)]

/-! ## 5. Measurability of the summands -/

theorem measurable_exclusionIndicator (y : M.V) :
    Measurable fun ω : Config M.V =>
      (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) := by
  classical
  have hEq : (fun ω : Config M.V =>
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y))
      = fun ω => if y ∈ cluster ω (0 : M.V) then (0 : ℝ≥0∞) else 1 := by
    funext ω
    by_cases h : y ∈ cluster ω (0 : M.V)
    · rw [ite_eq_left h, Set.indicator_of_notMem (by simpa using h)]
    · rw [ite_eq_right h, Set.indicator_of_mem (by simpa using h)]
  rw [hEq]
  exact Measurable.ite (measurableSet_cluster_mem (0 : M.V) y) measurable_const measurable_const

theorem measurable_summandQuad (y : M.V) (_r : ℝ) :
    Measurable fun ω : Config M.V =>
      clusterVol ω (0 : M.V) *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2) := by
  have h0 : Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) := measurable_clusterVol (0 : M.V)
  have hy : Measurable fun ω : Config M.V => clusterVol ω y := measurable_clusterVol y
  have hi : Measurable fun ω : Config M.V =>
      (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) :=
    M.measurable_exclusionIndicator y
  exact h0.mul (hi.mul (hy.pow_const 2))

theorem measurable_summandLin (y : M.V) (_r : ℝ) :
    Measurable fun ω : Config M.V =>
      clusterVol ω (0 : M.V) ^ 2 *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y) := by
  have h0 : Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) := measurable_clusterVol (0 : M.V)
  have hy : Measurable fun ω : Config M.V => clusterVol ω y := measurable_clusterVol y
  have hi : Measurable fun ω : Config M.V =>
      (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) :=
    M.measurable_exclusionIndicator y
  exact (h0.pow_const 2).mul (hi.mul hy)

/-! ## 6. The per-`y` swap -/

/-- **The per-vertex exclusion swap.**  For every finite summand vertex `y`, the two excluded
`p = 2` moments `E[|K_0| 1(y∉K_0)|K_y|²]` and `E[|K_0|² 1(y∉K_0)|K_y|]` are equal. -/
theorem lintegral_summand_swap (r : ℝ) (y : M.V) :
    (∫⁻ ω, clusterVol ω (0 : M.V) *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
        ∂(M.cutLaw r))
      = ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
        ∂(M.cutLaw r) := by
  rw [M.lintegral_reflEquiv r y (M.measurable_summandLin y r)]
  refine lintegral_congr fun ω => ?_
  have ha : clusterVol (Hvol.permConfig (M.reflEquiv y) ω) (0 : M.V) = clusterVol ω y := by
    simpa only [M.reflEquiv_self y] using M.clusterVol_reflEquiv y ω y
  have hb : clusterVol (Hvol.permConfig (M.reflEquiv y) ω) y = clusterVol ω (0 : M.V) := by
    simpa only [M.reflEquiv_zero y] using M.clusterVol_reflEquiv y ω (0 : M.V)
  rw [ha, hb, M.indicator_reflEquiv y ω]
  ring

/-! ## 7. Summing over the finite window: the two excluded masses agree -/

/-- **`exclMassQuad r = exclMassSqLin r`.**  The two excluded window masses of Lemma I.4.1 at
`p = 2` are equal at every radius, by the per-vertex reflection of
`lintegral_summand_swap` and the finiteness of the closed window `B_r`. -/
theorem exclMassQuad_eq_exclMassSqLin (r : ℝ) :
    M.exclMassQuad r = M.exclMassSqLin r := by
  have hL : M.exclMassQuad r = ∫⁻ ω, ∑ y ∈ E1Sign.ballF M r,
      clusterVol ω (0 : M.V) *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2)
      ∂(M.cutLaw r) := by
    simp only [SourceModelData.exclMassQuad, SourceModelData.exclSumQuad, Finset.mul_sum]
  have hR : M.exclMassSqLin r = ∫⁻ ω, ∑ y ∈ E1Sign.ballF M r,
      clusterVol ω (0 : M.V) ^ 2 *
        (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
      ∂(M.cutLaw r) := by
    simp only [SourceModelData.exclMassSqLin, SourceModelData.exclSumLin, Finset.mul_sum]
  rw [hL, hR,
    lintegral_finsetSum (E1Sign.ballF M r) (fun y _ => M.measurable_summandQuad y r),
    lintegral_finsetSum (E1Sign.ballF M r) (fun y _ => M.measurable_summandLin y r)]
  exact Finset.sum_congr rfl fun y _ => M.lintegral_summand_swap r y

/-- **The coefficient `3` of (I.4.14) is an identity.**  The accepted `p = 2` right-hand side
`p2RHS r = exclMassQuad r + 2 * exclMassSqLin r` (the `ℓ = 0` and `ℓ = 1` excluded terms with
their binomial coefficients) equals three times the single excluded quadratic window mass
`E[|K| Σ_{y∈B_r, y∉K}|K_y|²]` of the source display. -/
theorem p2RHS_eq_three_mul_exclMassQuad (r : ℝ) :
    M.p2RHS r = 3 * M.exclMassQuad r := by
  rw [SourceModelData.p2RHS, M.exclMassQuad_eq_exclMassSqLin r]
  ring

/-- The real-valued form of the same identity: the source's `p = 2` right-hand side, divided by
the coefficient `β|J'(r)|`, is `3 U` with `U = E[|K| Σ_{y∈B_r, y∉K}|K_y|²]` the single excluded
quadratic window mass. -/
theorem p2RHS_toReal_eq_three_mul (r : ℝ) :
    (M.p2RHS r).toReal = 3 * (M.exclMassQuad r).toReal := by
  rw [M.p2RHS_eq_three_mul_exclMassQuad r, ENNReal.toReal_mul, ENNReal.toReal_ofNat]

end SourceModelData
end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_reflEquiv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_map_reflEquiv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.lintegral_summand_swap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuad_eq_exclMassSqLin
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_eq_three_mul_exclMassQuad
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_toReal_eq_three_mul
