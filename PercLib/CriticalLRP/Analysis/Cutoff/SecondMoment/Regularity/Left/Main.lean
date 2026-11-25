/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The strict-left limit of the `p = 2` excluded RHS

Swarm `smwvc1d9z`, member `m4`, direction `d3`.

Integration donor: `.ultramath/smwvc1d9z/m4`; independently checked at
`4bb37c4a38e226728ba0b9d8732d9ddebbbdded3`.

Hutchcroft, *Critical long-range percolation I*, Lemma I.4.1 expresses the `p = 2` second-moment
flux through the closed-window mass `p2RHS r = E[|K_0| ∑_{y∈B_r, y∉K_0}|K_y|²] +
2 E[|K_0|² ∑_{y∈B_r, y∉K_0}|K_y|]`, where `B_r = {y | ρ y ≤ r}` is the *closed* window.
`SecondMoment/Regularity/Main` rewrites it as the difference of the three monotone marked window
masses and proves the **right** continuity `tendsto_p2RHS_toReal_nhdsGT`; it also states that the
remaining input for two-sided continuity is the **left** limit
(`continuousAt_p2RHS_toReal_of_left`), which is not a consequence of right continuity because the
closed window changes discontinuously at an attained radius.

This file proves that left limit, with no attainment hypothesis and no shell cancellation:

* as `r ↑ r₀` a closed-window mass at the law `cutLaw r` increases to the strict-window mass
  `{ρ < r₀}` at the law `cutLaw r₀` (monotone convergence, `iSup_*Mass_nat`);
* consequently `(p2RHS r).toReal → (p2RHSStrict r₀).toReal` (`tendsto_p2RHS_toReal_nhdsLT`), where
  `p2RHSStrict` is the landed strict-window companion of `SecondMoment/Defs`;
* off the sphere `{ρ = r₀}` the strict and closed windows coincide, so there the one-sided limit is
  a two-sided limit and `p2RHS` is `ContinuousAt` (`continuousAt_p2RHS_toReal_of_no_sphere`).

At an *attained* radius the left limit is `p2RHSStrict r₀` and the right limit is `p2RHS r₀`; the
difference is exactly the shell layer `p2RHSShell r₀` (`SecondMoment/Corner`), which is why this
file does **not** claim two-sided differentiability or continuity at attained radii.

Definitions are in `Defs.lean`.  No `sorry`, `admit`, `native_decide` or custom axiom; only the
standard axioms enter (audit at the end of the file).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Left.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Corner

/-!
# The left limit of the `p = 2` excluded RHS

The strict-window marked masses are right continuous and monotone, their left limits are the landed
`p2RHSStrict`, and off the sphere the two-sided statement follows.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. Measurability of the strict-window integrands -/

theorem measurable_quadWindowSumLt (r : ℝ) :
    Measurable fun u : Sym2 M.V → ℝ =>
      ∑ y ∈ M.ballFLt r, clusterVol (atParameter (M.cutProb r) u) y ^ 2 :=
  Finset.measurable_sum _ fun y _ =>
    ((measurable_clusterVol y).comp (measurable_atParameter _)).pow_const 2

theorem measurable_sqLinWindowSumLt (r : ℝ) :
    Measurable fun u : Sym2 M.V → ℝ =>
      ∑ y ∈ M.ballFLt r, clusterVol (atParameter (M.cutProb r) u) y :=
  Finset.measurable_sum _ fun y _ =>
    (measurable_clusterVol y).comp (measurable_atParameter _)

theorem measurable_connWindowSumLt (r : ℝ) :
    Measurable fun u : Sym2 M.V → ℝ =>
      ∑ y ∈ M.ballFLt r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y :=
  Finset.measurable_sum _ fun y _ =>
    measurable_const.indicator
      ((measurableSet_cluster_mem (0 : M.V) y).preimage (measurable_atParameter _))

theorem measurable_quadPairFunLt (r : ℝ) : Measurable (M.quadPairFunLt r) :=
  (M.measurable_markVol r).mul (M.measurable_quadWindowSumLt r)

theorem measurable_sqLinPairFunLt (r : ℝ) : Measurable (M.sqLinPairFunLt r) :=
  ((M.measurable_markVol r).pow_const 2).mul (M.measurable_sqLinWindowSumLt r)

theorem measurable_connCubeFunLt (r : ℝ) : Measurable (M.connCubeFunLt r) :=
  ((M.measurable_markVol r).pow_const 3).mul (M.measurable_connWindowSumLt r)

/-! ## 2. Pointwise exhaustion of the strict window

For `r n ↑ r₀` the closed window `B_{r n}` exhausts `{ρ < r₀}` and the cluster at `cutProb (r n)`
increases to the cluster at `cutProb r₀`, so the window sums increase to the strict-window sum at
`r₀`.  The `k = 1` and indicator cases are the landed `iSup_pairWindowSum`/`iSup_windowSum`; the
next lemma is the `clusterVol ^ k` version that covers `k = 2` (`quadPairFun`). -/

theorem iSup_clusterWindowSum_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0))
    (k : ℕ) (u : Sym2 M.V → ℝ) :
    (⨆ n, ∑ y ∈ E1Sign.ballF M (r n),
      clusterVol (atParameter (M.cutProb (r n)) u) y ^ k)
      = ∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y ^ k := by
  classical
  have hr0 : 0 < r0 := lt_trans (hpos 0) (hlt 0)
  have hmonoProb : ∀ (n : ℕ) (e : Sym2 M.V),
      M.cutProb (r n) e ≤ M.cutProb (r (n + 1)) e :=
    fun n e => M.cutProb_mono (hpos n) (hpos (n + 1)) (hmono n) e
  have hlimProb : ∀ e : Sym2 M.V,
      Tendsto (fun n : ℕ => ((M.cutProb (r n) e : unitInterval) : ℝ)) atTop
        (𝓝 ((M.cutProb r0 e : unitInterval) : ℝ)) :=
    fun e => (M.continuousAt_cutProb r0 hr0 e).tendsto.comp hlim
  have hsup : ∀ y : M.V, clusterVol (atParameter (M.cutProb r0) u) y
      = ⨆ n, clusterVol (atParameter (M.cutProb (r n)) u) y :=
    fun y => PercLib.CriticalLRP.CutoffMomentTransfer.clusterVol_atParameter_eq_iSup
      hmonoProb hlimProb u y
  have hsub : ∀ n, E1Sign.ballF M (r n) ⊆ M.ballFLt r0 := by
    intro n y hy
    exact M.mem_ballFLt.mpr (lt_of_le_of_lt ((M.mem_ballF_rho).mp hy) (hlt n))
  have hmono_le : ∀ n m : ℕ, n ≤ m → r n ≤ r m := monotone_nat_of_le_succ hmono
  have hmono_g : ∀ y : M.V, Monotone fun n =>
      clusterVol (atParameter (M.cutProb (r n)) u) y ^ k :=
    fun y n m hnm =>
      pow_le_pow_left' (M.clusterVol_atParameter_mono (hpos n) (hpos m)
        (hmono_le n m hnm) u y) k
  have hex : ∀ y ∈ M.ballFLt r0, ∃ N : ℕ, ∀ n ≥ N, y ∈ E1Sign.ballF M (r n) := by
    intro y hy
    have hρ : M.S.ρ (toVec y) < r0 := M.mem_ballFLt.mp hy
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (Ioi_mem_nhds hρ))
    exact ⟨N, fun n hn => (M.mem_ballF_rho).mpr (le_of_lt (hN n hn))⟩
  refine le_antisymm (iSup_le fun n => ?_) ?_
  · calc (∑ y ∈ E1Sign.ballF M (r n),
          clusterVol (atParameter (M.cutProb (r n)) u) y ^ k)
        ≤ ∑ y ∈ E1Sign.ballF M (r n),
            clusterVol (atParameter (M.cutProb r0) u) y ^ k :=
          Finset.sum_le_sum fun y _ =>
            pow_le_pow_left' (M.clusterVol_atParameter_mono (hpos n) hr0
              (le_of_lt (hlt n)) u y) k
      _ ≤ ∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y ^ k :=
          Finset.sum_le_sum_of_subset_of_nonneg (hsub n) (fun _ _ _ => zero_le)
  · have h1 : (∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y ^ k)
        = ∑ y ∈ M.ballFLt r0,
            ⨆ n, clusterVol (atParameter (M.cutProb (r n)) u) y ^ k := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← ENNReal.iSup_pow, hsup y]
    rw [h1, M.iSup_finset_sum_nat hmono_g]
    choose N hN using hex
    refine iSup_le fun n => ?_
    set M₀ : ℕ := (M.ballFLt r0).attach.sup (fun y => N y.1 y.2) with hM₀
    have hM₀spec : ∀ y ∈ M.ballFLt r0, y ∈ E1Sign.ballF M (r M₀) := by
      intro y hy
      have hle : N y hy ≤ M₀ :=
        Finset.le_sup (f := fun y : {y // y ∈ M.ballFLt r0} => N y.1 y.2)
          (Finset.mem_attach _ ⟨y, hy⟩)
      exact hN y hy M₀ hle
    have hstep : (∑ y ∈ M.ballFLt r0,
        clusterVol (atParameter (M.cutProb (r n)) u) y ^ k)
        ≤ ∑ y ∈ E1Sign.ballF M (r (max n M₀)),
            clusterVol (atParameter (M.cutProb (r (max n M₀))) u) y ^ k := by
      refine le_trans (Finset.sum_le_sum fun y _ => hmono_g y (le_max_left n M₀)) ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => zero_le)
      intro y hy
      exact (M.mem_ballF_rho).mpr
        (le_trans ((M.mem_ballF_rho).mp (hM₀spec y hy))
          (hmono_le M₀ (max n M₀) (le_max_right n M₀)))
    exact le_trans hstep (le_iSup (fun k' => ∑ y ∈ E1Sign.ballF M (r k'),
      clusterVol (atParameter (M.cutProb (r k')) u) y ^ k) (max n M₀))

/-- The `k = 1` case, restated: the landed `iSup_pairWindowSum`. -/
theorem iSup_clusterWindowSum_one {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0))
    (u : Sym2 M.V → ℝ) :
    (⨆ n, ∑ y ∈ E1Sign.ballF M (r n),
      clusterVol (atParameter (M.cutProb (r n)) u) y)
      = ∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y := by
  simpa using M.iSup_clusterWindowSum_nat hpos hlt hmono hlim 1 u

/-- The indicator case, restated: the landed `iSup_windowSum`. -/
theorem iSup_connWindowSum_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0))
    (u : Sym2 M.V → ℝ) :
    (⨆ n, ∑ y ∈ E1Sign.ballF M (r n),
      (cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y)
      = ∑ y ∈ M.ballFLt r0,
        (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y :=
  M.iSup_windowSum hpos hlt hmono hlim u

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

namespace PercLib.CriticalLRP.Orchestration

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology
open PercLib.CriticalLRP

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 3. The pointwise supremum of the three integrands -/

theorem iSup_quadPairFun_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) (u : Sym2 M.V → ℝ) :
    (⨆ n, M.quadPairFun (r n) u) = M.quadPairFunLt r0 u := by
  classical
  have hr0 : 0 < r0 := lt_trans (hpos 0) (hlt 0)
  have hmonoProb : ∀ (n : ℕ) (e : Sym2 M.V),
      M.cutProb (r n) e ≤ M.cutProb (r (n + 1)) e :=
    fun n e => M.cutProb_mono (hpos n) (hpos (n + 1)) (hmono n) e
  have hlimProb : ∀ e : Sym2 M.V,
      Tendsto (fun n : ℕ => ((M.cutProb (r n) e : unitInterval) : ℝ)) atTop
        (𝓝 ((M.cutProb r0 e : unitInterval) : ℝ)) :=
    fun e => (M.continuousAt_cutProb r0 hr0 e).tendsto.comp hlim
  have hvol : (⨆ n, M.markVol (r n) u) = M.markVol r0 u :=
    (PercLib.CriticalLRP.CutoffMomentTransfer.clusterVol_atParameter_eq_iSup
      hmonoProb hlimProb u 0).symm
  have hsum := M.iSup_clusterWindowSum_nat hpos hlt hmono hlim 2 u
  have hmonoA : Monotone fun n => M.markVol (r n) u := fun n m hnm =>
    M.clusterVol_atParameter_mono (hpos n) (hpos m)
      (monotone_nat_of_le_succ hmono hnm) u 0
  have hmonoB : Monotone fun n => ∑ y ∈ E1Sign.ballF M (r n),
      clusterVol (atParameter (M.cutProb (r n)) u) y ^ 2 := by
    intro n m hnm
    have hnm' : r n ≤ r m := monotone_nat_of_le_succ hmono hnm
    calc (∑ y ∈ E1Sign.ballF M (r n),
          clusterVol (atParameter (M.cutProb (r n)) u) y ^ 2)
        ≤ ∑ y ∈ E1Sign.ballF M (r n),
            clusterVol (atParameter (M.cutProb (r m)) u) y ^ 2 :=
          Finset.sum_le_sum fun y _ =>
            pow_le_pow_left' (M.clusterVol_atParameter_mono (hpos n) (hpos m) hnm' u y) 2
      _ ≤ ∑ y ∈ E1Sign.ballF M (r m),
            clusterVol (atParameter (M.cutProb (r m)) u) y ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (M.ballF_mono hnm') (fun _ _ _ => zero_le)
  simp only [SourceModelData.quadPairFun, SourceModelData.quadPairFunLt]
  rw [← hvol, ← hsum]
  exact PercLib.CriticalLRP.iSup_mul_iSup_nat hmonoA hmonoB

theorem iSup_sqLinPairFun_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) (u : Sym2 M.V → ℝ) :
    (⨆ n, M.sqLinPairFun (r n) u) = M.sqLinPairFunLt r0 u := by
  classical
  have hr0 : 0 < r0 := lt_trans (hpos 0) (hlt 0)
  have hmonoProb : ∀ (n : ℕ) (e : Sym2 M.V),
      M.cutProb (r n) e ≤ M.cutProb (r (n + 1)) e :=
    fun n e => M.cutProb_mono (hpos n) (hpos (n + 1)) (hmono n) e
  have hlimProb : ∀ e : Sym2 M.V,
      Tendsto (fun n : ℕ => ((M.cutProb (r n) e : unitInterval) : ℝ)) atTop
        (𝓝 ((M.cutProb r0 e : unitInterval) : ℝ)) :=
    fun e => (M.continuousAt_cutProb r0 hr0 e).tendsto.comp hlim
  have hvol : (⨆ n, M.markVol (r n) u) = M.markVol r0 u :=
    (PercLib.CriticalLRP.CutoffMomentTransfer.clusterVol_atParameter_eq_iSup
      hmonoProb hlimProb u 0).symm
  have hvol2 : (⨆ n, (M.markVol (r n) u) ^ 2) = (M.markVol r0 u) ^ 2 := by
    rw [← ENNReal.iSup_pow, hvol]
  have hsum := M.iSup_pairWindowSum hpos hlt hmono hlim u
  have hmonoA : Monotone fun n => (M.markVol (r n) u) ^ 2 := fun n m hnm =>
    pow_le_pow_left' (M.clusterVol_atParameter_mono (hpos n) (hpos m)
      (monotone_nat_of_le_succ hmono hnm) u 0) 2
  have hmonoB : Monotone fun n => ∑ y ∈ E1Sign.ballF M (r n),
      clusterVol (atParameter (M.cutProb (r n)) u) y := by
    intro n m hnm
    have hnm' : r n ≤ r m := monotone_nat_of_le_succ hmono hnm
    calc (∑ y ∈ E1Sign.ballF M (r n),
          clusterVol (atParameter (M.cutProb (r n)) u) y)
        ≤ ∑ y ∈ E1Sign.ballF M (r n),
            clusterVol (atParameter (M.cutProb (r m)) u) y :=
          Finset.sum_le_sum fun y _ =>
            M.clusterVol_atParameter_mono (hpos n) (hpos m) hnm' u y
      _ ≤ ∑ y ∈ E1Sign.ballF M (r m),
            clusterVol (atParameter (M.cutProb (r m)) u) y :=
          Finset.sum_le_sum_of_subset_of_nonneg (M.ballF_mono hnm') (fun _ _ _ => zero_le)
  simp only [SourceModelData.sqLinPairFun, SourceModelData.sqLinPairFunLt]
  rw [← hvol2, ← hsum]
  exact PercLib.CriticalLRP.iSup_mul_iSup_nat hmonoA hmonoB

theorem iSup_connCubeFun_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) (u : Sym2 M.V → ℝ) :
    (⨆ n, M.connCubeFun (r n) u) = M.connCubeFunLt r0 u := by
  classical
  have hr0 : 0 < r0 := lt_trans (hpos 0) (hlt 0)
  have hmonoProb : ∀ (n : ℕ) (e : Sym2 M.V),
      M.cutProb (r n) e ≤ M.cutProb (r (n + 1)) e :=
    fun n e => M.cutProb_mono (hpos n) (hpos (n + 1)) (hmono n) e
  have hlimProb : ∀ e : Sym2 M.V,
      Tendsto (fun n : ℕ => ((M.cutProb (r n) e : unitInterval) : ℝ)) atTop
        (𝓝 ((M.cutProb r0 e : unitInterval) : ℝ)) :=
    fun e => (M.continuousAt_cutProb r0 hr0 e).tendsto.comp hlim
  have hvol : (⨆ n, M.markVol (r n) u) = M.markVol r0 u :=
    (PercLib.CriticalLRP.CutoffMomentTransfer.clusterVol_atParameter_eq_iSup
      hmonoProb hlimProb u 0).symm
  have hvol3 : (⨆ n, (M.markVol (r n) u) ^ 3) = (M.markVol r0 u) ^ 3 := by
    rw [← ENNReal.iSup_pow, hvol]
  have hsum := M.iSup_connWindowSum_nat hpos hlt hmono hlim u
  have hmonoA : Monotone fun n => (M.markVol (r n) u) ^ 3 := fun n m hnm =>
    pow_le_pow_left' (M.clusterVol_atParameter_mono (hpos n) (hpos m)
      (monotone_nat_of_le_succ hmono hnm) u 0) 3
  have hmonoB : Monotone fun n => ∑ y ∈ E1Sign.ballF M (r n),
      (cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y := by
    intro n m hnm
    have hnm' : r n ≤ r m := monotone_nat_of_le_succ hmono hnm
    have hcl : cluster (atParameter (M.cutProb (r n)) u) (0 : M.V) ⊆
        cluster (atParameter (M.cutProb (r m)) u) (0 : M.V) :=
      cluster_mono (fun e he => lt_of_lt_of_le he
        (Subtype.coe_le_coe.mpr (M.cutProb_mono (hpos n) (hpos m) hnm' e))) 0
    calc (∑ y ∈ E1Sign.ballF M (r n),
          (cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y)
        ≤ ∑ y ∈ E1Sign.ballF M (r n),
            (cluster (atParameter (M.cutProb (r m)) u) (0 : M.V)).indicator
              (fun _ => (1 : ℝ≥0∞)) y := by
          refine Finset.sum_le_sum fun y _ => ?_
          by_cases hy : y ∈ cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hcl hy)]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ ≤ ∑ y ∈ E1Sign.ballF M (r m),
            (cluster (atParameter (M.cutProb (r m)) u) (0 : M.V)).indicator
              (fun _ => (1 : ℝ≥0∞)) y :=
          Finset.sum_le_sum_of_subset_of_nonneg (M.ballF_mono hnm') (fun _ _ _ => zero_le)
  simp only [SourceModelData.connCubeFun, SourceModelData.connCubeFunLt]
  rw [← hvol3, ← hsum]
  exact PercLib.CriticalLRP.iSup_mul_iSup_nat hmonoA hmonoB

/-! ## 4. Monotone convergence of the three masses to their strict-window companions -/

theorem iSup_quadPairMass_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) :
    (⨆ n, M.quadPairMass (r n)) = M.quadPairMassLt r0 := by
  have hmeas : ∀ n, Measurable (M.quadPairFun (r n)) := fun n =>
    M.measurable_quadPairFun (r n)
  have hmonoFun : Monotone fun n => M.quadPairFun (r n) := fun n m hnm =>
    M.quadPairFun_mono (hpos n) (monotone_nat_of_le_succ hmono hnm)
  have hstep := lintegral_iSup (μ := markMeasure M.V) hmeas hmonoFun
  have hptfun : (fun u => ⨆ n, M.quadPairFun (r n) u) = M.quadPairFunLt r0 :=
    funext fun u => M.iSup_quadPairFun_nat hpos hlt hmono hlim u
  rw [hptfun] at hstep
  rw [SourceModelData.quadPairMassLt]
  simpa only [SourceModelData.quadPairMass] using hstep.symm

theorem iSup_sqLinPairMass_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) :
    (⨆ n, M.sqLinPairMass (r n)) = M.sqLinPairMassLt r0 := by
  have hmeas : ∀ n, Measurable (M.sqLinPairFun (r n)) := fun n =>
    M.measurable_sqLinPairFun (r n)
  have hmonoFun : Monotone fun n => M.sqLinPairFun (r n) := fun n m hnm =>
    M.sqLinPairFun_mono (hpos n) (monotone_nat_of_le_succ hmono hnm)
  have hstep := lintegral_iSup (μ := markMeasure M.V) hmeas hmonoFun
  have hptfun : (fun u => ⨆ n, M.sqLinPairFun (r n) u) = M.sqLinPairFunLt r0 :=
    funext fun u => M.iSup_sqLinPairFun_nat hpos hlt hmono hlim u
  rw [hptfun] at hstep
  rw [SourceModelData.sqLinPairMassLt]
  simpa only [SourceModelData.sqLinPairMass] using hstep.symm

theorem iSup_connCubeMass_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) :
    (⨆ n, M.connCubeMass (r n)) = M.connCubeMassLt r0 := by
  have hmeas : ∀ n, Measurable (M.connCubeFun (r n)) := fun n =>
    M.measurable_connCubeFun (r n)
  have hmonoFun : Monotone fun n => M.connCubeFun (r n) := fun n m hnm =>
    M.connCubeFun_mono (hpos n) (monotone_nat_of_le_succ hmono hnm)
  have hstep := lintegral_iSup (μ := markMeasure M.V) hmeas hmonoFun
  have hptfun : (fun u => ⨆ n, M.connCubeFun (r n) u) = M.connCubeFunLt r0 :=
    funext fun u => M.iSup_connCubeFun_nat hpos hlt hmono hlim u
  rw [hptfun] at hstep
  rw [SourceModelData.connCubeMassLt]
  simpa only [SourceModelData.connCubeMass] using hstep.symm

/-! ## 5. Comparison of a closed-window mass with the strict-window mass at a larger radius -/

theorem quadPairFunLt_le (r : ℝ) : M.quadPairFunLt r ≤ M.quadPairFun r := by
  intro u
  simp only [SourceModelData.quadPairFunLt, SourceModelData.quadPairFun]
  refine mul_le_mul' le_rfl ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun y hy => (M.mem_ballF_rho).mpr (le_of_lt (M.mem_ballFLt.mp hy)))
    (fun _ _ _ => zero_le)

theorem sqLinPairFunLt_le (r : ℝ) : M.sqLinPairFunLt r ≤ M.sqLinPairFun r := by
  intro u
  simp only [SourceModelData.sqLinPairFunLt, SourceModelData.sqLinPairFun]
  refine mul_le_mul' le_rfl ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun y hy => (M.mem_ballF_rho).mpr (le_of_lt (M.mem_ballFLt.mp hy)))
    (fun _ _ _ => zero_le)

theorem connCubeFunLt_le (r : ℝ) : M.connCubeFunLt r ≤ M.connCubeFun r := by
  intro u
  simp only [SourceModelData.connCubeFunLt, SourceModelData.connCubeFun]
  refine mul_le_mul' le_rfl ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun y hy => (M.mem_ballF_rho).mpr (le_of_lt (M.mem_ballFLt.mp hy)))
    (fun _ _ _ => zero_le)

theorem quadPairMassLt_le (r : ℝ) : M.quadPairMassLt r ≤ M.quadPairMass r := by
  rw [SourceModelData.quadPairMassLt, SourceModelData.quadPairMass]
  exact lintegral_mono fun u => M.quadPairFunLt_le r u

theorem sqLinPairMassLt_le (r : ℝ) : M.sqLinPairMassLt r ≤ M.sqLinPairMass r := by
  rw [SourceModelData.sqLinPairMassLt, SourceModelData.sqLinPairMass]
  exact lintegral_mono fun u => M.sqLinPairFunLt_le r u

theorem connCubeMassLt_le (r : ℝ) : M.connCubeMassLt r ≤ M.connCubeMass r := by
  rw [SourceModelData.connCubeMassLt, SourceModelData.connCubeMass]
  exact lintegral_mono fun u => M.connCubeFunLt_le r u

theorem quadPairFun_le_quadPairFunLt {r r0 : ℝ} (hr : 0 < r) (hrr : r < r0) :
    M.quadPairFun r ≤ M.quadPairFunLt r0 := by
  intro u
  have hr0 : 0 < r0 := lt_trans hr hrr
  simp only [SourceModelData.quadPairFun, SourceModelData.quadPairFunLt,
    SourceModelData.markVol]
  refine mul_le_mul' (M.clusterVol_atParameter_mono hr hr0 hrr.le u 0) ?_
  calc (∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r) u) y ^ 2)
      ≤ ∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r0) u) y ^ 2 :=
        Finset.sum_le_sum fun y _ =>
          pow_le_pow_left' (M.clusterVol_atParameter_mono hr hr0 hrr.le u y) 2
    _ ≤ ∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun y hy => M.mem_ballFLt.mpr (lt_of_le_of_lt ((M.mem_ballF_rho).mp hy) hrr))
          (fun _ _ _ => zero_le)

theorem sqLinPairFun_le_sqLinPairFunLt {r r0 : ℝ} (hr : 0 < r) (hrr : r < r0) :
    M.sqLinPairFun r ≤ M.sqLinPairFunLt r0 := by
  intro u
  have hr0 : 0 < r0 := lt_trans hr hrr
  simp only [SourceModelData.sqLinPairFun, SourceModelData.sqLinPairFunLt,
    SourceModelData.markVol]
  refine mul_le_mul' (pow_le_pow_left'
    (M.clusterVol_atParameter_mono hr hr0 hrr.le u 0) 2) ?_
  calc (∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r) u) y)
      ≤ ∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r0) u) y :=
        Finset.sum_le_sum fun y _ => M.clusterVol_atParameter_mono hr hr0 hrr.le u y
    _ ≤ ∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun y hy => M.mem_ballFLt.mpr (lt_of_le_of_lt ((M.mem_ballF_rho).mp hy) hrr))
          (fun _ _ _ => zero_le)

theorem connCubeFun_le_connCubeFunLt {r r0 : ℝ} (hr : 0 < r) (hrr : r < r0) :
    M.connCubeFun r ≤ M.connCubeFunLt r0 := by
  intro u
  have hr0 : 0 < r0 := lt_trans hr hrr
  have hcl : cluster (atParameter (M.cutProb r) u) (0 : M.V) ⊆
      cluster (atParameter (M.cutProb r0) u) (0 : M.V) :=
    cluster_mono (fun e he => lt_of_lt_of_le he
      (Subtype.coe_le_coe.mpr (M.cutProb_mono hr hr0 hrr.le e))) 0
  simp only [SourceModelData.connCubeFun, SourceModelData.connCubeFunLt,
    SourceModelData.markVol]
  refine mul_le_mul' (pow_le_pow_left'
    (M.clusterVol_atParameter_mono hr hr0 hrr.le u 0) 3) ?_
  calc (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
      ≤ ∑ y ∈ E1Sign.ballF M r,
          (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases hy : y ∈ cluster (atParameter (M.cutProb r) u) (0 : M.V)
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hcl hy)]
        · rw [Set.indicator_of_notMem hy]
          exact zero_le
    _ ≤ ∑ y ∈ M.ballFLt r0,
          (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun y hy => M.mem_ballFLt.mpr (lt_of_le_of_lt ((M.mem_ballF_rho).mp hy) hrr))
          (fun _ _ _ => zero_le)

theorem quadPairMass_le_quadPairMassLt {r r0 : ℝ} (hr : 0 < r) (hrr : r < r0) :
    M.quadPairMass r ≤ M.quadPairMassLt r0 := by
  rw [SourceModelData.quadPairMass, SourceModelData.quadPairMassLt]
  exact lintegral_mono fun u => M.quadPairFun_le_quadPairFunLt hr hrr u

theorem sqLinPairMass_le_sqLinPairMassLt {r r0 : ℝ} (hr : 0 < r) (hrr : r < r0) :
    M.sqLinPairMass r ≤ M.sqLinPairMassLt r0 := by
  rw [SourceModelData.sqLinPairMass, SourceModelData.sqLinPairMassLt]
  exact lintegral_mono fun u => M.sqLinPairFun_le_sqLinPairFunLt hr hrr u

theorem connCubeMass_le_connCubeMassLt {r r0 : ℝ} (hr : 0 < r) (hrr : r < r0) :
    M.connCubeMass r ≤ M.connCubeMassLt r0 := by
  rw [SourceModelData.connCubeMass, SourceModelData.connCubeMassLt]
  exact lintegral_mono fun u => M.connCubeFun_le_connCubeFunLt hr hrr u

/-! ## 6. Finiteness of the strict-window masses -/

theorem quadPairMassLt_ne_top {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.quadPairMassLt r ≠ ⊤ :=
  ne_top_of_le_ne_top (M.quadPairMass_ne_top h4) (M.quadPairMassLt_le r)

theorem sqLinPairMassLt_ne_top {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.sqLinPairMassLt r ≠ ⊤ :=
  ne_top_of_le_ne_top (M.sqLinPairMass_ne_top h4) (M.sqLinPairMassLt_le r)

theorem connCubeMassLt_ne_top {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.connCubeMassLt r ≠ ⊤ :=
  ne_top_of_le_ne_top (M.connCubeMass_ne_top h4) (M.connCubeMassLt_le r)

/-! ## 7. The left limit of a mass family whose monotone convergence is its strict-window companion

The `ε`-argument of the landed `tendsto_pairMassReal_nhdsLT`, stated for an arbitrary monotone
family `G` with strict companion `Glt`. -/

theorem tendsto_toReal_nhdsLT_of_iSup {G Glt : ℝ → ℝ≥0∞}
    (hiSup : ∀ (r : ℕ → ℝ) (r0 : ℝ), (∀ n, 0 < r n) → (∀ n, r n < r0) →
      (∀ n, r n ≤ r (n + 1)) → Tendsto r atTop (𝓝 r0) → (⨆ n, G (r n)) = Glt r0)
    (hmono : ∀ ⦃r r' : ℝ⦄, 0 < r → r ≤ r' → G r ≤ G r')
    (hle : ∀ ⦃r r0 : ℝ⦄, 0 < r → r < r0 → G r ≤ Glt r0)
    (r0 : ℝ) (hr0 : 0 < r0) (hfin : Glt r0 ≠ ⊤) :
    Tendsto (fun r => (G r).toReal) (𝓝[<] r0) (𝓝 ((Glt r0).toReal)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set r : ℕ → ℝ := fun n => r0 - r0 / ((n : ℝ) + 2) with hrdef
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hrpos : ∀ n : ℕ, 0 < r n := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h2 : r0 / ((n : ℝ) + 2) < r0 := by
      rw [div_lt_iff₀ h1]
      nlinarith
    simp only [hrdef]
    linarith
  have hrlt : ∀ n : ℕ, r n < r0 := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h2 : 0 < r0 / ((n : ℝ) + 2) := div_pos hr0 h1
    simp only [hrdef]
    linarith
  have hmono_seq : ∀ n : ℕ, r n ≤ r (n + 1) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h3 : r0 / (((n : ℝ) + 1) + 2) ≤ r0 / ((n : ℝ) + 2) := by
      apply div_le_div_of_nonneg_left hr0.le h1
      linarith
    have hcast : (((n + 1 : ℕ)) : ℝ) + 2 = ((n : ℝ) + 1) + 2 := by push_cast; ring
    simp only [hrdef]
    rw [hcast]
    linarith
  have hlim : Tendsto r atTop (𝓝 r0) := by
    have h0 : Tendsto (fun n : ℕ => r0 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa using tendsto_const_nhds.div_atTop h1
    simp only [hrdef]
    simpa using tendsto_const_nhds.sub h0
  have hsup := hiSup r r0 hrpos hrlt hmono_seq hlim
  have hseqT : Tendsto (fun n => G (r n)) atTop (𝓝 (Glt r0)) := by
    rw [← hsup]
    exact tendsto_atTop_iSup (monotone_nat_of_le_succ fun n =>
      hmono (hrpos n) (hmono_seq n))
  have hrealSeq : Tendsto (fun n => (G (r n)).toReal) atTop (𝓝 ((Glt r0).toReal)) :=
    (ENNReal.tendsto_toReal hfin).comp hseqT
  have hev : ∀ᶠ n : ℕ in atTop, (Glt r0).toReal - ε < (G (r n)).toReal :=
    (tendsto_order.1 hrealSeq).1 ((Glt r0).toReal - ε) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨r0 - r N, by linarith [hrlt N], ?_⟩
  intro x hxIio hxdist
  have hx1 : r N < x := by
    rw [Real.dist_eq, abs_lt] at hxdist
    linarith [hxdist.1]
  have hx2 : x < r0 := hxIio
  have hxpos : 0 < x := lt_trans (hrpos N) hx1
  have hfinx : G x ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (hle hxpos hx2)
  have hN' : (Glt r0).toReal - ε < (G (r N)).toReal := hN N le_rfl
  have h1 : (G (r N)).toReal ≤ (G x).toReal :=
    ENNReal.toReal_mono hfinx (hmono (hrpos N) hx1.le)
  have h2 : (G x).toReal ≤ (Glt r0).toReal := ENNReal.toReal_mono hfin (hle hxpos hx2)
  have h3 : (Glt r0).toReal - ε < (G x).toReal := lt_of_lt_of_le hN' h1
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-! ## 8. The left limits of the three strict-window masses -/

theorem quadPairMass_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    M.quadPairMass r ≤ M.quadPairMass r' :=
  lintegral_mono fun u => M.quadPairFun_mono hr hrr' u

theorem sqLinPairMass_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    M.sqLinPairMass r ≤ M.sqLinPairMass r' :=
  lintegral_mono fun u => M.sqLinPairFun_mono hr hrr' u

theorem connCubeMass_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    M.connCubeMass r ≤ M.connCubeMass r' :=
  lintegral_mono fun u => M.connCubeFun_mono hr hrr' u

theorem tendsto_quadPairMass_toReal_nhdsLT (r0 : ℝ) (hr0 : 0 < r0)
    (hfin : M.quadPairMassLt r0 ≠ ⊤) :
    Tendsto (fun r => (M.quadPairMass r).toReal) (𝓝[<] r0)
      (𝓝 ((M.quadPairMassLt r0).toReal)) :=
  SourceModelData.tendsto_toReal_nhdsLT_of_iSup
    (G := fun r => M.quadPairMass r) (Glt := fun r => M.quadPairMassLt r)
    (fun _ _ hpos hlt hmono hlim => M.iSup_quadPairMass_nat hpos hlt hmono hlim)
    (fun _ _ hr hrr' => M.quadPairMass_mono hr hrr')
    (fun _ _ hr hrr => M.quadPairMass_le_quadPairMassLt hr hrr) r0 hr0 hfin

theorem tendsto_sqLinPairMass_toReal_nhdsLT (r0 : ℝ) (hr0 : 0 < r0)
    (hfin : M.sqLinPairMassLt r0 ≠ ⊤) :
    Tendsto (fun r => (M.sqLinPairMass r).toReal) (𝓝[<] r0)
      (𝓝 ((M.sqLinPairMassLt r0).toReal)) :=
  SourceModelData.tendsto_toReal_nhdsLT_of_iSup
    (G := fun r => M.sqLinPairMass r) (Glt := fun r => M.sqLinPairMassLt r)
    (fun _ _ hpos hlt hmono hlim => M.iSup_sqLinPairMass_nat hpos hlt hmono hlim)
    (fun _ _ hr hrr' => M.sqLinPairMass_mono hr hrr')
    (fun _ _ hr hrr => M.sqLinPairMass_le_sqLinPairMassLt hr hrr) r0 hr0 hfin

theorem tendsto_connCubeMass_toReal_nhdsLT (r0 : ℝ) (hr0 : 0 < r0)
    (hfin : M.connCubeMassLt r0 ≠ ⊤) :
    Tendsto (fun r => (M.connCubeMass r).toReal) (𝓝[<] r0)
      (𝓝 ((M.connCubeMassLt r0).toReal)) :=
  SourceModelData.tendsto_toReal_nhdsLT_of_iSup
    (G := fun r => M.connCubeMass r) (Glt := fun r => M.connCubeMassLt r)
    (fun _ _ hpos hlt hmono hlim => M.iSup_connCubeMass_nat hpos hlt hmono hlim)
    (fun _ _ hr hrr' => M.connCubeMass_mono hr hrr')
    (fun _ _ hr hrr => M.connCubeMass_le_connCubeMassLt hr hrr) r0 hr0 hfin

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Orchestration

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology
open PercLib.CriticalLRP

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 9. The strict-window decomposition

Exactly as at the closed window, the excluded indicator splits each window summand into a
`y ∈ K_0` part (`|K_0|³`, the cubic connection mass) and a `y ∉ K_0` part (the excluded term), so
`quadPairMassLt = connCubeMassLt + exclMassQuadLt` and `sqLinPairMassLt = connCubeMassLt +
exclMassSqLinLt`.  Hence `p2RHSStrict = quadPairMassLt + 2 sqLinPairMassLt - 3 connCubeMassLt`
wherever the masses are finite. -/

theorem exclMassQuadLt_eq_mark (r : ℝ) :
    M.exclMassQuadLt r = ∫⁻ u, M.markVol r u *
      ∑ y ∈ M.ballFLt r,
        ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) y *
          clusterVol (atParameter (M.cutProb r) u) y ^ 2 ∂(markMeasure M.V) := by
  rw [exclMassQuadLt, E1Sign.cutLaw_eq M r, ← markMeasure_map_atParameter]
  refine lintegral_map ?_ (measurable_atParameter _)
  refine (measurable_clusterVol (0 : M.V)).mul (Finset.measurable_sum _ fun y _ => ?_)
  exact (measurable_const.indicator (measurableSet_cluster_mem (0 : M.V) y).compl).mul
    ((measurable_clusterVol y).pow_const 2)

theorem exclMassSqLinLt_eq_mark (r : ℝ) :
    M.exclMassSqLinLt r = ∫⁻ u, M.markVol r u ^ 2 *
      ∑ y ∈ M.ballFLt r,
        ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) y *
          clusterVol (atParameter (M.cutProb r) u) y ∂(markMeasure M.V) := by
  rw [exclMassSqLinLt, E1Sign.cutLaw_eq M r, ← markMeasure_map_atParameter]
  refine lintegral_map ?_ (measurable_atParameter _)
  refine ((measurable_clusterVol (0 : M.V)).pow_const 2).mul
    (Finset.measurable_sum _ fun y _ => ?_)
  exact (measurable_const.indicator (measurableSet_cluster_mem (0 : M.V) y).compl).mul
    (measurable_clusterVol y)

theorem quadPairFunLt_apply (r : ℝ) (u : Sym2 M.V → ℝ) :
    M.quadPairFunLt r u = M.connCubeFunLt r u + M.markVol r u *
      ∑ y ∈ M.ballFLt r,
        ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) y *
          clusterVol (atParameter (M.cutProb r) u) y ^ 2 := by
  simp only [quadPairFunLt, connCubeFunLt, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => quad_summand_split M _ y

theorem sqLinPairFunLt_apply (r : ℝ) (u : Sym2 M.V → ℝ) :
    M.sqLinPairFunLt r u = M.connCubeFunLt r u + M.markVol r u ^ 2 *
      ∑ y ∈ M.ballFLt r,
        ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) y *
          clusterVol (atParameter (M.cutProb r) u) y := by
  simp only [sqLinPairFunLt, connCubeFunLt, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => sqLin_summand_split M _ y

theorem quadPairMassLt_eq_connCubeMassLt_add (r : ℝ) :
    M.quadPairMassLt r = M.connCubeMassLt r + M.exclMassQuadLt r := by
  rw [quadPairMassLt, connCubeMassLt, M.exclMassQuadLt_eq_mark r,
    ← lintegral_add_left (M.measurable_connCubeFunLt r)]
  exact lintegral_congr fun u => M.quadPairFunLt_apply r u

theorem sqLinPairMassLt_eq_connCubeMassLt_add (r : ℝ) :
    M.sqLinPairMassLt r = M.connCubeMassLt r + M.exclMassSqLinLt r := by
  rw [sqLinPairMassLt, connCubeMassLt, M.exclMassSqLinLt_eq_mark r,
    ← lintegral_add_left (M.measurable_connCubeFunLt r)]
  exact lintegral_congr fun u => M.sqLinPairFunLt_apply r u

theorem p2RHSStrict_add_three_mul_connCubeLt (r : ℝ) :
    M.p2RHSStrict r + 3 * M.connCubeMassLt r =
      M.quadPairMassLt r + 2 * M.sqLinPairMassLt r := by
  have h0 := M.quadPairMassLt_eq_connCubeMassLt_add r
  have h1 := M.sqLinPairMassLt_eq_connCubeMassLt_add r
  rw [p2RHSStrict, h0, h1, two_mul, two_mul]
  ring

/-! ## 10. The strict-window `p = 2` RHS in real form -/

theorem p2RHSStrict_toReal_eq_pair_sub (r : ℝ) (h4 : M.cutMoment 4 r ≠ ⊤) :
    (M.p2RHSStrict r).toReal = (M.quadPairMassLt r).toReal
      + 2 * (M.sqLinPairMassLt r).toReal - 3 * (M.connCubeMassLt r).toReal := by
  have hA0 : M.quadPairMassLt r ≠ ⊤ := M.quadPairMassLt_ne_top h4
  have hA1 : M.sqLinPairMassLt r ≠ ⊤ := M.sqLinPairMassLt_ne_top h4
  have hC : M.connCubeMassLt r ≠ ⊤ := M.connCubeMassLt_ne_top h4
  have h3C : (3 : ℝ≥0∞) * M.connCubeMassLt r ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hC
  have h2A1 : (2 : ℝ≥0∞) * M.sqLinPairMassLt r ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hA1
  have hP : M.p2RHSStrict r ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hA0, h2A1⟩) ?_
    calc M.p2RHSStrict r ≤ M.p2RHSStrict r + 3 * M.connCubeMassLt r := le_self_add
      _ = M.quadPairMassLt r + 2 * M.sqLinPairMassLt r :=
          M.p2RHSStrict_add_three_mul_connCubeLt r
  have h1 : (M.p2RHSStrict r + 3 * M.connCubeMassLt r).toReal
      = (M.quadPairMassLt r + 2 * M.sqLinPairMassLt r).toReal := by
    rw [M.p2RHSStrict_add_three_mul_connCubeLt r]
  rw [ENNReal.toReal_add hP h3C, ENNReal.toReal_add hA0 h2A1,
    ENNReal.toReal_mul, ENNReal.toReal_mul] at h1
  have h3 : ((3 : ℝ≥0∞)).toReal = 3 := ENNReal.toReal_ofNat 3
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := ENNReal.toReal_ofNat 2
  rw [h3, h2] at h1
  linarith

/-! ## 11. The left limit of the `p = 2` excluded RHS

The closed-window RHS at radius `r` is the difference of the three closed-window masses; each of
them converges from the left to its strict-window companion at `r₀`.  The result is the exact left
limit, with no attainment hypothesis and no use of `ENNReal.toReal ⊤ = 0`: finiteness of the fourth
cut-off moment at `r₀` makes every `toReal` conversion legitimate. -/

theorem tendsto_p2RHS_toReal_nhdsLT (r0 : ℝ) (hr0 : 0 < r0) (h4 : M.cutMoment 4 r0 ≠ ⊤) :
    Tendsto (fun r => (M.p2RHS r).toReal) (𝓝[<] r0) (𝓝 ((M.p2RHSStrict r0).toReal)) := by
  have hA0 := M.tendsto_quadPairMass_toReal_nhdsLT r0 hr0 (M.quadPairMassLt_ne_top h4)
  have hA1 := M.tendsto_sqLinPairMass_toReal_nhdsLT r0 hr0 (M.sqLinPairMassLt_ne_top h4)
  have hC := M.tendsto_connCubeMass_toReal_nhdsLT r0 hr0 (M.connCubeMassLt_ne_top h4)
  have hcomb : Tendsto (fun r => (M.quadPairMass r).toReal + 2 * (M.sqLinPairMass r).toReal
      - 3 * (M.connCubeMass r).toReal) (𝓝[<] r0)
      (𝓝 ((M.quadPairMassLt r0).toReal + 2 * (M.sqLinPairMassLt r0).toReal
        - 3 * (M.connCubeMassLt r0).toReal)) :=
    (hA0.add (hA1.const_mul 2)).sub (hC.const_mul 3)
  have hev : (fun r => (M.p2RHS r).toReal) =ᶠ[𝓝[<] r0]
      fun r => (M.quadPairMass r).toReal + 2 * (M.sqLinPairMass r).toReal
        - 3 * (M.connCubeMass r).toReal := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact M.p2RHS_toReal_eq_pair_sub r (M.cutMoment_ne_top_of_le (le_of_lt hr) 4 h4)
  have hlim := (tendsto_congr' hev).mpr hcomb
  rwa [← M.p2RHSStrict_toReal_eq_pair_sub r0 h4] at hlim

/-! ## 12. Off the sphere the strict and closed windows agree

At a radius that carries no lattice point the closed and strict windows coincide, so the left limit
is a two-sided limit and the `p = 2` RHS is continuous there.  At an attained radius the two sides
differ by exactly the shell layer `p2RHSShell`, so nothing here asserts two-sided continuity there. -/

theorem exclMassQuadLt_eq_of_ballFLt_eq {r : ℝ} (h : M.ballFLt r = E1Sign.ballF M r) :
    M.exclMassQuadLt r = M.exclMassQuad r := by
  simp only [exclMassQuadLt, exclMassQuad, exclSumQuadLt, exclSumQuad, h]

theorem exclMassSqLinLt_eq_of_ballFLt_eq {r : ℝ} (h : M.ballFLt r = E1Sign.ballF M r) :
    M.exclMassSqLinLt r = M.exclMassSqLin r := by
  simp only [exclMassSqLinLt, exclMassSqLin, exclSumLinLt, exclSumLin, h]

theorem p2RHSStrict_eq_p2RHS_of_no_sphere {r : ℝ}
    (h : ∀ y : M.V, M.S.ρ (toVec y) ≠ r) : M.p2RHSStrict r = M.p2RHS r := by
  have hb := M.ballFLt_eq_ballF_of_no_sphere h
  simp only [p2RHSStrict, p2RHS, M.exclMassQuadLt_eq_of_ballFLt_eq hb,
    M.exclMassSqLinLt_eq_of_ballFLt_eq hb]

theorem tendsto_p2RHS_toReal_nhdsLT_of_no_sphere (r0 : ℝ) (hr0 : 0 < r0)
    (h4 : M.cutMoment 4 r0 ≠ ⊤) (h : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) :
    Tendsto (fun r => (M.p2RHS r).toReal) (𝓝[<] r0) (𝓝 ((M.p2RHS r0).toReal)) := by
  have hlim := M.tendsto_p2RHS_toReal_nhdsLT r0 hr0 h4
  rwa [M.p2RHSStrict_eq_p2RHS_of_no_sphere h] at hlim

/-- **Two-sided continuity of the `p = 2` excluded RHS off the sphere.**  Right continuity is the
landed `tendsto_p2RHS_toReal_nhdsGT`; the left limit is `tendsto_p2RHS_toReal_nhdsLT_of_no_sphere`,
where the strict and closed windows agree.  No statement is made at an attained radius. -/
theorem continuousAt_p2RHS_toReal_of_no_sphere (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ}
    (hr1 : r0 < r1) (h4 : M.cutMoment 4 r1 ≠ ⊤)
    (h : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) :
    ContinuousAt (fun r => (M.p2RHS r).toReal) r0 :=
  M.continuousAt_p2RHS_toReal_of_left r0 hr0 hr1 h4
    (M.tendsto_p2RHS_toReal_nhdsLT_of_no_sphere r0 hr0
      (M.cutMoment_ne_top_of_le hr1.le 4 h4) h)

/-- The derivative weight `rhsScalarTwo = coeffRHS · (p2RHS ·).toReal` is left continuous with the
strict-window value at `r₀`, i.e. `coeffRHS r₀ · (p2RHSStrict r₀).toReal`, whenever the coefficient
is left continuous.  This is the `p = 2` companion of the landed `p = 1` statement. -/
theorem tendsto_rhsScalarTwo_nhdsLT (r0 : ℝ) (hr0 : 0 < r0) (h4 : M.cutMoment 4 r0 ≠ ⊤)
    (hcoef : Tendsto M.coeffRHS (𝓝[<] r0) (𝓝 (M.coeffRHS r0))) :
    Tendsto M.rhsScalarTwo (𝓝[<] r0)
      (𝓝 (M.coeffRHS r0 * (M.p2RHSStrict r0).toReal)) :=
  hcoef.mul (M.tendsto_p2RHS_toReal_nhdsLT r0 hr0 h4)

/-- **Two-sided continuity of the derivative weight off the sphere.** -/
theorem continuousAt_rhsScalarTwo_of_no_sphere (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ}
    (hr1 : r0 < r1) (h4 : M.cutMoment 4 r1 ≠ ⊤)
    (h : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) (hcoef : ContinuousAt M.coeffRHS r0) :
    ContinuousAt M.rhsScalarTwo r0 :=
  hcoef.mul (M.continuousAt_p2RHS_toReal_of_no_sphere r0 hr0 hr1 h4 h)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Orchestration

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology
open PercLib.CriticalLRP

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 13. The jump at an attained radius is the shell layer

`p2RHS = p2RHSStrict + p2RHSShell` (`SecondMoment/Corner`).  Together with §11 and §12 this pins
the discontinuity down exactly: at a radius whose shell layer is finite and nonzero the left limit of
`(p2RHS ·).toReal` is *not* the closed-window value, so no two-sided continuity statement can hold
there.  This is the precise sense in which the left limit proved above cannot be upgraded. -/

theorem p2RHS_ne_top_of_fourth {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) : M.p2RHS r ≠ ⊤ := by
  have hle : M.p2RHS r ≤ M.quadPairMass r + 2 * M.sqLinPairMass r := by
    calc M.p2RHS r ≤ M.p2RHS r + 3 * M.connCubeMass r := le_self_add
      _ = M.quadPairMass r + 2 * M.sqLinPairMass r := M.p2RHS_add_three_mul_connCube r
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨M.quadPairMass_ne_top h4,
      ENNReal.mul_ne_top (by norm_num) (M.sqLinPairMass_ne_top h4)⟩) hle

theorem p2RHSStrict_ne_top {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) : M.p2RHSStrict r ≠ ⊤ := by
  have hA0 : M.quadPairMassLt r ≠ ⊤ := M.quadPairMassLt_ne_top h4
  have hA1 : M.sqLinPairMassLt r ≠ ⊤ := M.sqLinPairMassLt_ne_top h4
  have h2A1 : (2 : ℝ≥0∞) * M.sqLinPairMassLt r ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hA1
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hA0, h2A1⟩) ?_
  calc M.p2RHSStrict r ≤ M.p2RHSStrict r + 3 * M.connCubeMassLt r := le_self_add
    _ = M.quadPairMassLt r + 2 * M.sqLinPairMassLt r :=
        M.p2RHSStrict_add_three_mul_connCubeLt r

theorem p2RHSShell_ne_top_of_fourth {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) :
    M.p2RHSShell r ≠ ⊤ :=
  ne_top_of_le_ne_top (M.p2RHS_ne_top_of_fourth h4) (M.p2RhsMassShell_le_p2RhsMass r)

/-- The exact real closed/strict/shell decomposition of the `p = 2` RHS. -/
theorem p2RHS_toReal_eq_strict_add_shell {r : ℝ} (h4 : M.cutMoment 4 r ≠ ⊤) :
    (M.p2RHS r).toReal = (M.p2RHSStrict r).toReal + (M.p2RHSShell r).toReal := by
  rw [M.p2RhsMass_eq_strict_add_shell r,
    ENNReal.toReal_add (M.p2RHSStrict_ne_top h4) (M.p2RHSShell_ne_top_of_fourth h4)]

/-- **The left limit is not the closed-window value at an attained radius.**  If the shell layer at
`r₀` is finite and nonzero, then `(p2RHS ·).toReal` has no left limit equal to `(p2RHS r₀).toReal`:
its actual left limit is `(p2RHSStrict r₀).toReal`, which is strictly smaller.  No two-sided
continuity (and hence no two-sided differentiability) of the `p = 2` excluded RHS is asserted or
possible at such a radius. -/
theorem not_tendsto_p2RHS_toReal_nhdsLT_of_shell_ne_zero (r0 : ℝ) (hr0 : 0 < r0)
    (h4 : M.cutMoment 4 r0 ≠ ⊤) (hshell : M.p2RHSShell r0 ≠ 0) :
    ¬ Tendsto (fun r => (M.p2RHS r).toReal) (𝓝[<] r0) (𝓝 ((M.p2RHS r0).toReal)) := by
  intro hclosed
  have hleft := M.tendsto_p2RHS_toReal_nhdsLT r0 hr0 h4
  have heq : (M.p2RHSStrict r0).toReal = (M.p2RHS r0).toReal := tendsto_nhds_unique hleft hclosed
  rw [M.p2RHS_toReal_eq_strict_add_shell h4] at heq
  have hzero : (M.p2RHSShell r0).toReal = 0 := by linarith
  refine hshell ?_
  rcases (ENNReal.toReal_eq_zero_iff (M.p2RHSShell r0)).mp hzero with h | h
  · exact h
  · exact absurd h (M.p2RHSShell_ne_top_of_fourth h4)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_clusterWindowSum_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_quadPairFun_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_sqLinPairFun_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_connCubeFun_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_quadPairMass_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_sqLinPairMass_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_connCubeMass_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_toReal_nhdsLT_of_iSup
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_quadPairMass_toReal_nhdsLT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_sqLinPairMass_toReal_nhdsLT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_connCubeMass_toReal_nhdsLT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.quadPairMassLt_eq_connCubeMassLt_add
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sqLinPairMassLt_eq_connCubeMassLt_add
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHSStrict_add_three_mul_connCubeLt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHSStrict_toReal_eq_pair_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_p2RHS_toReal_nhdsLT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHSStrict_eq_p2RHS_of_no_sphere
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_p2RHS_toReal_nhdsLT_of_no_sphere
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_p2RHS_toReal_of_no_sphere
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_rhsScalarTwo_nhdsLT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_rhsScalarTwo_of_no_sphere
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_ne_top_of_fourth
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHSStrict_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_toReal_eq_strict_add_shell
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.not_tendsto_p2RHS_toReal_nhdsLT_of_shell_ne_zero
