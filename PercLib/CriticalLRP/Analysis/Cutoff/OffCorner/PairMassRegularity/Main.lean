module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairMassRegularity.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.ScalarFactor.Main

/-!
# Radius continuity of pair and excluded masses

The pair integrand is monotone in the cutoff radius. Monotone convergence gives its left limit,
including strict-window identification off the sphere. The right limit uses general-base
box-change and escape comparisons, with a finite union of escape events for the required roots.
Subtracting connected-mass continuity via `E1Sign.pairMass_eq` gives excluded-mass continuity.

No pair-mass or excluded-mass continuity is asserted without its positivity, no-sphere, and
finite-moment hypotheses. `continuousAt_pairMassReal` uses a finite second cutoff moment at a
strictly larger radius from either side. `continuousAt_exclScalar` also needs a finite third
cutoff moment at a strictly larger radius for the connected-mass comparison. These moments are
inputs, not derived from `θ = 0` or from `ENNReal.toReal` conventions. The left-continuity
statements have their own explicit finite second/third-moment hypotheses; no unconditional
left-continuity claim is made. The general-base events are in `PairMassRegularity.Defs`.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The pair integrand and its monotonicity -/

/-- Membership in the closed window, in the radius of the source norm. -/
theorem mem_ballF_rho {r : ℝ} {y : M.V} :
    y ∈ E1Sign.ballF M r ↔ M.S.ρ (toVec y) ≤ r := by
  rw [E1Sign.mem_ballF]
  rfl

theorem pairMass_eq_lintegral_pairMarkFun (r : ℝ) :
    E1Sign.pairMass M r = ∫⁻ u, M.pairMarkFun r u ∂(markMeasure M.V) := by
  rw [E1Sign.pairMass_eq_mark]
  rfl

theorem measurable_pairMarkFun (r : ℝ) : Measurable (M.pairMarkFun r) := by
  have hsum : Measurable fun u : Sym2 M.V → ℝ =>
      ∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r) u) y :=
    Finset.measurable_sum _ fun y _ =>
      (measurable_clusterVol y).comp (measurable_atParameter _)
  exact (M.measurable_markVol r).mul hsum

theorem measurable_pairMarkFunLt (r : ℝ) : Measurable (M.pairMarkFunLt r) := by
  have hsum : Measurable fun u : Sym2 M.V → ℝ =>
      ∑ y ∈ M.ballFLt r, clusterVol (atParameter (M.cutProb r) u) y :=
    Finset.measurable_sum _ fun y _ =>
      (measurable_clusterVol y).comp (measurable_atParameter _)
  exact (M.measurable_markVol r).mul hsum

theorem pairMarkFun_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    M.pairMarkFun r ≤ M.pairMarkFun r' := by
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  intro u
  refine mul_le_mul' (M.clusterVol_atParameter_mono hr hr' hrr' u 0) ?_
  calc (∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r) u) y)
      ≤ ∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r') u) y :=
        Finset.sum_le_sum fun y _ => M.clusterVol_atParameter_mono hr hr' hrr' u y
    _ ≤ ∑ y ∈ E1Sign.ballF M r', clusterVol (atParameter (M.cutProb r') u) y :=
        Finset.sum_le_sum_of_subset_of_nonneg (M.ballF_mono hrr') (fun _ _ _ => zero_le)

/-! ## 2. Suprema of monotone `ℝ≥0∞` families over finite sets -/

theorem iSup_add_iSup_nat {a b : ℕ → ℝ≥0∞} (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, a n + b n) = (⨆ n, a n) + (⨆ n, b n) := by
  refine le_antisymm (iSup_le fun n => add_le_add (le_iSup a n) (le_iSup b n)) ?_
  rw [ENNReal.iSup_add]
  refine iSup_le fun n => ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun m => ?_
  calc a n + b m ≤ a (max n m) + b (max n m) :=
        add_le_add (ha (le_max_left n m)) (hb (le_max_right n m))
    _ ≤ ⨆ k, a k + b k := le_iSup (fun k => a k + b k) (max n m)

theorem iSup_finset_sum_nat {s : Finset M.V} {g : ℕ → M.V → ℝ≥0∞}
    (hg : ∀ y : M.V, Monotone fun n => g n y) :
    (∑ y ∈ s, ⨆ n, g n y) = ⨆ n, ∑ y ∈ s, g n y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      simp only [Finset.sum_insert hx, ih]
      exact (iSup_add_iSup_nat (hg x)
        (monotone_nat_of_le_succ fun n => Finset.sum_le_sum fun y _ => hg y (Nat.le_succ n))).symm

/-! ## 3. Pointwise exhaustion of the strict window -/

theorem iSup_pairWindowSum {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n) (hlt : ∀ n, r n < r0)
    (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0)) (u : Sym2 M.V → ℝ) :
    (⨆ n, ∑ y ∈ E1Sign.ballF M (r n), clusterVol (atParameter (M.cutProb (r n)) u) y)
      = ∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y := by
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
  have hmono_g : ∀ y : M.V, Monotone fun n => clusterVol (atParameter (M.cutProb (r n)) u) y :=
    fun y n m hnm => M.clusterVol_atParameter_mono (hpos n) (hpos m) (hmono_le n m hnm) u y
  have hex : ∀ y ∈ M.ballFLt r0, ∃ N : ℕ, ∀ n ≥ N, y ∈ E1Sign.ballF M (r n) := by
    intro y hy
    have hρ : M.S.ρ (toVec y) < r0 := M.mem_ballFLt.mp hy
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (Ioi_mem_nhds hρ))
    exact ⟨N, fun n hn => (M.mem_ballF_rho).mpr (le_of_lt (hN n hn))⟩
  refine le_antisymm (iSup_le fun n => ?_) ?_
  · calc (∑ y ∈ E1Sign.ballF M (r n), clusterVol (atParameter (M.cutProb (r n)) u) y)
        ≤ ∑ y ∈ E1Sign.ballF M (r n), clusterVol (atParameter (M.cutProb r0) u) y :=
          Finset.sum_le_sum fun y _ =>
            M.clusterVol_atParameter_mono (hpos n) hr0 (le_of_lt (hlt n)) u y
      _ ≤ ∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y :=
          Finset.sum_le_sum_of_subset_of_nonneg (hsub n) (fun _ _ _ => zero_le)
  · have h1 : (∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y)
        = ∑ y ∈ M.ballFLt r0, ⨆ n, clusterVol (atParameter (M.cutProb (r n)) u) y :=
      Finset.sum_congr rfl fun y _ => hsup y
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
    have hstep : (∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb (r n)) u) y)
        ≤ ∑ y ∈ E1Sign.ballF M (r (max n M₀)),
            clusterVol (atParameter (M.cutProb (r (max n M₀))) u) y := by
      refine le_trans (Finset.sum_le_sum fun y _ => hmono_g y (le_max_left n M₀)) ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => zero_le)
      intro y hy
      exact (M.mem_ballF_rho).mpr
        (le_trans ((M.mem_ballF_rho).mp (hM₀spec y hy))
          (hmono_le M₀ (max n M₀) (le_max_right n M₀)))
    exact le_trans hstep (le_iSup (fun k => ∑ y ∈ E1Sign.ballF M (r k),
      clusterVol (atParameter (M.cutProb (r k)) u) y) (max n M₀))

/-! ## 4. Pointwise supremum of the pair integrand -/

theorem iSup_pairMarkFun_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) (u : Sym2 M.V → ℝ) :
    (⨆ n, M.pairMarkFun (r n) u) = M.pairMarkFunLt r0 u := by
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
  have hsum := M.iSup_pairWindowSum hpos hlt hmono hlim u
  have hmonoA : Monotone fun n => M.markVol (r n) u := fun n m hnm =>
    M.clusterVol_atParameter_mono (hpos n) (hpos m) (monotone_nat_of_le_succ hmono hnm) u 0
  have hmonoB : Monotone fun n => ∑ y ∈ E1Sign.ballF M (r n),
      clusterVol (atParameter (M.cutProb (r n)) u) y := by
    intro n m hnm
    have hnm' : r n ≤ r m := monotone_nat_of_le_succ hmono hnm
    calc (∑ y ∈ E1Sign.ballF M (r n), clusterVol (atParameter (M.cutProb (r n)) u) y)
        ≤ ∑ y ∈ E1Sign.ballF M (r n), clusterVol (atParameter (M.cutProb (r m)) u) y :=
          Finset.sum_le_sum fun y _ => M.clusterVol_atParameter_mono (hpos n) (hpos m) hnm' u y
      _ ≤ ∑ y ∈ E1Sign.ballF M (r m), clusterVol (atParameter (M.cutProb (r m)) u) y :=
          Finset.sum_le_sum_of_subset_of_nonneg (M.ballF_mono hnm') (fun _ _ _ => zero_le)
  simp only [SourceModelData.pairMarkFun, SourceModelData.pairMarkFunLt]
  rw [← hvol, ← hsum]
  exact PercLib.CriticalLRP.iSup_mul_iSup_nat hmonoA hmonoB

/-! ## 5. Monotone convergence of the pair mass to the strict-window mass -/

theorem iSup_pairMass_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) :
    (⨆ n, E1Sign.pairMass M (r n)) = M.pairMassLt r0 := by
  have hmeas : ∀ n, Measurable (M.pairMarkFun (r n)) := fun n => M.measurable_pairMarkFun (r n)
  have hmonoFun : Monotone fun n => M.pairMarkFun (r n) := fun n m hnm =>
    M.pairMarkFun_mono (hpos n) (monotone_nat_of_le_succ hmono hnm)
  have hstep := lintegral_iSup (μ := markMeasure M.V) hmeas hmonoFun
  have hptfun : (fun u => ⨆ n, M.pairMarkFun (r n) u) = M.pairMarkFunLt r0 :=
    funext fun u => M.iSup_pairMarkFun_nat hpos hlt hmono hlim u
  rw [hptfun] at hstep
  rw [SourceModelData.pairMassLt]
  simpa only [M.pairMass_eq_lintegral_pairMarkFun] using hstep.symm

/-- The pair mass at a radius strictly below `r₀` is at most the strict-window mass at `r₀`. -/
theorem pairMass_le_pairMassLt {r r0 : ℝ} (hr : 0 < r) (hrr : r < r0) :
    E1Sign.pairMass M r ≤ M.pairMassLt r0 := by
  have hr0 : 0 < r0 := lt_trans hr hrr
  rw [M.pairMass_eq_lintegral_pairMarkFun, SourceModelData.pairMassLt]
  refine lintegral_mono fun u => ?_
  simp only [SourceModelData.pairMarkFun, SourceModelData.pairMarkFunLt]
  have hsub : E1Sign.ballF M r ⊆ M.ballFLt r0 := fun y hy =>
    M.mem_ballFLt.mpr (lt_of_le_of_lt ((M.mem_ballF_rho).mp hy) hrr)
  refine mul_le_mul' (M.clusterVol_atParameter_mono hr hr0 hrr.le u 0) ?_
  calc (∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r) u) y)
      ≤ ∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r0) u) y :=
        Finset.sum_le_sum fun y _ => M.clusterVol_atParameter_mono hr hr0 hrr.le u y
    _ ≤ ∑ y ∈ M.ballFLt r0, clusterVol (atParameter (M.cutProb r0) u) y :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)

/-! ## 6. Left continuity of the pair mass -/

/-- **Monotone convergence gives the left limit of the pair mass**, from finiteness of the
strict-window mass at `r₀` only.  This is the exact pair-mass analogue of
`tendsto_connMassReal_nhdsLT`. -/
theorem tendsto_pairMassReal_nhdsLT (r0 : ℝ) (hr0 : 0 < r0) (hfin : M.pairMassLt r0 ≠ ⊤) :
    Tendsto (fun r => (E1Sign.pairMass M r).toReal) (𝓝[<] r0)
      (𝓝 ((M.pairMassLt r0).toReal)) := by
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
  have hmono : ∀ n : ℕ, r n ≤ r (n + 1) := by
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
  have hseq := M.iSup_pairMass_nat hrpos hrlt hmono hlim
  have hseqT : Tendsto (fun n => E1Sign.pairMass M (r n)) atTop (𝓝 (M.pairMassLt r0)) := by
    rw [← hseq]
    exact tendsto_atTop_iSup (monotone_nat_of_le_succ fun n =>
      E1Sign.pairMass_mono M (hrpos n) (hmono n))
  have hrealSeq : Tendsto (fun n => (E1Sign.pairMass M (r n)).toReal) atTop
      (𝓝 ((M.pairMassLt r0).toReal)) :=
    (ENNReal.tendsto_toReal hfin).comp hseqT
  have hev : ∀ᶠ n : ℕ in atTop, (M.pairMassLt r0).toReal - ε <
      (E1Sign.pairMass M (r n)).toReal :=
    (tendsto_order.1 hrealSeq).1 ((M.pairMassLt r0).toReal - ε) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨r0 - r N, by linarith [hrlt N], ?_⟩
  intro x hxIio hxdist
  have hx1 : r N < x := by
    rw [Real.dist_eq, abs_lt] at hxdist
    linarith [hxdist.1]
  have hx2 : x < r0 := hxIio
  have hxpos : 0 < x := lt_trans (hrpos N) hx1
  have hfinx : E1Sign.pairMass M x ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (M.pairMass_le_pairMassLt hxpos hx2)
  have hN' : (M.pairMassLt r0).toReal - ε < (E1Sign.pairMass M (r N)).toReal := hN N le_rfl
  have h1 : (E1Sign.pairMass M (r N)).toReal ≤ (E1Sign.pairMass M x).toReal :=
    ENNReal.toReal_mono hfinx (E1Sign.pairMass_mono M (hrpos N) hx1.le)
  have h2 : (E1Sign.pairMass M x).toReal ≤ (M.pairMassLt r0).toReal :=
    ENNReal.toReal_mono hfin (M.pairMass_le_pairMassLt hxpos hx2)
  have h3 : (M.pairMassLt r0).toReal - ε < (E1Sign.pairMass M x).toReal :=
    lt_of_lt_of_le hN' h1
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-! ## 7. Off the sphere, the strict window is the closed window -/

/-- At a radius carrying no lattice point, the strict window `{ρ < r}` and the closed window
`{ρ ≤ r}` coincide. -/
theorem ballFLt_eq_ballF_of_no_sphere {r : ℝ} (h : ∀ y : M.V, M.S.ρ (toVec y) ≠ r) :
    M.ballFLt r = E1Sign.ballF M r := by
  refine Finset.Subset.antisymm (fun y hy => (M.mem_ballF_rho).mpr
    (le_of_lt (M.mem_ballFLt.mp hy))) ?_
  intro y hy
  exact M.mem_ballFLt.mpr (lt_of_le_of_ne ((M.mem_ballF_rho).mp hy) (h y))

/-- Off the sphere the strict-window pair mass is the closed-window pair mass. -/
theorem pairMassLt_eq_pairMass_of_no_sphere {r : ℝ}
    (h : ∀ y : M.V, M.S.ρ (toVec y) ≠ r) :
    M.pairMassLt r = E1Sign.pairMass M r := by
  rw [SourceModelData.pairMassLt, M.pairMass_eq_lintegral_pairMarkFun]
  refine lintegral_congr fun u => ?_
  simp only [SourceModelData.pairMarkFunLt, SourceModelData.pairMarkFun,
    M.ballFLt_eq_ballF_of_no_sphere h]

/-- **Left continuity of the pair mass off the sphere.** -/
theorem tendsto_pairMassReal_nhdsLT_of_no_sphere {r0 : ℝ} (hr0 : 0 < r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) (hfin : E1Sign.pairMass M r0 ≠ ⊤) :
    Tendsto (fun r => (E1Sign.pairMass M r).toReal) (𝓝[<] r0)
      (𝓝 ((E1Sign.pairMass M r0).toReal)) := by
  have hfin' : M.pairMassLt r0 ≠ ⊤ := by
    rw [M.pairMassLt_eq_pairMass_of_no_sphere hsphere]
    exact hfin
  have h := M.tendsto_pairMassReal_nhdsLT r0 hr0 hfin'
  rwa [M.pairMassLt_eq_pairMass_of_no_sphere hsphere] at h

/-! ## 8. The excluded mass as the pair mass minus the connected mass -/

/-- **The real form of `E1Sign.pairMass_eq`.**  Where both summands are finite,
`exclMass.toReal` is the difference `pairMass.toReal - connMass.toReal`. -/
theorem exclScalar_eq_pairMassReal_sub_connMassReal {r : ℝ}
    (hc : E1Sign.connMass M r ≠ ⊤) (he : E1Sign.exclMass M r ≠ ⊤) :
    M.exclScalar r = (E1Sign.pairMass M r).toReal - (E1Sign.connMass M r).toReal := by
  have hsum : (E1Sign.pairMass M r).toReal
      = (E1Sign.connMass M r).toReal + M.exclScalar r := by
    rw [E1Sign.pairMass_eq M r, ENNReal.toReal_add hc he]
    rfl
  rw [hsum]
  ring

/-- The finiteness of `exclMass` and `connMass` used by the decomposition, on a window. -/
theorem exclScalar_eq_pairMassReal_sub_connMassReal_of_le {r b : ℝ} (hrb : r ≤ b)
    (h2b : M.cutMoment 2 b ≠ ⊤) :
    M.exclScalar r = (E1Sign.pairMass M r).toReal - (E1Sign.connMass M r).toReal :=
  M.exclScalar_eq_pairMassReal_sub_connMassReal
    (E1Sign.connMass_ne_top M r (M.cutMoment_ne_top_of_le hrb 2 h2b))
    (M.exclMass_ne_top_of_le hrb h2b)

/-! ## 9. Left continuity of the excluded mass -/

/-- **The excluded mass is left continuous at every radius carrying no lattice point**, from
finiteness of the third cutoff moment at that radius.  The proof goes through the pair mass:
both `(pairMass ·).toReal` and `(connMass ·).toReal` have left limits equal to their values at
`r₀` (§6 and the landed `tendsto_connMassReal_nhdsLT_of_sphereMass_eq_zero`), and on a window
`exclScalar = pairMassReal - connMassReal` (§8). -/
theorem tendsto_exclScalar_nhdsLT {r0 : ℝ} (hr0 : 0 < r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) (h2 : M.cutMoment 2 r0 ≠ ⊤)
    (h3 : M.cutMoment 3 r0 ≠ ⊤) :
    Tendsto M.exclScalar (𝓝[<] r0) (𝓝 (M.exclScalar r0)) := by
  have hpair0 : E1Sign.pairMass M r0 ≠ ⊤ := E1Sign.pairMass_ne_top M r0 h2
  have hconnLt : M.connMassLt r0 ≠ ⊤ :=
    ne_top_of_le_ne_top h3 (M.connMassLt_le_cutMoment_three r0)
  have hpairT := M.tendsto_pairMassReal_nhdsLT_of_no_sphere hr0 hsphere hpair0
  have hconnT := M.tendsto_connMassReal_nhdsLT_of_sphereMass_eq_zero r0 hr0 hconnLt
    (M.sphereMass_eq_zero_of_no_sphere hsphere)
  have hlim : (E1Sign.pairMass M r0).toReal - (E1Sign.connMass M r0).toReal
      = M.exclScalar r0 :=
    (M.exclScalar_eq_pairMassReal_sub_connMassReal_of_le (le_refl r0) h2).symm
  have hsub := hpairT.sub hconnT
  rw [hlim] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (M.exclScalar_eq_pairMassReal_sub_connMassReal_of_le (le_of_lt hr) h2).symm

/-! ## 10. The two-sided reduction -/

/-- **Excluded-mass continuity reduces to pair-mass continuity.**  At an off-corner radius
`r₀ > 0`, given finiteness of the third cutoff moment at one strictly larger radius and no
lattice point on the sphere `{ρ = r₀}`, the continuity of `(exclMass ·).toReal` is equivalent to
the continuity of `(pairMass ·).toReal`; this theorem is the direction that consumes the pair-mass
statement.  The connected-mass continuity is supplied by the landed
`continuousAt_connMassReal`. -/
theorem continuousAt_exclScalar_of_pairMassReal {r0 : ℝ} (hr0 : 0 < r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤)
    (hpair : ContinuousAt (fun r => (E1Sign.pairMass M r).toReal) r0) :
    ContinuousAt M.exclScalar r0 := by
  have hconn : ContinuousAt (fun r => (E1Sign.connMass M r).toReal) r0 :=
    M.continuousAt_connMassReal r0 hr0 hr1 h3 hsphere
  have hsub := hpair.sub hconn
  refine hsub.congr ?_
  filter_upwards [Ioi_mem_nhds hr0, Iic_mem_nhds hr1] with r hrpos hrr1
  exact (M.exclScalar_eq_pairMassReal_sub_connMassReal_of_le hrr1 h2).symm

/-- **Sharpness of the reduction.**  Given the landed connected-mass regularity and finiteness of
the second and third cutoff moments at one strictly larger radius, continuity of the pair mass at
an off-corner radius is *equivalent* to continuity of the excluded mass there.  Hence the pair
mass is neither a stronger nor a weaker target: it is the same analytic content, carried by a
monotone integrand. -/
theorem continuousAt_pairMassReal_iff_continuousAt_exclScalar {r0 : ℝ} (hr0 : 0 < r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤) :
    ContinuousAt (fun r => (E1Sign.pairMass M r).toReal) r0 ↔ ContinuousAt M.exclScalar r0 := by
  refine ⟨M.continuousAt_exclScalar_of_pairMassReal hr0 hsphere hr1 h2 h3, fun hex => ?_⟩
  have hconn : ContinuousAt (fun r => (E1Sign.connMass M r).toReal) r0 :=
    M.continuousAt_connMassReal r0 hr0 hr1 h3 hsphere
  have hdiff : ContinuousAt
      (fun r => (E1Sign.pairMass M r).toReal - (E1Sign.connMass M r).toReal) r0 := by
    refine hex.congr ?_
    filter_upwards [Ioi_mem_nhds hr0, Iic_mem_nhds hr1] with r hrpos hrr1
    exact M.exclScalar_eq_pairMassReal_sub_connMassReal_of_le hrr1 h2
  refine (hdiff.add hconn).congr ?_
  filter_upwards [Ioi_mem_nhds hr0, Iic_mem_nhds hr1] with r hrpos hrr1
  simp only [Pi.add_apply]
  ring

/-- **Left continuity of the pair mass from the second cutoff moment.**  The moment-based form of
`tendsto_pairMassReal_nhdsLT_of_no_sphere`, ready to be consumed with
`E1Sign.pairMass_ne_top`. -/
theorem tendsto_pairMassReal_nhdsLT_of_moment {r0 : ℝ} (hr0 : 0 < r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) (h2 : M.cutMoment 2 r0 ≠ ⊤) :
    Tendsto (fun r => (E1Sign.pairMass M r).toReal) (𝓝[<] r0)
      (𝓝 ((E1Sign.pairMass M r0).toReal)) :=
  M.tendsto_pairMassReal_nhdsLT_of_no_sphere hr0 hsphere
    (E1Sign.pairMass_ne_top M r0 h2)

theorem mem_markEscapeUnion {r R : ℝ} {s : Finset M.V} {u : Sym2 M.V → ℝ} :
    u ∈ M.markEscapeUnion r R s ↔ ∃ v ∈ s, u ∈ M.markEscapeAt r R v := by
  simp only [SourceModelData.markEscapeUnion, Set.mem_iUnion, exists_prop, Finset.mem_coe]

theorem markVol_eq_cutMassAt (r : ℝ) (v : M.V) :
    ∫⁻ u : Sym2 M.V → ℝ, clusterVol (atParameter (M.cutProb r) u) v ∂(markMeasure M.V)
      = M.cutMassAt r v := by
  have hlaw : M.cutMassAt r v =
      ∫⁻ ω, clusterVol ω v ∂(edgeMeasure (M.cutProb r)) := rfl
  rw [hlaw, ← markMeasure_map_atParameter]
  rw [lintegral_map (measurable_clusterVol v) (measurable_atParameter _)]

theorem measurableSet_markEscapeAt (r R : ℝ) (v : M.V) :
    MeasurableSet (M.markEscapeAt r R v) := by
  have h : M.markEscapeAt r R v = ⋃ x : M.V,
      {u : Sym2 M.V → ℝ | x ∉ M.ball R ∧
        Connects (atParameter (M.cutProb r) u) v x} := by
    ext u
    simp only [SourceModelData.markEscapeAt, Set.mem_iUnion]
    exact exists_congr fun x => by simp
  rw [h]
  refine MeasurableSet.iUnion fun x => ?_
  by_cases hx : x ∈ M.ball R
  · have h0 : {u : Sym2 M.V → ℝ | x ∉ M.ball R ∧
        Connects (atParameter (M.cutProb r) u) v x} = ∅ := by
      ext u
      simp [hx]
    rw [h0]
    exact MeasurableSet.empty
  · have h1 : {u : Sym2 M.V → ℝ | x ∉ M.ball R ∧
        Connects (atParameter (M.cutProb r) u) v x} =
        (atParameter (M.cutProb r)) ⁻¹' {ω : Config M.V | Connects ω v x} := by
      ext u
      simp [hx]
    rw [h1]
    exact (measurableSet_connects v x).preimage (measurable_atParameter _)

theorem measurableSet_markEscapeUnion (r R : ℝ) (s : Finset M.V) :
    MeasurableSet (M.markEscapeUnion r R s) :=
  MeasurableSet.biUnion s.countable_toSet fun v _ => M.measurableSet_markEscapeAt r R v

theorem markEscapeAt_antitone {r R R' : ℝ} (h : R ≤ R') (v : M.V) :
    M.markEscapeAt r R' v ⊆ M.markEscapeAt r R v := by
  rintro u ⟨x, hx, hconn⟩
  exact ⟨x, fun hmem => hx (PercLib.CriticalLRP.BallAverage.ball_mono M h hmem), hconn⟩

theorem markEscapeAt_mono {r r' R : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r') (v : M.V) :
    M.markEscapeAt r R v ⊆ M.markEscapeAt r' R v := by
  rintro u ⟨x, hx, hconn⟩
  exact ⟨x, hx, connects_mono (fun e he => lt_of_lt_of_le he
    (Subtype.coe_le_coe.mpr (M.cutProb_mono hr hr' h e))) hconn⟩

theorem markEscapeUnion_antitone {r R R' : ℝ} (h : R ≤ R') (s : Finset M.V) :
    M.markEscapeUnion r R' s ⊆ M.markEscapeUnion r R s := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := M.mem_markEscapeUnion.mp hu
  exact M.mem_markEscapeUnion.mpr ⟨v, hv, M.markEscapeAt_antitone h v hvu⟩

theorem markEscapeUnion_mono {r r' R : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r')
    (s : Finset M.V) : M.markEscapeUnion r R s ⊆ M.markEscapeUnion r' R s := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := M.mem_markEscapeUnion.mp hu
  exact M.mem_markEscapeUnion.mpr ⟨v, hv, M.markEscapeAt_mono hr hr' h v hvu⟩

/-- A cluster of `v` which leaves every lattice ball is infinite. -/
theorem clusterVol_eq_top_of_forall_mem_markEscapeAt {r : ℝ} {u : Sym2 M.V → ℝ} {v : M.V}
    (h : ∀ n : ℕ, u ∈ M.markEscapeAt r (n : ℝ) v) :
    clusterVol (atParameter (M.cutProb r) u) v = ⊤ := by
  have hinf : (cluster (atParameter (M.cutProb r) u) v).Infinite := by
    intro hfin
    obtain ⟨N, hN⟩ := M.exists_ball_subset_of_finite hfin
    obtain ⟨x, hx, hconn⟩ := h N
    exact hx (hN (mem_cluster_iff.mpr hconn))
  have := (inInfiniteCluster_iff (atParameter (M.cutProb r) u) v).mpr hinf
  simpa only [InInfiniteCluster] using this

/-- **Nullity of the shrinking union escape event.**  For a finite set `s` of base points and
finite cut-off mass at the origin, almost every mark has every `s`-cluster staying inside a
sufficiently large ball. -/
theorem measure_iInter_markEscapeUnion_eq_zero {r : ℝ} {s : Finset M.V}
    (hfin : M.cutMassAt r 0 ≠ ⊤) :
    markMeasure M.V (⋂ n : ℕ, M.markEscapeUnion r (n : ℝ) s) = 0 := by
  have hv : ∀ v ∈ s, M.cutMassAt r v ≠ ⊤ := fun v _ => by
    rw [M.cutMassAt_eq_zero r v]
    exact hfin
  have hfinall : ∀ᵐ u ∂(markMeasure M.V),
      ∀ v ∈ s, clusterVol (atParameter (M.cutProb r) u) v ≠ ⊤ := by
    rw [Finset.eventually_all s]
    intro v hvs
    have hmeas : Measurable fun u : Sym2 M.V → ℝ =>
        clusterVol (atParameter (M.cutProb r) u) v :=
      (measurable_clusterVol v).comp (measurable_atParameter _)
    have hint : (∫⁻ u : Sym2 M.V → ℝ, clusterVol (atParameter (M.cutProb r) u) v
        ∂(markMeasure M.V)) ≠ ⊤ := by
      rw [M.markVol_eq_cutMassAt r v]
      exact hv v hvs
    filter_upwards [ae_lt_top hmeas hint] with u hu
    exact hu.ne
  refine measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [hfinall] with u hu hmem
  have hex : ∀ w ∈ s, ∃ N : ℕ, u ∉ M.markEscapeAt r (N : ℝ) w := by
    intro w hws
    by_contra hcon
    push Not at hcon
    exact hu w hws (M.clusterVol_eq_top_of_forall_mem_markEscapeAt hcon)
  set M₀ : ℕ := s.attach.sup (fun w => Classical.choose (hex w.1 w.2)) with hM₀
  have hM₀spec : ∀ w ∈ s, u ∉ M.markEscapeAt r (M₀ : ℝ) w := by
    intro w hws
    have h1 : Classical.choose (hex w hws) ≤ M₀ :=
      Finset.le_sup (f := fun w : {w // w ∈ s} => Classical.choose (hex w.1 w.2))
        (Finset.mem_attach _ ⟨w, hws⟩)
    have h2 : ((Classical.choose (hex w hws) : ℕ) : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast h1
    exact fun hcontra =>
      (Classical.choose_spec (hex w hws)) (M.markEscapeAt_antitone h2 w hcontra)
  obtain ⟨w, hws, hwu⟩ := M.mem_markEscapeUnion.mp (Set.mem_iInter.mp hmem M₀)
  exact hM₀spec w hws hwu

/-- Inside a box on whose edges two configurations agree, a cluster of a general base point which
is contained in the box is contained in the other configuration's cluster. -/
theorem cluster_subset_of_eq_on_box_gen {R : ℝ} {ω ω' : Config M.V} {v : M.V}
    (hagree : ∀ e ∈ M.boxEdges R, e ∈ ω → e ∈ ω')
    (hsub : cluster ω v ⊆ M.ball R) :
    cluster ω v ⊆ cluster ω' v := by
  intro y hy
  rw [mem_cluster_iff] at hy
  have hy' : Relation.ReflTransGen (openGraph ω).Adj v y :=
    (SimpleGraph.reachable_iff_reflTransGen (G := openGraph ω) v y).mp hy
  clear hy
  have hmain : Relation.ReflTransGen (openGraph ω').Adj v y := by
    induction hy' with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        rename_i b c
        have hb : b ∈ M.ball R :=
          hsub (mem_cluster_iff.mpr
            ((SimpleGraph.reachable_iff_reflTransGen (G := openGraph ω) v b).mpr hab))
        have hc : c ∈ M.ball R :=
          hsub (mem_cluster_iff.mpr
            ((SimpleGraph.reachable_iff_reflTransGen (G := openGraph ω) v c).mpr
              (Relation.ReflTransGen.tail hab hbc)))
        have hedge : s(b, c) ∈ ω := (openGraph_adj.mp hbc).2
        have hbox : s(b, c) ∈ M.boxEdges R := by
          rw [SourceModelData.boxEdges, Finset.mem_sym2_iff]
          intro a ha
          have ha' : a = b ∨ a = c := by simpa using ha
          rcases ha' with rfl | rfl
          · simpa using hb
          · simpa using hc
        have hopen : s(b, c) ∈ ω' := hagree _ hbox hedge
        exact Relation.ReflTransGen.tail ih (openGraph_adj.mpr ⟨hbc.ne, hopen⟩)
  exact mem_cluster_iff.mpr
    ((SimpleGraph.reachable_iff_reflTransGen (G := openGraph ω') v y).mpr hmain)

/-- **Volume comparison at a general base point.**  Off the box-change event and off the escape
event of `v`, and for `r ≥ r₀`, the cut-off cluster volume of `v` is the same at `r` and `r₀`. -/
theorem clusterVol_eq_of_notMem {r0 r R : ℝ} {u : Sym2 M.V → ℝ} {v : M.V}
    (hr0 : 0 < r0) (hrr : r0 ≤ r)
    (hbox : u ∉ M.markBoxChange r0 r R) (hesc : u ∉ M.markEscapeAt r R v) :
    clusterVol (atParameter (M.cutProb r) u) v =
      clusterVol (atParameter (M.cutProb r0) u) v := by
  have hr : 0 < r := lt_of_lt_of_le hr0 hrr
  refine le_antisymm ?_ (M.clusterVol_atParameter_mono hr0 hr hrr u v)
  refine M.clusterVol_le_of_cluster_subset ?_
  refine M.cluster_subset_of_eq_on_box_gen (R := R) ?_ ?_
  · intro e he hmem
    exact M.lt_cutProb_r0_of_notMem_markBoxChange hbox he hmem
  · intro y hy
    by_contra hcon
    exact hesc ⟨y, hcon, mem_cluster_iff.mpr hy⟩


/-! ## 12. Pointwise identification of the pair integrand off the two error events -/

/-- **Off the box-change event and the union escape event the pair integrand is unchanged.**  For
`r₀ ≤ r ≤ r₁`, provided the closed window does not move between `r₀` and `r`, no edge inside the
box and no edge of the trajectory of any relevant cluster changes, so every cluster volume in the
integrand — of the origin and of every point of `B_{r₁}` — is the same at `r` as at `r₀`.

The escape event is taken over the *finite* set `insert 0 B_{r₁}`: these are exactly the base
points whose clusters the frozen window `B_{r₀} = B_r` involves, and this is the point at which
the landed root-only comparison `SourceModelData.clusterVol_le_of_notMem` does not suffice. -/
theorem pairMarkFun_eq_of_notMem {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hr0r : r0 ≤ r)
    (hrr1 : r ≤ r1) (hwin : E1Sign.ballF M r = E1Sign.ballF M r0) {u : Sym2 M.V → ℝ}
    (hbox : u ∉ M.markBoxChange r0 r R)
    (hesc : u ∉ M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))) :
    M.pairMarkFun r u = M.pairMarkFun r0 u := by
  have hrpos : 0 < r := lt_of_lt_of_le hr0 hr0r
  have hrr1pos : 0 < r1 := lt_of_lt_of_le hrpos hrr1
  have h0mem : (0 : M.V) ∈ insert (0 : M.V) (E1Sign.ballF M r1) := Finset.mem_insert_self _ _
  have hnotid : ∀ v ∈ insert (0 : M.V) (E1Sign.ballF M r1), u ∉ M.markEscapeAt r R v := by
    intro v hv hcontra
    exact hesc (M.mem_markEscapeUnion.mpr ⟨v, hv, M.markEscapeAt_mono hrpos hrr1pos hrr1 v hcontra⟩)
  have hvol : M.markVol r u = M.markVol r0 u :=
    M.clusterVol_eq_of_notMem hr0 hr0r hbox (hnotid 0 h0mem)
  have hsum : (∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r) u) y)
      = ∑ y ∈ E1Sign.ballF M r0, clusterVol (atParameter (M.cutProb r0) u) y := by
    rw [hwin]
    refine Finset.sum_congr rfl fun y hy => ?_
    exact M.clusterVol_eq_of_notMem hr0 hr0r hbox
      (hnotid y (Finset.mem_insert_of_mem (M.ballF_mono (le_trans hr0r hrr1) hy)))
  simp only [SourceModelData.pairMarkFun, hvol, hsum]

/-- **Increment bound for the pair integrand.**  For `r₀ ≤ r ≤ r₁` and a fixed window, the pair
integrand at `r` exceeds the one at `r₀` only on the box-change event and the union escape event,
where it is dominated by the `r₁`-integrand. -/
theorem pairMarkFun_le_add {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hr0r : r0 ≤ r) (hrr1 : r ≤ r1)
    (hwin : E1Sign.ballF M r = E1Sign.ballF M r0) (u : Sym2 M.V → ℝ) :
    M.pairMarkFun r u ≤
      M.pairMarkFun r0 u +
        (M.markBoxChange r0 r R).indicator (M.pairMarkFun r1) u +
        (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
          (M.pairMarkFun r1) u := by
  have hrpos : 0 < r := lt_of_lt_of_le hr0 hr0r
  have hmono : M.pairMarkFun r u ≤ M.pairMarkFun r1 u := M.pairMarkFun_mono hrpos hrr1 u
  by_cases hbox : u ∈ M.markBoxChange r0 r R
  · rw [Set.indicator_of_mem hbox]
    calc M.pairMarkFun r u ≤ M.pairMarkFun r1 u := hmono
      _ ≤ M.pairMarkFun r0 u + M.pairMarkFun r1 u := le_add_self
      _ ≤ M.pairMarkFun r0 u + M.pairMarkFun r1 u +
            (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
              (M.pairMarkFun r1) u := le_self_add
  · rw [Set.indicator_of_notMem hbox]
    by_cases hesc : u ∈ M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))
    · rw [Set.indicator_of_mem hesc]
      calc M.pairMarkFun r u ≤ M.pairMarkFun r1 u := hmono
        _ ≤ M.pairMarkFun r0 u + M.pairMarkFun r1 u := le_add_self
        _ = M.pairMarkFun r0 u + 0 + M.pairMarkFun r1 u := by rw [add_zero]
    · rw [Set.indicator_of_notMem hesc, add_zero, add_zero]
      exact le_of_eq (M.pairMarkFun_eq_of_notMem hr0 hr0r hrr1 hwin hbox hesc)

/-- **Integrated increment bound for the pair mass.** -/
theorem pairMass_le_add {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hr0r : r0 ≤ r) (hrr1 : r ≤ r1)
    (hwin : E1Sign.ballF M r = E1Sign.ballF M r0) :
    E1Sign.pairMass M r ≤
      E1Sign.pairMass M r0 +
        (∫⁻ u, (M.markBoxChange r0 r R).indicator (M.pairMarkFun r1) u
          ∂(markMeasure M.V)) +
        (∫⁻ u, (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
          (M.pairMarkFun r1) u ∂(markMeasure M.V)) := by
  have hmono : ∫⁻ u, M.pairMarkFun r u ∂(markMeasure M.V) ≤
      ∫⁻ u, (M.pairMarkFun r0 u +
        (M.markBoxChange r0 r R).indicator (M.pairMarkFun r1) u +
        (M.markEscapeUnion r1 R (insert (0 : M.V) (E1Sign.ballF M r1))).indicator
          (M.pairMarkFun r1) u) ∂(markMeasure M.V) :=
    lintegral_mono fun u => M.pairMarkFun_le_add hr0 hr0r hrr1 hwin u
  have h12 : Measurable fun u : Sym2 M.V → ℝ => M.pairMarkFun r0 u +
      (M.markBoxChange r0 r R).indicator (M.pairMarkFun r1) u :=
    (M.measurable_pairMarkFun r0).add
      ((M.measurable_pairMarkFun r1).indicator (M.measurableSet_markBoxChange r0 r R))
  rw [lintegral_add_left h12, lintegral_add_left (M.measurable_pairMarkFun r0)] at hmono
  rw [M.pairMass_eq_lintegral_pairMarkFun r, M.pairMass_eq_lintegral_pairMarkFun r0]
  exact hmono

/-! ## 13. The window is locally constant from the right -/

/-- **The closed window is constant on a right-neighbourhood.**  Because the set of attained radii
inside any finite window is finite, there is `δ > 0` with `B_r = B_{r₀}` for `r ∈ (r₀, r₀ + δ)`. -/
theorem exists_ballF_eq_of_right {r0 r1 : ℝ} (hr0r1 : r0 < r1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Set.Ioo r0 (r0 + δ), E1Sign.ballF M r = E1Sign.ballF M r0 := by
  classical
  set g : M.V → ℝ := fun y => M.S.ρ (toVec y) with hg
  set T : Finset M.V := (E1Sign.ballF M r1).filter (fun y => r0 < g y) with hT
  have hTspec : ∀ y : M.V, y ∈ T ↔ y ∈ E1Sign.ballF M r1 ∧ r0 < g y := by
    intro y
    rw [hT, Finset.mem_filter]
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · refine ⟨(r1 - r0) / 2, by linarith, ?_⟩
    intro r hr
    have hrr1 : r ≤ r1 := by linarith [hr.2]
    refine Finset.Subset.antisymm ?_ (M.ballF_mono (le_of_lt hr.1))
    intro y hy
    have hρ : g y ≤ r := (M.mem_ballF_rho).mp hy
    refine (M.mem_ballF_rho).mpr ?_
    by_contra hcon
    have hcon' : r0 < g y := not_le.mp hcon
    have hyT : y ∈ T := (hTspec y).mpr ⟨(M.mem_ballF_rho).mpr (hρ.trans hrr1), hcon'⟩
    rw [hT0] at hyT
    exact absurd hyT (Finset.notMem_empty y)
  · have hne : (T.image g).Nonempty := hTne.image g
    refine ⟨(T.image g).min' hne - r0, ?_, ?_⟩
    · have hmem : (T.image g).min' hne ∈ T.image g := Finset.min'_mem _ hne
      obtain ⟨y, hy, hyval⟩ := Finset.mem_image.mp hmem
      have h1 : r0 < g y := ((hTspec y).mp hy).2
      linarith [hyval, h1]
    · intro r hr
      have hmin_le_r1 : (T.image g).min' hne ≤ r1 := by
        have hmem : (T.image g).min' hne ∈ T.image g := Finset.min'_mem _ hne
        obtain ⟨y, hy, hyval⟩ := Finset.mem_image.mp hmem
        rw [← hyval]
        exact (M.mem_ballF_rho).mp ((hTspec y).mp hy).1
      have hrr1 : r ≤ r1 := by linarith [hr.2]
      refine Finset.Subset.antisymm ?_ (M.ballF_mono (le_of_lt hr.1))
      intro y hy
      have hρ : g y ≤ r := (M.mem_ballF_rho).mp hy
      refine (M.mem_ballF_rho).mpr ?_
      by_contra hcon
      have hcon' : r0 < g y := not_le.mp hcon
      have hyT : y ∈ T := (hTspec y).mpr ⟨(M.mem_ballF_rho).mpr (hρ.trans hrr1), hcon'⟩
      have h2 : (T.image g).min' hne ≤ g y :=
        Finset.min'_le _ _ (Finset.mem_image_of_mem g hyT)
      linarith [hr.2]


/-! ## 14. The error-event integrals shrink -/

/-- Bridge between the indicator form and the restricted-integral form. -/
theorem toReal_indicator_eq_setIntegral {s : Set (Sym2 M.V → ℝ)} (hs : MeasurableSet s)
    (f : (Sym2 M.V → ℝ) → ℝ≥0∞) :
    (∫⁻ u, s.indicator f u ∂(markMeasure M.V)).toReal
      = (∫⁻ u in s, f u ∂(markMeasure M.V)).toReal := by
  rw [lintegral_indicator hs f]

/-- **The box-change integral vanishes from the right**, exactly as in
`SourceModelData.tendsto_boxIntegral_pow`, with the `r₁`-pair integrand in place of `|K_{r₁}|^p`
and the pair-mass finiteness in place of the moment. -/
theorem tendsto_boxIntegral_pair (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (_hr1 : r0 < r1)
    (hfin : E1Sign.pairMass M r1 ≠ ⊤) (R : ℝ) :
    Tendsto (fun r => (∫⁻ u in M.markBoxChange r0 r R, M.pairMarkFun r1 u
      ∂(markMeasure M.V)).toReal) (𝓝[>] r0) (𝓝 0) := by
  set rseq : ℕ → ℝ := fun n => r0 + r0 / ((n : ℝ) + 2) with hrseq
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hrpos : ∀ n : ℕ, r0 < rseq n := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h2 : 0 < r0 / ((n : ℝ) + 2) := div_pos hr0 h1
    simp only [hrseq]
    linarith
  have hseq : Tendsto rseq atTop (𝓝 r0) := by
    have h0 : Tendsto (fun n : ℕ => r0 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa using tendsto_const_nhds.div_atTop h1
    simp only [hrseq]
    simpa using tendsto_const_nhds.add h0
  have hanti : Antitone fun n : ℕ => M.markBoxChange r0 (rseq n) R := by
    intro n m hnm
    refine M.markBoxChange_mono hr0 (lt_trans hr0 (hrpos m)) (lt_trans hr0 (hrpos n)) ?_
    have hd1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have hd2 : (0 : ℝ) < (m : ℝ) + 2 := hden m
    have hcast : ((n : ℝ) + 2) ≤ ((m : ℝ) + 2) := by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith
    simp only [hrseq]
    have : r0 / ((m : ℝ) + 2) ≤ r0 / ((n : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr0.le hd1 hcast
    linarith
  have hnull : markMeasure M.V (⋂ n : ℕ, M.markBoxChange r0 (rseq n) R) = 0 :=
    measure_mono_null (M.iInter_markBoxChange_subset hr0 hseq) (M.measure_boxNull r0 R)
  have hInt : (∫⁻ a, M.pairMarkFun r1 a ∂(markMeasure M.V)) = E1Sign.pairMass M r1 :=
    (M.pairMass_eq_lintegral_pairMarkFun r1).symm
  have hconv : Tendsto (fun n : ℕ => (∫⁻ u in M.markBoxChange r0 (rseq n) R,
      M.pairMarkFun r1 u ∂(markMeasure M.V)).toReal) atTop (𝓝 0) :=
    tendsto_setLIntegral_toReal_of_antitone (μ := markMeasure M.V)
      (f := M.pairMarkFun r1) (M.measurable_pairMarkFun r1)
      (by rw [hInt]; exact hfin)
      (fun n => M.measurableSet_markBoxChange r0 (rseq n) R) hanti hnull
  refine tendsto_zero_of_le_seq (r := rseq) ?_ ?_ hrpos hconv
  · intro x y hx hxy
    have hy : 0 < y := lt_of_lt_of_le (lt_trans hr0 hx) hxy
    have hsub : M.markBoxChange r0 x R ⊆ M.markBoxChange r0 y R :=
      M.markBoxChange_mono hr0 (lt_trans hr0 hx) hy hxy
    have hfin' : (∫⁻ u in M.markBoxChange r0 y R, M.pairMarkFun r1 u
        ∂(markMeasure M.V)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono_set (Set.subset_univ _))
      rw [Measure.restrict_univ, hInt]
      exact hfin
    exact ENNReal.toReal_mono hfin' (lintegral_mono_set hsub)
  · intro x
    exact ENNReal.toReal_nonneg

/-- **The union-escape integral vanishes as the ball grows**, along the whole escape family at the
outer radius `r₁`. -/
theorem tendsto_escapeIntegral_pair (r1 : ℝ) (hfin : E1Sign.pairMass M r1 ≠ ⊤)
    (hcm : M.cutMassAt r1 0 ≠ ⊤) (s : Finset M.V) :
    Tendsto (fun n : ℕ => (∫⁻ u in M.markEscapeUnion r1 (n : ℝ) s, M.pairMarkFun r1 u
      ∂(markMeasure M.V)).toReal) atTop (𝓝 0) :=
  tendsto_setLIntegral_toReal_of_antitone (μ := markMeasure M.V)
    (f := M.pairMarkFun r1) (M.measurable_pairMarkFun r1)
    (by rw [← M.pairMass_eq_lintegral_pairMarkFun r1]; exact hfin)
    (fun n => M.measurableSet_markEscapeUnion r1 (n : ℝ) s)
    (fun n m hnm => M.markEscapeUnion_antitone (by exact_mod_cast hnm) s)
    (M.measure_iInter_markEscapeUnion_eq_zero hcm)

/-! ## 15. Right continuity of the pair mass -/

/-- **Continuity from above of the pair mass.**  For `r ↓ r₀` the pair mass at `r` is bounded by
the one at `r₀` plus the box-change and escape integrals of the fixed `r₁`-integrand, both of
which vanish; monotonicity supplies the reverse inequality.  Only the second cutoff moment at `r₁`
enters. -/
theorem tendsto_pairMassReal_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) :
    Tendsto (fun r => (E1Sign.pairMass M r).toReal) (𝓝[>] r0)
      (𝓝 ((E1Sign.pairMass M r0).toReal)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set s : Finset M.V := insert (0 : M.V) (E1Sign.ballF M r1) with hs
  have hfin1 : E1Sign.pairMass M r1 ≠ ⊤ := E1Sign.pairMass_ne_top M r1 h2
  have hfin1' : (∫⁻ u, M.pairMarkFun r1 u ∂(markMeasure M.V)) ≠ ⊤ := by
    rw [← M.pairMass_eq_lintegral_pairMarkFun r1]
    exact hfin1
  have hcm : M.cutMassAt r1 0 ≠ ⊤ :=
    ne_top_of_le_ne_top h2 (E1Sign.cutMassAt_le_cutMoment_two M r1)
  have hesc_tend := M.tendsto_escapeIntegral_pair r1 hfin1 hcm s
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hesc_tend (ε / 2) (by linarith)
  have hN' : (∫⁻ u in M.markEscapeUnion r1 (N : ℝ) s, M.pairMarkFun r1 u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    have h := hN N le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h
  have hbox_tend := M.tendsto_boxIntegral_pair r0 hr0 hr1 hfin1 (N : ℝ)
  obtain ⟨δ1, hδ1, hspec1⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hbox_tend) (ε / 2) (by linarith)
  obtain ⟨δ2, hδ2, hwin⟩ := M.exists_ballF_eq_of_right hr1
  refine ⟨min δ1 (min δ2 (r1 - r0)), lt_min hδ1 (lt_min hδ2 (by linarith)), ?_⟩
  intro r hr hdist
  have habs : |r - r0| < min δ1 (min δ2 (r1 - r0)) := by
    rwa [Real.dist_eq] at hdist
  rw [Real.dist_eq, abs_lt] at hdist
  have hb1 := min_le_left δ1 (min δ2 (r1 - r0))
  have hb2 := min_le_right δ1 (min δ2 (r1 - r0))
  have hb3 := min_le_left δ2 (r1 - r0)
  have hb4 := min_le_right δ2 (r1 - r0)
  have hrr1 : r ≤ r1 := by linarith [hdist.2]
  have hrdel2 : r < r0 + δ2 := by linarith [hdist.2]
  have hwinr : E1Sign.ballF M r = E1Sign.ballF M r0 := hwin r ⟨hr, hrdel2⟩
  have hboxsmall : (∫⁻ u in M.markBoxChange r0 r (N : ℝ), M.pairMarkFun r1 u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    have h2' : dist (∫⁻ u in M.markBoxChange r0 r (N : ℝ), M.pairMarkFun r1 u
        ∂(markMeasure M.V)).toReal 0 < ε / 2 :=
      hspec1 hr (by rw [Real.dist_eq]; exact lt_of_lt_of_le habs hb1)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h2'
  have hincl := M.pairMass_le_add hr0 hr.le hrr1 hwinr (R := (N : ℝ))
  have hfinr0 : E1Sign.pairMass M r0 ≠ ⊤ :=
    E1Sign.pairMass_ne_top M r0 (M.cutMoment_ne_top_of_le (le_of_lt hr1) 2 h2)
  have hfinr : E1Sign.pairMass M r ≠ ⊤ :=
    ne_top_of_le_ne_top hfin1 (E1Sign.pairMass_mono M (lt_trans hr0 hr) hrr1)
  have hboxfin : (∫⁻ u, (M.markBoxChange r0 r (N : ℝ)).indicator (M.pairMarkFun r1) u
      ∂(markMeasure M.V)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin1' (lintegral_mono fun u => ?_)
    by_cases hu : u ∈ M.markBoxChange r0 r (N : ℝ)
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      exact zero_le
  have hescfin : (∫⁻ u, (M.markEscapeUnion r1 (N : ℝ) s).indicator (M.pairMarkFun r1) u
      ∂(markMeasure M.V)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin1' (lintegral_mono fun u => ?_)
    by_cases hu : u ∈ M.markEscapeUnion r1 (N : ℝ) s
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      exact zero_le
  have hsplit1 : (E1Sign.pairMass M r0 +
      (∫⁻ u, (M.markBoxChange r0 r (N : ℝ)).indicator (M.pairMarkFun r1) u
        ∂(markMeasure M.V))) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinr0, hboxfin⟩
  have hupperfin : E1Sign.pairMass M r0 +
      (∫⁻ u, (M.markBoxChange r0 r (N : ℝ)).indicator (M.pairMarkFun r1) u
        ∂(markMeasure M.V)) +
      (∫⁻ u, (M.markEscapeUnion r1 (N : ℝ) s).indicator (M.pairMarkFun r1) u
        ∂(markMeasure M.V)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hsplit1, hescfin⟩
  have hreal := ENNReal.toReal_mono hupperfin hincl
  rw [ENNReal.toReal_add hsplit1 hescfin, ENNReal.toReal_add hfinr0 hboxfin] at hreal
  have hboxsmall' : (∫⁻ u, (M.markBoxChange r0 r (N : ℝ)).indicator (M.pairMarkFun r1) u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    rw [M.toReal_indicator_eq_setIntegral (M.measurableSet_markBoxChange r0 r (N : ℝ))
      (M.pairMarkFun r1)]
    exact hboxsmall
  have hescsmall' : (∫⁻ u, (M.markEscapeUnion r1 (N : ℝ) s).indicator (M.pairMarkFun r1) u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    rw [M.toReal_indicator_eq_setIntegral (M.measurableSet_markEscapeUnion r1 (N : ℝ) s)
      (M.pairMarkFun r1)]
    exact hN'
  have hmono : (E1Sign.pairMass M r0).toReal ≤ (E1Sign.pairMass M r).toReal :=
    ENNReal.toReal_mono hfinr (E1Sign.pairMass_mono M hr0 hr.le)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## 16. Two-sided continuity of the pair mass, and of the excluded mass -/

/-- **Continuity of the pair mass at an off-corner radius**, from the second cutoff moment at one
strictly larger radius and no lattice point on the sphere.  Left continuity is §6, right
continuity is §15. -/
theorem continuousAt_pairMassReal {r0 : ℝ} (hr0 : 0 < r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) :
    ContinuousAt (fun r => (E1Sign.pairMass M r).toReal) r0 := by
  have h2r0 : M.cutMoment 2 r0 ≠ ⊤ := M.cutMoment_ne_top_of_le hr1.le 2 h2
  have hleft := M.tendsto_pairMassReal_nhdsLT_of_no_sphere hr0 hsphere
    (E1Sign.pairMass_ne_top M r0 h2r0)
  have hright := M.tendsto_pairMassReal_nhdsGT r0 hr0 hr1 h2
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ1, hδ1, hspec1⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hleft) ε hε
  obtain ⟨δ2, hδ2, hspec2⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hright) ε hε
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun x hx => ?_⟩
  rw [Real.dist_eq] at hx ⊢
  rcases lt_trichotomy x r0 with h | h | h
  · refine hspec1 (show x ∈ Set.Iio r0 from h) ?_
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hx (min_le_left _ _)
  · subst h
    simpa using hε
  · refine hspec2 (show x ∈ Set.Ioi r0 from h) ?_
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hx (min_le_right _ _)

/-- **The excluded mass is continuous at an off-corner radius.**  This closes direction (A) of the
swarm: the excluded mass inherits its radius regularity from the pair mass through the exact
identity `pairMass = connMass + exclMass`, and the pair mass is handled by monotone convergence
from the left and the box/escape comparison from the right.

Hypotheses: `r₀ > 0`; no lattice point on the sphere `{ρ = r₀}` (the closed window is the strict
one); and finiteness of the second and third cutoff moments at one strictly larger radius `r₁`
(the second moment bounds `pairMass` and `exclMass`, the third bounds `connMass` in the landed
`continuousAt_connMassReal`). -/
theorem continuousAt_exclScalar {r0 : ℝ} (hr0 : 0 < r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) {r1 : ℝ} (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤) :
    ContinuousAt M.exclScalar r0 :=
  M.continuousAt_exclScalar_of_pairMassReal hr0 hsphere hr1 h2 h3
    (M.continuousAt_pairMassReal hr0 hsphere hr1 h2)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMarkFun

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMarkFunLt

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMassLt

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMarkFun_mono

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_finset_sum_nat

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_pairWindowSum

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_pairMarkFun_nat

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_pairMass_nat

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMass_le_pairMassLt

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_pairMassReal_nhdsLT

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ballFLt_eq_ballF_of_no_sphere

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMassLt_eq_pairMass_of_no_sphere

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_pairMassReal_nhdsLT_of_no_sphere

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclScalar_eq_pairMassReal_sub_connMassReal

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_exclScalar_nhdsLT

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_exclScalar_of_pairMassReal

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_pairMassReal_iff_continuousAt_exclScalar

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_pairMassReal_nhdsLT_of_moment

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.markEscapeAt

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.markEscapeUnion

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.markVol_eq_cutMassAt

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurableSet_markEscapeAt

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurableSet_markEscapeUnion

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.markEscapeUnion_antitone

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.markEscapeUnion_mono

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measure_iInter_markEscapeUnion_eq_zero

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cluster_subset_of_eq_on_box_gen

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.clusterVol_eq_of_notMem

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMarkFun_eq_of_notMem

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMarkFun_le_add

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMass_le_add

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_ballF_eq_of_right

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.toReal_indicator_eq_setIntegral

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_boxIntegral_pair

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_escapeIntegral_pair

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_pairMassReal_nhdsGT

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_pairMassReal

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_exclScalar

end PercLib.CriticalLRP.Orchestration
