/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The one-step conditional estimate at the actual BFS exploration

Swarm `smwpbvro2`, member m2, direction d2.

`PROOF.md` Lemma 4.4, in the conditional-expectation-free form of a fibre integral:
for a frontier state `σ` with finite processed set `Q` and frontier `T`, and any history
function `H` of the revealed block,

  `∫_{state = σ} H · λ^{|G_{k+1}|} ≤ (∫_{state = σ} H) · e^{(λ-1) m #T}`.

The proof uses the committed adapted-revelation factorization
(`lintegral_bfs_adapted_pgf_le`), the state-level fresh edge set `freshEdges`, monotone
convergence over finite fresh subsets, `gen_encard_le_queried`, and the row-sum charging
`sum_le_rowSum` with the real→`ℝ≥0∞` factor bound `prod_pgfFactor_le_exp` of direction 1.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Generation.Fresh

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open Classical MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators Topology

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*} [Countable V]

/-! ### The state bound -/

/-- The one-step bound attached to a compressed state: at `some (Q,T)` it is
`e^{(λ-1) m #T}`, and at the trivial state it is `⊤` (no information, which is all the
estimate can give when the frontier is infinite). -/
def stateBound (τ m : ℝ) (σ : FinState V) : ℝ≥0∞ :=
  match σ with
  | some (_, T) => ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ))))
  | none => ⊤

theorem stateBound_none (τ m : ℝ) : stateBound τ m (none : FinState V) = ⊤ := rfl

/-- At a finite state the one-step bound is the `epow` of the Poisson envelope value. -/
theorem stateBound_some_eq_epow (τ m : ℝ) (hτ : 1 ≤ τ) (hm : 0 ≤ m) (Q T : Finset V) :
    stateBound τ m (some (Q, T)) =
      epow (ENNReal.ofReal (Real.exp ((τ - 1) * m))) ((T.card : ℕ∞)) := by
  have h1 : (τ - 1) * (m * (T.card : ℝ)) = (T.card : ℝ) * ((τ - 1) * m) := by ring
  have h2 : Real.exp ((T.card : ℝ) * ((τ - 1) * m)) = Real.exp ((τ - 1) * m) ^ T.card :=
    Real.exp_nat_mul _ _
  rw [stateBound, h1, h2, epow_ofReal_pow (Real.one_le_exp (mul_nonneg (by linarith) hm))]

/-! ### Measurability of the open count -/

theorem openCount_eq_sum (S : Finset (Sym2 V)) (ω : Config V) :
    openCount S ω = ∑ e ∈ S, (if e ∈ ω then 1 else 0) := by
  classical
  rw [openCount, Finset.card_filter]

theorem measurable_openCount (S : Finset (Sym2 V)) :
    Measurable fun ω : Config V => openCount S ω := by
  classical
  have h : (fun ω : Config V => openCount S ω)
      = fun ω => ∑ e ∈ S, (if e ∈ ω then (1:ℕ) else 0) := by
    funext ω; rw [openCount_eq_sum]
  rw [h]
  exact Finset.measurable_sum _ (fun e _ =>
    Measurable.ite (measurableSet_mem e) measurable_const measurable_const)

theorem measurable_pow_openCount_generation (t : ℝ≥0∞) (S : Finset (Sym2 V)) :
    Measurable fun ω : Config V => t ^ openCount S ω :=
  (measurable_of_countable (fun n : ℕ => t ^ n)).comp (measurable_openCount S)

/-! ### The per-fresh-set estimate -/

theorem unitInterval_toNNReal_coe (p : Sym2 V → unitInterval) (e : Sym2 V) :
    ((unitInterval.toNNReal (p e)) : ℝ≥0∞) = ENNReal.ofReal ((p e : ℝ)) := by
  rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]

/-- **The per-fresh-set one-step estimate.**  For a finite fresh set `t` of queried edges
at a finite state `(Q,T)`, the integral over the state fibre of a history function times
the fresh monomial is bounded by the history mass times `e^{(λ-1) m #T}`. -/
theorem fibre_factor_bound {p : Sym2 V → unitInterval} {m : ℝ} (hrow : RowSum p m)
    {τ : ℝ} (hτ : 1 ≤ τ) (o : V) (k : ℕ) {Q T : Finset V}
    (hQT : Disjoint (Q : Set V) (T : Set V))
    (t : Finset (Sym2 V)) (ht : (t : Set (Sym2 V)) ⊆ freshEdges (some (Q, T)))
    (H : Set (Sym2 V) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
        H (hist o k ω) * (ENNReal.ofReal τ) ^ openCount t ω ∂(prodBernoulli p)
      ≤ (∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
          H (hist o k ω) ∂(prodBernoulli p))
        * ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ)))) := by
  classical
  set σ₀ : FinState V := some (Q, T) with hσ₀
  set G : Config V → ℝ≥0∞ :=
    fun ω => if finState ω o k = σ₀ then H (hist o k ω) else 0 with hG
  set Hh : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞ :=
    fun σ η => if σ = σ₀ then H (extendBlock (revealFin σ) η) else 0 with hHh
  set S : FinState V → Finset (Sym2 V) := fun σ => if σ = σ₀ then t else ∅ with hSdef
  set B : FinState V → ℝ≥0∞ :=
    fun σ => if σ = σ₀ then ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ)))) else ⊤
    with hBdef
  have hHmeas : ∀ σ, Measurable (Hh σ) := by
    intro σ
    by_cases h : σ = σ₀
    · rw [show Hh σ = fun η => H (extendBlock (revealFin σ) η) from by
        simp only [hHh]
        funext η
        simp only [ite_eq_left h]]
      exact hH.comp (measurable_extendBlock _)
    · rw [show Hh σ = fun _ => (0 : ℝ≥0∞) from by
        simp only [hHh]
        funext η
        simp only [ite_eq_right h]]
      exact measurable_const
  have hGfac : ∀ ω, G ω = Hh (finState ω o k)
      (blockRestrict (revealFin (finState ω o k)) ω) := by
    intro ω
    simp only [hG, hHh]
    by_cases h : finState ω o k = σ₀
    · rw [ite_eq_left h, ite_eq_left h, extendBlock_blockRestrict]
      rfl
    · rw [ite_eq_right h, ite_eq_right h]
  have hSdisj : ∀ σ, Disjoint ((S σ : Finset (Sym2 V)) : Set (Sym2 V)) (revealFin σ) := by
    intro σ
    by_cases h : σ = σ₀
    · subst h
      rw [hSdef]
      simp only [↓reduceIte, hσ₀]
      rw [Set.disjoint_left]
      intro e he1 he2
      exact (Set.disjoint_left.mp (freshEdges_disjoint_reveal Q T hQT)) (ht he1) he2
    · rw [hSdef]
      simp only [ite_eq_right h, Finset.coe_empty]
      exact Set.empty_disjoint _
  have hB : ∀ σ : FinState V, (∏ e ∈ S σ,
      (ENNReal.ofReal τ * (unitInterval.toNNReal (p e) : ℝ≥0∞) +
        (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞)))) ≤ B σ := by
    intro σ
    by_cases h : σ = σ₀
    · subst h
      rw [hSdef, hBdef]
      simp only [↓reduceIte, hσ₀]
      have hq : ∀ e ∈ t, (ENNReal.ofReal τ * (unitInterval.toNNReal (p e) : ℝ≥0∞) +
          (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞)))
          = (ENNReal.ofReal τ * ENNReal.ofReal ((p e : ℝ)) +
              (1 - ENNReal.ofReal ((p e : ℝ)))) := by
        intro e _
        rw [unitInterval_toNNReal_coe]
      rw [Finset.prod_congr rfl hq]
      refine le_trans (PercLib.Probability.ExplorationPoisson.prod_pgfFactor_le_exp (fun e => ((p e : unitInterval) : ℝ))
        (fun e => (p e).2.1) (fun e => (p e).2.2) τ hτ t
        (m := m * (T.card : ℝ)) ?_) (le_of_eq ?_)
      · refine sum_le_rowSum (T := T) (U := ((Q : Set V) ∪ (T : Set V))ᶜ) hrow ?_ t ht
        rw [Set.disjoint_left]
        intro x hxT hx
        exact hx (Or.inr hxT)
      · congr 1
    · simp only [hSdef, hBdef]
      rw [ite_eq_right h, ite_eq_right h]
      simp
  have hmain := lintegral_bfs_adapted_pgf_le p o k G Hh hHmeas hGfac S hSdisj
    (ENNReal.ofReal τ) B hB
  -- identify the left side
  have hleft : ∫⁻ ω, G ω * (ENNReal.ofReal τ) ^ openCount (S (finState ω o k)) ω
      ∂(prodBernoulli p)
      = ∫⁻ ω in {ω : Config V | finState ω o k = σ₀},
          H (hist o k ω) * (ENNReal.ofReal τ) ^ openCount t ω ∂(prodBernoulli p) := by
    rw [← lintegral_indicator (measurableSet_finState_eq o k σ₀)]
    refine lintegral_congr (fun ω => ?_)
    by_cases h : finState ω o k = σ₀
    · simp only [hG, hSdef, h, ↓reduceIte]
      rw [Set.indicator_of_mem (by simpa using h)]
    · simp only [hG, hSdef, h, ↓reduceIte]
      rw [Set.indicator_of_notMem (by simpa using h)]
      simp
  rw [hleft] at hmain
  -- identify the right side
  have hright : ∑' σ : FinState V,
      (∫⁻ ω in {ω : Config V | finState ω o k = σ}, G ω ∂(prodBernoulli p)) * B σ
      = (∫⁻ ω in {ω : Config V | finState ω o k = σ₀},
          H (hist o k ω) ∂(prodBernoulli p))
        * ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ)))) := by
    rw [tsum_eq_single σ₀]
    · simp only [hBdef, ↓reduceIte]
      congr 1
      refine setLIntegral_congr_fun (measurableSet_finState_eq o k σ₀) (fun ω hω => ?_)
      simp only [hG]
      rw [ite_eq_left (by simpa using hω)]
    · intro b hb
      have hzero : ∀ ω ∈ {ω : Config V | finState ω o k = b}, G ω = 0 := by
        intro ω hω
        have hne : ¬ (finState ω o k = σ₀) := by
          intro hcon
          exact hb (hω.symm.trans hcon)
        simp only [hG]
        rw [ite_eq_right hne]
      rw [setLIntegral_congr_fun (measurableSet_finState_eq o k b) hzero]
      simp
  rw [hright] at hmain
  exact hmain



/-! ### The per-state one-step estimate -/

/-- Reachable finite states have disjoint processed set and frontier. -/
theorem finState_disjoint {ω : Config V} {o : V} {k : ℕ} {Q T : Finset V}
    (h : finState ω o k = some (Q, T)) : Disjoint (Q : Set V) (T : Set V) := by
  obtain ⟨hQ, hT⟩ := finState_eq_some_iff.mp h
  rw [hQ, hT]
  exact disjoint_P_A ω o k

/-- **The one-step conditional estimate at a finite frontier state.**  For any history
function `H` of the revealed block and any `1 ≤ τ`, the integral over the state fibre of
`H · τ^{|G_{k+1}|}` is at most the history mass times `e^{(τ-1) m #T}`.

The finite fresh sets are taken from the state-level set `freshEdges (some (Q,T))`; the
supremum over them is handled by monotone convergence, so no finiteness of the queried
set is assumed. -/
theorem fibre_step {p : Sym2 V → unitInterval} {m : ℝ} (hrow : RowSum p m)
    {τ : ℝ} (hτ : 1 ≤ τ) (o : V) (k : ℕ) (Q T : Finset V)
    (hQT : Disjoint (Q : Set V) (T : Set V))
    (H : Set (Sym2 V) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
        H (hist o k ω) * epow (ENNReal.ofReal τ) ((gen ω o k).encard) ∂(prodBernoulli p)
      ≤ (∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
          H (hist o k ω) ∂(prodBernoulli p))
        * ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ)))) := by
  classical
  have hs_meas : MeasurableSet {ω : Config V | finState ω o k = some (Q, T)} :=
    measurableSet_finState_eq o k (some (Q, T))
  have hHhist : Measurable fun ω : Config V => H (hist o k ω) := hH.comp (measurable_hist o k)
  -- the pointwise domination by the supremum over finite fresh sets
  have hpt : ∀ ω ∈ {ω : Config V | finState ω o k = some (Q, T)},
      H (hist o k ω) * epow (ENNReal.ofReal τ) ((gen ω o k).encard)
        ≤ H (hist o k ω) * ⨆ (F : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆
              freshEdges (some (Q, T))}), (ENNReal.ofReal τ) ^ openCount F.1 ω := by
    intro ω hω
    have hs : queried ω o k ∩ ω ⊆ freshEdges (some (Q, T)) := by
      have h1 : finState ω o k = some (Q, T) := by simpa using hω
      have h2 : queried ω o k ∩ ω ⊆ freshEdges (finState ω o k) :=
        Set.inter_subset_left.trans (queried_subset_freshEdges ω o k)
      rwa [h1] at h2
    exact mul_le_mul' le_rfl (gen_epow_le_iSup_openCount hτ hs)
  calc ∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
        H (hist o k ω) * epow (ENNReal.ofReal τ) ((gen ω o k).encard) ∂(prodBernoulli p)
      ≤ ∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
          H (hist o k ω) * ⨆ (F : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆
              freshEdges (some (Q, T))}), (ENNReal.ofReal τ) ^ openCount F.1 ω
            ∂(prodBernoulli p) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hs_meas] with ω hω
        exact hpt ω hω
    _ = ⨆ (F : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆ freshEdges (some (Q, T))}),
          ∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
            H (hist o k ω) * (ENNReal.ofReal τ) ^ openCount F.1 ω ∂(prodBernoulli p) := by
        rw [← lintegral_iSup_directed_of_measurable
          (f := fun (F : {F : Finset (Sym2 V) //
            (F : Set (Sym2 V)) ⊆ freshEdges (some (Q, T))}) (ω : Config V) =>
              H (hist o k ω) * (ENNReal.ofReal τ) ^ openCount F.1 ω)]
        · refine lintegral_congr (fun ω => ?_)
          rw [ENNReal.mul_iSup]
        · intro F
          exact hHhist.mul (measurable_pow_openCount_generation _ _)
        · intro F₁ F₂
          refine ⟨⟨F₁.1 ∪ F₂.1, ?_⟩, ?_, ?_⟩
          · rw [Finset.coe_union]
            exact Set.union_subset F₁.2 F₂.2
          · intro ω
            refine mul_le_mul' le_rfl ?_
            exact pow_le_pow_right₀ (by simpa using ENNReal.ofReal_le_ofReal hτ)
              (Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left))
          · intro ω
            refine mul_le_mul' le_rfl ?_
            exact pow_le_pow_right₀ (by simpa using ENNReal.ofReal_le_ofReal hτ)
              (Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right))
    _ ≤ ⨆ (_F : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆ freshEdges (some (Q, T))}),
          (∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
            H (hist o k ω) ∂(prodBernoulli p))
          * ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ)))) :=
        iSup_le (fun F => (fibre_factor_bound hrow hτ o k hQT F.1 F.2 H hH).trans
          (le_iSup (fun _ : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆
              freshEdges (some (Q, T))} =>
            (∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
              H (hist o k ω) ∂(prodBernoulli p))
            * ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ))))) F))
    _ = (∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
          H (hist o k ω) ∂(prodBernoulli p))
        * ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ)))) := by
        refine le_antisymm (iSup_le fun _ => le_rfl) ?_
        exact le_iSup (fun _ : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆
            freshEdges (some (Q, T))} =>
          (∫⁻ ω in {ω : Config V | finState ω o k = some (Q, T)},
            H (hist o k ω) ∂(prodBernoulli p))
          * ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ))))) ⟨∅, by simp⟩

end PercLib.CriticalLRP.Exploration.BFS
