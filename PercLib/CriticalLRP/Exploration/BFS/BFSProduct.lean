/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The countable BFS specialization of adapted product factorization.

Accepted from independent submission `smwpalb9h` direction D2.
No generation-moment induction or cluster-moment finiteness is asserted here.
-/
module

/-
Private swarm module (member m2, swarm smwpalb9h), direction 2.

Bridge to direction 1 (`RevealData`, member m1): the BFS exploration has a
*countable* adapted-revelation state — the pair `(P k, A k)` of processed set
and frontier when both are finite, and `none` otherwise.  (The full state space
`(Set V)^3` is uncountable, so the countable partition of `RevealData` needs
this refinement; `U k = (P k ∪ A k)ᶜ` is determined by the pair.)  The revealed
set of a finite state is the outline's `R k`, and the stopping-set property is
`state_eq_of_eqOn_revealed`.  The factorization theorems are direction 1's
`lintegral_adapted_prod` / `lintegral_adapted_pgf` / `lintegral_adapted_pgf_le`
applied to this data; nothing probabilistic is reproved here.
-/
public import PercLib.CriticalLRP.Exploration.BFS.RevealData
public import PercLib.Probability.Exploration.AdaptedReveal.PGF

set_option autoImplicit false


@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

set_option linter.unusedSectionVars false

variable {V : Type*} [Countable V]

/-- The countable adapted-revelation state: `some (Q,T)` when the processed set
and the frontier are both finite, and `none` otherwise. -/
abbrev FinState (V : Type*) := Option (Finset V × Finset V)

/-- The BFS state compressed to the countable type `FinState`. -/
noncomputable def finState (ω : Config V) (o : V) (k : ℕ) : FinState V := by
  classical
  exact if h : (P ω o k).Finite ∧ (A ω o k).Finite then
    some (h.1.toFinset, h.2.toFinset)
  else none

/-- Characterization of the finite states. -/
theorem finState_eq_some_iff {ω : Config V} {o : V} {k : ℕ} {Q T : Finset V} :
    finState ω o k = some (Q, T) ↔
      (Q : Set V) = P ω o k ∧ (T : Set V) = A ω o k := by
  classical
  unfold finState
  by_cases h : (P ω o k).Finite ∧ (A ω o k).Finite
  · rw [dite_eq_left h]
    constructor
    · intro heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨hQ, hT⟩ := heq
      exact ⟨by rw [← Set.Finite.coe_toFinset h.1, hQ],
        by rw [← Set.Finite.coe_toFinset h.2, hT]⟩
    · rintro ⟨hQ, hT⟩
      have hQ' : h.1.toFinset = Q := by
        ext v
        rw [Set.Finite.mem_toFinset, ← Finset.mem_coe, hQ]
      have hT' : h.2.toFinset = T := by
        ext v
        rw [Set.Finite.mem_toFinset, ← Finset.mem_coe, hT]
      rw [hQ', hT']
  · rw [dite_eq_right h]
    constructor
    · intro hcon
      exact absurd hcon (by simp)
    · rintro ⟨hQ, hT⟩
      exact absurd ⟨hQ ▸ Q.finite_toSet, hT ▸ T.finite_toSet⟩ h

theorem measurableSet_finState_eq_some (o : V) (k : ℕ) (Q T : Finset V) :
    MeasurableSet {ω : Config V | finState ω o k = some (Q, T)} := by
  have h : {ω : Config V | finState ω o k = some (Q, T)} =
      {ω : Config V | P ω o k = (Q : Set V)} ∩
        {ω : Config V | A ω o k = (T : Set V)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    exact ⟨fun hω => ⟨(finState_eq_some_iff.mp hω).1.symm,
        (finState_eq_some_iff.mp hω).2.symm⟩,
      fun hω => finState_eq_some_iff.mpr ⟨hω.1.symm, hω.2.symm⟩⟩
  rw [h]
  exact (measurableSet_P_eq o k (Q : Set V)).inter (measurableSet_A_eq o k (T : Set V))

theorem measurableSet_finState_eq (o : V) (k : ℕ) (σ : FinState V) :
    MeasurableSet {ω : Config V | finState ω o k = σ} := by
  cases σ with
  | none =>
      have h : {ω : Config V | finState ω o k = none} =
          (⋃ QT : Finset V × Finset V,
            {ω : Config V | finState ω o k = some QT})ᶜ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion]
        constructor
        · intro hω ⟨QT, hQT⟩
          rw [hω] at hQT
          cases hQT
        · intro hω
          cases h' : finState ω o k with
          | none => rfl
          | some QT => exact absurd ⟨QT, h'⟩ hω
      rw [h]
      exact (MeasurableSet.iUnion fun QT => by
        obtain ⟨Q, T⟩ := QT
        exact measurableSet_finState_eq_some o k Q T).compl
  | some QT =>
      obtain ⟨Q, T⟩ := QT
      exact measurableSet_finState_eq_some o k Q T

/-- The revealed edge set as a function of the countable state: for a finite
state `(Q,T)` it is the outline's `R k` (edges incident to `Q`), and for `none`
it is the whole space (the fibre of `none` is described trivially). -/
def revealFin : FinState V → Set (Sym2 V)
  | some (Q, _) => {e | ∃ v ∈ (Q : Set V), v ∈ e}
  | none => univ

/-- The BFS exploration as adapted-revelation data on the countable state
`FinState V`. -/
noncomputable def finRevealData (o : V) (k : ℕ) : RevealData (Sym2 V) (FinState V) where
  reveal := revealFin
  state := fun ω => finState ω o k
  cyl := fun σ =>
    {η : Set (revealFin σ) | finState (extendBlock (revealFin σ) η) o k = σ}
  cyl_measurable := fun σ =>
    (measurableSet_finState_eq o k σ).preimage (measurable_extendBlock _)
  fiber := fun σ => by
    ext ω
    simp only [Set.mem_ofPred_eq]
    cases σ with
    | none =>
        simp only [revealFin]
        rw [extendBlock_blockRestrict, Set.inter_univ]
    | some QT =>
        obtain ⟨Q, T⟩ := QT
        constructor
        · intro hω
          obtain ⟨hQ, hT⟩ := finState_eq_some_iff.mp hω
          have hrev : revealed ω o k = revealFin (some (Q, T)) := by
            ext e
            simp only [revealed, revealFin, Set.mem_ofPred_eq]
            constructor
            · rintro ⟨v, hv, hve⟩
              exact ⟨v, hQ ▸ hv, hve⟩
            · rintro ⟨v, hv, hve⟩
              exact ⟨v, hQ ▸ hv, hve⟩
          have hstate : P (ω ∩ revealFin (some (Q, T))) o k = P ω o k := by
            have h : ∀ e ∈ revealed ω o k, (e ∈ ω ↔ e ∈ ω ∩ revealFin (some (Q, T))) := by
              intro e he
              rw [hrev] at he
              exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
            exact (congrArg State.P
              (state_eq_of_eqOn_revealed ω (ω ∩ revealFin (some (Q, T))) o k h)).symm
          have hstateA : A (ω ∩ revealFin (some (Q, T))) o k = A ω o k := by
            have h : ∀ e ∈ revealed ω o k, (e ∈ ω ↔ e ∈ ω ∩ revealFin (some (Q, T))) := by
              intro e he
              rw [hrev] at he
              exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
            exact (congrArg State.A
              (state_eq_of_eqOn_revealed ω (ω ∩ revealFin (some (Q, T))) o k h)).symm
          rw [extendBlock_blockRestrict]
          exact finState_eq_some_iff.mpr ⟨hQ.trans hstate.symm, hT.trans hstateA.symm⟩
        · intro hη
          rw [extendBlock_blockRestrict] at hη
          obtain ⟨hQ, hT⟩ := finState_eq_some_iff.mp hη
          have hrev : revealed (ω ∩ revealFin (some (Q, T))) o k =
              revealFin (some (Q, T)) := by
            ext e
            simp only [revealed, revealFin, Set.mem_ofPred_eq]
            constructor
            · rintro ⟨v, hv, hve⟩
              exact ⟨v, hQ ▸ hv, hve⟩
            · rintro ⟨v, hv, hve⟩
              exact ⟨v, hQ ▸ hv, hve⟩
          have h : ∀ e ∈ revealed (ω ∩ revealFin (some (Q, T))) o k,
              (e ∈ ω ∩ revealFin (some (Q, T)) ↔ e ∈ ω) := by
            intro e he
            exact ⟨fun h => h.1, fun h => ⟨h, hrev ▸ he⟩⟩
          have hstate := state_eq_of_eqOn_revealed (ω ∩ revealFin (some (Q, T))) ω o k h
          exact finState_eq_some_iff.mpr
            ⟨hQ.trans (congrArg State.P hstate), hT.trans (congrArg State.A hstate)⟩

/-- At a reachable finite state, `E(A k, U k)` is disjoint from `R k`. -/
theorem disjoint_queried_revealFin_of_some {ω : Config V} {o : V} {k : ℕ} {Q T : Finset V}
    (h : finState ω o k = some (Q, T)) :
    Disjoint (queried ω o k) (revealFin (some (Q, T))) := by
  obtain ⟨hQ, -⟩ := finState_eq_some_iff.mp h
  rw [show revealFin (some (Q, T)) = revealed ω o k from by
    ext e
    simp only [revealed, revealFin, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, hve⟩
      exact ⟨v, hQ ▸ hv, hve⟩
    · rintro ⟨v, hv, hve⟩
      exact ⟨v, hQ ▸ hv, hve⟩]
  exact (disjoint_revealed_queried ω o k).symm

/-- **Direction 1's factorization at the BFS countable state.**  This is
`PercLib.Probability.AdaptedReveal.lintegral_adapted_prod` applied to
`finRevealData o k`.  The state is the pair `(P k, A k)` when both are finite and
`none` otherwise; the fresh set `S σ` must be a finite set of edges disjoint from
the revealed set of state `σ` (for `σ = none` this forces `S none = ∅`, since
`revealFin none = univ`). -/
theorem lintegral_bfs_adapted_prod (p : Sym2 V → unitInterval) (o : V) (k : ℕ)
    (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (S : FinState V → Finset (Sym2 V))
    (hS : ∀ σ, Disjoint ((S σ : Finset (Sym2 V)) : Set (Sym2 V)) (revealFin σ))
    (f : Sym2 V → Prop → ℝ≥0∞) :
    ∫⁻ ω, G ω * ∏ e ∈ S (finState ω o k), f e (e ∈ ω) ∂(prodBernoulli p) =
      ∑' σ : FinState V, (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
          * ∏ e ∈ S σ, ∫⁻ ω, f e (e ∈ ω) ∂(prodBernoulli p) :=
  lintegral_adapted_prod p (finRevealData o k) G H hH hG S hS f

/-- **The Bernoulli pgf form of the BFS factorization.** -/
theorem lintegral_bfs_adapted_pgf (p : Sym2 V → unitInterval) (o : V) (k : ℕ)
    (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (S : FinState V → Finset (Sym2 V))
    (hS : ∀ σ, Disjoint ((S σ : Finset (Sym2 V)) : Set (Sym2 V)) (revealFin σ))
    (t : ℝ≥0∞) :
    ∫⁻ ω, G ω * t ^ openCount (S (finState ω o k)) ω ∂(prodBernoulli p) =
      ∑' σ : FinState V, (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
          * ∏ e ∈ S σ, (t * (unitInterval.toNNReal (p e) : ℝ≥0∞)
              + (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞))) :=
  lintegral_adapted_pgf p (finRevealData o k) G H hH hG S hS t

/-- **The bounded Bernoulli pgf form at the BFS state**, the one-step estimate
consumed by the generation induction. -/
theorem lintegral_bfs_adapted_pgf_le (p : Sym2 V → unitInterval) (o : V) (k : ℕ)
    (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (S : FinState V → Finset (Sym2 V))
    (hS : ∀ σ, Disjoint ((S σ : Finset (Sym2 V)) : Set (Sym2 V)) (revealFin σ))
    (t : ℝ≥0∞) (B : FinState V → ℝ≥0∞)
    (hB : ∀ σ : FinState V, (∏ e ∈ S σ, (t * (unitInterval.toNNReal (p e) : ℝ≥0∞)
        + (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞)))) ≤ B σ) :
    ∫⁻ ω, G ω * t ^ openCount (S (finState ω o k)) ω ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V, (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p)) * B σ :=
  lintegral_adapted_pgf_le p (finRevealData o k) G H hH hG S hS t B hB

end PercLib.CriticalLRP.Exploration.BFS
