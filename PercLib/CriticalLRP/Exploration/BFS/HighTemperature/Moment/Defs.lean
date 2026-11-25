/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# High-temperature BFS cluster moments

Accepted from independent submission `smwpdapl6` direction D2.
Generic independent edge percolation under a uniform finite-partial row-sum
bound; no source-critical or cutoff instantiation is asserted here.
-/
module

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The remaining-generation moment induction (part 1: bookkeeping)

Swarm `smwpdplm2` (member m2).  Definitions and bookkeeping for the induction

  `∫ G · λ^{N(k,n)} ≤ ∫ G · u_n^{|A k|}`,

where `N(k,n) = Σ_{j<n} |G_{k+j}|` is the number of vertices in the generations `k` to
`k+n-1`, `u_n` is the scalar envelope `u_{n+1} = e^{m (λ u_n - 1)}`, and `G` is a
nonnegative history function of the revealed block at step `k`.

Nothing here asserts a cluster bound; the induction itself is in `Induction.lean`.
-/
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.FiniteHorizon

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open Classical MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*} [Countable V]

/-! ### The remaining-generation cardinality -/

/-- `N o k n` is the total extended cardinality of the generations `k, k+1, …, k+n-1`:
the number of vertices discovered in the `n` exploration steps starting at step `k`. -/
def N (o : V) (k n : ℕ) (ω : Config V) : ℕ∞ :=
  ∑ j ∈ Finset.range n, (gen ω o (k + j)).encard

theorem N_zero (o : V) (k : ℕ) (ω : Config V) : N o k 0 ω = 0 := by
  simp [N]

/-- **The successor decomposition** `N(k,n+1) = |G_k| + N(k+1,n)`. -/
theorem N_succ (o : V) (k n : ℕ) (ω : Config V) :
    N o k (n + 1) ω = (gen ω o k).encard + N o (k + 1) n ω := by
  rw [N, N, Finset.sum_range_succ']
  have h0 : gen ω o (k + 0) = gen ω o k := by rw [Nat.add_zero]
  rw [h0, add_comm]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by rw [show k + (j + 1) = k + 1 + j from by omega])

theorem N_zero_left (o : V) (n : ℕ) (ω : Config V) :
    N o 0 n ω = ∑ j ∈ Finset.range n, (gen ω o j).encard :=
  Finset.sum_congr rfl (fun j _ => by rw [Nat.zero_add])

/-- The horizon cardinality is one plus the remaining-generation cardinality at `k = 0`. -/
theorem encard_horizon_eq_one_add_N (o : V) (n : ℕ) (ω : Config V) :
    (horizon ω o n).encard = 1 + N o 0 n ω := by
  rw [encard_horizon, N_zero_left]

/-! ### The frontier is a function of the revealed block -/

/-- The frontier at step `k` is determined by the revealed block at step `k`. -/
theorem A_hist_eq (o : V) (k : ℕ) (ω : Config V) : A (hist o k ω) o k = A ω o k := by
  cases h : finState ω o k with
  | none =>
      have hhist : hist o k ω = ω := by
        rw [hist, h]
        exact Set.inter_univ ω
      rw [hhist]
  | some QT =>
      obtain ⟨Q, T⟩ := QT
      have h' := finState_hist_eq o k ω
      rw [h] at h'
      rw [← (finState_eq_some_iff.mp h).2, ← (finState_eq_some_iff.mp h').2]

/-- The processed set at step `k` is determined by the revealed block at step `k`. -/
theorem P_hist_eq (o : V) (k : ℕ) (ω : Config V) : P (hist o k ω) o k = P ω o k := by
  cases h : finState ω o k with
  | none =>
      have hhist : hist o k ω = ω := by
        rw [hist, h]
        exact Set.inter_univ ω
      rw [hhist]
  | some QT =>
      obtain ⟨Q, T⟩ := QT
      have h' := finState_hist_eq o k ω
      rw [h] at h'
      rw [← (finState_eq_some_iff.mp h).1, ← (finState_eq_some_iff.mp h').1]

theorem measurable_encard_A (o : V) (k : ℕ) :
    Measurable fun ω : Config V => (A ω o k).encard := by
  refine measurable_encard.comp ?_
  rw [measurable_set_iff]
  intro y
  exact measurableSet_setOfPred.mp (measurableSet_mem_A o k y)

/-- `epow` of the frontier cardinality is a history function at step `k`. -/
theorem isHistFun_epow_encard_A (o : V) (k : ℕ) (lam : ℝ≥0∞) :
    IsHistFun o k (fun ω : Config V => epow lam ((A ω o k).encard)) :=
  ⟨fun h => epow lam ((A h o k).encard),
    (measurable_epow lam).comp (measurable_encard_A o k),
    fun ω => by
      show epow lam ((A ω o k).encard) = epow lam ((A (hist o k ω) o k).encard)
      rw [A_hist_eq]⟩

theorem IsHistFun.measurable {o : V} {k : ℕ} {G : Config V → ℝ≥0∞} (h : IsHistFun o k G) :
    Measurable G := by
  obtain ⟨H, hH, hEq⟩ := h
  rw [funext hEq]
  exact hH.comp (measurable_hist o k)

theorem IsHistFun.mul {o : V} {k : ℕ} {G G' : Config V → ℝ≥0∞}
    (h : IsHistFun o k G) (h' : IsHistFun o k G') :
    IsHistFun o k (fun ω => G ω * G' ω) := by
  obtain ⟨H, hH, hEq⟩ := h
  obtain ⟨H', hH', hEq'⟩ := h'
  refine ⟨fun hh => H hh * H' hh, hH.mul hH', fun ω => ?_⟩
  show G ω * G' ω = H (hist o k ω) * H' (hist o k ω)
  rw [hEq ω, hEq' ω]

/-- The image map `η ↦ ↑η` from subsets of a subtype to subsets of the ambient type is
measurable. -/
theorem measurable_image_subtype_val {ι : Type*} (S : Set ι) :
    Measurable fun η : Set S => (Subtype.val '' η : Set ι) := by
  rw [measurable_set_iff]
  intro e
  apply measurableSet_setOfPred.mp
  by_cases he : e ∈ S
  · have hset : {η : Set S | e ∈ Subtype.val '' η} = {η : Set S | (⟨e, he⟩ : S) ∈ η} := by
      ext η
      constructor
      · rintro ⟨x, hx, hxe⟩
        have hx' : x = ⟨e, he⟩ := Subtype.ext hxe
        rwa [hx'] at hx
      · intro h
        exact ⟨⟨e, he⟩, h, rfl⟩
    rw [hset]
    exact measurableSet_mem _
  · have hset : {η : Set S | e ∈ Subtype.val '' η} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro η hmem
      obtain ⟨x, _, hxe⟩ := hmem
      exact he (hxe ▸ x.2)
    rw [hset]
    exact MeasurableSet.empty

/-- The image of the revealed block is the history: `↑(blockRestrict S ω) = ω ∩ S`. -/
theorem image_blockRestrict (S : Set (Sym2 V)) (ω : Config V) :
    Subtype.val '' (blockRestrict S ω) = ω ∩ S := by
  rw [blockRestrict, Set.image_preimage_eq_inter_range, Subtype.range_val]

/-- **The per-fibre history data of a history function.**  A function of the revealed block
is, equivalently, a state-dependent function of the block restriction: the `hG` hypothesis
of `lintegral_bfs_adapted_pgf_le`. -/
theorem isHistFun_fibreData {o : V} {k : ℕ} {G : Config V → ℝ≥0∞} (h : IsHistFun o k G) :
    ∃ H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞,
      (∀ σ, Measurable (H σ)) ∧
        ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω) := by
  obtain ⟨Hh, hHh, hEq⟩ := h
  refine ⟨fun σ η => Hh (Subtype.val '' (η : Set ↑(revealFin σ))), fun σ => ?_, fun ω => ?_⟩
  · exact hHh.comp (measurable_image_subtype_val _)
  · rw [hEq ω]
    exact congrArg Hh (image_blockRestrict (revealFin (finState ω o k)) ω).symm

end PercLib.CriticalLRP.Exploration.BFS
