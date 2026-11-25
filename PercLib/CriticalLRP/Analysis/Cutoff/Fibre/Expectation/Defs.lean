/-
Swarm `smwu10gjo`, member `m3`, direction A (expectation-level finite-truncation fibre assembly).

Definitions only: the explicit monotone cofinal sequence of finite vertex windows used to turn the
`Finset`-indexed supremum of the fibre truncations into a sequential truncation limit.
-/
module

public import Mathlib

/-!
# Monotone cofinal finite windows in a countable vertex type

The fibre truncations at `HEAD` are indexed by *all* finite vertex sets `A : Finset V`
(`PercLib.CriticalLRP.Orchestration.paperSum_eq_iSup_tsum_pairIncr`).  The monotone convergence
theorem for the Lebesgue integral in this Mathlib is stated for sequences (`lintegral_iSup`) or for
directed families over a countable index (`lintegral_iSup_directed`).  `Finset V` is countable, but
it is convenient to also have an explicit *sequence* of windows: given an injection `e : V → ℕ`
(supplied by `Encodable.encode`, hence by `Countable V`), `window e he k` is the finite set of
vertices of code at most `k`.

* `mem_window`, `monotone_window`;
* `exists_window_subset`: every finite set of vertices sits inside some window (cofinality);
* `iSup_window_eq`: consequently the supremum over the windows is the supremum over all finite sets,
  for any monotone family in a complete lattice;
* `tendsto_window`: the same cofinality in filter form.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

variable {V : Type*}

/-- The finite window `{v | e v ≤ k}` of an injective coding `e` of the vertex set. -/
noncomputable def window (e : V → ℕ) (he : Function.Injective e) (k : ℕ) : Finset V :=
  (Set.Finite.preimage (f := e) (s := Set.Iic k) (fun _ _ _ _ h => he h)
    (Set.finite_Iic k)).toFinset

theorem mem_window {e : V → ℕ} {he : Function.Injective e} {k : ℕ} {v : V} :
    v ∈ window e he k ↔ e v ≤ k := by
  rw [window, Set.Finite.mem_toFinset]
  simp

theorem window_subset_window {e : V → ℕ} {he : Function.Injective e} : Monotone (window e he) := by
  intro k l hkl v hv
  rw [mem_window] at hv ⊢
  exact hv.trans hkl

theorem exists_window_subset (e : V → ℕ) (he : Function.Injective e) (s : Finset V) :
    ∃ k, s ⊆ window e he k := by
  classical
  refine ⟨s.sup e, fun v hv => ?_⟩
  rw [mem_window]
  exact Finset.le_sup (f := e) hv

/-- The windows are cofinal in the finite subsets, so a monotone family has the same supremum. -/
theorem iSup_window_eq (e : V → ℕ) (he : Function.Injective e) {α : Type*} [CompleteLattice α]
    (f : Finset V → α) (hf : Monotone f) : ⨆ k, f (window e he k) = ⨆ s : Finset V, f s := by
  refine le_antisymm (iSup_le fun k => le_iSup f _) (iSup_le fun s => ?_)
  obtain ⟨k, hk⟩ := exists_window_subset e he s
  exact le_iSup_of_le k (hf hk)

/-- Filter form of `iSup_window_eq`: the window truncations converge to the full supremum. -/
theorem tendsto_window (e : V → ℕ) (he : Function.Injective e) {α : Type*} [CompleteLattice α]
    [TopologicalSpace α] [SupConvergenceClass α] (f : Finset V → α) (hf : Monotone f) :
    Filter.Tendsto (fun k => f (window e he k)) Filter.atTop (nhds (⨆ s : Finset V, f s)) := by
  rw [← iSup_window_eq e he f hf]
  exact tendsto_atTop_iSup (hf.comp (window_subset_window (he := he)))

end PercLib.CriticalLRP.Orchestration

/-! ## The canonical window sequence of a countable vertex type

`codeWindow V k` is the window of vertices whose canonical code (an injection `V → ℕ` supplied by
`Countable V`) is at most `k`, so that the cofinal-sequence statements below need no extra data
beyond `Countable V`. -/

namespace PercLib.CriticalLRP.Orchestration

/-- A canonical injection of a countable type into `ℕ`. -/
noncomputable def code (V : Type*) [Countable V] : V → ℕ :=
  Classical.choose (exists_injective_nat V)

theorem code_injective (V : Type*) [Countable V] : Function.Injective (code V) :=
  Classical.choose_spec (exists_injective_nat V)

/-- The canonical monotone cofinal sequence of finite vertex windows of a countable type. -/
noncomputable def codeWindow (V : Type*) [Countable V] (k : ℕ) : Finset V :=
  window (code V) (code_injective V) k

theorem mem_codeWindow {V : Type*} [Countable V] {k : ℕ} {v : V} :
    v ∈ codeWindow V k ↔ code V v ≤ k :=
  mem_window

theorem monotone_codeWindow (V : Type*) [Countable V] : Monotone (codeWindow V) :=
  window_subset_window (e := code V) (he := code_injective V)

theorem exists_codeWindow_subset (V : Type*) [Countable V] (s : Finset V) :
    ∃ k, s ⊆ codeWindow V k :=
  exists_window_subset _ (code_injective V) s

/-- The canonical windows are cofinal in the finite vertex sets. -/
theorem iSup_codeWindow_eq (V : Type*) [Countable V] {α : Type*} [CompleteLattice α]
    (f : Finset V → α) (hf : Monotone f) : ⨆ k, f (codeWindow V k) = ⨆ s : Finset V, f s :=
  iSup_window_eq _ (code_injective V) f hf

/-- Filter form of `iSup_codeWindow_eq`. -/
theorem tendsto_codeWindow (V : Type*) [Countable V] {α : Type*} [CompleteLattice α]
    [TopologicalSpace α] [SupConvergenceClass α] (f : Finset V → α) (hf : Monotone f) :
    Filter.Tendsto (fun k => f (codeWindow V k)) Filter.atTop (nhds (⨆ s : Finset V, f s)) :=
  tendsto_window _ (code_injective V) f hf

end PercLib.CriticalLRP.Orchestration
