/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The critical parameter `β_c` of long-range percolation, with the paper's *literal*
definition, and its threshold structure.

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.1.2, p. 6:

  "we define the critical point `β_c` to be
   `β_c := inf{β ≥ 0 : an infinite cluster exists P_β-a.s.}`"

So `β_c` is the infimum of the set of `β ≥ 0` for which the event
`{ω : ∃ v, |K_v(ω)| = ∞}` has `P_β`-probability one.  Here `β : NNReal`, so the constraint
`β ≥ 0` is automatic, and `β_c` is `sInf` of that set.

Proved here, unconditionally (no `sorry`, no custom axioms):

* `criticalBetaSet_isUpperSet` — the set of `β` at which an infinite cluster exists a.s. is
  an up-set (stochastic monotonicity in `β`, `Marks.lean`);
* `criticalBeta_le_of_mem` — `β_c ≤ β` for every such `β`;
* `ne_one_of_lt_criticalBeta` — `β < β_c` implies `P_β(∃ infinite cluster) ≠ 1`;
* `infiniteClusterProb_eq_zero_of_lt_criticalBeta` — with Kolmogorov's zero–one law,
  `β < β_c` implies `P_β(∃ infinite cluster) = 0` (no infinite cluster a.s. below `β_c`);
* `mem_of_criticalBeta_lt` — if the percolation set is nonempty then `β > β_c` implies
  `P_β(∃ infinite cluster) = 1`;
* `zero_not_mem_criticalBetaSet` — `β = 0` does not percolate.

`β_c ∈ criticalBetaSet` (percolation *at* `β_c`) is deliberately **not** claimed: it is
equivalent to a discontinuity of the phase transition at `β_c`.  Continuity holds for
`0 < α < d` (Berger [22], quoted on p. 6) and fails for `d = α = 1` ([5],[41]); both are
external results, not formalized here.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.CountableProduct.Base
public import PercLib.CriticalLRP.CountableProduct.Marks
public import PercLib.CriticalLRP.CountableProduct.ZeroOne

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

section Critical

variable {V : Type*} [Countable V] {J : Sym2 V → ℝ} {hJ : ∀ e, 0 ≤ J e}

/-- The set of parameters at which an infinite cluster exists almost surely. -/
noncomputable def criticalBetaSet (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) : Set NNReal :=
  {β : NNReal | infiniteClusterProb J hJ β = 1}

/-- **The critical parameter** of §I.1.2:
`β_c := inf{β ≥ 0 : an infinite cluster exists P_β-a.s.}`. -/
noncomputable def criticalBeta (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) : NNReal :=
  sInf (criticalBetaSet J hJ)

theorem mem_criticalBetaSet_iff (β : NNReal) :
    β ∈ criticalBetaSet J hJ ↔ infiniteClusterProb J hJ β = 1 := Iff.rfl

theorem criticalBetaSet_bddBelow : BddBelow (criticalBetaSet J hJ) :=
  ⟨0, fun b _ => zero_le⟩

/-- The percolation set is an **up-set**: if an infinite cluster exists a.s. at `β`, it does
so at every larger `β` (stochastic monotonicity). -/
theorem criticalBetaSet_isUpperSet : IsUpperSet (criticalBetaSet J hJ) := by
  intro a b hab ha
  refine le_antisymm (infiniteClusterProb_le_one J hJ b) ?_
  rw [← ha]
  exact infiniteClusterProb_mono hJ hab

theorem criticalBeta_le_of_mem {β : NNReal} (h : β ∈ criticalBetaSet J hJ) :
    criticalBeta J hJ ≤ β :=
  csInf_le criticalBetaSet_bddBelow h

/-- Below `β_c` there is not a.s. percolation. -/
theorem ne_one_of_lt_criticalBeta {β : NNReal} (h : β < criticalBeta J hJ) :
    infiniteClusterProb J hJ β ≠ 1 := by
  intro h1
  exact absurd (criticalBeta_le_of_mem h1) (not_le.mpr h)

/-- **Below `β_c` there is no infinite cluster a.s.** — the zero–one law upgrades "not a.s.
percolation" to "a.s. no percolation". -/
theorem infiniteClusterProb_eq_zero_of_lt_criticalBeta {β : NNReal}
    (h : β < criticalBeta J hJ) : infiniteClusterProb J hJ β = 0 :=
  (percolationEventProb_zero_or_one J hJ β).resolve_right (ne_one_of_lt_criticalBeta h)

/-- **Above `β_c` there is an infinite cluster a.s.**, provided the percolation set is
nonempty (which is what `β_c < ∞` amounts to for the paper's kernels, Theorem I.1.6). -/
theorem mem_of_criticalBeta_lt (hne : (criticalBetaSet J hJ).Nonempty) {β : NNReal}
    (h : criticalBeta J hJ < β) : β ∈ criticalBetaSet J hJ := by
  obtain ⟨a, ha, hab⟩ := (csInf_lt_iff criticalBetaSet_bddBelow hne).mp h
  exact criticalBetaSet_isUpperSet (le_of_lt hab) ha

/-- If the percolation set is nonempty, the threshold description is complete away from
`β_c` itself. -/
theorem mem_criticalBetaSet_iff_of_nonempty (hne : (criticalBetaSet J hJ).Nonempty)
    {β : NNReal} :
    β ∈ criticalBetaSet J hJ ↔ criticalBeta J hJ ≤ β ∧
      (β = criticalBeta J hJ → infiniteClusterProb J hJ (criticalBeta J hJ) = 1) := by
  constructor
  · intro h
    exact ⟨criticalBeta_le_of_mem h, fun hb => hb ▸ h⟩
  · rintro ⟨h1, h2⟩
    rcases lt_or_eq_of_le h1 with h1' | h1'
    · exact mem_of_criticalBeta_lt hne h1'
    · rw [mem_criticalBetaSet_iff, ← h1']
      exact h2 h1'.symm

/-- `β = 0` does not percolate, so `0` is not in the percolation set. -/
theorem zero_not_mem_criticalBetaSet : (0 : NNReal) ∉ criticalBetaSet J hJ := by
  simp [criticalBetaSet, infiniteClusterProb_zero J hJ]

/-- The percolation set is nonempty iff some `β` percolates. -/
theorem criticalBetaSet_nonempty_iff :
    (criticalBetaSet J hJ).Nonempty ↔ ∃ β : NNReal, infiniteClusterProb J hJ β = 1 :=
  Iff.rfl

end Critical

/-! ## The paper's kernel as an instance

`V = Z^d` with the supremum norm and `J(x,y) = ‖x - y‖^{-d-α}` (Definition I.1.3 with
`δ ≡ 0`), so that the abstract law above is literally the paper's `P_β`.  Normalizations of
the norm and of `J` only rescale `β` (p. 7), so nothing is lost by this choice. -/

section Lattice

/-- `J(x,y) = ‖x - y‖^{-d-α}` on `Z^d` with the supremum norm, as a function of the
unordered pair. -/
noncomputable def lrKernel (d : ℕ) (α : ℝ) : Sym2 (Fin d → ℤ) → ℝ :=
  Sym2.lift ⟨fun x y => (‖x - y‖ : ℝ) ^ (-((d : ℝ) + α)), by
    intro x y
    show (‖x - y‖ : ℝ) ^ (-((d : ℝ) + α)) = (‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))
    have h : (‖x - y‖ : ℝ) = ‖y - x‖ := by rw [← norm_neg, neg_sub]
    rw [h]⟩

/-- The paper's kernel vanishes on the diagonal (`J(x,y) = 1(x ≠ y)J(‖x-y‖)`), so diagonal
pairs are never open: this is the `1(x ≠ y)` factor of Definition I.1.3. -/
theorem lrKernel_diag (d : ℕ) {α : ℝ} (hα : 0 < α) (x : Fin d → ℤ) :
    lrKernel d α s(x, x) = 0 := by
  simp only [lrKernel, Sym2.lift_mk, sub_self, norm_zero]
  refine Real.zero_rpow ?_
  have : (0 : ℝ) < (d : ℝ) + α := by positivity
  linarith

theorem lrKernel_nonneg (d : ℕ) (α : ℝ) (e : Sym2 (Fin d → ℤ)) : 0 ≤ lrKernel d α e := by
  obtain ⟨x, y, rfl⟩ := Sym2.mk_surjective e
  simp only [lrKernel, Sym2.lift_mk]
  exact Real.rpow_nonneg (norm_nonneg _) _

/-- The paper's law on `Z^d` with kernel `‖x-y‖^{-d-α}`. -/
noncomputable def latticeLongRangeMeasure (d : ℕ) (α : ℝ) (β : NNReal) :
    Measure (Config (Fin d → ℤ)) :=
  longRangeMeasure (lrKernel d α) (lrKernel_nonneg d α) β

instance (d : ℕ) (α : ℝ) (β : NNReal) :
    IsProbabilityMeasure (latticeLongRangeMeasure d α β) := by
  rw [latticeLongRangeMeasure]; infer_instance

/-! ## Non-vacuity: the complete kernel percolates -/

section Complete

variable {V : Type*} [Countable V] [Infinite V]

/-- Under the degenerate law with every edge open, there is an infinite cluster almost
surely.  (This is not of the form `bernoulliEdgeProb J hJ β` for finite `β`; it is a check
that `InInfiniteCluster` and the percolation event are not vacuous.) -/
theorem percolationEventProb_one :
    percolationEventProb (fun _ : Sym2 V => (1 : unitInterval)) = 1 := by
  rw [percolationEventProb, edgeMeasure_one]
  have h : (Set.univ : Config V) ∈ existsInfiniteClusterEvent V := by
    refine ⟨Classical.arbitrary V, ?_⟩
    exact inInfiniteCluster_univ _
  rw [Measure.dirac_apply_of_mem h]

end Complete

end Lattice

end PercLib.CriticalLRP
