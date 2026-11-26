/-
Direction (C), member m2: audit extras for the cut-off domination chain.

What the migrated module leaves implicit, made explicit here:

* `A1` — for `r ≤ 1` the cut-off kernel `J_r` of Definition I.1.5 is *identically zero*
  (distinct lattice points have distance at least `1`), so the paper's quantifier `r < ∞`
  is covered: the interesting range is `r ≥ 1`, which is exactly the hypothesis of the
  migrated theorems.  `exists_cutoffCoefficient_domination` packages the result in the
  paper's own "for every `r` there is `ε = ε(r) > 0`" shape.
* `A2` — exact use of the diagonal hypothesis `K 0 = 0`.  At the loop `s(x,x)` the cut-off
  kernel is `0` and the uncut kernel is `K 0`, so
  - the *edge comparison* at the loop needs only `0 ≤ K 0`, not `K 0 = 0`
    (`cutoffSymKernel_loop_le_of_nonneg`, `cutoffSymKernel_le_scaled_of_nonneg`);
  - `0 ≤ K 0` is itself necessary: with `K 0 < 0` the loop comparison fails
    (`hK0nn_sharp`);
  - `K 0 = 0` is nevertheless the right hypothesis for the chain, because the uncut kernel
    of a Bernoulli edge law must satisfy `∀ e, 0 ≤ J e`, and that already fails at the loop
    when `K 0 < 0` (`not_forall_nonneg_kernelJ_of_K0_neg`); moreover `K 0 = 0` is exactly
    what makes `kernelJ = radialKernel` (the paper's factor `1(x ≠ y)`,
    `kernelJ_loop_eq`).
* `A3` — the coefficient `ε = K r / K 1`: `K 1 = 1` (the paper's normalisation) gives
  `ε = K r`; `ε < 1` (strict domination) holds exactly when `K r > 0`, and `ε = 1`
  (trivial domination) exactly when `K r = 0`.  `K 1 > 0` is what makes this a condition on
  `K r` alone.

No new definitions; no `sorry`, `admit`, `native_decide` or custom axioms.
-/
module

public import PercLib.CriticalLRP.CutoffDominated

/-! # Boundary conditions for the cutoff-domination chain -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP.CutoffDominatedAudit

open PercLib.CriticalLRP.FiniteVolume CutoffKernel CutoffLimit TreeExpansion
open PercLib.CriticalLRP.CutoffDominated

variable {d : ℕ} {K : ℝ → ℝ}

/-! ## A1. Below the cut-off radius the kernel vanishes identically -/

/-- For `r ≤ 1` the cut-off kernel is zero on **every** edge of `Sym2 (ℤ^d)`: distinct
lattice points are at distance `≥ 1 ≥ r`, and on the diagonal the kernel is `0` by
construction.  Hence in the paper's `r < ∞` there is nothing to prove for `r ≤ 1`. -/
theorem cutoffSymKernel_eq_zero_of_le_one (K : ℝ → ℝ) (d : ℕ) {r : ℝ} (hr : r ≤ 1)
    (e : Sym2 (Fin d → ℤ)) : cutoffSymKernel K d r e = 0 := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [cutoffSymKernel_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy]
      have hs : (1 : ℝ) ≤ ((linfNorm (x - y) : ℕ) : ℝ) := one_le_latticeDist hxy
      rcases le_or_gt ((linfNorm (x - y) : ℕ) : ℝ) r with hsr | hsr
      · have hEq : ((linfNorm (x - y) : ℕ) : ℝ) = r := le_antisymm hsr (le_trans hr hs)
        rw [cutoffProfile_of_le hsr, hEq, sub_self]
      · exact cutoffProfile_of_lt hsr

/-- In the trivial range `r ≤ 1` the cut-off kernel is dominated by `(1/2) J`. -/
theorem cutoffSymKernel_le_half_of_le_one (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    (d : ℕ) {r : ℝ} (hr : r ≤ 1) (e : Sym2 (Fin d → ℤ)) :
    cutoffSymKernel K d r e
      ≤ (1 - 1 / 2 : ℝ) * kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
          (profile_even K) e := by
  rw [cutoffSymKernel_eq_zero_of_le_one K d hr e]
  exact mul_nonneg (by norm_num) (uncutKernel_nonneg hKnn hK0 d e)

/-- **Definition I.1.5 in the paper's quantifier shape**, for *every* real `r` (not only
`r ≥ 1`): there is `ε = ε(r) ∈ (0,1]` with `J_r ≤ (1 − ε) J` on every edge.  For `r ≥ 1`
the coefficient is the paper's `ε = K r / K 1`; for `r ≤ 1` the kernel is zero (`A1`) and
any `ε ∈ (0,1]` works. -/
theorem exists_cutoffCoefficient_domination (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0) (hK1 : 0 < K 1)
    (hKr : ∀ r : ℝ, 1 ≤ r → 0 < K r) (r : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ e : Sym2 (Fin d → ℤ),
        cutoffSymKernel K d r e
          ≤ (1 - ε) * kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
              (profile_even K) e := by
  rcases le_or_gt 1 r with hr | hr
  · exact ⟨K r / K 1, div_pos (hKr r hr) hK1,
      (cutoffCoefficient_mem hK hr (hKr r hr) hK1).2.2,
      fun e => cutoffSymKernel_le_scaled hK hKnn hK0 hr (hKr r hr) hK1 e⟩
  · exact ⟨1 / 2, by norm_num, by norm_num,
      fun e => cutoffSymKernel_le_half_of_le_one hKnn hK0 d (le_of_lt hr) e⟩

/-! ## A2. The diagonal: exact use of `K 0 = 0` -/

/-- The uncut kernel at the loop `s(x,x)` is the profile at `0`, with no hypothesis. -/
theorem kernelJ_loop_eq (K : ℝ → ℝ) (d : ℕ) (x : Fin d → ℤ) :
    kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K) s(x, x) = K 0 := by
  change K ((linfNorm (x - x) : ℕ) : ℝ) = K 0
  rw [sub_self, show linfNorm (0 : Fin d → ℤ) = 0 from linfNorm_eq_zero_iff.mpr rfl]
  simp

/-- **At the loop the comparison needs only `0 ≤ K 0`**, not `K 0 = 0`: the cut-off kernel
vanishes there and the right-hand side is `(1 − K r / K 1) K 0` with a nonnegative factor. -/
theorem cutoffSymKernel_loop_le_of_nonneg (hK : AntitoneOn K (Set.Ioi 0)) (hK0nn : 0 ≤ K 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (x : Fin d → ℤ) :
    cutoffSymKernel K d r s(x, x)
      ≤ (1 - K r / K 1) * kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
          (profile_even K) s(x, x) := by
  rw [cutoffSymKernel_loop, kernelJ_loop_eq]
  exact mul_nonneg (cutoffCoefficient_nonneg hK hr hKr hK1) hK0nn

/-- **The edge comparison under the weaker hypothesis `0 ≤ K 0`**: the migrated
`cutoffSymKernel_le_scaled` assumes `K 0 = 0`, but its proof uses the diagonal value only
through nonnegativity. -/
theorem cutoffSymKernel_le_scaled_of_nonneg (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0nn : 0 ≤ K 0) {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r)
    (hK1 : 0 < K 1) (e : Sym2 (Fin d → ℤ)) :
    cutoffSymKernel K d r e
      ≤ (1 - K r / K 1) * kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
          (profile_even K) e := by
  induction e using Sym2.ind with
  | _ x y =>
    change cutoffSymKernel K d r s(x, y)
      ≤ (1 - K r / K 1) * K ((linfNorm (y - x) : ℕ) : ℝ)
    rw [show ((linfNorm (y - x) : ℕ) : ℝ) = latticeDist x y from by
      unfold latticeDist
      rw [show y - x = -(x - y) by abel, linfNorm_neg]]
    rw [cutoffSymKernel_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, hxy, latticeDist_self]
      exact mul_nonneg (cutoffCoefficient_nonneg hK hr hKr hK1) hK0nn
    · rw [ite_eq_right hxy]
      exact cutoffProfile_dominated hK hKnn (one_le_latticeDist hxy) hr hKr hK1

/-- **`0 ≤ K 0` is necessary** for the loop comparison: a profile with all other
hypotheses and `K 0 < 0` violates it at `r = 2`. -/
theorem hK0nn_sharp (d : ℕ) :
    ∃ K : ℝ → ℝ, AntitoneOn K (Set.Ioi 0) ∧ (∀ t, 0 < t → 0 ≤ K t) ∧ 0 < K 1 ∧
      (∀ r : ℝ, 1 ≤ r → 0 < K r) ∧ K 0 < 0 ∧
      ¬ ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
          cutoffSymKernel K d r e
            ≤ (1 - K r / K 1) * kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
                (profile_even K) e := by
  refine ⟨fun t => if t = 0 then -1 else Real.exp (-t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    dsimp only
    change (if b = 0 then (-1 : ℝ) else Real.exp (-b))
      ≤ (if a = 0 then -1 else Real.exp (-a))
    rw [ite_eq_right (ne_of_gt hb), ite_eq_right (ne_of_gt ha)]
    exact Real.exp_le_exp.mpr (by linarith)
  · intro t ht
    dsimp only
    rw [ite_eq_right (ne_of_gt ht)]
    exact (Real.exp_pos _).le
  · dsimp only
    rw [ite_eq_right (by norm_num : (1 : ℝ) ≠ 0)]
    exact Real.exp_pos _
  · intro r hr
    dsimp only
    rw [ite_eq_right (by linarith : r ≠ 0)]
    exact Real.exp_pos _
  · dsimp only
    rw [ite_eq_left rfl]
    norm_num
  · intro h
    have h2 := h 2 (s(0, 0) : Sym2 (Fin d → ℤ))
    have hl : cutoffSymKernel (fun t => if t = 0 then -1 else Real.exp (-t)) d 2
        (s(0, 0) : Sym2 (Fin d → ℤ)) = 0 := by
      simpa using cutoffSymKernel_loop (d := d)
        (fun t => if t = 0 then -1 else Real.exp (-t)) 2 (0 : Fin d → ℤ)
    rw [hl] at h2
    have hk : kernelJ (fun y : Fin d → ℤ =>
          (fun t => if t = 0 then -1 else Real.exp (-t)) ((linfNorm y : ℕ) : ℝ))
        (profile_even (fun t => if t = 0 then -1 else Real.exp (-t)))
        (s(0, 0) : Sym2 (Fin d → ℤ)) = -1 := by
      have h0 := kernelJ_loop_eq (d := d)
        (fun t => if t = 0 then -1 else Real.exp (-t)) 0
      simpa using h0
    rw [hk] at h2
    dsimp only at h2
    rw [ite_eq_right (by norm_num : (2 : ℝ) ≠ 0),
      ite_eq_right (by norm_num : (1 : ℝ) ≠ 0)] at h2
    have hpos : 0 < 1 - Real.exp (-2 : ℝ) / Real.exp (-1 : ℝ) := by
      have hlt : Real.exp (-2 : ℝ) / Real.exp (-1 : ℝ) < 1 := by
        rw [div_lt_one (Real.exp_pos (-1 : ℝ))]
        exact Real.exp_lt_exp.mpr (by norm_num)
      linarith
    nlinarith [h2, hpos]

/-- **Why `K 0 = 0` is the right hypothesis nevertheless**: the uncut kernel has to be a
nonnegative kernel (`∀ e, 0 ≤ J e` is the hypothesis of `bernoulliEdgeProb`), and this
already fails at the loop as soon as `K 0 < 0`.  So the diagonal hypothesis serves the law
construction, while `0 ≤ K 0` is all the inequality itself needs. -/
theorem not_forall_nonneg_kernelJ_of_K0_neg (h : K 0 < 0) (x : Fin d → ℤ) :
    ¬ ∀ e : Sym2 (Fin d → ℤ),
        0 ≤ kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K) e := by
  intro hnn
  have hloop := hnn s(x, x)
  rw [kernelJ_loop_eq] at hloop
  linarith

/-! ## A3. The coefficient: normalisation `K 1 = 1` and strictness -/

/-- **The normalisation `K 1 > 0` is not cosmetic.**  If `K 1 = 0`, Lean's division
convention `K r / 0 = 0` makes the coefficient identically `1`, so the strict statement
`1 − ε < 1` (i.e. `ε > 0`) fails for *every* profile with `K 1 = 0` however small `K r` is.
This is exactly why `cutoffCoefficient_mem` and the whole chain carry `0 < K 1`. -/
theorem cutoffCoefficient_lt_one_needs_K1 (h1 : K 1 = 0) (r : ℝ) :
    ¬ 1 - K r / K 1 < 1 := by
  rw [h1, div_zero, sub_zero]
  exact lt_irrefl 1

/-- A profile normalised by `K 1 = 1` (as the paper's `r ↦ r^{-(d+α)}` is: `1^{-(d+α)} = 1`)
has coefficient `ε(r) = K r`, i.e. `1 − ε = 1 − K r`.  The migrated
`modelProfile_coefficient` is the instance `K = modelProfile d α`. -/
theorem cutoffCoefficient_of_normalized (h1 : K 1 = 1) (r : ℝ) :
    1 - K r / K 1 = 1 - K r := by
  rw [h1, div_one]

/-- Strict domination (`1 − ε < 1`, i.e. `ε > 0`) holds exactly when `K r > 0`; so the
hypothesis `0 < K r` of `cutoffCoefficient_mem` is not a convenience but the sharp
condition under which the cut-off law sits at a strictly smaller parameter. -/
theorem cutoffCoefficient_lt_one_iff (hK1 : 0 < K 1) {r : ℝ} :
    1 - K r / K 1 < 1 ↔ 0 < K r := by
  rw [sub_lt_self_iff, div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, hneg⟩)
    · exact h
    · linarith
  · intro h
    exact Or.inl ⟨h, hK1⟩

/-- The trivial-domination case: the coefficient is `1` (no strict gain) exactly when
`K r = 0`.  This is the degenerate end of the family `ε(r) = K r / K 1`, and the reason the
migrated theorems carry `0 < K r`. -/
theorem cutoffCoefficient_eq_one_iff (hK1 : 0 < K 1) {r : ℝ} :
    1 - K r / K 1 = 1 ↔ K r = 0 := by
  constructor
  · intro h
    have hz : K r / K 1 = 0 := by linarith
    rcases (div_eq_zero_iff.mp hz) with h | h
    · exact h
    · exact absurd h (ne_of_gt hK1)
  · intro h
    rw [h, zero_div, sub_zero]

end PercLib.CriticalLRP.CutoffDominatedAudit
