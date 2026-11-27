/-
Ultramath swarm `smwziumdb`, member `m1`, direction `d7`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

# The `q = 0` atlas exponent ledger: sharpness, and the Case-3 consequence

Companion to `Defs.lean`; see there for the source references (Hutchcroft,
*Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.17 p. 45, Lemma I.4.18
p. 46, proof of Proposition I.4.15 Case 3 p. 47, printed pp. 42-47).

## Results

* `kpow_le_chi_pow` — the general exponent ceiling of the `ℓ`-fold kernel power,
  `kpow D.k ℓ u v ≤ χ ^ ℓ` for `ℓ ≥ 1`.  Together with one row sum per label and per off-path
  vertex this is exactly the arithmetic of the accepted atlas: a shape whose tree path has
  length `ℓ` sits at `χ ^ (7 - ℓ) * k ^ ℓ`, and the window total of every shape sits at `χ ^ 7`.
* `shapeTwo_const`, `shapeThreeA_const`, `shapeThreeB_const`, `shapeFour_const` — in the
  constant-kernel witness every one of the four shapes equals `n ^ 6` *exactly*.
* `shapeTwo_sharp`, `shapeThreeA_sharp`, `shapeThreeB_sharp`, `shapeFour_sharp` — the four
  accepted shape targets `χ⁵k²`, `χ⁴k³`, `χ⁴k³`, `χ³k⁴` are **attained with equality** on the
  witness.  The exponent ledger of the atlas is sharp shape by shape: no power of `χ` is wasted
  and none can be saved.
* `atlas_const`, `atlas_window_sum_const`, `atlas_le_sharp` — the atlas is `15 n ^ 6`, its
  window total over `Fin n` is `15 n ^ 7`, and the assembly `atlas_le` of the accepted packet is
  also an equality on the witness.  In particular the window ledger `χ ^ 7` is attained: no
  summation order or constant improvement inside the atlas can lower it.
* `no_chi_four_window_bound`, `driver_must_grow` — there is no constant `C` with
  `windowSum ≤ C * χ ^ 4` for all witness kernels; quantitatively, any bound of the shape
  `C χ⁴ D(n)` on the window total forces `D(n) ≥ (15 / C) χ³`, i.e. **every** kernel-level
  Case-3 consumer of the `q = 0` atlas must carry an effective driver at least a constant times
  `χ ^ 3`, and the `q = 0` route cannot be pushed to the vanishing driver scale
  `∇_{r^c} + r^{-c}` from `KernelData` alone.
* `case3_exponent_ledger`, `case3_residual_lower_bound` — the exponent arithmetic of that
  consequence in the source's Case-3 parametrisation: if `0 < α` and `d ≤ 3α` then
  `α ≤ 4α - d`, so the normalized `q = 0` residual `χ ^ 4 / |B_r|` is at least a constant times
  `r ^ α` and does not vanish.

All statements are about the accepted `QZeroAtlas` definitions only; nothing here introduces a
new hypothesis, and no `sorry`, `admit`, `native_decide` or custom axiom is used.  The exact
build command and the axiom audit are in `RESULTS.md`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroAtlasWitness.Defs

/-! # Sharpness of the atlas exponent ledger -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.QZeroAtlas

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The general exponent ceiling -/

/-- `1 ≤ χ`: the susceptibility dominates the diagonal entry `k a a = 1`. -/
theorem one_le_chi_of (D : KernelData V) (a : V) : 1 ≤ D.χ := by
  have h1 : D.k a a ≤ ∑' z, D.k a z := ENNReal.le_tsum a
  rw [D.diag] at h1
  exact le_trans h1 (D.row a)

/-- **The `ℓ`-fold kernel power is at most `χ ^ ℓ`** (`ℓ ≥ 1`).  This is the only estimate
behind every `χ`-power of the accepted atlas. -/
theorem kpow_le_chi_pow_aux (D : KernelData V) :
    ∀ (m : ℕ) (u v : V), kpow D.k (m + 1) u v ≤ D.χ ^ (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro u v
    rw [kpow_one, pow_one]
    exact (D.le_one u v).trans (one_le_chi_of D u)
  | succ m ih =>
    intro u v
    rw [kpow_succ]
    calc ∑' z, D.k u z * kpow D.k (m + 1) z v
        ≤ ∑' z, D.k u z * D.χ ^ (m + 1) :=
          ENNReal.tsum_le_tsum fun z => mul_le_mul_right (ih z v) _
      _ = (∑' z, D.k u z) * D.χ ^ (m + 1) := ENNReal.tsum_mul_right
      _ ≤ D.χ * D.χ ^ (m + 1) := mul_le_mul_left (D.row u) _
      _ = D.χ ^ (m + 1 + 1) := by rw [pow_succ]; ring

theorem kpow_le_chi_pow (D : KernelData V) (u v : V) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    kpow D.k ℓ u v ≤ D.χ ^ ℓ := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  exact kpow_le_chi_pow_aux D m u v

/-! ## The constant-kernel witness: powers -/

theorem kpow_two_constKernel (n : ℕ) (u v : Fin n) :
    kpow (constKernel n) 2 u v = (n : ℝ≥0∞) := by
  simp [kpow_two, constKernel]

theorem kpow_three_constKernel (n : ℕ) (u v : Fin n) :
    kpow (constKernel n) 3 u v = (n : ℝ≥0∞) ^ 2 := by
  simp [kpow_three, kpow_two, constKernel]; ring

theorem kpow_four_constKernel (n : ℕ) (u v : Fin n) :
    kpow (constKernel n) 4 u v = (n : ℝ≥0∞) ^ 3 := by
  simp [kpow_four, kpow_three, kpow_two, constKernel]; ring

/-! ## The four shapes on the witness -/

theorem shapeTwo_const (n : ℕ) (u v : Fin n) :
    shapeTwo (constKernelData n) u v = (n : ℝ≥0∞) ^ 6 := by
  simp [shapeTwo, constKernel]; ring

theorem shapeThreeA_const (n : ℕ) (u v : Fin n) :
    shapeThreeA (constKernelData n) u v = (n : ℝ≥0∞) ^ 6 := by
  simp [shapeThreeA, constKernel]; ring

theorem shapeThreeB_const (n : ℕ) (u v : Fin n) :
    shapeThreeB (constKernelData n) u v = (n : ℝ≥0∞) ^ 6 := by
  simp [shapeThreeB, constKernel]; ring

theorem shapeFour_const (n : ℕ) (u v : Fin n) :
    shapeFour (constKernelData n) u v = (n : ℝ≥0∞) ^ 6 := by
  simp [shapeFour, constKernel]; ring

/-! ## Sharpness of the four accepted shape targets

Each target has the form `shape ≤ χ ^ (7 - ℓ) * k ^ ℓ`; on the witness every one of them is an
equality.  Hence the four exponents of the accepted packet cannot be improved. -/

/-- `shapeTwo ≤ χ⁵ k²` is attained. -/
theorem shapeTwo_sharp (n : ℕ) (u v : Fin n) :
    shapeTwo (constKernelData n) u v
      = (constKernelData n).χ ^ 5 * kpow (constKernelData n).k 2 u v := by
  simp [shapeTwo, constKernel, kpow_two]; ring

/-- `shapeThreeA ≤ χ⁴ k³` is attained. -/
theorem shapeThreeA_sharp (n : ℕ) (u v : Fin n) :
    shapeThreeA (constKernelData n) u v
      = (constKernelData n).χ ^ 4 * kpow (constKernelData n).k 3 u v := by
  simp [shapeThreeA, constKernel, kpow_three, kpow_two]; ring

/-- `shapeThreeB ≤ χ⁴ k³` is attained. -/
theorem shapeThreeB_sharp (n : ℕ) (u v : Fin n) :
    shapeThreeB (constKernelData n) u v
      = (constKernelData n).χ ^ 4 * kpow (constKernelData n).k 3 u v := by
  simp [shapeThreeB, constKernel, kpow_three, kpow_two]; ring

/-- `shapeFour ≤ χ³ k⁴` is attained. -/
theorem shapeFour_sharp (n : ℕ) (u v : Fin n) :
    shapeFour (constKernelData n) u v
      = (constKernelData n).χ ^ 3 * kpow (constKernelData n).k 4 u v := by
  simp [shapeFour, constKernel, kpow_four, kpow_three, kpow_two]; ring

/-! ## The atlas and its window total -/

theorem atlas_const (n : ℕ) (u v : Fin n) :
    atlas (constKernelData n) u v = 15 * (n : ℝ≥0∞) ^ 6 := by
  simp [atlas, shapeTwo, shapeThreeA, shapeThreeB, shapeFour, constKernel]; ring

/-- **The window ledger is attained**: the atlas window total over the whole witness space is
`15 χ ^ 7`.  (The `q = 0`, `p = 3` atlas has `3 + 3 + 3 + 6 = 15` trees and `7` edges each.) -/
theorem atlas_window_sum_const (n : ℕ) (u : Fin n) :
    (∑ y : Fin n, atlas (constKernelData n) u y) = 15 * (n : ℝ≥0∞) ^ 7 := by
  have h : ∀ y : Fin n, atlas (constKernelData n) u y = 15 * (n : ℝ≥0∞) ^ 6 := atlas_const n u
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The assembly step of the accepted packet is also an equality on the witness: the three-term
weight `3χ⁵k² + 6χ⁴k³ + 6χ³k⁴` equals the atlas. -/
theorem atlas_le_sharp (n : ℕ) (u v : Fin n) :
    atlas (constKernelData n) u v
      = 3 * ((constKernelData n).χ ^ 5 * kpow (constKernelData n).k 2 u v)
        + 6 * ((constKernelData n).χ ^ 4 * kpow (constKernelData n).k 3 u v)
        + 6 * ((constKernelData n).χ ^ 3 * kpow (constKernelData n).k 4 u v) := by
  simp only [constKernelData_k, constKernelData_chi]
  rw [atlas_const, kpow_two_constKernel, kpow_three_constKernel, kpow_four_constKernel]
  ring

/-- The ledger's factorization: the window total is `χ ^ 4` times the *effective driver*
`15 χ ^ 3`. -/
theorem window_ledger_factor (n : ℕ) :
    15 * (n : ℝ≥0∞) ^ 7 = (n : ℝ≥0∞) ^ 4 * (15 * (n : ℝ≥0∞) ^ 3) := by ring

/-! ## The negative conclusion: no `χ ^ 4` window bound

The accepted atlas gives `windowSum = 15 χ ^ 7 = χ ^ 4 * (15 χ ^ 3)`.  The Case-3 numerator
consumes the window total in the normalized form `windowSum / (|B_r| χ χ ^ 2)`, so this ledger
produces the residual driver `15 χ ^ 3 / |B_r|`, which does not vanish in Case 3.  The two
theorems below record that this is a property of the atlas, not of a particular reading of it. -/

/-- No constant `C` bounds the atlas window total by `C * χ ^ 4` uniformly over the witness. -/
theorem no_chi_four_window_bound :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → 15 * (n : ℝ) ^ 7 ≤ C * (n : ℝ) ^ 4 := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn, hbig⟩ : ∃ n : ℕ, 1 ≤ n ∧ C < 15 * (n : ℝ) ^ 3 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max C 1)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans (le_max_right _ _) hn.le
    have hClt : C < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    refine ⟨n, by exact_mod_cast hn1, ?_⟩
    nlinarith [hn1, hClt,
      mul_pos (by linarith : (0:ℝ) < (n:ℝ)) (by linarith : (0:ℝ) < (n:ℝ))]
  have h := hC n hn
  have h4 : (0:ℝ) < (n : ℝ) ^ 4 := by positivity
  nlinarith [h, hbig, h4]

/-- **The driver must grow like `χ ^ 3`.**  If the atlas window total is bounded by
`C χ ^ 4 D(n)` on the witness family, then `D(n) ≥ (15 / C) χ ^ 3`: the effective driver of the
`q = 0` route is bounded below by a constant multiple of `χ ^ 3` and cannot be a vanishing
quantity. -/
theorem driver_must_grow (C : ℝ) (hC : 0 < C) (D : ℕ → ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → 15 * (n : ℝ) ^ 7 ≤ C * (n : ℝ) ^ 4 * D n) :
    ∀ n : ℕ, 1 ≤ n → (15 / C) * (n : ℝ) ^ 3 ≤ D n := by
  intro n hn
  have hn1 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h4 : (0:ℝ) < (n : ℝ) ^ 4 := by positivity
  have h' : 15 * (n : ℝ) ^ 3 ≤ C * D n := by
    have h3 : (15 * (n : ℝ) ^ 3) * (n : ℝ) ^ 4 ≤ (C * D n) * (n : ℝ) ^ 4 := by
      calc (15 * (n : ℝ) ^ 3) * (n : ℝ) ^ 4 = 15 * (n : ℝ) ^ 7 := by ring
        _ ≤ C * (n : ℝ) ^ 4 * D n := h n hn
        _ = (C * D n) * (n : ℝ) ^ 4 := by ring
    exact le_of_mul_le_mul_right h3 h4
  have hrew : (15 / C) * (n : ℝ) ^ 3 = (15 * (n : ℝ) ^ 3) / C := by ring
  rw [hrew, div_le_iff₀ hC]
  have hcomm : C * D n = D n * C := by ring
  linarith [h', hcomm]

/-! ## The exponent arithmetic in the source's Case-3 parametrisation

In Case 3 the susceptibility and the ball behave as `χ ≍ r ^ α`, `|B_r| ≍ r ^ d` with
`d ≤ 3α`.  The normalized `q = 0` residual delivered by the atlas ledger is `χ ^ 4 / |B_r|`, of
order `r ^ (4α - d)`; the next theorem is exactly why it cannot vanish there. -/

theorem case3_exponent_ledger {α d : ℝ} (_hα : 0 < α) (hd : d ≤ 3 * α) :
    α ≤ 4 * α - d := by linarith

/-- The same statement as a lower bound for `r ^ (4α - d)` at `r ≥ 1`: the `q = 0` residual is
at least `r ^ α`. -/
theorem case3_residual_lower_bound {α d r : ℝ} (_hα : 0 < α) (hd : d ≤ 3 * α) (hr : 1 ≤ r) :
    r ^ α ≤ r ^ (4 * α - d) := by
  refine Real.rpow_le_rpow_of_exponent_le hr (by linarith)

/-! ## The `ℓ = 2` class alone forces the driver

The `q = 0` atlas at `p = 3` has three tree classes in which the `x - y` tree path has length
`ℓ = 2`.  The next two theorems isolate them: the `ℓ = 2` window total alone is `3 χ ^ 7`, so it
*by itself* forces an effective driver of order `χ ^ 3`.  This is the exact quantitative form of
the obstruction that blocks the `q = 0` route: the `p = 2`, `q = 1` route of Lemma I.4.17 has
`ℓ ∈ {3, 4}` only (the marked path of the printed proof forces `ℓ ≥ 3`), so it never sees this
class. -/

/-- The `ℓ = 2` shape window total is exactly `χ ^ 7` on the witness. -/
theorem shapeTwo_window_sum_const (n : ℕ) (u : Fin n) :
    (∑ y : Fin n, shapeTwo (constKernelData n) u y) = (n : ℝ≥0∞) ^ 7 := by
  have h : ∀ y : Fin n, shapeTwo (constKernelData n) u y = (n : ℝ≥0∞) ^ 6 := shapeTwo_const n u
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The multiplicity three of the `ℓ = 2` class against the ledger `χ ^ 7`:
`3 χ ^ 7 = χ ^ 4 * (3 χ ^ 3)`, i.e. the `ℓ = 2` class alone demands the driver `3 χ ^ 3`. -/
theorem ellTwo_window_forces_chi_cube (n : ℕ) (u : Fin n) :
    3 * (∑ y : Fin n, shapeTwo (constKernelData n) u y)
      = (n : ℝ≥0∞) ^ 4 * (3 * (n : ℝ≥0∞) ^ 3) := by
  rw [shapeTwo_window_sum_const]; ring

/-- **The `ℓ = 2` class alone forces the driver to grow like `χ ^ 3`.**  If the `ℓ = 2` shape
window total is bounded by `C χ ^ 4 D(n)` on the witness family, then `D(n) ≥ (3 / C) χ ^ 3`. -/
theorem ellTwo_driver_must_grow (C : ℝ) (hC : 0 < C) (D : ℕ → ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → 3 * (n : ℝ) ^ 7 ≤ C * (n : ℝ) ^ 4 * D n) :
    ∀ n : ℕ, 1 ≤ n → (3 / C) * (n : ℝ) ^ 3 ≤ D n := by
  intro n hn
  have hn1 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h4 : (0:ℝ) < (n : ℝ) ^ 4 := by positivity
  have h' : 3 * (n : ℝ) ^ 3 ≤ C * D n := by
    have h3 : (3 * (n : ℝ) ^ 3) * (n : ℝ) ^ 4 ≤ (C * D n) * (n : ℝ) ^ 4 := by
      calc (3 * (n : ℝ) ^ 3) * (n : ℝ) ^ 4 = 3 * (n : ℝ) ^ 7 := by ring
        _ ≤ C * (n : ℝ) ^ 4 * D n := h n hn
        _ = (C * D n) * (n : ℝ) ^ 4 := by ring
    exact le_of_mul_le_mul_right h3 h4
  have hrew : (3 / C) * (n : ℝ) ^ 3 = (3 * (n : ℝ) ^ 3) / C := by ring
  rw [hrew, div_le_iff₀ hC]
  have hcomm : C * D n = D n * C := by ring
  linarith [h', hcomm]

/-! ## The general window ceiling: the same ledger without a witness

The witness of the previous section attains the window ledger `15 χ ^ 7`.  This section proves
that `15 χ ^ 7` is also a *ceiling* for arbitrary `KernelData`, so the witness is extremal rather
than a pathology: the negative conclusion above is a statement about the atlas itself.

The only input is the content of the accepted packet's residual, i.e. the four shape evaluations
in the per-vertex form `shape ≤ χ ^ (7 - ℓ) * k ^ ℓ`.  (`master` production proves them from
`peel_labels` and the chain identities; they are carried as hypotheses here so that this file
stays independent of that development.)
-/

/-- The `ℓ`-fold power has total mass at most `χ ^ ℓ`: this is the window analogue of
`kpow_le_chi_pow`, and the reason every shape contributes `χ ^ 7` to the window. -/
theorem tsum_kpow_le (D : KernelData V) :
    ∀ (m : ℕ) (v : V), (∑' y, kpow D.k (m + 1) v y) ≤ D.χ ^ (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro v
    simpa [kpow_one] using D.row v
  | succ m ih =>
    intro v
    have step : ∀ y : V, kpow D.k (m + 1 + 1) v y
        = ∑' z, D.k v z * kpow D.k (m + 1) z y := fun y =>
      kpow_succ D.k (m + 1) v y
    calc ∑' y, kpow D.k (m + 1 + 1) v y
        = ∑' y, ∑' z, D.k v z * kpow D.k (m + 1) z y := tsum_congr step
      _ = ∑' z, ∑' y, D.k v z * kpow D.k (m + 1) z y := ENNReal.tsum_comm
      _ = ∑' z, D.k v z * (∑' y, kpow D.k (m + 1) z y) :=
            tsum_congr fun z => ENNReal.tsum_mul_left
      _ ≤ ∑' z, D.k v z * D.χ ^ (m + 1) :=
            ENNReal.tsum_le_tsum fun z => mul_le_mul_right (ih z) _
      _ = (∑' z, D.k v z) * D.χ ^ (m + 1) := ENNReal.tsum_mul_right
      _ ≤ D.χ * D.χ ^ (m + 1) := mul_le_mul_left (D.row v) _
      _ = D.χ ^ (m + 1 + 1) := by rw [pow_succ]; ring

theorem tsum_shapeTwo_le (D : KernelData V) (v : V)
    (h2 : ∀ y : V, shapeTwo D v y ≤ D.χ ^ 5 * kpow D.k 2 v y) :
    (∑' y, shapeTwo D v y) ≤ D.χ ^ 7 := by
  calc ∑' y, shapeTwo D v y
      ≤ ∑' y, D.χ ^ 5 * kpow D.k 2 v y := ENNReal.tsum_le_tsum h2
    _ = D.χ ^ 5 * (∑' y, kpow D.k 2 v y) := ENNReal.tsum_mul_left
    _ ≤ D.χ ^ 5 * D.χ ^ (1 + 1) := mul_le_mul_right (tsum_kpow_le D 1 v) _
    _ = D.χ ^ 7 := by rw [← pow_add]

theorem tsum_shapeThreeA_le (D : KernelData V) (v : V)
    (h3 : ∀ y : V, shapeThreeA D v y ≤ D.χ ^ 4 * kpow D.k 3 v y) :
    (∑' y, shapeThreeA D v y) ≤ D.χ ^ 7 := by
  calc ∑' y, shapeThreeA D v y
      ≤ ∑' y, D.χ ^ 4 * kpow D.k 3 v y := ENNReal.tsum_le_tsum h3
    _ = D.χ ^ 4 * (∑' y, kpow D.k 3 v y) := ENNReal.tsum_mul_left
    _ ≤ D.χ ^ 4 * D.χ ^ (2 + 1) := mul_le_mul_right (tsum_kpow_le D 2 v) _
    _ = D.χ ^ 7 := by rw [← pow_add]

theorem tsum_shapeThreeB_le (D : KernelData V) (v : V)
    (h3 : ∀ y : V, shapeThreeB D v y ≤ D.χ ^ 4 * kpow D.k 3 v y) :
    (∑' y, shapeThreeB D v y) ≤ D.χ ^ 7 := by
  calc ∑' y, shapeThreeB D v y
      ≤ ∑' y, D.χ ^ 4 * kpow D.k 3 v y := ENNReal.tsum_le_tsum h3
    _ = D.χ ^ 4 * (∑' y, kpow D.k 3 v y) := ENNReal.tsum_mul_left
    _ ≤ D.χ ^ 4 * D.χ ^ (2 + 1) := mul_le_mul_right (tsum_kpow_le D 2 v) _
    _ = D.χ ^ 7 := by rw [← pow_add]

theorem tsum_shapeFour_le (D : KernelData V) (v : V)
    (h4 : ∀ y : V, shapeFour D v y ≤ D.χ ^ 3 * kpow D.k 4 v y) :
    (∑' y, shapeFour D v y) ≤ D.χ ^ 7 := by
  calc ∑' y, shapeFour D v y
      ≤ ∑' y, D.χ ^ 3 * kpow D.k 4 v y := ENNReal.tsum_le_tsum h4
    _ = D.χ ^ 3 * (∑' y, kpow D.k 4 v y) := ENNReal.tsum_mul_left
    _ ≤ D.χ ^ 3 * D.χ ^ (3 + 1) := mul_le_mul_right (tsum_kpow_le D 3 v) _
    _ = D.χ ^ 7 := by rw [← pow_add]

/-- **The general window ceiling.**  Given the four shape evaluations, the atlas window total
over the whole vertex set is at most `15 χ ^ 7` for every `KernelData`.  Together with
`atlas_window_sum_const` this pins the ledger exactly: ceiling `15 χ ^ 7`, attained. -/
theorem tsum_atlas_le (D : KernelData V) (v : V)
    (h2 : ∀ y : V, shapeTwo D v y ≤ D.χ ^ 5 * kpow D.k 2 v y)
    (h3A : ∀ y : V, shapeThreeA D v y ≤ D.χ ^ 4 * kpow D.k 3 v y)
    (h3B : ∀ y : V, shapeThreeB D v y ≤ D.χ ^ 4 * kpow D.k 3 v y)
    (h4 : ∀ y : V, shapeFour D v y ≤ D.χ ^ 3 * kpow D.k 4 v y) :
    (∑' y, atlas D v y) ≤ 15 * D.χ ^ 7 := by
  have hA := tsum_shapeTwo_le D v h2
  have hB := tsum_shapeThreeA_le D v h3A
  have hC := tsum_shapeThreeB_le D v h3B
  have hD := tsum_shapeFour_le D v h4
  calc ∑' y, atlas D v y
      = ∑' y, (3 * shapeTwo D v y + 3 * shapeThreeA D v y
          + 3 * shapeThreeB D v y + 6 * shapeFour D v y) := rfl
    _ = 3 * (∑' y, shapeTwo D v y) + 3 * (∑' y, shapeThreeA D v y)
          + 3 * (∑' y, shapeThreeB D v y) + 6 * (∑' y, shapeFour D v y) := by
        simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ 3 * D.χ ^ 7 + 3 * D.χ ^ 7 + 3 * D.χ ^ 7 + 6 * D.χ ^ 7 := by gcongr
    _ = 15 * D.χ ^ 7 := by ring

end PercLib.CriticalLRP.QZeroAtlas




set_option linter.hashCommand false in
-- Audit: only the three standard axioms.
#print axioms PercLib.CriticalLRP.QZeroAtlas.one_le_chi_of
#print axioms PercLib.CriticalLRP.QZeroAtlas.kpow_le_chi_pow
#print axioms PercLib.CriticalLRP.QZeroAtlas.shapeTwo_sharp
#print axioms PercLib.CriticalLRP.QZeroAtlas.shapeThreeA_sharp
#print axioms PercLib.CriticalLRP.QZeroAtlas.shapeThreeB_sharp
#print axioms PercLib.CriticalLRP.QZeroAtlas.shapeFour_sharp
#print axioms PercLib.CriticalLRP.QZeroAtlas.atlas_window_sum_const
#print axioms PercLib.CriticalLRP.QZeroAtlas.atlas_le_sharp
#print axioms PercLib.CriticalLRP.QZeroAtlas.no_chi_four_window_bound
#print axioms PercLib.CriticalLRP.QZeroAtlas.driver_must_grow
#print axioms PercLib.CriticalLRP.QZeroAtlas.shapeTwo_window_sum_const
#print axioms PercLib.CriticalLRP.QZeroAtlas.ellTwo_window_forces_chi_cube
#print axioms PercLib.CriticalLRP.QZeroAtlas.ellTwo_driver_must_grow
#print axioms PercLib.CriticalLRP.QZeroAtlas.tsum_kpow_le
#print axioms PercLib.CriticalLRP.QZeroAtlas.tsum_atlas_le
#print axioms PercLib.CriticalLRP.QZeroAtlas.case3_residual_lower_bound
