/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m2/KpowSum.lean ; imports migrated;
auxiliary definitions and probability instances are collected in `Defs.lean`.
-/

/-
Composition and row/column sums for the infinite matrix powers of the connection kernel.

Production (`PercLib/CriticalLRP/Analysis/KernelPower/Defs.lean`) defines the `ℝ≥0∞`-valued
`Kpow K n x y` by iterated `tsum`, and `Main.lean`/`Model.lean` prove diagonal maximality for
it.  What Lemma I.4.18 still needs from the matrix power is the calculus of its sums:

* `Kpow_add` : `Kpow K (m+n) x y = ∑' u, Kpow K m x u * Kpow K n u y` — the source's
  `T^ℓ(0,0) = ∑_y ∇(0,y) T^{ℓ-3}(y,0)`, which is the case `m = 3`, `∇ = T³`;
* `Kpow_rowSum` / `Kpow_colSum` : if every row (resp. column) of `K` sums to `χ`, then every
  row (resp. column) of `Kpow K n` sums to `χ^n` — the source's `∑_y T^n(y,0) = (E|K|)^n`;
* `Kpow_succ_le_pow` : `Kpow K (n+1) x y ≤ χ^n` for `K ≤ 1` — the source's
  `T^{ℓ-3}(y,0) ≤ χ^{ℓ-4}`;
* `Kpow_comm` : a symmetric kernel has symmetric powers.

Everything is stated for `ℝ≥0∞`, where no summability side conditions are needed.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Monotone
public import PercLib.CriticalLRP.Analysis.KernelPower.Main

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.KernelPower

variable {V : Type*}

theorem deltaE_of_ne' {x y : V} (h : x ≠ y) : deltaE x y = 0 := by
  classical simp [deltaE, h]

theorem deltaE_self' (x : V) : deltaE x x = 1 := by classical simp [deltaE]

/-- **Composition of infinite matrix powers.** -/
theorem Kpow_add (K : V → V → ℝ≥0∞) (m n : ℕ) (x y : V) :
    Kpow K (m + n) x y = ∑' u, Kpow K m x u * Kpow K n u y := by
  induction n generalizing y with
  | zero =>
    rw [Nat.add_zero]
    show Kpow K m x y = ∑' u, Kpow K m x u * deltaE u y
    rw [tsum_eq_single (f := fun u => Kpow K m x u * deltaE u y) y
      (fun b hb => by rw [deltaE_of_ne' hb, mul_zero])]
    rw [deltaE_self', mul_one]
  | succ n ih =>
    rw [Nat.add_succ]
    show Kpow K (m + n + 1) x y = ∑' u, Kpow K m x u * Kpow K (n + 1) u y
    rw [Kpow_succ]
    have h1 : ∀ v : V, Kpow K (m + n) x v = ∑' u, Kpow K m x u * Kpow K n u v := fun v => ih v
    simp only [h1]
    have h2 : ∀ v : V, (∑' u, Kpow K m x u * Kpow K n u v) * K v y
        = ∑' u, (Kpow K m x u * Kpow K n u v) * K v y := fun v =>
      (ENNReal.tsum_mul_right).symm
    simp only [h2]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun u => ?_
    rw [Kpow_succ, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun v => mul_assoc _ _ _

/-- If every row of `K` has mass `χ`, every row of `Kpow K n` has mass `χ^n`. -/
theorem Kpow_rowSum (K : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (hrow : ∀ x, ∑' y, K x y = χ)
    (n : ℕ) (x : V) : ∑' y, Kpow K n x y = χ ^ n := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero]
    show ∑' y, deltaE x y = (1 : ℝ≥0∞)
    rw [tsum_eq_single (f := fun y => deltaE x y) x
      (fun b hb => deltaE_of_ne' (Ne.symm hb))]
    exact deltaE_self' x
  | succ n ih =>
    show ∑' y, (∑' u, Kpow K n x u * K u y) = χ ^ (n + 1)
    rw [ENNReal.tsum_comm (f := fun y u => Kpow K n x u * K u y)]
    have h1 : ∀ u : V, (∑' y, Kpow K n x u * K u y) = Kpow K n x u * χ := fun u => by
      rw [ENNReal.tsum_mul_left, hrow u]
    simp only [h1]
    rw [ENNReal.tsum_mul_right, ih x, pow_succ]

/-- If every column of `K` has mass `χ`, every column of `Kpow K n` has mass `χ^n`. -/
theorem Kpow_colSum (K : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (hcol : ∀ y, ∑' x, K x y = χ)
    (n : ℕ) (y : V) : ∑' x, Kpow K n x y = χ ^ n := by
  induction n generalizing y with
  | zero =>
    rw [pow_zero]
    show ∑' x, deltaE x y = (1 : ℝ≥0∞)
    rw [tsum_eq_single (f := fun x => deltaE x y) y (fun b hb => deltaE_of_ne' hb)]
    exact deltaE_self' y
  | succ n ih =>
    show ∑' x, (∑' u, Kpow K n x u * K u y) = χ ^ (n + 1)
    rw [ENNReal.tsum_comm (f := fun x u => Kpow K n x u * K u y)]
    have h1 : ∀ u : V, (∑' x, Kpow K n x u * K u y) = χ ^ n * K u y := fun u => by
      rw [ENNReal.tsum_mul_right, ih u]
    simp only [h1]
    rw [ENNReal.tsum_mul_left, hcol y, pow_succ]

/-- The source's `T^{ℓ-3}(y,0) ≤ χ^{ℓ-4}`: with `K ≤ 1` and rows summing to `χ`, every entry
of the `(n+1)`-fold power is at most `χ^n`. -/
theorem Kpow_succ_le_pow (K : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (hrow : ∀ x, ∑' y, K x y = χ)
    (hK1 : ∀ a b, K a b ≤ 1) (n : ℕ) (x y : V) : Kpow K (n + 1) x y ≤ χ ^ n := by
  induction n generalizing x y with
  | zero =>
    rw [pow_zero, Kpow_one]
    exact hK1 x y
  | succ n ih =>
    have hleft : Kpow K (n + 1 + 1) x y = ∑' u, K x u * Kpow K (n + 1) u y := by
      have h := Kpow_add K 1 (n + 1) x y
      rw [Nat.one_add] at h
      simpa only [Kpow_one] using h
    rw [hleft]
    calc ∑' u, K x u * Kpow K (n + 1) u y
        ≤ ∑' u, K x u * χ ^ n := ENNReal.tsum_le_tsum fun u =>
          mul_le_mul' le_rfl (ih u y)
      _ = χ * χ ^ n := by rw [ENNReal.tsum_mul_right, hrow x]
      _ = χ ^ (n + 1) := (pow_succ' χ n).symm

/-- For a symmetric kernel with constant row sums, the powers also have constant column sums:
the source's `∑_y T^n(y,0) = (E|K|)^n`. -/
theorem Kpow_colSum_of_symm (K : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (hrow : ∀ x, ∑' y, K x y = χ)
    (hK : ∀ a b, K a b = K b a) (n : ℕ) (y : V) : ∑' x, Kpow K n x y = χ ^ n :=
  Kpow_colSum K χ (fun y => by
    rw [← hrow y]
    exact tsum_congr fun x => hK x y) n y

end PercLib.CriticalLRP.KernelPower

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

theorem cutKpow_row (r : ℝ) :
    ∀ y : M.V, ∑' z, M.cutTwoPointE r y z = M.cutMassAt r 0 := fun y => by
  rw [M.tsum_cutTwoPointE_eq_cutMassAt r y, M.cutMassAt_eq_zero r y]

/-- **All-n row sums at the cutoff law**: `∑_y T^n_{β_c,r}(x,y) = χ^n`. -/
theorem cutKpow_rowSum (r : ℝ) (n : ℕ) (x : M.V) :
    ∑' y, KernelPower.Kpow (M.cutTwoPointE r) n x y = (M.cutMassAt r 0) ^ n :=
  KernelPower.Kpow_rowSum _ _ (M.cutKpow_row r) n x

/-- **All-n column sums at the cutoff law**: the source's `∑_y T^n_{β_c,r}(y,0) = χ^n`. -/
theorem cutKpow_colSum (r : ℝ) (n : ℕ) (y : M.V) :
    ∑' x, KernelPower.Kpow (M.cutTwoPointE r) n x y = (M.cutMassAt r 0) ^ n :=
  KernelPower.Kpow_colSum_of_symm _ _ (M.cutKpow_row r)
    (fun a b => M.cutTwoPointE_comm r a b) n y

/-- **The source's `T^{ℓ-3}(y,0) ≤ χ^{ℓ-4}`**, as a bound on the entries of the power. -/
theorem cutKpow_entry (r : ℝ) (n : ℕ) (x y : M.V) :
    KernelPower.Kpow (M.cutTwoPointE r) (n + 1) x y ≤ (M.cutMassAt r 0) ^ n :=
  KernelPower.Kpow_succ_le_pow _ _ (M.cutKpow_row r)
    (fun a b => M.cutTwoPointE_le_one r a b) n x y

/-- **The source's decomposition `T^ℓ(0,0) = ∑_y ∇(0,y) T^{ℓ-3}(y,0)`** with `ℓ = n+3` and
`∇(0,y) = T³(0,y) = Kpow (cutTwoPointE r) 3 0 y`. -/
theorem cutKpow_comp (r : ℝ) (n : ℕ) :
    KernelPower.Kpow (M.cutTwoPointE r) (n + 3) (0 : M.V) 0
      = ∑' y, KernelPower.Kpow (M.cutTwoPointE r) 3 (0 : M.V) y
          * KernelPower.Kpow (M.cutTwoPointE r) n y 0 := by
  rw [Nat.add_comm]
  exact KernelPower.Kpow_add _ 3 n 0 0

/-- Real-valued row sums, the form in which I.4.18's exponent bookkeeping is done, under the
explicit hypothesis that `χ = E_{β_c,r}|K|` is finite. -/
theorem cutKpow_rowSum_toReal (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ) (x : M.V) :
    ∑' y, (KernelPower.Kpow (M.cutTwoPointE r) n x y).toReal
      = (M.cutMassAt r 0).toReal ^ n := by
  have hfin : ∀ y : M.V, KernelPower.Kpow (M.cutTwoPointE r) n x y ≠ ⊤ := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      intro y
      rw [KernelPower.Kpow_zero]
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      classical
      rw [KernelPower.deltaE]
      split_ifs <;> simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
      intro y
      exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hχ) (M.cutKpow_entry r m x y)
  rw [← ENNReal.tsum_toReal_eq hfin, M.cutKpow_rowSum r n x, ENNReal.toReal_pow]

/-- Real-valued column sums: `∑_y T^n_{β_c,r}(y,0) = χ^n` in `ℝ`, for finite `χ`. -/
theorem cutKpow_colSum_toReal (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ) (y : M.V) :
    ∑' x, (KernelPower.Kpow (M.cutTwoPointE r) n x y).toReal
      = (M.cutMassAt r 0).toReal ^ n := by
  have hfin : ∀ x : M.V, KernelPower.Kpow (M.cutTwoPointE r) n x y ≠ ⊤ := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      intro x
      rw [KernelPower.Kpow_zero]
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      classical
      rw [KernelPower.deltaE]
      split_ifs <;> simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
      intro x
      exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hχ) (M.cutKpow_entry r m x y)
  rw [← ENNReal.tsum_toReal_eq hfin, M.cutKpow_colSum r n y, ENNReal.toReal_pow]

end SourceModelData

end PercLib.CriticalLRP.Orchestration
