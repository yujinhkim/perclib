/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Discrete layer cake for integer-valued extended natural random variables

For `X : Ω → ℝ≥0∞` which is pointwise either `⊤` or a natural number (the shape of every
extended cardinality `|K| = (encard : ℕ∞)`, including `|K ∩ W|`), we prove

* `lintegral_eq_tsum_meas_ge` : `∫⁻ X = ∑' n, μ {ω | (n+1 : ℝ≥0∞) ≤ X ω}`,
* `lintegral_pow_eq_tsum_meas_ge` : for `k ≥ 1`,
  `∫⁻ X^k = ∑' n, ((n+1)^k - n^k) * μ {ω | (n+1 : ℝ≥0∞) ≤ X ω}`.

Both are obtained by truncation `X ∧ n` (monotone convergence) and the exact telescoping
identity `X ∧ n = ∑_{j<n} 1{X ≥ j+1}` (resp. its `k`-th power analogue), so no fractional
part ever appears.  These are the discrete ("finite-to-countable") counterparts of the
integration by parts over `(0,∞)` used in the paper's §I.2.1.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Tightness

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The indicator of a set, as an `ℝ≥0∞`-valued function (with the `1`/`0` fixed definitionally,
so that `lintegral_indicator_one` applies syntactically). -/
noncomputable def ind (s : Set Ω) : Ω → ℝ≥0∞ := s.indicator (fun _ => 1)

lemma ind_apply (s : Set Ω) (ω : Ω) : ind s ω = s.indicator (fun _ => (1 : ℝ≥0∞)) ω := rfl

lemma measurable_ind {s : Set Ω} (hs : MeasurableSet s) : Measurable (ind s) :=
  measurable_const.indicator hs

lemma lintegral_ind {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) :
    ∫⁻ ω, ind s ω ∂μ = μ s :=
  lintegral_indicator_one hs

/-! ### Cast and counting helpers for `ℝ≥0∞` -/

lemma cast_min_nat (m n : ℕ) : ((min m n : ℕ) : ℝ≥0∞) = min (m : ℝ≥0∞) (n : ℝ≥0∞) := by
  rcases le_total m n with h | h
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]

lemma cast_sum_nat {α : Type*} (s : Finset α) (g : α → ℕ) :
    ((∑ i ∈ s, g i : ℕ) : ℝ≥0∞) = ∑ i ∈ s, (g i : ℝ≥0∞) := by
  push_cast
  rfl

lemma filter_range_succ_le (m n : ℕ) :
    (Finset.range n).filter (fun j => j + 1 ≤ m) = Finset.range (min m n) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The telescoping sum `∑_{j<n} ((j+1)^k - j^k) = n^k` in `ℝ≥0∞`, for `k ≥ 1`. -/
lemma sum_range_pow_sub (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    ∑ j ∈ Finset.range n, (((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) = (n : ℝ≥0∞) ^ k := by
  induction n with
  | zero => simp [zero_pow (by omega : k ≠ 0)]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      show ((n + 1 : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) + 1 by push_cast; ring,
      add_tsub_cancel_of_le (pow_le_pow_left' (le_add_right (le_refl (n : ℝ≥0∞))) k)]

/-! ### The truncation identities -/

/-- **Truncation identity.**  If `x : ℝ≥0∞` is either `⊤` or a natural number, then for every
`n`, `min x n = ∑_{j < n} 1 {j + 1 ≤ x}`. -/
lemma min_eq_sum_ite {x : ℝ≥0∞} (hint : x = ⊤ ∨ ∃ m : ℕ, x = (m : ℝ≥0∞)) (n : ℕ) :
    min x (n : ℝ≥0∞) = ∑ j ∈ Finset.range n, (if ((j : ℝ≥0∞) + 1) ≤ x then 1 else 0) := by
  rcases hint with rfl | ⟨m, rfl⟩
  · rw [min_eq_right (le_top : (n : ℝ≥0∞) ≤ ⊤)]
    simp
  · have hstep : ∀ j ∈ Finset.range n,
        (if ((j : ℝ≥0∞) + 1) ≤ ((m : ℝ≥0∞)) then (1 : ℝ≥0∞) else 0)
          = ((if j + 1 ≤ m then 1 else 0 : ℕ) : ℝ≥0∞) := by
      intro j _
      have hcast : ((j : ℝ≥0∞) + 1) ≤ ((m : ℝ≥0∞)) ↔ j + 1 ≤ m := by
        rw [show ((j : ℝ≥0∞) + 1) = ((j + 1 : ℕ) : ℝ≥0∞) by push_cast; ring, Nat.cast_le]
      by_cases h : j + 1 ≤ m
      · rw [ite_eq_left (hcast.mpr h), ite_eq_left h]; simp
      · rw [ite_eq_right (hcast.not.mpr h), ite_eq_right h]; simp
    have hcard : ((∑ j ∈ Finset.range n, (if j + 1 ≤ m then 1 else 0 : ℕ) : ℕ) : ℝ≥0∞)
        = ((min m n : ℕ) : ℝ≥0∞) := by
      rw [← Finset.card_filter, filter_range_succ_le, Finset.card_range]
    rw [Finset.sum_congr rfl hstep, ← cast_sum_nat, hcard, cast_min_nat]

/-- **Power truncation identity.**  If `x : ℝ≥0∞` is either `⊤` or a natural number, then for
every `n` and `k ≥ 1`, `(min x n)^k = ∑_{j<n} ((j+1)^k - j^k) 1{j+1 ≤ x}`. -/
lemma min_pow_eq_sum_ite {x : ℝ≥0∞} (hint : x = ⊤ ∨ ∃ m : ℕ, x = (m : ℝ≥0∞)) (n k : ℕ)
    (hk : 1 ≤ k) :
    min x (n : ℝ≥0∞) ^ k
      = ∑ j ∈ Finset.range n,
          ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            (if ((j : ℝ≥0∞) + 1) ≤ x then 1 else 0)) := by
  rcases hint with rfl | ⟨m, rfl⟩
  · rw [min_eq_right (le_top : (n : ℝ≥0∞) ≤ ⊤)]
    simp only [le_top, ite_true, mul_one]
    exact (sum_range_pow_sub k hk n).symm
  · have hstep : ∀ j ∈ Finset.range n,
        ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            (if ((j : ℝ≥0∞) + 1) ≤ ((m : ℝ≥0∞)) then 1 else 0))
          = (if j + 1 ≤ m then (((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) else 0) := by
      intro j _
      have hcast : ((j : ℝ≥0∞) + 1) ≤ ((m : ℝ≥0∞)) ↔ j + 1 ≤ m := by
        rw [show ((j : ℝ≥0∞) + 1) = ((j + 1 : ℕ) : ℝ≥0∞) by push_cast; ring, Nat.cast_le]
      by_cases h : j + 1 ≤ m
      · rw [ite_eq_left (hcast.mpr h), ite_eq_left h, mul_one]
      · rw [ite_eq_right (hcast.not.mpr h), ite_eq_right h, mul_zero]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, filter_range_succ_le,
      sum_range_pow_sub k hk, cast_min_nat]

/-! ### The truncations increase to `X` -/

lemma iSup_min_eq_self (x : ℝ≥0∞) : (⨆ n : ℕ, min x (n : ℝ≥0∞)) = x := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  by_cases hx : x = ⊤
  · rw [hx]
    exact le_trans (le_of_eq ENNReal.iSup_natCast.symm)
      (iSup_le fun n => le_iSup_of_le n (by rw [min_top_left]))
  · obtain ⟨r, rfl⟩ : ∃ r : ℝ≥0, (r : ℝ≥0∞) = x := WithTop.ne_top_iff_exists.mp hx
    refine le_iSup_of_le ⌈r⌉₊ ?_
    rw [min_eq_left (by exact_mod_cast Nat.le_ceil r)]

lemma iSup_min_pow_eq_self (x : ℝ≥0∞) (k : ℕ) (hk : 1 ≤ k) :
    (⨆ n : ℕ, min x (n : ℝ≥0∞) ^ k) = x ^ k := by
  refine le_antisymm (iSup_le fun n => pow_le_pow_left' (min_le_left _ _) k) ?_
  by_cases hx : x = ⊤
  · have htop : (⊤ : ℝ≥0∞) ^ k = ⊤ := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ]
      simp
    rw [hx, htop]
    refine le_trans (le_of_eq ENNReal.iSup_natCast.symm) (iSup_le fun N => ?_)
    refine le_iSup_of_le N ?_
    rw [min_top_left]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [zero_pow (by omega : k ≠ 0)]
    · calc (N : ℝ≥0∞) = (N : ℝ≥0∞) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ≥0∞) ^ k := pow_le_pow_right' (by exact_mod_cast Nat.succ_le_of_lt hN) hk
  · obtain ⟨r, rfl⟩ : ∃ r : ℝ≥0, (r : ℝ≥0∞) = x := WithTop.ne_top_iff_exists.mp hx
    refine le_iSup_of_le ⌈r⌉₊ ?_
    rw [min_eq_left (by exact_mod_cast Nat.le_ceil r)]

section Main

/-- **Discrete layer cake (first moment).** -/
theorem lintegral_eq_tsum_meas_ge {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞)) :
    ∫⁻ ω, X ω ∂μ = ∑' n : ℕ, μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω} := by
  have hiSup : (⨆ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ∂μ) = ∫⁻ ω, X ω ∂μ := by
    rw [← lintegral_iSup (f := fun n ω => min (X ω) (n : ℝ≥0∞))]
    · exact lintegral_congr fun ω => iSup_min_eq_self (X ω)
    · exact fun n => hX.min (measurable_const (a := (n : ℝ≥0∞)))
    · exact fun a b hab ω => min_le_min_left _ (by exact_mod_cast hab)
  have hterm : ∀ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ∂μ
      = ∑ j ∈ Finset.range n, μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} := by
    intro n
    have hmeas : ∀ j : ℕ, MeasurableSet {ω : Ω | ((j : ℝ≥0∞) + 1) ≤ X ω} :=
      fun j => hX measurableSet_Ici
    have hpt : ∀ ω, min (X ω) (n : ℝ≥0∞)
        = ∑ j ∈ Finset.range n, ind {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} ω := by
      intro ω
      rw [min_eq_sum_ite (hint ω) n]
      refine Finset.sum_congr rfl fun j _ => ?_
      classical
      simp only [ind_apply, Set.indicator_apply]
      by_cases h : ((j : ℝ≥0∞) + 1) ≤ X ω <;> simp [h]
    calc ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ∂μ
        = ∫⁻ ω, ∑ j ∈ Finset.range n, ind {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} ω ∂μ :=
          lintegral_congr hpt
      _ = ∑ j ∈ Finset.range n, ∫⁻ ω, ind {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} ω ∂μ := by
          rw [lintegral_finsetSum]
          exact fun j _ => measurable_ind (hmeas j)
      _ = ∑ j ∈ Finset.range n, μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} := by
          exact Finset.sum_congr rfl fun j _ => lintegral_ind (hmeas j)
  calc ∫⁻ ω, X ω ∂μ = ⨆ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ∂μ := hiSup.symm
    _ = ⨆ n : ℕ, ∑ j ∈ Finset.range n, μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} := by
        simp only [hterm]
    _ = ∑' n : ℕ, μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω} := ENNReal.tsum_eq_iSup_nat.symm

/-- **Discrete layer cake (k-th moment).** -/
theorem lintegral_pow_eq_tsum_meas_ge {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞))
    (k : ℕ) (hk : 1 ≤ k) :
    ∫⁻ ω, X ω ^ k ∂μ
      = ∑' n : ℕ, ((((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) *
          μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω}) := by
  have hiSup : (⨆ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ^ k ∂μ) = ∫⁻ ω, X ω ^ k ∂μ := by
    rw [← lintegral_iSup (f := fun n ω => min (X ω) (n : ℝ≥0∞) ^ k)]
    · exact lintegral_congr fun ω => iSup_min_pow_eq_self (X ω) k hk
    · exact fun n => (hX.min (measurable_const (a := (n : ℝ≥0∞)))).pow_const k
    · exact fun a b hab ω => pow_le_pow_left' (min_le_min_left _ (by exact_mod_cast hab)) k
  have hterm : ∀ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ^ k ∂μ
      = ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
          μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}) := by
    intro n
    have hmeas : ∀ j : ℕ, MeasurableSet {ω : Ω | ((j : ℝ≥0∞) + 1) ≤ X ω} :=
      fun j => hX measurableSet_Ici
    have hpt : ∀ ω, min (X ω) (n : ℝ≥0∞) ^ k
        = ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            ind {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} ω) := by
      intro ω
      rw [min_pow_eq_sum_ite (hint ω) n k hk]
      refine Finset.sum_congr rfl fun j _ => ?_
      classical
      simp only [ind_apply, Set.indicator_apply]
      by_cases h : ((j : ℝ≥0∞) + 1) ≤ X ω <;> simp [h]
    calc ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ^ k ∂μ
        = ∫⁻ ω, ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            ind {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} ω) ∂μ := lintegral_congr hpt
      _ = ∑ j ∈ Finset.range n, ∫⁻ ω, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            ind {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} ω) ∂μ := by
          rw [lintegral_finsetSum]
          exact fun j _ => (measurable_ind (hmeas j)).const_mul _
      _ = ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_const_mul _ (measurable_ind (hmeas j)), lintegral_ind (hmeas j)]
  calc ∫⁻ ω, X ω ^ k ∂μ = ⨆ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ^ k ∂μ := hiSup.symm
    _ = ⨆ n : ℕ, ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
          μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}) := by simp only [hterm]
    _ = ∑' n : ℕ, ((((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) *
          μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω}) := ENNReal.tsum_eq_iSup_nat.symm

end Main

end PercLib.CriticalLRP.Tightness
