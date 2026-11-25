/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Member m5, swarm smwg5u3az — direction E (HD first-moment asymptotics).

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.4.1, proof of Lemma I.4.9 (pp. 37–38) and
Proposition I.4.2, Case 1 (`d > 3α`).

Formalized here:
* `error_of_E0_E1`: the multiplicative error `Ē = 1 − (1−𝓔₀)(1−𝓔₁)` of (I.4.6)
  satisfies `|Ē| ≤ 1/8 + (9/8) C r^{3α−d} (A/((α/β)r^α))³` whenever
  `|𝓔₀| ≤ 1/8` and `0 ≤ 𝓔₁ ≤ C r^{3α−d} (A/((α/β)r^α))³`.
* `tree_graph_error_bound`: the algebra of (I.4.8) — from `|B_r| ≥ c r^d` and
  `𝓔₁ ≤ 3A³/|B_r|` (Lemma I.4.7 + tree-graph inequality `E|K|³ ≤ 3(E|K|)^5`).
* `bootstrap_perturbed`: Lemma I.4.9's engine, with the paper's bookkeeping but
  *honestly* allowing the perturbation `1/8` coming from `𝓔₀`.  (The paper's
  display `Ē ≤ C r^{3α−d}(...)^3` for every `r ≥ 1` silently drops `𝓔₀`; the
  correct statement is additive, and this is why the constants below differ.)
* `first_moment_bound_all_beta`: runs the engine for every `β ∈ [β_c/2, β_c)`
  with a `β`-independent constant and passes to `β ↑ β_c` by monotone
  convergence.

Explicit, non-hidden inputs (supplied by other components of the campaign):
* the ODE identity (I.4.6) for each `β` (Russo's formula/pivot identity on the
  countable model plus the error algebra of `VolumeMoments/ErrorTerms.lean`);
* `𝓔_{1,r,β} ≤ 3(E_{β,r}|K|)³/|B_r|` (Lemma I.4.7 together with the tree-graph
  inequality `E|K|³ ≤ 3(E|K|)^5`);
* `|B_r| ≥ c r^d` (Lemma I.4.6);
* sharpness of the phase transition: for `β < β_c`, `E_{β,r}|K| ≤ (2α/β) r^α`
  eventually;
* monotone convergence of `E_{β,r}|K|` as `β ↑ β_c`.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.Asymptotic
public import PercLib.CriticalLRP.VolumeMoments.Bootstrap

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.VolumeMoments.FirstMoment

/-! ### Rewriting helpers for `rpow` -/

theorem rpow_mul_absorb {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    r ^ (3 * a - b) * r ^ (-(3 * a)) = r ^ (-b) := by
  rw [← Real.rpow_add hr]
  congr 1
  ring

theorem rpow_cube_of_pos {r : ℝ} (hr : 0 < r) (a : ℝ) : (r ^ a) ^ 3 = r ^ (3 * a) := by
  rw [← Real.rpow_natCast (r ^ a) 3, ← Real.rpow_mul hr.le]
  congr 1
  ring

/-! ### The error `Ē` of (I.4.6) in terms of `𝓔₀` and `𝓔₁` -/

/-- `Ē = 1 − (1−𝓔₀)(1−𝓔₁) = 𝓔₀ + 𝓔₁ − 𝓔₀𝓔₁`; if `|𝓔₀| ≤ 1/8` and
`0 ≤ 𝓔₁ ≤ C r^{3α−d}(A/((α/β)r^α))³` then
`|Ē| ≤ 1/8 + (9/8) C r^{3α−d}(A/((α/β)r^α))³`. -/
theorem error_of_E0_E1 {α β d C E0 E1 A r : ℝ} (hE0 : |E0| ≤ 1 / 8) (hE1nn : 0 ≤ E1)
    (hE1 : E1 ≤ C * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3) :
    |1 - (1 - E0) * (1 - E1)|
      ≤ 1 / 8 + (9 / 8) * C * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3 := by
  have h1 : |1 - E0| ≤ 9 / 8 := by
    have h := abs_le.1 hE0
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hkey : (1 - (1 - E0) * (1 - E1)) = E0 + E1 * (1 - E0) := by ring
  rw [hkey]
  have h3 : |E1 * (1 - E0)| ≤ (9 / 8) * E1 := by
    rw [abs_mul]
    calc |E1| * |1 - E0| ≤ E1 * (9 / 8) := by
          rw [abs_of_nonneg hE1nn]
          exact mul_le_mul_of_nonneg_left h1 hE1nn
      _ = (9 / 8) * E1 := by ring
  have h4 : (9 / 8) * E1 ≤ (9 / 8) * (C * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3) := by
    nlinarith [hE1]
  calc |E0 + E1 * (1 - E0)| ≤ |E0| + |E1 * (1 - E0)| := abs_add_le _ _
    _ ≤ 1 / 8 + (9 / 8) * E1 := by linarith [hE0, h3]
    _ ≤ 1 / 8 + (9 / 8) * (C * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3) := by linarith [h4]
    _ = 1 / 8 + (9 / 8) * C * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3 := by ring

/-- **The algebra of (I.4.8)**: if `|B_r| ≥ c r^d` and `𝓔₁ ≤ 3A³/|B_r|` then
`𝓔₁ ≤ (3/c)(α/β)³ r^{3α−d} (A/((α/β)r^α))³`. -/
theorem tree_graph_error_bound {α β d c A b E1 r : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hc : 0 < c) (hr : 0 < r) (hA : 0 < A)
    (hb : c * r ^ d ≤ b) (hE1 : E1 ≤ 3 * A ^ 3 / b) :
    E1 ≤ (3 / c) * (α / β) ^ 3 * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3 := by
  have hbpos : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have hcrd : 0 < c * r ^ d := by positivity
  have h1 : 3 * A ^ 3 / b ≤ 3 * A ^ 3 / (c * r ^ d) :=
    div_le_div_of_nonneg_left (by positivity) hcrd hb
  have h2 : (3 / c) * (α / β) ^ 3 * r ^ (3 * α - d) * (A / (α / β * r ^ α)) ^ 3
      = 3 * A ^ 3 / (c * r ^ d) := by
    have hcube : (A / (α / β * r ^ α)) ^ 3 = A ^ 3 / ((α / β) ^ 3 * r ^ (3 * α)) := by
      rw [div_pow, mul_pow, rpow_cube_of_pos hr α]
    have hsplit : r ^ (3 * α - d) * (r ^ (3 * α))⁻¹ = r ^ (-d) := by
      rw [← Real.rpow_neg hr.le, rpow_mul_absorb hr α d]
    have hstep : (3 / c) * (α / β) ^ 3 * r ^ (3 * α - d) * (A ^ 3 / ((α / β) ^ 3 * r ^ (3 * α)))
        = (3 / c) * A ^ 3 * (r ^ (3 * α - d) * (r ^ (3 * α))⁻¹) := by
      field_simp
    rw [hcube, hstep, hsplit, Real.rpow_neg hr.le]
    field_simp
  linarith [hE1, h1, le_of_eq h2]


/-! ### Threshold arithmetic for the bootstrap -/

theorem rpow_div_pow {P r₀ α d : ℝ} (hP : 0 < P) (hr₀ : 0 < r₀) (hd : 0 < d) :
    (P ^ (1 / d) * r₀ ^ (3 * α / d)) ^ d = P * r₀ ^ (3 * α) := by
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hP.le,
    ← Real.rpow_mul hr₀.le,
    show (1 / d) * d = 1 by field_simp,
    show (3 * α / d) * d = 3 * α by field_simp,
    Real.rpow_one]

theorem one_le_threshold {P r₀ α d : ℝ} (hP : 0 < P) (hα : 0 < α) (hd : 0 < d)
    (hr₀ : P ^ (-(1 / (3 * α))) < r₀) :
    1 ≤ P ^ (1 / d) * r₀ ^ (3 * α / d) := by
  have hstep : P ^ (-(1 / d)) ≤ r₀ ^ (3 * α / d) := by
    have h1 : (P ^ (-(1 / (3 * α)))) ^ (3 * α / d) ≤ r₀ ^ (3 * α / d) :=
      Real.rpow_le_rpow (x := P ^ (-(1 / (3 * α)))) (y := r₀) (z := 3 * α / d)
        (Real.rpow_nonneg hP.le _) hr₀.le (by positivity)
    have h2 : (P ^ (-(1 / (3 * α)))) ^ (3 * α / d) = P ^ (-(1 / d)) := by
      rw [← Real.rpow_mul hP.le]
      congr 1
      field_simp
    rwa [h2] at h1
  calc (1 : ℝ) = P ^ (1 / d) * P ^ (-(1 / d)) := by
        rw [← Real.rpow_add hP]; norm_num
    _ ≤ P ^ (1 / d) * r₀ ^ (3 * α / d) := by
        apply mul_le_mul_of_nonneg_left hstep (le_of_lt (Real.rpow_pos_of_pos hP _))

theorem R₁_le_threshold {P r₀ R₁ α d : ℝ} (hP : 0 < P) (hα : 0 < α) (hd : 0 < d)
    (hR₁ : 0 ≤ R₁) (hr₀ : R₁ ^ (d / (3 * α)) * P ^ (-(1 / (3 * α))) < r₀) :
    R₁ ≤ P ^ (1 / d) * r₀ ^ (3 * α / d) := by
  have hbase : 0 ≤ R₁ ^ (d / (3 * α)) * P ^ (-(1 / (3 * α))) := by positivity
  have h1 : (R₁ ^ (d / (3 * α)) * P ^ (-(1 / (3 * α)))) ^ (3 * α / d)
      ≤ r₀ ^ (3 * α / d) :=
    Real.rpow_le_rpow hbase hr₀.le (by positivity)
  have h2 : (R₁ ^ (d / (3 * α)) * P ^ (-(1 / (3 * α)))) ^ (3 * α / d)
      = R₁ * P ^ (-(1 / d)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hR₁ _) (Real.rpow_nonneg hP.le _),
      ← Real.rpow_mul hR₁, ← Real.rpow_mul hP.le,
      show d / (3 * α) * (3 * α / d) = 1 by field_simp,
      show -(1 / (3 * α)) * (3 * α / d) = -(1 / d) by field_simp,
      Real.rpow_one]
  rw [h2] at h1
  have key : R₁ * P ^ (-(1 / d)) * P ^ (1 / d) ≤ r₀ ^ (3 * α / d) * P ^ (1 / d) :=
    mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hP.le _)
  have hPprod : P ^ (-(1 / d)) * P ^ (1 / d) = 1 := by
    rw [← Real.rpow_add hP]
    norm_num
  calc R₁ = R₁ * 1 := by ring
    _ = R₁ * (P ^ (-(1 / d)) * P ^ (1 / d)) := by rw [hPprod]
    _ = R₁ * P ^ (-(1 / d)) * P ^ (1 / d) := by ring
    _ ≤ r₀ ^ (3 * α / d) * P ^ (1 / d) := key
    _ = P ^ (1 / d) * r₀ ^ (3 * α / d) := by ring

theorem threshold_lt_self {P r₀ α d : ℝ} (hP : 0 < P) (hr₀ : 0 < r₀) (hα : 0 < α)
    (hg : 0 < d - 3 * α)
    (hr : P ^ (1 / (d - 3 * α)) < r₀) :
    P ^ (1 / d) * r₀ ^ (3 * α / d) < r₀ := by
  have hd : 0 < d := by linarith
  have hexp : 1 - 3 * α / d = (d - 3 * α) / d := by field_simp
  have h1 : P ^ (1 / d) < r₀ ^ (1 - 3 * α / d) := by
    have h2 : (P ^ (1 / (d - 3 * α))) ^ ((d - 3 * α) / d) < r₀ ^ ((d - 3 * α) / d) :=
      Real.rpow_lt_rpow (x := P ^ (1 / (d - 3 * α))) (y := r₀) (z := (d - 3 * α) / d)
        (Real.rpow_nonneg hP.le _) hr (by positivity)
    have h3 : (P ^ (1 / (d - 3 * α))) ^ ((d - 3 * α) / d) = P ^ (1 / d) := by
      rw [← Real.rpow_mul hP.le]
      congr 1
      field_simp
    have h4 : r₀ ^ ((d - 3 * α) / d) = r₀ ^ (1 - 3 * α / d) := by rw [hexp]
    rwa [h3, h4] at h2
  have h5 : P ^ (1 / d) * r₀ ^ (3 * α / d) < r₀ ^ (1 - 3 * α / d) * r₀ ^ (3 * α / d) :=
    mul_lt_mul_of_pos_right h1 (Real.rpow_pos_of_pos hr₀ _)
  have h6 : r₀ ^ (1 - 3 * α / d) * r₀ ^ (3 * α / d) = r₀ := by
    rw [← Real.rpow_add hr₀]
    rw [show 1 - 3 * α / d + 3 * α / d = 1 by ring, Real.rpow_one]
  rw [h6] at h5
  exact h5


/-! ### The bootstrapping engine of Lemma I.4.9 -/

/-- The threshold produced by the bootstrapping argument: with `P = 128 C`,
`r₀ ≤ max 1 (max A₁ (max A₂ (max A₃ A₄)))` where
`A₁ = R₁ P^{−1/(3α)}`, `A₂ = R₁^{d/(3α)} P^{−1/(3α)}`, `A₃ = P^{1/(d−3α)}`,
`A₄ = P^{−1/(3α)}`.  (The paper's `(32C)^{1/(d−3α)}` corresponds to `A₃`; the
extra factors are needed because of the `𝓔₀` perturbation and because the engine
is stated with `R₁ ≥ 1`-type side conditions made explicit.) -/
noncomputable def bootstrapThreshold (α R₁ d C : ℝ) : ℝ :=
  max 1 (max (R₁ * (128 * C) ^ (-(1 / (3 * α))))
    (max (R₁ ^ (d / (3 * α)) * (128 * C) ^ (-(1 / (3 * α))))
      (max ((128 * C) ^ (1 / (d - 3 * α))) ((128 * C) ^ (-(1 / (3 * α)))))))

/-- **Lemma I.4.9's engine**, with the paper's bookkeeping and the honest
perturbation `1/8` coming from `𝓔₀`: if `d > 3α`, `F` satisfies
`F' = (1−e) β r^{−α−1}F²`, the multiplicative error obeys
`|e r| ≤ 1/8 + C r^{3α−d}(F r/((α/β)r^α))³` for `r ≥ R₁`, `F` is positive and
monotone, and `r₀ ≥ 1` is *minimal* with `F r ≤ (2α/β)r^α` for `r ≥ r₀`
(sharpness of the phase transition), then `r₀ ≤ bootstrapThreshold α R₁ d C`. -/
theorem bootstrap_perturbed
    {α β d C R₁ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hC : 0 < C) (hγ : 0 < d - 3 * α)
    (hR₁ : 0 ≤ R₁)
    {F F' e : ℝ → ℝ}
    (hderiv : ∀ r, 1 ≤ r → HasDerivAt F (F' r) r)
    (hODE : ∀ r, 1 ≤ r → F' r = (1 - e r) * β * r ^ (-α - 1) * (F r) ^ 2)
    (hpos : ∀ r, 1 ≤ r → 0 < F r)
    (hmono : ∀ r s, 1 ≤ r → r ≤ s → F r ≤ F s)
    (herr : ∀ r, R₁ ≤ r → |e r| ≤ 1 / 8 + C * r ^ (3 * α - d) * (F r / (α / β * r ^ α)) ^ 3)
    {r₀ : ℝ} (hr₀ : 1 ≤ r₀) (hbdd : ∀ r, r₀ ≤ r → F r ≤ 2 * α / β * r ^ α)
    (hmin : ∀ b, 1 ≤ b → (∀ r, b ≤ r → F r ≤ 2 * α / β * r ^ α) → r₀ ≤ b) :
    r₀ ≤ bootstrapThreshold α R₁ d C := by
  rw [bootstrapThreshold]
  set A1 : ℝ := R₁ * (128 * C) ^ (-(1 / (3 * α))) with hA1def
  set A2 : ℝ := R₁ ^ (d / (3 * α)) * (128 * C) ^ (-(1 / (3 * α))) with hA2def
  set A3 : ℝ := (128 * C) ^ (1 / (d - 3 * α)) with hA3def
  set A4 : ℝ := (128 * C) ^ (-(1 / (3 * α))) with hA4def
  set R : ℝ := max 1 (max A1 (max A2 (max A3 A4))) with hRdef
  have hdpos : 0 < d := by linarith
  have hPpos : 0 < 128 * C := by positivity
  by_contra hcon
  rw [not_le] at hcon
  have hlt : R < r₀ := hcon
  -- the five consequences of `r₀ > R`
  have hA1le : A1 ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_left A1 _) (le_max_right 1 _)
  have hA2le : A2 ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_left A2 _) (le_trans (le_max_right A1 _) (le_max_right 1 _))
  have hA3le : A3 ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_left A3 A4)
      (le_trans (le_max_right A2 _) (le_trans (le_max_right A1 _) (le_max_right 1 _)))
  have hA4le : A4 ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_right A3 A4)
      (le_trans (le_max_right A2 _) (le_trans (le_max_right A1 _) (le_max_right 1 _)))
  have h1le : (1:ℝ) ≤ R := by rw [hRdef]; exact le_max_left _ _
  have hR1 : A4 < r₀ := lt_of_le_of_lt hA4le hlt
  have hR2 : A1 < r₀ := lt_of_le_of_lt hA1le hlt
  have hR3 : A2 < r₀ := lt_of_le_of_lt hA2le hlt
  have hR4 : A3 < r₀ := lt_of_le_of_lt hA3le hlt
  have hr₀pos : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  set P : ℝ := 128 * C with hPdef
  have hPpos' : 0 < P := by rw [hPdef]; exact hPpos
  -- keep the numeric lemmas in the `P` form
  have hR1' : P ^ (-(1 / (3 * α))) < r₀ := hR1
  have hR3' : R₁ ^ (d / (3 * α)) * P ^ (-(1 / (3 * α))) < r₀ := hR3
  have hR4' : P ^ (1 / (d - 3 * α)) < r₀ := hR4
  set r : ℝ := P ^ (1 / d) * r₀ ^ (3 * α / d) with hrdef
  have hr1 : 1 ≤ r := one_le_threshold hPpos' hα hdpos hR1'
  have hrR₁ : R₁ ≤ r := R₁_le_threshold hPpos' hα hdpos hR₁ hR3'
  have hrlt : r < r₀ := threshold_lt_self hPpos' hr₀pos hα hγ hR4'
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrd : r ^ d = P * r₀ ^ (3 * α) := rpow_div_pow hPpos' hr₀pos hdpos
  -- the a priori bound with `max s r₀`
  have hFa : ∀ s, 1 ≤ s → F s ≤ (2 * α / β) * (max s r₀) ^ α := by
    intro s hs
    rcases le_total r₀ s with h | h
    · rw [max_eq_left h]; exact hbdd s h
    · rw [max_eq_right h]
      calc F s ≤ F r₀ := hmono s r₀ hs h
        _ ≤ 2 * α / β * r₀ ^ α := hbdd r₀ le_rfl
  -- the crucial smallness of the error on `[r, ∞)`
  have herr14 : ∀ s, r ≤ s → |e s| ≤ 1 / 4 := by
    intro s hrs
    have hs1 : 1 ≤ s := le_trans hr1 hrs
    have hsR₁ : R₁ ≤ s := le_trans hrR₁ hrs
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have hcube : (F s / (α / β * s ^ α)) ^ 3 ≤ 8 * (((max s r₀) / s) ^ (3 * α)) := by
      have hspos : 0 < s ^ α := Real.rpow_pos_of_pos hs0 α
      have hratio : F s / (α / β * s ^ α) ≤ 2 * (((max s r₀) / s) ^ α) := by
        rw [div_le_iff₀ (by positivity)]
        calc F s ≤ (2 * α / β) * ((max s r₀) ^ α) := hFa s hs1
          _ = 2 * (((max s r₀) / s) ^ α) * (α / β * s ^ α) := by
              rw [Real.div_rpow (by positivity) hs0.le]
              field_simp
      have hnonneg : 0 ≤ F s / (α / β * s ^ α) :=
        le_of_lt (div_pos (hpos s hs1) (by positivity))
      calc (F s / (α / β * s ^ α)) ^ 3 ≤ (2 * (((max s r₀) / s) ^ α)) ^ 3 :=
            pow_le_pow_left₀ hnonneg hratio 3
        _ = 8 * (((max s r₀) / s) ^ (3 * α)) := by
            rw [mul_pow, rpow_cube_of_pos (by positivity) (α)]
            norm_num
    have hstep : C * s ^ (3 * α - d) * (F s / (α / β * s ^ α)) ^ 3
        ≤ 8 * C * ((max s r₀) ^ (3 * α)) * s ^ (-d) := by
      have hA : (0:ℝ) ≤ C * s ^ (3 * α - d) :=
        mul_nonneg hC.le (Real.rpow_nonneg hs0.le _)
      have h1 : C * s ^ (3 * α - d) * (F s / (α / β * s ^ α)) ^ 3
          ≤ C * s ^ (3 * α - d) * (8 * (((max s r₀) / s) ^ (3 * α))) :=
        mul_le_mul_of_nonneg_left hcube hA
      have h2 : C * s ^ (3 * α - d) * (8 * (((max s r₀) / s) ^ (3 * α)))
          = 8 * C * ((max s r₀) ^ (3 * α)) * s ^ (-d) := by
        have hsplit : ((max s r₀) / s) ^ (3 * α)
            = (max s r₀) ^ (3 * α) * (s ^ (3 * α))⁻¹ := by
          rw [Real.div_rpow (by positivity) hs0.le, div_eq_mul_inv]
        have h3 : s ^ (3 * α - d) * (s ^ (3 * α))⁻¹ = s ^ (-d) := by
          rw [← Real.rpow_neg hs0.le, rpow_mul_absorb hs0 α d]
        rw [hsplit]
        calc C * s ^ (3 * α - d) * (8 * ((max s r₀) ^ (3 * α) * (s ^ (3 * α))⁻¹))
            = 8 * C * (max s r₀) ^ (3 * α) * (s ^ (3 * α - d) * (s ^ (3 * α))⁻¹) := by ring
          _ = 8 * C * (max s r₀) ^ (3 * α) * s ^ (-d) := by rw [h3]
      linarith [h1, le_of_eq h2]
    have hmax : ((max s r₀) ^ (3 * α)) * s ^ (-d) ≤ (r₀ ^ (3 * α)) * r ^ (-d) := by
      rcases le_total r₀ s with h | h
      · rw [max_eq_left h]
        have h1 : s ^ (3 * α - d) ≤ r₀ ^ (3 * α - d) :=
          Real.rpow_le_rpow_of_nonpos hr₀pos h (by linarith)
        have h2 : s ^ (3 * α - d) = s ^ (3 * α) * s ^ (-d) := by
          rw [← Real.rpow_add hs0]; ring_nf
        have hratio : 1 ≤ r₀ ^ d * r ^ (-d) := by
          rw [Real.rpow_neg hrpos.le, ← div_eq_mul_inv, ← Real.div_rpow hr₀pos.le hrpos.le]
          rw [← Real.one_rpow d]
          exact Real.rpow_le_rpow zero_le_one (le_of_lt ((one_lt_div hrpos).2 hrlt)) hdpos.le
        have h3 : r₀ ^ (3 * α - d) ≤ r₀ ^ (3 * α) * r ^ (-d) := by
          calc r₀ ^ (3 * α - d) = r₀ ^ (3 * α - d) * 1 := by ring
            _ ≤ r₀ ^ (3 * α - d) * (r₀ ^ d * r ^ (-d)) :=
                mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hr₀pos.le _)
            _ = r₀ ^ (3 * α) * r ^ (-d) := by
                rw [← mul_assoc, ← Real.rpow_add hr₀pos, show 3 * α - d + d = 3 * α by ring]
        linarith [h1, h2, h3]
      · rw [max_eq_right h]
        have h4 : s ^ (-d) ≤ r ^ (-d) := Real.rpow_le_rpow_of_nonpos hrpos hrs (by linarith)
        have h5 : 0 ≤ r₀ ^ (3 * α) := Real.rpow_nonneg hr₀pos.le _
        exact mul_le_mul_of_nonneg_left h4 h5
    have hfinal : 8 * C * ((max s r₀) ^ (3 * α)) * s ^ (-d)
        ≤ 8 * C * (r₀ ^ (3 * α)) * r ^ (-d) := by
      have h8 : 0 ≤ 8 * C := by positivity
      nlinarith [hmax, h8]
    have hrpow2 : 8 * C * (r₀ ^ (3 * α)) * r ^ (-d) = 1 / 16 := by
      rw [Real.rpow_neg hrpos.le, hrd]
      have hPr : 0 < P * r₀ ^ (3 * α) := by positivity
      have hPval : P = 128 * C := hPdef
      field_simp
      nlinarith [hPr]
    have hbase := herr s hsR₁
    linarith [hbase, hstep, hfinal, hrpow2]
  have hadm : ∀ s, r ≤ s → F s ≤ (2 * α / β) * s ^ α := by
    intro s hs
    have hs1 : 1 ≤ s := le_trans hr1 hs
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have hineq : ∀ x, r ≤ x → (3 / 4 * β) * x ^ (-α - 1) * (F x) ^ 2 ≤ F' x := by
      intro x hx
      have hx1 : 1 ≤ x := le_trans hr1 hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      rw [hODE x hx1]
      have hle : |e x| ≤ 1 / 4 := herr14 x hx
      have hge : (3 / 4 : ℝ) ≤ 1 - e x := by
        have h2 := abs_le.1 hle
        linarith [h2.2]
      have hnn : 0 ≤ β * x ^ (-α - 1) * (F x) ^ 2 := by
        have := hpos x hx1
        positivity
      have h1 : (3 / 4) * (β * x ^ (-α - 1) * (F x) ^ 2)
          ≤ (1 - e x) * (β * x ^ (-α - 1) * (F x) ^ 2) :=
        mul_le_mul_of_nonneg_right hge hnn
      calc (3 / 4 * β) * x ^ (-α - 1) * (F x) ^ 2
          = (3 / 4) * (β * x ^ (-α - 1) * (F x) ^ 2) := by ring
        _ ≤ (1 - e x) * (β * x ^ (-α - 1) * (F x) ^ 2) := h1
        _ = (1 - e x) * β * x ^ (-α - 1) * (F x) ^ 2 := by ring
    have hmain := PercLib.CriticalLRP.VolumeMoments.lemma_I_4_5_one_nocont
      (f := F) (f' := F') (A := 3 / 4 * β) (α := α) (r₀ := r)
      (by positivity) hα hrpos
      (fun x hx => hderiv x (le_trans hr1 hx))
      (fun x hx => hpos x (le_trans hr1 hx)) hineq
    have hfin := hmain s hs
    have hcoef : α / (3 / 4 * β) = 4 * α / (3 * β) := by field_simp
    rw [hcoef] at hfin
    have hle2 : 4 * α / (3 * β) ≤ 2 * α / β := by
      have h3β : (0:ℝ) < 3 * β := by positivity
      rw [div_le_iff₀ h3β]
      have h6 : 2 * α / β * (3 * β) = 6 * α := by
        field_simp
        ring
      rw [h6]
      linarith [hα]
    have hspos : 0 < s ^ α := Real.rpow_pos_of_pos hs0 α
    nlinarith [hfin, hle2, hspos]
  have hlast := hmin r hr1 hadm
  linarith

/-! ### Proposition I.4.2, Case 1: assembly -/

/-- **Proposition I.4.2, Case 1 (`d > 3α`) — the a priori bound.**

Suppose that for every `β ∈ [β_c/2, β_c)`:
* `F β` satisfies the first-moment ODE (I.4.6) with error `e β`;
* `F β > 0` and `r ↦ F β r` is nondecreasing;
* the multiplicative error obeys `|e β r| ≤ 1/8 + C r^{3α−d}(F β r/((α/β)r^α))³` for
  `r ≥ R₁` — this is (I.4.8) together with Lemma I.4.7, with a `β`-independent
  constant;
* `r₀ β ≥ 1` is the *minimal* threshold with `F β r ≤ (2α/β) r^α` for `r ≥ r₀ β`
  (sharpness of the phase transition);

and suppose `F β r → F β_c r` as `β ↑ β_c` for every `r`.  Then there is
`R < ∞`, depending only on `α, d, C, R₁`, with `F β_c r ≤ (2α/β_c) r^α` for all
`r ≥ R`. -/
theorem first_moment_bound_all_beta
    {α d C βc R₁ : ℝ} (hα : 0 < α) (hβc : 0 < βc) (hC : 0 < C) (hγ : 0 < d - 3 * α)
    (hR₁ : 0 ≤ R₁)
    {F F' e : ℝ → ℝ → ℝ} {r₀ : ℝ → ℝ}
    (hderiv : ∀ β r, 1 ≤ r → HasDerivAt (F β) (F' β r) r)
    (hODE : ∀ β r, 1 ≤ r → F' β r = (1 - e β r) * β * r ^ (-α - 1) * (F β r) ^ 2)
    (hpos : ∀ β r, 1 ≤ r → 0 < F β r)
    (hmono : ∀ β r s, 1 ≤ r → r ≤ s → F β r ≤ F β s)
    (herr : ∀ β r, βc / 2 ≤ β → β ≤ βc → R₁ ≤ r →
      |e β r| ≤ 1 / 8 + C * r ^ (3 * α - d) * (F β r / (α / β * r ^ α)) ^ 3)
    (hr₀1 : ∀ β, βc / 2 ≤ β → β < βc → 1 ≤ r₀ β)
    (hbdd : ∀ β r, βc / 2 ≤ β → β < βc → r₀ β ≤ r → F β r ≤ 2 * α / β * r ^ α)
    (hmin : ∀ β b, βc / 2 ≤ β → β < βc → 1 ≤ b →
      (∀ r, b ≤ r → F β r ≤ 2 * α / β * r ^ α) → r₀ β ≤ b)
    (hmeet : ∀ r, Tendsto (fun β => F β r) (𝓝[<] βc) (𝓝 (F βc r))) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ r, R ≤ r → F βc r ≤ 2 * α / βc * r ^ α := by
  refine ⟨bootstrapThreshold α R₁ d C, ?_, ?_⟩
  · rw [bootstrapThreshold]
    exact le_max_left 1 _
  · intro r hr
    have hτ1 : 1 ≤ bootstrapThreshold α R₁ d C := by
      rw [bootstrapThreshold]
      exact le_max_left 1 _
    have hr1 : 1 ≤ r := le_trans hτ1 hr
    -- every `β < β_c` in the range obeys the bound at this fixed `r`
    have hstep : ∀ β, βc / 2 ≤ β → β < βc → F β r ≤ 2 * α / β * r ^ α := by
      intro β h1β h2β
      have hβpos : 0 < β := lt_of_lt_of_le (by linarith) h1β
      have hτ := bootstrap_perturbed (F := F β) (F' := F' β) (e := e β) (R₁ := R₁)
        hα hβpos hC hγ hR₁ (hderiv β) (hODE β) (hpos β) (hmono β)
        (fun s hs => herr β s h1β h2β.le hs) (hr₀1 β h1β h2β)
        (fun s hs => hbdd β s h1β h2β hs)
        (fun b hb1 hb2 => hmin β b h1β h2β hb1 hb2)
      exact hbdd β r h1β h2β (le_trans hτ hr)
    -- pass to `β ↑ β_c`
    have hlimR : Tendsto (fun β : ℝ => 2 * α / β * r ^ α) (𝓝[<] βc) (𝓝 (2 * α / βc * r ^ α)) := by
      have h1 : Tendsto (fun β : ℝ => β⁻¹) (𝓝[<] βc) (𝓝 βc⁻¹) :=
        (tendsto_inv₀ hβc.ne').mono_left nhdsWithin_le_nhds
      have h2 := h1.const_mul (2 * α * r ^ α)
      have h3 : (2 * α * r ^ α) * βc⁻¹ = 2 * α / βc * r ^ α := by
        field_simp
      rw [h3] at h2
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h2
    refine le_of_tendsto_of_tendsto (hmeet r) hlimR ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds (show βc / 2 < βc by linarith))] with β hβlt hβgt
    exact hstep β hβgt.le hβlt

end PercLib.CriticalLRP.VolumeMoments.FirstMoment
