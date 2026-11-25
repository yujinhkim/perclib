/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Separation of the hypotheses of the I.5.8 assembly

The abstract finite model of `VolumeMoments/I58Remainder.lean` is a finite type `Ω`,
a weight `w : Ω → ℝ` with `w ≥ 0`, `∑ w = 1`, a cluster map `K : Ω → Finset (Site d)`,
restored clusters `Ky : Site d → Ω → Finset (Site d)`, a ball `B`, a direction `u` and
a radius `r`.  The four displayed remainder estimates `hR0 hR2 hR3 hR4` and `hGq` are
*hypotheses* there.

This file settles which of them are consequences of the others in that bare model.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.I58Cross

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.I58

/-! ## A concrete two-dimensional test family

`d = 2`, direction `u = (1,0)`, single-point cluster `K = {(1,0)}` and ball
`B_n = {(1,0)} ∪ {(0,1), …, (0,n)}`.  The restored cluster of `y` is `y + (1,0)`.

Because `⟨(0,a),u⟩ = 0` for every vertical site, the `T4` term vanishes on the
vertical points without any reflection symmetry, and `T3` contributes `1` per
vertical point. -/

/-- The site `(a,b)` of `ℤ²`. -/
def p2 (a b : ℤ) : Site 2 := fun i => if i = 0 then a else b

@[simp] lemma p2_zero (a b : ℤ) : p2 a b 0 = a := by simp [p2]

lemma p2_one (a b : ℤ) : p2 a b 1 = b := by
  simp [p2, show (1 : Fin 2) ≠ 0 from by decide]

lemma p2_add (a b c e : ℤ) : p2 a b + p2 c e = p2 (a + c) (b + e) := by
  funext i
  by_cases hi : i = 0 <;> simp [p2, hi]

lemma p2_sub (a b c e : ℤ) : p2 a b - p2 c e = p2 (a - c) (b - e) := by
  funext i
  by_cases hi : i = 0 <;> simp [p2, hi]

/-- The direction `u = (1,0)`. -/
def u10 : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

@[simp] lemma u10_zero : u10 0 = 1 := by simp [u10]
lemma u10_one : u10 1 = 0 := by simp [u10, show (1 : Fin 2) ≠ 0 from by decide]

lemma dot_u10 (x : Site 2) : dot u10 x = (x 0 : ℝ) := by
  rw [dot, Fin.sum_univ_two]
  simp [u10_zero, u10_one]

@[simp] lemma dot_u10_p2 (a b : ℤ) : dot u10 (p2 a b) = (a : ℝ) := by
  rw [dot_u10, p2_zero]

lemma uNormSq_u10 : uNormSq u10 = 1 := by
  rw [uNormSq, Fin.sum_univ_two]
  simp [u10_zero, u10_one]

lemma p2_inj {a b a' b' : ℤ} (h : p2 a b = p2 a' b') : a = a' ∧ b = b' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [p2_zero] at h0
  simp only [p2, show (1 : Fin 2) ≠ 0 from by decide, ite_false] at h1
  exact ⟨h0, h1⟩

/-- The vertical part `{(0,1), …, (0,n)}` of the ball. -/
def verts (n : ℕ) : Finset (Site 2) := (Finset.Icc (1 : ℤ) n).image (fun a => p2 0 a)

/-- The ball `B_n = {(1,0)} ∪ {(0,1), …, (0,n)}`. -/
def ball (n : ℕ) : Finset (Site 2) := insert (p2 1 0) (verts n)

lemma mem_verts_iff {n : ℕ} {a b : ℤ} :
    p2 a b ∈ verts n ↔ a = 0 ∧ b ∈ Finset.Icc (1 : ℤ) n := by
  rw [verts, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, hce⟩
    obtain ⟨h1, h2⟩ := p2_inj hce
    exact ⟨h1.symm, h2 ▸ hc⟩
  · rintro ⟨rfl, hb⟩
    exact ⟨b, hb, rfl⟩

lemma one_not_mem_verts {n : ℕ} : p2 1 0 ∉ verts n := by
  rw [mem_verts_iff]
  exact fun h => one_ne_zero h.1

lemma card_verts (n : ℕ) : (verts n).card = n := by
  rw [verts, Finset.card_image_of_injOn, Int.card_Icc]
  · omega
  · intro a _ b _ hab
    exact (p2_inj hab).2

lemma card_ball (n : ℕ) : (ball n).card = n + 1 := by
  rw [ball, Finset.card_insert_of_notMem one_not_mem_verts, card_verts]

lemma sum_ball {n : ℕ} (f : Site 2 → ℝ) :
    ∑ y ∈ ball n, f y = f (p2 1 0) + ∑ a ∈ Finset.Icc (1 : ℤ) n, f (p2 0 a) := by
  rw [ball, Finset.sum_insert one_not_mem_verts, verts,
    Finset.sum_image (g := fun a : ℤ => p2 0 a)
      (by intro a _ b _ hab; exact (p2_inj hab).2)]

/-! ## The model data -/

/-- Trivial sample space: the deterministic weight `w = 1` is a probability weight. -/
def Ww : PUnit → ℝ := fun _ => 1

/-- Single-point cluster `K = {(1,0)}`, independent of the configuration. -/
def WK : PUnit → Finset (Site 2) := fun _ => {p2 1 0}

/-- Restored cluster of `y`: `K_y = {y + (1,0)}`. -/
def WKy : Site 2 → PUnit → Finset (Site 2) := fun y _ => {y + p2 1 0}

lemma Ww_nonneg : ∀ ω, 0 ≤ Ww ω := fun _ => zero_le_one

lemma Ww_sum : ∑ ω : PUnit, Ww ω = 1 := by simp [Ww]

lemma ex_punit (X : PUnit → ℝ) : ex Ww X = X ⟨⟩ := by simp [ex, Ww]

lemma mem_WK {y : Site 2} {ω : PUnit} : y ∈ WK ω ↔ y = p2 1 0 := by
  simp [WK]

lemma id_ball {n : ℕ} : p2 1 0 ∈ ball n := by
  rw [ball]; exact Finset.mem_insert_self _ _

lemma vert_not_mem_WK {a : ℤ} {ω : PUnit} : p2 0 a ∉ WK ω := by
  rw [mem_WK]
  intro h
  exact absurd (p2_inj h).1 (by norm_num)

/-! ### The elementary cell values -/

lemma kcard_WK (ω : PUnit) : kcard WK ω = 1 := by simp [kcard, WK]

lemma kap_WK_ball (n : ℕ) (ω : PUnit) : kap WK (ball n) ω = 1 := by
  have h : ({p2 1 0} : Finset (Site 2)) ⊆ ball n := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx, ball]
    exact Finset.mem_insert_self _ _
  have hinter : ({p2 1 0} : Finset (Site 2)) ∩ ball n = {p2 1 0} :=
    Finset.inter_eq_left.mpr h
  simp [kap, WK, hinter]

lemma kS_WK (ω : PUnit) : kS u10 WK ω = 1 := by
  simp [kS, sMoment, q, WK, dot_u10_p2]

lemma kDot_WK (ω : PUnit) : kDot u10 WK ω = 1 := by
  simp [kDot, WK, dot_u10_p2]

lemma kcard_WKy (y : Site 2) (ω : PUnit) : kcard (WKy y) ω = 1 := by
  simp [kcard, WKy]

lemma sum_WKy (a : ℤ) (ω : PUnit) :
    ∑ z ∈ WKy (p2 0 a) ω, dot u10 (z - p2 0 a) = 1 := by
  have hz : WKy (p2 0 a) ω = {p2 1 a} := by
    simp only [WKy]
    congr 1
    funext i
    by_cases hi : i = 0
    · simp only [p2, hi, Pi.add_apply]
      norm_num
    · simp only [p2, hi, Pi.add_apply]
      norm_num
  rw [hz, Finset.sum_singleton, p2_sub, dot_u10_p2]
  norm_num

/-! ### The four remainders at the ball's two kinds of sites -/

@[simp] lemma vert_ne_id (a : ℤ) : p2 0 a ≠ p2 1 0 :=
  fun h => absurd (p2_inj h).1 (by norm_num)

@[simp] lemma id_eq_p2_iff {a b : ℤ} : p2 1 0 = p2 a b ↔ a = 1 ∧ b = 0 := by
  constructor
  · intro h
    exact p2_inj h.symm
  · rintro ⟨rfl, rfl⟩
    rfl

lemma T0_id : ex Ww (T0 u10 WK WKy (p2 1 0)) = 0 := by
  rw [ex_punit]
  simp [T0, restW, indOut, WK, kcard_WK, kcard_WKy]

lemma T0_vert (a : ℤ) : ex Ww (T0 u10 WK WKy (p2 0 a)) = 0 := by
  rw [ex_punit]
  simp [T0, restW, indOut, WK, kcard_WK, kcard_WKy, q, dot_u10]

lemma T2_id : ex Ww (T2 u10 WK WKy (p2 1 0)) = 0 := by
  rw [ex_punit]
  simp [T2, pairW, indOut, WK, kcard_WKy, kS_WK]

lemma T2_vert (a : ℤ) : ex Ww (T2 u10 WK WKy (p2 0 a)) = 1 := by
  rw [ex_punit]
  simp [T2, pairW, indOut, WK, kcard_WKy, kS_WK]

lemma T3_id : ex Ww (T3 u10 WK WKy (p2 1 0)) = 0 := by
  rw [ex_punit]
  simp [T3, indOut, WK, kDot_WK]

lemma T3_vert (a : ℤ) : ex Ww (T3 u10 WK WKy (p2 0 a)) = 1 := by
  rw [ex_punit]
  simp [T3, indOut, WK, kDot_WK, sum_WKy]

lemma T4_id : ex Ww (T4 u10 WK WKy (p2 1 0)) = 0 := by
  rw [ex_punit]
  simp [T4, indOut, WK, kcard_WKy, kDot_WK]

lemma T4_vert (a : ℤ) : ex Ww (T4 u10 WK WKy (p2 0 a)) = 0 := by
  rw [ex_punit]
  simp [T4, indOut, WK, kcard_WKy, kDot_WK, dot_u10]

/-! ### The ball sums -/

lemma sum_one_Icc (n : ℕ) : ∑ _a ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 : ℝ) = (n : ℝ) := by
  rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
  have : ((n : ℤ) + 1 - 1).toNat = n := by omega
  rw [this, mul_one]

lemma sum_T0_ball (n : ℕ) : ∑ y ∈ ball n, ex Ww (T0 u10 WK WKy y) = 0 := by
  rw [sum_ball, T0_id]
  simp only [zero_add]
  refine Finset.sum_eq_zero fun a _ => T0_vert a

lemma sum_T2_ball (n : ℕ) : ∑ y ∈ ball n, ex Ww (T2 u10 WK WKy y) = (n : ℝ) := by
  rw [sum_ball, T2_id, zero_add]
  exact (Finset.sum_congr rfl fun a _ => T2_vert a).trans (sum_one_Icc n)

lemma sum_T3_ball (n : ℕ) : ∑ y ∈ ball n, ex Ww (T3 u10 WK WKy y) = (n : ℝ) := by
  rw [sum_ball, T3_id, zero_add]
  exact (Finset.sum_congr rfl fun a _ => T3_vert a).trans (sum_one_Icc n)

lemma sum_T4_ball (n : ℕ) : ∑ y ∈ ball n, ex Ww (T4 u10 WK WKy y) = 0 := by
  rw [sum_ball, T4_id]
  simp only [zero_add]
  refine Finset.sum_eq_zero fun a _ => T4_vert a

/-! ### The model quantities `U`, `G`, `Gq` -/

lemma sum_q_ball (n : ℕ) : ∑ y ∈ ball n, q u10 y = 1 := by
  rw [sum_ball]
  have hzero : ∑ a ∈ Finset.Icc (1 : ℤ) (n : ℤ), q u10 (p2 0 a) = 0 :=
    Finset.sum_eq_zero fun a _ => by
      simp [q, dot_u10]
  rw [hzero, add_zero]
  simp [q, dot_u10]

lemma U_val (n : ℕ) :
    uNormSq u10 * (1 : ℝ) ^ 2 * ex Ww (fun ω => (kcard WK ω) ^ 2 * kap WK (ball n) ω) = 1 := by
  rw [uNormSq_u10, ex_punit]
  simp [kcard_WK, kap_WK_ball]

lemma G_val (n : ℕ) :
    ex Ww (fun ω => kcard WK ω * kap WK (ball n) ω * kS u10 WK ω) = 1 := by
  rw [ex_punit]
  simp [kcard_WK, kap_WK_ball, kS_WK]

lemma Gq_val (n : ℕ) :
    ex Ww (fun ω => (kcard WK ω) ^ 2 * sMoment u10 (WK ω ∩ ball n)) = 1 := by
  have h : WK (⟨⟩ : PUnit) ∩ ball n = {p2 1 0} := by
    simp [WK, id_ball]
  rw [ex_punit, h, kcard_WK]
  simp [sMoment, q, dot_u10]

/-! ### `derivTerm` and `mainTerm` in the test family -/

lemma ex_kcard_WK : ex Ww (kcard WK) = 1 := by
  rw [ex_punit]; simp [kcard_WK]

lemma ex_kS_WK : ex Ww (kS u10 WK) = 1 := by
  rw [ex_punit]; simp [kS_WK]

theorem derivTerm_val (n : ℕ) : derivTerm Ww u10 WK WKy (ball n) = 0 := by
  simp only [derivTerm, sum_T0_ball, sum_T2_ball, sum_T3_ball, sum_T4_ball]
  ring

theorem mainTerm_val (n : ℕ) : mainTerm Ww u10 WK (ball n) = 2 * (n : ℝ) + 3 := by
  simp only [mainTerm, ex_kcard_WK, ex_kS_WK, sum_q_ball, card_ball]
  push_cast
  ring

/-- The bare per-site AM-GM halves of the `T3` estimate, summed over the ball.
They are *tight* here: each equals `n`. -/
lemma sum_pairW_ball (n : ℕ) :
    ∑ y ∈ ball n, ex Ww (pairW u10 WK WKy y) = (n : ℝ) := by
  have hid : ex Ww (pairW u10 WK WKy (p2 1 0)) = 0 := by
    rw [ex_punit]; simp [pairW, indOut, WK, kcard_WKy, kS_WK]
  have hvert : ∀ a : ℤ, ex Ww (pairW u10 WK WKy (p2 0 a)) = 1 := by
    intro a
    rw [ex_punit]; simp [pairW, indOut, WK, kcard_WKy, kS_WK]
  rw [sum_ball, hid, zero_add]
  exact (Finset.sum_congr rfl fun a _ => hvert a).trans (sum_one_Icc n)

lemma sum_pairQ_ball (n : ℕ) :
    ∑ y ∈ ball n, ex Ww (pairQ u10 WK WKy y) = (n : ℝ) := by
  have hid : ex Ww (pairQ u10 WK WKy (p2 1 0)) = 0 := by
    rw [ex_punit]; simp [pairQ, indOut, WK, kcard_WK]
  have hvert : ∀ a : ℤ, ex Ww (pairQ u10 WK WKy (p2 0 a)) = 1 := by
    intro a
    rw [ex_punit]
    simp [pairQ, indOut, WK, WKy, kcard_WK, q, dot_u10]
  rw [sum_ball, hid, zero_add]
  exact (Finset.sum_congr rfl fun a _ => hvert a).trans (sum_one_Icc n)

/-! ### The five hypotheses of the assembly in the test family

With `r = 1` and `n ≥ 1`: `hR0`, `hR2`, `hR4`, `hGq` hold, `G = U = Gq = 1`,
but `hR3` — the displayed `(1/2) G` estimate on `T3` — fails as soon as `n ≥ 1`,
and the assembly conclusion `3U + 5G` fails as soon as `n ≥ 3`. -/

theorem hR0_holds (n : ℕ) :
    |(∑ y ∈ ball n, ex Ww (T0 u10 WK WKy y)) -
        (ex Ww (kcard WK)) ^ 2 * (∑ y ∈ ball n, q u10 y)|
      ≤ uNormSq u10 * (1 : ℝ) ^ 2
          * ex Ww (fun ω => (kcard WK ω) ^ 2 * kap WK (ball n) ω) := by
  rw [sum_T0_ball, sum_q_ball, ex_kcard_WK, U_val]
  norm_num

theorem hR2_holds (n : ℕ) :
    |(∑ y ∈ ball n, ex Ww (T2 u10 WK WKy y)) -
        ((ball n).card : ℝ) * (ex Ww (kcard WK)) * (ex Ww (kS u10 WK))|
      ≤ ex Ww (fun ω => kcard WK ω * kap WK (ball n) ω * kS u10 WK ω) := by
  rw [sum_T2_ball, ex_kcard_WK, ex_kS_WK, G_val, card_ball]
  rw [abs_le]
  constructor <;> push_cast <;> linarith [Nat.cast_nonneg (α := ℝ) n]

theorem hR4_holds (n : ℕ) :
    |(∑ y ∈ ball n, ex Ww (T4 u10 WK WKy y))|
      ≤ (1 / 2) * ex Ww (fun ω => kcard WK ω * kap WK (ball n) ω * kS u10 WK ω)
        + (1 / 2) * ex Ww (fun ω => (kcard WK ω) ^ 2 * sMoment u10 (WK ω ∩ ball n)) := by
  rw [sum_T4_ball, G_val, Gq_val, abs_zero]
  linarith

theorem hGq_holds (n : ℕ) :
    ex Ww (fun ω => (kcard WK ω) ^ 2 * sMoment u10 (WK ω ∩ ball n))
      ≤ uNormSq u10 * (1 : ℝ) ^ 2
          * ex Ww (fun ω => (kcard WK ω) ^ 2 * kap WK (ball n) ω) := by
  rw [Gq_val, U_val]

/-- **The printed `(1/2) G` estimate on `T3` fails** in the bare model: here the sum
equals `n` while `G = 1`. -/
theorem hR3_fails (n : ℕ) (hn : 1 ≤ n) :
    ¬ (|∑ y ∈ ball n, ex Ww (T3 u10 WK WKy y)|
        ≤ (1 / 2) * ex Ww (fun ω => kcard WK ω * kap WK (ball n) ω * kS u10 WK ω)) := by
  rw [sum_T3_ball, G_val]
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  intro h
  linarith

/-- The same data also violate the coefficient `1` version `|sum T3| <= G`. -/
theorem T3_coeff_one_fails (n : ℕ) (hn : 2 ≤ n) :
    ¬ (|∑ y ∈ ball n, ex Ww (T3 u10 WK WKy y)|
        ≤ ex Ww (fun ω => kcard WK ω * kap WK (ball n) ω * kS u10 WK ω)) := by
  rw [sum_T3_ball, G_val]
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  intro h
  linarith

/-- The assembly conclusion with the displayed constants `3U + 5G` fails. -/
theorem assembly_bound_fails (n : ℕ) (hn : 3 ≤ n) :
    ¬ (|derivTerm Ww u10 WK WKy (ball n) - mainTerm Ww u10 WK (ball n)|
      ≤ 3 * (uNormSq u10 * (1 : ℝ) ^ 2
            * ex Ww (fun ω => (kcard WK ω) ^ 2 * kap WK (ball n) ω))
        + 5 * ex Ww (fun ω => kcard WK ω * kap WK (ball n) ω * kS u10 WK ω)) := by
  rw [derivTerm_val, mainTerm_val, U_val, G_val, zero_sub, abs_neg,
    abs_of_nonneg (by positivity)]
  have hn' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  intro h
  linarith

/-- Even the sharpened `3U + 6G` conclusion fails in the bare model (from `n = 4` on),
which is why `T3_bound_global` needs `hgap` and the translation symmetries. -/
theorem assembly_bound_six_fails (n : ℕ) (hn : 4 ≤ n) :
    ¬ (|derivTerm Ww u10 WK WKy (ball n) - mainTerm Ww u10 WK (ball n)|
      ≤ 3 * (uNormSq u10 * (1 : ℝ) ^ 2
            * ex Ww (fun ω => (kcard WK ω) ^ 2 * kap WK (ball n) ω))
        + 6 * ex Ww (fun ω => kcard WK ω * kap WK (ball n) ω * kS u10 WK ω)) := by
  rw [derivTerm_val, mainTerm_val, U_val, G_val, zero_sub, abs_neg,
    abs_of_nonneg (by positivity)]
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  intro h
  linarith

/-- **No constant bound on `T3` holds in the bare model.**  For every proposed
constant `C` there is a ball size with `|sum T3| > C * G`; the sum is `n` while `G`
stays equal to `1`. -/
theorem no_constant_T3_bound (C : ℝ) :
    ∃ n : ℕ, C * ex Ww (fun ω => kcard WK ω * kap WK (ball n) ω * kS u10 WK ω)
      < |∑ y ∈ ball n, ex Ww (T3 u10 WK WKy y)| := by
  refine ⟨⌊C⌋₊ + 1, ?_⟩
  rw [G_val, sum_T3_ball, mul_one,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((⌊C⌋₊ + 1 : ℕ) : ℝ)))]
  have h := Nat.lt_floor_add_one C
  push_cast at h ⊢
  linarith

/-- The structure of the failure: the per-site AM-GM bound is tight, but the two
halves sum to `n` each instead of to `G = 1`, i.e. the mass-transport
identification `sum pairW = G` (the hypothesis `hmt1` of `sum_of_halves_first`) is
exactly what fails. -/
theorem mass_transport_identification_fails (n : ℕ) (hn : 2 ≤ n) :
    ¬ (∑ y ∈ ball n, ex Ww (pairW u10 WK WKy y)
        = ex Ww (fun ω => kcard WK ω * kap WK (ball n) ω * kS u10 WK ω)) := by
  rw [sum_pairW_ball, G_val]
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  intro h
  linarith

/-! ### The four hypotheses as predicates, and the separation certificates -/

/-- The displayed `T0` remainder estimate (`hR0`). -/
noncomputable def HR0 (u : Fin 2 → ℝ) (K : PUnit → Finset (Site 2))
    (Ky : Site 2 → PUnit → Finset (Site 2)) (B : Finset (Site 2)) (r : ℝ) : Prop :=
  |(∑ y ∈ B, ex Ww (T0 u K Ky y)) - (ex Ww (kcard K)) ^ 2 * (∑ y ∈ B, q u y)|
    ≤ uNormSq u * r ^ 2 * ex Ww (fun ω => (kcard K ω) ^ 2 * kap K B ω)

/-- The displayed `T2` remainder estimate (`hR2`). -/
noncomputable def HR2 (u : Fin 2 → ℝ) (K : PUnit → Finset (Site 2))
    (Ky : Site 2 → PUnit → Finset (Site 2)) (B : Finset (Site 2)) : Prop :=
  |(∑ y ∈ B, ex Ww (T2 u K Ky y)) - (B.card : ℝ) * (ex Ww (kcard K)) * (ex Ww (kS u K))|
    ≤ ex Ww (fun ω => kcard K ω * kap K B ω * kS u K ω)

/-- The printed `T3` estimate, with the source's extra `1/2`. -/
noncomputable def HR3 (u : Fin 2 → ℝ) (K : PUnit → Finset (Site 2))
    (Ky : Site 2 → PUnit → Finset (Site 2)) (B : Finset (Site 2)) : Prop :=
  |∑ y ∈ B, ex Ww (T3 u K Ky y)|
    ≤ (1 / 2) * ex Ww (fun ω => kcard K ω * kap K B ω * kS u K ω)

/-- The `T3` estimate with coefficient `1`, which is what `sum_of_halves_first` and
`T3_bound_global` actually deliver. -/
noncomputable def HR3one (u : Fin 2 → ℝ) (K : PUnit → Finset (Site 2))
    (Ky : Site 2 → PUnit → Finset (Site 2)) (B : Finset (Site 2)) : Prop :=
  |∑ y ∈ B, ex Ww (T3 u K Ky y)|
    ≤ ex Ww (fun ω => kcard K ω * kap K B ω * kS u K ω)

/-- The displayed `T4` remainder estimate (`hR4`). -/
noncomputable def HR4 (u : Fin 2 → ℝ) (K : PUnit → Finset (Site 2))
    (Ky : Site 2 → PUnit → Finset (Site 2)) (B : Finset (Site 2)) : Prop :=
  |∑ y ∈ B, ex Ww (T4 u K Ky y)|
    ≤ (1 / 2) * ex Ww (fun ω => kcard K ω * kap K B ω * kS u K ω)
      + (1 / 2) * ex Ww (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B))

/-- The displayed `Gq <= U` estimate (`hGq`). -/
noncomputable def HGq (u : Fin 2 → ℝ) (K : PUnit → Finset (Site 2)) (B : Finset (Site 2)) : Prop :=
  ex Ww (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B))
    ≤ uNormSq u * (1 : ℝ) ^ 2 * ex Ww (fun ω => (kcard K ω) ^ 2 * kap K B ω)

lemma HR0_holds' (n : ℕ) : HR0 u10 WK WKy (ball n) 1 := hR0_holds n
lemma HR2_holds' (n : ℕ) : HR2 u10 WK WKy (ball n) := hR2_holds n
lemma HR4_holds' (n : ℕ) : HR4 u10 WK WKy (ball n) := hR4_holds n
lemma HGq_holds' (n : ℕ) : HGq u10 WK (ball n) := hGq_holds n
lemma HR3_fails' (n : ℕ) (hn : 1 ≤ n) : ¬ HR3 u10 WK WKy (ball n) := hR3_fails n hn
lemma HR3one_fails' (n : ℕ) (hn : 2 ≤ n) : ¬ HR3one u10 WK WKy (ball n) :=
  T3_coeff_one_fails n hn

/-- **Separation of the printed `1/2`.**  `hR0`, `hR2`, `hR4`, `hGq` do not imply
the printed `T3` estimate `|sum T3| <= (1/2) G` in the bare weighted model of
`lemma_I_5_8_assembly`: the ball `B_3` of the test family satisfies all four and
violates `hR3` (`|sum T3| = 3`, `G = 1`). -/
theorem printed_half_separated :
    HR0 u10 WK WKy (ball 3) 1 ∧ HR2 u10 WK WKy (ball 3) ∧ HR4 u10 WK WKy (ball 3) ∧
      HGq u10 WK (ball 3) ∧ ¬ HR3 u10 WK WKy (ball 3) :=
  ⟨HR0_holds' 3, HR2_holds' 3, HR4_holds' 3, HGq_holds' 3, HR3_fails' 3 (by norm_num)⟩

/-- **The coefficient `1` is not available either**, so the printed `1/2` is not a
mere constant slip that algebra could repair: even `|sum T3| <= G` fails on the same
data (`B_2` and above), and no constant works at all (`no_constant_T3_bound`). -/
theorem coeff_one_separated : ¬ HR3one u10 WK WKy (ball 2) := HR3one_fails' 2 (by norm_num)

/-- **The assembly conclusion `3U + 5G` is not a consequence of `hR0, hR2, hR4, hGq`.**
(The witness has `|derivTerm - mainTerm| = 9` and `3U + 5G = 8`.) -/
theorem assembly_five_separated :
    HR0 u10 WK WKy (ball 3) 1 ∧ HR2 u10 WK WKy (ball 3) ∧ HR4 u10 WK WKy (ball 3) ∧
      HGq u10 WK (ball 3) ∧
      ¬ (|derivTerm Ww u10 WK WKy (ball 3) - mainTerm Ww u10 WK (ball 3)|
        ≤ 3 * (uNormSq u10 * (1 : ℝ) ^ 2
              * ex Ww (fun ω => (kcard WK ω) ^ 2 * kap WK (ball 3) ω))
          + 5 * ex Ww (fun ω => kcard WK ω * kap WK (ball 3) ω * kS u10 WK ω)) :=
  ⟨HR0_holds' 3, HR2_holds' 3, HR4_holds' 3, HGq_holds' 3,
    assembly_bound_fails 3 (by norm_num)⟩

/-- **The sharpened conclusion `3U + 6G` also needs more than the four hypotheses**:
on `B_4` it fails, so the covariance-gap input `hgap` (with the translation
symmetries) used by `T3_bound_global` cannot be dropped. -/
theorem assembly_six_separated :
    HR0 u10 WK WKy (ball 4) 1 ∧ HR2 u10 WK WKy (ball 4) ∧ HR4 u10 WK WKy (ball 4) ∧
      HGq u10 WK (ball 4) ∧
      ¬ (|derivTerm Ww u10 WK WKy (ball 4) - mainTerm Ww u10 WK (ball 4)|
        ≤ 3 * (uNormSq u10 * (1 : ℝ) ^ 2
              * ex Ww (fun ω => (kcard WK ω) ^ 2 * kap WK (ball 4) ω))
          + 6 * ex Ww (fun ω => kcard WK ω * kap WK (ball 4) ω * kS u10 WK ω)) :=
  ⟨HR0_holds' 4, HR2_holds' 4, HR4_holds' 4, HGq_holds' 4,
    assembly_bound_six_fails 4 (by norm_num)⟩

/-- **Redundancy test, negative result.**  In the bare model the printed `1/2` is not
recoverable from `hgap`-free data even for a single site: the identity
`sum_y E[pairW_y] = G`, which is the `hmt1` input of `sum_of_halves_first` and
`T3_bound_global`, fails on `B_2` while `hR0`, `hR2`, `hR4`, `hGq` hold.  So the
coefficient `1` (let alone `1/2`) is carried by the mass-transport / disjoint-occurrence
layer, not by the algebraic layer. -/
theorem mass_transport_separated :
    HR0 u10 WK WKy (ball 2) 1 ∧ HR2 u10 WK WKy (ball 2) ∧ HR4 u10 WK WKy (ball 2) ∧
      HGq u10 WK (ball 2) ∧
      ¬ (∑ y ∈ ball 2, ex Ww (pairW u10 WK WKy y)
          = ex Ww (fun ω => kcard WK ω * kap WK (ball 2) ω * kS u10 WK ω)) :=
  ⟨HR0_holds' 2, HR2_holds' 2, HR4_holds' 2, HGq_holds' 2,
    mass_transport_identification_fails 2 (by norm_num)⟩



/-! ### Redundancy: the printed `1/2` is stronger than the coefficient `1` -/

/-- `G` is nonnegative for a nonnegative weight. -/
lemma G_nonneg {d : ℕ} {Ω : Type*} [Fintype Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (B : Finset (Site d)) :
    0 ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  refine ex_nonneg hw fun ω => ?_
  have h1 : (0 : ℝ) ≤ kcard K ω := by simp [kcard]
  have h2 : (0 : ℝ) ≤ kap K B ω := by simp [kap]
  have h3 : (0 : ℝ) ≤ kS u K ω := sMoment_nonneg u (K ω)
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-- The printed `(1/2) G` estimate implies the coefficient `1` estimate. -/
theorem HR3_implies_HR3one (u : Fin 2 → ℝ) (K : PUnit → Finset (Site 2))
    (Ky : Site 2 → PUnit → Finset (Site 2)) (B : Finset (Site 2))
    (hG : 0 ≤ ex Ww (fun ω => kcard K ω * kap K B ω * kS u K ω))
    (h : HR3 u K Ky B) : HR3one u K Ky B := by
  refine h.trans ?_
  have : (0 : ℝ) ≤ (1 / 2) * ex Ww (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
    linarith
  nlinarith

/-- **Redundancy finding.**  The printed hypothesis `hR3` (coefficient `1/2`) yields the
conclusion of the assembly with `6G` as well as the displayed `5G`: the printed estimate
is strictly stronger than the hypothesis actually used by `T3_bound_global`
(coefficient `1`).  Hence `3U + 5G` is not a sharper conclusion — it is the same
conclusion drawn from a stronger input. -/
theorem assembly_six_of_printed_half
    (u : Fin 2 → ℝ) (K : PUnit → Finset (Site 2))
    (Ky : Site 2 → PUnit → Finset (Site 2)) (B : Finset (Site 2))
    (h0 : HR0 u K Ky B 1) (h2 : HR2 u K Ky B) (h3 : HR3 u K Ky B)
    (h4 : HR4 u K Ky B) (h5 : HGq u K B) :
    |derivTerm Ww u K Ky B - mainTerm Ww u K B|
      ≤ 3 * (uNormSq u * (1 : ℝ) ^ 2
            * ex Ww (fun ω => (kcard K ω) ^ 2 * kap K B ω))
        + 6 * ex Ww (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  have hG : 0 ≤ ex Ww (fun ω => kcard K ω * kap K B ω * kS u K ω) :=
    G_nonneg Ww_nonneg u K B
  have h3' : HR3one u K Ky B := HR3_implies_HR3one u K Ky B hG h3
  have := PercLib.CriticalLRP.I58.abs_assembly_global
    ((∑ y ∈ B, ex Ww (T0 u K Ky y)) - (ex Ww (kcard K)) ^ 2 * (∑ y ∈ B, q u y))
    ((∑ y ∈ B, ex Ww (T2 u K Ky y))
      - (B.card : ℝ) * (ex Ww (kcard K)) * (ex Ww (kS u K)))
    (∑ y ∈ B, ex Ww (T3 u K Ky y))
    (∑ y ∈ B, ex Ww (T4 u K Ky y))
    (uNormSq u * (1 : ℝ) ^ 2 * ex Ww (fun ω => (kcard K ω) ^ 2 * kap K B ω))
    (ex Ww (fun ω => kcard K ω * kap K B ω * kS u K ω))
    (ex Ww (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)))
    h0 h2 h3' h4 h5
  rw [derivTerm_sub_mainTerm]
  exact this





/-! ### Strictness: coefficient `1` does not imply the printed `1/2`

At `n = 1` the test family has `|sum T3| = 1 = G`, so the coefficient-`1` estimate
holds while the printed `(1/2) G` fails. -/

theorem coeff_one_holds_one : HR3one u10 WK WKy (ball 1) := by
  show |∑ y ∈ ball 1, ex Ww (T3 u10 WK WKy y)|
      ≤ ex Ww (fun ω => kcard WK ω * kap WK (ball 1) ω * kS u10 WK ω)
  rw [sum_T3_ball, G_val]
  norm_num

/-- **The printed `1/2` is strictly stronger than the coefficient `1`.**  On `B_1` all
four of `hR0, hR2, hR4, hGq` hold and `|sum T3| = G = 1`: the coefficient-`1` estimate
is true and the printed `(1/2) G` estimate is false.  Together with
`HR3_implies_HR3one` this pins the logical relation between the two forms. -/
theorem half_strictly_stronger :
    HR0 u10 WK WKy (ball 1) 1 ∧ HR2 u10 WK WKy (ball 1) ∧ HR4 u10 WK WKy (ball 1) ∧
      HGq u10 WK (ball 1) ∧ HR3one u10 WK WKy (ball 1) ∧ ¬ HR3 u10 WK WKy (ball 1) :=
  ⟨HR0_holds' 1, HR2_holds' 1, HR4_holds' 1, HGq_holds' 1, coeff_one_holds_one,
    HR3_fails' 1 (by norm_num)⟩









/-! ### Sharpness of the coefficient `1` within the paper's own chain

At `n = 1` both mass-transport identifications hold and the per-site AM-GM is tight,
so the chain "AM-GM + both transported halves" gives exactly `G` — attained.  Hence no
refinement of that chain can produce the printed `(1/2) G`. -/

theorem halves_tight :
    (∑ y ∈ ball 1, ex Ww (pairW u10 WK WKy y))
        = ex Ww (fun ω => kcard WK ω * kap WK (ball 1) ω * kS u10 WK ω) ∧
      (∑ y ∈ ball 1, ex Ww (pairQ u10 WK WKy y))
        = ex Ww (fun ω => kcard WK ω * kap WK (ball 1) ω * kS u10 WK ω) ∧
      |∑ y ∈ ball 1, ex Ww (T3 u10 WK WKy y)|
        = ex Ww (fun ω => kcard WK ω * kap WK (ball 1) ω * kS u10 WK ω) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sum_pairW_ball, G_val]; norm_num
  · rw [sum_pairQ_ball, G_val]; norm_num
  · rw [sum_T3_ball, G_val]
    norm_num






namespace PercLib.CriticalLRP.I58

#print axioms derivTerm_val
#print axioms mainTerm_val
#print axioms hR0_holds
#print axioms hR2_holds
#print axioms hR4_holds
#print axioms hGq_holds
#print axioms hR3_fails
#print axioms T3_coeff_one_fails
#print axioms assembly_bound_fails
#print axioms assembly_bound_six_fails
#print axioms no_constant_T3_bound
#print axioms mass_transport_identification_fails
#print axioms printed_half_separated
#print axioms coeff_one_separated
#print axioms assembly_five_separated
#print axioms assembly_six_separated
#print axioms mass_transport_separated
#print axioms G_nonneg
#print axioms HR3_implies_HR3one
#print axioms assembly_six_of_printed_half
#print axioms coeff_one_holds_one
#print axioms half_strictly_stronger
#print axioms halves_tight

end PercLib.CriticalLRP.I58
