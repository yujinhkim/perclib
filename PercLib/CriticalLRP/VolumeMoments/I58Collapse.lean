/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Lemma I.5.8 of T. Hutchcroft, *Critical long-range percolation I*
(arXiv:2508.18807v1): the six-term trinomial collapse to `eq:x12_derivative`
/ (I.5.3), written as a **raw four-term + defect decomposition**.

Source audited against the local TeX `.scratch/i52/source/Zd_renormalizationHD.tex`
lines 2749--2840 and `.scratch/tom1.txt` lines 3287--3370 (Lemma I.5.8, proof).

## The source's step

The proof writes the derivative of the quadratic spatial moment as

    ∑_{x ∈ K} ∑_{y ∈ B_r} 1(y ∉ K) ∑_{z ∈ K_y} ⟪z - x, u⟫²

substitutes `z - x = (z - y) + (y - 0) + (0 - x)`, expands into **six** terms,
and then says

> "Using the mass-transport principle again to exchange the roles of `0` and `y`
>  we see that some of these terms are equal"

printing **four** terms with the coefficient pattern `1, 2, -2, -4` (the paper's
(I.5.3)).  Writing the six terms of the expansion as

    A + B + C + 2D - 2E - 2F

(`A = S1`, `B = S2`, `C = S3`, `2D = S4`, `-2E = S5`, `-2F = S6`) the printed four
are `A + 2C - 2E - 4F`, so the arithmetic residue is `B - C + 2D + 2F`:
the source needs the two expectation-level comparisons

    (BC)  E B = E C        (DF)  E D = - E F .

## What is proved here

* `sum_sum_q_sub_eq`: the exact six-term expansion of the summed integrand, from
  `QuadraticMerge`'s `sq_sub_eq_trinomial`.
* `six_term_collapse`: the per-site identity exhibiting `1, 2, -2, -4` plus the
  residue.
* `rawRusso_eq`: the exact decomposition
  `rawRusso = paperFour + exchangeDefect`.
* `exchangeDefect_eq_comparisons`: **the defect is exactly the source's residue**,
  `exchangeDefect = Bfun - Cfun + 2·Dfun + 2·Ffun`, and
  `ex_exchangeDefect_eq_comparisons` puts this at expectation level.
* `collapse_of_comparisons`: the two comparisons `(BC)` and `(DF)` **imply** the
  collapse, i.e. they discharge `hExchange`; `collapse_iff_comparisons` is the
  exact form.  This file does **not** prove `(BC)` or `(DF)`, and does not claim
  they fail: they are isolated here as the two named expectation-level inputs.
* `abs_exchangeDefect_le`: a crude nonnegative domination of the defect.

No `sorry`, no `admit`, no custom axioms, no `native_decide`.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.I58Remainder
public import PercLib.CriticalLRP.VolumeMoments.QuadraticMerge

set_option autoImplicit true

@[expose] public section

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PercLib.CriticalLRP.I58

variable {d : ℕ}

/-! ## 0. The weight re-centred at `y`

Kept as opaque definitions so that `q u (x - y)` is a single syntactic atom; this
avoids the `x - y` / `-y + x` normal-form clash in the `ring` steps below. -/

/-- `q_u` re-centred at `y`: `x ↦ q_u(x - y)`. -/
noncomputable def qrel (u : Fin d → ℝ) (y x : Site d) : ℝ := q u (x - y)

/-- `⟪·,u⟫` re-centred at `y`: `x ↦ ⟪x - y, u⟫`. -/
noncomputable def drel (u : Fin d → ℝ) (y x : Site d) : ℝ := dot u (x - y)

theorem qrel_apply (u : Fin d → ℝ) (y x : Site d) : qrel u y x = q u (x - y) := rfl

theorem drel_apply (u : Fin d → ℝ) (y x : Site d) : drel u y x = dot u (x - y) := rfl

/-! ## 1. Two summed shift identities for the quadratic weight -/

/-- `q_u` re-anchored at `y`: `q_u(z) = q_u(z - y) + q_u(y) + 2⟪z-y,u⟫⟪y,u⟫`,
summed over a finite cluster.  Immediate from `q_add`. -/
theorem sum_q_shift (u : Fin d → ℝ) (C : Finset (Site d)) (y : Site d) :
    (∑ z ∈ C, q u z)
      = (∑ z ∈ C, qrel u y z) + (C.card : ℝ) * (dot u y * dot u y)
        + 2 * dot u y * (∑ z ∈ C, drel u y z) := by
  have hpt : ∀ z : Site d,
      q u z = qrel u y z + dot u y * dot u y + 2 * dot u y * drel u y z := by
    intro z
    have h := q_add u (z - y) y
    rw [sub_add_cancel] at h
    simp only [qrel, drel]
    rw [h]; simp only [q]; ring
  rw [Finset.sum_congr rfl (fun z _ => hpt z)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]

/-- `q_u(x - y) = q_u(x) + q_u(y) - 2⟪x,u⟫⟪y,u⟫`, summed over a finite cluster. -/
theorem sum_q_sub_shift (u : Fin d → ℝ) (A : Finset (Site d)) (y : Site d) :
    (∑ x ∈ A, qrel u y x)
      = (∑ x ∈ A, q u x) + (A.card : ℝ) * (dot u y * dot u y)
        - 2 * dot u y * (∑ x ∈ A, dot u x) := by
  have hpt : ∀ x : Site d,
      qrel u y x = q u x + dot u y * dot u y - 2 * dot u y * dot u x := by
    intro x; simp only [qrel, q, dot_sub]; ring
  rw [Finset.sum_congr rfl (fun x _ => hpt x)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]

/-! ## 2. The six-term trinomial expansion, summed over both clusters

With `a z = ⟪z - y, u⟫`, `b = ⟪y,u⟫`, `c x = ⟪x,u⟫` the source's substitution
`z - x = (z - y) + (y - 0) + (0 - x)` gives `(a + b - c)²`, expanded through
`QuadraticMerge.sq_sub_eq_trinomial`. -/

/-- **Six-term expansion, one site `x`.**  Summed over `z ∈ C` only. -/
theorem sum_q_sub_eq (u : Fin d → ℝ) (C : Finset (Site d)) (x y : Site d) :
    (∑ z ∈ C, q u (z - x))
      = (∑ z ∈ C, qrel u y z) + (C.card : ℝ) * q u y + (C.card : ℝ) * q u x
        + (-2) * ((C.card : ℝ) * (dot u y * dot u x))
        + 2 * (dot u y * (∑ z ∈ C, drel u y z))
        + (-2) * ((∑ z ∈ C, drel u y z) * dot u x) := by
  have hpt : ∀ z : Site d,
      q u (z - x) = qrel u y z + q u y + q u x + (-2) * (dot u y * dot u x)
        + 2 * (dot u y * drel u y z) + (-2) * (drel u y z * dot u x) := by
    intro z
    have h := PercLib.CriticalLRP.FiniteVolume.sq_sub_eq_trinomial
      (dot u z - dot u y) (dot u y) (dot u x)
    simp only [qrel, drel, q, dot_sub]
    linarith [h]
  rw [Finset.sum_congr rfl (fun z _ => hpt z)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- **Six-term expansion, both clusters.**  The exact form of the source's line
"Writing `z - x = (z - y) + (y - 0) + (0 - x)` and expanding out the product". -/
theorem sum_sum_q_sub_eq (u : Fin d → ℝ) (A C : Finset (Site d)) (y : Site d) :
    (∑ x ∈ A, ∑ z ∈ C, q u (z - x))
      = (A.card : ℝ) * (∑ z ∈ C, qrel u y z)
        + (A.card : ℝ) * ((C.card : ℝ) * q u y)
        + (C.card : ℝ) * (∑ x ∈ A, q u x)
        + (-2) * ((C.card : ℝ) * (dot u y * (∑ x ∈ A, dot u x)))
        + 2 * ((A.card : ℝ) * (dot u y * (∑ z ∈ C, drel u y z)))
        + (-2) * ((∑ z ∈ C, drel u y z) * (∑ x ∈ A, dot u x)) := by
  rw [Finset.sum_congr rfl (fun x _ => sum_q_sub_eq u C x y)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-! ## 3. The collapse: exact identity with an exchange defect -/

variable {Ω : Type*} [Fintype Ω]

/-- The Russo/perturbation integrand of `lem:gyration_derivative2` **before** any
collapse: for every `x` in the origin's cluster and every `y` in the ball, the whole
quadratic weight of the far cluster `K_y` measured from `x`. -/
noncomputable def rawRusso (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ y ∈ B, indOut K y ω * ∑ x ∈ K ω, ∑ z ∈ Ky y ω, q u (z - x)

/-- The paper's four-term right-hand side `(I.5.3)` per site, before summing over `y`. -/
noncomputable def fourSite (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => T0 u K Ky y ω + 2 * T2 u K Ky y ω - 2 * T3 u K Ky y ω - 4 * T4 u K Ky y ω

/-- The paper's four-term right-hand side `(I.5.3)`, as a function of the
configuration: `T0 + 2 T2 - 2 T3 - 4 T4` (coefficients `1, 2, -2, -4`). -/
noncomputable def paperFour (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ y ∈ B, fourSite u K Ky y ω

/-- **The exchange defect**: the exact difference between the six-term expansion and
the printed four-term form, in closed form (`qrel u y x` is definitionally `q u (x - y)`).
It is the raw two-cluster swap `|K| ∑_{K_y} q_u(·) − |K_y| ∑_K q_u(· − y)`; the `q_u(y)`
contributions of the two sides cancel identically (see `six_term_collapse`). -/
noncomputable def exchangeDefect (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ y ∈ B, indOut K y ω * ((kcard K ω) * (∑ z ∈ Ky y ω, q u z)
    - (kcard (Ky y) ω) * (∑ x ∈ K ω, qrel u y x))

/-- **The per-site collapse.**  One site's worth of the six-term expansion equals the
four-term form plus the exchange defect.  This is where the coefficient pattern
`1, 2, -2, -4` is *derived*: `T0` keeps coefficient `1`, `T2` is doubled, `T3` keeps
`-2`, `T4` is doubled to `-4`, and the residue is `|K| ∑_{K_y} q_u − |K_y| ∑_K q_u(·−y)`. -/
theorem six_term_collapse (u : Fin d → ℝ) (A C : Finset (Site d)) (y : Site d) (io : ℝ) :
    io * (∑ x ∈ A, ∑ z ∈ C, q u (z - x))
      = io * ((A.card : ℝ) * ((C.card : ℝ) * q u y))
        + 2 * (io * ((C.card : ℝ) * (∑ x ∈ A, q u x)))
        + (-2) * (io * ((∑ x ∈ A, dot u x) * (∑ z ∈ C, drel u y z)))
        + (-4) * (io * ((C.card : ℝ) * (dot u y * (∑ x ∈ A, dot u x))))
        + io * ((A.card : ℝ) * (∑ z ∈ C, q u z)
            - (C.card : ℝ) * (∑ x ∈ A, qrel u y x)) := by
  have h6 := sum_sum_q_sub_eq u A C y
  have hA := sum_q_shift u C y
  have hB := sum_q_sub_shift u A y
  rw [h6, hA, hB]
  ring

/-- **The exact collapse identity.**  The source's six-term expansion equals the printed
four-term expression **plus** the exchange defect.  The collapse is therefore equivalent
to the exchange defect having mean zero (`collapse_iff`), which is what the source's
"exchange the roles of `0` and `y`" has to establish. -/
theorem rawRusso_eq (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) (ω : Ω) :
    rawRusso u K Ky B ω
      = paperFour u K Ky B ω + exchangeDefect u K Ky B ω := by
  have hfun : ∀ y ∈ B,
      indOut K y ω * (∑ x ∈ K ω, ∑ z ∈ Ky y ω, q u (z - x))
        = fourSite u K Ky y ω
          + indOut K y ω * ((kcard K ω) * (∑ z ∈ Ky y ω, q u z)
              - (kcard (Ky y) ω) * (∑ x ∈ K ω, qrel u y x)) := by
    intro y _
    have h := six_term_collapse u (K ω) (Ky y ω) y (indOut K y ω)
    simp only [fourSite, T0, T2, T3, T4, restW, pairW, kcard, kS, kDot, sMoment,
      drel] at h ⊢
    rw [h]
    ring
  simp only [rawRusso, paperFour, exchangeDefect]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hfun

/-! ## 4. Expectation form: the collapse as an exact hypothesis -/

variable {w : Ω → ℝ}

/-- Linearity of the finite expectation over the four-term combination. -/
theorem ex_lin4 (a b c e : Ω → ℝ) :
    ex w (fun ω => a ω + 2 * b ω - 2 * c ω - 4 * e ω)
      = ex w a + 2 * ex w b - 2 * ex w c - 4 * ex w e := by
  simp only [ex_add, ex_sub, ex_const_mul]

/-- The same linearity after summing over the ball. -/
theorem sum_lin4 {ι : Type*} (B : Finset ι) (a b c e : ι → ℝ) :
    (∑ y ∈ B, (a y + 2 * b y - 2 * c y - 4 * e y))
      = (∑ y ∈ B, a y) + 2 * (∑ y ∈ B, b y) - 2 * (∑ y ∈ B, c y)
        - 4 * (∑ y ∈ B, e y) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- `derivTerm` is the expectation of `paperFour`: the four-term right-hand side of
`(I.5.3)` in the finite model. -/
theorem ex_paperFour (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) :
    ex w (paperFour u K Ky B) = derivTerm w u K Ky B := by
  have h1 : ex w (paperFour u K Ky B) = ∑ y ∈ B, ex w (fourSite u K Ky y) := by
    rw [show paperFour u K Ky B = (fun ω => ∑ y ∈ B, fourSite u K Ky y ω) from rfl]
    exact ex_sum B (fun y => fourSite u K Ky y)
  rw [h1]
  simp only [derivTerm]
  have h : ∀ y ∈ B, ex w (fourSite u K Ky y)
      = ex w (T0 u K Ky y) + 2 * ex w (T2 u K Ky y)
        - 2 * ex w (T3 u K Ky y) - 4 * ex w (T4 u K Ky y) := by
    intro y _
    rw [show fourSite u K Ky y
        = (fun ω => T0 u K Ky y ω + 2 * T2 u K Ky y ω - 2 * T3 u K Ky y ω
            - 4 * T4 u K Ky y ω) from rfl]
    exact ex_lin4 _ _ _ _
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **The exact relation between the Russo integrand and `derivTerm`.** -/
theorem ex_rawRusso_eq (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) :
    ex w (rawRusso u K Ky B)
      = derivTerm w u K Ky B + ex w (exchangeDefect u K Ky B) := by
  have h : rawRusso u K Ky B
      = fun ω => paperFour u K Ky B ω + exchangeDefect u K Ky B ω := by
    funext ω; exact rawRusso_eq u K Ky B ω
  rw [h, ex_add, ex_paperFour]

/-- **The paper's collapse holds exactly iff the exchange defect has mean zero.** -/
theorem collapse_iff (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) :
    ex w (rawRusso u K Ky B) = derivTerm w u K Ky B
      ↔ ex w (exchangeDefect u K Ky B) = 0 := by
  rw [ex_rawRusso_eq]
  constructor <;> intro h <;> linarith

/-- The remaining content of `(I.5.3)`, made explicit as a named hypothesis:
the mean of the exchange defect vanishes.  This is the paper's "exchange the roles
of `0` and `y`", and it is *not* derivable from translation invariance alone. -/
theorem collapse_of_exchange (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d))
    (h : ex w (exchangeDefect u K Ky B) = 0) :
    ex w (rawRusso u K Ky B) = derivTerm w u K Ky B :=
  (collapse_iff u K Ky B).mpr h

/-! ## 5. The defect is dominated by nonnegative functionals of the retained shape -/

/-- The (nonnegative) functional `∑_{y∈B} 1(y∉K) |K| ∑_{z∈K_y} q_u(z)`. -/
noncomputable def exFirst (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ y ∈ B, indOut K y ω * ((kcard K ω) * (∑ z ∈ Ky y ω, q u z))

/-- The (nonnegative) transposed functional
`∑_{y∈B} 1(y∉K) |K_y| ∑_{x∈K} q_u(x - y)`. -/
noncomputable def exSecond (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ y ∈ B, indOut K y ω * ((kcard (Ky y) ω) * (∑ x ∈ K ω, qrel u y x))

/-- `exchangeDefect = exFirst - exSecond`, pointwise. -/
theorem exchangeDefect_apply (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) (ω : Ω) :
    exchangeDefect u K Ky B ω = exFirst u K Ky B ω - exSecond u K Ky B ω := by
  simp only [exchangeDefect, exFirst, exSecond]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem exFirst_nonneg (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) (ω : Ω) :
    0 ≤ exFirst u K Ky B ω := by
  refine Finset.sum_nonneg fun y _ => ?_
  have h1 : 0 ≤ indOut K y ω := indOut_nonneg K y ω
  have h2 : 0 ≤ kcard K ω := by simp only [kcard]; positivity
  have h3 : 0 ≤ ∑ z ∈ Ky y ω, q u z := Finset.sum_nonneg fun z _ => q_nonneg u z
  exact mul_nonneg h1 (mul_nonneg h2 h3)

theorem exSecond_nonneg (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) (ω : Ω) :
    0 ≤ exSecond u K Ky B ω := by
  refine Finset.sum_nonneg fun y _ => ?_
  have h1 : 0 ≤ indOut K y ω := indOut_nonneg K y ω
  have h2 : 0 ≤ kcard (Ky y) ω := by simp only [kcard]; positivity
  have h3 : 0 ≤ ∑ x ∈ K ω, qrel u y x := by
    refine Finset.sum_nonneg fun z _ => ?_
    rw [qrel_apply]; exact q_nonneg u (z - y)
  exact mul_nonneg h1 (mul_nonneg h2 h3)

/-- **Crude domination of the defect by two nonnegative functionals of the retained
shape.**  Both `exFirst` and `exSecond` are sums over `y` of `1(y∉K)` times a cluster
volume times a quadratic moment, i.e. exactly the shape of the paper's `G`-type errors;
the second is the transposed partner of `T2`.

Caveat: this bound is of *main* order, not of error order, so it is not a small-error
estimate and it does **not** replace the two comparisons `(BC)`, `(DF)`; it is recorded
only to display the shape of the defect. -/
theorem abs_exchangeDefect_le (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) (hw : ∀ ω, 0 ≤ w ω) :
    |ex w (exchangeDefect u K Ky B)|
      ≤ ex w (fun ω => exFirst u K Ky B ω + exSecond u K Ky B ω) := by
  have hpt : ∀ ω, |exchangeDefect u K Ky B ω|
      ≤ exFirst u K Ky B ω + exSecond u K Ky B ω := by
    intro ω
    have hp := exFirst_nonneg u K Ky B ω
    have hn := exSecond_nonneg u K Ky B ω
    rw [exchangeDefect_apply u K Ky B ω, abs_le]
    constructor <;> linarith
  refine (ex_abs_le hw _).trans (ex_mono hw fun ω => hpt ω)

/-! ## 6. The defect is exactly the source's arithmetic residue `B - C + 2D + 2F`

Writing the six terms of the expansion as `A + B + C + 2D - 2E - 2F` (`A = S1`,
`B = S2`, `C = S3`, `2D = S4`, `-2E = S5`, `-2F = S6`) and the printed four as
`A + 2C - 2E - 4F`, the residue is `B - C + 2D + 2F`.  The four items `Bfun`, `Cfun`,
`Dfun`, `Ffun` below are `B`, `C`, `D`, `F`; the source needs the two expectation-level
comparisons `ex B = ex C` and `ex D = - ex F`, and together they discharge the defect
(`collapse_of_comparisons`).  Neither comparison is proved here, and nothing here
asserts that they fail. -/

/-- `B = S2 = ∑_{y∈B} 1(y∉K) |K| ∑_{z∈K_y} q_u(z - y)`: the `⟪z-y,u⟫²` term. -/
noncomputable def Bfun (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ y ∈ B, indOut K y ω * (kcard K ω * (∑ z ∈ Ky y ω, qrel u y z))

/-- `C = S3 = T2 = ∑_{y∈B} 1(y∉K) |K_y| S(K)`: the `⟪x,u⟫²` term. -/
noncomputable def Cfun (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ y ∈ B, indOut K y ω * (kcard (Ky y) ω * kS u K ω)

/-- `D = S4/2 = ∑_{y∈B} 1(y∉K) |K| ⟪y,u⟫ ∑_{z∈K_y} ⟪z-y,u⟫`: half the `2αβ` term. -/
noncomputable def Dfun (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ y ∈ B, indOut K y ω * (kcard K ω * (dot u y * (∑ z ∈ Ky y ω, drel u y z)))

/-- `F = T4 = ∑_{y∈B} 1(y∉K) |K_y| ⟪y,u⟫ ∑_{x∈K} ⟪x,u⟫`: half the `-2βγ` term. -/
noncomputable def Ffun (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ y ∈ B, indOut K y ω * (kcard (Ky y) ω * (dot u y * kDot u K ω))

/-- **The defect is the source's residue.**  `exchangeDefect = B - C + 2D + 2F`
pointwise.  The `q_u(y)` parts of `B + 2D` and `C + 2F` cancel identically. -/
theorem exchangeDefect_eq_comparisons (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) (ω : Ω) :
    exchangeDefect u K Ky B ω
      = Bfun u K Ky B ω - Cfun u K Ky B ω + 2 * Dfun u K Ky B ω
        + 2 * Ffun u K Ky B ω := by
  have hsite : ∀ y ∈ B,
      indOut K y ω * ((kcard K ω) * (∑ z ∈ Ky y ω, q u z)
          - (kcard (Ky y) ω) * (∑ x ∈ K ω, qrel u y x))
        = indOut K y ω * (kcard K ω * (∑ z ∈ Ky y ω, qrel u y z))
          - indOut K y ω * (kcard (Ky y) ω * kS u K ω)
          + 2 * (indOut K y ω * (kcard K ω * (dot u y * (∑ z ∈ Ky y ω, drel u y z))))
          + 2 * (indOut K y ω * (kcard (Ky y) ω * (dot u y * kDot u K ω))) := by
    intro y _
    have hA := sum_q_shift u (Ky y ω) y
    have hB := sum_q_sub_shift u (K ω) y
    simp only [kS, kDot, kcard, sMoment] at hA hB ⊢
    rw [hA, hB]
    generalize h1 : (∑ z ∈ Ky y ω, qrel u y z) = S1
    generalize h2 : (∑ z ∈ Ky y ω, drel u y z) = S2
    generalize h3 : (∑ x ∈ K ω, q u x) = S3
    generalize h4 : (∑ x ∈ K ω, dot u x) = S4
    generalize h5 : (((K ω).card : ℕ) : ℝ) = M
    generalize h6 : (((Ky y ω).card : ℕ) : ℝ) = Mc
    generalize h7 : dot u y = b
    generalize h8 : indOut K y ω = io
    ring
  simp only [exchangeDefect, Bfun, Cfun, Dfun, Ffun]
  rw [Finset.sum_congr rfl hsite]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

/-- **The defect at expectation level is the source's residue.** -/
theorem ex_exchangeDefect_eq_comparisons (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) :
    ex w (exchangeDefect u K Ky B)
      = ex w (Bfun u K Ky B) - ex w (Cfun u K Ky B)
        + 2 * ex w (Dfun u K Ky B) + 2 * ex w (Ffun u K Ky B) := by
  have h : exchangeDefect u K Ky B
      = fun ω => Bfun u K Ky B ω - Cfun u K Ky B ω + 2 * Dfun u K Ky B ω
          + 2 * Ffun u K Ky B ω := by
    funext ω; exact exchangeDefect_eq_comparisons u K Ky B ω
  rw [h]
  simp only [ex_add, ex_sub, ex_const_mul]

/-- **The two source comparisons discharge the collapse.**
`(BC) : ex B = ex C` and `(DF) : ex D = - ex F` together give
`ex rawRusso = derivTerm`, i.e. they discharge `hExchange`. -/
theorem collapse_of_comparisons (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d))
    (hBC : ex w (Bfun u K Ky B) = ex w (Cfun u K Ky B))
    (hDF : ex w (Dfun u K Ky B) = -ex w (Ffun u K Ky B)) :
    ex w (rawRusso u K Ky B) = derivTerm w u K Ky B := by
  refine (collapse_iff u K Ky B).mpr ?_
  rw [ex_exchangeDefect_eq_comparisons]
  linarith

/-- **Exact form of the collapse in terms of the residue.** -/
theorem collapse_iff_comparisons (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) :
    ex w (rawRusso u K Ky B) = derivTerm w u K Ky B
      ↔ ex w (Bfun u K Ky B) - ex w (Cfun u K Ky B)
          + 2 * ex w (Dfun u K Ky B) + 2 * ex w (Ffun u K Ky B) = 0 := by
  rw [collapse_iff, ex_exchangeDefect_eq_comparisons]

end PercLib.CriticalLRP.I58

#print axioms PercLib.CriticalLRP.I58.sum_q_shift
#print axioms PercLib.CriticalLRP.I58.sum_q_sub_shift
#print axioms PercLib.CriticalLRP.I58.sum_q_sub_eq
#print axioms PercLib.CriticalLRP.I58.sum_sum_q_sub_eq
#print axioms PercLib.CriticalLRP.I58.six_term_collapse
#print axioms PercLib.CriticalLRP.I58.rawRusso_eq
#print axioms PercLib.CriticalLRP.I58.ex_paperFour
#print axioms PercLib.CriticalLRP.I58.ex_rawRusso_eq
#print axioms PercLib.CriticalLRP.I58.collapse_iff
#print axioms PercLib.CriticalLRP.I58.collapse_of_exchange
#print axioms PercLib.CriticalLRP.I58.abs_exchangeDefect_le
#print axioms PercLib.CriticalLRP.I58.exchangeDefect_eq_comparisons
#print axioms PercLib.CriticalLRP.I58.ex_exchangeDefect_eq_comparisons
#print axioms PercLib.CriticalLRP.I58.collapse_of_comparisons
#print axioms PercLib.CriticalLRP.I58.collapse_iff_comparisons
