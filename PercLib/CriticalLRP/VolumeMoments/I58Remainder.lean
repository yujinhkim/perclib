/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Lemma I.5.8 of T. Hutchcroft, *Critical long-range percolation I*
(arXiv:2508.18807v1): the exact error-bound assembly for the gyration
derivative.  Source audited against the local TeX source
`.scratch/i52/source/Zd_renormalizationHD.tex`, `lem:gyration_derivative2`
(eq. `eq:x12_derivative` and the three displayed remainder estimates following
it), and against `.scratch/tom1.txt` I.5.8 (lines ~3287-3440).

This file contains **only** the arithmetic/assembly layer: the exact
factorisation of the main terms, the triangle-inequality bookkeeping with
explicit constants, the pointwise Cauchy-Schwarz/AM-GM inputs, and the
conversion of the paper's `E[|K|^2 sum_{y in K cap B_r} <y,u>^2]` into
`||u||^2 r^2 E[|K|^2 |K cap B_r|]`.  The four displayed remainder estimates of
the paper (which are proved there from the BK/tree-graph inequalities, the
restoration Lemma I.2.1 and the mass-transport principle) enter as **named
hypotheses** with their provenance recorded; no probabilistic statement is
smuggled into the conclusion.
-/
module

public import Mathlib

set_option autoImplicit true

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP.I58

/-! ## 1. The quadratic spatial weight `q_u(x) = <x,u>^2` on `Z^d` -/

/-- Lattice sites. -/
abbrev Site (d : ℕ) := Fin d → ℤ

variable {d : ℕ}

/-- The inner product `<x,u>`. -/
noncomputable def dot (u : Fin d → ℝ) (x : Site d) : ℝ := ∑ i, u i * (x i : ℝ)

/-- The quadratic spatial weight `q_u(x) = <x,u>^2`. -/
noncomputable def q (u : Fin d → ℝ) (x : Site d) : ℝ := dot u x ^ 2

/-- `||u||_2^2`. -/
noncomputable def uNormSq (u : Fin d → ℝ) : ℝ := ∑ i, u i ^ 2

/-- `||x||_2^2` of a lattice site. -/
noncomputable def siteNormSq (x : Site d) : ℝ := ∑ i, (x i : ℝ) ^ 2

/-- The spatial moment `S(K) = sum_{x in K} q_u(x)`. -/
noncomputable def sMoment (u : Fin d → ℝ) (K : Finset (Site d)) : ℝ := ∑ x ∈ K, q u x

lemma dot_add (u : Fin d → ℝ) (x y : Site d) : dot u (x + y) = dot u x + dot u y := by
  simp only [dot, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

lemma dot_neg (u : Fin d → ℝ) (x : Site d) : dot u (-x) = -dot u x := by
  simp only [dot, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

lemma dot_sub (u : Fin d → ℝ) (x y : Site d) : dot u (x - y) = dot u x - dot u y := by
  simp only [dot, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]

lemma q_nonneg (u : Fin d → ℝ) (x : Site d) : 0 ≤ q u x := sq_nonneg _

lemma q_add (u : Fin d → ℝ) (x y : Site d) :
    q u (x + y) = q u x + q u y + 2 * (dot u x * dot u y) := by
  simp only [q, dot_add]; ring

lemma q_sub (u : Fin d → ℝ) (x y : Site d) :
    q u (x - y) = q u x + q u y - 2 * (dot u x * dot u y) := by
  simp only [q, dot_sub]; ring

/-- The trinomial (three-term) expansion of the quadratic weight, in the shape
used in the proof of Lemma I.5.8 for `z - x = (z - y) + (y - 0) + (0 - x)`. -/
lemma q_three (u : Fin d → ℝ) (a b c : Site d) :
    q u (a + b + c) =
      q u a + q u b + q u c +
        2 * (dot u a * dot u b + dot u a * dot u c + dot u b * dot u c) := by
  simp only [q, dot_add]; ring

/-- The Cauchy-Schwarz bound `<x,u>^2 <= ||u||^2 ||x||^2`. -/
lemma q_le_uNormSq_mul_siteNormSq (u : Fin d → ℝ) (x : Site d) :
    q u x ≤ uNormSq u * siteNormSq x := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin d)) u (fun i => (x i : ℝ))
  simpa only [q, dot, uNormSq, siteNormSq] using h

lemma uNormSq_nonneg (u : Fin d → ℝ) : 0 ≤ uNormSq u :=
  Finset.sum_nonneg fun i _ => sq_nonneg (u i)

/-- On the ball of radius `r`, the weight is `O(||u||^2 r^2)` **pointwise**.  This
is the step that turns the paper's `E[|K|^2 sum_{y in K cap B_r} <y,u>^2]` into
`||u||^2 r^2 E[|K|^2 |K cap B_r|]`. -/
lemma q_le_of_siteNormSq_le (u : Fin d → ℝ) (x : Site d) {r : ℝ}
    (hx : siteNormSq x ≤ r ^ 2) : q u x ≤ uNormSq u * r ^ 2 :=
  (q_le_uNormSq_mul_siteNormSq u x).trans
    (mul_le_mul_of_nonneg_left hx (uNormSq_nonneg u))

/-- `|ab| <= (a^2 + b^2)/2`; the origin of the two `1/2` coefficients in the
cross-term estimates of Lemma I.5.8. -/
lemma abs_mul_le_half (a b : ℝ) : |a * b| ≤ (1 / 2) * (a ^ 2 + b ^ 2) := by
  have h1 : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h2 : -(a ^ 2 + b ^ 2) ≤ 2 * (a * b) := by nlinarith [sq_nonneg (a + b)]
  rw [abs_le]
  constructor <;> nlinarith

lemma sMoment_nonneg (u : Fin d → ℝ) (K : Finset (Site d)) : 0 ≤ sMoment u K :=
  Finset.sum_nonneg fun x _ => q_nonneg u x

/-- `S(K cap B) <= ||u||^2 r^2 |K cap B|` on the ball: the deterministic heart of
the `O(||u||^2 r^2 ...)` error terms. -/
lemma sMoment_inter_le (u : Fin d → ℝ) {B : Finset (Site d)} {r : ℝ}
    (hB : ∀ y ∈ B, siteNormSq y ≤ r ^ 2) (K : Finset (Site d)) :
    sMoment u (K ∩ B) ≤ uNormSq u * r ^ 2 * ((K ∩ B).card : ℝ) := by
  have hterm : ∀ y ∈ K ∩ B, q u y ≤ uNormSq u * r ^ 2 := fun y hy =>
    q_le_of_siteNormSq_le u y (hB y (Finset.mem_of_mem_inter_right hy))
  calc sMoment u (K ∩ B) = ∑ y ∈ K ∩ B, q u y := rfl
    _ ≤ ∑ _y ∈ K ∩ B, uNormSq u * r ^ 2 := Finset.sum_le_sum hterm
    _ = uNormSq u * r ^ 2 * ((K ∩ B).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ## 2. Finite weighted expectation

Every statement below is an exact identity or an inequality in the finitely
supported measure `w`; no continuity or limiting argument is involved. -/

variable {Ω : Type*} [Fintype Ω]

/-- Expectation against a finite weight `w` (intended: `w omega >= 0`,
`sum w = 1`, e.g. `configurationLaw p`). -/
noncomputable def ex (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, w ω * X ω

variable {w : Ω → ℝ}

lemma ex_add (X Y : Ω → ℝ) : ex w (fun ω => X ω + Y ω) = ex w X + ex w Y := by
  simp only [ex, mul_add, Finset.sum_add_distrib]

lemma ex_sub (X Y : Ω → ℝ) : ex w (fun ω => X ω - Y ω) = ex w X - ex w Y := by
  simp only [ex, mul_sub, Finset.sum_sub_distrib]

lemma ex_neg (X : Ω → ℝ) : ex w (fun ω => -X ω) = -ex w X := by
  simp only [ex, mul_neg, Finset.sum_neg_distrib]

lemma ex_const_mul (c : ℝ) (X : Ω → ℝ) : ex w (fun ω => c * X ω) = c * ex w X := by
  have h : (fun ω => w ω * (c * X ω)) = fun ω => c * (w ω * X ω) := by
    funext ω; ring
  rw [ex, ex, h, Finset.mul_sum]

lemma ex_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    ex w (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, ex w (X i) := by
  have h : ex w (fun ω => ∑ i ∈ s, X i ω) = ∑ ω, ∑ i ∈ s, w ω * X i ω := by
    simp only [ex, Finset.mul_sum]
  rw [h]
  exact Finset.sum_comm

lemma ex_nonneg (hw : ∀ ω, 0 ≤ w ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ ex w X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (hX ω)

lemma ex_mono (hw : ∀ ω, 0 ≤ w ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    ex w X ≤ ex w Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)

lemma ex_abs_le (hw : ∀ ω, 0 ≤ w ω) (X : Ω → ℝ) :
    |ex w X| ≤ ex w (fun ω => |X ω|) := by
  have h1 : |ex w X| ≤ ∑ ω, |w ω * X ω| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ ω, |w ω * X ω| = ∑ ω, w ω * |X ω| :=
    Finset.sum_congr rfl fun ω _ => by rw [abs_mul, abs_of_nonneg (hw ω)]
  calc |ex w X| ≤ ∑ ω, |w ω * X ω| := h1
    _ = ex w (fun ω => |X ω|) := h2

/-- **Summation/absorption lemma.** A family of nonnegative observables indexed by
`B`, each multiplied by a per-site weight bounded by `C`, is bounded by `C` times
the expectation of the *summed* observable.  This is the step that converts a
sum over `y in B_r` of per-site error bounds into the printed `O(...)`
expressions of (I.5.2). -/
lemma sum_weighted_ex_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (C : ℝ)
    (f : ι → Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (_hc : ∀ i ∈ s, 0 ≤ c i)
    (hcC : ∀ i ∈ s, c i ≤ C) (hf : ∀ i ∈ s, ∀ ω, 0 ≤ f i ω) :
    ∑ i ∈ s, c i * ex w (f i) ≤ C * ex w (fun ω => ∑ i ∈ s, f i ω) := by
  have h1 : ∀ i ∈ s, c i * ex w (f i) = ex w (fun ω => c i * f i ω) := fun i _ =>
    (ex_const_mul (c i) (f i)).symm
  calc ∑ i ∈ s, c i * ex w (f i) = ∑ i ∈ s, ex w (fun ω => c i * f i ω) :=
        Finset.sum_congr rfl h1
    _ = ex w (fun ω => ∑ i ∈ s, c i * f i ω) := (ex_sum s _).symm
    _ ≤ ex w (fun ω => ∑ i ∈ s, C * f i ω) := by
        refine ex_mono hw fun ω => Finset.sum_le_sum fun i hi => ?_
        exact mul_le_mul_of_nonneg_right (hcC i hi) (hf i hi ω)
    _ = ex w (fun ω => C * ∑ i ∈ s, f i ω) := by
        simp only [Finset.mul_sum]
    _ = C * ex w (fun ω => ∑ i ∈ s, f i ω) := ex_const_mul C _

/-! ## 3. The finite model: cluster, restored cluster, and the four remainder
estimates of the proof of Lemma I.5.8

The objects below are the ones appearing in `eq:x12_derivative` of the TeX
source:

`T0 = |K| sum_{y in B} 1(y notin K) |K_y| <y,u>^2`            (coefficient 1)
`T2 = sum_{x in K} <x,u>^2 sum_{y in B} 1(y notin K) |K_y|`  (coefficient 2)
`T3 = sum_{x in K} <x,u> sum_{y in B} 1(y notin K) sum_{z in K_y} <z-y,u>` (coefficient -2)
`T4 = sum_{x in K} <x,u> sum_{y in B} <y,u> 1(y notin K) |K_y|` (coefficient -4)
-/

/-- `|K|`. -/
noncomputable def kcard (K : Ω → Finset (Site d)) : Ω → ℝ := fun ω => ((K ω).card : ℝ)

/-- `|K cap B|`. -/
noncomputable def kap (K : Ω → Finset (Site d)) (B : Finset (Site d)) : Ω → ℝ :=
  fun ω => ((K ω ∩ B).card : ℝ)

/-- `S(K) = sum_{x in K} <x,u>^2`. -/
noncomputable def kS (u : Fin d → ℝ) (K : Ω → Finset (Site d)) : Ω → ℝ :=
  fun ω => sMoment u (K ω)

/-- `sum_{x in K} <x,u>`, the signed first moment of `K`. -/
noncomputable def kDot (u : Fin d → ℝ) (K : Ω → Finset (Site d)) : Ω → ℝ :=
  fun ω => ∑ x ∈ K ω, dot u x

/-- `1(y in K)`. -/
noncomputable def indIn (K : Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => if y ∈ K ω then 1 else 0

/-- `1(y notin K)`. -/
noncomputable def indOut (K : Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => if y ∈ K ω then 0 else 1

/-- `|K| 1(y notin K) |K_y|`: the restored-cluster weight. -/
noncomputable def restW (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => indOut K y ω * kcard K ω * kcard (Ky y) ω

/-- `|K| S(K) 1(y in K)`: the second-moment error of the "similar reasoning" step. -/
noncomputable def prodIn (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => kcard K ω * kS u K ω * indIn K y ω

/-- `1(y notin K) |K_y| S(K)`: half of the AM-GM split of the cross terms. -/
noncomputable def pairW (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => indOut K y ω * kcard (Ky y) ω * kS u K ω

/-- `1(y notin K) |K| sum_{z in K_y} <z-y,u>^2`: the other half of the AM-GM split. -/
noncomputable def pairQ (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => indOut K y ω * kcard K ω * ∑ z ∈ Ky y ω, q u (z - y)

/-- `1(y notin K) |K| |K_y| <y,u>^2`: the `<y,u>`-weighted cross remainder. -/
noncomputable def pairQy (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => indOut K y ω * kcard K ω * kcard (Ky y) ω * q u y

/-- The four terms of `eq:x12_derivative`. -/
noncomputable def T0 (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => restW K Ky y ω * q u y

noncomputable def T2 (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  pairW u K Ky y

noncomputable def T3 (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => indOut K y ω * kDot u K ω * (∑ z ∈ Ky y ω, dot u (z - y))

noncomputable def T4 (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) : Ω → ℝ :=
  fun ω => indOut K y ω * kcard (Ky y) ω * dot u y * kDot u K ω

lemma indIn_nonneg (K : Ω → Finset (Site d)) (y : Site d) : ∀ ω, 0 ≤ indIn K y ω := by
  intro ω; simp only [indIn]; split <;> norm_num

lemma indOut_nonneg (K : Ω → Finset (Site d)) (y : Site d) : ∀ ω, 0 ≤ indOut K y ω := by
  intro ω; simp only [indOut]; split <;> norm_num

/-- Counting identity: summing `1(y in K)` over `B` gives `|K cap B|`. -/
lemma sum_indIn (K : Ω → Finset (Site d)) (B : Finset (Site d)) :
    ∑ y ∈ B, indIn K y = kap K B := by
  funext ω
  simp only [Finset.sum_apply, indIn, kap, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.inter_comm]

/-- `u = 0` is the vacuous case: the weight vanishes identically, so every bound
below holds with both sides zero (cf. the first line of the paper's proof). -/
lemma q_zero (x : Site d) : q (0 : Fin d → ℝ) x = 0 := by
  simp [q, dot]

/-! ### 3.1 The four remainder estimates -/

/-- **First remainder** (paper: "for the first expectation on the right hand side
of `(eq:x12_derivative)`", using `lem:BK_disjoint_clusters_covariance`).

The named hypothesis `hrest` is the paper's pair of displayed facts
`(E|K|)^2 - E[1(y notin K)|K||K_y|] >= 0` and
`... <= E[|K|^2 1(y in K)]`, combined into an absolute-value bound; it is exactly
`lem:BK_disjoint_clusters_covariance` applied to the two-cluster covariance at
the site `y`. -/
theorem remainder_volume_bound
    (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) {r : ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hB : ∀ y ∈ B, siteNormSq y ≤ r ^ 2)
    (hrest : ∀ y ∈ B,
      |(ex w (kcard K)) ^ 2 - ex w (restW K Ky y)|
        ≤ ex w (fun ω => (kcard K ω) ^ 2 * indIn K y ω)) :
    |(∑ y ∈ B, ex w (T0 u K Ky y)) - (ex w (kcard K)) ^ 2 * (∑ y ∈ B, q u y)|
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω) := by
  have hT0 : ∀ y, ex w (T0 u K Ky y)
      = q u y * ex w (restW K Ky y) := by
    intro y
    have hfun : T0 u K Ky y = fun ω => q u y * restW K Ky y ω := by
      funext ω; simp only [T0, restW]; ring
    rw [hfun, ex_const_mul]
  have hdiff : (∑ y ∈ B, ex w (T0 u K Ky y)) - (ex w (kcard K)) ^ 2 * (∑ y ∈ B, q u y)
      = -∑ y ∈ B, q u y * ((ex w (kcard K)) ^ 2 - ex w (restW K Ky y)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hT0 y]; ring
  have hstep : |∑ y ∈ B, q u y * ((ex w (kcard K)) ^ 2 - ex w (restW K Ky y))|
      ≤ ∑ y ∈ B, q u y * ex w (fun ω => (kcard K ω) ^ 2 * indIn K y ω) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => ?_)
    rw [abs_mul, abs_of_nonneg (q_nonneg u y)]
    exact mul_le_mul_of_nonneg_left (hrest y hy) (q_nonneg u y)
  have hq : ∀ y ∈ B, q u y ≤ uNormSq u * r ^ 2 := fun y hy => q_le_of_siteNormSq_le u y (hB y hy)
  have hfin : ∑ y ∈ B, q u y * ex w (fun ω => (kcard K ω) ^ 2 * indIn K y ω)
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω) := by
    refine (sum_weighted_ex_le (w := w) B (fun y => q u y) (uNormSq u * r ^ 2)
      (fun y ω => (kcard K ω) ^ 2 * indIn K y ω) hw (fun y _ => q_nonneg u y) hq
      (fun y _ ω => mul_nonneg (sq_nonneg _) (indIn_nonneg K y ω))).trans ?_
    have hfun : (fun ω => ∑ i ∈ B, (kcard K ω) ^ 2 * indIn K i ω)
        = fun ω => (kcard K ω) ^ 2 * kap K B ω := by
      funext ω
      rw [← Finset.mul_sum, ← Finset.sum_apply, sum_indIn K B]
    rw [hfun]
  rw [hdiff, abs_neg]
  exact hstep.trans hfin

/-- **Second remainder** (paper: "for the second expectation we have by similar
reasoning").  The named hypothesis `h2` is the paper's displayed conclusion of
that "similar reasoning", with the mass-transport input made explicit per site. -/
theorem remainder_mass_bound
    (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d))
    (_hw : ∀ ω, 0 ≤ w ω)
    (h2 : ∀ y ∈ B,
      |(ex w (kcard K)) * (ex w (kS u K)) - ex w (pairW u K Ky y)|
        ≤ ex w (prodIn u K y)) :
    |(∑ y ∈ B, ex w (T2 u K Ky y)) -
        (B.card : ℝ) * (ex w (kcard K)) * (ex w (kS u K))|
      ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  have hdiff : (∑ y ∈ B, ex w (T2 u K Ky y)) -
        (B.card : ℝ) * (ex w (kcard K)) * (ex w (kS u K))
      = ∑ y ∈ B, (ex w (pairW u K Ky y) - (ex w (kcard K)) * (ex w (kS u K))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    simp only [T2]
    ring
  have hstep : |∑ y ∈ B, (ex w (pairW u K Ky y) - (ex w (kcard K)) * (ex w (kS u K)))|
      ≤ ∑ y ∈ B, ex w (prodIn u K y) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => ?_)
    rw [abs_sub_comm]
    exact h2 y hy
  rw [hdiff]
  refine hstep.trans ?_
  rw [← ex_sum]
  have hfun : (fun ω => ∑ y ∈ B, prodIn u K y ω)
      = fun ω => kcard K ω * kap K B ω * kS u K ω := by
    funext ω
    show ∑ y ∈ B, kcard K ω * kS u K ω * indIn K y ω
      = kcard K ω * kap K B ω * kS u K ω
    rw [← Finset.mul_sum, ← Finset.sum_apply, sum_indIn K B]
    ring
  rw [hfun]

/-- **Formal bookkeeping only.**  If both AM-GM halves of the `T3` cross term are
identified with the same real number `G`, then the cross term is bounded by `G`.
The hypothesis `hmt1`/`hmt2` here is a *purely formal* identification.  It is
**not** the mass-transport principle: the paper's mass transport acts on the
*enlarged* weights (the `y notin K` restriction dropped) and is not formalised
here; the paper's actual cross-term bound enters the assembly below as a
displayed hypothesis. -/
theorem sum_of_halves_first
    (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (B : Finset (Site d)) (G : ℝ)
    (h3 : ∀ y ∈ B, |ex w (T3 u K Ky y)|
      ≤ (1 / 2) * ex w (pairW u K Ky y) + (1 / 2) * ex w (pairQ u K Ky y))
    (hmt1 : ∑ y ∈ B, ex w (pairW u K Ky y) = G)
    (hmt2 : ∑ y ∈ B, ex w (pairQ u K Ky y) = G) :
    |∑ y ∈ B, ex w (T3 u K Ky y)| ≤ G := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsum : ∑ y ∈ B, |ex w (T3 u K Ky y)|
      ≤ (1 / 2) * (∑ y ∈ B, ex w (pairW u K Ky y)) +
        (1 / 2) * (∑ y ∈ B, ex w (pairQ u K Ky y)) := by
    refine (Finset.sum_le_sum h3).trans ?_
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  exact hsum.trans (le_of_eq (by rw [hmt1, hmt2]; ring))

/-- As `sum_of_halves_first`, for the `<y,u>`-weighted cross remainder.  Again the
identifications are formal, not mass transport. -/
theorem sum_of_halves_second
    (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (B : Finset (Site d)) (G Gq : ℝ)
    (h4 : ∀ y ∈ B, |ex w (T4 u K Ky y)|
      ≤ (1 / 2) * ex w (pairW u K Ky y) + (1 / 2) * ex w (pairQy u K Ky y))
    (hmt1 : ∑ y ∈ B, ex w (pairW u K Ky y) = G)
    (hmt3 : ∑ y ∈ B, ex w (pairQy u K Ky y) = Gq) :
    |∑ y ∈ B, ex w (T4 u K Ky y)| ≤ (1 / 2) * G + (1 / 2) * Gq := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsum : ∑ y ∈ B, |ex w (T4 u K Ky y)|
      ≤ (1 / 2) * (∑ y ∈ B, ex w (pairW u K Ky y)) +
        (1 / 2) * (∑ y ∈ B, ex w (pairQy u K Ky y)) := by
    refine (Finset.sum_le_sum h4).trans ?_
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  exact hsum.trans (le_of_eq (by rw [hmt1, hmt3]))

/-- **From `E[|K|^2 sum_{y in K cap B_r} <y,u>^2]` to `||u||^2 r^2 E[|K|^2 |K cap B_r|]`.**
This is the paper's `\preceq r^{2} \E_r[|K|^2|K\cap B_r|]`, proved here with the
explicit constant `1`: the only input is the pointwise Cauchy-Schwarz bound on
the ball plus the counting identity `sum_{y in B} 1(y in K) = |K cap B|`. -/
theorem Gq_le_U
    (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (B : Finset (Site d)) {r : ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hB : ∀ y ∈ B, siteNormSq y ≤ r ^ 2) :
    ex w (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B))
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω) := by
  have hpt : ∀ ω, (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)
      ≤ (uNormSq u * r ^ 2) * ((kcard K ω) ^ 2 * kap K B ω) := by
    intro ω
    have h1 := mul_le_mul_of_nonneg_left (sMoment_inter_le u hB (K ω)) (sq_nonneg (kcard K ω))
    calc (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)
        ≤ (kcard K ω) ^ 2 * (uNormSq u * r ^ 2 * ((K ω ∩ B).card : ℝ)) := h1
      _ = (uNormSq u * r ^ 2) * ((kcard K ω) ^ 2 * kap K B ω) := by
          simp only [kap, kcard]; ring
  calc ex w (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B))
      ≤ ex w (fun ω => (uNormSq u * r ^ 2) * ((kcard K ω) ^ 2 * kap K B ω)) :=
        ex_mono hw hpt
    _ = (uNormSq u * r ^ 2) * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω) :=
        ex_const_mul _ _

/-! ### 3.2 The two cross-term `1/2`-splits, proved from pointwise AM-GM

The paper's last three terms of `eq:x12_derivative` are estimated by the
tree-graph inequalities, then split with `|a||b| <= (a^2+b^2)/2` and finally
identified with each other by mass transport.  The AM-GM splitting itself is
pure algebra and is proved here; only the tree-graph domination and the
mass-transport identification remain as named inputs. -/

/-- **AM-GM for the `T3` pairing**, pointwise in the configuration: the two
`1/2`-halves are `|K_y| S(K)` and `|K| sum_{z in K_y} <z-y,u>^2`. -/
theorem dot_pair_abs_le (u : Fin d → ℝ) (A Bs : Finset (Site d)) (y : Site d) :
    |(∑ x ∈ A, dot u x) * (∑ z ∈ Bs, dot u (z - y))| ≤
      (1 / 2) * ((Bs.card : ℝ) * sMoment u A +
        (A.card : ℝ) * ∑ z ∈ Bs, q u (z - y)) := by
  have hprod : (∑ x ∈ A, dot u x) * (∑ z ∈ Bs, dot u (z - y))
      = ∑ x ∈ A, ∑ z ∈ Bs, dot u x * dot u (z - y) :=
    Finset.sum_mul_sum A Bs (fun x => dot u x) (fun z => dot u (z - y))
  have hbase : ∑ x ∈ A, ∑ z ∈ Bs, (dot u x ^ 2 + dot u (z - y) ^ 2)
      = (Bs.card : ℝ) * ∑ x ∈ A, dot u x ^ 2 +
        (A.card : ℝ) * ∑ z ∈ Bs, dot u (z - y) ^ 2 := by
    have hinner : ∀ x, ∑ z ∈ Bs, (dot u x ^ 2 + dot u (z - y) ^ 2)
        = (Bs.card : ℝ) * dot u x ^ 2 + ∑ z ∈ Bs, dot u (z - y) ^ 2 := by
      intro x
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun x _ => hinner x, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
  rw [hprod]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun z hz =>
    abs_mul_le_half (dot u x) (dot u (z - y))).trans ?_
  rw [Finset.sum_congr rfl fun x _ => (Finset.mul_sum (s := Bs)
    (f := fun z => dot u x ^ 2 + dot u (z - y) ^ 2) (a := (1 / 2 : ℝ))).symm]
  rw [← Finset.mul_sum, hbase]
  simp only [q, sMoment]
  exact le_rfl

/-- **AM-GM for the `<y,u>`-weighted pairing**, pointwise in the configuration. -/
theorem dot_single_abs_le (u : Fin d → ℝ) (A : Finset (Site d)) (y : Site d) :
    |dot u y * (∑ x ∈ A, dot u x)| ≤
      (1 / 2) * ((A.card : ℝ) * q u y + sMoment u A) := by
  have hprod : dot u y * (∑ x ∈ A, dot u x) = ∑ x ∈ A, dot u y * dot u x :=
    Finset.mul_sum A (fun x => dot u x) (dot u y)
  rw [hprod]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun x _ =>
    abs_mul_le_half (dot u y) (dot u x)).trans ?_
  have hbase : ∑ x ∈ A, (dot u y ^ 2 + dot u x ^ 2)
      = (A.card : ℝ) * dot u y ^ 2 + ∑ x ∈ A, dot u x ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, hbase]
  simp only [q, sMoment]
  exact le_rfl

/-- Pointwise domination of the `T3` cross term by the AM-GM split. -/
theorem abs_T3_le (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (y : Site d) :
    ∀ ω, |T3 u K Ky y ω| ≤ (1 / 2) * pairW u K Ky y ω + (1 / 2) * pairQ u K Ky y ω := by
  intro ω
  have hind : 0 ≤ indOut K y ω := indOut_nonneg K y ω
  have hAB := dot_pair_abs_le u (K ω) (Ky y ω) y
  have hfac : T3 u K Ky y ω
      = indOut K y ω * ((∑ x ∈ K ω, dot u x) * (∑ z ∈ Ky y ω, dot u (z - y))) := by
    simp only [T3, kDot]
    ring
  rw [hfac, abs_mul, abs_of_nonneg hind]
  refine (mul_le_mul_of_nonneg_left hAB hind).trans_eq ?_
  simp only [pairW, pairQ, kcard, kS]
  ring

/-- Pointwise domination of the `T4` cross term by the AM-GM split. -/
theorem abs_T4_le (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (y : Site d) :
    ∀ ω, |T4 u K Ky y ω| ≤ (1 / 2) * pairW u K Ky y ω + (1 / 2) * pairQy u K Ky y ω := by
  intro ω
  have hind : 0 ≤ indOut K y ω := indOut_nonneg K y ω
  have hKc : 0 ≤ kcard (Ky y) ω := by
    simp only [kcard]; positivity
  have hAB := dot_single_abs_le u (K ω) y
  have hfac : T4 u K Ky y ω
      = indOut K y ω * kcard (Ky y) ω * (dot u y * (∑ x ∈ K ω, dot u x)) := by
    simp only [T4, kDot]
    ring
  rw [hfac, abs_mul, abs_of_nonneg (mul_nonneg hind hKc)]
  refine (mul_le_mul_of_nonneg_left hAB (mul_nonneg hind hKc)).trans_eq ?_
  simp only [pairW, pairQy, kcard, kS]
  ring

/-- The **per-site AM-GM half** of the `T3` estimate, proved from pointwise AM-GM
and monotonicity of the expectation.  This is the step the paper performs after
enlarging the covariance sum to all connected triples; the enlargement itself
(and the subsequent mass-transport identification of the two halves) is *not*
proved here. -/
theorem cross_first_bound_proved (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (hw : ∀ ω, 0 ≤ w ω) (y : Site d) :
    |ex w (T3 u K Ky y)| ≤ (1 / 2) * ex w (pairW u K Ky y) + (1 / 2) * ex w (pairQ u K Ky y) := by
  refine (ex_abs_le hw (T3 u K Ky y)).trans ?_
  calc ex w (fun ω => |T3 u K Ky y ω|)
      ≤ ex w (fun ω => (1 / 2) * pairW u K Ky y ω + (1 / 2) * pairQ u K Ky y ω) :=
        ex_mono hw (abs_T3_le u K Ky y)
    _ = (1 / 2) * ex w (pairW u K Ky y) + (1 / 2) * ex w (pairQ u K Ky y) := by
        rw [ex_add, ex_const_mul, ex_const_mul]

/-- The **per-site AM-GM half** of the `<y,u>`-weighted cross-term estimate,
proved from pointwise AM-GM.  As above, the enlargement and the mass-transport
identification are not proved here. -/
theorem cross_second_bound_proved (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (hw : ∀ ω, 0 ≤ w ω) (y : Site d) :
    |ex w (T4 u K Ky y)| ≤ (1 / 2) * ex w (pairW u K Ky y) + (1 / 2) * ex w (pairQy u K Ky y) := by
  refine (ex_abs_le hw (T4 u K Ky y)).trans ?_
  calc ex w (fun ω => |T4 u K Ky y ω|)
      ≤ ex w (fun ω => (1 / 2) * pairW u K Ky y ω + (1 / 2) * pairQy u K Ky y ω) :=
        ex_mono hw (abs_T4_le u K Ky y)
    _ = (1 / 2) * ex w (pairW u K Ky y) + (1 / 2) * ex w (pairQy u K Ky y) := by
        rw [ex_add, ex_const_mul, ex_const_mul]

/-! ### 3.2b The enlargement and AM-GM steps at the level of pair weights

The paper's estimate of the cross terms has three steps:
(a) write the expectation as a sum over pairs `(x,z)` with the disjoint-occurrence
    weights `Pr(0 <-> x nleftrightarrow y <-> z)`;
(b) *enlarge* the weights to the all-connected weights `Pr(0 <-> x <-> y <-> z)`
    (this is `lem:disjoint_connections`, a hypothesis here);
(c) apply `|ab| <= (a^2+b^2)/2` and then mass transport to identify the two halves
    (the identification is a hypothesis here, labelled `hMT`).
Step (c)'s AM-GM part and the monotone enlargement are proved below; the
coefficient produced is exactly one. -/

/-- **Enlargement of a finite pairing sum**: pointwise larger nonnegative pair
weights increase a sum with nonnegative summands.  In the proof of Lemma I.5.8
this is the step `Pr(0<->x nleftrightarrow y<->z) <= Pr(0<->x<->y<->z)`, supplied
by the BK inequality; only the finite-sum monotonicity is proved here. -/
theorem enlargement_le {ι κ : Type*} (A : Finset ι) (C : Finset κ)
    (Pd Pf : ι → κ → ℝ) (hle : ∀ x ∈ A, ∀ z ∈ C, Pd x z ≤ Pf x z)
    (f : ι → κ → ℝ) (hf : ∀ x ∈ A, ∀ z ∈ C, 0 ≤ f x z) :
    ∑ x ∈ A, ∑ z ∈ C, Pd x z * f x z ≤ ∑ x ∈ A, ∑ z ∈ C, Pf x z * f x z :=
  Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun z hz =>
    mul_le_mul_of_nonneg_right (hle x hx z hz) (hf x hx z hz)

/-- **AM-GM under pair weights**: the second step of the paper's cross-term
estimate, proved.  The two `1/2`-halves are the `<x,u>^2` and `<z-y,u>^2` sums. -/
theorem weighted_pair_abs_le {ι κ : Type*} (A : Finset ι) (C : Finset κ)
    (Pf : ι → κ → ℝ) (hPf : ∀ x ∈ A, ∀ z ∈ C, 0 ≤ Pf x z) (a : ι → ℝ) (b : κ → ℝ) :
    ∑ x ∈ A, ∑ z ∈ C, Pf x z * |a x * b z|
      ≤ (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * a x ^ 2)
        + (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * b z ^ 2) := by
  have hpt : ∀ x ∈ A, ∀ z ∈ C, Pf x z * |a x * b z|
      ≤ (1 / 2) * (Pf x z * a x ^ 2) + (1 / 2) * (Pf x z * b z ^ 2) := by
    intro x hx z hz
    have h0 := hPf x hx z hz
    refine (mul_le_mul_of_nonneg_left (abs_mul_le_half (a x) (b z)) h0).trans_eq ?_
    ring
  refine (Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun z hz => hpt x hx z hz).trans ?_
  have h1 : ∀ x ∈ A, ∑ z ∈ C, ((1 / 2) * (Pf x z * a x ^ 2) + (1 / 2) * (Pf x z * b z ^ 2))
      = (1 / 2) * (∑ z ∈ C, Pf x z * a x ^ 2) + (1 / 2) * (∑ z ∈ C, Pf x z * b z ^ 2) := by
    intro x _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc ∑ x ∈ A, ∑ z ∈ C, ((1 / 2) * (Pf x z * a x ^ 2) + (1 / 2) * (Pf x z * b z ^ 2))
      = ∑ x ∈ A, ((1 / 2) * (∑ z ∈ C, Pf x z * a x ^ 2) +
          (1 / 2) * (∑ z ∈ C, Pf x z * b z ^ 2)) := Finset.sum_congr rfl h1
    _ = (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * a x ^ 2) +
          (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * b z ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  exact le_rfl

/-- The signed version of `weighted_pair_abs_le`. -/
theorem weighted_pair_amgm {ι κ : Type*} (A : Finset ι) (C : Finset κ)
    (Pf : ι → κ → ℝ) (hPf : ∀ x ∈ A, ∀ z ∈ C, 0 ≤ Pf x z) (a : ι → ℝ) (b : κ → ℝ) :
    |∑ x ∈ A, ∑ z ∈ C, Pf x z * (a x * b z)|
      ≤ (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * a x ^ 2)
        + (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * b z ^ 2) := by
  have heq : ∑ x ∈ A, ∑ z ∈ C, |Pf x z * (a x * b z)|
      = ∑ x ∈ A, ∑ z ∈ C, Pf x z * |a x * b z| := by
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun z hz => ?_
    rw [abs_mul, abs_of_nonneg (hPf x hx z hz)]
  calc |∑ x ∈ A, ∑ z ∈ C, Pf x z * (a x * b z)|
      ≤ ∑ x ∈ A, |∑ z ∈ C, Pf x z * (a x * b z)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ A, ∑ z ∈ C, |Pf x z * (a x * b z)| :=
        Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ A, ∑ z ∈ C, Pf x z * |a x * b z| := heq
    _ ≤ (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * a x ^ 2)
        + (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * b z ^ 2) :=
        weighted_pair_abs_le A C Pf hPf a b

/-- **The cross-term estimate of Lemma I.5.8 in the shape of the source**:
enlargement (hypothesis `hle`, the BK inequality `lem:disjoint_connections`),
then AM-GM (proved), then the mass-transport identification of the two halves
(hypothesis `hMT`, the only probabilistic input).  The conclusion carries
coefficient **one**, not one half. -/
theorem enlarged_cross_bound {ι κ : Type*} (A : Finset ι) (C : Finset κ)
    (Pd Pf : ι → κ → ℝ) (hPd : ∀ x ∈ A, ∀ z ∈ C, 0 ≤ Pd x z)
    (hle : ∀ x ∈ A, ∀ z ∈ C, Pd x z ≤ Pf x z)
    (hPf : ∀ x ∈ A, ∀ z ∈ C, 0 ≤ Pf x z) (a : ι → ℝ) (b : κ → ℝ)
    (hMT : ∑ x ∈ A, ∑ z ∈ C, Pf x z * b z ^ 2
      = ∑ x ∈ A, ∑ z ∈ C, Pf x z * a x ^ 2) :
    |∑ x ∈ A, ∑ z ∈ C, Pd x z * (a x * b z)|
      ≤ ∑ x ∈ A, ∑ z ∈ C, Pf x z * a x ^ 2 := by
  have h1 : |∑ x ∈ A, ∑ z ∈ C, Pd x z * (a x * b z)|
      ≤ ∑ x ∈ A, ∑ z ∈ C, Pd x z * |a x * b z| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun z hz => ?_
    rw [abs_mul, abs_of_nonneg (hPd x hx z hz)]
  have h2 : ∑ x ∈ A, ∑ z ∈ C, Pd x z * |a x * b z|
      ≤ ∑ x ∈ A, ∑ z ∈ C, Pf x z * |a x * b z| :=
    enlargement_le A C Pd Pf hle (fun x z => |a x * b z|) (fun _ _ _ _ => abs_nonneg _)
  have h3 : ∑ x ∈ A, ∑ z ∈ C, Pf x z * |a x * b z|
      ≤ (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * a x ^ 2)
        + (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * b z ^ 2) :=
    weighted_pair_abs_le A C Pf hPf a b
  calc |∑ x ∈ A, ∑ z ∈ C, Pd x z * (a x * b z)|
      ≤ ∑ x ∈ A, ∑ z ∈ C, Pd x z * |a x * b z| := h1
    _ ≤ ∑ x ∈ A, ∑ z ∈ C, Pf x z * |a x * b z| := h2
    _ ≤ (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * a x ^ 2)
        + (1 / 2) * (∑ x ∈ A, ∑ z ∈ C, Pf x z * b z ^ 2) := h3
    _ = ∑ x ∈ A, ∑ z ∈ C, Pf x z * a x ^ 2 := by rw [hMT]; ring

/-! ### 3.2 The main terms and the assembly -/

/-- The two factored main terms of (I.5.2). -/
noncomputable def mainTerm (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (B : Finset (Site d)) : ℝ :=
  2 * (B.card : ℝ) * ex w (kcard K) * ex w (kS u K) +
    (ex w (kcard K)) ^ 2 * ∑ y ∈ B, q u y

/-- The four-term right-hand side of `eq:x12_derivative` (the form of the Russo
integrand after the mass-transport collapse of the six-term trinomial
expansion). -/
noncomputable def derivTerm (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) : ℝ :=
  (∑ y ∈ B, ex w (T0 u K Ky y)) + 2 * (∑ y ∈ B, ex w (T2 u K Ky y)) -
    2 * (∑ y ∈ B, ex w (T3 u K Ky y)) - 4 * (∑ y ∈ B, ex w (T4 u K Ky y))

/-- The exact decomposition of the derivative side into the main terms plus the
four remainders.  Pure algebra; no hypothesis. -/
theorem derivTerm_sub_mainTerm
    (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (B : Finset (Site d)) :
    derivTerm w u K Ky B - mainTerm w u K B
      = ((∑ y ∈ B, ex w (T0 u K Ky y)) -
            (ex w (kcard K)) ^ 2 * (∑ y ∈ B, q u y))
        + 2 * ((∑ y ∈ B, ex w (T2 u K Ky y)) -
            (B.card : ℝ) * (ex w (kcard K)) * (ex w (kS u K)))
        - 2 * (∑ y ∈ B, ex w (T3 u K Ky y))
        - 4 * (∑ y ∈ B, ex w (T4 u K Ky y)) := by
  simp only [derivTerm, mainTerm]
  ring

/-- Elementary combination of the paper's four remainder bounds with the
constants exactly as displayed there: the `T3` term carries `1/2`, the `T4` term
`1/2 G + 1/2 Gq`, and `Gq <= U0`.  The total is `3 U0 + 5 G`. -/
theorem abs_assembly (a b c e U0 G Gq : ℝ)
    (h1 : |a| ≤ U0) (h2 : |b| ≤ G) (h3 : |c| ≤ (1 / 2) * G)
    (h4 : |e| ≤ (1 / 2) * G + (1 / 2) * Gq) (h5 : Gq ≤ U0) :
    |a + 2 * b - 2 * c - 4 * e| ≤ 3 * U0 + 5 * G := by
  have ha := abs_le.mp h1
  have hb := abs_le.mp h2
  have hc := abs_le.mp h3
  have he := abs_le.mp h4
  rw [abs_le]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, he.1, he.2]

/-- **Lemma I.5.8: the exact error-bound assembly.**

`derivTerm` is the four-term right-hand side of the paper's `eq:x12_derivative`
(coefficients `1, 2, -2, -4`, audited in the TeX source), `mainTerm` its two
factored main terms `2 |B| E|K| E[S(K)] + (E|K|)^2 sum_{y in B} <y,u>^2`, and

* `U  = ||u||^2 r^2 E[|K|^2 |K cap B|]`,
* `G  = E[|K| |K cap B| S(K)]`,
* `Gq = E[|K|^2 sum_{y in K cap B} <y,u>^2]`.

The hypotheses `hR0`, `hR2`, `hR3`, `hR4` are the paper's four **displayed**
remainder estimates, with the constants as displayed (`1/2` on the `T3` term,
`1/2 G + 1/2 Gq` on the `T4` term), and `hGq : Gq <= U` is the paper's
`\preceq r^2 E[|K|^2 |K cap B_r|]`.  Conclusion: the difference is at most
`3 U + 5 G`, i.e. the two printed `O(...)` terms of (I.5.2) with explicit
absolute constants.

**Status of the inputs.** The decomposition, the summation and triangle
bookkeeping, the constant tracking, and the AM-GM halves
(`cross_first_bound_proved`, `cross_second_bound_proved`) are proved here. The
four displayed estimates are **assumed**: in the paper they follow from the BK
inequality (`lem:disjoint_connections`), the restoration lemma I.2.1,
`lem:BK_disjoint_clusters_covariance` and the mass-transport principle.  Those
derivations are *not* formalised here, and **no mass-transport identity is
asserted**: the mass transport acts on the enlarged (`y notin K`-restriction
dropped) pair weights, see `enlarged_cross_bound`, where it enters as the single
labelled hypothesis `hMT`. -/
theorem lemma_I_5_8_assembly
    (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (B : Finset (Site d)) {r : ℝ}
    (hR0 : |(∑ y ∈ B, ex w (T0 u K Ky y)) -
        (ex w (kcard K)) ^ 2 * (∑ y ∈ B, q u y)|
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
    (hR2 : |(∑ y ∈ B, ex w (T2 u K Ky y)) -
        (B.card : ℝ) * (ex w (kcard K)) * (ex w (kS u K))|
      ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω))
    (hR3 : |∑ y ∈ B, ex w (T3 u K Ky y)|
      ≤ (1 / 2) * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω))
    (hR4 : |∑ y ∈ B, ex w (T4 u K Ky y)|
      ≤ (1 / 2) * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)
        + (1 / 2) * ex w (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)))
    (hGq : ex w (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B))
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω)) :
    |derivTerm w u K Ky B - mainTerm w u K B|
      ≤ 3 * (uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
        + 5 * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  rw [derivTerm_sub_mainTerm]
  exact abs_assembly _ _ _ _ _ _ _ hR0 hR2 hR3 hR4 hGq

/-- As `lemma_I_5_8_assembly`, with the paper's `Gq \preceq U` step discharged by
`Gq_le_U` (Cauchy-Schwarz on the ball plus the counting identity), so that the
only hypotheses left are the four displayed remainder estimates. -/
theorem lemma_I_5_8_assembly_of_ball
    (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (B : Finset (Site d)) {r : ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hB : ∀ y ∈ B, siteNormSq y ≤ r ^ 2)
    (hR0 : |(∑ y ∈ B, ex w (T0 u K Ky y)) -
        (ex w (kcard K)) ^ 2 * (∑ y ∈ B, q u y)|
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
    (hR2 : |(∑ y ∈ B, ex w (T2 u K Ky y)) -
        (B.card : ℝ) * (ex w (kcard K)) * (ex w (kS u K))|
      ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω))
    (hR3 : |∑ y ∈ B, ex w (T3 u K Ky y)|
      ≤ (1 / 2) * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω))
    (hR4 : |∑ y ∈ B, ex w (T4 u K Ky y)|
      ≤ (1 / 2) * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)
        + (1 / 2) * ex w (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B))) :
    |derivTerm w u K Ky B - mainTerm w u K B|
      ≤ 3 * (uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
        + 5 * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) :=
  lemma_I_5_8_assembly u K Ky B hR0 hR2 hR3 hR4 (Gq_le_U u K B hw hB)

/-! ### 3.3 The case `u = 0`

The paper writes "we may assume that `u != 0`, the claim holding vacuously
otherwise".  Here that is not a side condition: both the derivative side and
the main terms are identically zero, with no division by `||u||` anywhere. -/

lemma dot_zero (x : Site d) : dot (0 : Fin d → ℝ) x = 0 := by
  simp [dot]

lemma kS_zero (K : Ω → Finset (Site d)) : kS (0 : Fin d → ℝ) K = fun _ => 0 := by
  funext ω
  simp [kS, sMoment, q_zero]

lemma kDot_zero (K : Ω → Finset (Site d)) : kDot (0 : Fin d → ℝ) K = fun _ => 0 := by
  funext ω
  simp [kDot, dot_zero]

theorem mainTerm_zero (K : Ω → Finset (Site d)) (B : Finset (Site d)) :
    mainTerm w (0 : Fin d → ℝ) K B = 0 := by
  have h1 : ex w (kS (0 : Fin d → ℝ) K) = 0 := by
    rw [kS_zero]; simp [ex]
  have h2 : ∑ y ∈ B, q (0 : Fin d → ℝ) y = 0 := by simp [q_zero]
  rw [mainTerm, h1, h2]
  ring

lemma T0_zero (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) :
    T0 (0 : Fin d → ℝ) K Ky y = fun _ => 0 := by
  funext ω; simp [T0, q_zero]

lemma T2_zero (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) :
    T2 (0 : Fin d → ℝ) K Ky y = fun _ => 0 := by
  funext ω; simp [T2, pairW, kS_zero]

lemma T3_zero (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) :
    T3 (0 : Fin d → ℝ) K Ky y = fun _ => 0 := by
  funext ω; simp [T3, kDot_zero, dot_zero]

lemma T4_zero (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d)) (y : Site d) :
    T4 (0 : Fin d → ℝ) K Ky y = fun _ => 0 := by
  funext ω; simp [T4, kDot_zero, dot_zero]

theorem derivTerm_zero (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (B : Finset (Site d)) : derivTerm w (0 : Fin d → ℝ) K Ky B = 0 := by
  have h0 : ∀ y, ex w (T0 (0 : Fin d → ℝ) K Ky y) = 0 := by
    intro y; rw [T0_zero]; simp [ex]
  have h2 : ∀ y, ex w (T2 (0 : Fin d → ℝ) K Ky y) = 0 := by
    intro y; rw [T2_zero]; simp [ex]
  have h3 : ∀ y, ex w (T3 (0 : Fin d → ℝ) K Ky y) = 0 := by
    intro y; rw [T3_zero]; simp [ex]
  have h4 : ∀ y, ex w (T4 (0 : Fin d → ℝ) K Ky y) = 0 := by
    intro y; rw [T4_zero]; simp [ex]
  simp only [derivTerm, h0, h2, h3, h4, Finset.sum_const_zero,
    mul_zero, add_zero, sub_zero]

/-- The `IsBigO` form of the assembly along a family of radii: a bound that holds
for every `r >= 1` with a fixed constant is an `O`-relation at `r -> infinity`
with reference function `U(r) + G(r)`. -/
theorem remainder_isBigO (R U0 Gg : ℝ → ℝ)
    (h : ∀ r, 1 ≤ r → |R r| ≤ 3 * U0 r + 6 * Gg r)
    (hU : ∀ r, 0 ≤ U0 r) (hG : ∀ r, 0 ≤ Gg r) :
    R =O[Filter.atTop] (fun r => U0 r + Gg r) := by
  refine Asymptotics.IsBigO.of_bound 6 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hU' := hU r
  have hG' := hG r
  have hge : (0 : ℝ) ≤ U0 r + Gg r := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hge]
  have := h r hr
  linarith

end PercLib.CriticalLRP.I58

#print axioms PercLib.CriticalLRP.I58.q_three
#print axioms PercLib.CriticalLRP.I58.q_le_of_siteNormSq_le
#print axioms PercLib.CriticalLRP.I58.sMoment_inter_le
#print axioms PercLib.CriticalLRP.I58.abs_mul_le_half
#print axioms PercLib.CriticalLRP.I58.sum_weighted_ex_le
#print axioms PercLib.CriticalLRP.I58.sum_indIn
#print axioms PercLib.CriticalLRP.I58.remainder_volume_bound
#print axioms PercLib.CriticalLRP.I58.remainder_mass_bound
#print axioms PercLib.CriticalLRP.I58.Gq_le_U
#print axioms PercLib.CriticalLRP.I58.derivTerm_sub_mainTerm
#print axioms PercLib.CriticalLRP.I58.abs_assembly
#print axioms PercLib.CriticalLRP.I58.lemma_I_5_8_assembly
#print axioms PercLib.CriticalLRP.I58.abs_T3_le
#print axioms PercLib.CriticalLRP.I58.abs_T4_le
#print axioms PercLib.CriticalLRP.I58.cross_first_bound_proved
#print axioms PercLib.CriticalLRP.I58.cross_second_bound_proved
#print axioms PercLib.CriticalLRP.I58.dot_pair_abs_le
#print axioms PercLib.CriticalLRP.I58.dot_single_abs_le
#print axioms PercLib.CriticalLRP.I58.mainTerm_zero
#print axioms PercLib.CriticalLRP.I58.derivTerm_zero
#print axioms PercLib.CriticalLRP.I58.enlargement_le
#print axioms PercLib.CriticalLRP.I58.weighted_pair_abs_le
#print axioms PercLib.CriticalLRP.I58.weighted_pair_amgm
#print axioms PercLib.CriticalLRP.I58.enlarged_cross_bound
#print axioms PercLib.CriticalLRP.I58.sum_of_halves_first
#print axioms PercLib.CriticalLRP.I58.sum_of_halves_second
#print axioms PercLib.CriticalLRP.I58.lemma_I_5_8_assembly
#print axioms PercLib.CriticalLRP.I58.lemma_I_5_8_assembly_of_ball
#print axioms PercLib.CriticalLRP.I58.remainder_isBigO
