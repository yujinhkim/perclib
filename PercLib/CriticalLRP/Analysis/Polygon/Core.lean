/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m3/Core.lean ; definitions moved to Defs.lean.
-/
module

/-
Direction C of swarm `smwqozn0q` (member m3): source-scale analytic assembly for
Lemma I.4.18 of T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, p.46.

This file is the *assembly layer*: given the matrix powers `P` of the cutoff two-point function
together with the exact source-level inputs that directions A and B supply, it derives the
displayed estimate of Lemma I.4.18, with the explicit choice `R = r^{α/(2d)}` and explicit
constants `c`, `C` independent of `ell` and `r`.

Nothing here touches production files.
-/

public import PercLib.CriticalLRP.Analysis.Polygon.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.I418C

variable {V : Type*} [Zero V] [DecidableEq V] [Countable V]

/-! ## Matrix powers of a two-point kernel -/

/-- `polyK T n x y` is the `n`-fold matrix power of the kernel `T`, i.e. the polygon diagram
`T^n(x,y)` of the paper (Lemma I.4.17: "`T^ℓ` denotes the `ℓ`-fold power of the two-point matrix
`T(x,y) := P(x ↔ y)`"), specialised to the cutoff two-point function `T = T_{β_c,r}` of
Lemma I.4.18.  It is the intended instance of the abstract family `P` used below. -/
theorem polyK_zero (T : V → V → ℝ) (x y : V) :
    polyK T 0 x y = if x = y then 1 else 0 := rfl

theorem polyK_succ (T : V → V → ℝ) (n : ℕ) (x y : V) :
    polyK T (n + 1) x y = ∑' z, polyK T n x z * T z y := rfl

/-- The one-fold power is the kernel itself. -/
theorem polyK_one (T : V → V → ℝ) (x y : V) : polyK T 1 x y = T x y := by
  have h1 : polyK T 1 x y = ∑' z, (if x = z then (1 : ℝ) else 0) * T z y := by
    rw [polyK_succ]; simp only [polyK_zero]
  rw [h1, tsum_eq_single x (fun b hb => by simp [Ne.symm hb])]
  simp

/-! ## The named source-level inputs

Every field below is a source-level statement about the actual object; none of them is the
conclusion of the lemma.

IMPORTANT: `P` is the family of powers of the *cutoff* two-point function `T_{β_c,r}` and both
sides of `comp` use the *same* kernel.  The paper's first display is read as the composition
identity `T^ℓ = T^3 · T^{ℓ-3}`; the *uncut* open triangle `∇_{β_c}(0,·)` enters only through the
domination `triSup` of the cutoff threefold power and through the far-tail bound `htailc` of the
assembly theorems.  (Mixing the cutoff `P` with the uncut triangle in `comp` would be invalid.)

* `nonneg` — the two-point kernel and all its powers are nonnegative.
* `base` — the zero-th power is the identity matrix.
* `comp` — composition of matrix powers in the paper's form
  `T^ℓ(0,0) = ∑_y T^3(0,y) T^{ℓ-3}(y,0)` (take `ℓ = n+3`); both factors are powers of the same
  cutoff kernel.  Direction B supplies this from the convolution/Fubini development.
* `compSummable` — summability of the family in `comp` (part of the composition argument).
* `colsum` — the column sums of the powers are the powers of the first moment
  `χ = E_{β_c,r}|K| = ∑_y T(y,0)`, i.e. `∑_y T^n(y,0) = χ^n` (row sums plus translation
  invariance).
* `colSummable` — summability of the column sums.
* `entry` — the uniform entry bound `T^n(y,0) ≤ χ^{n-1}` for `n ≥ 1`; this is the paper's
  `T^{ℓ-3}(y,0) ≤ (E|K|)^{ℓ-4}` step, obtained from the column sums (`polyK_entry` derives it for
  `P = polyK T`).
* `selfOne` — `T(0,0) = 1` (the diagonal of a two-point function).
* `triSup` — `T^3_{β_c,r}(0,y) ≤ ∇_{β_c} < ∞`: the cutoff threefold power is dominated by the
  triangle diagram.  This is where the *uncut* open triangle of the source enters: pointwise
  domination `T_{β_c,r} ≤ T_{β_c}` gives `T^3_{β_c,r} ≤ T^3_{β_c} = ∇_{β_c}(0,·)` (monotone
  convergence in `ℝ≥0∞`), and `∇_{β_c}(0,y) ≤ ∇_{β_c}(0,0)` under the triangle condition. -/
namespace PowerInputs

variable {P : ℕ → V → V → ℝ} {nablaT χ : ℝ}

theorem chi_nonneg (H : PowerInputs P nablaT χ) : 0 ≤ χ := by
  have h := H.colsum 1
  rw [pow_one] at h
  rw [← h]
  exact tsum_nonneg (fun y => H.nonneg 1 y 0)

/-! ### The `ℓ = 3` case: the constant bound `T^3(0,0) ≤ ∇_{β_c}`

With `comp` at `n = 0` the paper's first display reads `T^3(0,0) = ∑_y T^3(0,y) T^0(y,0)`; the
`ℓ = 3` case is therefore *definitionally* the diagonal of the threefold power, so the displayed
chain with the exponent `ℓ-4` (a negative power at `ℓ = 3`) is only meaningful for `ℓ ≥ 4`.  The
honest statement in the `ℓ = 3` case is the constant bound below, which is exactly what the
applications use (the coefficient `C_{p,q,3}` of Lemma I.4.17 multiplies `χ^{2p+2q-2} ≤ χ^{2p}`). -/
theorem ell_three_le (H : PowerInputs P nablaT χ) : P 3 0 0 ≤ nablaT :=
  H.triSup 0

end PowerInputs

/-! ## The near/far split

The paper splits `∑_y ∇(0,y) T^{ℓ-3}(y,0)` at the ball of radius `R`.  We phrase the split at an
arbitrary finite set `s` containing the open ball of radius `R`: this keeps the two estimates
independent (the near sum only uses the uniform entry bound `T^n ≤ χ^{n-1}`; the far sum only uses
that `∇` is small off `s`).  The source's card bound `|B_R| ≤ K R^d` then enters as a hypothesis on
`s.card`. -/
theorem split_bound
    {P : ℕ → V → V → ℝ} {nablaT χ : ℝ}
    (H : PowerInputs P nablaT χ)
    (s : Finset V) (w : V → ℝ) (R t : ℝ)
    (ht : 0 ≤ t)
    (hfar : ∀ y : V, y ∉ s → R ≤ w y)
    (htail : ∀ y : V, R ≤ w y → P 3 0 y ≤ t)
    {ell : ℕ} (hell : 4 ≤ ell) :
    P ell 0 0 ≤ t * χ ^ (ell - 3) + nablaT * (s.card : ℝ) * χ ^ (ell - 4) := by
  obtain ⟨n, rfl⟩ : ∃ n, ell = n + 3 := ⟨ell - 3, by omega⟩
  have hn : 1 ≤ n := by omega
  have hchi : 0 ≤ χ := H.chi_nonneg
  have hsplit' := (H.compSummable n).sum_add_tsum_compl (s := s)
  -- far part
  have hsplit' : (∑ x ∈ s, P 3 0 x * P n x 0)
      + (∑' x : {x // x ∉ (s : Set V)}, P 3 0 x * P n x 0) = ∑' x, P 3 0 x * P n x 0 :=
    (H.compSummable n).sum_add_tsum_compl (s := s)
  -- far part
  have hfar_le : (∑' x : {x // x ∉ (s : Set V)}, P 3 0 x * P n x 0) ≤ t * χ ^ n := by
    have h₁ : (∑' x : {x // x ∉ (s : Set V)}, P 3 0 x * P n x 0)
        ≤ ∑' x : {x // x ∉ (s : Set V)}, t * P n x 0 := by
      refine Summable.tsum_le_tsum (fun x => ?_) ((H.compSummable n).subtype _)
        (((H.colSummable n).subtype _).mul_left t)
      exact mul_le_mul_of_nonneg_right (htail (x : V) (hfar (x : V) x.2)) (H.nonneg n (x : V) 0)
    have h₂ : (∑' x : {x // x ∉ (s : Set V)}, t * P n x 0)
        = t * ∑' x : {x // x ∉ (s : Set V)}, P n x 0 := tsum_mul_left
    have h₃ : (∑' x : {x // x ∉ (s : Set V)}, P n x 0) ≤ χ ^ n := by
      have hsplit2 : (∑ x ∈ s, P n x 0) + (∑' x : {x // x ∉ (s : Set V)}, P n x 0) = χ ^ n := by
        have h0 := (H.colSummable n).sum_add_tsum_compl (s := s)
        rw [H.colsum n] at h0
        exact h0
      have hnn : 0 ≤ ∑ x ∈ s, P n x 0 := Finset.sum_nonneg fun x _ => H.nonneg n x 0
      linarith
    calc (∑' x : {x // x ∉ (s : Set V)}, P 3 0 x * P n x 0)
        ≤ ∑' x : {x // x ∉ (s : Set V)}, t * P n x 0 := h₁
      _ = t * ∑' x : {x // x ∉ (s : Set V)}, P n x 0 := h₂
      _ ≤ t * χ ^ n := mul_le_mul_of_nonneg_left h₃ ht
  -- near part
  have hnear_le : (∑ x ∈ s, P 3 0 x * P n x 0) ≤ nablaT * (s.card : ℝ) * χ ^ (n - 1) := by
    have hstep : ∀ x ∈ s, P 3 0 x * P n x 0 ≤ nablaT * χ ^ (n - 1) := by
      intro x _
      have h1 : P 3 0 x ≤ nablaT := H.triSup x
      have h2 : P n x 0 ≤ χ ^ (n - 1) := H.entry n hn x
      have h0 : 0 ≤ P 3 0 x := H.nonneg 3 0 x
      have h3 : 0 ≤ χ ^ (n - 1) := pow_nonneg hchi _
      nlinarith [h1, h2, h0, h3]
    calc (∑ x ∈ s, P 3 0 x * P n x 0) ≤ ∑ x ∈ s, nablaT * χ ^ (n - 1) := Finset.sum_le_sum hstep
      _ = (s.card : ℝ) * (nablaT * χ ^ (n - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = nablaT * (s.card : ℝ) * χ ^ (n - 1) := by ring
  have hexp : n - 1 = n + 3 - 4 := by omega
  have hexp3 : n + 3 - 3 = n := by omega
  rw [H.comp n, ← hsplit', hexp3]
  rw [hexp] at hnear_le
  linarith [hfar_le, hnear_le]

/-! ## The arithmetic of the final line

With `|B_R| ≤ K R^d`, `χ ≥ c₀ r^α` and `R = r^{α/(2d)}` we have
`|B_R| χ^{ℓ-4} ≤ (K/c₀) r^{-α/2} χ^{ℓ-3}`, and `r^{-α/2} ≤ r^{-c}` for `r ≥ 1`,
`c ≤ α/2`. -/

/-- The near term after inserting the card bound and `R = r^{α/(2d)}`. -/
theorem near_arith
    {nablaT K c₀ r α cc χ : ℝ} {ell : ℕ}
    (hnab : 0 ≤ nablaT) (hK : 0 ≤ K) (hc₀ : 0 < c₀)
    (hr : 1 ≤ r) (hell : 4 ≤ ell)
    (hcc : cc ≤ α / 2)
    (hχ : c₀ * r ^ α ≤ χ) :
    nablaT * K * r ^ (α / 2) * χ ^ (ell - 4)
      ≤ (nablaT * K / c₀) * r ^ (-cc) * χ ^ (ell - 3) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hχ0 : 0 < χ := lt_of_lt_of_le (by positivity) hχ
  have hχnn : 0 ≤ χ := le_of_lt hχ0
  have hpow : 0 ≤ χ ^ (ell - 4) := pow_nonneg hχnn _
  have hcostep : 0 ≤ nablaT * K * r ^ (α / 2) := by positivity
  -- step 1: `χ^{ℓ-4} * (c₀ r^α) ≤ χ^{ℓ-3}`
  have hstep : χ ^ (ell - 4) * (c₀ * r ^ α) ≤ χ ^ (ell - 3) := by
    have h1 : χ ^ (ell - 3) = χ ^ (ell - 4) * χ := by
      have : ell - 3 = (ell - 4) + 1 := by omega
      rw [this, pow_succ]
    rw [h1]
    exact mul_le_mul_of_nonneg_left hχ hpow
  have hA : χ ^ (ell - 4) ≤ χ ^ (ell - 3) / (c₀ * r ^ α) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hstep]
  have hB : nablaT * K * r ^ (α / 2) * χ ^ (ell - 4)
      ≤ nablaT * K * r ^ (α / 2) * (χ ^ (ell - 3) / (c₀ * r ^ α)) :=
    mul_le_mul_of_nonneg_left hA hcostep
  have hdiv : r ^ (α / 2) / r ^ α = r ^ (-α / 2) := by
    rw [← Real.rpow_sub hr0]; ring_nf
  have hC : nablaT * K * r ^ (α / 2) * (χ ^ (ell - 3) / (c₀ * r ^ α))
      = (nablaT * K / c₀) * r ^ (-α / 2) * χ ^ (ell - 3) := by
    rw [← hdiv]
    field_simp
  have hexp : r ^ (-α / 2) ≤ r ^ (-cc) := by
    refine Real.rpow_le_rpow_of_exponent_le hr ?_
    linarith
  have hfin : (nablaT * K / c₀) * r ^ (-α / 2) * χ ^ (ell - 3)
      ≤ (nablaT * K / c₀) * r ^ (-cc) * χ ^ (ell - 3) := by
    have h1 : 0 ≤ nablaT * K / c₀ := by positivity
    have h2 : 0 ≤ χ ^ (ell - 3) := pow_nonneg hχnn _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h1) h2
  calc nablaT * K * r ^ (α / 2) * χ ^ (ell - 4)
      ≤ nablaT * K * r ^ (α / 2) * (χ ^ (ell - 3) / (c₀ * r ^ α)) := hB
    _ = (nablaT * K / c₀) * r ^ (-α / 2) * χ ^ (ell - 3) := hC
    _ ≤ (nablaT * K / c₀) * r ^ (-cc) * χ ^ (ell - 3) := hfin

/-! ## The card bound `|B_R| ≤ K R^d` at `R = r^{α/(2d)}` -/

theorem rpow_card {R r α : ℝ} {d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d)
    (hR : R = r ^ (α / (2 * (d : ℝ)))) :
    R ^ (d : ℝ) = r ^ (α / 2) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [hR, ← Real.rpow_mul hr0.le]
  congr 1
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 0 < (d : ℝ) := by exact_mod_cast hd
    exact ne_of_gt this
  field_simp

/-! ## Lemma I.4.18, assembled -/

/-- **Lemma I.4.18 (analytic assembly, `ℓ ≥ 4`).**

Let `χ = E_{β_c,r}|K|`, `∇(0,·)` the open triangle, `∇_{r^c}` its tail, and `P` the matrix
powers of the cutoff two-point function, with the source-level inputs `PowerInputs`.
Take `R = r^{α/(2d)}` and `c = α/(4d)`.  Then

  `T^ℓ(0,0) ≤ max 1 (∇_{β_c} K / c₀) (∇_{r^c} + r^{-c}) χ^{ℓ-3}`

for every `ℓ ≥ 4` and every `r ≥ 1`.  The constant `max 1 (∇ K / c₀)` does not depend on `ℓ`
or on `r`.  The hypotheses are:

* `hfar` — `s` contains the open ball of radius `R`;
* `htailc` — `∇(0,y) ≤ ∇_{r^c}` for `‖y‖ ≥ r^c`;
* `hcard` — the normalized ball estimate `|B_R| ≤ K R^d`;
* `hχ` — the first-moment lower comparison `χ ≥ c₀ r^α`. -/
theorem polygon_bound
    {P : ℕ → V → V → ℝ} {nablaT χ : ℝ}
    (H : PowerInputs P nablaT χ)
    (s : Finset V) (w : V → ℝ) (r R trc : ℝ) {d : ℕ} {α c₀ K cc : ℝ}
    (hα : 0 < α) (hd : 1 ≤ d) (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hr : 1 ≤ r)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = α / (4 * (d : ℝ)))
    (hfar : ∀ y : V, y ∉ s → R ≤ w y)
    (htailc : ∀ y : V, r ^ cc ≤ w y → P 3 0 y ≤ trc)
    (htrc : 0 ≤ trc)
    (hcard : (s.card : ℝ) ≤ K * R ^ (d : ℝ))
    (hR : R = r ^ (α / (2 * (d : ℝ))))
    (hχ : c₀ * r ^ α ≤ χ) :
    P ell 0 0 ≤ max 1 (nablaT * K / c₀) * (trc + r ^ (-cc)) * χ ^ (ell - 3) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hcc0 : 0 < cc := by
    rw [hct]; positivity
  have hccd : cc ≤ α / (2 * (d : ℝ)) := by
    rw [hct]
    have hb : (0 : ℝ) < 2 * (d : ℝ) := by linarith
    have hc : 2 * (d : ℝ) ≤ 4 * (d : ℝ) := by linarith
    exact div_le_div_of_nonneg_left (le_of_lt hα) hb hc
  have hcc2 : cc ≤ α / 2 := by
    have hd2 : α / (2 * (d : ℝ)) ≤ α / 2 := by
      have hb : (0 : ℝ) < 2 := by norm_num
      have hc : (2 : ℝ) ≤ 2 * (d : ℝ) := by linarith
      exact div_le_div_of_nonneg_left (le_of_lt hα) hb hc
    linarith
  have hRc : r ^ cc ≤ R := by
    rw [hR]
    exact Real.rpow_le_rpow_of_exponent_le hr hccd
  have hnab : 0 ≤ nablaT := le_trans (H.nonneg 3 0 0) (H.triSup 0)
  -- the split, with `t := trc`
  have hsplit := split_bound H s w R trc htrc hfar
    (fun y hy => htailc y (le_trans hRc hy)) hell
  -- near term
  have hRd : R ^ (d : ℝ) = r ^ (α / 2) := rpow_card hr hd hR
  have hcard' : (nablaT * (s.card : ℝ) * χ ^ (ell - 4))
      ≤ nablaT * K * r ^ (α / 2) * χ ^ (ell - 4) := by
    have hy : χ ^ (ell - 4) ≥ 0 := pow_nonneg H.chi_nonneg _
    have h1 : (s.card : ℝ) ≤ K * r ^ (α / 2) := by
      refine le_trans hcard ?_
      rw [hRd]
    have h2 : nablaT * (s.card : ℝ) ≤ nablaT * (K * r ^ (α / 2)) :=
      mul_le_mul_of_nonneg_left h1 hnab
    have h3 : nablaT * (s.card : ℝ) * χ ^ (ell - 4) ≤ nablaT * (K * r ^ (α / 2)) * χ ^ (ell - 4) :=
      mul_le_mul_of_nonneg_right h2 hy
    calc nablaT * (s.card : ℝ) * χ ^ (ell - 4)
        ≤ nablaT * (K * r ^ (α / 2)) * χ ^ (ell - 4) := h3
      _ = nablaT * K * r ^ (α / 2) * χ ^ (ell - 4) := by ring
  have hnear := near_arith (nablaT := nablaT) (K := K) (c₀ := c₀) (r := r) (α := α)
    (cc := cc) (χ := χ) (ell := ell) hnab hK hc₀ hr hell hcc2 hχ
  -- combine
  have hC1 : (0 : ℝ) < max 1 (nablaT * K / c₀) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCp : (nablaT * K / c₀) ≤ max 1 (nablaT * K / c₀) := le_max_right _ _
  have hχn : 0 ≤ χ ^ (ell - 3) := pow_nonneg H.chi_nonneg _
  have hrm : 0 ≤ r ^ (-cc) := le_of_lt (Real.rpow_pos_of_pos hr0 _)
  have hsum : trc * χ ^ (ell - 3) + (nablaT * K / c₀) * r ^ (-cc) * χ ^ (ell - 3)
      ≤ max 1 (nablaT * K / c₀) * (trc + r ^ (-cc)) * χ ^ (ell - 3) := by
    have h1 : trc * χ ^ (ell - 3) ≤ max 1 (nablaT * K / c₀) * trc * χ ^ (ell - 3) := by
      have : trc ≤ max 1 (nablaT * K / c₀) * trc := by
        nlinarith [le_max_left (1 : ℝ) (nablaT * K / c₀), htrc]
      exact mul_le_mul_of_nonneg_right this hχn
    have h2 : (nablaT * K / c₀) * r ^ (-cc) * χ ^ (ell - 3)
        ≤ max 1 (nablaT * K / c₀) * r ^ (-cc) * χ ^ (ell - 3) := by
      apply mul_le_mul_of_nonneg_right _ hχn
      exact mul_le_mul_of_nonneg_right hCp hrm
    have h3 : max 1 (nablaT * K / c₀) * trc * χ ^ (ell - 3)
        + max 1 (nablaT * K / c₀) * r ^ (-cc) * χ ^ (ell - 3)
        = max 1 (nablaT * K / c₀) * (trc + r ^ (-cc)) * χ ^ (ell - 3) := by ring
    linarith [h1, h2, h3]
  linarith [hsplit, hcard', hnear, hsum]

/-- **Lemma I.4.18 in the form of the source**, i.e. with the supremum over `x`:
`sup_x T^ℓ(0,x) ≤ C(∇_{r^c} + r^{-c}) χ^{ℓ-3}`.  The input `hdiag` is direction A's
diagonal maximality `T^ℓ(0,x) ≤ T^ℓ(0,0)`, which is where translation invariance and positive
definiteness of the cutoff two-point function are used. -/
theorem polygon_bound_sup
    {P : ℕ → V → V → ℝ} {nablaT χ : ℝ}
    (H : PowerInputs P nablaT χ)
    (s : Finset V) (w : V → ℝ) (r R trc : ℝ) {d : ℕ} {α c₀ K cc : ℝ}
    (hα : 0 < α) (hd : 1 ≤ d) (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hr : 1 ≤ r)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = α / (4 * (d : ℝ)))
    (hfar : ∀ y : V, y ∉ s → R ≤ w y)
    (htailc : ∀ y : V, r ^ cc ≤ w y → P 3 0 y ≤ trc)
    (htrc : 0 ≤ trc)
    (hcard : (s.card : ℝ) ≤ K * R ^ (d : ℝ))
    (hR : R = r ^ (α / (2 * (d : ℝ))))
    (hχ : c₀ * r ^ α ≤ χ)
    (hdiag : ∀ x : V, P ell 0 x ≤ P ell 0 0) :
    ∀ x : V, P ell 0 x ≤ max 1 (nablaT * K / c₀) * (trc + r ^ (-cc)) * χ ^ (ell - 3) := by
  have h := polygon_bound H s w r R trc hα hd hc₀ hK hr hell hct hfar htailc htrc hcard hR hχ
  intro x
  exact le_trans (hdiag x) h

/-- The same estimate in the shape displayed in the task statement,
`C (∇_{r^c} + r^{-c} χ^{ℓ-3})`.

Note the two shapes differ by the placement of one parenthesis, and the difference is essential:
the paper's shape `C(∇_{r^c} + r^{-c}) χ^{ℓ-3}` is the one that comes out of the near/far split
(the far sum is bounded by `∇_{r^c} ∑_y T^{ℓ-3}(y,0) = ∇_{r^c} χ^{ℓ-3}`), and it *implies* the
shape below exactly when `χ^{ℓ-3} ≤ 1`.  For `χ^{ℓ-3} ≥ 1` the shape below is strictly stronger and
is not available from this argument. -/
theorem polygon_bound_displayed
    {P : ℕ → V → V → ℝ} {nablaT χ : ℝ}
    (H : PowerInputs P nablaT χ)
    (s : Finset V) (w : V → ℝ) (r R trc : ℝ) {d : ℕ} {α c₀ K cc : ℝ}
    (hα : 0 < α) (hd : 1 ≤ d) (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hr : 1 ≤ r)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = α / (4 * (d : ℝ)))
    (hfar : ∀ y : V, y ∉ s → R ≤ w y)
    (htailc : ∀ y : V, r ^ cc ≤ w y → P 3 0 y ≤ trc)
    (htrc : 0 ≤ trc)
    (hcard : (s.card : ℝ) ≤ K * R ^ (d : ℝ))
    (hR : R = r ^ (α / (2 * (d : ℝ))))
    (hχ : c₀ * r ^ α ≤ χ)
    (hχ1 : χ ^ (ell - 3) ≤ 1)
    (hdiag : ∀ x : V, P ell 0 x ≤ P ell 0 0) :
    ∀ x : V, P ell 0 x ≤ max 1 (nablaT * K / c₀) * (trc + r ^ (-cc) * χ ^ (ell - 3)) := by
  have h := polygon_bound_sup H s w r R trc hα hd hc₀ hK hr hell hct hfar htailc htrc hcard hR hχ
    hdiag
  have hC : (0 : ℝ) ≤ max 1 (nablaT * K / c₀) := le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  intro x
  refine le_trans (h x) ?_
  have hχn : 0 ≤ χ ^ (ell - 3) := pow_nonneg H.chi_nonneg _
  have hrm : 0 ≤ r ^ (-cc) := le_of_lt (Real.rpow_pos_of_pos (zero_lt_one.trans_le hr) _)
  have hkey : (trc + r ^ (-cc)) * χ ^ (ell - 3) ≤ trc + r ^ (-cc) * χ ^ (ell - 3) := by
    have h4 : trc * χ ^ (ell - 3) ≤ trc * 1 :=
      mul_le_mul_of_nonneg_left hχ1 htrc
    nlinarith [h4]
  calc max 1 (nablaT * K / c₀) * (trc + r ^ (-cc)) * χ ^ (ell - 3)
      = max 1 (nablaT * K / c₀) * ((trc + r ^ (-cc)) * χ ^ (ell - 3)) := by ring
    _ ≤ max 1 (nablaT * K / c₀) * (trc + r ^ (-cc) * χ ^ (ell - 3)) := by
        exact mul_le_mul_of_nonneg_left hkey hC

/-- The matrix powers of a nonnegative kernel are nonnegative. -/
theorem polyK_nonneg (T : V → V → ℝ) (hT : ∀ x y, 0 ≤ T x y) (n : ℕ) (x y : V) :
    0 ≤ polyK T n x y := by
  induction n generalizing x y with
  | zero =>
    rw [polyK_zero]
    split <;> norm_num
  | succ n ih =>
    rw [polyK_succ]
    exact tsum_nonneg fun z => mul_nonneg (ih x z) (hT z y)

/-- **The paper's `T^{ℓ-3}(y,0) ≤ (E|K|)^{ℓ-4}` step**, derived from the column sums.

For the intended instance `P = polyK T` the uniform entry bound `entry` of `PowerInputs` is a
*consequence* of the column sums `∑_y T(y,0) = χ` and `T ≤ 1`, not an extra assumption: the
one-fold power is `≤ 1 = χ^0`, and each further power multiplies the bound by `∑_z T(z,0) = χ`. -/
theorem polyK_entry (T : V → V → ℝ) (hnn : ∀ x y, 0 ≤ T x y) (hT1 : ∀ x y, T x y ≤ 1)
    {χ : ℝ} (hcol : ∀ z : V, ∑' w, T w z = χ)
    (hcolSummable : ∀ z : V, Summable (fun w => T w z))
    (hstep : ∀ (n : ℕ) (y z : V), Summable (fun w => polyK T n y w * T w z)) :
    ∀ (n : ℕ), 1 ≤ n → ∀ y : V, polyK T n y 0 ≤ χ ^ (n - 1) := by
  have hχ0 : 0 ≤ χ := by
    rw [← hcol 0]
    exact tsum_nonneg (fun w => hnn w 0)
  have hmain : ∀ (n : ℕ), 1 ≤ n → ∀ y z : V, polyK T n y z ≤ χ ^ (n - 1) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro _ y z
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [polyK_one]
        simpa using hT1 y z
      · have hIH : ∀ w : V, polyK T n y w ≤ χ ^ (n - 1) := fun w => ih hn y w
        have h1 : polyK T (n + 1) y z ≤ ∑' w, χ ^ (n - 1) * T w z := by
          rw [polyK_succ]
          refine Summable.tsum_le_tsum (fun w => ?_) (hstep n y z) ((hcolSummable z).mul_left _)
          exact mul_le_mul_of_nonneg_right (hIH w) (hnn w z)
        have h2 : (∑' w, χ ^ (n - 1) * T w z) = χ ^ (n - 1) * χ := by
          rw [tsum_mul_left, hcol z]
        have h3 : χ ^ (n - 1) * χ = χ ^ (n + 1 - 1) := by
          rw [show n + 1 - 1 = n from by omega, show n = (n - 1) + 1 from by omega]
          exact (pow_succ χ (n - 1)).symm
        calc polyK T (n + 1) y z ≤ ∑' w, χ ^ (n - 1) * T w z := h1
          _ = χ ^ (n - 1) * χ := h2
          _ = χ ^ (n + 1 - 1) := h3
  exact fun n hn y => hmain n hn y 0

/-! ## The cutoff threefold power versus the uncut open triangle

`triSup` is about `P 3 0 ·`, the threefold power of the *cutoff* kernel.  To bound it by the
triangle diagram one compares with the *uncut* threefold power pointwise; the two lemmas below
reduce that comparison to summability of the uncut two- and three-step convolutions. -/

theorem polyK_two (T : V → V → ℝ) (x y : V) : polyK T 2 x y = ∑' v, T x v * T v y := by
  have h : (2 : ℕ) = 1 + 1 := rfl
  rw [h, polyK_succ]
  simp only [polyK_one]

theorem polyK_three (T : V → V → ℝ) (x y : V) :
    polyK T 3 x y = ∑' u, (∑' v, T x v * T v u) * T u y := by
  have h : (3 : ℕ) = 2 + 1 := rfl
  rw [h, polyK_succ]
  simp only [polyK_two]

/-- **Pointwise domination of the threefold powers.**  If `A ≤ B` pointwise and the uncut
two- and three-step convolutions of `B` are summable, then `A^3 ≤ B^3` pointwise.  At the model,
`A = T_{β_c,r}` is the cutoff two-point function, `B = τ_{β_c}` is the uncut one
(`SourceModelData.cutTwoPoint_le_twoPoint`), and the two summability hypotheses are the finiteness
of the two- and threefold convolutions of the uncut two-point function under the triangle
condition. -/
theorem polyK_three_mono {A B : V → V → ℝ} (hA : ∀ x y, 0 ≤ A x y) (hAB : ∀ x y, A x y ≤ B x y)
    (hB2 : ∀ u : V, Summable (fun v => B 0 v * B v u))
    (hB3 : ∀ y : V, Summable (fun u => (∑' v, B 0 v * B v u) * B u y)) :
    ∀ y : V, polyK A 3 0 y ≤ polyK B 3 0 y := by
  have hBnn : ∀ x y, 0 ≤ B x y := fun x y => (hA x y).trans (hAB x y)
  -- step 1: the twofold powers
  have h2 : ∀ u : V, (∑' v, A 0 v * A v u) ≤ ∑' v, B 0 v * B v u := by
    intro u
    have hsumA : Summable (fun v => A 0 v * A v u) :=
      Summable.of_nonneg_of_le (fun v => mul_nonneg (hA 0 v) (hA v u))
        (fun v => mul_le_mul (hAB 0 v) (hAB v u) (hA v u) (hBnn 0 v)) (hB2 u)
    exact Summable.tsum_le_tsum
      (fun v => mul_le_mul (hAB 0 v) (hAB v u) (hA v u) (hBnn 0 v)) hsumA (hB2 u)
  -- step 2: the threefold powers
  intro y
  rw [polyK_three, polyK_three]
  have hB2nn : ∀ u : V, 0 ≤ ∑' v, B 0 v * B v u :=
    fun u => tsum_nonneg fun v => mul_nonneg (hBnn 0 v) (hBnn v u)
  have hsumA : Summable (fun u => (∑' v, A 0 v * A v u) * A u y) :=
    Summable.of_nonneg_of_le
      (fun u => mul_nonneg (tsum_nonneg fun v => mul_nonneg (hA 0 v) (hA v u)) (hA u y))
      (fun u => mul_le_mul (h2 u) (hAB u y) (hA u y) (hB2nn u)) (hB3 y)
  exact Summable.tsum_le_tsum
    (fun u => mul_le_mul (h2 u) (hAB u y) (hA u y) (hB2nn u)) hsumA (hB3 y)

/-! ## The `ℓ = 3` obstruction, for the intended instance

For `P = polyK T` the value `T^3(0,0)` is at least `T(0,0)^3 = 1`.  Since `∇_{r^c} + r^{-c} → 0`
in `r` under the triangle condition (Kozma's theorem), the `ℓ = 3` case of the printed display
cannot hold in the shape `T^3(0,0) ≤ C(∇_{r^c} + r^{-c}) χ^0`.  In the applications the `ℓ = 3`
term is used with the constant bound `T^3(0,0) ≤ ∇_{β_c} < ∞` of `PowerInputs.ell_three_le`. -/
theorem one_le_polyK_three (T : V → V → ℝ) (hT : ∀ x y, 0 ≤ T x y) (h00 : T 0 0 = 1)
    (h1 : Summable (fun z => polyK T 1 0 z * T z 0))
    (h2 : Summable (fun z => polyK T 2 0 z * T z 0)) :
    1 ≤ polyK T 3 0 0 := by
  have hstep : ∀ (n : ℕ), Summable (fun z => polyK T n 0 z * T z 0) →
      polyK T n 0 0 * T 0 0 ≤ polyK T (n + 1) 0 0 := by
    intro n hn
    rw [polyK_succ]
    have h := Summable.sum_le_tsum (f := fun z => polyK T n 0 z * T z 0) ({0} : Finset V)
      (fun i _ => mul_nonneg (polyK_nonneg T hT n 0 i) (hT i 0)) hn
    simpa using h
  have h1' : polyK T 1 0 0 = 1 := by rw [polyK_one, h00]
  have hA : 1 ≤ polyK T 2 0 0 := by
    have h := hstep 1 h1
    rw [h1', h00, mul_one] at h
    exact h
  have hB : polyK T 2 0 0 ≤ polyK T 3 0 0 := by
    have h := hstep 2 h2
    rwa [h00, mul_one] at h
  linarith

end PercLib.CriticalLRP.I418C
