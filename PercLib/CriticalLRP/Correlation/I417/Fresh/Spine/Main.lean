/-
Independently built for swarm `smwxcafk7`, member `m1`, direction
`GENERAL-Q-WEIGHTED-EVALUATION`.  Read-only against production
`repo/.scratch/critical-lrp-orchestration` at HEAD `8d1c9eb`.  Proofs only; the definitions live in
`Defs.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Spine.Defs

/-!
# The generic spine tree-sum

Hanging forests contribute `χ`, and the pin--mark chain contributes `T^ℓ`.

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied paper text pp. 43--46, lines 2444--2513).

`Hang.val_eq_pow` is the "every off-path vertex supplies exactly one `χ`" step, in its sharp form:
a hanging forest of `m` vertices contributes `χ ^ m` **for every base vertex**.  Because the answer
does not depend on the base, the peel order is irrelevant and no branch enumeration is needed.

`spineVal_eq` is the whole tree sum: a `y`--`w` chain of `ℓ` legs with hanging forests of total size
`N` at its spine vertices evaluates to `χ ^ N · T^ℓ(y,w)`.  `spineVal_eq_normal` is the printed
normalisation with `N = 2q - ℓ`, i.e. `(2q - ℓ) + ℓ = 2q` two-point factors.

`spineVal_eq_kernel` is the `kernel π` form in the orientation of
`I417FreshFour.Eval.freshFourProfile` and of the `q = 5` candidate profile, `T^ℓ(w,y)`.

The worked instances `spineVal_four_profile_first` / `_last` / `spineVal_hub` reproduce the values
of
accepted `q = 4` cover members (`χ⁴T⁴`, `χ⁷T`, `χ^m T`) with no peel-order computation, so the
theorem is not vacuous.

Hypotheses used: `[DecidableEq V]`, and the constant row sum `∑_z τ(a,z) = χ`.  No `[Countable V]`,
no probability, no BK, no moment or subcriticality hypothesis; exactly as in the accepted `q = 4`
engine (`Fresh/Eval/Engine.lean`).-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false





open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal


@[expose] public section

namespace PercLib.CriticalLRP.I417FreshGenSpine

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Base
open PercLib.CriticalLRP.I417FreshFour.Eval (tau_symm)

variable {V : Type*}

namespace Hang

@[simp] theorem size_nil : (nil : Hang).size = 0 := rfl

@[simp] theorem size_cons (c r : Hang) : (cons c r).size = c.size + 1 + r.size := rfl

@[simp] theorem size_star : ∀ (m : ℕ), (star m).size = m
  | 0 => rfl
  | (m + 1) => by
      have h : (star (m + 1)).size = (nil : Hang).size + 1 + (star m).size := rfl
      rw [h]
      simp only [size_nil, size_star m]
      omega

/-- **Every hanging forest contributes exactly one `χ` per vertex.**  The base vertex plays no
role, which is precisely why the peel can be performed in *any* order and why no branch-by-branch
computation is needed. -/
theorem val_eq_pow (tau : V → V → ℝ≥0∞) (chi : ℝ≥0∞) (hchi : ∀ a : V, ∑' b : V, tau a b = chi) :
    ∀ (F : Hang) (a : V), F.val tau a = chi ^ F.size
  | .nil, _ => by simp [val, size]
  | .cons c r, a => by
      have hc : ∀ b : V, val tau c b = chi ^ c.size := fun b => val_eq_pow tau chi hchi c b
      have hr : val tau r a = chi ^ r.size := val_eq_pow tau chi hchi r a
      have h1 : chi ^ (c.size + 1) = chi * chi ^ c.size := by
        rw [pow_add, pow_one, mul_comm]
      have h2 : chi ^ (c.size + 1 + r.size) = chi ^ (c.size + 1) * chi ^ r.size := by
        rw [pow_add]
      simp only [val, hc, hr, size]
      rw [ENNReal.tsum_mul_right, hchi, h2, h1]

end Hang

variable [DecidableEq V]

/-- **The generic spine tree-sum.**  A tree diagram that is a `y`--`w` chain of `ℓ` legs with
hanging forests of total size `N` at its spine vertices evaluates to `χ ^ N · T^ℓ(y,w)`.

This is the order-free substitute for the 48 (resp. 384) hand-ordered branch evaluations of the
accepted `q = 4` cover and of the `q = 5` candidate: it covers *every* tree shape at once. -/
theorem spineVal_eq (tau : V → V → ℝ≥0∞) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, tau a b = chi) :
    ∀ (ℓ : ℕ) (Fs : Fin (ℓ + 1) → Hang) (y w : V),
      spineVal tau ℓ Fs y w = chi ^ (∑ i : Fin (ℓ + 1), (Fs i).size) * iterPow tau ℓ y w
  | 0, Fs, y, w => by
      rw [Fin.sum_univ_one]
      by_cases h : y = w
      · rw [h,
          show spineVal tau 0 Fs w w = Hang.val tau (Fs 0) w from by simp [spineVal],
          show iterPow tau 0 w w = 1 from by simp [iterPow],
          Hang.val_eq_pow tau chi hchi]
        ring
      · simp [spineVal, iterPow, h]
  | (ℓ + 1), Fs, y, w => by
      have ih : ∀ u : V, spineVal tau ℓ (fun i : Fin (ℓ + 1) => Fs i.succ) u w =
          chi ^ (∑ i : Fin (ℓ + 1), (Fs i.succ).size) * iterPow tau ℓ u w :=
        fun u => spineVal_eq tau chi hchi ℓ _ u w
      have hpush : (∑' u : V,
            tau y u * (chi ^ (∑ i : Fin (ℓ + 1), (Fs i.succ).size) * iterPow tau ℓ u w)) =
          chi ^ (∑ i : Fin (ℓ + 1), (Fs i.succ).size) *
            (∑' u : V, tau y u * iterPow tau ℓ u w) := by
        rw [show chi ^ (∑ i : Fin (ℓ + 1), (Fs i.succ).size) *
              (∑' u : V, tau y u * iterPow tau ℓ u w) =
            (∑' u : V, tau y u * iterPow tau ℓ u w) *
              chi ^ (∑ i : Fin (ℓ + 1), (Fs i.succ).size) from mul_comm _ _,
          ← ENNReal.tsum_mul_right]
        exact tsum_congr fun u => by ring
      have hstep : iterPow tau (ℓ + 1) y w = ∑' u : V, tau y u * iterPow tau ℓ u w := rfl
      have hsum : (∑ i : Fin (ℓ + 2), (Fs i).size) =
          (Fs 0).size + ∑ i : Fin (ℓ + 1), (Fs i.succ).size := by
        rw [Fin.sum_univ_succ]
      simp only [spineVal, ih, hpush, Hang.val_eq_pow tau chi hchi]
      rw [hstep, hsum, pow_add]
      ring

/-- **The printed normalisation.**  If the `2 q` legs of the diagram split as `ℓ` path legs and
`2 q - ℓ` hanging vertices, the value is `χ ^ (2q-ℓ) · T^ℓ(y,w)`: exactly `(2q - ℓ) + ℓ = 2q`
two-point factors, the fresh side of Lemma I.4.17. -/
theorem spineVal_eq_normal (tau : V → V → ℝ≥0∞) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, tau a b = chi) (ℓ q : ℕ) (Fs : Fin (ℓ + 1) → Hang) (y w : V)
    (hlen : (∑ i : Fin (ℓ + 1), (Fs i).size) = 2 * q - ℓ) :
    spineVal tau ℓ Fs y w = chi ^ (2 * q - ℓ) * iterPow tau ℓ y w := by
  rw [spineVal_eq tau chi hchi, hlen]

variable [Countable V]

/-- The symmetric-kernel form used everywhere in `Fresh/`: `χ ^ (2q-ℓ) · T^ℓ(w,y)`. -/
theorem spineVal_eq_kernel (pi : Sym2 V → unitInterval) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, I417FreshTwo.kernel pi a b = chi)
    (ℓ q : ℕ) (Fs : Fin (ℓ + 1) → Hang) (y w : V)
    (hlen : (∑ i : Fin (ℓ + 1), (Fs i).size) = 2 * q - ℓ) :
    spineVal (I417FreshTwo.kernel pi) ℓ Fs y w =
      chi ^ (2 * q - ℓ) * iterPow (I417FreshTwo.kernel pi) ℓ w y := by
  rw [spineVal_eq_normal (I417FreshTwo.kernel pi) chi hchi ℓ q Fs y w hlen,
    I417Base.iterPow_comm (I417FreshTwo.kernel pi) (fun a b => tau_symm pi a b) ℓ y w]

/-- The constant row sum in the `tau` form in which production states it. -/
theorem kernel_rowSum_of_tau (pi : Sym2 V → unitInterval) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, I417Fresh.tau pi a b = chi) :
    ∀ a : V, ∑' b : V, I417FreshTwo.kernel pi a b = chi :=
  fun a => hchi a

/-! ## Worked instances: the accepted `q = 4` profile endpoints -/

/-- The deepest branch of the `q = 4` cover (`ℓ = 4`, four single arms hanging from `z1, z2, z3, w`
and none from `y`): value `χ^4 · T^4(w,y)`.  This is `I417FreshFour.Eval.ev_0`'s value, obtained
here with no peel-order computation. -/
theorem spineVal_four_profile_first (pi : Sym2 V → unitInterval) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, I417FreshTwo.kernel pi a b = chi) (y w : V) :
    spineVal (I417FreshTwo.kernel pi) 4
        (fun i : Fin 5 => if i = 0 then Hang.nil else Hang.star 1) y w =
      chi ^ 4 * iterPow (I417FreshTwo.kernel pi) 4 w y := by
  have hlen : (∑ i : Fin 5, ((if i = 0 then Hang.nil else Hang.star 1) : Hang).size) = 4 := by
    decide
  exact spineVal_eq_kernel pi chi hchi 4 4 _ y w hlen

/-- The shallowest branch of the `q = 4` cover (`ℓ = 1`, seven arms hanging off the spine, `w`
included): value `χ^7 · T(w,y)`.  This is the value of each of the fifteen `ℓ = 1` members. -/
theorem spineVal_four_profile_last (pi : Sym2 V → unitInterval) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, I417FreshTwo.kernel pi a b = chi) (y w : V) :
    spineVal (I417FreshTwo.kernel pi) 1
        (fun i : Fin 2 => if i = 0 then Hang.nil else Hang.star 7) y w =
      chi ^ 7 * iterPow (I417FreshTwo.kernel pi) 1 w y := by
  have hlen : (∑ i : Fin 2, ((if i = 0 then Hang.nil else Hang.star 7) : Hang).size) = 7 := by
    decide
  exact spineVal_eq_kernel pi chi hchi 1 4 _ y w hlen

/-- A one-leg diagram with `m` arms hanging from `w`: `χ^m · T(w,y)`; the `m = 4` case is the hub
star of `I417FreshTwo.freshTwoPoly`. -/
theorem spineVal_hub (pi : Sym2 V → unitInterval) (chi : ℝ≥0∞)
    (hchi : ∀ a : V, ∑' b : V, I417FreshTwo.kernel pi a b = chi) (m : ℕ) (y w : V) :
    spineVal (I417FreshTwo.kernel pi) 1
        (fun i : Fin 2 => if i = 0 then Hang.nil else Hang.star m) y w =
      chi ^ m * iterPow (I417FreshTwo.kernel pi) 1 w y := by
  have hsum : (∑ i : Fin 2, ((if i = 0 then Hang.nil else Hang.star m) : Hang).size) = m := by
    rw [Fin.sum_univ_two]
    simp
  rw [spineVal_eq (I417FreshTwo.kernel pi) chi hchi 1 _ y w, hsum,
    I417Base.iterPow_comm (I417FreshTwo.kernel pi) (fun a b => tau_symm pi a b) 1 y w]

end PercLib.CriticalLRP.I417FreshGenSpine
