/-
Independently rebuilt and reviewed from `smwx8o5tv/m3`.
Production integration revision `f5eac7918f853f5a5be71b3e7d205bf9981a0539`.
Only the compiled diagram/summation part is integrated here; no event-cover premise,
numerical counterexample or moment-completion assertion is inherited.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Eval

/-!
# Candidate two-centre slot evaluations for the `p = 5`, `k = 2` case

Ultramath swarm `smwx8o5tv`, member `m3`, direction MIXED-K-ALTERNATE-REALIZATION.
Source anchor: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.16 (`paper.txt` lines 2370--2440).

The production `HubK2` slot for `p = 5, k = 2` links *both* hubs to the root and keeps the
residual arm at the first hub.  A proposed regrouping of the six-terminal comb
(`SixPoint.combSystem_nine`) motivates a different two-hub shape instead: two joint pairs and
one two-point arm measured from a first centre, a spine link to a second centre, and the last
two-point arm there.  This file defines candidate shapes (`hubChainA`, `hubChainB`) and
evaluates them,
slot by slot, to at most `(E|K_0|^2)^2 (E|K_0|)^3`, the `p = 5`, `k = 2` exponent of the
lemma.  The event-level realization of the shape is *not* claimed here; see the accompanying
`RESULTS.md` for the exact remaining gap.
-/
open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ## Two elementary slack lemmas -/

/-- A joint two-point event is at most its left marginal. -/
theorem jointP_le_tau_left [Countable V] (π : Sym2 V → unitInterval) (a b c : V) :
    jointP π a b c ≤ tau π a c := by
  rw [jointP, tau]
  exact measure_mono (inter_subset_left)

/-- A joint two-point event is at most its right marginal. -/
theorem jointP_le_tau_right [Countable V] (π : Sym2 V → unitInterval) (a b c : V) :
    jointP π a b c ≤ tau π b c := by
  rw [jointP, tau]
  exact measure_mono (inter_subset_right)

/-- The susceptibility is at most the second cluster moment. -/
theorem firstMoment_le_secondMoment [Countable V] (π : Sym2 V → unitInterval) (o : V) :
    firstMoment π o ≤ secondMoment π o := by
  rw [firstMoment_eq, secondMoment_eq]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have h : tau π o x = jointP π x x o := by
    rw [jointP, tau, conn_symm o x, Set.inter_self]
  rw [h]
  exact ENNReal.le_tsum (f := fun y => jointP π x y o) x


/-! ## Reordering tools for five leaves and two centres -/

/-- Move the last index of a six-fold sum to the front. -/
theorem tsum_move_last_six' (F : V → V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' x, F a b c d e x)
      = ∑' x, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e x := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' x, F a b c d e x)
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' e, F a b c d e x :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' x, ∑' d, ∑' e, F a b c d e x :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' x, ∑' c, ∑' d, ∑' e, F a b c d e x :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' x, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e x :=
        tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' x, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e x := ENNReal.tsum_comm

/-! ## The corrected two-hub diagram -/

/-- **One-hub-per-centre diagram.**  Two joint pairs and one two-point arm measured from the
first centre `c₁`, a spine link `c₁ — c₂` and one two-point arm at `c₂`. -/
noncomputable def hubChainA (π : Sym2 V → unitInterval) (o a b d e g : V) : ℝ≥0∞ :=
  ∑' c1, ∑' c2,
    jointP π a b c1 * (jointP π d e c1 * (tau π o c1 * (tau π c1 c2 * tau π g c2)))

/-- **Two-joint, three-single diagram at a single centre with a link.**  Both joint pairs and one
two-point arm sit at `c`; the remaining two arms sit at the summed vertex `x` linked to `c`. -/
noncomputable def hubChainB (π : Sym2 V → unitInterval) (o a b d e g : V) : ℝ≥0∞ :=
  ∑' c, ∑' x,
    jointP π a b c * (jointP π d e c * (tau π o c * (tau π g x * tau π x c)))

/-! ## Evaluation of `hubChainA` -/

/-- Leaf summation at fixed centres: the four joint leaves produce the squared second moment at
`c₁` and the last leaf produces the susceptibility. -/
theorem hubChainA_leaf [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o c1 c2 : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' g,
        jointP π a b c1 * (jointP π d e c1 * (tau π o c1 * (tau π c1 c2 * tau π g c2))))
      = secondMoment π c1 *
          (secondMoment π c1 * (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))) := by
  have hg : ∀ a b d e : V,
      (∑' g,
        jointP π a b c1 * (jointP π d e c1 * (tau π o c1 * (tau π c1 c2 * tau π g c2))))
        = jointP π a b c1 *
            (jointP π d e c1 * (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))) := by
    intro a b d e
    rw [show (∑' g,
        jointP π a b c1 * (jointP π d e c1 * (tau π o c1 * (tau π c1 c2 * tau π g c2))))
        = ∑' g, (jointP π a b c1 * (jointP π d e c1 * (tau π o c1 * tau π c1 c2))) * tau π g c2
        from tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c2]
    ring
  rw [tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
    hg a b d e]
  have he : ∀ a b d : V,
      (∑' e, jointP π a b c1 *
        (jointP π d e c1 * (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))))
        = jointP π a b c1 *
            ((∑' e, jointP π d e c1) *
              (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))) := by
    intro a b d
    rw [show (∑' e, jointP π a b c1 *
        (jointP π d e c1 * (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))))
        = ∑' e, (jointP π a b c1 * (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))) *
          jointP π d e c1 from tsum_congr fun e => by ring]
    rw [ENNReal.tsum_mul_left]
    ring
  rw [tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => he a b d]
  have hd : ∀ a b : V,
      (∑' d, jointP π a b c1 *
        ((∑' e, jointP π d e c1) *
          (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))))
        = jointP π a b c1 *
            (secondMoment π c1 * (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))) := by
    intro a b
    rw [show (∑' d, jointP π a b c1 *
        ((∑' e, jointP π d e c1) *
          (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))))
        = ∑' d, (jointP π a b c1 * (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))) *
          (∑' e, jointP π d e c1) from tsum_congr fun d => by ring]
    rw [ENNReal.tsum_mul_left]
    rw [show (∑' d, ∑' e, jointP π d e c1) = secondMoment π c1 from
      (secondMoment_eq π c1).symm]
    ring
  rw [tsum_congr fun a => tsum_congr fun b => hd a b]
  rw [show (∑' a, ∑' b, jointP π a b c1 *
      (secondMoment π c1 * (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))))
      = ∑' a, ∑' b, (secondMoment π c1 * (tau π o c1 * (tau π c1 c2 *
          (∑' x, tau π 0 x)))) * jointP π a b c1 from
    tsum_congr fun a => tsum_congr fun b => by ring]
  rw [tsum_two_const_mul (a := secondMoment π c1 * (tau π o c1 * (tau π c1 c2 *
      (∑' x, tau π 0 x)))) (R := fun a b => jointP π a b c1)]
  rw [secondMoment_eq π c1]
  ring


/-- **Evaluation of the corrected two-hub diagram with the root at its first two-point arm.**
The five leaf sums produce `(E|K_0|^2)^2` and three susceptibility factors. -/
theorem hubChainA_tsum_root_single [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' g, hubChainA π o a b d e g)
      = secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
  simp only [hubChainA]
  rw [tsum_seven_swap (F := fun a b d e g c1 c2 =>
    jointP π a b c1 * (jointP π d e c1 * (tau π o c1 * (tau π c1 c2 * tau π g c2))))]
  rw [tsum_congr fun c1 => tsum_congr fun c2 => hubChainA_leaf π hq o c1 c2]
  have step2 : ∀ c1 : V,
      (∑' c2, secondMoment π c1 * (secondMoment π c1 *
        (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))))
        = secondMoment π c1 * (secondMoment π c1 *
            (tau π o c1 * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro c1
    rw [show (∑' c2, secondMoment π c1 * (secondMoment π c1 *
        (tau π o c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))))
        = ∑' c2, (secondMoment π c1 * (secondMoment π c1 *
          (tau π o c1 * (∑' x, tau π 0 x)))) * tau π c1 c2 from
      tsum_congr fun c2 => by ring]
    rw [ENNReal.tsum_mul_left, tau_row π hq c1]
    ring
  rw [tsum_congr fun c1 => step2 c1]
  rw [show (∑' c1, secondMoment π c1 * (secondMoment π c1 *
      (tau π o c1 * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))))
      = ∑' c1, (secondMoment π 0 * (secondMoment π 0 *
        ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) * tau π o c1 from
    tsum_congr fun c1 => by rw [secondMoment_root_independent π hq c1]; ring]
  rw [ENNReal.tsum_mul_left, tau_row π hq o]
  ring


/-- **Root in the second centre's two-point arm.**  Both joint pairs and the first arm sum out
completely; only the spine link and the root arm remain. -/
theorem hubChainA_tsum_root_single2 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' r, hubChainA π r a b d e 0)
      = secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
  simp only [hubChainA]
  rw [tsum_seven_swap (F := fun a b d e r c1 c2 =>
    jointP π a b c1 * (jointP π d e c1 * (tau π r c1 * (tau π c1 c2 * tau π 0 c2))))]
  have hstep : ∀ c1 c2 : V,
      (∑' a, ∑' b, ∑' d, ∑' e, ∑' r,
        jointP π a b c1 * (jointP π d e c1 * (tau π r c1 * (tau π c1 c2 * tau π 0 c2))))
        = secondMoment π c1 * (secondMoment π c1 *
            ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))) := by
    intro c1 c2
    have hr : (∑' r, tau π r c1) = ∑' x, tau π 0 x := tau_col π hq c1
    have h1 : ∀ a b d e : V,
        (∑' r, jointP π a b c1 * (jointP π d e c1 *
          (tau π r c1 * (tau π c1 c2 * tau π 0 c2))))
          = jointP π a b c1 * (jointP π d e c1 *
              ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))) := by
      intro a b d e
      rw [show (∑' r, jointP π a b c1 * (jointP π d e c1 *
          (tau π r c1 * (tau π c1 c2 * tau π 0 c2))))
          = ∑' r, (jointP π a b c1 * (jointP π d e c1 *
            (tau π c1 c2 * tau π 0 c2))) * tau π r c1 from
        tsum_congr fun r => by ring]
      rw [ENNReal.tsum_mul_left, hr]
      ring
    rw [tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
      h1 a b d e]
    have he : ∀ a b d : V,
        (∑' e, jointP π a b c1 * (jointP π d e c1 *
          ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))))
          = jointP π a b c1 * ((∑' e, jointP π d e c1) *
              ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))) := by
      intro a b d
      rw [show (∑' e, jointP π a b c1 * (jointP π d e c1 *
          ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))))
          = ∑' e, (jointP π a b c1 *
            ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))) * jointP π d e c1 from
        tsum_congr fun e => by ring]
      rw [ENNReal.tsum_mul_left]
      ring
    rw [tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => he a b d]
    have hd : ∀ a b : V,
        (∑' d, jointP π a b c1 * ((∑' e, jointP π d e c1) *
          ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))))
          = jointP π a b c1 * (secondMoment π c1 *
              ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))) := by
      intro a b
      rw [show (∑' d, jointP π a b c1 * ((∑' e, jointP π d e c1) *
          ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))))
          = ∑' d, (jointP π a b c1 *
            ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))) *
            (∑' e, jointP π d e c1) from tsum_congr fun d => by ring]
      rw [ENNReal.tsum_mul_left]
      rw [show (∑' d, ∑' e, jointP π d e c1) = secondMoment π c1 from
        (secondMoment_eq π c1).symm]
      ring
    rw [tsum_congr fun a => tsum_congr fun b => hd a b]
    rw [show (∑' a, ∑' b, jointP π a b c1 * (secondMoment π c1 *
        ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))))
        = ∑' a, ∑' b, (secondMoment π c1 * ((∑' x, tau π 0 x) *
          (tau π c1 c2 * tau π 0 c2))) * jointP π a b c1 from
      tsum_congr fun a => tsum_congr fun b => by ring]
    rw [tsum_two_const_mul (a := secondMoment π c1 * ((∑' x, tau π 0 x) *
      (tau π c1 c2 * tau π 0 c2))) (R := fun a b => jointP π a b c1)]
    rw [secondMoment_eq π c1]
    ring
  rw [tsum_congr fun c1 => tsum_congr fun c2 => hstep c1 c2]
  rw [ENNReal.tsum_comm]
  have hc1 : ∀ c2 : V,
      (∑' c1, secondMoment π c1 * (secondMoment π c1 *
        ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))))
        = (secondMoment π 0 * (secondMoment π 0 * (∑' x, tau π 0 x))) *
            (tau π 0 c2 * (∑' x, tau π 0 x)) := by
    intro c2
    rw [show (∑' c1, secondMoment π c1 * (secondMoment π c1 *
        ((∑' x, tau π 0 x) * (tau π c1 c2 * tau π 0 c2))))
        = ∑' c1, (secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * tau π 0 c2))) * tau π c1 c2 from
      tsum_congr fun c1 => by rw [secondMoment_root_independent π hq c1]; ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c2]
    ring
  rw [tsum_congr fun c2 => hc1 c2]
  have hc2 : (∑' c2, (secondMoment π 0 * (secondMoment π 0 * (∑' x, tau π 0 x))) *
      (tau π 0 c2 * (∑' x, tau π 0 x)))
      = ((secondMoment π 0 * (secondMoment π 0 * (∑' x, tau π 0 x))) *
          (∑' x, tau π 0 x)) * (∑' c2, tau π 0 c2) := by
    rw [show (∑' c2, (secondMoment π 0 * (secondMoment π 0 * (∑' x, tau π 0 x))) *
        (tau π 0 c2 * (∑' x, tau π 0 x)))
        = ∑' c2, ((secondMoment π 0 * (secondMoment π 0 * (∑' x, tau π 0 x))) *
            (∑' x, tau π 0 x)) * tau π 0 c2 from
      tsum_congr fun c2 => by ring]
    rw [ENNReal.tsum_mul_left]
  rw [hc2, tau_row π hq (0 : V)]
  ring

/-- **Root in a joint arm.**  The root keeps one joint pair alive; the pair is summed with
`tsum_jointP_centre`, which recovers the second moment, so the total stays `χ^2 T^3`. -/
theorem hubChainA_tsum_root_joint [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' b, ∑' d, ∑' e, ∑' r, ∑' g, hubChainA π r 0 b d e g)
      = secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
  simp only [hubChainA]
  rw [tsum_seven_swap (F := fun b d e r g c1 c2 =>
    jointP π 0 b c1 * (jointP π d e c1 * (tau π r c1 * (tau π c1 c2 * tau π g c2))))]
  have hstep : ∀ c1 c2 : V,
      (∑' b, ∑' d, ∑' e, ∑' r, ∑' g,
        jointP π 0 b c1 * (jointP π d e c1 * (tau π r c1 * (tau π c1 c2 * tau π g c2))))
        = (∑' b, jointP π 0 b c1) * (secondMoment π c1 *
            ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))) := by
    intro c1 c2
    have h1 : ∀ b d e r : V,
        (∑' g, jointP π 0 b c1 * (jointP π d e c1 *
          (tau π r c1 * (tau π c1 c2 * tau π g c2))))
          = jointP π 0 b c1 * (jointP π d e c1 *
              (tau π r c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))) := by
      intro b d e r
      rw [show (∑' g, jointP π 0 b c1 * (jointP π d e c1 *
          (tau π r c1 * (tau π c1 c2 * tau π g c2))))
          = ∑' g, (jointP π 0 b c1 * (jointP π d e c1 *
            (tau π r c1 * tau π c1 c2))) * tau π g c2 from
        tsum_congr fun g => by ring]
      rw [ENNReal.tsum_mul_left, tau_col π hq c2]
      ring
    rw [tsum_congr fun b => tsum_congr fun d => tsum_congr fun e => tsum_congr fun r =>
      h1 b d e r]
    have h2 : ∀ b d e : V,
        (∑' r, jointP π 0 b c1 * (jointP π d e c1 *
          (tau π r c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))))
          = jointP π 0 b c1 * (jointP π d e c1 *
              ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))) := by
      intro b d e
      rw [show (∑' r, jointP π 0 b c1 * (jointP π d e c1 *
          (tau π r c1 * (tau π c1 c2 * (∑' x, tau π 0 x)))))
          = ∑' r, (jointP π 0 b c1 * (jointP π d e c1 *
            (tau π c1 c2 * (∑' x, tau π 0 x)))) * tau π r c1 from
        tsum_congr fun r => by ring]
      rw [ENNReal.tsum_mul_left, tau_col π hq c1]
      ring
    rw [tsum_congr fun b => tsum_congr fun d => tsum_congr fun e => h2 b d e]
    have h3 : ∀ b d : V,
        (∑' e, jointP π 0 b c1 * (jointP π d e c1 *
          ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))))
          = jointP π 0 b c1 * ((∑' e, jointP π d e c1) *
              ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))) := by
      intro b d
      rw [show (∑' e, jointP π 0 b c1 * (jointP π d e c1 *
          ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))))
          = ∑' e, (jointP π 0 b c1 *
            ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))) *
            jointP π d e c1 from tsum_congr fun e => by ring]
      rw [ENNReal.tsum_mul_left]
      ring
    rw [tsum_congr fun b => tsum_congr fun d => h3 b d]
    have h4 : ∀ b : V,
        (∑' d, jointP π 0 b c1 * ((∑' e, jointP π d e c1) *
          ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))))
          = jointP π 0 b c1 * (secondMoment π c1 *
              ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))) := by
      intro b
      rw [show (∑' d, jointP π 0 b c1 * ((∑' e, jointP π d e c1) *
          ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))))
          = ∑' d, (jointP π 0 b c1 *
            ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))) *
            (∑' e, jointP π d e c1) from tsum_congr fun d => by ring]
      rw [ENNReal.tsum_mul_left]
      rw [show (∑' d, ∑' e, jointP π d e c1) = secondMoment π c1 from
        (secondMoment_eq π c1).symm]
      ring
    rw [tsum_congr fun b => h4 b]
    rw [show (∑' b, jointP π 0 b c1 * (secondMoment π c1 *
        ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))))
        = ∑' b, (secondMoment π c1 * ((∑' x, tau π 0 x) *
          (tau π c1 c2 * (∑' x, tau π 0 x)))) * jointP π 0 b c1 from
      tsum_congr fun b => by ring]
    rw [ENNReal.tsum_mul_left]
    ring
  rw [tsum_congr fun c1 => tsum_congr fun c2 => hstep c1 c2]
  have hc2 : ∀ c1 : V,
      (∑' c2, (∑' b, jointP π 0 b c1) * (secondMoment π c1 *
        ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))))
        = (∑' b, jointP π 0 b c1) * (secondMoment π c1 *
            ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
    intro c1
    rw [show (∑' c2, (∑' b, jointP π 0 b c1) * (secondMoment π c1 *
        ((∑' x, tau π 0 x) * (tau π c1 c2 * (∑' x, tau π 0 x)))))
        = ∑' c2, ((∑' b, jointP π 0 b c1) * (secondMoment π c1 *
          ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) * tau π c1 c2 from
      tsum_congr fun c2 => by ring]
    rw [ENNReal.tsum_mul_left, tau_row π hq c1]
    ring
  rw [tsum_congr fun c1 => hc2 c1]
  have hc1 : (∑' c1, (∑' b, jointP π 0 b c1) * (secondMoment π c1 *
      ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))))
      = (secondMoment π 0 * ((∑' x, tau π 0 x) *
          ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) * (secondMoment π 0) := by
    rw [show (∑' c1, (∑' b, jointP π 0 b c1) * (secondMoment π c1 *
        ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))))
        = ∑' c1, (secondMoment π 0 * ((∑' x, tau π 0 x) *
          ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) * (∑' b, jointP π 0 b c1) from
      tsum_congr fun c1 => by rw [secondMoment_root_independent π hq c1]; ring]
    rw [ENNReal.tsum_mul_left]
    rw [show (∑' c1, ∑' b, jointP π 0 b c1) = secondMoment π 0 from
      tsum_jointP_centre π hq 0]
  rw [hc1]
  ring

/-- The two ears of the first joint pair are interchangeable. -/
theorem hubChainA_swap_joint1 [Countable V] (π : Sym2 V → unitInterval) (o a b d e g : V) :
    hubChainA π o a b d e g = hubChainA π o b a d e g := by
  simp only [hubChainA, jointP_comm π a b]

/-- **Root in the second arm of the first joint pair.**  Follows from the first-ear case by the
ear swap and a reindexing of the two summed ears. -/
theorem hubChainA_tsum_root_joint' [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' a, ∑' d, ∑' e, ∑' r, ∑' g, hubChainA π r a 0 d e g)
      = secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
  rw [show (∑' a, ∑' d, ∑' e, ∑' r, ∑' g, hubChainA π r a 0 d e g)
      = ∑' a, ∑' d, ∑' e, ∑' r, ∑' g, hubChainA π r 0 a d e g from
    tsum_congr fun a => tsum_congr fun d => tsum_congr fun e => tsum_congr fun r =>
      tsum_congr fun g => hubChainA_swap_joint1 π r a 0 d e g]
  exact hubChainA_tsum_root_joint π hq

/-! ## A shape intended for a six-terminal comb regrouping -/

/-- **Candidate two-centre slot.**  Joint pair `(a,b)` and two-point arm `f` at `c₁`, spine
link `c₁ — c₂`, joint pair `(d,e)` and two-point arm `g` at `c₂`.  This is the regrouping of
`SixPoint.CombSystem` for the arm positions whose two joint groups carry the two comb spines:
both joint pairs are measured at their own centre and only the spine link ties the centres, so
unlike `hubChainA` it matches the geometry that `combSystem_nine` supplies. -/
noncomputable def hubTwoCentre (π : Sym2 V → unitInterval) (f a b d e g : V) : ℝ≥0∞ :=
  ∑' c1, ∑' c2,
    jointP π a b c1 * (tau π f c1 * (tau π c1 c2 * (jointP π d e c2 * tau π g c2)))

/-- Leaf summation for `hubTwoCentre` at fixed centres. -/
theorem hubTwoCentre_leaf [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (f c1 c2 : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' g,
        jointP π a b c1 * (tau π f c1 * (tau π c1 c2 * (jointP π d e c2 * tau π g c2))))
      = secondMoment π c1 * (tau π f c1 * (tau π c1 c2 *
          (secondMoment π c2 * (∑' x, tau π 0 x)))) := by
  have hg : ∀ a b d e : V,
      (∑' g, jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
        (jointP π d e c2 * tau π g c2))))
        = jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
            (jointP π d e c2 * (∑' x, tau π 0 x)))) := by
    intro a b d e
    rw [show (∑' g, jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
        (jointP π d e c2 * tau π g c2))))
        = ∑' g, (jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
          jointP π d e c2))) * tau π g c2 from tsum_congr fun g => by ring]
    rw [ENNReal.tsum_mul_left, tau_col π hq c2]
    ring
  rw [tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
    hg a b d e]
  have he : ∀ a b d : V,
      (∑' e, jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
        (jointP π d e c2 * (∑' x, tau π 0 x)))))
        = jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
            ((∑' e, jointP π d e c2) * (∑' x, tau π 0 x)))) := by
    intro a b d
    rw [show (∑' e, jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
        (jointP π d e c2 * (∑' x, tau π 0 x)))))
        = ∑' e, (jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
          (∑' x, tau π 0 x)))) * jointP π d e c2 from tsum_congr fun e => by ring]
    rw [ENNReal.tsum_mul_left]
    ring
  rw [tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => he a b d]
  have hd : ∀ a b : V,
      (∑' d, jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
        ((∑' e, jointP π d e c2) * (∑' x, tau π 0 x)))))
        = jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
            (secondMoment π c2 * (∑' x, tau π 0 x)))) := by
    intro a b
    rw [show (∑' d, jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
        ((∑' e, jointP π d e c2) * (∑' x, tau π 0 x)))))
        = ∑' d, (jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
          (∑' x, tau π 0 x)))) * (∑' e, jointP π d e c2) from
      tsum_congr fun d => by ring]
    rw [ENNReal.tsum_mul_left]
    rw [show (∑' d, ∑' e, jointP π d e c2) = secondMoment π c2 from
      (secondMoment_eq π c2).symm]
    ring
  rw [tsum_congr fun a => tsum_congr fun b => hd a b]
  rw [show (∑' a, ∑' b, jointP π a b c1 * (tau π f c1 * (tau π c1 c2 *
      (secondMoment π c2 * (∑' x, tau π 0 x)))))
      = ∑' a, ∑' b, (tau π f c1 * (tau π c1 c2 *
        (secondMoment π c2 * (∑' x, tau π 0 x)))) * jointP π a b c1 from
    tsum_congr fun a => tsum_congr fun b => by ring]
  rw [tsum_two_const_mul (a := tau π f c1 * (tau π c1 c2 *
    (secondMoment π c2 * (∑' x, tau π 0 x)))) (R := fun a b => jointP π a b c1)]
  rw [secondMoment_eq π c1]
  ring

/-- **Evaluation of the comb-faithful two-centre shape with the root at the first centre's
two-point arm.**  The four joint leaves produce `(E|K_0|^2)^2`, and the spine link together
with the root arm and the last leaf produce the cube of the susceptibility. -/
theorem hubTwoCentre_tsum_root_single [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' g, hubTwoCentre π 0 a b d e g)
      = secondMoment π 0 * (secondMoment π 0 *
          ((∑' x, tau π 0 x) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)))) := by
  simp only [hubTwoCentre]
  rw [tsum_seven_swap (F := fun a b d e g c1 c2 =>
    jointP π a b c1 * (tau π 0 c1 * (tau π c1 c2 * (jointP π d e c2 * tau π g c2))))]
  rw [tsum_congr fun c1 => tsum_congr fun c2 => hubTwoCentre_leaf π hq 0 c1 c2]
  have hc2 : ∀ c1 : V,
      (∑' c2, secondMoment π c1 * (tau π 0 c1 * (tau π c1 c2 *
        (secondMoment π c2 * (∑' x, tau π 0 x)))))
        = secondMoment π c1 * (tau π 0 c1 * ((∑' x, tau π 0 x) *
            (secondMoment π 0 * (∑' x, tau π 0 x)))) := by
    intro c1
    rw [show (∑' c2, secondMoment π c1 * (tau π 0 c1 * (tau π c1 c2 *
        (secondMoment π c2 * (∑' x, tau π 0 x)))))
        = ∑' c2, (secondMoment π c1 * (tau π 0 c1 *
          (secondMoment π 0 * (∑' x, tau π 0 x)))) * tau π c1 c2 from
      tsum_congr fun c2 => by rw [secondMoment_root_independent π hq c2]; ring]
    rw [ENNReal.tsum_mul_left, tau_row π hq c1]
    ring
  rw [tsum_congr fun c1 => hc2 c1]
  have hc1 : (∑' c1, secondMoment π c1 * (tau π 0 c1 * ((∑' x, tau π 0 x) *
      (secondMoment π 0 * (∑' x, tau π 0 x)))))
      = (secondMoment π 0 * ((∑' x, tau π 0 x) *
          (secondMoment π 0 * (∑' x, tau π 0 x)))) * (∑' c1, tau π 0 c1) := by
    rw [show (∑' c1, secondMoment π c1 * (tau π 0 c1 * ((∑' x, tau π 0 x) *
        (secondMoment π 0 * (∑' x, tau π 0 x)))))
        = ∑' c1, (secondMoment π 0 * ((∑' x, tau π 0 x) *
          (secondMoment π 0 * (∑' x, tau π 0 x)))) * tau π 0 c1 from
      tsum_congr fun c1 => by rw [secondMoment_root_independent π hq c1]; ring]
    rw [ENNReal.tsum_mul_left]
  rw [hc1, tau_row π hq (0 : V)]
  ring

end PercLib.CriticalLRP.TreeExpansion.HubK2
