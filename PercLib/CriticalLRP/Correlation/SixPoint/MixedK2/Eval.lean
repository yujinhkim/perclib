/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m4/Eval.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Defs

/-!
Evaluation of the two-hub `p = 5`, `k = 2` slot diagrams.

The analytic content of the `k = 2` regrouping: every joint pair sums to the native second
moment `E|K|^2` at its hub, every two-point link to the root sums to the susceptibility
`E|K| = ∑' x, tau 0 x`, and the two hub sums converge because each hub carries one link to
the root.  The result

  `∑' (five free leaves) (two hubs), hubStar = (E|K|^2)^2 * (E|K|)^3`

is exactly the exponent pattern `(2p-3)!! (E|K|^2)^k (E|K|)^{2p-1-3k}` of Hutchcroft's
Lemma I.4.16 at `p = 5`, `k = 2` (with `2p-1-3k = 3` and `k = 2`).

Nothing here uses a moment-finiteness or subcriticality hypothesis: everything is an identity
of extended nonnegative quantities.  The only external input is full translation invariance of
the opening profile, used once for root independence of the second moment and once for
`∑' a, tau a c = ∑' a, tau 0 a`.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ## Splitting a fivefold sum into two double sums and a single sum -/

/-- A fivefold sum of a product of three independent factors splits into the product of the
three sums. -/
theorem tsum_five_split [Countable V] [AddCommGroup V]
    (A : V → V → ℝ≥0∞) (B : V → V → ℝ≥0∞) (C : V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, A a b * B d e * C f)
      = (∑' a, ∑' b, A a b) * ((∑' d, ∑' e, B d e) * (∑' f, C f)) := by
  have hf : ∀ a b d e : V,
      (∑' f, A a b * B d e * C f) = A a b * B d e * (∑' f, C f) :=
    fun a b d e => ENNReal.tsum_mul_left
  have h4 : ∀ a b : V, (∑' d, ∑' e, ∑' f, A a b * B d e * C f)
      = A a b * ((∑' d, ∑' e, B d e) * (∑' f, C f)) := by
    intro a b
    rw [show (∑' d, ∑' e, ∑' f, A a b * B d e * C f)
        = ∑' d, ∑' e, A a b * (B d e * (∑' f, C f)) from
          tsum_congr fun d => tsum_congr fun e => by
            rw [hf a b d e]; ring]
    rw [tsum_two_const_mul, tsum_two_mul_const]
  calc (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, A a b * B d e * C f)
      = ∑' a, ∑' b, A a b * ((∑' d, ∑' e, B d e) * (∑' f, C f)) :=
        tsum_congr fun a => tsum_congr fun b => h4 a b
    _ = (∑' a, ∑' b, A a b) * ((∑' d, ∑' e, B d e) * (∑' f, C f)) := by
        rw [show (∑' a, ∑' b, A a b * ((∑' d, ∑' e, B d e) * (∑' f, C f)))
            = ∑' a, (∑' b, A a b) * ((∑' d, ∑' e, B d e) * (∑' f, C f)) from
              tsum_congr fun a => ENNReal.tsum_mul_right]
        exact ENNReal.tsum_mul_right

/-! ## The leaf sum at fixed hubs -/

/-- **Leaf factorization.**  With the two hubs held fixed, the five free leaves separate into
two joint double sums and the residual two-point sum. -/
theorem hubStar_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval) (o c1 c2 : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, hubStar π o a b d e f c1 c2)
      = (secondMoment π c1 * tau π o c1) *
          ((secondMoment π c2 * tau π o c2) * (∑' x, tau π x c1)) := by
  have hsplit := tsum_five_split (A := fun a b => jointP π a b c1 * tau π o c1)
    (B := fun d e => jointP π d e c2 * tau π o c2) (C := fun f => tau π f c1)
  have hA : (∑' a, ∑' b, jointP π a b c1 * tau π o c1)
      = secondMoment π c1 * tau π o c1 := by
    rw [tsum_two_mul_const, ← secondMoment_eq]
  have hB : (∑' d, ∑' e, jointP π d e c2 * tau π o c2)
      = secondMoment π c2 * tau π o c2 := by
    rw [tsum_two_mul_const, ← secondMoment_eq]
  have hshape : (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, hubStar π o a b d e f c1 c2)
      = ∑' a, ∑' b, ∑' d, ∑' e, ∑' f,
          (jointP π a b c1 * tau π o c1) * (jointP π d e c2 * tau π o c2) * tau π f c1 :=
    tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
      tsum_congr fun f => by simp only [hubStar]
  rw [hshape, hsplit, hA, hB]

/-! ## Bringing the two hub sums to the front -/

/-- Move the last index of a sevenfold sum to the front. -/
theorem tsum_move_last_seven (F : V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, ∑' c2, F a b d e f c1 c2)
      = ∑' c2, ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, F a b d e f c1 c2 := by
  calc (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, ∑' c2, F a b d e f c1 c2)
      = ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c2, ∑' c1, F a b d e f c1 c2 :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
          tsum_congr fun f => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' d, ∑' e, ∑' c2, ∑' f, ∑' c1, F a b d e f c1 c2 :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
          ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' d, ∑' c2, ∑' e, ∑' f, ∑' c1, F a b d e f c1 c2 :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c2, ∑' d, ∑' e, ∑' f, ∑' c1, F a b d e f c1 c2 :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' c2, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, F a b d e f c1 c2 :=
        tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' c2, ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, F a b d e f c1 c2 :=
        ENNReal.tsum_comm

/-- Move both hub sums of a sevenfold sum to the front. -/
theorem tsum_seven_swap [Countable V] [AddCommGroup V]
    (F : V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, ∑' c2, F a b d e f c1 c2)
      = ∑' c1, ∑' c2, ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, F a b d e f c1 c2 := by
  rw [tsum_move_last_seven]
  rw [show (∑' c2, ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, F a b d e f c1 c2)
      = ∑' c2, ∑' c1, ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, F a b d e f c1 c2 from
        tsum_congr fun c2 =>
          tsum_move_last_six (F := fun a b d e f c1 => F a b d e f c1 c2)]
  rw [ENNReal.tsum_comm]

/-! ## The two-hub evaluation -/

/-- **Two-hub evaluation.**  Summing the five free leaves and both hubs gives the square of the
native second moment times the cube of the susceptibility. -/
theorem tsum_hubStar [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, ∑' c2, hubStar π o a b d e f c1 c2)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  have hS : ∀ c : V, secondMoment π c = secondMoment π o := fun c =>
    (secondMoment_root_independent π hq c).trans (secondMoment_root_independent π hq o).symm
  have hT : ∀ c : V, (∑' x, tau π x c) = ∑' x, tau π o x := fun c => by
    rw [tau_col π hq c, ← tau_row π hq o]
  rw [tsum_seven_swap]
  calc (∑' c1, ∑' c2, ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, hubStar π o a b d e f c1 c2)
      = ∑' c1, ∑' c2,
          (secondMoment π c1 * tau π o c1) *
            ((secondMoment π c2 * tau π o c2) * (∑' x, tau π x c1)) :=
        tsum_congr fun c1 => tsum_congr fun c2 => hubStar_tsum π o c1 c2
    _ = ∑' c1, ∑' c2,
          (secondMoment π o * tau π o c1) *
            ((secondMoment π o * tau π o c2) * (∑' x, tau π o x)) :=
        tsum_congr fun c1 => tsum_congr fun c2 => by rw [hS c1, hS c2, hT c1]
    _ = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
        have hfac : ∀ c1 c2 : V,
            (secondMoment π o * tau π o c1) *
                ((secondMoment π o * tau π o c2) * (∑' x, tau π o x))
              = (secondMoment π o * (∑' x, tau π o x) * secondMoment π o) *
                  (tau π o c1 * tau π o c2) := by
          intro c1 c2
          ring
        rw [tsum_congr fun c1 => tsum_congr fun c2 => hfac c1 c2]
        have hstep : ∀ c1 : V,
            (∑' c2, (secondMoment π o * (∑' x, tau π o x) * secondMoment π o) *
                (tau π o c1 * tau π o c2))
              = ((secondMoment π o * (∑' x, tau π o x) * secondMoment π o) * tau π o c1) *
                  (∑' c2, tau π o c2) := by
          intro c1
          rw [show (∑' c2, (secondMoment π o * (∑' x, tau π o x) * secondMoment π o) *
                (tau π o c1 * tau π o c2))
              = ∑' c2, ((secondMoment π o * (∑' x, tau π o x) * secondMoment π o) *
                  tau π o c1) * tau π o c2 from
                tsum_congr fun c2 => by ring]
          exact ENNReal.tsum_mul_left
        rw [tsum_congr hstep]
        rw [show (∑' c1, ((secondMoment π o * (∑' x, tau π o x) * secondMoment π o) *
              tau π o c1) * (∑' c2, tau π o c2))
            = ∑' c1, (((secondMoment π o * (∑' x, tau π o x) * secondMoment π o) *
                (∑' c2, tau π o c2)) * tau π o c1) from
              tsum_congr fun c1 => by ring]
        rw [ENNReal.tsum_mul_left]
        rw [show (∑' c2, tau π o c2) = ∑' x, tau π o x from rfl,
          show (∑' c1, tau π o c1) = ∑' x, tau π o x from rfl]
        ring


/-! ## Permutation invariance of the leaf labelling -/


/-- Five nested sums over `V` as one sum over `Fin 5 → V`. -/
theorem tsum_fin5 (G : (Fin 5 → V) → ℝ≥0∞) :
    (∑' X : Fin 5 → V, G X) = ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, G ![x0, x1, x2, x3, x4] := by
  rw [← Equiv.tsum_eq fin5Prod.symm G]
  simp only [ENNReal.tsum_prod']
  rfl

/-- A fivefold sum is invariant under permuting the five index positions. -/
theorem tsum_fin5_perm (σ : Equiv.Perm (Fin 5)) (G : (Fin 5 → V) → ℝ≥0∞) :
    (∑' X : Fin 5 → V, G (fun i => X (σ i))) = ∑' X : Fin 5 → V, G X :=
  Equiv.tsum_eq (Equiv.arrowCongr σ.symm (Equiv.refl V)) G

/-- The nested form of `tsum_fin5_perm`. -/
theorem tsum_five_perm (σ : Equiv.Perm (Fin 5)) (H : V → V → V → V → V → ℝ≥0∞) :
    (∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4,
        H (![x0, x1, x2, x3, x4] (σ 0)) (![x0, x1, x2, x3, x4] (σ 1))
          (![x0, x1, x2, x3, x4] (σ 2)) (![x0, x1, x2, x3, x4] (σ 3))
          (![x0, x1, x2, x3, x4] (σ 4)))
      = ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, H x0 x1 x2 x3 x4 := by
  rw [← tsum_fin5 (G := fun X => H (X (σ 0)) (X (σ 1)) (X (σ 2)) (X (σ 3)) (X (σ 4)))]
  rw [tsum_fin5_perm σ (G := fun X => H (X 0) (X 1) (X 2) (X 3) (X 4))]
  rw [tsum_fin5 (G := fun X => H (X 0) (X 1) (X 2) (X 3) (X 4))]
  rfl

/-! ## The slot-diagram evaluation -/

/-- **Pattern independence.**  Every labelling of the five slots gives the same value, so the
event side is free to use any family of `105` labellings. -/
theorem tsum_slotK2 [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 5)) (o : V) :
    (∑' L : Fin 5 → V, slotK2 π σ o L)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  rw [tsum_fin5 (G := fun L => slotK2 π σ o L)]
  exact (tsum_five_perm σ
    (H := fun y z w q r => ∑' c1, ∑' c2, hubStar π o y z w q r c1 c2)).trans
    (tsum_hubStar π hq o)

/-- The five-nested-sum form used by the moment assembly. -/
theorem tsum_slotK2_five [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 5)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, slotK2 π σ o ![y, z, w, q, r])
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  rw [← tsum_fin5 (G := fun L => slotK2 π σ o L)]
  exact tsum_slotK2 π hq σ o

end PercLib.CriticalLRP.TreeExpansion.HubK2
