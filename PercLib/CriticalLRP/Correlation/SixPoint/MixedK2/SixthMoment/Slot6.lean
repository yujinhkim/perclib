/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m1.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m1/Slot6.lean`.
-/

/-
Ultramath `smwzqts7r`, member `m1`, direction `d2`.

# Evaluation of the `p = 6`, `k = 2` two-hub slot diagrams

The `p = 6` companion of production's `tsum_slotK2_five`
(`PercLib/CriticalLRP/Correlation/SixPoint/MixedK2/Eval.lean`).

The analytic content of the `k = 2` regrouping at `p = 6`: every joint pair sums to the native
second moment `E|K|^2` at its hub, every two-point link to the root sums to the susceptibility
`E|K| = ∑' x, tau 0 x`, and the two residual free leaves contribute one susceptibility each.
The result

  `∑' (six free leaves) (two hubs), hubStarSix = (E|K|^2)^2 * (E|K|)^4`

is the `k = 2` pattern `(E|K|^2)^k (E|K|)^{2k+2}` of Hutchcroft's Lemma I.4.16 at `p = 6`;
it is *stronger* than the source's `(E|K|^2)^2 (E|K|)^5 = (E|K|^2)^2 (E|K|)^{2p-1-3k}`
because `E|K| ≥ 1`.

Nothing here uses a moment-finiteness or subcriticality hypothesis: everything is an identity of
extended nonnegative quantities.  The only external input is full translation invariance of the
opening profile, used once for root independence of the second moment and once for the identity
of row and column sums of the two-point function.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Eval
public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Defs

/-! Exact moment evaluations for the candidate two-hub six-point diagrams. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ## `Fin 6 → V` as six nested indices -/

/-- `Fin 6 → V` as a iterated product. -/
def fin6Prod : (Fin 6 → V) ≃ V × V × V × V × V × V where
  toFun X := (X 0, X 1, X 2, X 3, X 4, X 5)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2]
  left_inv X := by funext i; fin_cases i <;> rfl
  right_inv p := by obtain ⟨a, b, c, d, e, f⟩ := p; rfl

/-- Six nested sums over `V` as one sum over `Fin 6 → V`. -/
theorem tsum_fin6 [Countable V] (G : (Fin 6 → V) → ℝ≥0∞) :
    (∑' X : Fin 6 → V, G X) =
      ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, G ![x0, x1, x2, x3, x4, x5] := by
  rw [← Equiv.tsum_eq fin6Prod.symm G]
  simp only [ENNReal.tsum_prod']
  rfl

/-- A sixfold sum is invariant under permuting the six index positions. -/
theorem tsum_fin6_perm (σ : Equiv.Perm (Fin 6)) (G : (Fin 6 → V) → ℝ≥0∞) :
    (∑' X : Fin 6 → V, G (fun i => X (σ i))) = ∑' X : Fin 6 → V, G X :=
  Equiv.tsum_eq (Equiv.arrowCongr σ.symm (Equiv.refl V)) G

/-! ## Splitting a sixfold sum into two double sums and two single sums -/

/-- A sixfold sum of a product of four independent factors splits into the product of the
four sums. -/
theorem tsum_six_split [Countable V] [AddCommGroup V]
    (A B : V → V → ℝ≥0∞) (C D : V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' g, A a b * B d e * C f * D g)
      = (∑' a, ∑' b, A a b) * ((∑' d, ∑' e, B d e) * ((∑' f, C f) * (∑' g, D g))) := by
  set Y : ℝ≥0∞ := (∑' f, C f) * (∑' g, D g) with hY
  have hinner : ∀ (X : ℝ≥0∞), (∑' f, ∑' g, X * (C f * D g)) = X * Y := by
    intro X
    rw [show (∑' f, ∑' g, X * (C f * D g)) = ∑' f, X * (∑' g, C f * D g) from
      tsum_congr fun f => ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_left, PercLib.CriticalLRP.TreeExpansion.tsum_two_mul]
  have hstep : ∀ a b : V, (∑' d, ∑' e, (A a b * B d e) * Y)
      = (A a b * Y) * (∑' d, ∑' e, B d e) := by
    intro a b
    rw [show (∑' d, ∑' e, (A a b * B d e) * Y) = ∑' d, ∑' e, B d e * (A a b * Y) from
      tsum_congr fun d => tsum_congr fun e => by ring]
    rw [tsum_two_mul_const (F := fun d e => B d e) (A a b * Y)]
    ring
  calc (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' g, A a b * B d e * C f * D g)
      = ∑' a, ∑' b, ∑' d, ∑' e, (A a b * B d e) * Y := by
        refine tsum_congr fun a => tsum_congr fun b => tsum_congr fun d =>
          tsum_congr fun e => ?_
        rw [show (∑' f, ∑' g, A a b * B d e * C f * D g)
            = ∑' f, ∑' g, (A a b * B d e) * (C f * D g) from
          tsum_congr fun f => tsum_congr fun g => by ring]
        exact hinner (A a b * B d e)
    _ = ∑' a, ∑' b, (A a b * Y) * (∑' d, ∑' e, B d e) :=
        tsum_congr fun a => tsum_congr fun b => hstep a b
    _ = (∑' a, ∑' b, A a b * Y) * (∑' d, ∑' e, B d e) :=
        tsum_two_mul_const (F := fun a b => A a b * Y) _
    _ = ((∑' a, ∑' b, A a b) * Y) * (∑' d, ∑' e, B d e) := by
        rw [tsum_two_mul_const (F := fun a b => A a b) Y]
    _ = (∑' a, ∑' b, A a b) * ((∑' d, ∑' e, B d e) * Y) := by ring

/-! ## The leaf sum at fixed hubs -/

/-- **Leaf factorization at fixed hubs.**  With the two hubs held fixed, the six free leaves
separate into two joint double sums and two residual two-point sums. -/
theorem hubStarSix_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (o c1 c2 : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' g, hubStarSix π o a b d e f g c1 c2)
      = (secondMoment π c1 * tau π o c1) *
          ((secondMoment π c2 * tau π o c2) * ((∑' x, tau π x c1) * (∑' x, tau π x c2))) := by
  have hsplit := tsum_six_split (A := fun a b => jointP π a b c1 * tau π o c1)
    (B := fun d e => jointP π d e c2 * tau π o c2) (C := fun f => tau π f c1)
    (D := fun g => tau π g c2)
  have hA : (∑' a, ∑' b, jointP π a b c1 * tau π o c1)
      = secondMoment π c1 * tau π o c1 := by
    rw [tsum_two_mul_const, ← secondMoment_eq]
  have hB : (∑' d, ∑' e, jointP π d e c2 * tau π o c2)
      = secondMoment π c2 * tau π o c2 := by
    rw [tsum_two_mul_const, ← secondMoment_eq]
  have hshape : (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' g, hubStarSix π o a b d e f g c1 c2)
      = ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' g,
          (jointP π a b c1 * tau π o c1) * (jointP π d e c2 * tau π o c2)
            * tau π f c1 * tau π g c2 :=
    tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
      tsum_congr fun f => tsum_congr fun g => by simp only [hubStarSix]; ring
  rw [hshape, hsplit, hA, hB]

/-- **Leaf factorization at fixed hubs, on `Fin 6 → V`.** -/
theorem hubStarSix_tsum_fin [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (o c1 c2 : V) :
    (∑' L : Fin 6 → V, hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2)
      = (secondMoment π c1 * tau π o c1) *
          ((secondMoment π c2 * tau π o c2) * ((∑' x, tau π x c1) * (∑' x, tau π x c2))) := by
  rw [tsum_fin6 (G := fun L => hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2)]
  exact hubStarSix_tsum π o c1 c2

/-! ## The hub sums -/

/-- **Two-hub evaluation at `p = 6`.**  Summing the six free leaves and both hubs gives the
square of the native second moment times the fourth power of the susceptibility. -/
theorem tsum_hubStarSix [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    (∑' c1, ∑' c2, ∑' L : Fin 6 → V,
        hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 4 := by
  have hS : ∀ c : V, secondMoment π c = secondMoment π o := fun c =>
    (secondMoment_root_independent π hq c).trans (secondMoment_root_independent π hq o).symm
  have hT : ∀ c : V, (∑' x, tau π x c) = ∑' x, tau π o x := fun c => by
    rw [tau_col π hq c, ← tau_row π hq o]
  calc (∑' c1, ∑' c2, ∑' L : Fin 6 → V,
        hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2)
      = ∑' c1, ∑' c2,
          (secondMoment π c1 * tau π o c1) *
            ((secondMoment π c2 * tau π o c2) * ((∑' x, tau π x c1) * (∑' x, tau π x c2))) :=
        tsum_congr fun c1 => tsum_congr fun c2 => hubStarSix_tsum_fin π o c1 c2
    _ = ∑' c1, ∑' c2,
          (secondMoment π o * tau π o c1) *
            ((secondMoment π o * tau π o c2) * ((∑' x, tau π o x) * (∑' x, tau π o x))) :=
        tsum_congr fun c1 => tsum_congr fun c2 => by rw [hS c1, hS c2, hT c1, hT c2]
    _ = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 4 := by
        have hfac : ∀ c1 c2 : V,
            (secondMoment π o * tau π o c1) *
                ((secondMoment π o * tau π o c2) * ((∑' x, tau π o x) * (∑' x, tau π o x)))
              = (secondMoment π o * secondMoment π o * (∑' x, tau π o x) * (∑' x, tau π o x))
                  * (tau π o c1 * tau π o c2) := by
          intro c1 c2
          ring
        rw [tsum_congr fun c1 => tsum_congr fun c2 => hfac c1 c2]
        have hpull : (∑' c1, ∑' c2,
            (secondMoment π o * secondMoment π o * (∑' x, tau π o x) * (∑' x, tau π o x))
              * (tau π o c1 * tau π o c2))
            = (secondMoment π o * secondMoment π o * (∑' x, tau π o x) * (∑' x, tau π o x))
              * ((∑' c1, tau π o c1) * (∑' c2, tau π o c2)) := by
          rw [show (∑' c1, ∑' c2,
              (secondMoment π o * secondMoment π o * (∑' x, tau π o x) * (∑' x, tau π o x))
                * (tau π o c1 * tau π o c2))
              = ∑' c1, (secondMoment π o * secondMoment π o * (∑' x, tau π o x)
                  * (∑' x, tau π o x))
                * (∑' c2, tau π o c1 * tau π o c2) from
                tsum_congr fun c1 => ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_mul_left]
          congr 1
          exact PercLib.CriticalLRP.TreeExpansion.tsum_two_mul _ _
        rw [hpull]
        ring

/-! ## The slot-diagram evaluation -/

/-- **Pattern independence at `p = 6`.**  Every labelling of the six slots gives the same
value, so the event side is free to choose its own labelling family. -/
theorem tsum_slotK2Six [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 6)) (o : V) :
    (∑' L : Fin 6 → V, slotK2Six π σ o L)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 4 := by
  have hperm : (∑' L : Fin 6 → V, slotK2Six π σ o L)
      = ∑' L : Fin 6 → V, slotK2Six π (Equiv.refl (Fin 6)) o L := by
    have h := tsum_fin6_perm σ (G := fun L => slotK2Six π (Equiv.refl (Fin 6)) o L)
    refine (tsum_congr fun L => ?_).trans h
    simp only [slotK2Six, Equiv.refl_apply]
  rw [hperm]
  have hswap : (∑' L : Fin 6 → V, slotK2Six π (Equiv.refl (Fin 6)) o L)
      = ∑' c1, ∑' c2, ∑' L : Fin 6 → V,
          hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2 := by
    simp only [slotK2Six, Equiv.refl_apply]
    calc (∑' L : Fin 6 → V, ∑' c1, ∑' c2,
          hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2)
        = ∑' L : Fin 6 → V, ∑' c2, ∑' c1,
            hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2 :=
          tsum_congr fun L => ENNReal.tsum_comm
      _ = ∑' c2, ∑' L : Fin 6 → V, ∑' c1,
            hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2 := ENNReal.tsum_comm
      _ = ∑' c2, ∑' c1, ∑' L : Fin 6 → V,
            hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2 :=
          tsum_congr fun c2 => ENNReal.tsum_comm
      _ = ∑' c1, ∑' c2, ∑' L : Fin 6 → V,
            hubStarSix π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c1 c2 := ENNReal.tsum_comm
  rw [hswap, tsum_hubStarSix π hq o]

/-- The six-nested-sum form used by the moment assembly. -/
theorem tsum_slotK2Six_six [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 6)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s, slotK2Six π σ o ![y, z, w, q, r, s])
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 4 := by
  rw [← tsum_fin6 (G := fun L => slotK2Six π σ o L)]
  exact tsum_slotK2Six π hq σ o

/-- **A `Fin 6 → V` sum is a six-nested sum.** -/
theorem tsum_fin6_apply [Countable V] (G : (Fin 6 → V) → ℝ≥0∞) :
    (∑' X : Fin 6 → V, G X) =
      ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, G ![x0, x1, x2, x3, x4, x5] :=
  tsum_fin6 G

end PercLib.CriticalLRP.TreeExpansion.HubK2
