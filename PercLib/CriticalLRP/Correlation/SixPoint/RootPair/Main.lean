/- Integrated from reviewed Ultramath root-pair work.
Production base 1eaaabcf41deb59c0da2c83d0f2d7ad9d952510f.
Scratch source output: ../../.ultramath/smwvlmbqa/m3/Main.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.RootPair.Defs
public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Chain
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Perm

/-!
# The root-in-joint-pair `p = 5`, `k = 2` chain evaluates to `(E|K|^2)^2 (E|K|)^3`

`hubChainRoot` keeps the root inside the first joint pair, which is what Hutchcroft's
`p = 3` example of the proof of Lemma I.4.16 does (`{0 ↔ x, w}` grouped, `{w ↔ y}`,
`{w ↔ z}` single).  The production `hubStar` / `hubChain` instead spend a *separate*
two-point arm on the root at the first hub, and that extra arm is exactly the unit of
arm-cost that makes the pointwise five-point event bound fail in nearest-neighbour
percolation.

The evaluation needs one new ingredient relative to `HubK2.tsum_hubChain`: the first joint
pair carries the root, so its leaf sum is `A c1 = sum_a jointP o a c1` rather than a
constant second moment.  The spine sum then converts `A` into the second moment:

`sum_c1 sum_c2 A c1 * tau c1 c2 = (sum_c1 A c1) * chi = secondMoment o * chi`,

using `SixPoint.tsum_jointP_centre'` for `sum_c1 A c1 = secondMoment o`.  All remaining
factors are the susceptibility `chi = sum_x tau o x` and the second moment, so the total is
`(E|K|^2)^2 (E|K|)^3` as required by Lemma I.4.16 at `p = 5`, `k = 2`.

Nothing here uses a moment hypothesis, subcriticality or local finiteness: every step is an
identity of extended nonnegative quantities, and full translation invariance `hq` is used
only for root independence of the second moment and for the row/column sums of `tau`.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubRoot

open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.HubK2

variable {V : Type*}

/-! ## Leaf and hub sums -/

/-- **Leaf factorization for the root-in-pair chain.**  The pair `(o,a)` at `c1` keeps the
root, so its leaf sum is `A c1 = sum_a jointP o a c1`; the arm `b – c1` sums to the
susceptibility at `c1`. -/
theorem hubChainRoot_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (o c1 c2 : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, hubChainRoot π o a b d e f c1 c2)
      = ((∑' a, jointP π o a c1) * (∑' b, tau π b c1)) *
          ((secondMoment π c2 * tau π c1 c2) * (∑' x, tau π x c2)) := by
  have hsplit := tsum_five_split (A := fun a b => jointP π o a c1 * tau π b c1)
    (B := fun d e => jointP π d e c2 * tau π c1 c2) (C := fun f => tau π f c2)
  have hA : (∑' a, ∑' b, jointP π o a c1 * tau π b c1)
      = (∑' a, jointP π o a c1) * (∑' b, tau π b c1) := by
    rw [show (∑' a, ∑' b, jointP π o a c1 * tau π b c1)
        = ∑' a, jointP π o a c1 * (∑' b, tau π b c1) from
          tsum_congr fun a => ENNReal.tsum_mul_left]
    exact ENNReal.tsum_mul_right
  have hB : (∑' d, ∑' e, jointP π d e c2 * tau π c1 c2)
      = secondMoment π c2 * tau π c1 c2 := by
    rw [tsum_two_mul_const, ← secondMoment_eq]
  have hshape : (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, hubChainRoot π o a b d e f c1 c2)
      = ∑' a, ∑' b, ∑' d, ∑' e, ∑' f,
          (jointP π o a c1 * tau π b c1) * (jointP π d e c2 * tau π c1 c2) * tau π f c2 :=
    tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
      tsum_congr fun f => by simp only [hubChainRoot]
  rw [hshape, hsplit, hA, hB]

/-- **Root-in-pair chain evaluation.**  Two joint pairs and a two-step spine give
`(E|K|^2)^2 (E|K|)^3`, exactly as the fan and the production chain do. -/
theorem tsum_hubChainRoot [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, ∑' c2, hubChainRoot π o a b d e f c1 c2)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  have hS : ∀ c : V, secondMoment π c = secondMoment π o := fun c =>
    (secondMoment_root_independent π hq c).trans (secondMoment_root_independent π hq o).symm
  have hC : ∀ c : V, (∑' x, tau π x c) = ∑' x, tau π o x := fun c => by
    rw [tau_col π hq c, ← tau_row π hq o]
  have hR : ∀ c : V, (∑' x, tau π c x) = ∑' x, tau π o x := fun c =>
    (tau_row π hq c).trans (tau_row π hq o).symm
  rw [tsum_seven_swap]
  have hstep5 : (∑' c1, ∑' c2, (∑' a, jointP π o a c1) * tau π c1 c2)
      = (∑' c1, ∑' a, jointP π o a c1) * (∑' x, tau π o x) := by
    rw [show (∑' c1, ∑' c2, (∑' a, jointP π o a c1) * tau π c1 c2)
        = ∑' c1, (∑' a, jointP π o a c1) * (∑' c2, tau π c1 c2) from
          tsum_congr fun c1 => ENNReal.tsum_mul_left]
    rw [show (∑' c1, (∑' a, jointP π o a c1) * (∑' c2, tau π c1 c2))
        = ∑' c1, (∑' a, jointP π o a c1) * (∑' x, tau π o x) from
          tsum_congr fun c1 => by rw [hR c1]]
    exact ENNReal.tsum_mul_right
  have hcentre : (∑' c1, ∑' a, jointP π o a c1) = secondMoment π o := by
    rw [ENNReal.tsum_comm, PercLib.CriticalLRP.TreeExpansion.SixPoint.tsum_jointP_centre' π hq o,
      hS 0]
  calc (∑' c1, ∑' c2, ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, hubChainRoot π o a b d e f c1 c2)
      = ∑' c1, ∑' c2,
          (((∑' a, jointP π o a c1) * (∑' b, tau π b c1)) *
            ((secondMoment π c2 * tau π c1 c2) * (∑' x, tau π x c2))) :=
        tsum_congr fun c1 => tsum_congr fun c2 => hubChainRoot_tsum π o c1 c2
    _ = ∑' c1, ∑' c2,
          (((∑' a, jointP π o a c1) * (∑' x, tau π o x)) *
            ((secondMoment π o * tau π c1 c2) * (∑' x, tau π o x))) := by
        refine tsum_congr fun c1 => tsum_congr fun c2 => ?_
        rw [hC c1, hC c2, hS c2]
    _ = ((∑' x, tau π o x) * (secondMoment π o * (∑' x, tau π o x))) *
          (∑' c1, ∑' c2, (∑' a, jointP π o a c1) * tau π c1 c2) := by
        rw [show (∑' c1, ∑' c2,
              (((∑' a, jointP π o a c1) * (∑' x, tau π o x)) *
                ((secondMoment π o * tau π c1 c2) * (∑' x, tau π o x))))
            = ∑' c1, ∑' c2,
              ((∑' x, tau π o x) * (secondMoment π o * (∑' x, tau π o x))) *
                ((∑' a, jointP π o a c1) * tau π c1 c2) from
              tsum_congr fun c1 => tsum_congr fun c2 => by ring]
        refine (tsum_congr fun c1 => ENNReal.tsum_mul_left).trans ?_
        exact ENNReal.tsum_mul_left
    _ = ((∑' x, tau π o x) * (secondMoment π o * (∑' x, tau π o x))) *
          (secondMoment π o * (∑' x, tau π o x)) := by rw [hstep5, hcentre]
    _ = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by ring

/-! ## The slot diagram -/

/-- The single-sum (`Fin 5 → V`) form of the root-in-pair chain evaluation. -/
theorem tsum_slotChainRoot [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 5)) (o : V) :
    (∑' L : Fin 5 → V, slotChainRoot π σ o L)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  rw [tsum_fin5 (G := fun L => slotChainRoot π σ o L)]
  exact (tsum_five_perm σ
    (H := fun y z w q r => ∑' c1, ∑' c2, hubChainRoot π o y z w q r c1 c2)).trans
    (tsum_hubChainRoot π hq o)

/-- The five-nested-sum form of the root-in-pair chain evaluation. -/
theorem tsum_slotChainRoot_five [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 5)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, slotChainRoot π σ o ![y, z, w, q, r])
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  rw [← tsum_fin5 (G := fun L => slotChainRoot π σ o L)]
  exact tsum_slotChainRoot π hq σ o

/-- The root-in-pair chain evaluation in the native normalisers. -/
theorem tsum_slotChainRoot_native [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 5)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, slotChainRoot π σ o ![y, z, w, q, r])
      = secondMoment π o ^ 2 * firstMoment π o ^ 3 := by
  rw [tsum_slotChainRoot_five π hq σ o, firstMoment_eq]

/-! ## The conditional `k = 2` consumer -/

/-- **`p = 5`, `k = 2` from the root-in-pair pointwise event bound alone.**  This is the
corrected companion of `HubK2.fifth_moment_mixed_k2_le_of_hubBound` and
`.of_chainBound`: the pointwise premise now has a shape whose arm cost reaches the
five-point event's cost in nearest-neighbour percolation, which neither the fan nor the
production chain does. -/
theorem fifth_moment_mixed_k2_le_of_chainRootBound [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (pat : Fin 105 → Equiv.Perm (Fin 5))
    (hpoint : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' s : Fin 105, slotChainRoot π (pat s) 0 ![y, z, w, q, r]) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 :=
  fifth_moment_le_of_hubDiagrams π
    (fun s y z w q r => slotChainRoot π (pat s) 0 ![y, z, w, q, r])
    hpoint fun s => tsum_slotChainRoot_five π hq (pat s) 0

/-- **The exact coefficient `105`.**  For any family of `105` leaf labellings, the sum of the
root-in-pair chain diagrams over the five free leaves is `105 * (E|K|^2)^2 (E|K|)^3` — the
`p = 5`, `k = 2` instance of `(2p-3)!! (E|K|^2)^k (E|K|)^{2p-1-3k}` with `(2 * 5 - 3)!! = 105`. -/
theorem tsum_fin105_slotChainRoot_five [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (pat : Fin 105 → Equiv.Perm (Fin 5)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s : Fin 105,
        slotChainRoot π (pat s) o ![y, z, w, q, r])
      = 105 * (secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3) := by
  rw [PercLib.CriticalLRP.TreeExpansion.SixPoint.tsum_fin_five_swap]
  rw [show (∑' s : Fin 105, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        slotChainRoot π (pat s) o ![y, z, w, q, r])
      = ∑' _s : Fin 105, secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 from
        tsum_congr fun s => tsum_slotChainRoot_five π hq (pat s) o]
  exact PercLib.CriticalLRP.TreeExpansion.SixPoint.tsum_fin105_const _

end PercLib.CriticalLRP.TreeExpansion.HubRoot

