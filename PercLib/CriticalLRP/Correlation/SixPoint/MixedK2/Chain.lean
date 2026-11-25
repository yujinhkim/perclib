/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m4/Chain.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Assembly

/-!
A second two-hub shape for the `p = 5`, `k = 2` regrouping: the *chain* diagram, in which only
the first hub is linked to the root and the second hub hangs off the first along the spine.
Ultramath `smwvk712v` member `m4`.

The six-terminal cover committed at HEAD (`CombSystem`) has the spine `u — v — w`, so the two
selected 3-star centres are naturally adjacent along the spine rather than both linked to the
root directly.  This file proves that the chain shape has the same value,
`(E|K|^2)^2 (E|K|)^3`. These are evaluations only, not universal pointwise covers.
Nearest-neighbour percolation on `ℤ` refutes the universal fan/chain cover premises;
see `docs/CRITICAL_LRP_FIFTH_MOMENT.md`. The two shapes are:

* `hubStar`  (fan):   `J(a,b,c₁) · tau(o,c₁) · J(d,e,c₂) · tau(o,c₂) · tau(f,c₁)`;
* `hubChain` (chain): `J(a,b,c₁) · tau(o,c₁) · J(d,e,c₂) · tau(c₁,c₂) · tau(f,c₂)`.

Both are two joint pairs and three two-point factors, i.e. `k = 2` copies of the three-point
function and `2p - 1 - 3k = 3` copies of the two-point function, and both evaluate to
`(E|K|^2)^2 (E|K|)^3`.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}


/-- **Leaf factorization for the chain.** -/
theorem hubChain_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (o c1 c2 : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, hubChain π o a b d e f c1 c2)
      = (secondMoment π c1 * tau π o c1) *
          ((secondMoment π c2 * tau π c1 c2) * (∑' x, tau π x c2)) := by
  have hsplit := tsum_five_split (A := fun a b => jointP π a b c1 * tau π o c1)
    (B := fun d e => jointP π d e c2 * tau π c1 c2) (C := fun f => tau π f c2)
  have hA : (∑' a, ∑' b, jointP π a b c1 * tau π o c1)
      = secondMoment π c1 * tau π o c1 := by
    rw [tsum_two_mul_const, ← secondMoment_eq]
  have hB : (∑' d, ∑' e, jointP π d e c2 * tau π c1 c2)
      = secondMoment π c2 * tau π c1 c2 := by
    rw [tsum_two_mul_const, ← secondMoment_eq]
  have hshape : (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, hubChain π o a b d e f c1 c2)
      = ∑' a, ∑' b, ∑' d, ∑' e, ∑' f,
          (jointP π a b c1 * tau π o c1) * (jointP π d e c2 * tau π c1 c2) * tau π f c2 :=
    tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
      tsum_congr fun f => by simp only [hubChain]
  rw [hshape, hsplit, hA, hB]

/-- **Chain evaluation.**  Two joint pairs and a two-step spine give the same value as the fan:
`(E|K|^2)^2 (E|K|)^3`. -/
theorem tsum_hubChain [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' c1, ∑' c2, hubChain π o a b d e f c1 c2)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  have hS : ∀ c : V, secondMoment π c = secondMoment π o := fun c =>
    (secondMoment_root_independent π hq c).trans (secondMoment_root_independent π hq o).symm
  have hT : ∀ c : V, (∑' x, tau π x c) = ∑' x, tau π o x := fun c => by
    rw [tau_col π hq c, ← tau_row π hq o]
  have hR : ∀ c : V, (∑' x, tau π c x) = ∑' x, tau π o x := fun c =>
    (tau_row π hq c).trans (tau_row π hq o).symm
  rw [tsum_seven_swap]
  calc (∑' c1, ∑' c2, ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, hubChain π o a b d e f c1 c2)
      = ∑' c1, ∑' c2,
          (secondMoment π c1 * tau π o c1) *
            ((secondMoment π c2 * tau π c1 c2) * (∑' x, tau π x c2)) :=
        tsum_congr fun c1 => tsum_congr fun c2 => hubChain_tsum π o c1 c2
    _ = ∑' c1, ∑' c2,
          (secondMoment π o * tau π o c1) *
            ((secondMoment π o * tau π c1 c2) * (∑' x, tau π o x)) :=
        tsum_congr fun c1 => tsum_congr fun c2 => by rw [hS c1, hS c2, hT c2]
    _ = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
        have hinner : ∀ c1 : V,
            (∑' c2, (secondMoment π o * tau π o c1) *
                ((secondMoment π o * tau π c1 c2) * (∑' x, tau π o x)))
              = (secondMoment π o * tau π o c1) *
                  ((secondMoment π o * (∑' x, tau π o x)) * (∑' x, tau π o x)) := by
          intro c1
          rw [show (∑' c2, (secondMoment π o * tau π o c1) *
                ((secondMoment π o * tau π c1 c2) * (∑' x, tau π o x)))
              = ∑' c2, ((secondMoment π o * tau π o c1) *
                  (secondMoment π o * (∑' x, tau π o x))) * tau π c1 c2 from
                tsum_congr fun c2 => by ring]
          rw [ENNReal.tsum_mul_left]
          rw [hR c1]
          ring
        rw [tsum_congr hinner]
        rw [show (∑' c1, (secondMoment π o * tau π o c1) *
              ((secondMoment π o * (∑' x, tau π o x)) * (∑' x, tau π o x)))
            = ∑' c1, ((secondMoment π o * (∑' x, tau π o x)) *
                ((secondMoment π o * (∑' x, tau π o x)))) * tau π o c1 from
              tsum_congr fun c1 => by ring]
        rw [ENNReal.tsum_mul_left]
        rw [show (∑' c1, tau π o c1) = ∑' x, tau π o x from rfl]
        ring

/-- The single-sum (`Fin 5 → V`) form of the chain evaluation. -/
theorem tsum_slotChain [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 5)) (o : V) :
    (∑' L : Fin 5 → V, slotChain π σ o L)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  rw [tsum_fin5 (G := fun L => slotChain π σ o L)]
  exact (tsum_five_perm σ
    (H := fun y z w q r => ∑' c1, ∑' c2, hubChain π o y z w q r c1 c2)).trans
    (tsum_hubChain π hq o)

/-- The five-nested-sum form of the chain evaluation. -/
theorem tsum_slotChain_five [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 5)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, slotChain π σ o ![y, z, w, q, r])
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  rw [← tsum_fin5 (G := fun L => slotChain π σ o L)]
  exact tsum_slotChain π hq σ o

/-- **`p = 5`, `k = 2` from the chain-shaped pointwise event bound alone.** -/
theorem fifth_moment_mixed_k2_le_of_chainBound [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (pat : Fin 105 → Equiv.Perm (Fin 5))
    (hpoint : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' s : Fin 105, slotChain π (pat s) 0 ![y, z, w, q, r]) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 :=
  fifth_moment_le_of_hubDiagrams π (fun s y z w q r => slotChain π (pat s) 0 ![y, z, w, q, r])
    hpoint fun s => tsum_slotChain_five π hq (pat s) 0

end PercLib.CriticalLRP.TreeExpansion.HubK2
