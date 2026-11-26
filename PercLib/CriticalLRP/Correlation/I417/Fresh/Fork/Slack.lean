/- Independently rebuilt and integrated finding f4 of swarm `smwwyd7lg`, member `m1`.
Production integration revision: `d2734e7c030f377ae4642466daef7f78ff648cb8`. -/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Fork.Main

/-!
# What the chain family already contains: the single-hub diagram

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof.

`freshChainBound π q y w` is a sum over spine vectors `u : Fin (q+1) → V`.  This
file evaluates it at the constant spine `u ≡ a`.  The `q+1` slot factors all
become `χ(a) + τ(a,y)`, and the `q+1` spine factors become `τ(w,a) · τ(a,a)^q`
=`τ(w,a)`.  Consequently the chain family at every order `q ≥ 0` already
contains the *single-hub* diagram with `q+1` legs at one hub `a`,

  `τ(w,a) · (χ(a) + τ(a,y))^(q+1)`,

which is the `(q+1)`-leg version of the two-hub fork's monomial.  So the reason the
chain family fails at `q = 3` is *not* that its diagram value is too small at a
single hub — the "stay" step `v (i+1) = v i` of the spine puts arbitrarily many
legs at one hub — but that a chain *walk out of the mark* cannot visit two hubs
that both hang directly off the mark.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

namespace Q3

variable {V : Type*} [Countable V]

/-- The spine factors of `chainTerm` at the constant spine `u ≡ a`: they
collapse to the single factor `τ(w,a)`. -/
theorem chainSpine_const (π : Sym2 V → unitInterval) (q : ℕ) (w a : V) :
    (∏ i : Fin (q + 1),
        tau π (constSpine w a q (Fin.castSucc i)) (constSpine w a q i.succ)) =
      tau π w a := by
  rw [Fin.prod_univ_succ]
  have h0 : tau π (constSpine w a q (Fin.castSucc (0 : Fin (q + 1))))
      (constSpine w a q (0 : Fin (q + 1)).succ) = tau π w a := by
    simp [constSpine]
  rw [h0]
  have hrest : (∏ i : Fin q,
      tau π (constSpine w a q (Fin.castSucc i.succ)) (constSpine w a q (i.succ).succ)) = 1 := by
    rw [Finset.prod_eq_one]
    intro i _
    simp [constSpine, tau_self_apply]
  rw [hrest, mul_one]

/-- The slot factors of `chainTerm` at the constant spine `u ≡ a`: the `q+1`
copies of `χ(a) + τ(a,y)`. -/
theorem chainSlot_const (π : Sym2 V → unitInterval) (q : ℕ) (y w a : V) :
    (∏ i : Fin (q + 1),
        (hubArmSum π (constSpine w a q i.succ) + tau π (constSpine w a q i.succ) y)) =
      (hubArmSum π a + tau π a y) ^ (q + 1) := by
  rw [show (∏ i : Fin (q + 1),
      (hubArmSum π (constSpine w a q i.succ) + tau π (constSpine w a q i.succ) y)) =
      ∏ _ : Fin (q + 1), (hubArmSum π a + tau π a y) from
    Finset.prod_congr rfl (fun i _ => by simp [constSpine])]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The chain monomial at the constant spine. -/
theorem chainTerm_const (π : Sym2 V → unitInterval) (q : ℕ) (y w a : V) :
    chainTerm π q y w (fun _ => a) = tau π w a * (hubArmSum π a + tau π a y) ^ (q + 1) := by
  have hspine := chainSpine_const π q w a
  have hslot := chainSlot_const π q y w a
  simp only [chainTerm, constSpine] at hspine hslot ⊢
  rw [hspine, hslot]

/-- **The single-hub diagram with `q+1` legs is inside the chain family.**  At the
constant spine `u ≡ a` the `q`-th chain monomial is exactly
`τ(w,a) · (χ(a) + τ(a,y)) ^ (q+1)`: the spine pays `τ(w,a)` and every one of the
`q+1` slots reads the same hub `a`.  Hence the chain family at `q` already
contains the `q+1`-leg single-hub diagram at every hub `a`. -/
theorem singleHub_le_chain (π : Sym2 V → unitInterval) (q : ℕ) (y w a : V) :
    tau π w a * (hubArmSum π a + tau π a y) ^ (q + 1) ≤ freshChainBound π q y w := by
  rw [freshChainBound_eq_tsum]
  refine le_trans ?_ (ENNReal.le_tsum (f := chainTerm π q y w) (fun _ => a))
  rw [chainTerm_const]


/-- The map `a ↦ (u ≡ a)` from hubs to constant spine vectors is injective. -/
theorem constSpineVec_injective (q : ℕ) :
    Function.Injective (fun a : V => (fun _ : Fin (q + 1) => a)) := by
  intro a b h
  have h0 := congrFun h 0
  simpa using h0

/-- **The hub-averaged single-hub family is inside the chain family.**  Summing
`τ(w,a) · (χ(a) + τ(a,y)) ^ (q+1)` over the hub `a` costs nothing: the first
spine vertex of `freshChainBound` is itself summed over `V`. -/
theorem hubAveraged_le_chain (π : Sym2 V → unitInterval) (q : ℕ) (y w : V) :
    (∑' a : V, tau π w a * (hubArmSum π a + tau π a y) ^ (q + 1)) ≤
      freshChainBound π q y w := by
  rw [freshChainBound_eq_tsum]
  have heq : (∑' a : V, tau π w a * (hubArmSum π a + tau π a y) ^ (q + 1)) =
      ∑' a : V, chainTerm π q y w (fun _ => a) :=
    tsum_congr fun a => (chainTerm_const π q y w a).symm
  rw [heq]
  exact ENNReal.tsum_comp_le_tsum_of_injective (constSpineVec_injective q) _

/-- **The fresh side of Lemma I.4.17 from one hub-moment inequality.**  If the
`q`-fold hub moment is bounded by the hub-averaged single-hub family, then
`FreshCombBound π q` holds with the production diagram value — no further
premise, no finiteness hypothesis, no change to the diagram family. -/
theorem freshCombBound_of_hubMoment (π : Sym2 V → unitInterval) {q : ℕ}
    (h : ∀ y w : V, (∑' g : Fin q → V, (edgeMeasure π) (hubStar y w g)) ≤
      ∑' a : V, tau π w a * (hubArmSum π a + tau π a y) ^ (q + 1)) :
    FreshCombBound π q := by
  intro y w j
  refine le_trans (fresh_factor_le_hubStar π y w j) ?_
  refine le_trans (h y w) ?_
  refine le_trans (hubAveraged_le_chain π q y w) ?_
  rw [freshCombBound]
  exact self_le_add_right _ _

/-- The `q = 3` instance of `freshCombBound_of_hubMoment`. -/
theorem freshCombBound_three_of_hubMoment (π : Sym2 V → unitInterval)
    (h : ∀ y w : V, (∑' g : Fin 3 → V, (edgeMeasure π) (hubStar y w g)) ≤
      ∑' a : V, tau π w a * (hubArmSum π a + tau π a y) ^ (4)) :
    FreshCombBound π 3 :=
  freshCombBound_of_hubMoment π h

end Q3

end PercLib.CriticalLRP.I417Fresh

