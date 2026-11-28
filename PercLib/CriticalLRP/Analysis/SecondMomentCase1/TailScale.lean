/-
Compatibility interface for the earlier partial scale-calculation packet.
The complete proof is in `SecondMomentCase1.Capstone`. Its definitions supersede
that packet's repeated partial declarations without changing their statements.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase1.Capstone

/-! Historical scale-analysis interface, re-exporting the completed tail proof.

The declarations that were introduced as partial scale lemmas now resolve to the
complete `Capstone` development. Only its independent product-of-even-integers
helper stays here, since the completed proof inlines that calculation.
-/

@[expose] public section

noncomputable section

open Finset
open scoped BigOperators

namespace CaseOneTail

lemma eq_even (q : ℕ) :
    (∏ i ∈ Finset.range (q - 1), (2 * i + 2)) = 2 ^ (q - 1) * Nat.factorial (q - 1) := by
  have step : (∏ i ∈ Finset.range (q - 1), (2 * i + 2)) =
      ∏ i ∈ Finset.range (q - 1), (2 * (i + 1)) := by
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [step, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_range_add_one_eq_factorial]

end CaseOneTail

set_option linter.hashCommand false
#print axioms CaseOneTail.eq_even
