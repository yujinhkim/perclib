/-
Coordinator-integrated from the independently rebuilt `smwxb4a1l/m3` Line6 artifact
at production base `8d1c9eb3738a26cc63afc07f525ba4af357bd905`.
-/
/-
The exponent count for the six-vertex line counterexample.

Ultramath swarm `smwxb4a1l`, member `m3`, direction `HUB-LINK-COUNTEREXAMPLE`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Reach

/-!
# Exponent count

For every labelling of the five slots by the five leaves `1,2,3,4,5` and every choice of the
two hubs, the exponent
`max (pdist a c₁) (pdist b c₁) + c₁ + pdist f c₁ + max (pdist d c₂) (pdist e c₂) + c₂`
is at least `7`.  The finite check is by decision over the `120 × 36` cases, and `7` is
attained, so the count cannot be improved.
-/

set_option maxRecDepth 40000

@[expose] public section

namespace PercLib.CriticalLRP.Counterexample.Line6

/-- The hub exponent is at least `7` for every slot labelling and both hubs. -/
theorem exp_eight :
    ∀ (σ : Equiv.Perm (Fin 5)) (c1 c2 : Fin 6),
      7 ≤ max (pdist (leaves (σ 0)) c1) (pdist (leaves (σ 1)) c1) + c1.val
        + pdist (leaves (σ 4)) c1
        + max (pdist (leaves (σ 2)) c2) (pdist (leaves (σ 3)) c2) + c2.val := by
  decide

/-- The bound `7` is attained, so it cannot be improved. -/
theorem exp_seven_attained :
    ∃ (σ : Equiv.Perm (Fin 5)) (c1 c2 : Fin 6),
      max (pdist (leaves (σ 0)) c1) (pdist (leaves (σ 1)) c1) + c1.val
        + pdist (leaves (σ 4)) c1
        + max (pdist (leaves (σ 2)) c2) (pdist (leaves (σ 3)) c2) + c2.val = 7 := by
  decide

end PercLib.CriticalLRP.Counterexample.Line6
