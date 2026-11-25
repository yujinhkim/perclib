/-
# Ordered-pair and unordered-edge excluded increments

Independently reviewed intermediate packet from swarm `smwtvrwnn` member `m3`, direction D1C.
These definitions package the excluded increment only; the finite-fibre reindexing and `A ↑ V` limit
remain open.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv

/-!
The ordered-pair increment and its unordered-edge counterpart.
-/

set_option autoImplicit false

@[expose] public section

open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The ordered-pair (`p = 1`, standardized) excluded integrand with the cluster volume truncated to
the finite vertex set `A`: the paper's `pivotWeight r ω 0 b c` with `|K_c|` replaced by
`|K_c ∩ A|`.  `d` is the two-point distance predicate (`d c b` is `M.S.dist c b ≤ r`). -/
noncomputable def pairIncr (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (A : Finset V) (b c : V) : ℝ≥0∞ :=
  (if Connects ω o b then (1 : ℝ≥0∞) else 0) * (if d c b then 1 else 0) *
    (if ¬ Connects ω b c then 1 else 0) * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω

/-- The same excluded increment read as a function of the **edge** `{x,y}`: the increment of
`|K_o ∩ A|` produced by opening that edge, restricted to the closed event.  This is the `e`-th
summand of the standardized edge flux. -/
noncomputable def edgeIncr (d : V → V → Prop) [DecidableRel d] (hd : ∀ a b, (d a b ↔ d b a))
    (ω : Config V) (o : V) (A : Finset V) (e : Sym2 V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun x y => (if d x y then 1 else 0) *
      ((if Connects ω o x then (1 : ℝ≥0∞) else 0) *
          (if ¬ Connects ω x y then 1 else 0) *
          sMomentTruncENN (fun _ => (1 : ℝ)) y A ω
        + (if Connects ω o y then (1 : ℝ≥0∞) else 0) *
          (if ¬ Connects ω y x then 1 else 0) *
          sMomentTruncENN (fun _ => (1 : ℝ)) x A ω), by
    intro a b
    dsimp only
    by_cases hab : d a b
    · have hba : d b a := (hd b a).mpr hab
      simp only [hab, hba, ite_true]
      ring
    · have hba : ¬ d b a := fun h => hab ((hd b a).mp h)
      simp only [hab, hba, ite_false]
      ring⟩ e


end PercLib.CriticalLRP.Orchestration
