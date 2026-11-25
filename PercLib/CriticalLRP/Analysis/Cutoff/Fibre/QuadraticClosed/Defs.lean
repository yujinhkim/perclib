/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Truncated and full quadratic closed-edge increments

Integration donors: `.ultramath/smwvbcnfb/m1/P2Excluded.lean` and
`.ultramath/smwvc1d9z/m1/mirror/Defs.lean`, independently reviewed at `a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f`.
Definitions migrated here to keep proof modules definition-free.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.RussoAssembly.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Defs

/-!
# Quadratic excluded increments, with and without a finite truncation
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The ordered-pair excluded quadratic increment under a finite truncation:
`1(o ↔ b) · 1(d c b) · 1(b ↮ c) · (2|K_o∩A||K_c∩A| + |K_c∩A|²)`. -/
noncomputable def qPairIncr (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (A : Finset V) (b c : V) : ℝ≥0∞ :=
  (if Connects ω o b then (1 : ℝ≥0∞) else 0) * (if d c b then 1 else 0) *
    (if ¬ Connects ω b c then 1 else 0) *
    (2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
      + sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ^ 2)

/-- The unordered-edge `p = 2` excluded increment: the sum of the two ordered-pair orientations,
carrying the paper's distance indicator `1(d x y)` on the edge. -/
noncomputable def qEdgeIncr (d : V → V → Prop) [DecidableRel d] (hd : ∀ a b, (d a b ↔ d b a))
    (ω : Config V) (o : V) (A : Finset V) (e : Sym2 V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun x y => (if d x y then 1 else 0) *
      (qPairIncr d ω o A x y + qPairIncr d ω o A y x), by
    intro a b
    dsimp only
    by_cases hab : d a b
    · have hba : d b a := (hd b a).mpr hab
      simp only [hab, hba, ite_true]
      ring
    · have hba : ¬ d b a := fun h => hab ((hd b a).mp h)
      simp only [hab, hba, ite_false]
      ring⟩ e

/-- The same quadratic excluded increment without a truncation, using the actual full
cluster volumes. -/
noncomputable def qPairIncrFull (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (b c : V) : ℝ≥0∞ :=
  (if Connects ω o b then (1 : ℝ≥0∞) else 0) * (if d c b then 1 else 0) *
    (if ¬ Connects ω b c then 1 else 0) *
    (2 * clusterVol ω o * clusterVol ω c + clusterVol ω c ^ 2)

/-- The untruncated unordered-edge `p = 2` excluded increment: `qPairIncrFull` read as a function
of the unordered edge, i.e. the sum of its two ordered-pair orientations, carrying the paper's
distance indicator `1(d x y)` on the edge. -/
noncomputable def qEdgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (e : Sym2 V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun x y => (if d x y then 1 else 0) *
      (qPairIncrFull d ω o x y + qPairIncrFull d ω o y x), by
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
