/- Integrated from independently rebuilt Ultramath work.
Production base e6fb888fa60f4bb3d7fa5ab717b2d149345e3a7f.
Scratch source: repository-root .ultramath/smwwp7q3k/m1/.
-/

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Decorrelation quantities for the critical-dimension case (`d = 3α`) of the proof of
Hutchcroft, *Critical long-range percolation I*, Proposition I.4.20, Case 2.

The paper (p. 51) proves, for `0 ≤ ℓ ≤ p - 1`,
`0 ≤ |B_r| E_r|K|^{ℓ+1} E_r|K|^{p-ℓ}
   - E_r[|K|^{ℓ+1} Σ_{y ∈ B_r} 1(y ∉ K)|K_y|^{p-ℓ}] ≤ E_r[|K|^{p+1}|K ∩ B_r|]`,
then bounds the joint moment by Cauchy–Schwarz, the upper bound (I.4.19) at index `2p+2`, and
`E_r[|K ∩ B_r|²] ⪯ M_r E_r|K|` (universal tightness, Corollary I.2.5), and finally deduces
that the
error is `o(|B_r| (M₂/M₁)^{p-1} M₁²)` using `M_r = o(r^{(d+α)/2})` (the `Hydro` hypothesis).

This file only contains the definitions of those quantities in the model of
`PercLib.CriticalLRP.Orchestration`; no statement is asserted here.
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs

@[expose] public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace PercLib.CriticalLRP.Analysis.I420Case2

/-- `|K ∩ B_r|`: the volume of the cluster of the origin inside the ball `B_r` of the
cut-off model `M.cutLaw r`. This is the quantity `|K ∩ B_r|` of Proposition I.4.20. -/
def interVol (M : Orchestration.SourceModelData) (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  clusterVolIn ω (0 : M.V) (M.ball r)

/-- The joint moment `E_r[|K|^{p+1} |K ∩ B_r|]` of Proposition I.4.20, Case 2, which dominates
the decorrelation error. -/
def jointMoment (M : Orchestration.SourceModelData) (p : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ^ (p + 1) * interVol M r ω ∂(M.cutLaw r)

/-- The second moment `E_r[|K ∩ B_r|²]` of the intersection volume. -/
def interSecond (M : Orchestration.SourceModelData) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, interVol M r ω ^ 2 ∂(M.cutLaw r)

/-- The cardinality `|B_r|` of the ball, as a real number. -/
def ballCard (M : Orchestration.SourceModelData) (r : ℝ) : ℝ := ((M.ball r).ncard : ℝ)

/-- The normalized decorrelation target `|B_r| (M₂/M₁)^{p-1} M₁²` of estimate (I.4.21) in the
critical case `d = 3α`; here `m₁` and `m₂` are the first and second moments `E_r|K|`,
`E_r|K|²`. -/
def normTarget (M : Orchestration.SourceModelData) (p : ℕ) (m₁ m₂ : ℝ → ℝ)
    (r : ℝ) : ℝ :=
  ballCard M r * (m₂ r / m₁ r) ^ (p - 1) * m₁ r ^ 2

/-- The factor `√(C (M₂/M₁)^{2p+1} M₁)` coming from the upper bound (I.4.19) at index
`2p+2`. -/
def i419Factor (C : ℝ) (p : ℕ) (m₁ m₂ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.sqrt (C * (m₂ r / m₁ r) ^ (2 * p + 1) * m₁ r)

/-- The factor `√(M_r M₁)` coming from universal tightness,
`E_r[|K ∩ B_r|²] ⪯ M_r E_r|K|`. -/
def tightFactor (M : Orchestration.SourceModelData) (m₁ : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.sqrt ((M.Mr r : ℝ) * m₁ r)

/-- The Cauchy–Schwarz bound `√(C (M₂/M₁)^{2p+1} M₁) · √(M_r M₁)` on the joint moment
`E_r[|K|^{p+1}|K ∩ B_r|]`. -/
def jointUpper (M : Orchestration.SourceModelData) (p : ℕ) (C : ℝ) (m₁ m₂ : ℝ → ℝ)
    (r : ℝ) : ℝ :=
  i419Factor C p m₁ m₂ r * tightFactor M m₁ r

end PercLib.CriticalLRP.Analysis.I420Case2
