/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.4.1: the algebra of the error terms `𝓔_{0,r}`,
`𝓔_{1,r}`, `𝓔_{2,r}` and `𝓗_r`, i.e. the passage

  (I.4.5)  d/dr E|K| = β|J'(r)| E[|K| ∑_{y∈B_r} 1(y∉K)|K_y|]
  (I.4.6)  d/dr E|K| = (1 - Ē_{1,r}) β r^{-α-1} (E|K|)²

and, for the second moment,

  (I.4.14) d/dr E|K|² = 3β|J'(r)| E[|K| ∑_{y∈B_r} 1(y∉K)|K_y|²]
  (I.4.15) d/dr E|K|² = 3α (1 - Ē_{2,r}) r^{-1} E|K|².

Both are pure algebra once the pivot identity of `ClusterAlgebra.lean` has been
applied.  Recall how the paper defines the errors (pp. 35 and 43):

  `𝓔_{1,r} = (|B_r|(E|K|)² - E[|K|∑_{y∈B_r}|K_y|] + E[|K|²|K∩B_r|]) / (|B_r|(E|K|)²)`
  `1 - 𝓔_{0,r} = |J'(r)||B_r| / r^{-α-1}`
  `1 - Ē_{1,r} = (1 - 𝓔_{1,r})(1 - 𝓔_{0,r})`

and, with `𝓗_r := (β/α) r^{-α}A - 1` (so that `A = (α/β) r^α (1 + 𝓗_r)`),

  `𝓔_{2,r} = (|B_r|E|K|E|K|² - E[|K|∑_{y∈B_r}1(y∉K)|K_y|²]) / (|B_r|E|K|E|K|²)`
  `1 - Ē_{2,r} = (1 - 𝓔_{2,r})(1 + 𝓗_r)(1 - 𝓔_{0,r})`.

The point of the two theorems below is that these definitions do exactly what the
paper says they do *given the pivot identity* (which is what turns
`E[|K|∑1(y∉K)|K_y|]` into `|B_r|(E|K|)²(1 - 𝓔_{1,r})`, and similarly for `q = 2`).
Nothing probabilistic is asserted: the expectations are real numbers constrained
by the pivot identity, so any measure supplying it instantiates these.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

namespace PercLib.CriticalLRP.VolumeMoments

/-- `1 - 𝓔_{0,r} = |J'(r)||B_r| / r^{-α-1}`, multiplied out. -/
def oneSubE0 (J b r α : ℝ) : ℝ := J * b * r ^ (α + 1)

/-- The paper's `𝓔_{1,r}` (p. 35), with `S = E[|K|∑_{y∈B_r}|K_y|]`,
`T = E[|K|²|K∩B_r|]`, `b = |B_r|`, `A = E|K|`. -/
def cE1 (A S T b : ℝ) : ℝ := (b * A ^ 2 - S + T) / (b * A ^ 2)

/-- `1 - Ē_{1,r} = (1 - 𝓔_{1,r})(1 - 𝓔_{0,r})` (p. 35). -/
def oneSubEbar1 (E1 J b r α : ℝ) : ℝ := (1 - E1) * oneSubE0 J b r α

/-- The paper's `𝓔_{2,r}` (p. 43), with `U = E[|K|∑_{y∈B_r}1(y∉K)|K_y|²]`
(after the pivot identity with `q = 2` has been applied to the paper's
`E[|K|∑|K_y|²] + E[|K|³|K∩B_r|]` form), `A2 = E|K|²`. -/
def cE2 (A A2 U b : ℝ) : ℝ := (b * A * A2 - U) / (b * A * A2)

/-- `1 - Ē_{2,r} = (1 - 𝓔_{2,r})(1 + 𝓗_r)(1 - 𝓔_{0,r})` (p. 43). -/
def oneSubEbar2 (E2 H J b r α : ℝ) : ℝ := (1 - E2) * (1 + H) * oneSubE0 J b r α

/-- **The passage (I.4.5) ⟹ (I.4.6).**  `β|J'(r)|(S - T)` is the right-hand
side of (I.4.5) after the pivot identity `S - T = |B_r|(E|K|)²(1 - 𝓔_{1,r})`;
the claim is that it equals `(1 - Ē_{1,r}) β r^{-α-1}(E|K|)²`. -/
theorem first_moment_ODE_of_pivot {A S T b J β r α : ℝ} (hA : 0 < A) (hb : 0 < b) (hr : 0 < r) :
    β * J * (S - T)
      = oneSubEbar1 (cE1 A S T b) J b r α * β * r ^ (-α - 1) * A ^ 2 := by
  have hrpow : r ^ (α + 1) * r ^ (-α - 1) = 1 := by
    rw [← Real.rpow_add hr]
    norm_num
  have hST : S - T = b * A ^ 2 * (1 - cE1 A S T b) := by
    unfold cE1
    field_simp
    ring
  have hbA : b * A ^ 2 ≠ 0 := by positivity
  unfold oneSubEbar1 oneSubE0
  rw [hST]
  calc β * J * (b * A ^ 2 * (1 - (b * A ^ 2 - S + T) / (b * A ^ 2)))
      = (1 - (b * A ^ 2 - S + T) / (b * A ^ 2)) * (J * b * r ^ (α + 1))
          * β * r ^ (-α - 1) * A ^ 2 := by
        rw [show (1 - (b * A ^ 2 - S + T) / (b * A ^ 2)) * (J * b * r ^ (α + 1)) * β
            * r ^ (-α - 1) * A ^ 2
            = (1 - (b * A ^ 2 - S + T) / (b * A ^ 2)) * (J * b) * β * A ^ 2
              * (r ^ (α + 1) * r ^ (-α - 1)) from by ring]
        rw [hrpow]
        ring
    _ = _ := rfl

/-- **The passage (I.4.14) ⟹ (I.4.15).**  With `A = E|K| = (α/β) r^α (1 + 𝓗_r)`,
`A2 = E|K|²` and `U = E[|K|∑1(y∉K)|K_y|²] = |B_r|A·A2(1 - 𝓔_{2,r})`,
the right-hand side of (I.4.14) equals `3α(1 - Ē_{2,r}) r^{-1} A2`. -/
theorem second_moment_ODE_of_pivot {A A2 U b J β r α H : ℝ}
    (hA : 0 < A) (hA2 : 0 < A2) (hb : 0 < b) (hr : 0 < r) (hβ : β ≠ 0)
    (hAr : A = (α / β) * r ^ α * (1 + H)) :
    3 * β * J * U = 3 * α * oneSubEbar2 (cE2 A A2 U b) H J b r α * r ^ (-1 : ℝ) * A2 := by
  set E2 := cE2 A A2 U b with hE2
  have hrpow : r ^ (α + 1) * r ^ (-1 : ℝ) = r ^ α := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hU : U = b * A * A2 * (1 - E2) := by
    rw [hE2]; unfold cE2; field_simp; ring
  have hβA : β * A = α * r ^ α * (1 + H) := by
    rw [hAr]; field_simp
  have hRHS : oneSubEbar2 E2 H J b r α * r ^ (-1 : ℝ)
      = (1 - E2) * (1 + H) * (J * b) * r ^ α := by
    unfold oneSubEbar2 oneSubE0
    rw [show (1 - E2) * (1 + H) * (J * b * r ^ (α + 1)) * r ^ (-1 : ℝ)
        = (1 - E2) * (1 + H) * (J * b) * (r ^ (α + 1) * r ^ (-1 : ℝ)) from by ring,
      hrpow]
  calc 3 * β * J * U
      = 3 * J * (β * A) * b * A2 * (1 - E2) := by rw [hU]; ring
    _ = 3 * J * (α * r ^ α * (1 + H)) * b * A2 * (1 - E2) := by rw [hβA]
    _ = 3 * α * oneSubEbar2 E2 H J b r α * r ^ (-1 : ℝ) * A2 := by
        have e1 : 3 * J * (α * r ^ α * (1 + H)) * b * A2 * (1 - E2)
            = 3 * α * ((1 - E2) * (1 + H) * (J * b) * r ^ α) * A2 := by ring
        rw [e1]
        unfold oneSubEbar2 oneSubE0
        rw [show r ^ (α + 1) = r ^ α * r from by
          rw [Real.rpow_add hr, Real.rpow_one]]
        rw [Real.rpow_neg_one]
        field_simp

end PercLib.CriticalLRP.VolumeMoments
