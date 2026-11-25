/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Non-vacuity witness for `I58Reflect.PRefl`, i.e. for the point-reflection
hypothesis that discharges `(BC)` and `(DF)` of Lemma I.5.8.

The model below is a genuine (if tiny) percolation model: three edges on the
line, clusters = connected components, and the uniform law on the `2^3 = 8`
edge configurations, which is invariant under the point reflection
`x ↦ y - x` at `y = 1`.

Edges:      `a = {0, y}`,  `b = {y, 3y}`,  `c = {0, -2y}`,
with `y = e₁ ∈ Z¹`.  The set of edges is invariant under `ρ_y : x ↦ y - x`:
`ρ_y` fixes `{0,y}` and swaps `{y,3y} ↔ {0,-2y}` (because `ρ_y(3y) = -2y`).
Hence

  `K_0(ω)  = {0} ∪ (a?{y}) ∪ (c?{-2y})`,
  `K_y(ω)  = {y} ∪ (a?{0}) ∪ (b?{3y})`,

and the induced involution `R` on configurations swaps the bits `b` and `c`.
All hypotheses of `PRefl` are then verified by `decide` (they are Bool/Finset
statements only — no real arithmetic), and the two comparisons are *non-trivial*
there: on `ω = (a,b,c) = (0,1,1)` the clusters are `{0,-2y}` and `{y,3y}`, so
`Σ_{z∈K_y} q_u(z-y) = q_u(0·u) + q_u(2y·u) = 0 + 4 = 4` and
`Σ_{x∈K_0} q_u(x) = q_u(0) + q_u(-2y) = 4` — the two sides of `(BC)` are the
same non-zero number, and on `ω = (0,1,0)` they differ (`B = 4`, `C = 0`), so
`(BC)` is genuinely an identity *in expectation*, not pointwise.  Likewise
`D = 4, F = -4` on `ω = (0,1,1)` and `D + F = 0` only after averaging.

No `sorry`, no `admit`, no custom axioms, no `native_decide`.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.I58Reflect

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.I58

/-! ## 1. The three-edge model -/

/-- The distinguished site `y = e₁`. -/
def wy : Site 1 := fun _ => 1

/-- The site `3y`. -/
def w3 : Site 1 := fun _ => 3

/-- The site `-2y = ρ_y(3y)`. -/
def wm2 : Site 1 := fun _ => -2

/-- The linear functional `u = 1`, so that `⟪x,u⟫ = x₁` and `q_u(x) = x₁²`. -/
def wu : Fin 1 → ℝ := fun _ => 1

/-- The uniform law on the `8` edge configurations. -/
noncomputable def ww : (Fin 3 → Bool) → ℝ := fun _ => 1 / 8

/-- The configuration-space involution induced by `ρ_y`: swap the bits of the
edges `{y,3y}` and `{0,-2y}`. -/
def wR (ω : Fin 3 → Bool) : Fin 3 → Bool :=
  fun i => if i = 1 then ω 2 else if i = 2 then ω 1 else ω 0

/-- The cluster of `0`. -/
def wK0 (ω : Fin 3 → Bool) : Finset (Site 1) :=
  ({0} : Finset (Site 1)) ∪ (if ω 0 then {wy} else ∅)
    ∪ (if ω 2 then {wm2} else ∅)

/-- The cluster of `y` (disjoint from `K_0` exactly when the edge `{0,y}` is
absent, and then equal to the restored cluster `K_y` of `I58Remainder`). -/
def wK1 (ω : Fin 3 → Bool) : Finset (Site 1) :=
  ({wy} : Finset (Site 1)) ∪ (if ω 0 then {0} else ∅)
    ∪ (if ω 1 then {w3} else ∅)

/-- The cluster map `y' ↦ K_{y'}`; only its value at `y' = y` is used by
`PRefl`. -/
def wKy (y' : Site 1) (ω : Fin 3 → Bool) : Finset (Site 1) :=
  if y' = wy then wK1 ω else ∅

/-! ## 2. The point-reflection hypotheses, verified -/

theorem wR_involutive : Function.Involutive wR := by
  intro ω
  funext i
  fin_cases i <;> simp [wR]

theorem wK0_refl : ∀ ω : Fin 3 → Bool, wK0 (wR ω) = (wK1 ω).image (rho wy) := by
  decide

theorem wK1_refl : ∀ ω : Fin 3 → Bool, wK1 (wR ω) = (wK0 ω).image (rho wy) := by
  decide

theorem wsep : ∀ ω : Fin 3 → Bool, (wy ∈ wK0 ω ↔ 0 ∈ wK1 ω) := by
  decide

/-- **The point-reflection hypothesis holds in the three-edge model.** -/
noncomputable def witness_PRefl : PRefl wu wK0 wKy ww wy where
  R := wR
  invol := wR_involutive
  weight := fun _ => rfl
  cluster0 := fun ω => by
    show wK0 (wR ω) = (wKy wy ω).image (rho wy)
    rw [show wKy wy ω = wK1 ω from by simp [wKy]]
    exact wK0_refl ω
  clusterY := fun ω => by
    show wKy wy (wR ω) = (wK0 ω).image (rho wy)
    rw [show wKy wy (wR ω) = wK1 (wR ω) from by simp [wKy]]
    exact wK1_refl ω
  sep := wsep

/-! ## 3. Non-degeneracy: the clusters are genuine, and the sums are not `0 = 0` -/

/-- The configuration with the edges `{y,3y}` and `{0,-2y}` present and `{0,y}`
absent: then `0` and `y` are separated and `K_y = {y, 3y}`. -/
def wcfg : Fin 3 → Bool := fun i => if i = 0 then false else true

theorem wcfg_sep : wy ∉ wK0 wcfg := by decide

theorem wcfg_K1 : wK1 wcfg = {wy, w3} := by decide

/-- The distinguished site `y` is not connected to `0`, and its cluster is
`{y, 3y}`: the point reflection hypothesis is therefore not about a degenerate
("everything connected" or "nothing connected") configuration. -/
theorem wcfg_nontrivial : wy ∉ wK0 wcfg ∧ wK1 wcfg = {wy, w3} :=
  ⟨wcfg_sep, wcfg_K1⟩

theorem w3_sub_wy : w3 - wy = (fun _ => (2 : ℤ)) := by
  funext i; fin_cases i; rfl

theorem wm2_eq : wm2 = (fun _ => (-2 : ℤ)) := rfl

/-- `q_u(2·u) = 4`: the shifted quadratic weight really moves. -/
theorem q_w3_sub : q wu (w3 - wy) = 4 := by
  rw [w3_sub_wy]
  simp only [q, dot, wu, Fin.sum_univ_one]
  norm_num

/-- `q_u(-2·u) = 4`, the reflected side. -/
theorem q_wm2 : q wu wm2 = 4 := by
  rw [wm2_eq]
  simp only [q, dot, wu, Fin.sum_univ_one]
  norm_num

/-- `⟪2·u⟫ = 2`. -/
theorem dot_w3_sub : dot wu (w3 - wy) = 2 := by
  rw [w3_sub_wy]
  simp only [dot, wu, Fin.sum_univ_one]
  norm_num

/-- `⟪-2·u⟫ = -2`: the dot sign that `(DF)` relies on. -/
theorem dot_wm2 : dot wu wm2 = -2 := by
  rw [wm2_eq]
  simp only [dot, wu, Fin.sum_univ_one]
  norm_num

/-! ## 4. The two comparisons, instantiated -/

/-- `(BC)` in the three-edge model. -/
theorem witness_BC :
    ex ww (Bfun wu wK0 wKy {wy}) = ex ww (Cfun wu wK0 wKy {wy}) :=
  ex_Bfun_eq_ex_Cfun (u := wu) (K := wK0) (Ky := wKy) (w := ww) {wy}
    (fun y hy => by
      rw [Finset.mem_singleton] at hy
      rw [hy]
      exact witness_PRefl)

/-- `(DF)` in the three-edge model. -/
theorem witness_DF :
    ex ww (Dfun wu wK0 wKy {wy}) = -ex ww (Ffun wu wK0 wKy {wy}) :=
  ex_Dfun_eq_neg_ex_Ffun (u := wu) (K := wK0) (Ky := wKy) (w := ww) {wy}
    (fun y hy => by
      rw [Finset.mem_singleton] at hy
      rw [hy]
      exact witness_PRefl)

/-- The collapse of `(I.5.3)` in the three-edge model. -/
theorem witness_collapse :
    ex ww (rawRusso wu wK0 wKy {wy}) = derivTerm ww wu wK0 wKy {wy} :=
  collapse_of_reflection (u := wu) (K := wK0) (Ky := wKy) (w := ww) {wy}
    (fun y hy => by
      rw [Finset.mem_singleton] at hy
      rw [hy]
      exact witness_PRefl)

end PercLib.CriticalLRP.I58

#print axioms PercLib.CriticalLRP.I58.wR_involutive
#print axioms PercLib.CriticalLRP.I58.witness_PRefl
#print axioms PercLib.CriticalLRP.I58.wcfg_nontrivial
#print axioms PercLib.CriticalLRP.I58.q_w3_sub
#print axioms PercLib.CriticalLRP.I58.witness_BC
#print axioms PercLib.CriticalLRP.I58.witness_DF
#print axioms PercLib.CriticalLRP.I58.witness_collapse
