module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RightExcludedMass.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusExcludedMass
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusSummedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusTailDeriv

/-!
# The right corner derivative past the tail threshold, and the exact shell discrepancy

Direction B6 of swarm `smwv6er9k`.

## What is proved here

* `vertexExhaustion` / `edgeExhaustion` — canonical finite exhaustions of the vertex set and of the
  edge set (needed by the landed off-corner theorems, which take `T` and `S` as parameters).
* `exists_tail_hasDerivWithinAt_cutMassReal_rhsScalar_Ici` — **for every radius beyond the source
  tail threshold, the cutoff mass has a right derivative at that radius, equal to the closed-window
  value `β_c(-K'(r₀)) (exclMass r₀).toReal`**.  This is the corner-free statement: at an attained
  radius it is the true right corner derivative, and off the corner set it agrees with the landed
  two-sided derivative.  The right window on which the landed off-corner theorem is applied is cut
  out by the finite set of attained radii in `(r₀, r₂)`, using
  `exists_ballF_eq_of_right`.  Remaining explicit inputs: per-vertex singleton-flux continuity on
  the window, continuity of `r ↦ K'(r)` on `[r₀, r₂]`, finiteness of the second and third cutoff
  moments at `r₂`, and `r₂ > r₀`.
* `exclMassShell_eq_exclMass_sub_strict` and
  `rhsScalar_sub_coeffRHS_mul_exclScalarStrict` — the right-hand value is the strict-window value
  plus exactly `coeffRHS r · (exclMassShell r).toReal`.  This answers the non-cancellation
  question in the precise form available: the closed/strict discrepancy is *exactly* the shell
  mass, so nothing else can cancel it; the two values differ whenever the shell mass is nonzero and
  `coeffRHS r ≠ 0`.
* `not_hasDerivAt_of_left_le_strictScalar` — consequently, if the left one-sided derivative at an
  attained radius is bounded by the strict-window value while the closed-window value is strictly
  larger, the two-sided derivative does not exist.  The bound is an explicit hypothesis: the
  left-hand limit itself is not claimed here.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. Canonical exhaustions -/

theorem monotone_vertexExhaustion : Monotone M.vertexExhaustion := fun n m hnm =>
  M.ballF_mono (by exact_mod_cast hnm)

theorem exists_mem_vertexExhaustion (y : M.V) : ∃ n, y ∈ M.vertexExhaustion n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (M.S.ρ (toVec y))
  exact ⟨n, (E1Sign.mem_ballF M).mpr hn⟩

theorem monotone_edgeExhaustion : Monotone M.edgeExhaustion := by
  intro n m hnm e he
  rw [edgeExhaustion, Finset.mem_sym2_iff] at he ⊢
  exact fun a ha => M.monotone_vertexExhaustion hnm (he a ha)

theorem exists_mem_edgeExhaustion (e : Sym2 M.V) : ∃ n, e ∈ M.edgeExhaustion n := by
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨n, hnx⟩ := M.exists_mem_vertexExhaustion x
    obtain ⟨m, hmy⟩ := M.exists_mem_vertexExhaustion y
    refine ⟨max n m, ?_⟩
    rw [edgeExhaustion, Finset.mk_mem_sym2_iff]
    exact ⟨M.monotone_vertexExhaustion (le_max_left n m) hnx,
      M.monotone_vertexExhaustion (le_max_right n m) hmy⟩

/-! ## 2. Right derivative past the tail threshold -/

/-- **The right corner derivative of the cutoff mass past the tail threshold.**

There is a threshold `R > 0` (the one of `SourceModelData.exists_deriv_bounds`) such that for every
`r₀ > R` and every `r₂ > r₀`, with finite second and third cutoff moments at `r₂`, continuity of
`r ↦ K'(r)` on `[r₀, r₂]` and per-vertex singleton-flux continuity on `(r₀, r₂)`,

`M.cutMassReal` has right derivative `M.rhsScalar r₀ = β_c(-K'(r₀)) (exclMass r₀).toReal` at `r₀`.

No condition on the sphere `{ρ = r₀}` is imposed, so this covers attained radii. -/
theorem exists_tail_hasDerivWithinAt_cutMassReal_rhsScalar_Ici :
    ∃ R : ℝ, 0 < R ∧ ∀ {r0 r2 : ℝ}, R < r0 → 0 < r0 → r0 < r2 →
      M.cutMoment 2 r2 ≠ ⊤ → M.cutMoment 3 r2 ≠ ⊤ →
      (∀ r ∈ Set.Icc r0 r2, ContinuousAt (fun r' => deriv M.K r') r) →
      (∀ y : M.V, ∀ r ∈ Set.Ioo r0 r2, ContinuousAt
        (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv) r) →
      HasDerivWithinAt M.cutMassReal (M.rhsScalar r0) (Set.Ici r0) r0 := by
  obtain ⟨R, hRpos, -, hlow, hupp⟩ := M.exists_deriv_bounds
  refine ⟨R, hRpos, ?_⟩
  intro r0 r2 hRr0 hr0 hr0r2 h2 h3 hK' hcontinf
  obtain ⟨δ, hδ, hwin⟩ := M.exists_ballF_eq_of_right hr0r2
  set r1 : ℝ := min (r0 + δ / 2) r2 with hr1def
  have hr0r1 : r0 < r1 := lt_min (by linarith) hr0r2
  have hr1le : r1 ≤ r0 + δ / 2 := by rw [hr1def]; exact min_le_left _ _
  have hr1r2 : r1 ≤ r2 := by rw [hr1def]; exact min_le_right _ _
  have hoff : ∀ r ∈ Set.Ioo r0 r1, r ∉ M.cornerRadii := by
    intro ρ hρ
    rw [← M.attainedRadii_eq_cornerRadii]
    rintro ⟨y, hy0, hyd⟩
    have hs1 : ρ < (ρ + r1) / 2 := by linarith [hρ.2]
    have hs2 : (ρ + r1) / 2 < r1 := by linarith [hρ.2]
    have hsδ : (ρ + r1) / 2 < r0 + δ := by linarith [hs2, hr1le, hδ]
    have hball := hwin ((ρ + r1) / 2) ⟨lt_trans hρ.1 hs1, hsδ⟩
    have hyρ : M.S.ρ (toVec y) = ρ := by
      rw [← SourceNormData.dist_zero_right, hyd]
    have hmem : y ∈ E1Sign.ballF M ((ρ + r1) / 2) :=
      (E1Sign.mem_ballF M).mpr (show M.S.ρ (toVec y) ≤ (ρ + r1) / 2 by
        rw [hyρ]; exact hs1.le)
    rw [hball] at hmem
    have hle : M.S.ρ (toVec y) ≤ r0 := (E1Sign.mem_ballF M).mp hmem
    rw [hyρ] at hle
    linarith [hρ.1]
  have h2r1 : M.cutMoment 2 r1 ≠ ⊤ := M.cutMoment_ne_top_of_le hr1r2 2 h2
  have h3r1 : M.cutMoment 3 r1 ≠ ⊤ := M.cutMoment_ne_top_of_le hr1r2 3 h3
  have hdiff : ∀ ρ ∈ Set.Ioo r0 r1, HasDerivAt M.cutMassReal (M.rhsScalar ρ) ρ := by
    intro ρ hρ
    have hKwin : ∀ r ∈ Set.Ioo r0 r1, ContinuousAt (fun r' => deriv M.K r') r :=
      fun r hr => hK' r ⟨le_of_lt hr.1, le_trans hr.2.le hr1r2⟩
    have hex : ∀ r ∈ Set.Ioo r0 r1, ContinuousAt M.exclScalar r :=
      fun r hr => M.continuousAt_exclScalar (lt_trans hr0 hr.1)
        (M.noSphere_of_cornerRadii (lt_trans hr0 hr.1) (hoff r hr)) hr.2 h2r1 h3r1
    have hGcont := M.hGcont_of_scalar_continuity hr0 h2r1 hoff hKwin hex
    exact M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail M.vertexExhaustion
      M.monotone_vertexExhaustion M.exists_mem_vertexExhaustion M.edgeExhaustion
      M.monotone_edgeExhaustion M.exists_mem_edgeExhaustion hRpos hRr0 hlow hupp hρ.1 hρ.2
      hoff h2r1 (fun y r hr => hcontinf y r ⟨hr.1, lt_of_lt_of_le hr.2 hr1r2⟩) hGcont
  have hfin : M.cutMassAt r1 0 ≠ ⊤ :=
    ne_top_of_le_ne_top h2r1 (E1Sign.cutMassAt_le_cutMoment_two M r1)
  exact M.hasDerivWithinAt_cutMassReal_rhsScalar_Ici hr0 hr0r1 h2r1 h3r1
    (hK' r0 ⟨le_rfl, le_trans hr0r1.le hr1r2⟩) hdiff hfin

/-! ## 3. The exact closed/strict discrepancy at one radius -/

/-- The shell mass is the difference of the closed-window and strict-window excluded masses. -/
theorem exclMassShell_eq_exclMass_sub_strict (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.exclMassShell r
      = E1Sign.exclMass M r - M.exclMassStrict r := by
  have hstrict : M.exclMassStrict r ≠ ⊤ := M.exclMassStrict_ne_top le_rfl h2
  have h := M.exclMass_eq_exclMassStrict_add_exclMassShell r
  rw [h, ENNReal.add_sub_cancel_left hstrict]

/-- **The exact discrepancy between the right-hand (closed-window) derivative value and the
strict-window value is the shell mass.**  Nothing cancels: the difference of the two scalars is
`β_c(-K'(r)) · (exclMassShell r).toReal`. -/
theorem rhsScalar_sub_coeffRHS_mul_exclScalarStrict (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.rhsScalar r - M.coeffRHS r * M.exclScalarStrict r
      = M.coeffRHS r * (M.exclMassShell r).toReal := by
  have hstrict : M.exclMassStrict r ≠ ⊤ := M.exclMassStrict_ne_top le_rfl h2
  have hclosed : E1Sign.exclMass M r ≠ ⊤ := M.exclMass_ne_top_of_le le_rfl h2
  have hshell : M.exclMassShell r ≠ ⊤ := by
    rw [M.exclMassShell_eq_exclMass_sub_strict r h2]
    exact ENNReal.sub_ne_top hclosed
  have hdecomp : M.exclScalar r
      = (M.exclMassStrict r).toReal + (M.exclMassShell r).toReal := by
    rw [exclScalar, M.exclMass_eq_exclMassStrict_add_exclMassShell r,
      ENNReal.toReal_add hstrict hshell]
  rw [rhsScalar, hdecomp, exclScalarStrict]
  ring

/-- **Non-cancellation.**  At a radius where the shell mass is nonzero and the coefficient
`β_c(-K'(r))` is nonzero, the closed-window derivative value differs from the strict-window one. -/
theorem rhsScalar_ne_coeffRHS_mul_exclScalarStrict_of_shell_ne_zero {r : ℝ}
    (h2 : M.cutMoment 2 r ≠ ⊤) (hshell : M.exclMassShell r ≠ 0)
    (hcoeff : M.coeffRHS r ≠ 0) :
    M.rhsScalar r ≠ M.coeffRHS r * M.exclScalarStrict r := by
  have hclosed : E1Sign.exclMass M r ≠ ⊤ := M.exclMass_ne_top_of_le le_rfl h2
  have hshelltop : M.exclMassShell r ≠ ⊤ := by
    rw [M.exclMassShell_eq_exclMass_sub_strict r h2]
    exact ENNReal.sub_ne_top hclosed
  intro heq
  have hdiff := M.rhsScalar_sub_coeffRHS_mul_exclScalarStrict r h2
  rw [heq, sub_self] at hdiff
  have hzero : (M.exclMassShell r).toReal = 0 := by
    rcases mul_eq_zero.mp hdiff.symm with h | h
    · exact absurd h hcoeff
    · exact h
  exact hshell ((ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right hshelltop)

/-! ## 4. The non-differentiability corollary -/

/-- **A strict-window left derivative rules out two-sided differentiability at a corner.**

If the cutoff mass has a right derivative `rhsScalar r₀` at `r₀` (from the off-corner family on
one right window) and a left one-sided derivative `L` at most the strict-window value
`coeffRHS r₀ * exclScalarStrict r₀`, and that value is strictly smaller than `rhsScalar r₀`, then
no two-sided derivative exists at `r₀`.

`hL` is the explicit left-hand input: it is not proved here (the left-hand limit is a separate
direction).  What is proved is that the right-hand side cannot be reconciled with it. -/
theorem not_hasDerivAt_of_left_le_strictScalar {r0 r1 L : ℝ} (hr0 : 0 < r0) (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤)
    (hK : ContinuousAt (fun r => deriv M.K r) r0)
    (hdiff : ∀ r ∈ Set.Ioo r0 r1, HasDerivAt M.cutMassReal (M.rhsScalar r) r)
    (hfin : M.cutMassAt r1 0 ≠ ⊤)
    (hL : HasDerivWithinAt M.cutMassReal L (Set.Iic r0) r0)
    (hLbound : L ≤ M.coeffRHS r0 * M.exclScalarStrict r0)
    (hgap : M.coeffRHS r0 * M.exclScalarStrict r0 < M.rhsScalar r0) :
    ¬ ∃ L', HasDerivAt M.cutMassReal L' r0 := by
  rintro ⟨L', hL'⟩
  have hright := M.hasDerivWithinAt_cutMassReal_rhsScalar_Ici hr0 hr1 h2 h3 hK hdiff hfin
  have e1 : derivWithin M.cutMassReal (Set.Ici r0) r0 = M.rhsScalar r0 :=
    hright.derivWithin (uniqueDiffWithinAt_Ici r0)
  have e2 : derivWithin M.cutMassReal (Set.Ici r0) r0 = L' :=
    hL'.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici r0)
  have e3 : derivWithin M.cutMassReal (Set.Iic r0) r0 = L :=
    hL.derivWithin (uniqueDiffWithinAt_Iic r0)
  have e4 : derivWithin M.cutMassReal (Set.Iic r0) r0 = L' :=
    hL'.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic r0)
  have hval : M.rhsScalar r0 = L := by rw [← e1, ← e3]; rw [e2, e4]
  linarith

/-- The same non-differentiability from the shell nonvanishing, with the strict-window gap
produced by `rhsScalar_sub_coeffRHS_mul_exclScalarStrict`. -/
theorem not_hasDerivAt_of_left_le_strictScalar_of_shell {r0 r1 L : ℝ} (hr0 : 0 < r0)
    (hr1 : r0 < r1) (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤)
    (h2r0 : M.cutMoment 2 r0 ≠ ⊤)
    (hK : ContinuousAt (fun r => deriv M.K r) r0)
    (hdiff : ∀ r ∈ Set.Ioo r0 r1, HasDerivAt M.cutMassReal (M.rhsScalar r) r)
    (hfin : M.cutMassAt r1 0 ≠ ⊤)
    (hL : HasDerivWithinAt M.cutMassReal L (Set.Iic r0) r0)
    (hLbound : L ≤ M.coeffRHS r0 * M.exclScalarStrict r0)
    (hshell : M.exclMassShell r0 ≠ 0) (hcoeffpos : 0 < M.coeffRHS r0) :
    ¬ ∃ L', HasDerivAt M.cutMassReal L' r0 := by
  have hclosed : E1Sign.exclMass M r0 ≠ ⊤ := M.exclMass_ne_top_of_le le_rfl h2r0
  have hshelltop : M.exclMassShell r0 ≠ ⊤ := by
    rw [M.exclMassShell_eq_exclMass_sub_strict r0 h2r0]
    exact ENNReal.sub_ne_top hclosed
  have hpos : 0 < (M.exclMassShell r0).toReal :=
    ENNReal.toReal_pos hshell hshelltop
  have hdiffeq := M.rhsScalar_sub_coeffRHS_mul_exclScalarStrict r0 h2r0
  have hgap : M.coeffRHS r0 * M.exclScalarStrict r0 < M.rhsScalar r0 := by
    have h2' : 0 < M.coeffRHS r0 * (M.exclMassShell r0).toReal := mul_pos hcoeffpos hpos
    linarith
  exact M.not_hasDerivAt_of_left_le_strictScalar hr0 hr1 h2 h3 hK hdiff hfin hL hLbound hgap

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.vertexExhaustion

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.monotone_vertexExhaustion

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_mem_vertexExhaustion

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.edgeExhaustion

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.monotone_edgeExhaustion

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_mem_edgeExhaustion

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tail_hasDerivWithinAt_cutMassReal_rhsScalar_Ici

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassShell_eq_exclMass_sub_strict

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.rhsScalar_sub_coeffRHS_mul_exclScalarStrict

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.rhsScalar_ne_coeffRHS_mul_exclScalarStrict_of_shell_ne_zero

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_hasDerivAt_of_left_le_strictScalar

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_hasDerivAt_of_left_le_strictScalar_of_shell

end PercLib.CriticalLRP.Orchestration
