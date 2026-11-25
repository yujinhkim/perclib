module
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusPivotalWeight
public import PercLib.CriticalLRP.MomentMonotonicity.StrictCutoffEpsilon

/-!
# Tail derivative comparison for the off-corner cutoff mass

Swarm `smwuinbxz`, member `m4`, direction (D).

`SourceModelData.exists_deriv_bounds` supplies `R > 0` with

  `(1/2) s ^ (-d-α-1) ≤ |K' s| ≤ 2 s ^ (-d-α-1)`   for `s > R`.

The off-axis exponent `-d-α-1` is *negative*, so `s ↦ s ^ (-d-α-1)` is antitone on `(0,∞)`
(`Real.rpow_le_rpow_of_nonpos`).  Hence on a window `a' ≤ s` with `a' > R` the slope `-K'` is
squeezed between two constants:

  `(1/2) b' ^ (-d-α-1) ≤ -K' r ≤ 2 a' ^ (-d-α-1)`   for `a' ≤ r ≤ b'`, `R < a'`,

using `0 ≤ -K'` (`deriv_K_nonpos`) to replace `|K'|` by `-K'`.  The lower tail bound, again with
`-K' ≥ 0`, also gives `K' ρ < 0` for every `ρ > R`.  No continuity of `deriv K` is used anywhere:
both bounds are pointwise consequences of the two-sided power-law envelope.

Consequently the three slope premises `hC0`, `hCb`, `hKβ` that
`hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope` (RadiusPivotalWeight.lean) still takes
as inputs are *derived* here from `exists_deriv_bounds`, and the differentiability hypothesis
`hKd` is derived from `K_diff`; what survives of the window data is `R < α`.  The result
`hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail` therefore has, as its only geometric
off-corner inputs, `R < α < r0 < β`, the off-corner condition `hoff`, the finite second cutoff
moment `h2β` at `β`, and the two flux-continuity hypotheses `hcontinf`, `hGcont`, which are kept
verbatim (they are *not* derived here).

## What is not claimed

* `h2β : M.cutMoment 2 β ≠ ⊤` stays an explicit input; nothing here produces a large-radius
  moment, and no finiteness is inferred from a vanishing defect or from `bool`/`toReal` junk.
* `hcontinf` and `hGcont` are unchanged premises.  This file proves no continuity of the
  infinite-volume singleton flux or of its sum; in particular the fixed-edge jump
  `cutEdgeDeriv_at_dist` is untouched.
* The bound `2 a' ^ (-d-α-1)` is *not* uniform in `a' ↓ 0`: because the exponent is negative the
  constant tends to `+∞`.  So this argument gives nothing on a window reaching down to the origin,
  and the hypothesis `R < α` (window starting past the tail threshold of `exists_deriv_bounds`) is
  what buys the bound; whether some other argument bounds `-K'` on a window touching `0` is not
  addressed here.  Within the tail the constant *is* uniform: `2 a' ^ p ≤ 2 R' ^ p` for
  `R < R' ≤ a'`, by the same antitonicity of the negative power.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-- The off-axis exponent `-d-α-1` of the source power law is nonpositive. -/
theorem tail_rpow_exponent_nonpos : -(M.d : ℝ) - M.α - 1 ≤ 0 := by
  have h1 : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
  linarith [M.hα]

/-- **Nonvanishing of the source slope past the tail threshold.**  The lower half of the
power-law envelope, `(1/2) ρ ^ (-d-α-1) ≤ |K' ρ|`, forces `K' ρ ≠ 0`; antitonicity of `K`
(`K' ≤ 0`) then upgrades this to `K' ρ < 0`.  No continuity of `K'` is used. -/
theorem deriv_K_neg_of_tail {R ρ : ℝ} (hRpos : 0 < R) (hRρ : R < ρ)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|) :
    deriv M.K ρ < 0 := by
  have hρ0 : 0 < ρ := lt_trans hRpos hRρ
  have hpow : 0 < ρ ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hρ0 _
  have hlowρ := hlow ρ hRρ
  have habs : 0 < |deriv M.K ρ| := by nlinarith
  have hnonpos : deriv M.K ρ ≤ 0 := M.deriv_K_nonpos hρ0
  rw [abs_of_nonpos hnonpos] at habs
  linarith

/-- **Constant upper bound for `-K'` on a tail window.**  For `R < a' ≤ r` the upper half of the
power-law envelope is combined with antitonicity of the *negative* power `s ↦ s ^ (-d-α-1)`:
`-K' r ≤ |K' r| ≤ 2 r ^ (-d-α-1) ≤ 2 a' ^ (-d-α-1)`.  This is the hypothesis `hCb` of the
envelope theorems in `RadiusEnvelope`/`RadiusPivotalWeight`, with the explicit constant
`2 a' ^ (-d-α-1)`. -/
theorem neg_deriv_K_le_of_tail {R a' r : ℝ} (hRpos : 0 < R) (hRa' : R < a') (ha'r : a' ≤ r)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1)) :
    -(deriv M.K r) ≤ 2 * a' ^ (-(M.d : ℝ) - M.α - 1) := by
  have ha'0 : 0 < a' := lt_trans hRpos hRa'
  have hr0 : 0 < r := lt_of_lt_of_le ha'0 ha'r
  have hmono : r ^ (-(M.d : ℝ) - M.α - 1) ≤ a' ^ (-(M.d : ℝ) - M.α - 1) :=
    Real.rpow_le_rpow_of_nonpos ha'0 ha'r M.tail_rpow_exponent_nonpos
  have huppr := hupp r (lt_of_lt_of_le hRa' ha'r)
  have hnonpos : deriv M.K r ≤ 0 := M.deriv_K_nonpos hr0
  rw [abs_of_nonpos hnonpos] at huppr
  linarith

/-- **Two-sided constant sandwich for `-K'` on a tail window.**  For `R < a'` and
`r ∈ [a', b']` the slope is bounded above and below by constants that depend only on `a'`, `b'`
and the tail exponent, with no continuity hypothesis on `deriv K`.  (The window condition
`a' ≤ b'` is not needed separately: it is implied by `r ∈ [a', b']`.) -/
theorem neg_deriv_K_window_sandwich {R a' b' : ℝ} (hRpos : 0 < R) (hRa' : R < a')
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    {r : ℝ} (hr : r ∈ Set.Icc a' b') :
    (1 / 2) * b' ^ (-(M.d : ℝ) - M.α - 1) ≤ -(deriv M.K r) ∧
      -(deriv M.K r) ≤ 2 * a' ^ (-(M.d : ℝ) - M.α - 1) := by
  have ha'0 : 0 < a' := lt_trans hRpos hRa'
  have hr0 : 0 < r := lt_of_lt_of_le ha'0 hr.1
  have hRr : R < r := lt_of_lt_of_le hRa' hr.1
  have hmono : b' ^ (-(M.d : ℝ) - M.α - 1) ≤ r ^ (-(M.d : ℝ) - M.α - 1) :=
    Real.rpow_le_rpow_of_nonpos hr0 hr.2 M.tail_rpow_exponent_nonpos
  have hnonpos : deriv M.K r ≤ 0 := M.deriv_K_nonpos hr0
  have hlowr : (1 / 2) * r ^ (-(M.d : ℝ) - M.α - 1) ≤ -(deriv M.K r) := by
    have h := hlow r hRr
    rw [abs_of_nonpos hnonpos] at h
    linarith
  exact ⟨by linarith, M.neg_deriv_K_le_of_tail hRpos hRa' hr.1 hupp⟩

/-- **Compact-window interval integrability of the total pivotal weight from the tail envelope.**
The dominating data `hCb`, `hC0` and `hKρ` of `intervalIntegrable_pivotalWeight_of_envelope` are
discharged by the tail bounds with `C = 2 a' ^ (-d-α-1)`, so the only inputs beyond the window
`R < a' ≤ b' ≤ ρ` are positivity of `ρ` and the finite first cutoff moment there. -/
theorem intervalIntegrable_pivotalWeight_of_tail {R a' b' ρ : ℝ}
    (hRpos : 0 < R) (hRa' : R < a') (ha'b' : a' ≤ b') (hb'ρ : b' ≤ ρ)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤) (y : M.V) :
    IntervalIntegrable (fun r => sMomentWeight (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a' b' := by
  have ha'0 : 0 < a' := lt_trans hRpos hRa'
  have hC0 : 0 ≤ 2 * a' ^ (-(M.d : ℝ) - M.α - 1) := by
    have h : 0 < a' ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos ha'0 _
    linarith
  have hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ 2 * a' ^ (-(M.d : ℝ) - M.α - 1) :=
    fun r hr => M.neg_deriv_K_le_of_tail hRpos hRa' hr.1 hupp
  have hKρ : deriv M.K ρ < 0 :=
    M.deriv_K_neg_of_tail hRpos (lt_of_lt_of_le (lt_of_lt_of_le hRa' ha'b') hb'ρ) hlow
  exact M.intervalIntegrable_pivotalWeight_of_envelope ha'0 ha'b' hb'ρ hCb hC0 hKρ hρ hvol y

/-- **The `hboundint` premise on an off-corner window, discharged from the tail envelope.**
This is the exact shape of the `hboundint` hypothesis of
`hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability`: for every `y` and every pair
`a', b'` in the window `Ioo α β`, starting the window past the tail threshold `R < α` and with a
finite second cutoff moment at `β`, the singleton pivotal weight is interval integrable.  Both
orderings of `a'`, `b'` are covered. -/
theorem intervalIntegrable_pivotalWeight_of_tail_window {R α β : ℝ}
    (hRpos : 0 < R) (hRα : R < α)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2β : M.cutMoment 2 β ≠ ⊤) (y : M.V) {a' b' : ℝ}
    (ha' : a' ∈ Set.Ioo α β) (hb' : b' ∈ Set.Ioo α β) :
    IntervalIntegrable (fun r => sMomentWeight (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a' b' := by
  have hα0 : 0 < α := lt_trans hRpos hRα
  have h1β : M.cutMoment 1 β ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2β
  rcases le_total a' b' with hab | hba
  · exact M.intervalIntegrable_pivotalWeight_of_tail (a' := a') (b' := b') (ρ := β)
      hRpos (lt_trans hRα ha'.1) hab hb'.2.le hlow hupp
      (lt_trans hα0 (lt_trans hb'.1 hb'.2)) h1β y
  · exact (M.intervalIntegrable_pivotalWeight_of_tail (a' := b') (b' := a') (ρ := β)
      hRpos (lt_trans hRα hb'.1) hba ha'.2.le hlow hupp
      (lt_trans hα0 (lt_trans ha'.1 ha'.2)) h1β y).symm

/-- **The endpoint off-corner derivative with every slope hypothesis supplied by the tail
envelope.**  Compared with `hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope`, the inputs
`C`, `hC0`, `hCb`, `hKβ` and `hKd` are gone: they are derived from the two halves of
`exists_deriv_bounds` at `R` and from `K_diff`, using `R < α`.  What remains is the off-corner
window `α < r0 < β` past the tail threshold, the off-corner condition, the finite second cutoff
moment at `β`, and the two flux-continuity hypotheses `hcontinf`, `hGcont` — which are *not*
reduced here. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {R α β r0 : ℝ} (hRpos : 0 < R) (hRα : R < α)
    (hlow : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (hupp : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hGcont : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 := by
  have hα0 : 0 < α := lt_trans hRpos hRα
  have hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r := fun r hr =>
    M.K_diff.differentiableAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (lt_trans hα0 hr.1)))
  refine M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope T hTmono hT S hSmono hS
    hα0 hαr0 hr0β hoff hKd h2β (C := 2 * α ^ (-(M.d : ℝ) - M.α - 1)) ?_ ?_ ?_ hcontinf hGcont
  · have h : 0 < α ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hα0 _
    linarith
  · exact fun r hr => M.neg_deriv_K_le_of_tail hRpos hRα hr.1.le hupp
  · exact M.deriv_K_neg_of_tail hRpos (lt_trans hRα (lt_trans hαr0 hr0β)) hlow

/-- **Tail-threshold form of the endpoint derivative.**  The tail threshold `R` itself is
produced by `SourceModelData.exists_deriv_bounds`, so the window hypothesis is exactly `R < α`:
every off-corner window starting past the source power law's tail threshold carries the derivative
`β_c (-K' r0) (exclMass r0)` of the cutoff mass.  `hcontinf`, `hGcont` and `h2β` are unchanged
inputs. -/
theorem exists_tail_hasDerivAt_cutMassReal_rhsScalar
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n) :
    ∃ R : ℝ, 0 < R ∧ ∀ {α β r0 : ℝ}, R < α → α < r0 → r0 < β →
      (∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii) →
      M.cutMoment 2 β ≠ ⊤ →
      (∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
        (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r) →
      (∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r) →
      HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 := by
  obtain ⟨R, hRpos, -, hlow, hupp⟩ := M.exists_deriv_bounds
  exact ⟨R, hRpos, fun hRα hαr0 hr0β hoff h2β hcontinf hGcont =>
    M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail T hTmono hT S hSmono hS
      hRpos hRα hlow hupp hαr0 hr0β hoff h2β hcontinf hGcont⟩

end PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP.Orchestration.SourceModelData

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tail_rpow_exponent_nonpos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.deriv_K_neg_of_tail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.neg_deriv_K_le_of_tail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.neg_deriv_K_window_sandwich
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_pivotalWeight_of_tail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_pivotalWeight_of_tail_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tail_hasDerivAt_cutMassReal_rhsScalar
