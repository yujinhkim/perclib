module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.Degree

/-!
# The off-corner per-`y` flux majorant

Swarm `smwu19308`, member `m1`.

The mixed incident transport `SourceModelData.abs_sMomentInfFlux_le_mixed` needs four inputs at the
radius under consideration: nonnegativity of the cutoff derivative weight, the *open-probability
compatibility* `openProb r e = 0 → cutEdgeDeriv r e = 0`, the per-vertex degree bound, and
finiteness of the mixed first moment.  This file discharges the first three, the degree bound
being `vertexWeight_stdEdgeWeight_le_stdDegree` (valid at every `r > 0`).

The compatibility condition is the only place where "off-corner" is used.  For a non-loop edge in
the range, `q_e(r) = 1 - exp(-β_c J_r(e))` and `c_r(e) = β_c(-K'(r)) exp(-β_c J_r(e))`, so:

* if `J_r(e) > 0` then `q_e(r) > 0` whenever `c_r(e) ≠ 0` (which forces `β_c > 0`);
* if `J_r(e) = 0` then `K` is flat on `[s, r]`, so by `deriv_eq_zero_of_flat_left` the derivative
  `K'(r)` vanishes and hence `c_r(e) = 0` as well.

No strict-decrease or tail hypothesis is needed: the flat case self-destructs.  What *is* needed is
that no edge of the support sits exactly at length `r`.  At an attained radius `r` the edge
`s(x, y)` with `S.dist x y = r` has `J_r(e) = 0` but `c_r(e) = β_c(-K'(r)) > 0`, so the
compatibility genuinely fails there — this is precisely why the statement is off-corner.

The remaining input — finiteness of the mixed moment `∫⁻ |K_0| 1{y ∈ K_0} ∂P_r` — is kept as an
explicit hypothesis; nothing here proves it.
-/

set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The open-probability compatibility off corner -/

/-- **A nonzero cutoff derivative weight forces a positive open probability**, at an off-corner
radius.  The two cases are a positive kernel gap (then `q_e > 0`) and a vanishing kernel gap (then
`K` is flat up to `r`, so `K'(r) = 0` and the weight itself vanishes). -/
theorem openProb_pos_of_cutEdgeDeriv_ne_zero {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) {e : Sym2 M.V} (hc : M.cutEdgeDeriv r e ≠ 0) :
    0 < M.openProb r e := by
  classical
  induction e using Sym2.ind with
  | h a b =>
    rw [M.cutEdgeDeriv_mk] at hc
    by_cases hab : a = b
    · rw [ite_eq_left hab] at hc
      exact absurd rfl hc
    · rw [ite_eq_right hab] at hc
      by_cases hd : M.S.dist a b ≤ r
      · rw [ite_eq_left hd] at hc
        have hspos : 0 < M.S.dist a b := M.S.dist_pos hab
        have hJeq : M.cutKernel r s(a, b) = M.K (M.S.dist a b) - M.K r := by
          rw [M.cutKernel_mk, ite_eq_right hab, FiniteVolume.cutoffProfile_of_le hd]
        have hJpos : 0 < M.cutKernel r s(a, b) := by
          rcases lt_trichotomy (M.cutKernel r s(a, b)) 0 with hneg | hzero | hpos
          · linarith [M.cutKernel_nonneg r s(a, b)]
          · -- vanishing gap: `K` is flat on `[s, r]`, hence `K'(r) = 0` and `c_r(e) = 0`
            exfalso
            have hne : M.S.dist a b ≠ r :=
              fun h => hoff (h ▸ M.S.mem_attainedRadii_of_dist hab)
            have hlt : M.S.dist a b < r := lt_of_le_of_ne hd hne
            have hKeq : M.K (M.S.dist a b) = M.K r := by
              have h := hJeq.symm.trans hzero
              linarith
            have hconst : ∀ u : ℝ, M.S.dist a b < u → u < r → M.K u = M.K r := by
              intro u hu1 hu2
              have hu1pos : 0 < u := lt_trans hspos hu1
              have h1 : M.K r ≤ M.K u :=
                M.K_antitone (Set.mem_Ioi.mpr hu1pos) (Set.mem_Ioi.mpr hr) hu2.le
              have h2 : M.K u ≤ M.K (M.S.dist a b) :=
                M.K_antitone (Set.mem_Ioi.mpr hspos) (Set.mem_Ioi.mpr hu1pos) hu1.le
              rw [hKeq] at h2
              linarith
            have hd0 : deriv M.K r = 0 :=
              M.deriv_eq_zero_of_flat_left (lo := M.S.dist a b) (r := r) hlt hr hconst
            apply hc
            rw [hd0]
            ring
          · exact hpos
        have hβne : (M.betaCrit : ℝ) ≠ 0 := by
          rintro h0
          apply hc
          rw [h0]
          ring
        have hβpos : 0 < (M.betaCrit : ℝ) :=
          lt_of_le_of_ne (by positivity) (Ne.symm hβne)
        have harg : -((M.betaCrit : ℝ) * M.cutKernel r s(a, b)) < 0 := by nlinarith
        have hexp : Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r s(a, b))) < 1 :=
          Real.exp_lt_one_iff.mpr harg
        rw [M.openProb_eq]
        linarith
      · rw [ite_eq_right hd] at hc
        exact absurd rfl hc

/-- **The open-probability compatibility** in the form consumed by the transport: at an off-corner
radius, a vanishing open probability forces a vanishing derivative weight. -/
theorem openProb_eq_zero_imp_cutEdgeDeriv_eq_zero {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) {e : Sym2 M.V} (hq : M.openProb r e = 0) :
    M.cutEdgeDeriv r e = 0 := by
  by_contra hc
  have hpos := M.openProb_pos_of_cutEdgeDeriv_ne_zero hr hoff hc
  rw [hq] at hpos
  exact lt_irrefl 0 hpos

/-! ## 2. The per-`y` flux majorant -/

/-- **The off-corner per-`y` flux majorant.**  At any positive off-corner radius the flux of the
singleton two-point moment `1{y ∈ K_0}` is at most the explicit finite constant `stdDegree r`
times the mixed cluster density at that radius.  The only remaining hypothesis is finiteness of
the mixed first moment. -/
theorem abs_sMomentInfFlux_le_stdDegree_mixed {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (y : M.V)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    |sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
      ≤ M.stdDegree r * M.mixedFluxDensity r y :=
  M.abs_sMomentInfFlux_le_mixed (r := r) y (D := M.stdDegree r)
    (M.stdDegree_nonneg hr)
    (fun e => M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e)
    (fun _ hq => M.openProb_eq_zero_imp_cutEdgeDeriv_eq_zero hr hoff hq)
    (fun x u => M.vertexWeight_stdEdgeWeight_le_stdDegree hr x u)
    hfin

end SourceModelData

end PercLib.CriticalLRP.Orchestration
