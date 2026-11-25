module

public import PercLib.CriticalLRP.Analysis.Cutoff.Incident.ScalarWeight
public import PercLib.CriticalLRP.Analysis.Cutoff.Incident.Transport
public import PercLib.CriticalLRP.RussoInf.Degree

/-!
# The finite incident-ball estimate for the standardized cutoff weight

Direction (activity 4) of swarm `smwtzmkep`, member `m5`.

This file closes the numerical incident step: on a **finite** set `u` of edges whose cut-off kernel
is bounded below by `γ > 0`, the standardized weight `stdEdgeWeight r` has an explicit finite
per-vertex mass

  `vertexWeight (stdEdgeWeight r) x u ≤ #{e ∈ u : x ∈ e} · (-deriv K r)/γ`,

so the vertex-degree hypothesis `hdeg` of the mixed incident transport is discharged with
`D = B · (-deriv K r)/γ` whenever every vertex meets at most `B` edges of `u`.  The count
`B = (2⌈r⌉₊+1)^d` of `RussoInf/Degree.card_activeEdgesAt_le` is the instance for edges of
`‖·‖_∞`-length at most `r`.

Consequences: (i) the finite-`u` mixed transport with an explicit finite `D` and with the edge
open-probability premise discharged from `0 < γ ≤ J_r`; (ii) the matching finite-window flux bound.
The passage to the full edge `tsum` still needs a lower bound for `J_r` uniform over the *infinite*
incident edge set, which is not available (the kernel vanishes as the length approaches `r` from
below); this residual is recorded in the README and no flux-level `D_std` is claimed here.
-/

set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. Positivity of the open probability and the kernel lower bound -/

/-- A positive cut-off kernel makes the open-edge probability positive. -/
theorem openProb_pos_of_kernel_pos {r : ℝ} (e : Sym2 M.V) (hβ : 0 < (M.betaCrit : ℝ))
    (hJ : 0 < M.cutKernel r e) : 0 < M.openProb r e := by
  rw [openProb_eq]
  have hlt : Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  linarith

/-- The cutoff derivative weight is nonnegative when the kernel decreases. -/
theorem cutEdgeDeriv_nonneg {r : ℝ} (hK' : 0 ≤ -(deriv M.K r)) (e : Sym2 M.V) :
    0 ≤ M.cutEdgeDeriv r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutEdgeDeriv_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy]
      split
      · refine mul_nonneg (mul_nonneg ?_ hK') ?_
        · exact (by positivity : (0 : ℝ) ≤ (M.betaCrit : ℝ))
        · exact (Real.exp_pos _).le
      · exact le_rfl

/-- **The scalar weight bound with an explicit kernel floor.** -/
theorem stdEdgeWeight_le_div_of_kernel_ge {r γ : ℝ} (e : Sym2 M.V) (hγ : 0 < γ)
    (hJ : γ ≤ M.cutKernel r e) (hK' : 0 ≤ -(deriv M.K r)) :
    M.stdEdgeWeight r e ≤ (-(deriv M.K r)) / γ :=
  le_trans (M.stdEdgeWeight_le_div_cutKernel e (lt_of_lt_of_le hγ hJ) hK')
    (div_le_div_of_nonneg_left hK' hγ hJ)

/-! ## 2. The finite incident-ball mass bound -/

/-- **Finite incident mass with an explicit count.**  If every edge of the finite set `u` has kernel
at least `γ > 0`, then the standardized weight of the edges of `u` incident to `x` is at most
`#{e ∈ u : x ∈ e} · (-deriv K r)/γ`. -/
theorem vertexWeight_stdEdgeWeight_le_card {r γ : ℝ} (u : Finset (Sym2 M.V)) (x : M.V)
    (hγ : 0 < γ) (hK' : 0 ≤ -(deriv M.K r))
    (hJ : ∀ e ∈ u, γ ≤ M.cutKernel r e) :
    vertexWeight (M.stdEdgeWeight r) x u
      ≤ ((u.filter (fun e => x ∈ e)).card : ℝ) * ((-(deriv M.K r)) / γ) := by
  classical
  have hVW : vertexWeight (M.stdEdgeWeight r) x u
      = ∑ e ∈ u, M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0) := by
    rw [vertexWeight_eq_sum]
    exact Finset.sum_congr rfl fun e _ => by by_cases h : x ∈ e <;> simp [h]
  rw [hVW]
  have hterm : ∀ e ∈ u, M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0)
      ≤ ((-(deriv M.K r)) / γ) * (if x ∈ e then (1 : ℝ) else 0) := by
    intro e he
    by_cases hxe : x ∈ e
    · rw [ite_eq_left hxe, mul_one, mul_one]
      exact M.stdEdgeWeight_le_div_of_kernel_ge e hγ (hJ e he) hK'
    · rw [ite_eq_right hxe, mul_zero, mul_zero]
  calc ∑ e ∈ u, M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0)
      ≤ ∑ e ∈ u, ((-(deriv M.K r)) / γ) * (if x ∈ e then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hterm
    _ = ((-(deriv M.K r)) / γ) * ∑ e ∈ u, (if x ∈ e then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ = ((-(deriv M.K r)) / γ) * ((u.filter (fun e => x ∈ e)).card : ℝ) := by
        rw [Finset.card_filter]
        push_cast
        rfl
    _ = ((u.filter (fun e => x ∈ e)).card : ℝ) * ((-(deriv M.K r)) / γ) := by ring

/-- **The `(2⌈r⌉₊+1)^d` form of the incident mass bound**, using
`RussoInf/Degree.card_activeEdgesAt_le` for edges of `‖·‖_∞`-length at most `r`. -/
theorem vertexWeight_stdEdgeWeight_le_box {r γ : ℝ} (u : Finset (Sym2 M.V)) (x : M.V)
    (hγ : 0 < γ) (hK' : 0 ≤ -(deriv M.K r))
    (hJ : ∀ e ∈ u, γ ≤ M.cutKernel r e)
    (hlen : ∀ e ∈ u, x ∈ e → (PercLib.CriticalLRP.FiniteVolume.edgeLen e : ℝ) ≤ r) :
    vertexWeight (M.stdEdgeWeight r) x u
      ≤ ((2 * ⌈r⌉₊ + 1) ^ M.d : ℝ) * ((-(deriv M.K r)) / γ) := by
  classical
  refine le_trans (M.vertexWeight_stdEdgeWeight_le_card u x hγ hK' hJ) ?_
  have hfin := (PercLib.CriticalLRP.FiniteVolume.card_activeEdgesAt_le (d := M.d) x r).1
  have hle := (PercLib.CriticalLRP.FiniteVolume.card_activeEdgesAt_le (d := M.d) x r).2
  have hsub : (↑(u.filter (fun e => x ∈ e)) : Set (Sym2 (Fin M.d → ℤ)))
      ⊆ {e : Sym2 (Fin M.d → ℤ) |
          x ∈ e ∧ (PercLib.CriticalLRP.FiniteVolume.edgeLen e : ℝ) ≤ r} := by
    intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    exact ⟨he.2, hlen e he.1 he.2⟩
  have hcard : (u.filter (fun e => x ∈ e)).card ≤ (2 * ⌈r⌉₊ + 1) ^ M.d := by
    rw [← Set.ncard_coe_finset (u.filter (fun e => x ∈ e))]
    exact le_trans (Set.ncard_le_ncard hsub hfin) hle
  refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ?_
  exact div_nonneg hK' hγ.le

/-! ## 3. The finite-`u` transport with the incident degree bound discharged -/

/-- **Vertex-weight form of a finite edge sum** (concrete-context bridge to
`vertexWeight_eq_sum`). -/
theorem vertexWeight_congr_sum {w : Sym2 M.V → ℝ} (x : M.V) (s : Finset (Sym2 M.V)) :
    vertexWeight w x s = ∑ e ∈ s, w e * (if x ∈ e then (1 : ℝ) else 0) := by
  rw [PercLib.CriticalLRP.vertexWeight_eq_sum]
  exact Finset.sum_congr rfl fun e _ => by by_cases h : x ∈ e <;> simp [h]

/-- **Finite-`u` mixed transport with an explicit finite constant.**  On a finite edge set `u`
whose kernel is bounded below by `γ > 0`, with at most `B` edges of `u` incident to any vertex, the
edge sum of `stdEdgeWeight r` against the coupled events is at most `B · (-deriv K r)/γ` times the
mixed cluster density at the same radius.  No global degree hypothesis and no global positivity of
the open-edge probability is assumed. -/
theorem sum_stdEdgeWeight_mixed_le_fin {r : ℝ} (y : M.V) (u : Finset (Sym2 M.V)) {γ B : ℝ}
    (hγ : 0 < γ) (hK' : 0 ≤ -(deriv M.K r))
    (hJ : ∀ e ∈ u, γ ≤ M.cutKernel r e)
    (hcard : ∀ x : M.V, ((u.filter (fun e => x ∈ e)).card : ℝ) ≤ B)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    ∑ e ∈ u, M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e)
      ≤ B * ((-(deriv M.K r)) / γ) * M.mixedFluxDensity r y := by
  classical
  set w : Sym2 M.V → ℝ := fun e => M.stdEdgeWeight r e * (if e ∈ u then (1 : ℝ) else 0) with hwdef
  have hW0 : ∀ e, 0 ≤ M.stdEdgeWeight r e := by
    intro e
    by_cases hq : M.openProb r e = 0
    · rw [SourceModelData.stdEdgeWeight, hq, div_zero]
    · exact div_nonneg (M.cutEdgeDeriv_nonneg hK' e)
        (le_of_lt (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hq)))
  have hB : 0 ≤ B := by
    have h0 : (0 : ℝ) ≤ ((u.filter (fun e => (0 : M.V) ∈ e)).card : ℝ) := by positivity
    exact le_trans h0 (hcard 0)
  have hw0 : ∀ e, 0 ≤ w e := by
    intro e
    exact mul_nonneg (hW0 e) (by split <;> norm_num)
  have hwzero : ∀ e : Sym2 M.V, e ∉ u → w e = 0 := by
    intro e he
    change M.stdEdgeWeight r e * (if e ∈ u then (1 : ℝ) else 0) = 0
    rw [ite_eq_right he, mul_zero]
  have hwone : ∀ e : Sym2 M.V, e ∈ u → w e = M.stdEdgeWeight r e := by
    intro e he
    change M.stdEdgeWeight r e * (if e ∈ u then (1 : ℝ) else 0) = M.stdEdgeWeight r e
    rw [ite_eq_left he, mul_one]
  have hdeg : ∀ x : M.V, ∀ u' : Finset (Sym2 M.V),
      vertexWeight w x u' ≤ B * ((-(deriv M.K r)) / γ) := by
    intro x u'
    rw [M.vertexWeight_congr_sum]
    have hstep : ∑ e ∈ u', w e * (if x ∈ e then (1 : ℝ) else 0)
        = ∑ e ∈ u'.filter (fun e => e ∈ u),
            M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e ∈ u
      · rw [hwone e he, ite_eq_left he]
      · rw [hwzero e he, zero_mul, ite_eq_right he]
    rw [hstep]
    calc ∑ e ∈ u'.filter (fun e => e ∈ u),
          M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0)
        ≤ ∑ e ∈ u, M.stdEdgeWeight r e * (if x ∈ e then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (fun e he => (Finset.mem_filter.mp he).2) ?_
          intro e he _
          exact mul_nonneg (hW0 e) (by split <;> norm_num)
      _ = vertexWeight (M.stdEdgeWeight r) x u := (M.vertexWeight_congr_sum x u).symm
      _ ≤ ((u.filter (fun e => x ∈ e)).card : ℝ) * ((-(deriv M.K r)) / γ) :=
          M.vertexWeight_stdEdgeWeight_le_card u x hγ hK' hJ
      _ ≤ B * ((-(deriv M.K r)) / γ) :=
          mul_le_mul_of_nonneg_right (hcard x) (div_nonneg hK' hγ.le)
  have hD : 0 ≤ B * ((-(deriv M.K r)) / γ) := mul_nonneg hB (div_nonneg hK' hγ.le)
  have hmain := tsum_weight_mixed_touch_le (o := (0 : M.V)) (y := y) (M.cutLaw r) w
    hD hw0 hdeg hfin
  have hzero : ∀ e : Sym2 M.V, e ∉ u →
      w e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e) = 0 := by
    intro e he
    rw [hwzero e he, zero_mul]
  have htsum : ∑' e : Sym2 M.V, w e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e)
      = ∑ e ∈ u, M.stdEdgeWeight r e
          * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e) := by
    rw [tsum_eq_sum hzero]
    exact Finset.sum_congr rfl fun e he => by rw [hwone e he]
  rw [htsum] at hmain
  exact hmain

/-! ## 4. The matching finite-window flux bound -/

/-- **Finite-window flux bound with an explicit constant.**  Same hypotheses as the finite-`u`
transport; the sum of the absolute pivotal contributions of the edges of `u` is bounded by the same
explicit constant times the mixed cluster density. -/
theorem sum_abs_flux_le_fin {r : ℝ} (y : M.V) (u : Finset (Sym2 M.V)) {γ B : ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hγ : 0 < γ) (hK' : 0 ≤ -(deriv M.K r))
    (hJ : ∀ e ∈ u, γ ≤ M.cutKernel r e)
    (hcard : ∀ x : M.V, ((u.filter (fun e => x ∈ e)).card : ℝ) ≤ B)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    ∑ e ∈ u, |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
      ≤ B * ((-(deriv M.K r)) / γ) * M.mixedFluxDensity r y := by
  classical
  refine le_trans (Finset.sum_le_sum fun e he => ?_)
    (M.sum_stdEdgeWeight_mixed_le_fin y u hγ hK' hJ hcard hfin)
  have hpiv : 0 ≤ pivotalFlux (M.cutLaw r)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
    rw [pivotalFlux]
    exact integral_nonneg fun ω => flipDiff_sMomentTrunc_singleton_nonneg (M := M) y e ω
  rw [abs_mul, abs_of_nonneg (M.cutEdgeDeriv_nonneg hK' e), abs_of_nonneg hpiv]
  exact M.cutEdgeDeriv_mul_pivotalFlux_le (r := r) (y := y) (e := e)
    (M.cutEdgeDeriv_nonneg hK' e)
    (M.openProb_pos_of_kernel_pos e hβ (lt_of_lt_of_le hγ (hJ e he)))

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 5. The explicit finite kernel floor and the discharged incident constant -/

/-- The minimal cut-off kernel over a nonempty finite edge set: the explicit finite kernel floor
`J_r` used for the incident constant. -/
noncomputable def kernelFloor (r : ℝ) (u : Finset (Sym2 M.V)) (hu : u.Nonempty) : ℝ :=
  u.inf' hu (fun e => M.cutKernel r e)

theorem kernelFloor_le {r : ℝ} {u : Finset (Sym2 M.V)} (hu : u.Nonempty) {e : Sym2 M.V}
    (he : e ∈ u) : M.kernelFloor r u hu ≤ M.cutKernel r e :=
  Finset.inf'_le (fun e => M.cutKernel r e) he

theorem kernelFloor_pos {r : ℝ} {u : Finset (Sym2 M.V)} (hu : u.Nonempty)
    (h : ∀ e ∈ u, 0 < M.cutKernel r e) : 0 < M.kernelFloor r u hu :=
  (Finset.lt_inf'_iff hu).mpr h

/-- **The finite incident-ball transport with an explicit finite constant and no degree
hypothesis, no kernel-floor hypothesis.**  Given positivity of the kernel on the finite edge set `u`,
the edge sum of `stdEdgeWeight r` against the coupled events is at most
`B · (-deriv K r)/min_{e ∈ u} J_r(e)` times the mixed cluster density, where `B` bounds the number of
edges of `u` incident to any vertex. -/
theorem sum_stdEdgeWeight_mixed_le_kernelFloor {r : ℝ} (y : M.V) (u : Finset (Sym2 M.V))
    (hu : u.Nonempty) {B : ℝ} (hK' : 0 ≤ -(deriv M.K r))
    (hpos : ∀ e ∈ u, 0 < M.cutKernel r e)
    (hcard : ∀ x : M.V, ((u.filter (fun e => x ∈ e)).card : ℝ) ≤ B)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    ∑ e ∈ u, M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e)
      ≤ B * ((-(deriv M.K r)) / M.kernelFloor r u hu) * M.mixedFluxDensity r y :=
  M.sum_stdEdgeWeight_mixed_le_fin y u (M.kernelFloor_pos hu hpos) hK'
    (fun e he => M.kernelFloor_le (e := e) hu he) hcard hfin

/-- **The finite-window flux bound with the explicit finite constant `D_std(r,u)`.** -/
theorem sum_abs_flux_le_kernelFloor {r : ℝ} (y : M.V) (u : Finset (Sym2 M.V))
    (hu : u.Nonempty) {B : ℝ} (hβ : 0 < (M.betaCrit : ℝ)) (hK' : 0 ≤ -(deriv M.K r))
    (hpos : ∀ e ∈ u, 0 < M.cutKernel r e)
    (hcard : ∀ x : M.V, ((u.filter (fun e => x ∈ e)).card : ℝ) ≤ B)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    ∑ e ∈ u, |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
      ≤ B * ((-(deriv M.K r)) / M.kernelFloor r u hu) * M.mixedFluxDensity r y :=
  M.sum_abs_flux_le_fin y u hβ (M.kernelFloor_pos hu hpos) hK'
    (fun e he => M.kernelFloor_le (e := e) hu he) hcard hfin

/-- **The incident-ball constant in the `(2⌈r⌉₊+1)^d` form.**  For a finite set of edges of
`‖·‖_∞`-length at most `r`, `D_std(r,u) = (2⌈r⌉₊+1)^d · (-deriv K r)/min_{e∈u} J_r(e)` is a valid
finite per-vertex incident constant. -/
theorem sum_stdEdgeWeight_mixed_le_box {r : ℝ} (y : M.V) (u : Finset (Sym2 M.V))
    (hu : u.Nonempty) (hK' : 0 ≤ -(deriv M.K r))
    (hpos : ∀ e ∈ u, 0 < M.cutKernel r e)
    (hlen : ∀ e ∈ u, ∀ x : M.V, x ∈ e →
      (PercLib.CriticalLRP.FiniteVolume.edgeLen e : ℝ) ≤ r)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    ∑ e ∈ u, M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e)
      ≤ ((2 * ⌈r⌉₊ + 1) ^ M.d : ℝ)
        * ((-(deriv M.K r)) / M.kernelFloor r u hu) * M.mixedFluxDensity r y := by
  classical
  have hγ : 0 < M.kernelFloor r u hu := M.kernelFloor_pos hu hpos
  have hJ : ∀ e ∈ u, M.kernelFloor r u hu ≤ M.cutKernel r e :=
    fun e he => M.kernelFloor_le (e := e) hu he
  have hcardB : ∀ x : M.V, ((u.filter (fun e => x ∈ e)).card : ℝ)
      ≤ ((2 * ⌈r⌉₊ + 1) ^ M.d : ℝ) := by
    intro x
    have hfin' := (PercLib.CriticalLRP.FiniteVolume.card_activeEdgesAt_le (d := M.d) x r).1
    have hle := (PercLib.CriticalLRP.FiniteVolume.card_activeEdgesAt_le (d := M.d) x r).2
    have hsub : (↑(u.filter (fun e => x ∈ e)) : Set (Sym2 (Fin M.d → ℤ)))
        ⊆ {e : Sym2 (Fin M.d → ℤ) |
            x ∈ e ∧ (PercLib.CriticalLRP.FiniteVolume.edgeLen e : ℝ) ≤ r} := by
      intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      exact ⟨he.2, hlen e he.1 x he.2⟩
    have hc : (u.filter (fun e => x ∈ e)).card ≤ (2 * ⌈r⌉₊ + 1) ^ M.d := by
      rw [← Set.ncard_coe_finset (u.filter (fun e => x ∈ e))]
      exact le_trans (Set.ncard_le_ncard hsub hfin') hle
    exact_mod_cast hc
  exact M.sum_stdEdgeWeight_mixed_le_fin y u hγ hK' hJ hcardB hfin

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 6. Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openProb_pos_of_kernel_pos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.stdEdgeWeight_le_div_of_kernel_ge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.vertexWeight_stdEdgeWeight_le_card
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.vertexWeight_stdEdgeWeight_le_box
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.vertexWeight_congr_sum
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_stdEdgeWeight_mixed_le_fin
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_abs_flux_le_fin
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.kernelFloor_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.kernelFloor_pos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_stdEdgeWeight_mixed_le_kernelFloor
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_abs_flux_le_kernelFloor
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_stdEdgeWeight_mixed_le_box
