/-
Independently rebuilt and integrated from the accepted `smwx5p94b/m3` artifact.
Prepared at base `5e579c30ee2c5caa2d151372f1929efd8ed587fb`;
production integration revision `9be3dd2832bf4fe01e33a70c2c3192ab4c837d88`.
Definitions are solely in the sibling `Defs.lean`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Q3Cover.Defs

/-!
# The spine–hub family: BK evaluation, and a fresh configuration no fork covers

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof.

## Positive result: the spine–hub diagram

`spineHubEvent_measure_le` is the five-fold van den Berg–Kesten bound for the five
requirements of `Q3.spineHubReq`; `fresh_spineHub_le` sums the three labelled arms
out and keeps the marked arm `y` as its own factor, giving the **five-factor**
monomial `τ(w,a) τ(w,y) χ(a)³`; `fresh_spineHub_le_bound` absorbs it in the summed
diagram `Q3.spineHubBound`.

## Negative result: the fan is not a fork configuration

`fan_not_forkEvent`: on the five-edge fan `fanE` (mark `0`, hub `1` carrying the
three arms `2, 3, 4`, and the marked arm `5` adjacent to the mark), for **every**
choice of the two fork hubs `a`, `b` the six fork requirements

`0 ↔ a`, `a ↔ 2`, `a ↔ 3`, `0 ↔ b`, `b ↔ 4`, `b ↔ 5`

have no pairwise edge-disjoint witnesses inside `fanE`. The proof is the cut count
of `I417/Fresh/Obstruction`: a witness for a connection separated by one of the five
cuts of the fan contains that cut's distinguished edge, so pairwise disjointness
makes each of the five cuts serve at most one of the six requirements
(`fanSep_le_five`), while the separation count of the six requirements is always at
least six (`fanSep_ge_six`).

Consequently the fork family of `I417/Fresh/Fork` is *not* a cover of the `q = 3`
fresh hub event (`fan_not_forkEvent`), even though it does cover the double star on
which the chain family fails. The two obstructions are complementary, and the
spine–hub family is non-vacuous on the fan (`fan_spineHubEvent`), with five factors
against the chain family's eight.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

namespace Q3

variable {V : Type*} [Countable V]

/-! ## The spine–hub event: increasing, finitely witnessed, and BK-bounded -/

theorem isUpperSet_spineHubReq (w a y : V) (g : Fin 3 → V) (i : Fin 5) :
    IsUpperSet (spineHubReq w a y g i) := by
  fin_cases i
  · exact isUpper_connSet w a
  · exact isUpper_connSet w y
  · exact isUpper_connSet a (g 0)
  · exact isUpper_connSet a (g 1)
  · exact isUpper_connSet a (g 2)

theorem finiteWitness_spineHubReq (w a y : V) (g : Fin 3 → V) (i : Fin 5) :
    Percolation.FiniteWitness (spineHubReq w a y g i) := by
  fin_cases i
  · exact finiteWitness_connSet w a
  · exact finiteWitness_connSet w y
  · exact finiteWitness_connSet a (g 0)
  · exact finiteWitness_connSet a (g 1)
  · exact finiteWitness_connSet a (g 2)

/-- **The spine–hub event carries its five-point monomial.** -/
theorem spineHubEvent_measure_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (w a y : V) (g : Fin 3 → V) :
    (edgeMeasure π) (spineHubEvent w a y g) ≤ spineHubMono π w a y g := by
  have h := I417Example.bk_fin_ennreal π hπ (spineHubReq w a y g)
    (isUpperSet_spineHubReq w a y g) (finiteWitness_spineHubReq w a y g)
  have hprod : (∏ i : Fin 5, (edgeMeasure π) (spineHubReq w a y g i)) =
      spineHubMono π w a y g := by
    rw [Fin.prod_univ_five]
    simp only [spineHubReq, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [spineHubMono, tau, mul_assoc]
  rw [hprod] at h
  exact h

/-- **The `q = 3` fresh arm sum at one hub, with the mark on the spine.**  All three
labelled arms are summed out (`hubArmSum`) and the marked arm `y` is retained as its
own factor, giving the five-factor monomial
`τ(w,a) · τ(w,y) · χ(a)³`. -/
theorem fresh_spineHub_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w a : V) :
    (∑' g : Fin 3 → V, (edgeMeasure π) (spineHubEvent w a y g)) ≤
      tau π w a * tau π w y * hubArmSum π a * hubArmSum π a * hubArmSum π a := by
  have h1 : ∀ g : Fin 3 → V,
      (edgeMeasure π) (spineHubEvent w a y g) ≤ spineHubMono π w a y g :=
    fun g => spineHubEvent_measure_le π hπ w a y g
  refine le_trans (ENNReal.tsum_le_tsum h1) ?_
  have hfac : (∑' g : Fin 3 → V, spineHubMono π w a y g) =
      (tau π w a * tau π w y) * (∑' g : Fin 3 → V,
        tau π a (g 0) * tau π a (g 1) * tau π a (g 2)) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun g => by simp only [spineHubMono]; ring
  rw [hfac, tsum_fin3_mul]
  simp only [hubArmSum]
  exact le_of_eq (by ring)

/-- The spine–hub arm sum absorbed in the summed diagram. -/
theorem fresh_spineHub_le_bound (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w a : V) :
    (∑' g : Fin 3 → V, (edgeMeasure π) (spineHubEvent w a y g)) ≤
      spineHubBound π y w := by
  refine le_trans (fresh_spineHub_le π hπ y w a) ?_
  rw [spineHubBound_eq]
  exact ENNReal.le_tsum (f := fun a : V =>
    tau π w a * tau π w y * hubArmSum π a * hubArmSum π a * hubArmSum π a) a

/-! ## The fan -/

theorem fanCutEdge_mem (c : Fin 5) : fanCutEdge c ∈ fanE := by
  fin_cases c <;> decide

/-- **The cut edge is unique**: an edge of the fan whose endpoints lie on different
sides of one of the five cuts is that cut's distinguished edge. -/
theorem fan_cut_unique : ∀ (c : Fin 5) (x y : FV), x ≠ y → s(x, y) ∈ fanE →
    fanSide c x ≠ fanSide c y → s(x, y) = fanCutEdge c := by
  decide

/-- A walk whose endpoints lie on different sides of a cut uses an edge whose
endpoints lie on different sides. -/
theorem fan_walk_has_sep_edge {g : FV → Bool} {a b : FV}
    (p : (⊤ : SimpleGraph FV).Walk a b) (h : g a ≠ g b) :
    ∃ x y : FV, x ≠ y ∧ s(x, y) ∈ p.edges ∧ g x ≠ g y := by
  induction p with
  | nil => exact absurd rfl h
  | cons hadj p' ih =>
      rename_i u v w
      by_cases hgv : g u = g v
      · obtain ⟨x, y, hxy, hmem, hdiff⟩ := ih (by rw [← hgv]; exact h)
        exact ⟨x, y, hxy, List.mem_cons_of_mem _ hmem, hdiff⟩
      · exact ⟨u, v, (SimpleGraph.top_adj u v).1 hadj, by simp, hgv⟩

/-- **Any witness for a connection separated by a fan cut contains that cut's
edge.** -/
theorem fan_cut_mem_of_connects (c : Fin 5) {W : Finset (Sym2 FV)} {a b : FV}
    (hW : (W : Set (Sym2 FV)) ⊆ (fanE : Set (Sym2 FV)))
    (hc : Connects (W : Config FV) a b) (h : fanSide c a ≠ fanSide c b) :
    fanCutEdge c ∈ W := by
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr hc
  obtain ⟨x, y, hxy, hmem, hdiff⟩ := fan_walk_has_sep_edge p h
  have hEW : s(x, y) ∈ W := hp _ hmem
  have hEd : s(x, y) ∈ fanE := hW hEW
  rw [fan_cut_unique c x y hxy hEd hdiff] at hEW
  exact hEW

/-- A single open edge of the fan connects its endpoints. -/
theorem fan_mem_connSet_of_single {a b : FV} (hne : a ≠ b) {W : Finset (Sym2 FV)}
    (h : s(a, b) ∈ W) : (W : Set (Sym2 FV)) ∈ connSet a b := by
  refine pathConnects_iff.mp ?_
  refine ⟨SimpleGraph.Walk.cons ((SimpleGraph.top_adj a b).2 hne) SimpleGraph.Walk.nil, ?_⟩
  intro e he
  have h' : e = s(a, b) := by simpa using he
  rw [h']
  exact h

/-- Membership of the fan in any connection event, with no distinctness side
condition: coinciding endpoints connect trivially. -/
theorem fan_conn (a b : FV) (h : s(a, b) ∈ fanE) : (fanE : Set (Sym2 FV)) ∈ connSet a b := by
  rcases eq_or_ne a b with rfl | hne
  · exact connects_refl (fanE : Config FV) a
  · exact fan_mem_connSet_of_single hne h

/-- **The six fork requirements always have total cut separation at least six** on
the fan, for every choice of the two hubs.  This is the finite check of the
obstruction; each of the `6 · 6` hub choices is evaluated cut by cut. -/
theorem fanSep_ge_six : ∀ a b : FV, 6 ≤ fanSep a b ![2, 3] ![4, 5] := by
  decide

/-- Each of the five fan cuts serves at most one of the six fork requirements of a
family of pairwise edge-disjoint witnesses. -/
theorem fanSep_le_five {a b : FV} (W : Fin 6 → Finset (Sym2 FV))
    (hsub : ∀ i, (W i : Set (Sym2 FV)) ⊆ (fanE : Set (Sym2 FV)))
    (hpair : ∀ i : Fin 6, Connects (W i : Config FV)
      (fanPair a b ![2, 3] ![4, 5] i).1 (fanPair a b ![2, 3] ![4, 5] i).2)
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j)) :
    fanSep a b ![2, 3] ![4, 5] ≤ 5 := by
  have hmemCut : ∀ (c : Fin 5) (i : Fin 6),
      fanSide c (fanPair a b ![2, 3] ![4, 5] i).1 ≠
        fanSide c (fanPair a b ![2, 3] ![4, 5] i).2 → fanCutEdge c ∈ W i :=
    fun c i hs => fan_cut_mem_of_connects c (hsub i) (hpair i) hs
  have hcount : ∀ c : Fin 5, fanCnt c a b ![2, 3] ![4, 5] ≤ 1 := by
    intro c
    have hcard : fanCnt c a b ![2, 3] ![4, 5] =
        (Finset.univ.filter (fun i : Fin 6 =>
          fanSide c (fanPair a b ![2, 3] ![4, 5] i).1 ≠
            fanSide c (fanPair a b ![2, 3] ![4, 5] i).2)).card := by
      rw [fanCnt, Finset.card_filter]
    rw [hcard, Finset.card_le_one]
    intro i hi j hj
    by_contra hij
    exact Finset.disjoint_left.mp (hdisj i j hij) (hmemCut c i (Finset.mem_filter.mp hi).2)
      (hmemCut c j (Finset.mem_filter.mp hj).2)
  have h0 := hcount 0
  have h1 := hcount 1
  have h2 := hcount 2
  have h3 := hcount 3
  have h4 := hcount 4
  simp only [fanSep, Fin.sum_univ_five]
  omega

/-- **No fork event holds on the fully open fan**, for any choice of the two hubs,
with the arms `2, 3` at the first hub and the arm `4` and the marked arm `5` at the
second.  Hence the two-hub fork family is not a cover of the `q = 3` fresh side. -/
theorem fan_not_forkEvent (a b : FV) :
    ¬ ((fanE : Config FV) ∈ forkEvent fanW a b ![2, 3] ![4, 5]) := by
  intro h
  simp only [forkEvent, Percolation.DisjointOccurrenceFin, Set.mem_ofPred_eq] at h
  obtain ⟨W, hsub, hmem, hdisj⟩ := h
  have hpair : ∀ i : Fin 6, Connects (W i : Config FV)
      (fanPair a b ![2, 3] ![4, 5] i).1 (fanPair a b ![2, 3] ![4, 5] i).2 := by
    intro i
    have h := hmem i
    fin_cases i <;> simpa [forkReq, fanPair, fanW, connSet] using h
  have hfive := fanSep_le_five (a := a) (b := b) W hsub hpair hdisj
  have hsix := fanSep_ge_six a b
  omega

/-! ## The fan is a fresh configuration the spine–hub family covers -/

theorem fanSpineHubW_sub : ∀ i : Fin 5,
    (fanSpineHubW i : Set (Sym2 FV)) ⊆ (fanE : Set (Sym2 FV)) := by
  intro i
  refine Finset.coe_subset.mpr ?_
  fin_cases i <;> decide

theorem fanSpineHubW_mem : ∀ i : Fin 5,
    (fanSpineHubW i : Set (Sym2 FV)) ∈ spineHubReq fanW fanHub fanY fanArm i := by
  intro i
  fin_cases i <;>
    exact fan_mem_connSet_of_single (by decide) (by simp [fanSpineHubW, fanW, fanHub, fanY,
      fanArm])

theorem fanSpineHubW_disj : ∀ i j : Fin 5, i ≠ j →
    Disjoint (fanSpineHubW i) (fanSpineHubW j) := by
  decide

/-- **The spine–hub event holds on the fully open fan.** -/
theorem fan_spineHubEvent :
    (fanE : Config FV) ∈ spineHubEvent fanW fanHub fanY fanArm :=
  ⟨fanSpineHubW, fanSpineHubW_sub, fanSpineHubW_mem, fanSpineHubW_disj⟩

/-- The mark is joined to each fresh arm of the fan through the hub. -/
theorem fan_conn_arm (j : Fin 3) :
    (fanE : Set (Sym2 FV)) ∈ connSet fanW (fanArm j) := by
  have h1 : Connects (fanE : Config FV) fanW fanHub :=
    fan_mem_connSet_of_single (by decide) (by simp [fanE, fanW, fanHub])
  have h2 : Connects (fanE : Config FV) fanHub (fanArm j) := by
    fin_cases j
    · exact fan_mem_connSet_of_single (by decide) (by simp [fanE, fanHub, fanArm])
    · exact fan_mem_connSet_of_single (by decide) (by simp [fanE, fanHub, fanArm])
    · exact fan_mem_connSet_of_single (by decide) (by simp [fanE, fanHub, fanArm])
  exact connects_trans h1 h2

/-- **The fresh hub event holds on the fully open fan**: the mark `0` is joined to
the marked arm `5` and to the three arms `2, 3, 4` through the hub `1`. -/
theorem fan_hubEvent : (fanE : Config FV) ∈ hubStar fanY fanW fanArm := by
  constructor
  · exact fan_conn _ _ (by simp [fanE, fanW, fanY])
  · simp only [armStar, Set.mem_iInter]
    exact fan_conn_arm

/-- **The fan separates the spine–hub family from the fork family.**  The `q = 3`
fresh hub event holds, the spine–hub event holds with its five single-edge
witnesses, and every fork event with any two hubs fails.  Combined with
`I417.Fresh.Fork.q3_doubleStar_fork_not_chain` (the double star admits a fork and no
chain spider), no single one of the chain, fork and spine–hub families covers the
`q = 3` fresh event on its own. -/
theorem fan_spineHub_vs_fork :
    (fanE : Config FV) ∈ hubStar fanY fanW fanArm ∧
      (fanE : Config FV) ∈ spineHubEvent fanW fanHub fanY fanArm ∧
      (∀ a b : FV, ¬ ((fanE : Config FV) ∈ forkEvent fanW a b ![2, 3] ![4, 5])) :=
  ⟨fan_hubEvent, fan_spineHubEvent, fan_not_forkEvent⟩

end Q3

end PercLib.CriticalLRP.I417Fresh
