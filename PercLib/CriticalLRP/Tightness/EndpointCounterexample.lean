/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Theorem 2.3 as printed (`k ≥ 0`) is false: the `k = 0` counterexample

Reference: T. Hutchcroft, *Power-law bounds for critical long-range percolation below the
upper-critical dimension*, arXiv:2008.11197v2, Theorem 2.3.

The source prints (2.8) and (2.9) for `λ ≥ 1` and `k ≥ 0`, while its proof (Lemma 2.4, (2.10),
(2.11)) only produces them for `k ≥ 1`.  This file shows that the printed range is genuinely too
wide: **both** displays fail already at `k = 0` in the smallest non-trivial instance.

The instance (`V = Bool`, one edge, `Λ = V`, `λ = 2`, `k = 0`, edge probability `1/2`): the two
events `{|K_max(Λ)| ≥ 2}` and `{|K_u ∩ Λ| ≥ 2}` both hold exactly when the single edge is open, so
both probabilities equal `1/2`.  At `k = 0` the displays read

    (2.8):  1/2 ≤ (1/2)^(4/3)          -- false, since (1/2)^(4/3) < 1/2
    (2.9):  1/2 ≤ (1/2)^(1/3) · (1/2)  -- false, since (1/2)^(1/3) < 1

The exponents `4/3` and `1/3` are the real values of `3^(k-1)+1` and `3^(k-1)` at `k = 0`; the
same two numbers are obtained from a *faithful* reading of the printed superscripts.  (Encoding
`3^(k-1)` with `Nat` subtraction would instead give `2` and `1`; both of those are false here too,
see `Display28NatSub`/`Display29NatSub`, so the defect is not an artefact of the encoding either
way — but the real exponents are the printed ones.)

Underlying cause, isolated abstractly: at `k = 0` the displays are *inclusions of an event in a
higher power of its own probability*, which can only hold in degenerate cases; `display29_zero_iff`
and `display28_zero_iff` below make this precise, so no choice of graph can repair the endpoint.
-/
module

public import PercLib.CriticalLRP.Tightness.MaxClusterPower
public import PercLib.CriticalLRP.Tightness.EndpointDomain

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP.Percolation MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

/-! ### General facts about `Conn` and about subsets of a one-point type -/

section General

variable {V : Type*} {E : Type*} {G : BondGraph V E} {ω : Set E} {x y : V}

/-- If `x` and `y` are connected by open edges and `x ≠ y`, then some edge is open.  (Pure
`ReflTransGen` bookkeeping; the last step of a non-trivial connecting chain is an open edge.) -/
theorem conn_nonempty (h : Conn G ω x y) : x = y ∨ ω.Nonempty := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
    obtain ⟨e, he, -⟩ := hstep
    exact Or.inr ⟨e, he⟩

/-- A subset of the one-point type `Unit` that contains the point is everything. -/
theorem set_unit_eq_univ {σ : Set Unit} (h : () ∈ σ) : σ = Set.univ := by
  ext e
  exact ⟨fun _ => trivial, fun _ => by rwa [Subsingleton.elim e ()]⟩

theorem set_unit_mem_iff {σ : Set Unit} : () ∈ σ ↔ σ = Set.univ :=
  ⟨set_unit_eq_univ, fun h => h ▸ trivial⟩

end General

/-! ### The one-edge graph on two vertices -/

/-- The graph with vertex set `Bool` and a single edge joining the two vertices. -/
def oneEdgeGraph : BondGraph Bool Unit := fun _ => s(false, true)

/-- The single edge carries probability `1/2`. -/
noncomputable def pHalf : Unit → unitInterval := fun _ => ⟨1 / 2, by norm_num⟩

/-- The window: both vertices. -/
def fullWindow : Finset Bool := Finset.univ

theorem pHalf_coe : (pHalf () : ℝ) = 1 / 2 := rfl

/-- In the one-edge graph, a configuration connects *every* pair of vertices as soon as the unique
edge is open. -/
theorem conn_oneEdge_of_mem (ω : Set Unit) (hω : () ∈ ω) (x y : Bool) :
    Conn oneEdgeGraph ω x y := by
  rcases eq_or_ne x y with rfl | hne
  · exact conn_refl oneEdgeGraph ω x
  · refine Relation.ReflTransGen.single ⟨(), hω, ?_⟩
    -- `s(false, true) = s(x, y)` for distinct `x y : Bool`
    show s(false, true) = s(x, y)
    rcases x with _ | _ <;> rcases y with _ | _ <;> simp_all [Sym2.eq_swap]

/-- If a cluster of the one-edge graph contains two vertices of the window, then the edge is
open. -/
theorem oneEdge_open_of_maxMeets {ω : Set Unit} (h : ω ∈ MaxMeets oneEdgeGraph fullWindow 2) :
    () ∈ ω := by
  obtain ⟨t, ht, hcard, u, hconn⟩ := mem_MaxMeets oneEdgeGraph fullWindow 2 |>.mp h
  have hsub : t ⊆ (Finset.univ : Finset Bool) := fun y _ => Finset.mem_univ y
  have hcard2 : t.card = 2 := le_antisymm (by simpa using Finset.card_le_card hsub) hcard
  have htuniv : t = Finset.univ := Finset.eq_univ_of_card t (by simpa using hcard2)
  -- the vertex `!u` lies in `t`, and it is different from `u`
  have hmem : Bool.not u ∈ t := htuniv ▸ Finset.mem_univ _
  have hne : u ≠ Bool.not u := by cases u <;> simp
  rcases conn_nonempty (hconn _ hmem) with h | h
  · exact absurd h hne
  · obtain ⟨e, he⟩ := h
    rwa [Subsingleton.elim e ()] at he

/-- `{|K_max(Λ)| ≥ 2}` in the one-edge graph is exactly "the edge is open". -/
theorem maxMeets_oneEdge : MaxMeets oneEdgeGraph fullWindow 2 = {ω : Set Unit | () ∈ ω} := by
  ext ω
  constructor
  · exact oneEdge_open_of_maxMeets
  · intro hω
    refine mem_MaxMeets oneEdgeGraph fullWindow 2 |>.mpr
      ⟨Finset.univ, fun _ _ => Finset.mem_univ _, by simp, false, fun y _ => ?_⟩
    exact conn_oneEdge_of_mem ω hω false y

/-- `{|K_u ∩ Λ| ≥ 2}` in the one-edge graph is exactly "the edge is open", for **every** `u`. -/
theorem pointedMeets_oneEdge (u : Bool) :
    PointedMeets oneEdgeGraph fullWindow u 2 = {ω : Set Unit | () ∈ ω} := by
  ext ω
  constructor
  · intro h
    obtain ⟨t, ht, hcard, hconn⟩ := mem_PointedMeets.mp h
    -- reuse the maximum-size argument: the pointed event sits inside `MaxMeets`
    exact oneEdge_open_of_maxMeets (pointedMeets_subset_maxMeets _ _ _ _ h)
  · intro hω
    refine mem_PointedMeets.mpr
      ⟨Finset.univ, fun _ _ => Finset.mem_univ _, by simp, fun y _ => ?_⟩
    exact conn_oneEdge_of_mem ω hω u y

/-- The law of the open edge: probability `1/2`. -/
theorem real_measure_open : (edgeLaw pHalf).real {ω : Set Unit | () ∈ ω} = 1 / 2 := by
  have hset : {ω : Set Unit | () ∈ ω} = ({Set.univ} : Set (Set Unit)) := by
    ext σ
    simpa using set_unit_mem_iff (σ := σ)
  rw [hset, edgeLaw_real_singleton]
  simp [pHalf]

theorem real_measure_maxMeets : (edgeLaw pHalf).real (MaxMeets oneEdgeGraph fullWindow 2) = 1 / 2 := by
  rw [maxMeets_oneEdge, real_measure_open]

theorem real_measure_pointedMeets (u : Bool) :
    (edgeLaw pHalf).real (PointedMeets oneEdgeGraph fullWindow u 2) = 1 / 2 := by
  rw [pointedMeets_oneEdge, real_measure_open]

/-! ### The two displays fail at `k = 0` -/

/-- **(2.8) fails at `k = 0`**: `1/2 ≤ (1/2)^(4/3)` is false. -/
theorem not_display28_zero : ¬ Display28 oneEdgeGraph fullWindow 0 2 pHalf := by
  intro h
  rw [Display28, threeExpSucc_zero, show 3 ^ 0 * 2 = 2 by norm_num,
    real_measure_maxMeets] at h
  have hlt : (1 / 2 : ℝ) ^ ((4 : ℝ) / 3) < (1 / 2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by norm_num)
  rw [Real.rpow_one] at hlt
  linarith

/-- **(2.9) fails at `k = 0`**: `1/2 ≤ (1/2)^(1/3) · 1/2` is false. -/
theorem not_display29_zero (u : Bool) : ¬ Display29 oneEdgeGraph fullWindow 0 2 u pHalf := by
  intro h
  rw [Display29, threeExp_zero, show 3 ^ 0 * 2 = 2 by norm_num, real_measure_maxMeets,
    real_measure_pointedMeets] at h
  have h1 : (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  nlinarith

/-- **Theorem 2.3 as printed (with `k ≥ 0`) is false for (2.8).** -/
theorem not_theorem28Printed : ¬ Theorem28Printed oneEdgeGraph pHalf :=
  fun h => not_display28_zero (h fullWindow Finset.univ_nonempty 0 2 (by norm_num))

/-- **Theorem 2.3 as printed (with `k ≥ 0`) is false for (2.9).** -/
theorem not_theorem29Printed : ¬ Theorem29Printed oneEdgeGraph pHalf :=
  fun h => not_display29_zero false (h fullWindow Finset.univ_nonempty false 0 2 (by norm_num))

/-! ### The same two failures for the `Nat`-subtraction encoding

Not needed for the refutation — recorded only to document that the printed `k ≥ 0` range is false
whichever way the (non-natural at `k = 0`) exponent is read, so that the refutation cannot be
attributed to the encoding.  At `k ≥ 1` the two readings agree (`threeExpSucc_eq_natCast`,
`threeExp_eq_natCast`). -/

/-- The `Nat`-subtraction encoding of (2.8): exponent `3^(k-1)+1 : ℕ`. -/
def Display28NatSub (G : BondGraph Bool Unit) (Λ : Finset Bool) (k lam : ℕ)
    (p : Unit → unitInterval) : Prop :=
  (edgeLaw p).real (MaxMeets G Λ (3 ^ k * lam)) ≤
    (edgeLaw p).real (MaxMeets G Λ lam) ^ ((3 ^ (k - 1) + 1 : ℕ) : ℝ)

/-- The `Nat`-subtraction encoding of (2.9): exponent `3^(k-1) : ℕ`. -/
def Display29NatSub (G : BondGraph Bool Unit) (Λ : Finset Bool) (k lam : ℕ) (u : Bool)
    (p : Unit → unitInterval) : Prop :=
  (edgeLaw p).real (PointedMeets G Λ u (3 ^ k * lam)) ≤
    (edgeLaw p).real (MaxMeets G Λ lam) ^ ((3 ^ (k - 1) : ℕ) : ℝ) *
      (edgeLaw p).real (PointedMeets G Λ u lam)

theorem not_display28NatSub_zero : ¬ Display28NatSub oneEdgeGraph fullWindow 0 2 pHalf := by
  intro h
  rw [Display28NatSub, show 3 ^ 0 * 2 = 2 by norm_num, real_measure_maxMeets] at h
  norm_num at h

theorem not_display29NatSub_zero (u : Bool) :
    ¬ Display29NatSub oneEdgeGraph fullWindow 0 2 u pHalf := by
  intro h
  rw [Display29NatSub, show 3 ^ 0 * 2 = 2 by norm_num, real_measure_maxMeets,
    real_measure_pointedMeets] at h
  norm_num at h

end Hutchcroft
