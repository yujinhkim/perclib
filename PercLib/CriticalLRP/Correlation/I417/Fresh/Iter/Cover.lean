/-
Independently rebuilt and integrated from the accepted `smwx9itnu/m2` artifact
`.ultramath/smwx9itnu/m2/Gen`. Production integration revision:
`8ae938fa49a73456688d438f25ef2441c282b2f4`.
The base split/diagram API is shared with `I417FreshFour.Refined` instead of
being duplicated.
-/
/-
Independently built for swarm `smwx9itnu`, member `m2`, direction GENERAL-Q-VECTOR-COVER.
No production files are modified; this module is read-only against production.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Iter.Attach

/-!
# Lemma I.4.17 for arbitrary `q ≥ 2`: the iterated first-hit fresh cover

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.17, supplied paper text lines 2444--2513: the fresh side of
the two-copy expansion is a family of tree diagrams with the pin `y` at the root and the `q`
labelled arms as leaves, with `2q` edges (the marked side carries `2p + 1`).

This file proves the deterministic cover for **arbitrary `q`** by induction on the number `n` of
attachment rounds (`n = q - 1`):

* `exists_iter_diag` — the induction.  Given the two edge-disjoint open halves
  `P : y → w`, `R : w → g j` of the marked path and any ordered list `a : Fin n → Fin q` of
  `n` arms distinct from `j`, together with `Connects ω y (g (a t))` for every `t`, there is an
  attachment history `H : Hist V n` whose `t`-th arm is exactly `g (a t)`, whose `2 * (n+1)` legs
  have a pairwise edge-disjoint witnessed diagram, and whose first leg still starts at the pin
  `y`.
* `freshMark_subset_genShape` — the cover at `n = q - 1`: for every arm tuple `g`, every selected
  arm `j`, and every enumeration `e : Fin (q-1) ≃ {i : Fin q // i ≠ j}` of the other arms, the
  fresh marked event is contained in the `q`-family `genShape y w g j e`.

The induction step is exactly the accepted `q = 4` first-hit step: obtain an open walk from the
next arm to `y`, first-hit the *whole* current diagram (`exists_first_hit`, using that `y` is in
its support), and split the hit leg (`step`).  The pin invariant `Hist.first_leg_start` supplies
`y ∈ support` at every round, so no round is special.

No definitions are introduced here.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417GenIter

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- The last arm of an extended history. -/
theorem Hist.arm_snoc_last {n : ℕ} (H : Hist V n) (k : Idx n) (z d : V) :
    (Hist.snoc H k z d).arm (Fin.last n) = d := by
  simp [Hist.arm]

/-- The earlier arms of an extended history. -/
theorem Hist.arm_snoc_castSucc {n : ℕ} (H : Hist V n) (k : Idx n) (z d : V) (t : Fin n) :
    (Hist.snoc H k z d).arm (Fin.castSucc t) = H.arm t := by
  simp [Hist.arm]

/-- **The iterated first-hit induction.**  For every `n`, every ordered list `a : Fin n → Fin q`
of arms avoiding the selected label `j`, and every configuration in which all those arms are
connected to `y`, the two halves of the marked path extend to an `n`-round attachment history:

* the `t`-th attached arm is `g (a t)`;
* the first leg of the resulting `2 * (n + 1)`-leg diagram still starts at `y`
  (so `y` lies in the diagram support and the next first hit can terminate there);
* the resulting legs carry pairwise edge-disjoint open path witnesses.

The base `n = 0` is the two-leg diagram of the disjoint occurrence; the step is the inside-segment
attachment `step` after a first hit `exists_first_hit`. -/
theorem exists_iter_diag {q : ℕ} (g : Fin q → V) (j : Fin q) :
    ∀ (n : ℕ) (a : Fin n → Fin q), (∀ t, a t ≠ j) →
      ∀ {ω : Config V} {y w : V} {P : (⊤ : SimpleGraph V).Walk y w}
        {R : (⊤ : SimpleGraph V).Walk w (g j)},
        P.IsPath → R.IsPath → (∀ e ∈ P.edges, e ∈ ω) → (∀ e ∈ R.edges, e ∈ ω) →
        Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset R.edges) →
        (∀ t : Fin n, Connects ω y (g (a t))) →
        ∃ H : Hist V n, (∀ t : Fin n, H.arm t = g (a t)) ∧
          (H.legs y w (g j) (first n)).1 = y ∧
          Nonempty (Diag (Idx n) ω (H.legs y w (g j))) := by
  intro n
  induction n with
  | zero =>
    intro a _ha ω y w P R hPpath hRpath hPop hRop hPR _hcon
    refine ⟨Hist.nil, ?_, ?_, ?_⟩
    · intro t
      exact Fin.elim0 t
    · rfl
    · exact ⟨baseDiag hPpath hRpath hPop hRop hPR⟩
  | succ n ih =>
    intro a ha ω y w P R hPpath hRpath hPop hRop hPR hcon
    -- the induction hypothesis for the first `n` arms
    obtain ⟨H, harm, hfirst, ⟨D⟩⟩ :=
      ih (fun t : Fin n => a t.castSucc) (fun t => ha t.castSucc)
        hPpath hRpath hPop hRop hPR (fun t => hcon t.castSucc)
    -- the next arm
    set d : V := g (a (Fin.last n)) with hd
    have hnext : Connects ω y d := hcon (Fin.last n)
    -- an open walk from the next arm to `y`
    obtain ⟨r, hr⟩ := pathConnects_iff.mpr (connects_symm hnext)
    -- first hit the whole current diagram
    have hyS : y ∈ ⋃ i, {v : V | v ∈ (D.W i).2.support} := by
      refine Set.mem_iUnion.mpr ⟨first n, ?_⟩
      have h1 : (D.W (first n)).1.1 = y := by
        rw [D.legs_eq (first n)]
        exact hfirst
      exact mem_support_start (D.W (first n)).2 h1
    obtain ⟨z, Q, _hzS, hQop, hQsupp⟩ :=
      exists_first_hit r hr (⋃ i, {v : V | v ∈ (D.W i).2.support}) hyS
    have hQreg : ∀ e ∈ Q.edges, ∀ v ∈ e,
        v ∈ ({z} ∪ (⋃ i, {v : V | v ∈ (D.W i).2.support})ᶜ) := by
      intro e he v hv
      rcases hQsupp v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e, he, hv⟩)) with h | h
      · exact Or.inl h
      · exact Or.inr h
    -- split the hit leg and attach the arm
    obtain ⟨k, ⟨D'⟩⟩ := step D _hzS Q hQop hQreg
    refine ⟨Hist.snoc H k z d, ?_, ?_, ?_⟩
    · -- the arms of the extended history
      intro t
      refine Fin.lastCases ?_ ?_ t
      · exact (Hist.arm_snoc_last H k z d).trans hd
      · intro t'
        exact (Hist.arm_snoc_castSucc H k z d t').trans (harm t')
    · -- the pin invariant is preserved
      change ((splitAt (H.legs y w (g j)) k z d) (Sum.inl (first n))).1 = y
      exact splitAt_left hfirst k z d
    · exact ⟨D'⟩

/-- **The general-`q` mark-on-the-path fresh cover.**  For every `q ≥ 2`, every configuration of
the fresh marked event with `q` labelled arms, every selected arm `j : Fin q` and every
enumeration `e : Fin (q-1) ≃ {i : Fin q // i ≠ j}` of the remaining labels, one of the `2q`-leg
diagrams of `genShape` occurs with all witnesses pairwise edge-disjoint.

No distinctness of the labels is needed (the enumeration `e` is a bijection onto the labels
different from `j`, so the other `q - 1` arms are attached exactly once each, in the order given
by `e`), and the attachment vertices may coincide with any vertex of the diagram or with the
arms: coincident arms, `w = y`, `w = g j` and trivial legs are all absorbed. -/
theorem freshMark_subset_genShape {q : ℕ} (_hq : 2 ≤ q) (y w : V) (g : Fin q → V) (j : Fin q)
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) :
    I417Gen.freshMark y g j w ⊆ genShape y w g j e := by
  classical
  rintro ω ⟨hDO, hlab⟩
  obtain ⟨s, t, hs, ht, hst, hys, hwt⟩ := hDO
  obtain ⟨p0, hp0⟩ := pathConnects_iff.mpr hys
  obtain ⟨r0, hr0⟩ := pathConnects_iff.mpr hwt
  -- the two halves of the selected path, as paths
  set P : (⊤ : SimpleGraph V).Walk y w := p0.bypass with hP
  set R : (⊤ : SimpleGraph V).Walk w (g j) := r0.bypass with hR
  have hPsub : ∀ e ∈ P.edges, e ∈ (s : Set (Sym2 V)) :=
    fun e he => hp0 e (SimpleGraph.Walk.edges_bypass_subset_edges p0 he)
  have hRsub : ∀ e ∈ R.edges, e ∈ (t : Set (Sym2 V)) :=
    fun e he => hr0 e (SimpleGraph.Walk.edges_bypass_subset_edges r0 he)
  have hPop : ∀ e ∈ P.edges, e ∈ ω := fun e he => hs (hPsub e he)
  have hRop : ∀ e ∈ R.edges, e ∈ ω := fun e he => ht (hRsub e he)
  have hPR : Disjoint (I417Example.edgeFinset P.edges) (I417Example.edgeFinset R.edges) := by
    rw [Finset.disjoint_left]
    intro e he he'
    exact Finset.disjoint_left.mp hst (hPsub e (I417Example.mem_edgeFinset.mp he))
      (hRsub e (I417Example.mem_edgeFinset.mp he'))
  -- all arms lie in the cluster of `y`
  rw [I417A.labelEvent_eq_iInter] at hlab
  have hcon : ∀ i : Fin q, Connects ω y (g i) := fun i => Set.mem_iInter.mp hlab i
  -- the induction, with the arms in the order prescribed by `e`
  obtain ⟨H, harm, _hfirst, ⟨D⟩⟩ :=
    exists_iter_diag (q := q) g j (q - 1) (fun t : Fin (q - 1) => (e t).1)
      (fun t => (e t).2)
      (SimpleGraph.Walk.bypass_isPath p0) (SimpleGraph.Walk.bypass_isPath r0)
      hPop hRop hPR (fun t => hcon (e t).1)
  refine Set.mem_iUnion.mpr ⟨⟨H, ?_⟩, ?_⟩
  · intro t
    exact harm t
  · exact shapeOfI_of_diag_legs D

/-- **The `q = 5` instance.**  The general cover applied at `q = 5` (ten fresh legs, four
attachment rounds); this is the first member of the family not covered by the accepted `q = 4`
artifact. -/
theorem freshMark_subset_genShape_five (y w : V) (g : Fin 5 → V) (j : Fin 5)
    (e : Fin 4 ≃ {i : Fin 5 // i ≠ j}) :
    I417Gen.freshMark y g j w ⊆ genShape y w g j e :=
  freshMark_subset_genShape (by norm_num) y w g j e

/-- **The `q = 4` instance.**  The general cover at `q = 4` (eight fresh legs, three attachment
rounds, `48` branch choices): this is the family whose evaluation is the accepted artifact
`smwx8o5tv/m2/Q4` / the `Q4-SUMMED-EVALUATION` direction. -/
theorem freshMark_subset_genShape_four (y w : V) (g : Fin 4 → V) (j : Fin 4)
    (e : Fin 3 ≃ {i : Fin 4 // i ≠ j}) :
    I417Gen.freshMark y g j w ⊆ genShape y w g j e :=
  freshMark_subset_genShape (by norm_num) y w g j e

end PercLib.CriticalLRP.I417GenIter
