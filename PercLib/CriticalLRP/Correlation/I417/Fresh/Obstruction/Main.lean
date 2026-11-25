/- Integrated from independently rebuilt Ultramath work.
Production base 545744b3e9550f31ac4373c2b1bb2f9134b2f93c.
Scratch source: repository-root .ultramath/smwvrtsxf/m2/Main.lean.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Main
public import PercLib.CriticalLRP.Correlation.TreeGraphCanonical
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Obstruction.Defs

/-!
# The four-arm hub event is not a chain spider

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof.

Production's fresh side at `q = 3` is the four-arm hub event
`hubStar y w g = {y ↔ w} ∩ ⋂_{j<3} {w ↔ g j}` summed over the three arms, against the
diagram value `freshCombBound π 3 y w`.  Every monomial of that value has the shape of a
`ChainSpider` (`Defs.lean`): a spine walk `w → v 1 → … → v 4` of four steps with four arm
slots, so that
BK applies to the eight connection events and produces exactly the monomial.

This file proves that the shape is **not** a cover of the four-arm hub event:

* `ds_hubEvent` — in the completely open six-edge double star (hub `0`, branch points `1`, `2`,
  terminals `3,4` at `1` and `5,6` at `2`) the hub event holds;
* `ds_no_chainSpider` — for **every** spine vector `u` and **every** injective assignment `z` of the
  four slots onto the four terminals, the eight connection requirements of the chain shape admit no
  pairwise edge-disjoint witnesses inside `dsE`.

The proof is a counting argument.  A witness for a connection separated by one of the six cuts of
the double star contains that cut's edge (`cut_mem_of_connects`), so pairwise disjointness forces
two separated requirements to be separated by different cuts: `chainSepC ≤ 6`.  On the other
hand the separation count of a chain shape with four steps and four slots at the four terminals is
at least seven (`chainSepX_ge_seven`), a finite check on the seven-vertex type.  Contradiction.

Consequence: neither the `q = 1` route (`freshMark_measure_le_oneHub`, one hub) nor the `q = 2`
route (`threeLeaf_treeGraph`, two hubs on a spine) extends to `q = 3` by the cover-plus-BK method,
and the chain family cannot receive the four-terminal cover.  This neither proves nor disproves
`FreshCombBound π 3`; the double star is the minimal configuration in which the four terminals hang
off two distinct branch points, the shape the chain monomial cannot express.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

/-! ## The six cuts of the double star -/

/-- The double star has six edges. -/
theorem dsE_card : dsE.card = 6 := by decide

/-- **The cut edge is unique**: an edge of the double star whose endpoints lie on different sides
of one of the six cuts is that cut's distinguished edge. -/
theorem cut_unique : ∀ (c : Fin 6) (x y : DSV), x ≠ y → s(x, y) ∈ dsE →
    dsSide c x ≠ dsSide c y → s(x, y) = dsCutEdge c := by
  decide

/-- A walk whose endpoints lie on different sides of a cut uses an edge whose endpoints lie on
different sides. -/
theorem walk_has_sep_edge {g : DSV → Bool} {a b : DSV}
    (p : (⊤ : SimpleGraph DSV).Walk a b) (h : g a ≠ g b) :
    ∃ x y : DSV, x ≠ y ∧ s(x, y) ∈ p.edges ∧ g x ≠ g y := by
  induction p with
  | nil => exact absurd rfl h
  | cons hadj p' ih =>
      rename_i u v w
      by_cases hgv : g u = g v
      · obtain ⟨x, y, hxy, hmem, hdiff⟩ := ih (by rw [← hgv]; exact h)
        exact ⟨x, y, hxy, List.mem_cons_of_mem _ hmem, hdiff⟩
      · exact ⟨u, v, (SimpleGraph.top_adj u v).1 hadj, by simp, hgv⟩

/-- **Any witness for a connection separated by a cut contains that cut's edge.** -/
theorem cut_mem_of_connects (c : Fin 6) {W : Finset (Sym2 DSV)} {a b : DSV}
    (hW : (W : Set (Sym2 DSV)) ⊆ (dsE : Set (Sym2 DSV)))
    (hc : Connects (W : Config DSV) a b) (h : dsSide c a ≠ dsSide c b) :
    dsCutEdge c ∈ W := by
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr hc
  obtain ⟨x, y, hxy, hmem, hdiff⟩ := walk_has_sep_edge p h
  have hEW : s(x, y) ∈ W := hp _ hmem
  have hEd : s(x, y) ∈ dsE := hW hEW
  rw [cut_unique c x y hxy hEd hdiff] at hEW
  exact hEW

/-! ## The hub event holds in the double star -/

/-- A single open edge of the double star connects its endpoints. -/
theorem conn_single {a b : DSV} (hab : s(a, b) ∈ dsE) (hne : a ≠ b) :
    Connects (dsE : Config DSV) a b := by
  refine pathConnects_iff.mp ?_
  refine ⟨SimpleGraph.Walk.cons ((SimpleGraph.top_adj a b).2 hne) SimpleGraph.Walk.nil, ?_⟩
  intro e he
  have h : e = s(a, b) := by simpa using he
  rw [h]
  exact hab

/-- **The four-arm hub event holds in the fully open double star**: the hub `0` is joined to the
three arms `3, 4, 5` and to the terminal `6` that the spine is attached to. -/
theorem ds_hubEvent :
    Connects (dsE : Config DSV) 6 0 ∧ Connects (dsE : Config DSV) 0 3 ∧
      Connects (dsE : Config DSV) 0 4 ∧ Connects (dsE : Config DSV) 0 5 := by
  have h01 : Connects (dsE : Config DSV) 0 1 := conn_single (by decide) (by decide)
  have h02 : Connects (dsE : Config DSV) 0 2 := conn_single (by decide) (by decide)
  have h13 : Connects (dsE : Config DSV) 1 3 := conn_single (by decide) (by decide)
  have h14 : Connects (dsE : Config DSV) 1 4 := conn_single (by decide) (by decide)
  have h25 : Connects (dsE : Config DSV) 2 5 := conn_single (by decide) (by decide)
  have h26 : Connects (dsE : Config DSV) 2 6 := conn_single (by decide) (by decide)
  exact ⟨connects_symm (connects_trans h02 h26), connects_trans h01 h13,
    connects_trans h01 h14, connects_trans h02 h25⟩

/-! ## The separation count is at least seven -/

set_option maxHeartbeats 4000000 in
-- Reason: the finite check below evaluates 2401 spine vectors times 24 slot permutations, far
-- beyond the default heartbeat budget.
set_option maxRecDepth 40000 in
/-- **The separation count of a chain shape with four steps and four slots at the four terminals is
at least seven.**  This is the only finite check in the file: an exhaustive computation on the
seven-vertex type, in the cut-by-cut form `chainSepX`. -/
theorem chainSepX_ge_seven_perm (u : Fin 4 → DSV) (e : Fin 4 ≃ Fin 4) :
    7 ≤ chainSepX 0 u (fun i => dsArm (e i)) := by
  revert u e
  decide

/-- The two writings of the pair separation count agree. -/
theorem nsep_eq_nsepC : ∀ a b : DSV, nsep a b = nsepC a b := by
  decide

/- The terminal reindexing function `dsSlot` is defined in `Obstruction.Defs`. -/

theorem dsArm_dsSlot {z : Fin 4 → DSV} (hz : ∀ i, z i = 3 ∨ z i = 4 ∨ z i = 5 ∨ z i = 6)
    (i : Fin 4) : dsArm (dsSlot z i) = z i := by
  rcases hz i with h | h | h | h <;> simp [dsSlot, h, dsArm]

/-- **The separation count of every chain shape at the four terminals is at least seven.** -/
theorem chainSepX_ge_seven (u z : Fin 4 → DSV)
    (hz : ∀ i, z i = 3 ∨ z i = 4 ∨ z i = 5 ∨ z i = 6) (hinj : Function.Injective z) :
    7 ≤ chainSepX 0 u z := by
  have hval : (fun i => dsArm (dsSlot z i)) = z := funext fun i => dsArm_dsSlot hz i
  have hinj' : Function.Injective (dsSlot z) := by
    intro i j hij
    exact hinj (by rw [← dsArm_dsSlot hz i, ← dsArm_dsSlot hz j, hij])
  have hbij : Function.Bijective (dsSlot z) := Finite.injective_iff_bijective.mp hinj'
  have h := chainSepX_ge_seven_perm u (Equiv.ofBijective (dsSlot z) hbij)
  simp only [Equiv.ofBijective_apply] at h
  rwa [hval] at h

/-- The two writings of the chain separation count agree. -/
theorem chainSepX_eq_chainSep (u z : Fin 4 → DSV) :
    chainSepX 0 u z = chainSep 0 u z := by
  simp only [chainSepX, chainSep, nsep_eq_nsepC, spineSrc, spineTgt, Fin.sum_univ_four]
  simp
  omega

/-- The cut-by-cut separation count is the chain separation count. -/
theorem chainSepC_eq_chainSepX (u z : Fin 4 → DSV) :
    chainSepC 0 u z = chainSepX 0 u z := by
  simp only [chainSepC, chainSepX, cntS, cntL, nsepC, spineSrc, spineTgt, dsSide,
    Fin.sum_univ_four]
  simp
  omega

/-! ## The obstruction -/

/-- **The four-arm hub event is not a chain spider.**  In the six-edge double star, for every spine
walk `u` and every injective assignment of the four slots onto the four terminals, the eight
connection requirements of the chain shape have no pairwise edge-disjoint witnesses.  Hence the hub
event is not contained in any chain-spider event, and the chain monomial cannot be produced from it
by the van den Berg–Kesten inequality: the chain family is not a cover at `q = 3`. -/
theorem ds_no_chainSpider (u z : Fin 4 → DSV)
    (hz : ∀ i, z i = 3 ∨ z i = 4 ∨ z i = 5 ∨ z i = 6) (hinj : Function.Injective z) :
    ¬ ChainSpider (dsE : Config DSV) 0 u z := by
  rintro ⟨S, L, hS, hL, hSc, hLc, hSd, hSL, hLd⟩
  have hmemS : ∀ (c : Fin 6) (i : Fin 4),
      dsSide c (spineSrc 0 u i) ≠ dsSide c (spineTgt u i) → dsCutEdge c ∈ S i :=
    fun c i h => cut_mem_of_connects c (hS i) (hSc i) h
  have hmemL : ∀ (c : Fin 6) (i : Fin 4),
      dsSide c (u i) ≠ dsSide c (z i) → dsCutEdge c ∈ L i :=
    fun c i h => cut_mem_of_connects c (hL i) (hLc i) h
  have hcount : ∀ c : Fin 6, cntS c 0 u + cntL c u z ≤ 1 := by
    intro c
    have hcross : ∀ (i j : Fin 4),
        dsSide c (spineSrc 0 u i) ≠ dsSide c (spineTgt u i) →
          dsSide c (u j) ≠ dsSide c (z j) → False := by
      intro i j hi hj
      exact Finset.disjoint_left.mp (hSL i j) (hmemS c i hi) (hmemL c j hj)
    have hSp : ∀ i j : Fin 4, dsSide c (spineSrc 0 u i) ≠ dsSide c (spineTgt u i) →
        dsSide c (spineSrc 0 u j) ≠ dsSide c (spineTgt u j) → i = j := by
      intro i j hi hj
      by_contra hij
      exact Finset.disjoint_left.mp (hSd i j hij) (hmemS c i hi) (hmemS c j hj)
    have hLg : ∀ i j : Fin 4, dsSide c (u i) ≠ dsSide c (z i) →
        dsSide c (u j) ≠ dsSide c (z j) → i = j := by
      intro i j hi hj
      by_contra hij
      exact Finset.disjoint_left.mp (hLd i j hij) (hmemL c i hi) (hmemL c j hj)
    have hcardS : cntS c 0 u = (Finset.univ.filter (fun i : Fin 4 =>
        dsSide c (spineSrc 0 u i) ≠ dsSide c (spineTgt u i))).card := by
      rw [cntS, Finset.card_filter]
    have hcardL : cntL c u z = (Finset.univ.filter (fun i : Fin 4 =>
        dsSide c (u i) ≠ dsSide c (z i))).card := by
      rw [cntL, Finset.card_filter]
    have hS1 : cntS c 0 u ≤ 1 := by
      rw [hcardS, Finset.card_le_one]
      intro a ha b hb
      exact hSp a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    have hL1 : cntL c u z ≤ 1 := by
      rw [hcardL, Finset.card_le_one]
      intro a ha b hb
      exact hLg a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    rcases Nat.eq_zero_or_pos (cntS c 0 u) with h0 | hpos
    · omega
    · obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [← hcardS]; omega)
      rw [Finset.mem_filter] at hi
      have hL0 : cntL c u z = 0 := by
        rw [hcardL, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro j hj
        rw [Finset.mem_filter] at hj
        exact hcross i j hi.2 hj.2
      omega
  have htotal : chainSepC 0 u z ≤ 6 := by
    simp only [chainSepC]
    have h0 := hcount 0
    have h1 := hcount 1
    have h2 := hcount 2
    have h3 := hcount 3
    have h4 := hcount 4
    have h5 := hcount 5
    omega
  have hseven : 7 ≤ chainSepC 0 u z := by
    rw [chainSepC_eq_chainSepX]
    exact chainSepX_ge_seven u z hz hinj
  omega

end PercLib.CriticalLRP.I417Fresh
