/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The fresh queried set at a compressed state, and its finite-fresh supremum

Swarm `smwpbvro2`, member m2, direction d2.

The one-step estimate needs `λ^{|G_{k+1}|}` dominated by a *finite* fresh monomial
`λ^{#open F}` with `F ⊆ E(A_k,U_k)`.  Since `E(A_k,U_k)` can be infinite even when the
frontier is finite, the domination is by a supremum over finite fresh subsets; the
finite sets have to be chosen from the *state* only, which is why `freshEdges` is
defined on `FinState`, not on the configuration.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Generation.Arithmetic

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators Topology

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*} [Countable V]

/-! ### The fresh queried set as a function of the compressed state -/

/-- The queried edge set `E(A,U)` at a compressed state: for `some (Q,T)` it is
`E(T, (Q ∪ T)ᶜ)`, and for the trivial state the whole space (a superset, which is all the
one-step estimate uses). -/
def freshEdges (σ : FinState V) : Set (Sym2 V) :=
  match σ with
  | some (Q, T) => edgeSet (T : Set V) (((Q : Set V) ∪ (T : Set V))ᶜ)
  | none => univ

theorem queried_subset_freshEdges (ω : Config V) (o : V) (k : ℕ) :
    queried ω o k ⊆ freshEdges (finState ω o k) := by
  classical
  set σ := finState ω o k with hσ
  cases h : σ with
  | none => exact Set.subset_univ _
  | some QT =>
    obtain ⟨Q, T⟩ := QT
    obtain ⟨hQ, hT⟩ := finState_eq_some_iff.mp h
    have hU : U ω o k = (((Q : Set V) ∪ (T : Set V))ᶜ) := by
      rw [U_eq_compl, hQ, hT]
    show queried ω o k ⊆ freshEdges (some (Q, T))
    rw [freshEdges, queried, hU, hT]

/-- The queried set is disjoint from the revealed set of the same state.  At a finite
state this is the state-level form of `disjoint_revealed_queried`. -/
theorem freshEdges_disjoint_reveal (Q T : Finset V) (hQT : Disjoint (Q : Set V) (T : Set V)) :
    Disjoint (freshEdges (some (Q, T))) (revealFin (some (Q, T))) := by
  classical
  rw [Set.disjoint_left]
  rintro e ⟨x, hxT, y, hyU, rfl⟩ ⟨v, hvQ, hve⟩
  have hxQ : x ∉ (Q : Set V) := fun hxQ => (Set.disjoint_left.mp hQT) hxQ hxT
  rw [Sym2.mem_iff] at hve
  rcases hve with h | h
  · exact hxQ (h ▸ hvQ)
  · exact hyU (Or.inl (h ▸ hvQ))

/-! ### The finite-fresh supremum -/

/-- **Finite-fresh domination.**  The generation cardinality is dominated, in `epow`, by
the supremum of the finite open counts over finite subsets of any set containing the open
queried edges.  This is the monotone-convergence input of the one-step estimate; the
index type is the subtype of finite subsets of the *fixed* set `s`, so it does not depend
on the configuration. -/
theorem gen_epow_le_iSup_openCount {s : Set (Sym2 V)} {τ : ℝ} (hτ : 1 ≤ τ)
    {o : V} {k : ℕ} {ω : Config V} (hs : queried ω o k ∩ ω ⊆ s) :
    epow (ENNReal.ofReal τ) ((gen ω o k).encard) ≤
      ⨆ (F : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆ s}),
        (ENNReal.ofReal τ) ^ openCount F.1 ω := by
  classical
  have hgen : (gen ω o k).encard ≤ (queried ω o k ∩ ω).encard := gen_encard_le_queried ω o k
  refine le_trans (epow_mono (ENNReal.ofReal τ) (by simpa using ENNReal.ofReal_le_ofReal hτ)
    hgen) ?_
  rw [epow]
  refine iSup_le (fun k' => ?_)
  have hex : ∃ t : Finset (Sym2 V), (t : Set (Sym2 V)) ⊆ s ∧
      openCount t ω = ((queried ω o k ∩ ω).encard ⊓ (k' : ℕ∞)).toNat := by
    have hb : (((queried ω o k ∩ ω).encard ⊓ (k' : ℕ∞)).toNat : ℕ∞) ≤
        (queried ω o k ∩ ω).encard :=
      le_trans (ENat.natCast_toNat_le_self _) inf_le_left
    obtain ⟨t, ht, htc⟩ := exists_finset_card_le_encard (s := queried ω o k ∩ ω)
      (n := ((queried ω o k ∩ ω).encard ⊓ (k' : ℕ∞)).toNat) hb
    refine ⟨t, ht.trans hs, ?_⟩
    have hfil : t.filter (fun e => e ∈ ω) = t := by
      refine Finset.filter_eq_self.mpr (fun e he => ?_)
      exact (ht (by simpa using he)).2
    rw [openCount, hfil, htc]
  obtain ⟨t, hts, htoc⟩ := hex
  rw [← htoc, ENNReal.rpow_natCast]
  exact le_iSup (fun F : {F : Finset (Sym2 V) // (F : Set (Sym2 V)) ⊆ s} =>
    (ENNReal.ofReal τ) ^ openCount F.1 ω) ⟨t, hts⟩

end PercLib.CriticalLRP.Exploration.BFS
