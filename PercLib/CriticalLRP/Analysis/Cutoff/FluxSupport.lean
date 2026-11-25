/-
# Exact support of the cutoff derivative weight and finite flux sums

Accepted from swarm `smwtvrwnn` member `m3`, direction d10.  Loop invisibility and support filtering
are proved here; no edge reindexing or full derivative identity is asserted.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxSupport.Defs

/-!
Loop invisibility, cutoff support, and finite support-filtered flux sums.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.hashCommand false

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

/-! ## d10 — loop edges are invisible; the exact support of the source weight -/

namespace PercLib.CriticalLRP.Orchestration

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- A pair whose edge is a loop has equal entries. -/
theorem eq_of_mk_eq_loop {a b x : V} (h : s(a, b) = s(x, x)) : a = b := by
  have h' := (Sym2.mk_eq_mk_iff (p := (a, b)) (q := (x, x))).mp h
  rcases h' with h' | h'
  · have h1 : a = x := congrArg Prod.fst h'
    have h2 : b = x := congrArg Prod.snd h'
    rw [h1, h2]
  · have h1 : a = x := congrArg Prod.fst h'
    have h2 : b = x := congrArg Prod.snd h'
    rw [h1, h2]

/-- Adding the loop edge `s(x,x)` does not change the open graph:
`SimpleGraph.fromEdgeSet` discards loops. -/
theorem openGraph_insert_loop (ω : Config V) (x : V) :
    openGraph (ω ∪ {s(x, x)}) = openGraph ω := by
  ext a b
  rw [openGraph_adj, openGraph_adj]
  constructor
  · rintro ⟨hne, hmem⟩
    refine ⟨hne, ?_⟩
    rcases hmem with h | h
    · exact h
    · exact absurd (eq_of_mk_eq_loop (Set.mem_singleton_iff.mp h)) hne
  · rintro ⟨hne, hmem⟩
    exact ⟨hne, Set.mem_union_left _ hmem⟩

/-- Deleting the loop edge does not change the open graph. -/
theorem openGraph_sdiff_loop (ω : Config V) (x : V) :
    openGraph (ω \ {s(x, x)}) = openGraph ω := by
  ext a b
  rw [openGraph_adj, openGraph_adj]
  constructor
  · rintro ⟨hne, hmem⟩
    exact ⟨hne, hmem.1⟩
  · rintro ⟨hne, hmem⟩
    refine ⟨hne, ⟨hmem, ?_⟩⟩
    intro h
    exact hne (eq_of_mk_eq_loop (Set.mem_singleton_iff.mp h))

theorem connects_insert_loop (ω : Config V) (x o v : V) :
    Connects (ω ∪ {s(x, x)}) o v ↔ Connects ω o v := by
  have h := openGraph_insert_loop ω x
  simp only [Connects, h]

theorem connects_sdiff_loop (ω : Config V) (x o v : V) :
    Connects (ω \ {s(x, x)}) o v ↔ Connects ω o v := by
  have h := openGraph_sdiff_loop ω x
  simp only [Connects, h]

theorem cluster_insert_loop (ω : Config V) (x o : V) :
    cluster (ω ∪ {s(x, x)}) o = cluster ω o := by
  ext v
  simp only [mem_cluster_iff, connects_insert_loop]

theorem cluster_sdiff_loop (ω : Config V) (x o : V) :
    cluster (ω \ {s(x, x)}) o = cluster ω o := by
  ext v
  simp only [mem_cluster_iff, connects_sdiff_loop]

theorem sMomentTrunc_insert_loop (q : V → ℝ) (ω : Config V) (x o : V) (A : Finset V) :
    sMomentTrunc q o A (ω ∪ {s(x, x)}) = sMomentTrunc q o A ω := by
  simp only [sMomentTrunc, cluster_insert_loop]

theorem sMomentTrunc_sdiff_loop (q : V → ℝ) (ω : Config V) (x o : V) (A : Finset V) :
    sMomentTrunc q o A (ω \ {s(x, x)}) = sMomentTrunc q o A ω := by
  simp only [sMomentTrunc, cluster_sdiff_loop]

/-- **A loop edge has zero pivotal flux** for every functional of the truncated cluster volume:
flipping it changes neither cluster. -/
theorem pivotalFlux_sMomentTrunc_loop (μ : Measure (Config V)) (q : V → ℝ) (o : V) (A : Finset V)
    (x : V) : pivotalFlux μ (sMomentTrunc q o A) s(x, x) = 0 := by
  have h : ∀ ω : Config V, flipDiff (sMomentTrunc q o A) s(x, x) ω = 0 := by
    intro ω
    simp only [flipDiff, forceOn_singleton_open_eq, forceOn_singleton_closed_eq,
      sMomentTrunc_insert_loop, sMomentTrunc_sdiff_loop, sub_self]
  simp only [pivotalFlux, h]
  simp

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.eq_of_mk_eq_loop
#print axioms PercLib.CriticalLRP.Orchestration.openGraph_insert_loop
#print axioms PercLib.CriticalLRP.Orchestration.openGraph_sdiff_loop
#print axioms PercLib.CriticalLRP.Orchestration.connects_insert_loop
#print axioms PercLib.CriticalLRP.Orchestration.cluster_insert_loop
#print axioms PercLib.CriticalLRP.Orchestration.cluster_sdiff_loop
#print axioms PercLib.CriticalLRP.Orchestration.sMomentTrunc_insert_loop
#print axioms PercLib.CriticalLRP.Orchestration.sMomentTrunc_sdiff_loop
#print axioms PercLib.CriticalLRP.Orchestration.pivotalFlux_sMomentTrunc_loop

end PercLib.CriticalLRP.Orchestration

/-! ## d10 (continued) — exact support: zero weight off the support, support filter of the sum -/

namespace PercLib.CriticalLRP.Orchestration

open MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace SourceModelData

variable (M : SourceModelData)

/-- The derivative weight of a loop edge is zero. -/
theorem cutEdgeDeriv_loop (r : ℝ) (x : M.V) : M.cutEdgeDeriv r s(x, x) = 0 := by
  rw [M.cutEdgeDeriv_mk]
  simp

/-- **The derivative weight vanishes outside the interaction range.**  For an edge longer than `r`
the cut-off kernel is `0`, so the cut-off probability is `q_e = 0` and the derivative weight is `0`.
(On such an edge the closed probability `1 - q_e` is nevertheless `1`, which is exactly why the
coefficient identity `c_r(e) = β_c(-K'(r))(1-q_e)` may not be stated off the support.) -/
theorem cutEdgeDeriv_eq_zero_of_lt_dist {r : ℝ} {x y : M.V} (h : r < M.S.dist x y) :
    M.cutEdgeDeriv r s(x, y) = 0 := by
  rw [M.cutEdgeDeriv_mk]
  by_cases hxy : x = y
  · rw [ite_eq_left hxy]
  · rw [ite_eq_right hxy, ite_eq_right (not_le.mpr h)]

/-- **The exact support.**  Every edge outside `inSupport M r` — a loop, or longer than `r` — has
zero derivative weight. -/
theorem cutEdgeDeriv_eq_zero_of_not_support {r : ℝ} {e : Sym2 M.V}
    (h : ¬ inSupport M r e) : M.cutEdgeDeriv r e = 0 := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · rw [hxy]; exact M.cutEdgeDeriv_loop r y
    · by_cases hd : M.S.dist x y ≤ r
      · exact absurd ⟨x, y, hxy, rfl, hd⟩ h
      · exact M.cutEdgeDeriv_eq_zero_of_lt_dist (not_le.mp hd)

end SourceModelData

/-- Filtering a finite edge-window sum to the exact support does not change it, because every
term outside the support carries the zero derivative weight.  `f` is any edge observable; the
statement is used with `f e = M.cutEdgeDeriv r e * pivotalFlux μ (sMomentTrunc q o A) e`. -/
theorem sum_filter_inSupport_eq (M : SourceModelData) (r : ℝ) (S : Finset (Sym2 M.V))
    (f : Sym2 M.V → ℝ) (hzero : ∀ e : Sym2 M.V, ¬ inSupport M r e → f e = 0) :
    ∑ e ∈ S, f e = ∑ e ∈ S.filter (inSupport M r), f e := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun e _ => by
    by_cases h : inSupport M r e
    · simp [h]
    · simp [h, hzero e h]

/-- **The registered support-restricted flux sum.**  For every finite edge window `S`, every law
`μ`, every weight `q`, anchor `o` and finite `A`, the source flux sum over `S` equals its sum over
the non-loop edges of length `≤ r`: the loop and out-of-range terms vanish identically. -/
theorem sum_cutEdgeDeriv_mul_pivotalFlux_support (M : SourceModelData) (r : ℝ)
    (S : Finset (Sym2 M.V)) (μ : Measure (Config M.V)) (q : M.V → ℝ) (o : M.V) (A : Finset M.V) :
    ∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux μ (sMomentTrunc q o A) e
      = ∑ e ∈ S.filter (inSupport M r),
          M.cutEdgeDeriv r e * pivotalFlux μ (sMomentTrunc q o A) e := by
  refine sum_filter_inSupport_eq M r S _ (fun e he => ?_)
  rw [M.cutEdgeDeriv_eq_zero_of_not_support he, zero_mul]

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.inSupport
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_loop
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_eq_zero_of_lt_dist
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_eq_zero_of_not_support
#print axioms PercLib.CriticalLRP.Orchestration.sum_filter_inSupport_eq
#print axioms PercLib.CriticalLRP.Orchestration.sum_cutEdgeDeriv_mul_pivotalFlux_support

end PercLib.CriticalLRP.Orchestration
