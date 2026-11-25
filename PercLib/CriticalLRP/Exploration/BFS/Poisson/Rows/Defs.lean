/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Row-sum charging of a finite fresh edge set once per frontier vertex.

Direction 1 (swarm `smwpbvro2`, member m1).  `PoissonBoundBFS` reduces the fresh-pgf
estimate to a deterministic budget `bud σ ≥ ∑_{e ∈ S σ} p_e`.  This file supplies the
budget for the actual BFS geometry: for a *finite* frontier `T`, a finite set `S` of edges
from `T` into the undiscovered part `U` has total intensity at most `|T| · M` whenever every
vertex row sum is at most `M`.

The count is `|T| · M`, not `|T|²·M`: the edges of `S` are grouped by their frontier
endpoint, so each row sum is charged exactly once.  The statement is about a finite `S`;
it does not assert anything about the (possibly infinite) full queried set
`E(T,U)`.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Budget
public import PercLib.CriticalLRP.Exploration.BFS.Basic

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond Finset
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

/-- **Uniform real row-sum hypothesis**, in finite-partial-sum form: every vertex row sum is at
most `M`.  For `0 ≤ p` this is equivalent to `∑' y, p(s(x,y)) ≤ M`; the finite form is used so
that no summability is ever needed. -/
def UniformRowBound (p : Sym2 V → unitInterval) (M : ℝ) : Prop :=
  ∀ x : V, ∀ t : Finset V, x ∉ t → ∑ y ∈ t, (p (s(x, y)) : ℝ) ≤ M

/-- The `ℝ≥0∞`-valued `tsum` form of the uniform row-sum hypothesis implies `UniformRowBound`.

The `ℝ`-valued form `∑' y, (p (s(x,y)) : ℝ) ≤ M` is *not* the right hypothesis: for a
non-summable nonnegative family Mathlib's `ℝ`-valued `tsum` is the junk value `0`, so that
statement is vacuous.  The finite-partial-sum form above, and the `ℝ≥0∞`-valued `tsum` form
here, are the honest ones. -/
theorem uniformRowBound_of_tsum_ennreal {p : Sym2 V → unitInterval} {M : ℝ} (hM0 : 0 ≤ M)
    (h : ∀ x : V, ∑' y : V, ENNReal.ofReal (p (s(x, y)) : ℝ) ≤ ENNReal.ofReal M) :
    UniformRowBound p M := by
  intro x t _
  rw [← ENNReal.ofReal_le_ofReal_iff hM0]
  calc ENNReal.ofReal (∑ y ∈ t, (p (s(x, y)) : ℝ))
      = ∑ y ∈ t, ENNReal.ofReal (p (s(x, y)) : ℝ) :=
        ENNReal.ofReal_sum_of_nonneg (fun y _ => (p (s(x, y))).2.1)
    _ ≤ ∑' y : V, ENNReal.ofReal (p (s(x, y)) : ℝ) := ENNReal.sum_le_tsum t
    _ ≤ ENNReal.ofReal M := h x

/-- The edge map is injective in its second argument once the first is fixed: an edge of
`edgeSet T U` determines its `U`-endpoint from its `T`-endpoint. -/
theorem s_left_inj {x y₁ y₂ : V} (h : s(x, y₁) = s(x, y₂)) : y₁ = y₂ := by
  rcases Sym2.eq_iff.mp h with ⟨-, hyy⟩ | ⟨hxy, hyx⟩
  · exact hyy
  · exact hyx.trans hxy

/-- **Row-sum charging.**  For a finite frontier `T`, a disjoint undiscovered set `U`, and a
finite set `S` of edges from `T` to `U`, the total intensity of `S` is at most `|T| · M`.

This is the deterministic input of the one-step estimate: the edges of `S` are partitioned by
their `T`-endpoint, the `T`-endpoint map is injective along each row, and each row sum is at
most `M`.  No finiteness of `U`, of the degree, or of the full queried set is assumed. -/
theorem sum_le_card_mul_of_subset_edgeSet (p : Sym2 V → unitInterval) {T : Finset V} {U : Set V}
    (hdisj : Disjoint (T : Set V) U) (S : Finset (Sym2 V))
    (hS : ∀ e ∈ S, e ∈ edgeSet (T : Set V) U) {M : ℝ} (hM : UniformRowBound p M) :
    ∑ e ∈ S, (p e : ℝ) ≤ (T.card : ℝ) * M := by
  classical
  have hU : ∀ x ∈ (T : Set V), x ∉ U := fun x hx hxu => Set.disjoint_left.mp hdisj hx hxu
  have hex : ∀ e : ↥S, ∃ x : V, ∃ y : V, x ∈ (T : Set V) ∧ y ∈ U ∧ s(x, y) = e.1 := by
    intro e
    obtain ⟨x, hx, y, hy, hxy⟩ := hS e.1 e.2
    exact ⟨x, y, hx, hy, hxy.symm⟩
  choose xx yy hxx hyy hss using hex
  set g : ↥S → ↥T := fun e => ⟨xx e, by simpa using hxx e⟩ with hgdef
  have hgval : ∀ e : ↥S, (g e : V) = xx e := fun e => rfl
  have hsum1 : ∑ e ∈ S, (p e : ℝ) = ∑ e : ↥S, (p (s(xx e, yy e)) : ℝ) := by
    rw [← Finset.sum_coe_sort S (fun e => (p e : ℝ))]
    exact Finset.sum_congr rfl (fun e _ => by rw [hss e])
  have hsum2 : ∑ e : ↥S, (p (s(xx e, yy e)) : ℝ)
      = ∑ x : ↥T, ∑ e ∈ (Finset.univ.filter (fun e : ↥S => g e = x)),
          (p (s(xx e, yy e)) : ℝ) :=
    (Finset.sum_fiberwise Finset.univ g (fun e : ↥S => (p (s(xx e, yy e)) : ℝ))).symm
  have hstep : ∀ x : ↥T,
      ∑ e ∈ (Finset.univ.filter (fun e : ↥S => g e = x)), (p (s(xx e, yy e)) : ℝ) ≤ M := by
    intro x
    have hfib : ∀ e ∈ (Finset.univ.filter (fun e : ↥S => g e = x)), xx e = x.1 := by
      intro e he
      have hge : g e = x := (Finset.mem_filter.mp he).2
      simpa [hgval] using congrArg Subtype.val hge
    have hcongr : ∑ e ∈ (Finset.univ.filter (fun e : ↥S => g e = x)),
          (p (s(xx e, yy e)) : ℝ)
        = ∑ e ∈ (Finset.univ.filter (fun e : ↥S => g e = x)), (p (s(x.1, yy e)) : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [hfib e he]
    rw [hcongr]
    have hinj : Set.InjOn yy ((Finset.univ.filter (fun e : ↥S => g e = x)) : Set ↥S) := by
      intro e₁ he₁ e₂ he₂ hyyeq
      have h1 : xx e₁ = x.1 := hfib e₁ he₁
      have h2 : xx e₂ = x.1 := hfib e₂ he₂
      have hedge : e₁.1 = e₂.1 := by
        rw [← hss e₁, ← hss e₂, h1, h2, hyyeq]
      exact Subtype.ext hedge
    rw [← Finset.sum_image (f := fun y => (p (s(x.1, y)) : ℝ)) hinj]
    have hnotmem : x.1 ∉ (Finset.univ.filter (fun e : ↥S => g e = x)).image yy := by
      intro hmem
      obtain ⟨e, -, he⟩ := Finset.mem_image.mp hmem
      exact hU x.1 (by simp) (he ▸ hyy e)
    exact hM x.1 _ hnotmem
  calc ∑ e ∈ S, (p e : ℝ) = ∑ e : ↥S, (p (s(xx e, yy e)) : ℝ) := hsum1
    _ = ∑ x : ↥T, ∑ e ∈ (Finset.univ.filter (fun e : ↥S => g e = x)),
          (p (s(xx e, yy e)) : ℝ) := hsum2
    _ ≤ ∑ _x : ↥T, M := Finset.sum_le_sum (fun x _ => hstep x)
    _ = (T.card : ℝ) * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

end PercLib.CriticalLRP.Exploration.BFS
