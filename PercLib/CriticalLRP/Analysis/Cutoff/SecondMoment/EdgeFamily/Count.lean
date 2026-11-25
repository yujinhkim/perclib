/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The exact `2`-to-`1` orientation count of the quadratic edge weight

Swarm `smwvc1d9z`, member `m2`, direction `d1`

Integration donor: `.ultramath/smwvc1d9z/m2`; independently reviewed at
`a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f` after one connectivity-composition repair in `Count.lean`..

`quadEdgeWeight dt ω o s(x,y)` is by definition the *sum of the two orientations* of the edge
`{x,y}` (`Defs.lean`), and the exact increment of `|K_o|²` when the closed edge is opened is
that sum (`clusterVol_sq_union_pair_eq_add_quadEdgeWeight`, donor `smwvbcnfb/m2`).  The content
of this file is the reindexing that turns the *unordered* edge family into the *ordered*
endpoint-pair family, with the honest factor `2` supplied by a count and not by an average:

* `sum_sum_mul_quadPairWeight` — the weighted double count.  For every finite vertex set `B`
  and every weight `h` of edges,
  `∑_{b ∈ B} ∑_{c ∈ B} h {b,c} · quadPairWeight b c = ∑_{e ∈ B.sym2} h e · quadEdgeWeight e`.
  This is where the `2` comes from: each *non-degenerate* unordered edge `{b,c}` with `b,c ∈ B`
  receives exactly the two ordered pairs `(b,c)` and `(c,b)`, and the degenerate pairs `(b,b)`
  contribute `0` because `quadPairWeight b b = 0` (a vertex is always connected to itself, so
  that edge is never pivotal).  No division, no averaging and no `Sym2` linear-order choice is
  used: the count is an induction on `B` through `Finset.sym2_insert`.

* `sum_sum_ite_quadPairWeight` — the explicit orientation count for a single edge:
  `∑_{b ∈ B} ∑_{c ∈ B} 1{s(b,c) = s(x,y)} · quadPairWeight b c = quadPairWeight x y +
  quadPairWeight y x`.  This is the form requested in the donor's notes ("split on `b = x`,
  `b = y`, else"); it is deduced here from the weighted double count with `h = 1{s(x,y)}`, so
  the `2`-to-`1` structure and the single-edge indicator are the same statement.  For `x ≠ y`
  the two terms on the right are exactly the two orientations of the edge; the identity is
  stated without that hypothesis because the degenerate case is `0 = 0` as well
  (`quadPairWeight x x = 0`), so no side condition is needed.

* `sum_sym2_quadEdgeWeight` — the unweighted finite edge-to-vertex identity
  `∑_{e ∈ B.sym2} quadEdgeWeight e = ∑_{b ∈ B} ∑_{c ∈ B} quadPairWeight b c`.

What is *not* claimed here: no `tsum` interchange, no measurability, and no statement about any
model or radius (those are in `EdgeToVertex.lean` / `Main.lean`).  Everything is a finite-sum
identity in `ℝ≥0∞`, unconditional in the configuration.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Defs

/-!
# The finite `2`-to-`1` orientation count

The main results are `sum_sum_mul_quadPairWeight` (weighted double count), its unweighted
specialisation `sum_sym2_quadEdgeWeight`, and the single-edge orientation count
`sum_sum_ite_quadPairWeight` requested by the donor's notes.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Finset
open scoped ENNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

/-! ## 1. Elementary facts about the two weights -/

variable {V : Type*}

/-- The unordered edge weight splits into its two orientations. -/
theorem quadEdgeWeight_mk (dt : V → V → Prop) (ω : Config V) (o x y : V) :
    quadEdgeWeight dt ω o s(x, y) = quadPairWeight dt ω o x y + quadPairWeight dt ω o y x :=
  Sym2.lift_mk ..

/-- The unordered edge weight only depends on the unordered pair (exchanging the two names of
the endpoints changes nothing).  The oriented weight itself is *not* symmetric: the base point is
singled out. -/
theorem quadEdgeWeight_swap (dt : V → V → Prop) (ω : Config V) (o x y : V) :
    quadEdgeWeight dt ω o s(x, y) = quadEdgeWeight dt ω o s(y, x) := by
  rw [quadEdgeWeight_mk, quadEdgeWeight_mk, add_comm]

/-- A degenerate oriented pair carries no weight: a vertex is always connected to itself, so the
edge `{b,b}` is never pivotal.  This is exactly why the double count has no `2` on the diagonal. -/
theorem quadPairWeight_self (dt : V → V → Prop) (ω : Config V) (o x : V) :
    quadPairWeight dt ω o x x = 0 := by
  have h : ¬ ¬ Connects ω x x := fun hc => hc (SimpleGraph.Reachable.refl x)
  simp only [quadPairWeight, h]
  simp

/-- The degenerate edge `{x,x}` carries no weight. -/
theorem quadEdgeWeight_diag (dt : V → V → Prop) (ω : Config V) (o x : V) :
    quadEdgeWeight dt ω o s(x, x) = 0 := by
  simp [quadEdgeWeight_mk, quadPairWeight_self]

/-- The oriented weight vanishes unless the base point is connected to the root. -/
theorem quadPairWeight_eq_zero_of_not_connects (dt : V → V → Prop) (ω : Config V) (o : V)
    {b c : V} (hb : ¬ Connects ω o b) : quadPairWeight dt ω o b c = 0 := by
  simp [quadPairWeight, hb]

/-- The oriented weight vanishes on an edge whose endpoints are already connected. -/
theorem quadPairWeight_eq_zero_of_connects (dt : V → V → Prop) (ω : Config V) (o : V)
    {b c : V} (hbc : Connects ω b c) : quadPairWeight dt ω o b c = 0 := by
  simp [quadPairWeight, hbc]

/-- **No double counting: at most one orientation of an edge is carried by the quadratic
weight.**  If one endpoint is connected to the root, the other one cannot be (else the two
endpoints would be connected and the edge would not be pivotal), so the two orientations of the
same edge are never both nonzero.  Hence summing the two orientations is *not* an averaging of a
doubled quantity: the `2`-to-`1` count is a count of indices, and `quadEdgeWeight` is exactly the
sum of the two (at most one of which is nonzero). -/
theorem quadPairWeight_mul_swap_eq_zero (dt : V → V → Prop) (ω : Config V) (o x y : V) :
    quadPairWeight dt ω o x y * quadPairWeight dt ω o y x = 0 := by
  by_cases hx : Connects ω o x
  · by_cases hxy : Connects ω x y
    · rw [quadPairWeight_eq_zero_of_connects dt ω o (SimpleGraph.Reachable.symm hxy), mul_zero]
    · have hy : ¬ Connects ω o y := fun h =>
        hxy (SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm hx) h)
      rw [quadPairWeight_eq_zero_of_not_connects dt ω o hy, mul_zero]
  · rw [quadPairWeight_eq_zero_of_not_connects dt ω o hx, zero_mul]

/-! ## 2. The weighted `2`-to-`1` double count

Each non-degenerate unordered pair `{b,c}` of vertices of `B` receives exactly its two
orientations; the diagonal receives `quadPairWeight b b = 0` on both sides.  The count is by
induction on `B`, with `Finset.sym2_insert` splitting off the edges through the new vertex `a`.
The weight `h` of an edge is arbitrary, which is what makes the single-edge indicator count
(`sum_sum_ite_quadPairWeight`) a corollary. -/

/-- **The weighted double count.**  For a finite vertex set `B` and an arbitrary edge weight
`h`, the sum of the oriented endpoint weights over the ordered pairs from `B` equals the sum of
the unordered edge weights over the edges of `B`, each weighted by `h`. -/
theorem sum_sum_mul_quadPairWeight (dt : V → V → Prop) (ω : Config V) (o : V)
    (h : Sym2 V → ℝ≥0∞) (B : Finset V) :
    (∑ b ∈ B, ∑ c ∈ B, h s(b, c) * quadPairWeight dt ω o b c)
      = ∑ e ∈ B.sym2, h e * quadEdgeWeight dt ω o e := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | insert a B' ha ih =>
    -- the edges through `a` are disjoint from the old edges
    have hdisj : Disjoint ((insert a B').image (fun b => s(a, b))) B'.sym2 := by
      refine Finset.disjoint_left.mpr ?_
      intro e he hf
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp he
      exact ha ((Finset.mem_sym2_iff.mp hf) a (Sym2.mem_mk_left a b))
    -- the map `b ↦ {a,b}` is injective
    have hinj : Set.InjOn (fun b => s(a, b)) ↑(insert a B') := by
      intro b _ b' _ hb
      rw [Sym2.eq_iff] at hb
      rcases hb with ⟨-, h1⟩ | ⟨h1, h2⟩
      · exact h1
      · exact h2.trans h1
    -- the swap of the two names of an edge
    have hswap : ∀ b : V, h s(a, b) = h s(b, a) := fun b => by rw [Sym2.eq_swap]
    -- the left-hand side, split into the row of `a` and the old block
    have hL : (∑ b ∈ insert a B', ∑ c ∈ insert a B', h s(b, c) * quadPairWeight dt ω o b c)
        = (∑ c ∈ B', h s(a, c) * quadPairWeight dt ω o a c)
          + (∑ b ∈ B', h s(b, a) * quadPairWeight dt ω o b a)
          + (∑ b ∈ B', ∑ c ∈ B', h s(b, c) * quadPairWeight dt ω o b c) := by
      rw [Finset.sum_insert ha]
      conv_lhs => rw [Finset.sum_insert ha]
      rw [Finset.sum_congr rfl (fun b _ => Finset.sum_insert ha)]
      rw [Finset.sum_add_distrib, quadPairWeight_self, mul_zero, zero_add]
      ac_rfl
    -- the right-hand side, split into the new edges and the old block
    have hR : (∑ e ∈ (insert a B').sym2, h e * quadEdgeWeight dt ω o e)
        = (∑ c ∈ B', h s(a, c) * quadPairWeight dt ω o a c)
          + (∑ b ∈ B', h s(b, a) * quadPairWeight dt ω o b a)
          + (∑ b ∈ B', ∑ c ∈ B', h s(b, c) * quadPairWeight dt ω o b c) := by
      rw [Finset.sym2_insert, Finset.sum_union hdisj, ← ih, Finset.sum_image hinj,
        Finset.sum_insert ha]
      rw [quadEdgeWeight_diag, mul_zero, zero_add]
      simp only [quadEdgeWeight_mk]
      rw [Finset.sum_congr rfl (fun b (_ : b ∈ B') =>
        mul_add (h s(a, b)) (quadPairWeight dt ω o a b) (quadPairWeight dt ω o b a))]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun b (_ : b ∈ B') =>
        congrArg (fun z => z * quadPairWeight dt ω o b a) (hswap b))]
    rw [hL, hR]

/-- **The unweighted finite edge-to-vertex identity.** -/
theorem sum_sym2_quadEdgeWeight (dt : V → V → Prop) (ω : Config V) (o : V) (B : Finset V) :
    ∑ e ∈ B.sym2, quadEdgeWeight dt ω o e
      = ∑ b ∈ B, ∑ c ∈ B, quadPairWeight dt ω o b c := by
  classical
  have h := sum_sum_mul_quadPairWeight dt ω o (fun _ => (1 : ℝ≥0∞)) B
  simpa using h.symm

/-! ## 3. The single-edge orientation count

With the edge weight `h = 1{s(x,y)}` the weighted double count localises at the single edge
`{x,y}`, and the left-hand side becomes the explicit `ite` sum carried by the ordered pairs that
represent that edge.  For `x ≠ y` these are exactly the two orientations `(x,y)` and `(y,x)`.

The `2`-to-`1` structure is recorded first as an honest card statement
(`filter_eq_pair_of_mk_eq` and `card_filter_eq_two`): the ordered pairs from `B` representing the
edge `{x,y}` form the two-element set `{(x,y), (y,x)}`, so the count is `2` and not an average.

### 3.1 The ordered pairs representing a single edge -/

/-- **The two-to-one count, as a finite-set statement.**  For `x ≠ y` and `x, y ∈ B`, the ordered
pairs from `B` whose unordered edge is `{x,y}` are exactly `(x,y)` and `(y,x)`. -/
theorem filter_eq_pair_of_mk_eq {B : Finset V} {x y : V} (hx : x ∈ B) (hy : y ∈ B) :
    (B ×ˢ B).filter (fun p : V × V => s(p.1, p.2) = s(x, y)) = {(x, y), (y, x)} := by
  classical
  ext p
  obtain ⟨a, b⟩ := p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
    Sym2.eq_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨hx, hy⟩, by simp⟩
    · exact ⟨⟨hy, hx⟩, by simp⟩

/-- **The count is `2`.**  For distinct `x, y` in `B` there are exactly two ordered pairs from
`B` representing the unordered edge `{x,y}`: the two orientations. -/
theorem card_filter_eq_two {B : Finset V} {x y : V} (hxy : x ≠ y) (hx : x ∈ B) (hy : y ∈ B) :
    ((B ×ˢ B).filter (fun p : V × V => s(p.1, p.2) = s(x, y))).card = 2 := by
  classical
  rw [filter_eq_pair_of_mk_eq hx hy,
    Finset.card_pair (a := (x, y)) (b := (y, x)) (by simp [hxy])]

/-! ### 3.2 The weighted count localised at one edge

The donor's statement, deduced from the weighted double count with `h = 1{s(x,y)}`. -/

/-- **The explicit orientation count requested by the donor's notes.**  For `x, y ∈ B`,
`∑_{b ∈ B} ∑_{c ∈ B} 1{s(b,c) = s(x,y)} · quadPairWeight b c`
`= quadPairWeight x y + quadPairWeight y x`: the two orientations of the edge and nothing else.
No `x ≠ y` hypothesis is needed, because the degenerate case reads `0 = 0`. -/
theorem sum_sum_ite_quadPairWeight (dt : V → V → Prop) (ω : Config V) (o : V) (B : Finset V)
    {x y : V} (hx : x ∈ B) (hy : y ∈ B) :
    (∑ b ∈ B, ∑ c ∈ B, if s(b, c) = s(x, y) then quadPairWeight dt ω o b c else 0)
      = quadPairWeight dt ω o x y + quadPairWeight dt ω o y x := by
  classical
  have h := sum_sum_mul_quadPairWeight dt ω o
    (fun e => if e = s(x, y) then (1 : ℝ≥0∞) else 0) B
  -- the left-hand side of the weighted count is the `ite` sum
  have hleft : ∀ b ∈ B, ∀ c ∈ B,
      (if s(b, c) = s(x, y) then (1 : ℝ≥0∞) else 0) * quadPairWeight dt ω o b c
        = if s(b, c) = s(x, y) then quadPairWeight dt ω o b c else 0 := by
    intro b _ c _
    split <;> simp
  rw [Finset.sum_congr rfl (fun b hb => Finset.sum_congr rfl (hleft b hb))] at h
  -- the right-hand side localises at the single edge `s(x,y) ∈ B.sym2`
  have hmem : s(x, y) ∈ B.sym2 := Finset.mk_mem_sym2_iff.mpr ⟨hx, hy⟩
  have hright : ∀ e ∈ B.sym2, e ≠ s(x, y) →
      (if e = s(x, y) then (1 : ℝ≥0∞) else 0) * quadEdgeWeight dt ω o e = 0 := by
    intro e _ he
    simp [he]
  have hsingle := Finset.sum_eq_single (s(x, y)) hright (fun hnot => absurd hmem hnot)
  have hone : (if s(x, y) = s(x, y) then (1 : ℝ≥0∞) else 0) * quadEdgeWeight dt ω o s(x, y)
      = quadEdgeWeight dt ω o s(x, y) := by simp
  rw [hsingle, hone, quadEdgeWeight_mk] at h
  exact h

end PercLib.CriticalLRP
