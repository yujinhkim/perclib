/- Integrated from reviewed Ultramath root-pair work.
Production base 1eaaabcf41deb59c0da2c83d0f2d7ad9d952510f.
Scratch source output: ../../.ultramath/smwvlmbqa/m3/Obstruction.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.RootPair.Defs

/-!
# Hub minimisation for `p = 5`, `k = 2` two-hub diagrams

In nearest-neighbour bond percolation on the line, `tau x y = p ^ |x-y|` and
`jointP a b c = p ^ (span of {a,b,c})`, so the value of a BK diagram at a fixed leaf
configuration is `p ^ (arm cost)`, where the cost of a two-point arm is `zdist` and the cost
of a joint pair measured from a hub is `zspan3`.  The five-point connection event at the six
consecutive positions `0,1,2,3,4,5` costs exactly `5` (the arc `0–1–2–3–4–5` must be open).

Every diagram whose leaf-and-hub sum normalises to `(E|K|^2)^2 (E|K|)^3` has seven arms: two
joint pairs (four arms) and three two-point arms forming a tree through the root and the two
hubs.  Up to relabelling there are three shapes, and this file reduces each to a
*hub-free* expression:

* `fan_cost_reduction` — the production fan `HubK2.hubStar`;
* `chain_cost_reduction` — the production chain `HubK2.hubChain`;
* `root_pair_cost_reduction` — the corrected shape `HubRoot.hubChainRoot`, which puts the
  root inside the first joint pair.

The reusable input is the Steiner step `zspan3_add_two_zdist_ge`: arms at a hub cost at least
the span of their far endpoints, so minimising over the hubs never costs more than the
spanning cost of the terminals.  With the reduction in hand the residual check is a finite
numeric comparison of spans of subsets of `{0,1,2,3,4,5}`; on that set

* the fan's reduced cost is `span{a,b,0,f} + span{d,e,0} ≥ 7`,
* the chain's reduced cost is `span{a,b,0} + span{d,e,f} ≥ 4`, sharpened to `≥ 6` by the
  spine term (see `armcost.py` in this directory for the full finite check),
* and the corrected shape reaches `5` (`root_pair_cost_eq_five`), which is the event cost.

The full finite check over all `30` leaf splits and all `60` root-in-pair assignments is
recorded in `armcost.py` of this directory; `root_pair_cost_eq_five` below is the sharp case.
Each reduction is proved by applying the Steiner steps hub by hub and closing with `linarith`;
no heartbeat option is used anywhere in this directory.
-/

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction

/-- **Steiner step.**  Adding a point to a span costs at most the arm from any point of it. -/
theorem zspan3_add_zdist_ge (a b c x : ℤ) : zspan3 a b x ≤ zspan3 a b c + zdist c x := by
  unfold zspan3 zdist
  omega

/-- **Steiner step, two arms.**  A hub carrying a joint pair and two single arms costs at
least the span of the four endpoints. -/
theorem zspan3_add_two_zdist_ge (a b x y c : ℤ) :
    zspan4 a b x y ≤ zspan3 a b c + zdist c x + zdist c y := by
  unfold zspan3 zspan4 zdist
  omega

/-- **Fan reduction.**  The fan's arm cost is at least `span{a,b,0,f} + span{d,e,0}`: the two
hubs can be eliminated at no cost. -/
theorem fan_cost_reduction (a b d e f c1 c2 : ℤ) :
    zspan4 a b 0 f + zspan4 d e 0 0 ≤
      zspan3 a b c1 + zdist c1 0 + zdist c1 f + zspan3 d e c2 + zdist c2 0 := by
  have h1 := zspan3_add_two_zdist_ge a b 0 f c1
  have h2 := zspan3_add_zdist_ge d e c2 0
  have h3 : zspan4 d e 0 0 = zspan3 d e 0 := by simp only [zspan3, zspan4]; omega
  linarith

/-- **Chain reduction.**  The production chain links the second hub to the first along the
spine `c1 – c2`; eliminating both hubs leaves `span{a,b,0,c2} + span{d,e,f}`, whose free
`c2` is itself a hub summand. -/
theorem chain_cost_reduction (a b d e f c1 c2 : ℤ) :
    zspan4 a b 0 0 + zspan4 d e f f ≤
      zspan3 a b c1 + zdist c1 0 + zspan3 d e c2 + zdist c1 c2 + zdist f c2 := by
  have h1 := zspan3_add_two_zdist_ge a b 0 c2 c1
  have h2 := zspan3_add_zdist_ge d e c2 f
  have h3 : zspan4 a b 0 0 ≤ zspan4 a b 0 c2 := by simp only [zspan4]; omega
  have h4 : zspan4 d e f f = zspan3 d e f := by simp only [zspan3, zspan4]; omega
  have h5 : zdist c2 f = zdist f c2 := by unfold zdist; omega
  linarith

/-- **Root-in-pair reduction.**  With the root inside the first joint pair, eliminating both
hubs leaves `span{0,a,b,c2} + span{d,e,f}` — the cheapest of the three reductions at the
configuration where the six terminals are consecutive. -/
theorem root_pair_cost_reduction (a b d e f c1 c2 : ℤ) :
    zspan4 0 a b b + zspan4 d e f f ≤
      zspan3 0 a c1 + zdist b c1 + zspan3 d e c2 + zdist c1 c2 + zdist f c2 := by
  have h1 := zspan3_add_two_zdist_ge 0 a b c2 c1
  have h2 := zspan3_add_zdist_ge d e c2 f
  have h3 : zspan4 0 a b b ≤ zspan4 0 a b c2 := by simp only [zspan4]; omega
  have h4 : zspan4 d e f f = zspan3 d e f := by simp only [zspan3, zspan4]; omega
  have h5 : zdist c2 f = zdist f c2 := by unfold zdist; omega
  have h6 : zdist c1 b = zdist b c1 := by unfold zdist; omega
  linarith

/-- **Sharpness of the corrected shape.**  With the root and the pair `(1,2)` at `c1 = 2`, the
pair `(4,5)` at `c2 = 3` and the single leaf `3`, the root-in-pair chain costs exactly `5`:
as cheap as the five-point event itself. This removes the local exponent obstruction;
the full pointwise cover remains open. -/
theorem root_pair_cost_eq_five :
    zspan3 0 1 2 + zdist 2 2 + zspan3 4 5 3 + zdist 2 3 + zdist 3 3 = 5 := by
  unfold zspan3 zdist
  norm_num

/-- At the same configuration the production chain costs `6` and the fan `7`: the single
missing unit is precisely the root's separate two-point arm. -/
theorem chain_and_fan_cost_at_same_configuration :
    zspan3 1 2 1 + zdist 1 0 + zspan3 4 5 3 + zdist 1 3 + zdist 3 3 = 6 ∧
      zspan3 4 5 3 + zdist 3 0 + zdist 3 3 + zspan3 1 2 0 + zdist 0 0 = 7 := by
  unfold zspan3 zdist
  norm_num

end PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction
