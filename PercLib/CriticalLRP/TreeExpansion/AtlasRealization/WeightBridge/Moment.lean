/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
The consumer: the atlas covering + BK bound in tree-weight form, and the shape-count audit.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.WeightBridge.Bridge
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Cover
public import PercLib.CriticalLRP.TreeExpansion.Moments

/-!
# From the atlas bound to the ordinary tree-weight bound

`AtlasRealization.Cover.prob_le_sum_shapes` bounds the probability that a root is connected to
all terminals of a finite label set `Z` by a sum over shapes of a product over the `2p - 1`
atlas edges.  `WeightBridge.Bridge` identifies the inner sum over internal positions with the
ordinary tree weight.  Combining the two (`prob_conn_le_sum_wtL` below) gives the tree-graph
bound in the form the source uses, with the tree weight of the actual shape rather than an atlas
product — the step the covering file reports as not performed.

## Scope of what is proved, and the shape-count gap that remains

The atlas covering theorem enumerates **plane** shapes: `RTree` is a type of ordered binary
trees, so a non-plane tree with `p` distinctly labelled leaves occurs as `2^(p-1)` distinct
`RTree`s (`RTree.card_swapFiber`).  The tree sum of the source inequality (I.2.2) is instead a
sum over **isomorphism classes**, which is `treeSum k m` = `2^(-(m-1))` times the plane sum.

Consequently the bound proved here,

  `P ≤ ∑ t : RTree.LT (Fin q), wtL k t x o = 2^(q-1) * treeSum k q o x`,

is a factor `2^(q-1)` weaker than (I.2.2), and the moment bound it yields is
`2^(q-1) (2q-3)!! (E|K|)^(2q-1)`, a factor `2^(q-1)` weaker than (I.2.3).  This is *not* a loss
in the covering or BK steps and *not* a loss in the atlas-to-weight bridge: it is exactly the
plane multiplicity.  `RTree.wtL_swap` below shows that the two children of a node can be
exchanged without changing the weight, so all `2^(p-1)` plane representatives of one non-plane
tree contribute the same value and the plane union bound over-counts each non-plane diagram
`2^(p-1)` times.  Removing the factor requires taking the union bound over a fundamental domain
of the child-swap action (a *canonical* shape per isomorphism class) rather than over all plane
shapes, i.e. it needs a covering theorem that produces a canonical shape, or equivalently the
transport of a realization across child swaps (`RTree.swapFiber`).  Neither exists in production,
and the bound proved here must not be quoted as (I.2.2) or (I.2.3).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## The two-point kernel of the bound -/

/-- **The tree-weight form of the covering + BK bound.**  For every nonempty finite label set
`Z`, the probability that `v` is connected to all terminals `y a` (`a ∈ Z`) is at most the sum
over plane shapes with leaf set `Z` of the ordinary tree weight `RTree.wtL`, with the root pinned
at `v` and the leaf labelled `a` pinned at `y a`.

Only BK (`BKIncreasing pr`) and the finiteness of `V` enter beyond the covering theorem and the
weight/positions bridge. -/
theorem prob_conn_le_sum_wtL (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : BKIncreasing pr) (ends : E → Sym2 V) (v : V) (y : α → V) {Z : Finset α}
    (hne : Z.Nonempty) :
    prob pr {ω | ∀ a ∈ Z, Conn ends ω v (y a)}
      ≤ ∑ t : LTon α Z, RTree.wtL (fun a b => prob pr {ω | Conn ends ω a b}) t.1 y v := by
  refine le_trans (prob_le_sum_shapes hp hp1 hBK ends v y hne) ?_
  refine Finset.sum_le_sum fun t _ => ?_
  exact le_of_eq (posSumWt_eq_wtL (fun a b => prob pr {ω | Conn ends ω a b}) t.1 y v)

/-- The shape sum of `prob_conn_le_sum_wtL` over `LTon α univ` is the sum over fully labelled
trees `RTree.LT α`. -/
theorem sum_LTon_univ_eq_sum_LT [Fintype (RTree.LT α)] (k : V → V → ℝ) (y : α → V)
    (v : V) :
    (∑ t : LTon α (Finset.univ : Finset α), RTree.wtL k t.1 y v)
      = ∑ t : RTree.LT α, RTree.wtL k t.1 y v := by
  refine Fintype.sum_equiv (ltonUnivEquivLT α) _ _ ?_
  intro t
  rfl

/-- **The bound with the fully labelled shapes of (I.2.2).**  For `q ≥ 1` terminals
`x : Fin q → V` and a root `o`, the probability that `o` is connected to all of them is at most
the sum of the tree weights over the `RTree.LT (Fin q)` family. -/
theorem prob_conn_le_sum_wtL_fin (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : BKIncreasing pr) (ends : E → Sym2 V) (o : V) {q : ℕ} (hq : 1 ≤ q)
    (x : Fin q → V) :
    prob pr {ω | ∀ i : Fin q, Conn ends ω o (x i)}
      ≤ ∑ t : RTree.LT (Fin q), RTree.wtL (fun a b => prob pr {ω | Conn ends ω a b}) t.1 x o := by
  have hne : (Finset.univ : Finset (Fin q)).Nonempty :=
    ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have hset : {ω : Finset E | ∀ a ∈ (Finset.univ : Finset (Fin q)), Conn ends ω o (x a)}
      = {ω : Finset E | ∀ i : Fin q, Conn ends ω o (x i)} := by
    ext ω
    simp
  rw [← hset]
  refine le_trans (prob_conn_le_sum_wtL pr hp hp1 hBK ends o x hne) (le_of_eq ?_)
  exact sum_LTon_univ_eq_sum_LT _ x o

/-! ## Summing the free terminals: the moment form -/

/-- The tree-weight analogue of `RTree.sum_wt_labelled`: summing the tree weight over all values
of the `p` leaf labels gives `S^(2p-1)` whenever all row sums of `k` are `S`. -/
theorem sum_wtL_labelled (k : V → V → ℝ) (S : ℝ) (hS : ∀ v : V, ∑ y : V, k v y = S)
    {p : ℕ} {t : RTree (Fin p)} (ht : RTree.FullyLabelled t) (v : V) :
    (∑ x : Fin p → V, RTree.wtL k t x v) = S ^ (2 * p - 1) := by
  rw [← RTree.sum_wt_labelled k S hS ht v]
  exact Finset.sum_congr rfl fun x _ => (RTree.wt_eq_wtL k t x v).symm

/-- **The moment bound from the atlas covering.**  Summing over the terminal positions,

  `∑_{x : Fin q → V} P(o ↔ x_1, ..., o ↔ x_q) ≤ #(RTree.LT (Fin q)) · (E|K|)^(2q-1)`.

The coefficient is the `cardinality of the plane shape family`; it is not evaluated here, and it
is `2^(q-1)` times the count `(2q-3)!!` of the source. -/
theorem sum_prob_le_card_mul (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : BKIncreasing pr) (ends : E → Sym2 V) (o : V) {q : ℕ} (hq : 1 ≤ q) (S : ℝ)
    (hS : ∀ v : V, ∑ u : V, (fun a b => prob pr {ω | Conn ends ω a b}) v u = S) :
    (∑ x : Fin q → V, prob pr {ω | ∀ i : Fin q, Conn ends ω o (x i)})
      ≤ (Fintype.card (RTree.LT (Fin q)) : ℝ) * S ^ (2 * q - 1) := by
  refine le_trans (Finset.sum_le_sum fun x _ => prob_conn_le_sum_wtL_fin pr hp hp1 hBK ends o hq x)
    ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun t _ =>
    sum_wtL_labelled (fun a b => prob pr {ω | Conn ends ω a b}) S hS t.2 o]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## The plane/non-plane gap -/

/-- Exchanging the children of a node does not change the tree weight.  Hence all `2^(p-1)`
plane representatives of a non-plane diagram (the elements of `RTree.swapFiber`) contribute the
same value, and a union bound over the plane family over-counts each non-plane diagram exactly
`2^(p-1)` times. -/
theorem wtL_swap (k : V → V → ℝ) (l r : RTree α) (y : α → V) (v : V) :
    RTree.wtL k (RTree.node l r) y v = RTree.wtL k (RTree.node r l) y v := by
  rw [RTree.wtL_node, RTree.wtL_node]
  exact Finset.sum_congr rfl fun w _ => by ac_rfl

/-- The plane sum of the tree weights is `2^(m-1)` times the source tree sum `treeSum`.
This is the exact identity behind the gap recorded in the module docstring: the atlas covering
produces the plane sum, while (I.2.2) has `treeSum`. -/
theorem sum_wtL_eq_two_pow_mul_treeSum (k : V → V → ℝ) (m : ℕ) (_hm : 1 ≤ m) (v : V)
    (x : Fin m → V) :
    (∑ t : RTree.LT (Fin m), RTree.wtL k t.1 x v) = 2 ^ (m - 1) * treeSum k m v x := by
  have hwt : (∑ t : RTree.LT (Fin m), RTree.wt k t.1 (fun q => x (RTree.leafOfPos t.1 q)) v)
      = ∑ t : RTree.LT (Fin m), RTree.wtL k t.1 x v :=
    Finset.sum_congr rfl fun t _ => RTree.wt_eq_wtL k t.1 x v
  rw [treeSum, hwt]
  have hne : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
  rw [one_div, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- **The bound of (I.2.2) up to the plane multiplicity.**  The atlas covering + BK + the
weight/positions bridge give (I.2.2)'s right-hand side multiplied by `2^(q-1)`; the missing
factor is the number of plane orderings of a non-plane diagram and is a shape-count issue only
(see `wtL_swap`). -/
theorem prob_conn_le_two_pow_mul_treeSum (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (o : V) {q : ℕ}
    (hq : 1 ≤ q) (x : Fin q → V) :
    prob pr {ω | ∀ i : Fin q, Conn ends ω o (x i)}
      ≤ 2 ^ (q - 1) * treeSum (fun a b => prob pr {ω | Conn ends ω a b}) q o x := by
  refine le_trans (prob_conn_le_sum_wtL_fin pr hp hp1 hBK ends o hq x) ?_
  rw [sum_wtL_eq_two_pow_mul_treeSum (fun a b => prob pr {ω | Conn ends ω a b}) q hq o x]

/-- **The moment bound implied by the atlas covering**, with the plane multiplicity explicit:

  `∑_x P(o ↔ x_1, ..., o ↔ x_q) ≤ 2^(q-1) · (2q-3)!! · (E|K|)^(2q-1)`.

This is a factor `2^(q-1)` weaker than (I.2.3) of the source and must not be quoted as it. -/
theorem sum_prob_le_two_pow_mul_dfactorial (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (o : V) {q : ℕ}
    (hq : 1 ≤ q) (S : ℝ) (hS : ∀ v : V, ∑ u : V,
      (fun a b => prob pr {ω | Conn ends ω a b}) v u = S) :
    (∑ x : Fin q → V, prob pr {ω | ∀ i : Fin q, Conn ends ω o (x i)})
      ≤ (2 : ℝ) ^ (q - 1) * ((VolumeMoments.M (q - 1) : ℝ) * S ^ (2 * q - 1)) := by
  have hS0 : 0 ≤ S := by
    have ho := hS o
    have h0 : ∀ u : V, 0 ≤ prob pr {ω | Conn ends ω o u} := fun u => prob_nonneg hp hp1 _
    rw [← ho]
    exact Finset.sum_nonneg fun u _ => h0 u
  have hc : (Fintype.card (RTree.LT (Fin q)) : ℝ)
      ≤ (2 : ℝ) ^ (q - 1) * (VolumeMoments.M (q - 1) : ℝ) := by
    exact_mod_cast RTree.card_LT_fin_le q
  refine le_trans (sum_prob_le_card_mul pr hp hp1 hBK ends o hq S hS) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hc (pow_nonneg hS0 _)) ?_
  rw [mul_assoc]

end PercLib.CriticalLRP.TreeExpansion.Real
