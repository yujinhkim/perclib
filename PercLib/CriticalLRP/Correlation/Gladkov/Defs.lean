/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.

The named literature input is Gladkov, Percolation Inequalities and Decision
Trees, arXiv:2408.08457v2, Theorem 6.2, temporarily assumed at the user's request.
-/

module

public import PercLib.Percolation.Bond.Basic

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.Correlation.Gladkov

open PercLib.Percolation.Bond

/-- The exact three-point Gladkov inequality for a fixed root `x`. This is an
explicit literature input, not a theorem proved here or a custom axiom.

The two variables `y,z` and permutations of `x,y,z` instantiate all triples
needed in Corollary I.2.8. -/
structure GladkovInput {V : Type*} [Countable V] (π : Sym2 V → unitInterval)
    (x : V) : Prop where
  three_point_sq_le : ∀ y z, law π (conn x y ∩ conn x z) ^ 2 ≤
    8 * law π (conn x y) * law π (conn y z) * law π (conn z x)

/-- Non-vacuity: on a single vertex the connection probabilities are one even
when every unordered pair has zero edge probability. -/
example : GladkovInput (fun _ : Sym2 Unit => 0) () := by
  constructor
  intro y z
  have hy : y = () := Subsingleton.elim _ _
  have hz : z = () := Subsingleton.elim _ _
  subst y
  subst z
  have hu : law (fun _ : Sym2 Unit => 0) (conn () ()) = 1 := by
    simp [conn]
  norm_num [hu]

end PercLib.CriticalLRP.Correlation.Gladkov
