/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m1/I417A/Defs.lean ; module path rewritten only.
-/

/-
# Hutchcroft Lemma I.4.17, direction A: definitions

Scratch formalization (swarm `smwpwq50m`, member `m1`).  Source: Tom Hutchcroft,
*Critical long-range percolation I: High effective dimension*, arXiv:2508.18807v1,
Lemma I.4.17 (p. 45):

  0 <= E|K|^p E|K|^q - E[|K_x|^p |K_y|^q 1(x nleftrightarrow y)]
    <= sum_{l=3}^{p+q+1} C_{p,q,l} T^l(x,y) (E|K|)^{2p+2q+1-l}.

This direction isolates the **nonnegativity** half and the exact labelled-vertex event
expansion of the raw signed difference.  Nothing here assumes moment finiteness: every
statement is in `ℝ≥0∞` with `cardFun K = ⊤` for infinite clusters.

Definition module only; every proof lives in the sibling modules.
-/
module

public import PercLib.CriticalLRP.BK.CanonicalCardinal

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace I417A

variable {V : Type*} [Countable V]

/-- **The labelled event.**  The labelled tuple `f : Fin p → V` is contained in the cluster
of `x`.  Its indicator is the pointwise product `∏ i, 1{f i ∈ K_x}` (`prod_indicator_apply`),
so `|K_x|^p` is the sum of its indicators over all tuples (`cardFun_pow_eq_tsum`). -/
def labelEvent (x : V) {p : ℕ} (f : Fin p → V) : Set (Config V) :=
  {ω | ∀ i, f i ∈ cluster ω x}

/-- The event `x nleftrightarrow y`, i.e. `y ∉ K_x`. -/
def notConnSet (x y : V) : Set (Config V) :=
  {ω | ¬ Connects ω x y}

/-- The `(f,g)`-summand of the raw signed moment difference: the labelled event of `x`,
the labelled event of `y`, and non-connection.  This is the *exact* native event whose
probability appears in `lintegral_negConn_mul_cardFun_pow`. -/
def deficitEvent (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) : Set (Config V) :=
  labelEvent x f ∩ labelEvent y g ∩ notConnSet x y

/-- The raw signed moment difference of Lemma I.4.17, in additive (`ℝ≥0∞`) form:
`E[1(x ↮ y) |K_x|^p |K_y|^q]`.  Nonnegativity of the difference
`E|K|^p E|K|^q - E[...]` is the inequality `rawDiff <= (∫ |K_x|^p) * (∫ |K_y|^q)`. -/
noncomputable def rawDiff (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (notConnSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
    (Percolation.cardFun (cluster ω x) ^ p * Percolation.cardFun (cluster ω y) ^ q)
    ∂(edgeMeasure π)

/-- The product of the two cluster moments, `E|K_x|^p · E|K_y|^q`. -/
noncomputable def momentProd (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) : ℝ≥0∞ :=
  (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)) *
    (∫⁻ ω, Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π))

end I417A

end PercLib.CriticalLRP
