/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m3/.
-/

/- Definitions for the Case 1 decorrelation estimate in the proof of Proposition I.4.20.
-/
module

public import PercLib.CriticalLRP.Correlation.Hrest
public import PercLib.CriticalLRP.MomentMonotonicity.WindowMoments

/-!
# Case 1 (`d > 3α`) of the decorrelation estimates (I.4.20)/(I.4.21)

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Proposition I.4.20, Case 1 (`d > 3α`), paper.txt
lines 2831--2861.  The paper proves, for `0 ≤ ℓ ≤ p - 1`,

```
0 ≤ |B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}
      - E[ |K|^{ℓ+1} ∑_{y∈B_r} 1(y∉K) |K_y|^{p-ℓ} ]
  ≤ E[ |K|^{p+1} |K ∩ B_r| ] ⪯_p (E|K|)^{2p+3} ≍_p r^{(2p+3)α},
```

which combined with `|B_r|E|K|^{ℓ+1}E|K|^{p-ℓ} ≍ r^{d+2pα}` and
`d + 2pα > (2p+3)α` (valid since `d > 3α`) gives (I.4.20) and hence (I.4.21).

The three objects below are exactly the three quantities in that display, in the
`ℝ≥0∞` (`|K| = ∞` harmless) formulation of the canonical independent-edge law
`edgeMeasure π` of §I.1.2:

* `mixedExcl π o a b B` is the *excluded mixed marked expectation*
  `E[ |K_o|^a ∑_{y∈B} 1(y ∉ K_o) |K_y|^b ]` (with `a = ℓ+1`, `b = p-ℓ`); it
  generalises `I411.exclMoment`, which is the case `a = b = 1`.
* `prodFactor π o a b B` is its *product-factor approximation*
  `∑_{y∈B} E|K_o|^a E|K_y|^b`; under homogeneity this is `|B| E|K|^a E|K|^b`.
* `windowMoment π o k B` is the *mixed cluster-window moment*
  `E[ |K_o|^k |K_o ∩ B| ]`; with `k = p+1` it is the paper's
  `E[|K|^{p+1}|K ∩ B_r|]`, and it is dominated by `powMomentAt π (k+1) o`.

Nothing here is assumed about the joint law beyond the canonical independent-edge
law: the discrepancy bounds relating the three quantities are proved in `Case1.lean`
from `Hrest.twoCluster_ennreal` (Lemma I.2.1(i), BK) and
`Hrest.hrest_generic` (Lemma I.2.1, Harris--FKG side).
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace I420Case1

variable {V : Type*} [Countable V]

/-! ## The three quantities of the Case 1 display -/

/-- The `a`-th cluster moment at the base point `v`: `E|K_v|^a`
(paper `E_{β,r}|K|^a`, `= ∞` if `K_v` is infinite). -/
noncomputable def powMomentAt (π : Sym2 V → unitInterval) (a : ℕ) (v : V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω v ^ a ∂(edgeMeasure π)

/-- The **excluded mixed marked expectation**
`E[ |K_o|^a ∑_{y∈B} 1(y ∉ K_o) |K_y|^b ]`.

This is the paper's `E_{β,r}[|K|^{ℓ+1} ∑_{y∈B_r} 1(y∉K) |K_y|^{p-ℓ}]` with
`a = ℓ+1` and `b = p-ℓ`; `I411.exclMoment` is the case `a = b = 1`. -/
noncomputable def mixedExcl (π : Sym2 V → unitInterval) (o : V) (a b : ℕ)
    (B : Finset V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω o ^ a *
      ∑ y ∈ B, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ b
    ∂(edgeMeasure π)

/-- The **product-factor approximation** of `mixedExcl`,
`∑_{y∈B} E|K_o|^a E|K_y|^b`.  Under homogeneity of the `b`-th moment this is
`|B| · E|K|^a · E|K|^b`, the paper's `|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}`. -/
noncomputable def prodFactor (π : Sym2 V → unitInterval) (o : V) (a b : ℕ)
    (B : Finset V) : ℝ≥0∞ :=
  ∑ y ∈ B, powMomentAt π a o * powMomentAt π b y

/-- The **mixed cluster-window moment** `E[ |K_o|^k |K_o ∩ B| ]`.

With `k = p+1` this is the paper's `E_{β,r}[|K|^{p+1}|K ∩ B_r|]`, the upper bound
for the discrepancy. -/
noncomputable def windowMoment (π : Sym2 V → unitInterval) (o : V) (k : ℕ)
    (B : Finset V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω o ^ k * clusterVolIn ω o (B : Set V) ∂(edgeMeasure π)

/-! ## Real-valued shadows and homogeneity

The paper's estimates live in `ℝ`; these are the `toReal` shadows used to state the
asymptotic squeeze at the end. -/

/-- `E|K_o|^a` as a real number (the paper's `E_{β,r}|K|^a`). -/
noncomputable def momR (π : Sym2 V → unitInterval) (a : ℕ) (v : V) : ℝ :=
  (powMomentAt π a v).toReal

/-- `mixedExcl` as a real number (the paper's excluded mixed marked expectation). -/
noncomputable def mixedExclR (π : Sym2 V → unitInterval) (o : V) (a b : ℕ)
    (B : Finset V) : ℝ :=
  (mixedExcl π o a b B).toReal

/-- Homogeneity of the `b`-th cluster moment: the source's transitivity of the
weighted graph, in the only form used by the product factor. -/
def MomentHomogeneous (π : Sym2 V → unitInterval) (b : ℕ) (o : V) : Prop :=
  ∀ y : V, powMomentAt π b y = powMomentAt π b o

end I420Case1

end PercLib.CriticalLRP
