# Continuation: I.4.11 diagram components and event fidelity

Source: supplied PDF, Lemma I.4.11 and Lemma I.4.12 on pages 39–40. The new
modules prove two exact components of the diagram calculation. They do not
prove the final error quotient for the infinite cutoff model.

## The source event is not disjoint occurrence

The `0 ↔ x ↮ y ↔ z` notation used in the excluded expectation means

```text
x ∈ K₀,  y ∉ K₀,  z ∈ K_y,
```

in one configuration. This is the existing `apartSet` definition, not the
`disjSet` disjoint-occurrence event. `Correlation/I411/Basic.lean` proves
`apartSet_subset_disjSet` and a strict four-site witness
`exists_disjSet_not_apartSet`. It also proves strict inequality of their
measures for any law giving the three displayed edges positive probability.

Consequently, replacing `apartSet` by `disjSet` in an additive gap upper bound
changes the mathematics. The two events cannot be identified by a documentation
alias or a broad renaming. The printed fresh-copy identity in the proof of
I.4.12 is not used as evidence; in particular, when `y ∈ K₀`, its displayed
difference does not reduce to the stated `y ∉ K₀` event. This was the missing proof obligation at the time of the audit;
it is discharged by the follow-up module described below.

## Excluded expectation, without infinite subtraction

`I411.exclMoment` is the canonical extended expectation

```text
∫⁻ |K₀| ∑_{y∈B} 1(y ∉ K₀) |K_y|.
```

`I411.exclMoment_eq_tsum_apartSet` identifies it exactly with

```text
∑_{y∈B} ∑_x ∑_z P(apartSet 0 x y z).
```

Both clusters are expanded into sums of indicators, and Tonelli is applied in
`ℝ≥0∞`. No finite-moment premise and no `∞ - ∞` operation occur. The finite
`B` sum and the countable `x,z` sums stay in their source order.

`I411.TwoClusterGapApart` and `I411.gapDiagram`, kept in `Basic.lean`, state the
source-shaped pointwise gap estimate and its five-factor diagram explicitly.
`I411_step_of_twoClusterGapApart` proves the additive summation step once that
pointwise estimate is supplied. It does not disguise the estimate as a proved
library input.

## Five-factor summation

`Correlation/I411/DiagramAssembly.lean` supplies the right-hand-side assembly
for a translation-invariant long-range kernel:

- expected cluster volume equals the sum of the two-point function;
- translation gives independence of this sum from the root;
- summation over `x,z` factors out two expected-volume terms;
- `twoPointFunction_comm` turns `τ(y,b)` into `τ(b,y)`;
- four nonnegative sums can be interchanged to match the order in the proof
  of I.4.11;
- the remaining double sum is the explicit triple convolution `∇(0,y)`.

The final `sum_twoCluster_le_of_pointwise` combines this with an explicitly
supplied pointwise gap inequality. Finiteness premises are separately exposed
for the real-value bridge; no unconditional real subtraction is claimed.

## Remaining gap and ledger consequence

The missing pointwise estimate is specifically the `apartSet` version used by
I.4.11. The already available `disjSet` theorem alone does not provide it.
The real quotient establishing `cE1 ≤ |B_r|⁻¹ ∑_{x∈B_r} ∇(0,x)` also remains
to be assembled.

Accordingly I.4.11 is PARTIAL. The earlier I.4.12 row is also corrected to
PARTIAL: the existing repaired theorem formalizes a different, disjoint-
occurrence gap bound, not the source-event statement exact as previously
claimed. This statement-audit correction is independent of compilation status.

## Follow-up: the source gap is now proved

`Correlation/I411/ApartGap.lean` closes the pointwise gap identified above.
Its `twoCluster_gap_apart` proves

```text
τ(o,x) τ(y,z) ≤ P(apartSet o x y z)
                 + ∑_a ∑_b τ(o,a)τ(a,x)τ(a,b)τ(y,b)τ(b,z)
```

for the canonical law with every edge probability strictly below one.
`longRange_twoClusterGapApart` discharges the previously named input for the
paper's law. The source statement of I.4.12 is therefore FULL, with a repaired
proof, rather than merely formalized in the weaker `disjSet` form.

The repair uses `cluster_forceOn_compl_touchSet`: restoration keeps exactly
the base root cluster. A fresh walk avoiding that cluster survives restoration
and lands in `apartSet`; if there is no such walk, the deterministic
`exists_fresh_disjOcc_of_no_avoid` supplies the branch point needed by the BK
alternative. This proves the exact product-measure covering without using the
printed factorization. It does not rely on the failed event renaming.

`I411_paper_display` and `I411_subtracted_display` then assemble the source
I.4.11 display from the pointwise gap and five-factor summation. The latter is
in `ℝ≥0∞` and uses truncated subtraction, so it is not a real `∞ - ∞`
computation. The real `cE1` quotient is the remaining step for I.4.11 itself.
I.4.11 consequently stays PARTIAL; there is no blanket infinite-moment claim.

## The real quotient

`Correlation/I411/RealQuotient.lean` now closes that algebraic step.
`joint_eq_excluded_add_windowMoment` proves the exact additive identity
`joint = excluded + connected`. `lemma_I_4_11_of_finite` then converts the
truncated-subtraction display to the real inequality

```text
cE1 A.toReal J.toReal T.toReal |B| ≤ (1/|B|) * (∑_{y∈B} ∇(0,y)).toReal.
```

Its premises are nonempty `B`, finite expected cluster volume, finite joint
window moment, and finite assembled triangle diagram. Translation invariance
and nonnegativity of the kernel are retained as premises. The excluded and
connected moments are shown finite from the joint moment, rather than silently
converted from `⊤` into zero by `toReal`.

`lemma_I_4_11_cutoff_of_firstMoment` now instantiates this at the actual
cutoff law and includes covariance nonnegativity. The preceding
`cutoffSecondMoment_ne_top_of_firstMoment` and
`cutoffJointSecondMoment_ne_top_of_firstMoment` results prove all required
moment finiteness from finite expected cluster volume; no separate second or
third moment is supplied by hand. The remaining model obligation is therefore
finite expected cluster volume via sharpness, along with finiteness of the
windowed triangle diagram and the nonempty-window convention. This is a much
stronger cutoff reduction, but I.4.11 remains PARTIAL unless those source-model
inputs are discharged. Arbitrary infinite means are not silently reinterpreted.

## Validation

The integrated modules passed the full 9,474-job `lake build --wfail PercLib`
build, with all 427 modules in the import closure. The twenty-six original gap/diagram checks and the eleven
follow-up checks for `ApartGap` all return only `propext`,
`Classical.choice`, and `Quot.sound`. The source-gap and real-quotient package passed 9,478 jobs
and all 431 modules in the import closure. The subsequent cutoff moment and
I.4.11 package passed 9,481 jobs and all 434 modules. These are local checks on the pending integration revision, not
upstream CI or a claim of completion of I.4.11/I.4.12.
