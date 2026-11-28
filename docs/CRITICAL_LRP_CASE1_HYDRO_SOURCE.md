# Case 1: single-cluster tail to the hydrodynamic condition

**Update:** `Analysis/SecondMomentCase1/Capstone` subsequently proves
`SingleClusterTail` itself from finite first cutoff moments and the ordinary
tree-moment bound. Its finite-moment and first-moment-asymptotic wrappers
therefore remove the `SingleClusterTail` and `1 ≤ m` inputs of the original
assembly. The [completed-tail note](CRITICAL_LRP_CASE1_SINGLE_CLUSTER_TAIL.md)
records the remaining first-moment input. The text below describes the earlier
conditional reduction and remains its historical/proof-scope record.


`Analysis/SecondMomentCase1/Hydro` proves the Case-1 tail-to-median direction
of Corollary I.4.14. It does not prove Proposition I.4.2 or the underlying
single-cluster exponential tail.

## Union bound and median estimate

For the actual cutoff law, `tail_maxCluster_le` proves
$$P_{\beta_c,r}(|K_{\max}(B_r)|\ge n)
 \le |B_r| P_{\beta_c,r}(|K|\ge n).$$
The proof enumerates the finite window, contains each relevant cluster in the
doubled ball around one of its vertices, and uses translation invariance.

`SingleClusterTail M r m` denotes the source's displayed bound
$$P_{\beta_c,r}(|K|\ge n)\le
 \sqrt{2m/n}\exp\{-n/(4m^2)\},\qquad n\ge1.$$
It remains an explicit hypothesis. Given that tail, $m(r)\ge1$, and a uniform
bound $|B_r|\le B_c r^d$, `mr_le_singleClusterTail` proves
$$M_r\le Cm(r)^2\log r,\qquad r\ge2,$$
with an explicit positive constant. The proof chooses
$n=\lceil Am(r)^2\log r\rceil$, shows that its union-bound tail is at most
$e^{-1}$, and uses admissibility in the median definition.
`exists_ball_ncard_bound` supplies the normalized-ball cardinality premise.

## Hydrodynamic consequence

`hydro_of_singleClusterTail` combines the median bound with $m(r)\preceq r^\alpha$
and $3\alpha<d$. Its squeeze has decay $\log r/r^{(d-3\alpha)/2}$, hence proves
`Hydro M`. The model corollaries instantiate $m(r)$ at the actual cutoff first
moment; `mr_isBigO_cutMoment_one` records the big-O form, and
`hydro_of_cutMoment_one'` uses the derived ball bound.

The two remaining probabilistic inputs are therefore exactly the single-cluster
tail and the Case-1 first-moment upper bound. No critical $n^{-1/2}$ tail,
critical second-moment bound, or triangle condition is inserted in their place.
All nine exported theorems were elaborated with the project's strict flags and
have only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

## Partial scale calculations for the missing tail

The companion [scale-analysis note](CRITICAL_LRP_CASE1_TAIL_SCALE.md) records
`Analysis/SecondMomentCase1/TailScale`: order-two and order-five scale bounds
on the windows $u\in[1,6]$ and $u\in[6,16]$, plus factorial and logarithm
estimates. These are proved intermediate calculations only. The $u\le1$ and
$u\ge16$ regions, the coefficient bridge to the tree-moment theorem, and the
cutoff Markov assembly remain open, so `SingleClusterTail` is still an input
to the hydrodynamic result above.
