# Derived positivity and finiteness of the critical parameter

Status: a source-level derived obligation for the eventual dependency graph.
It is **not** a new root hypothesis, a Lean proof, or a closed graph node.
The ordinary obligations remain `NOT_STARTED` until providers are assigned and
reviewed after topology approval. The small-`beta` argument is consistent with
`.ultramath/smwoa6sry/m3/BETAC_REVIEW.md`, whose first-moment span was checked
against the model text. That older file's one-dimensional and all-dimensional
finiteness arguments are superseded: its nearest-neighbour-in-`Z` threshold was
also wrong. The bounded refutation and valid `d >= 2` construction is
`.ultramath/smwohv6t4/m8/BETAC_DERIVATION.md`, with a second audit in
`.ultramath/smwoiwd22/m3/FINDINGS_C.md`. None is a proof-status approval.

## The source fact needed

The paper uses `alpha / beta_c` in both moment roots, measures the uncut critical distribution, and assigns the critical
cutoff derivative. This note derives positivity for every `d >= 1` and
finiteness for `d >= 2` in the source's kernel class. The cited one-dimensional
long-range results have not been read in full. The source asserts finiteness
for `d = 1` with `0 < alpha <= 1`, but its cited texts have not been read in
full. An earlier all-dimensional finite-range argument is retracted. Do not
add an arbitrary positive-finiteness hypothesis or infer a uniform first-moment
bound merely to simplify a route.

Let `m = sum_{x != 0} J(0,x)`. The decreasing differentiable kernel identity in
Definition I.1.3 and its logarithmically integrable error make this sum finite
whenever `alpha > 0`. Since `delta_r -> 0` and is logarithmically integrable, there is `K < infinity`
such that `J(r) <= K max(r,1)^(-d-alpha)`, and hence this sum is finite
whenever `alpha > 0`. These are derived facts about the source kernel, not
extra model premises. Positivity is derived below, not inferred merely from
integral positivity on a large interval.

## Small-beta first-moment bound

For `beta >= 0`, existence of a connection from the origin to `x` implies the
existence of a finite (possibly self-intersecting) walk from `0` to `x`. The
union bound over such walks, independence of distinct edges, and
`1 - exp(-t) <= t` for `t >= 0` give

```text
sum_x P_beta(0 <-> x)
  <= sum_{n >= 0} beta^n sum_{x_1,...,x_n in Z^d}
       product_{i=1}^n J(x_{i-1},x_i)      [x_0 = 0]
  =  sum_{n >= 0} (beta*m)^n.
```

The comparison is an upper bound, so repeated edges and repeated vertices do
not invalidate it. For `beta*m < 1`, the expected origin-cluster size is at
most `1/(1-beta*m)` and hence is finite. The origin's cluster is finite almost
surely. Translation invariance and a countable union over all possible origin
vertices then exclude an infinite cluster somewhere in space almost surely.

Coupling the Bernoulli edge probabilities monotonically in `beta` makes every
such `beta` subcritical. Consequently

```text
beta_c >= 1/m > 0.
```

## Large-beta finite-range square-lattice coupling for `d >= 2`

A previous collinear map `(m,n) |-> (m+n)v` is expressly **not** used here.
It names the same physical pair `{k*v,(k+1)*v}` for all coordinates with
`m+n=k`, so its alleged retained edges are not independent. Its abstract graph
can also have an infinite open component on three physical vertices, so the
transfer from an infinite abstract component to the long-range model is false.
Fresh review reference: `.ultramath/smwohv6t4/m8/BETAC_DERIVATION.md`, D1–D3.

For `d >= 2`, write `e_1,e_2` for two distinct standard integer coordinate
vectors and use the two linearly independent displacements
`v = e_1` and `w = 2e_2`. Define the **injective** map
`phi(m,n) = m*v + n*w` for `(m,n) in Z^2`. Retain exactly

```text
H(m,n) = {phi(m,n), phi(m+1,n)}   [displacement v],
V(m,n) = {phi(m,n), phi(m,n+1)}   [displacement w].
```

These are all pairs of distinct lattice vertices. There is an isomorphism from
ordinary nearest-neighbour `Z^2` onto this retained graph: `(m,n)` is joined to
`(m+-1,n)` by an `H`-edge and to `(m,n+-1)` by a `V`-edge. Within either family,
injectivity makes the pairs distinct. Across families, the differences are
`+-v` and `+-w`, which are unequal by linear independence of `v,w`.
Consequently the source's independence of distinct unordered vertex pairs
(`paper-tex.txt@L41` = `paper.html#S1.SS2.p1.1@L335`) applies to the retained
edges. They are open independently with probabilities
`q_v(beta) = 1-exp(-beta*J(0,v))` and
`q_w(beta) = 1-exp(-beta*J(0,w))`.

The representation in Definition I.1.3 gives positivity and finiteness,
rather than merely asserting them: after choosing `s_0` with
`1+delta_s >= 1/2` for `s >= s_0`,
`J(r) >= C/(2(d+alpha)) max(r,s_0)^(-d-alpha) > 0`.
Here `C` is the constant of (I.1.2), equal to `1` under the source's unit-ball
normalization, and the upper bound `J(r) <= K max(r,1)^(-d-alpha)` is the one
recorded above. Put
`j = min{J(0,v), J(0,w)} > 0`. Fix `p0 = 3/4` and choose
`beta > log(4)/j`. Both probabilities are then greater than `p0 > 1/2`.

For each retained edge `e`, independently sample `(U_e)` i.i.d. uniform on
`[0,1]`, **independent of the edge configuration**, and declare it thinned-open exactly when it was open and
`U_e <= p0/q_type(e)(beta)`. The thinned edges form independent nearest-neighbour
bond percolation on `Z^2` with common parameter `p0`, and are a subgraph of the
original configuration. Kesten's supercritical direction, stated explicitly in
Theorem 10 of B. Bollobas and O. Riordan,
*A short proof of the Harris--Kesten Theorem*
(arXiv:math/0410359v3, [PDF](https://arxiv.org/pdf/math/0410359v3)), gives an
infinite open cluster almost surely at every fixed `p > 1/2`. Hence the full
long-range configuration also has an infinite cluster almost surely, and

```text
beta_c <= log(4) / min{J(0,v), J(0,w)} < infinity.
```

No zero-one law is needed for this conclusion; the threshold already gives
almost-sure percolation. The v3 PDF was downloaded and text-checked at
Theorem 10; its SHA256 is
`b171039a2d77dece89a6760749fa31d49843028614c4adf92b6fad21da90d8e8`.
The external threshold supplies an input to this source-level argument, not a
Lean formalization. Any later 0-1 argument must be called the translation-invariant
0-1 law for an independent lattice-indexed family: the infinite-cluster event is
translation invariant but is **not** an outside-finite-box tail event.

At `d = 1`, the construction itself already fails at injectivity: `v` and `w`
are collinear and `phi(2,0) = phi(0,1)`, so infinitely many coordinate pairs
produce the same physical edge. Independently of that failure, no finite-range
subgraph proves supercriticality: if each edge is closed with probability at
least `c > 0`, then each cut is closed with probability at least `c^M` for some
finite `M`, and cuts at spacing greater than twice the range are edge-disjoint
and independent. The second Borel--Cantelli lemma therefore gives a.s.
infinitely many closed cuts, across which no cluster can pass. In particular,
the physical graph of length-1 and length-2 steps has `p_c = 1`. This does **not** show that the source's
one-dimensional long-range model has `beta_c = infinity`; genuinely long-range
citations are required, and only the asserted `0 < alpha <= 1` range is needed
for the two root domains considered here. That literature remains an open
external-input obligation, so this note makes no claim about `d = 1, alpha > 1`.

## Graph consequences

Both roots need the positivity/finiteness derivations exposed as ordinary
mathematical dependencies, with their model and threshold prerequisites. The
valid square-lattice derivation covers `d >= 2`; along either root domain, a
one-dimensional instance falls within the separately cited `0 < alpha <= 1`
case (in fact `alpha <= 1/3`). Those one-dimensional citations remain to be
read, not silently discharged by the embedding. The derivations must not be
hidden in `SourceModelData`, bundled into an `Input` structure, or added as free
conclusion-shaped premises. Such dependencies do not change a frozen
declaration's ABI.

Separate obligations remain:

- the uncut-cutoff transfer used in a particular tail derivation;
- Theorem 10 of Bollobas--Riordan, arXiv:math/0410359v3, for independent nearest-neighbour bond percolation on the square lattice, plus the heterogeneous-edge thinning comparison and any proved library match;
- the separately cited one-dimensional long-range supercriticality threshold for `0 < alpha <= 1`;
- any route-specific use of `theta(beta_c) = 0`;
- any uniform first-moment bound required by a cutoff limit.

These are different claims. In particular, `theta(beta_c)=0` **does** follow
from the uncut `(I.1.7)`/`(I.1.17)` tail decay: the event `{|K|=infinity}` is
contained in `{|K|>=n}` for every `n`, so its probability is at most the tail
probability, which tends to zero. It also follows from any `r`-uniform bound
`sup_r E_{beta_c,r}|K| < infinity`, by monotone convergence. It does **not**
follow from the growing `(I.1.6)`/`(I.1.16)` cutoff asymptotics alone. Berger
type continuity is an independent route option, not a new premise of those
theorems. The tail route for the Hydro-critical root remains to be
traced through Sections I.3/I.5.

## Citation and source-boundary limits

Reference [45] is F. J. Dyson's *Existence of a phase-transition in a
one-dimensional Ising ferromagnet* (1969), an Ising paper, **not** the third
paper in this series and not evidence for the Hydrodynamic condition or its
logarithmic corrections. That separate 105-page source is arXiv:2508.18809v1
(*Critical long-range percolation III: The upper critical dimension*), and it
was read selectively for those statements, not for all of their proofs.
The publisher's abstract for reference [90], Newman--Schulman, supports only a
restricted one-dimensional supercriticality statement; the full text remains
behind subscription access. Reference [97] and other unread inputs were not
verified, and no access restriction was bypassed. None of the small-beta or
square-lattice arguments above relies on those unread texts; neither does the
correct implication that established uncut tail decay gives `theta(beta_c)=0`.
Proposed citation-range and Figure-1 caption issues remain provisional.
